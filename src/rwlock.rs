use super::shared::{SpinWait, Waiter};
use std::{
    marker::PhantomData,
    ptr::NonNull,
    sync::atomic::{fence, AtomicUsize, Ordering},
};

const UNLOCKED: usize = 0;
const LOCKED: usize = 1;
const READING: usize = 2;
const QUEUED: usize = 4;
const QUEUE_LOCKED: usize = 8;
const READER_SHIFT: u32 = 16usize.trailing_zeros();
const SINGLE_READER: usize = LOCKED | READING | (1 << READER_SHIFT);

#[derive(Default)]
#[repr(transparent)]
pub struct RawRwLock {
    pub(super) state: AtomicUsize,
    _p: PhantomData<*const Waiter>,
}

unsafe impl Send for RawRwLock {}
unsafe impl Sync for RawRwLock {}

unsafe impl lock_api::RawRwLock for RawRwLock {
    type GuardMarker = crate::GuardMarker;

    const INIT: Self = Self {
        state: AtomicUsize::new(UNLOCKED),
        _p: PhantomData,
    };

    #[inline]
    fn is_locked(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        state & LOCKED != 0
    }

    #[inline]
    fn is_locked_exclusive(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        state & (LOCKED | READING) == LOCKED
    }

    #[inline]
    fn try_lock_exclusive(&self) -> bool {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        return unsafe {
            let mut old_locked_bit: u8;
            #[cfg(target_pointer_width = "64")]
            std::arch::asm!(
                "lock bts qword ptr [{0:r}], 0",
                "setc {1}",
                in(reg) &self.state,
                out(reg_byte) old_locked_bit,
                options(nostack),
            );
            #[cfg(target_pointer_width = "32")]
            std::arch::asm!(
                "lock bts dword ptr [{0:e}], 0",
                "setc {1}",
                in(reg) &self.state,
                out(reg_byte) old_locked_bit,
                options(nostack),
            );
            old_locked_bit == 0
        };

        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
        self.state
            .compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    #[inline]
    fn lock_exclusive(&self) {
        if !self.lock_exclusive_fast_assuming(UNLOCKED) {
            self.lock_exclusive_slow();
        }
    }

    #[inline]
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    unsafe fn unlock_exclusive(&self) {
        let state = self.state.fetch_sub(LOCKED, Ordering::Release);
        debug_assert_ne!(state & LOCKED, 0);
        debug_assert_eq!(state & READING, 0);

        if state & (QUEUED | QUEUE_LOCKED) == QUEUED {
            self.unlock_exclusive_slow(state);
        }
    }

    #[inline]
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    unsafe fn unlock_exclusive(&self) {
        if let Err(state) =
            self.state
                .compare_exchange(LOCKED, UNLOCKED, Ordering::Release, Ordering::Relaxed)
        {
            self.unlock_exclusive_slow(state);
        }
    }

    #[inline]
    fn try_lock_shared(&self) -> bool {
        self.try_lock_shared_fast() || self.try_lock_shared_slow()
    }

    #[inline]
    fn lock_shared(&self) {
        if !self.try_lock_shared_fast() {
            self.lock_shared_slow();
        }
    }

    #[inline]
    unsafe fn unlock_shared(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        if state == SINGLE_READER {
            match self.try_unlock_shared_uncontended() {
                None => {}
                Some(Ok(_)) => return,
                Some(Err(e)) => state = e,
            }
        }

        self.unlock_shared_slow(state)
    }
}

impl RawRwLock {
    #[inline(always)]
    fn lock_exclusive_fast_assuming(&self, state: usize) -> bool {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        return {
            let _ = state;
            use lock_api::RawRwLock;
            self.try_lock_exclusive()
        };

        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
        self.state
            .compare_exchange_weak(state, state | LOCKED, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    #[cold]
    fn lock_exclusive_slow(&self) {
        let is_writer = false;
        let try_lock = |state: usize| -> Option<bool> {
            match state & LOCKED {
                0 => Some(self.lock_exclusive_fast_assuming(state)),
                _ => None,
            }
        };

        self.lock(is_writer, try_lock);
    }

    #[cold]
    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    unsafe fn unlock_exclusive_slow(&self, mut state: usize) {
        assert_ne!(state & LOCKED, 0);
        assert_eq!(state & READING, 0);
        state -= LOCKED;

        while state & (LOCKED | QUEUED | QUEUE_LOCKED) == QUEUED {
            let new_state = state | QUEUE_LOCKED;
            match self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return self.unpark(new_state),
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    unsafe fn unlock_exclusive_slow(&self, mut state: usize) {
        loop {
            assert_ne!(state & LOCKED, 0);
            assert_ne!(state & QUEUED, 0);
            assert_eq!(state & READING, 0);

            let mut new_state = state & !LOCKED;
            new_state |= QUEUE_LOCKED;

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                state = e;
                continue;
            }

            if state & QUEUE_LOCKED == 0 {
                self.unpark(new_state);
            }

            return;
        }
    }

    #[inline(always)]
    fn try_lock_shared_assuming(&self, state: usize) -> Option<Result<usize, usize>> {
        if state == UNLOCKED {
            if let Some(result) = self.try_lock_shared_uncontended() {
                return Some(result);
            }
        } else if state & (LOCKED | READING | QUEUED) == (LOCKED | READING) {
            if let Some(with_reader) = state.checked_add(1 << READER_SHIFT) {
                return Some(self.state.compare_exchange_weak(
                    state,
                    with_reader | LOCKED | READING,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ));
            }
        }

        None
    }

    #[inline(always)]
    fn try_lock_shared_uncontended(&self) -> Option<Result<usize, usize>> {
        #[cfg(all(
            feature = "hardware-lock-elision",
            any(target_arch = "x86", target_arch = "x86_64")
        ))]
        return Some(unsafe {
            let mut prev_state: usize;
            #[cfg(target_pointer_width = "64")]
            std::arch::asm!(
                "xacquire lock cmpxchg qword ptr [{0:r}], {}",
                in(reg) &self.state,
                in(reg) SINGLE_READER,
                inout("rax") UNLOCKED => prev_state,
                options(nostack),
            );
            #[cfg(target_pointer_width = "32")]
            std::arch::asm!(
                "xacquire lock cmpxchg dword ptr [{0:e}], {}",
                in(reg) &self.state,
                in(reg) SINGLE_READER,
                inout("eax") UNLOCKED => prev_state,
                options(nostack),
            );
            match prev_state {
                UNLOCKED => Ok(prev_state),
                _ => Err(prev_state),
            }
        });

        #[cfg(not(feature = "hardware-lock-elision"))]
        None
    }

    #[inline(always)]
    fn try_lock_shared_fast(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        let result = self.try_lock_shared_assuming(state);
        matches!(result, Some(Ok(_)))
    }

    #[cold]
    fn try_lock_shared_slow(&self) -> bool {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            match self.try_lock_shared_assuming(state) {
                None => return false,
                Some(Err(e)) => state = e,
                Some(Ok(_)) => return true,
            }
        }
    }

    #[cold]
    fn lock_shared_slow(&self) {
        let is_writer = false;
        let try_lock = |state: usize| -> Option<bool> {
            let result = self.try_lock_shared_assuming(state)?;
            Some(result.is_ok())
        };

        self.lock(is_writer, try_lock)
    }

    #[inline(always)]
    fn try_unlock_shared_uncontended(&self) -> Option<Result<usize, usize>> {
        #[cfg(all(
            feature = "hardware-lock-elision",
            any(target_arch = "x86", target_arch = "x86_64")
        ))]
        return Some(unsafe {
            let mut prev_state: usize;
            #[cfg(target_pointer_width = "64")]
            std::arch::asm!(
                "xrelease lock cmpxchg qword ptr [{0:r}], {}",
                in(reg) &self.state,
                in(reg) UNLOCKED,
                inout("rax") SINGLE_READER => prev_state,
            );
            #[cfg(target_pointer_width = "32")]
            std::arch::asm!(
                "xrelease lock cmpxchg dword ptr [{0:e}], {}",
                in(reg) &self.state,
                in(reg) UNLOCKED,
                inout("eax") SINGLE_READER => prev_state,
            );
            match prev_state {
                SINGLE_READER => Ok(prev_state),
                _ => Err(prev_state),
            }
        });

        #[cfg(not(feature = "hardware-lock-elision"))]
        None
    }

    #[cold]
    unsafe fn unlock_shared_slow(&self, mut state: usize) {
        while state & QUEUED == 0 {
            assert_ne!(state & LOCKED, 0);
            assert_ne!(state & READING, 0);
            assert_ne!(state >> READER_SHIFT, 0);

            let mut new_state = state - (1 << READER_SHIFT);
            if state == SINGLE_READER {
                new_state = UNLOCKED;

                match self.try_unlock_shared_uncontended() {
                    None => {}
                    Some(Ok(_)) => return,
                    Some(Err(e)) => {
                        state = e;
                        continue;
                    }
                }
            }

            match self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(e) => state = e,
            }
        }

        assert_ne!(state & LOCKED, 0);
        assert_ne!(state & QUEUED, 0);
        assert_ne!(state & READING, 0);

        fence(Ordering::Acquire);
        let (_head, tail) = Waiter::get_and_link_queue(state, |_| {});

        let readers = tail.as_ref().counter.fetch_sub(1, Ordering::Release);
        assert_ne!(readers, 0);

        if readers > 0 {
            return;
        }

        state = self.state.load(Ordering::Relaxed);
        loop {
            assert_ne!(state & LOCKED, 0);
            assert_ne!(state & READING, 0);
            assert_ne!(state & QUEUED, 0);

            let mut new_state = state & !(LOCKED | READING);
            new_state |= QUEUE_LOCKED;

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                state = e;
                continue;
            }

            if state & QUEUE_LOCKED == 0 {
                self.unpark(new_state);
            }

            return;
        }
    }

    fn lock(&self, is_writer: bool, mut try_lock: impl FnMut(usize) -> Option<bool>) {
        Waiter::with(|waiter| {
            waiter.waiting_on.set(Some(NonNull::from(&self.state)));
            waiter.flags.set(is_writer as usize);

            loop {
                let mut state = self.state.load(Ordering::Relaxed);
                let mut spin = SpinWait::default();
                waiter.prev.set(None);

                loop {
                    let mut backoff = SpinWait::default();
                    while let Some(was_locked) = try_lock(state) {
                        if was_locked {
                            return;
                        }

                        backoff.yield_now();
                        state = self.state.load(Ordering::Relaxed);
                    }

                    if (state & QUEUED == 0) && spin.try_yield_now() {
                        state = self.state.load(Ordering::Relaxed);
                        continue;
                    }

                    let waiter_ptr = &*waiter as *const Waiter as usize;
                    let mut new_state = (state & !Waiter::MASK) | waiter_ptr | QUEUED;

                    if state & QUEUED == 0 {
                        waiter
                            .counter
                            .store(state >> READER_SHIFT, Ordering::Relaxed);
                        waiter.tail.set(Some(NonNull::from(&*waiter)));
                        waiter.next.set(None);
                    } else {
                        new_state |= QUEUE_LOCKED;
                        waiter.tail.set(None);
                        waiter
                            .next
                            .set(NonNull::new((state & Waiter::MASK) as *mut Waiter));
                    }

                    if let Err(e) = self.state.compare_exchange_weak(
                        state,
                        new_state,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) {
                        state = e;
                        continue;
                    }

                    if state & (QUEUED | QUEUE_LOCKED) == QUEUED {
                        unsafe { self.link_queue_or_unpark(new_state) };
                    }

                    assert!(waiter.parker.park(None));
                    break;
                }
            }
        });
    }

    #[cold]
    pub(super) unsafe fn unpark_requeue(&self, head: NonNull<Waiter>, tail: NonNull<Waiter>) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            let mut queue_head = head;
            if state & LOCKED == 0 {
                match head.as_ref().next.get() {
                    Some(next) => queue_head = next,
                    None => return self.unpark_waiters(head),
                }
            }

            let waiter_ptr = queue_head.as_ptr() as usize;
            let mut new_state = (state & !Waiter::MASK) | waiter_ptr | QUEUED;

            if state & QUEUED == 0 {
                queue_head.as_ref().tail.set(Some(tail));
                tail.as_ref().next.set(None);
            } else {
                new_state |= QUEUE_LOCKED;
                queue_head.as_ref().tail.set(None);
                tail.as_ref()
                    .next
                    .set(NonNull::new((state & Waiter::MASK) as *mut Waiter));
            }

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                state = e;
                continue;
            }

            if state & (QUEUED | QUEUE_LOCKED) == QUEUED {
                self.link_queue_or_unpark(new_state);
            }

            if queue_head != head {
                self.unpark_waiters(head);
            }

            return;
        }
    }

    #[cold]
    unsafe fn link_queue_or_unpark(&self, mut state: usize) {
        loop {
            assert_ne!(state & QUEUED, 0);
            assert_ne!(state & QUEUE_LOCKED, 0);

            if state & LOCKED == 0 {
                return self.unpark(state);
            }

            fence(Ordering::Acquire);
            let _ = Waiter::get_and_link_queue(state, |_| {});

            match self.state.compare_exchange_weak(
                state,
                state & !QUEUE_LOCKED,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn unpark(&self, mut state: usize) {
        loop {
            assert_ne!(state & QUEUED, 0);
            assert_ne!(state & QUEUE_LOCKED, 0);

            if state & LOCKED != 0 {
                match self.state.compare_exchange_weak(
                    state,
                    state & !QUEUE_LOCKED,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(e) => state = e,
                }
                continue;
            }

            fence(Ordering::Acquire);
            let (head, tail) = Waiter::get_and_link_queue(state, |_| {});

            let is_writer = tail.as_ref().flags.get() != 0;
            if is_writer {
                if let Some(new_tail) = tail.as_ref().prev.get() {
                    head.as_ref().tail.set(Some(new_tail));
                    self.state.fetch_and(!QUEUE_LOCKED, Ordering::Release);

                    tail.as_ref().prev.set(None);
                    return self.unpark_waiters(tail);
                }
            }

            match self.state.compare_exchange_weak(
                state,
                state & !(Waiter::MASK | QUEUED | QUEUE_LOCKED),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return self.unpark_waiters(tail),
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn unpark_waiters(&self, mut tail: NonNull<Waiter>) {
        loop {
            let waiting_on = tail.as_ref().waiting_on.get();
            let waiting_on = waiting_on.expect("waking a waiter thats not waiting on anything");
            assert_eq!(
                waiting_on,
                NonNull::from(&self.state),
                "waking a waiter thats not waiting on this lock",
            );

            let prev = tail.as_ref().prev.get();
            tail.as_ref().parker.unpark();

            match prev {
                Some(prev) => tail = prev,
                None => return,
            }
        }
    }
}

pub type RwLock<T> = lock_api::RwLock<RawRwLock, T>;
pub type RwLockReadGuard<'a, T> = lock_api::RwLockReadGuard<'a, RawRwLock, T>;
pub type RwLockWriteGuard<'a, T> = lock_api::RwLockWriteGuard<'a, RawRwLock, T>;
pub type MappedRwLockReadGuard<'a, T> = lock_api::MappedRwLockReadGuard<'a, RawRwLock, T>;
pub type MappedRwLockWriteGuard<'a, T> = lock_api::MappedRwLockWriteGuard<'a, RawRwLock, T>;

pub const fn const_rwlock<T>(value: T) -> RwLock<T> {
    RwLock::const_new(<RawRwLock as lock_api::RawRwLock>::INIT, value)
}

#[cfg(test)]
mod tests {
    use crate::RwLock;
    use rand::Rng;
    use std::{
        sync::{
            atomic::{AtomicUsize, Ordering},
            mpsc::channel,
            Arc,
        },
        thread,
    };

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(i32);

    #[test]
    fn smoke() {
        let l = RwLock::new(());
        drop(l.read());
        drop(l.write());
        drop((l.read(), l.read()));
        drop(l.write());
    }

    #[test]
    fn frob() {
        const N: u32 = 10;
        const M: u32 = 1000;

        let r = Arc::new(RwLock::new(()));

        let (tx, rx) = channel::<()>();
        for _ in 0..N {
            let tx = tx.clone();
            let r = r.clone();
            thread::spawn(move || {
                let mut rng = rand::thread_rng();
                for _ in 0..M {
                    if rng.gen_bool(1.0 / N as f64) {
                        drop(r.write());
                    } else {
                        drop(r.read());
                    }
                }
                drop(tx);
            });
        }
        drop(tx);
        let _ = rx.recv();
    }

    #[test]
    fn test_rw_arc_no_poison_wr() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _: Result<(), _> = thread::spawn(move || {
            let _lock = arc2.write();
            panic!();
        })
        .join();
        let lock = arc.read();
        assert_eq!(*lock, 1);
    }

    #[test]
    fn test_rw_arc_no_poison_ww() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _: Result<(), _> = thread::spawn(move || {
            let _lock = arc2.write();
            panic!();
        })
        .join();
        let lock = arc.write();
        assert_eq!(*lock, 1);
    }

    #[test]
    fn test_rw_arc_no_poison_rr() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _: Result<(), _> = thread::spawn(move || {
            let _lock = arc2.read();
            panic!();
        })
        .join();
        let lock = arc.read();
        assert_eq!(*lock, 1);
    }

    #[test]
    fn test_rw_arc_no_poison_rw() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _: Result<(), _> = thread::spawn(move || {
            let _lock = arc2.read();
            panic!()
        })
        .join();
        let lock = arc.write();
        assert_eq!(*lock, 1);
    }

    #[test]
    fn test_rw_arc() {
        let arc = Arc::new(RwLock::new(0));
        let arc2 = arc.clone();
        let (tx, rx) = channel();

        thread::spawn(move || {
            let mut lock = arc2.write();
            for _ in 0..10 {
                let tmp = *lock;
                *lock = -1;
                thread::yield_now();
                *lock = tmp + 1;
            }
            tx.send(()).unwrap();
        });

        // Readers try to catch the writer in the act
        let mut children = Vec::new();
        for _ in 0..5 {
            let arc3 = arc.clone();
            children.push(thread::spawn(move || {
                let lock = arc3.read();
                assert!(*lock >= 0);
            }));
        }

        // Wait for children to pass their asserts
        for r in children {
            assert!(r.join().is_ok());
        }

        // Wait for writer to finish
        rx.recv().unwrap();
        let lock = arc.read();
        assert_eq!(*lock, 10);
    }

    #[test]
    fn test_rw_arc_access_in_unwind() {
        let arc = Arc::new(RwLock::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move || {
            struct Unwinder {
                i: Arc<RwLock<isize>>,
            }
            impl Drop for Unwinder {
                fn drop(&mut self) {
                    let mut lock = self.i.write();
                    *lock += 1;
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let lock = arc.read();
        assert_eq!(*lock, 2);
    }

    #[test]
    fn test_rwlock_unsized() {
        let rw: &RwLock<[i32]> = &RwLock::new([1, 2, 3]);
        {
            let b = &mut *rw.write();
            b[0] = 4;
            b[2] = 5;
        }
        let comp: &[i32] = &[4, 2, 5];
        assert_eq!(&*rw.read(), comp);
    }

    #[test]
    fn test_rwlock_try_read() {
        let lock = RwLock::new(0isize);
        {
            let read_guard = lock.read();

            let read_result = lock.try_read();
            assert!(
                read_result.is_some(),
                "try_read should succeed while read_guard is in scope"
            );

            drop(read_guard);
        }
        {
            let write_guard = lock.write();

            let read_result = lock.try_read();
            assert!(
                read_result.is_none(),
                "try_read should fail while write_guard is in scope"
            );

            drop(write_guard);
        }
    }

    #[test]
    fn test_rwlock_try_write() {
        let lock = RwLock::new(0isize);
        {
            let read_guard = lock.read();

            let write_result = lock.try_write();
            assert!(
                write_result.is_none(),
                "try_write should fail while read_guard is in scope"
            );
            assert!(lock.is_locked());
            assert!(!lock.is_locked_exclusive());

            drop(read_guard);
        }
        {
            let write_guard = lock.write();

            let write_result = lock.try_write();
            assert!(
                write_result.is_none(),
                "try_write should fail while write_guard is in scope"
            );
            assert!(lock.is_locked());
            assert!(lock.is_locked_exclusive());

            drop(write_guard);
        }
    }

    #[test]
    fn test_into_inner() {
        let m = RwLock::new(NonCopy(10));
        assert_eq!(m.into_inner(), NonCopy(10));
    }

    #[test]
    fn test_into_inner_drop() {
        struct Foo(Arc<AtomicUsize>);
        impl Drop for Foo {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }
        let num_drops = Arc::new(AtomicUsize::new(0));
        let m = RwLock::new(Foo(num_drops.clone()));
        assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        {
            let _inner = m.into_inner();
            assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        }
        assert_eq!(num_drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_get_mut() {
        let mut m = RwLock::new(NonCopy(10));
        *m.get_mut() = NonCopy(20);
        assert_eq!(m.into_inner(), NonCopy(20));
    }

    #[test]
    fn test_rwlockguard_sync() {
        fn sync<T: Sync>(_: T) {}

        let rwlock = RwLock::new(());
        sync(rwlock.read());
        sync(rwlock.write());
    }

    #[test]
    fn test_rwlock_debug() {
        let x = RwLock::new(vec![0u8, 10]);

        assert_eq!(format!("{:?}", x), "RwLock { data: [0, 10] }");
        let _lock = x.write();
        assert_eq!(format!("{:?}", x), "RwLock { data: <locked> }");
    }

    #[test]
    fn test_clone() {
        let rwlock = RwLock::new(Arc::new(1));
        let a = rwlock.read();
        let b = a.clone();
        assert_eq!(Arc::strong_count(&b), 2);
    }

    #[test]
    fn test_parking_lot_issue_203() {
        struct Bar(RwLock<()>);

        impl Drop for Bar {
            fn drop(&mut self) {
                let _n = self.0.write();
            }
        }

        thread_local! {
            static B: Bar = Bar(RwLock::new(()));
        }

        thread::spawn(|| {
            B.with(|_| ());

            let a = RwLock::new(());
            let _a = a.read();
        })
        .join()
        .unwrap();
    }

    #[test]
    fn test_rw_write_is_locked() {
        let lock = RwLock::new(0isize);
        {
            let _read_guard = lock.read();

            assert!(lock.is_locked());
            assert!(!lock.is_locked_exclusive());
        }

        {
            let _write_guard = lock.write();

            assert!(lock.is_locked());
            assert!(lock.is_locked_exclusive());
        }
    }
}
