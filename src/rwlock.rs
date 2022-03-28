use super::shared::{SpinWait, Waiter};
use lock_api::RawRwLock as _RawRwLock;
use std::{
    fmt,
    marker::PhantomData,
    pin::Pin,
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

impl fmt::Debug for RawRwLock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("RawRwLock { .. }")
    }
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
        self.try_lock_exclusive_fast()
    }

    #[inline]
    fn lock_exclusive(&self) {
        if !self.try_lock_exclusive() {
            self.lock_exclusive_slow();
        }
    }

    #[inline]
    unsafe fn unlock_exclusive(&self) {
        self.unlock_exclusive_fast()
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
        if !self.unlock_shared_fast() {
            self.unlock_shared_slow();
        }
    }
}

//  --- X86 Specializations

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
impl RawRwLock {
    #[inline(always)]
    fn try_lock_exclusive_assuming(&self, _state: usize) -> bool {
        self.try_lock_exclusive()
    }

    #[inline(always)]
    fn try_lock_exclusive_fast(&self) -> bool {
        // On x86, `lock bts` is often faster for acquiring exclusive ownership
        // than a `lock cmpxchg` as the former wont spuriously fail when a thread
        // is updating the QUEUE_LOCKED bit or adding themselves to the queue.
        unsafe {
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
        }
    }

    #[inline(always)]
    unsafe fn unlock_exclusive_fast(&self) {
        // On x86, we unlock the exclusive lock first, then try and wake later.
        // This is faster than using a `lock cmpxchg` loop as it doesn't have
        // to fail and retry from other threads updating QUEUE_LOCKED bit or queueing themselves.
        let state = self.state.fetch_sub(LOCKED, Ordering::Release);
        debug_assert_eq!(state & (LOCKED | READING), LOCKED);

        // Only try to unpark if there's no QUEUE_LOCKED owner yet and if there's threads queued.
        if state & (QUEUED | QUEUE_LOCKED) == QUEUED {
            self.try_unpark();
        }
    }

    #[cold]
    unsafe fn unlock_shared_and_unpark(&self) {
        // On x86, we unlock the shared lock first, then try and wake later.
        // This is faster than using a `lock cmpxchg` loop as it doesn't have
        // to fail and retry from other threads updating QUEUE_LOCKED bit or queueing themselves.
        let state = self.state.fetch_sub(LOCKED | READING, Ordering::Release);
        debug_assert_eq!(state & (LOCKED | READING), LOCKED | READING);

        // Only try to unpark if there's no QUEUE_LOCKED owner yet and if there's threads queued.
        if state & (QUEUED | QUEUE_LOCKED) == QUEUED {
            self.try_unpark();
        }
    }

    #[cold]
    fn try_unpark(&self) {
        let mut state = self.state.load(Ordering::Relaxed);

        // Try to grab the QUEUE_LOCKED bit to wake up threads iff:
        // - theres no lock holder, as they can be the ones to do the wake up
        // - there are still threads queued to actually wake up
        // - the QUEUE_LOCKED bit isnt held as someone is already doing wake up
        while state & (LOCKED | QUEUED | QUEUE_LOCKED) == QUEUED {
            let new_state = state | QUEUE_LOCKED;
            match self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return unsafe { self.unpark(new_state) },
                Err(e) => state = e,
            }
        }
    }
}

#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
impl RawRwLock {
    #[inline(always)]
    fn try_lock_exclusive_assuming(&self, mut state: usize) -> bool {
        while state & LOCKED == 0 {
            match self.state.compare_exchange_weak(
                state,
                state | LOCKED,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(e) => state = e,
            }
        }

        false
    }

    #[inline(always)]
    fn try_lock_exclusive_fast(&self) -> bool {
        self.state
            .compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    #[inline(always)]
    unsafe fn unlock_exclusive_fast(&self) {
        if self
            .state
            .compare_exchange(LOCKED, UNLOCKED, Ordering::Release, Ordering::Relaxed)
            .is_err()
        {
            self.unlock_and_unpark();
        }
    }

    #[inline(always)]
    unsafe fn unlock_shared_and_unpark(&self) {
        self.unlock_and_unpark()
    }

    #[cold]
    unsafe fn unlock_and_unpark(&self, mut state: usize) {
        let state = self.state.load(Ordering::Relaxed);
        loop {
            assert_ne!(state & LOCKED, 0);
            assert_ne!(state & QUEUED, 0);

            // Unlocks the rwlock and tries to grab the QUEUE_LOCKED bit for wake up.
            let mut new_state = state & !LOCKED;
            new_state |= QUEUE_LOCKED;

            // Also unset the READING bit if the caller was the last shared owner
            if state & READING != 0 {
                new_state &= !READING;
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

            if state & QUEUE_LOCKED == 0 {
                self.unpark(new_state);
            }

            return;
        }
    }
}

//  --- Generic Code

impl RawRwLock {
    #[inline(always)]
    fn try_lock_shared_assuming(&self, state: usize) -> Option<Result<usize, usize>> {
        if state != UNLOCKED {
            if state & (LOCKED | READING | QUEUED) != (LOCKED | READING) {
                return None;
            }
        }

        if let Some(with_reader) = state.checked_add(1 << READER_SHIFT) {
            return Some(self.state.compare_exchange_weak(
                state,
                with_reader | LOCKED | READING,
                Ordering::Acquire,
                Ordering::Relaxed,
            ));
        }

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

    #[inline(always)]
    unsafe fn unlock_shared_fast(&self) -> bool {
        // Just go to the slow path if we're not the only reader
        let state = self.state.load(Ordering::Relaxed);
        if state != SINGLE_READER {
            return false;
        }

        self.state
            .compare_exchange(SINGLE_READER, UNLOCKED, Ordering::Release, Ordering::Relaxed)
            .is_ok()
    }

    #[cold]
    unsafe fn unlock_shared_slow(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        while state & QUEUED == 0 {
            assert_ne!(state & LOCKED, 0);
            assert_ne!(state & READING, 0);
            assert_ne!(state >> READER_SHIFT, 0);

            let mut new_state = state - (1 << READER_SHIFT);
            if state == SINGLE_READER {
                new_state = UNLOCKED;
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

        if readers == 1 {
            self.unlock_shared_and_unpark();
        }
    }

    #[cold]
    fn lock_exclusive_slow(&self) {
        let is_writer = true;
        let try_lock = |state: usize| -> Option<bool> {
            match state & LOCKED {
                0 => Some(self.try_lock_exclusive_assuming(state)),
                _ => None,
            }
        };

        self.lock_common(is_writer, try_lock)
    }

    #[cold]
    fn lock_shared_slow(&self) {
        let is_writer = false;
        let try_lock = |state: usize| -> Option<bool> {
            let result = self.try_lock_shared_assuming(state)?;
            Some(result.is_ok())
        };

        self.lock_common(is_writer, try_lock)
    }

    fn lock_common(&self, is_writer: bool, mut try_lock: impl FnMut(usize) -> Option<bool>) {
        Waiter::with(|waiter| {
            waiter.waiting_on.set(Some(NonNull::from(self).cast()));
            waiter.flags.set(is_writer as usize);

            let mut spin = SpinWait::default();
            loop {
                let mut state = self.state.load(Ordering::Relaxed);
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

                    if unsafe { self.try_queue(&mut state, waiter.as_ref()) } {
                        assert!(waiter.parker.park(None));
                        break;
                    }
                }
            }
        });
    }

    #[cold]
    pub(super) unsafe fn try_requeue(&self, waiter: Pin<&Waiter>) -> bool {
        let is_writer = waiter.flags.get() != 0;
        assert!(is_writer);

        let waiting_on = waiter.waiting_on.get();
        assert_eq!(waiting_on, Some(NonNull::from(self).cast()));

        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & LOCKED == 0 {
                return false;
            }
            if self.try_queue(&mut state, waiter.as_ref()) {
                return true;
            }
        }
    }

    unsafe fn try_queue(&self, state: &mut usize, waiter: Pin<&Waiter>) -> bool {
        waiter.prev.set(None);
        
        let waiter_ptr = &*waiter as *const Waiter as usize;
        let mut new_state = (*state & !Waiter::MASK) | waiter_ptr | QUEUED;

        if *state & QUEUED == 0 {
            let readers = *state >> READER_SHIFT;
            waiter.counter.store(readers, Ordering::Relaxed);
            waiter.next.set(None);
            waiter.tail.set(Some(NonNull::from(&*waiter)));
        } else {
            let head = NonNull::new((*state & Waiter::MASK) as *mut Waiter);
            new_state |= QUEUE_LOCKED;
            waiter.next.set(head);
            waiter.tail.set(None);
        }

        if let Err(e) = self.state.compare_exchange_weak(
            *state,
            new_state,
            Ordering::Release,
            Ordering::Relaxed,
        ) {
            *state = e;
            return false;
        }

        if *state & (QUEUED | QUEUE_LOCKED) == QUEUED {
            self.link_queue_or_unpark(new_state);
        }

        true
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
                NonNull::from(self).cast(),
                "waking a waiter thats not waiting on this lock",
            );

            let prev = tail.as_ref().prev.get();
            tail.as_ref().parker.unpark();

            tail = match prev {
                Some(prev) => prev,
                None => break,
            };
        }
    }
}

/// A reader-writer lock
///
/// This type of lock allows a number of readers or at most one writer at any
/// point in time. The write portion of this lock typically allows modification
/// of the underlying data (exclusive access) and the read portion of this lock
/// typically allows for read-only access (shared access).
///
/// This lock uses a task-fair locking policy which avoids both reader and
/// writer starvation. This means that readers trying to acquire the lock will
/// block even if the lock is unlocked when there are writers waiting to acquire
/// the lock. Because of this, attempts to recursively acquire a read lock
/// within a single thread may result in a deadlock.
///
/// The type parameter `T` represents the data that this lock protects. It is
/// required that `T` satisfies `Send` to be shared across threads and `Sync` to
/// allow concurrent access through readers. The RAII guards returned from the
/// locking methods implement `Deref` (and `DerefMut` for the `write` methods)
/// to allow access to the contained of the lock.
///
/// # Fairness
///
/// A typical unfair lock can often end up in a situation where a single thread
/// quickly acquires and releases the same lock in succession, which can starve
/// other threads waiting to acquire the rwlock. While this improves throughput
/// because it doesn't force a context switch when a thread tries to re-acquire
/// a rwlock it has just released, this can starve other threads.
///
/// This rwlock is unfair by default. This means that a thread which unlocks the
/// rwlock is allowed to re-acquire it again even when other threads are waiting
/// for the lock.
///
/// This greatly improves throughput (read "performance") but could potentially
/// starve an unlucky thread when there's constant lock contention. The rwlock
/// tries to at least wake up threads in the order that they we're queued as an
/// attempt to avoid starvation, but it is entirely up to the OS scheduler.
///
/// # Differences from the standard library `RwLock`
///
/// - Task-fair locking policy instead of an unspecified platform default.
/// - No poisoning, the lock is released normally on panic.
/// - Only requires 1 word of space, whereas the standard library boxes the
///   `RwLock` due to platform limitations.
/// - Can be statically constructed.
/// - Does not require any drop glue when dropped.
/// - Inline fast path for the uncontended case.
/// - Efficient handling of micro-contention using adaptive spinning.
/// - Allows raw locking & unlocking without a guard.
///
/// # Examples
///
/// ```
/// use usync::RwLock;
///
/// let lock = RwLock::new(5);
///
/// // many reader locks can be held at once
/// {
///     let r1 = lock.read();
///     let r2 = lock.read();
///     assert_eq!(*r1, 5);
///     assert_eq!(*r2, 5);
/// } // read locks are dropped at this point
///
/// // only one write lock may be held, however
/// {
///     let mut w = lock.write();
///     *w += 1;
///     assert_eq!(*w, 6);
/// } // write lock is dropped here
/// ```
pub type RwLock<T> = lock_api::RwLock<RawRwLock, T>;

/// RAII structure used to release the shared read access of a lock when
/// dropped.
pub type RwLockReadGuard<'a, T> = lock_api::RwLockReadGuard<'a, RawRwLock, T>;

/// RAII structure used to release the exclusive write access of a lock when
/// dropped.
pub type RwLockWriteGuard<'a, T> = lock_api::RwLockWriteGuard<'a, RawRwLock, T>;

/// An RAII read lock guard returned by `RwLockReadGuard::map`, which can point to a
/// subfield of the protected data.
///
/// The main difference between `MappedRwLockReadGuard` and `RwLockReadGuard` is that the
/// former doesn't support temporarily unlocking and re-locking, since that
/// could introduce soundness issues if the locked object is modified by another
/// thread.
pub type MappedRwLockReadGuard<'a, T> = lock_api::MappedRwLockReadGuard<'a, RawRwLock, T>;

/// An RAII write lock guard returned by `RwLockWriteGuard::map`, which can point to a
/// subfield of the protected data.
///
/// The main difference between `MappedRwLockWriteGuard` and `RwLockWriteGuard` is that the
/// former doesn't support temporarily unlocking and re-locking, since that
/// could introduce soundness issues if the locked object is modified by another
/// thread.
pub type MappedRwLockWriteGuard<'a, T> = lock_api::MappedRwLockWriteGuard<'a, RawRwLock, T>;

/// Creates a new instance of an `RwLock<T>` which is unlocked.
///
/// This allows creating a `RwLock<T>` in a constant context on stable Rust.
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
