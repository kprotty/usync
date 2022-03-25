use super::{shared::Waiter, MutexGuard, RawRwLock};
use lock_api::RawMutex as _RawMutex;
use std::{
    marker::PhantomData,
    ptr::NonNull,
    sync::atomic::{fence, AtomicUsize, Ordering},
    time::{Duration, Instant},
};

const EMPTY: usize = 0;
const SIGNAL: usize = 1;
const SIGNAL_MASK: usize = 0b111;
const SIGNAL_LOCKED: usize = SIGNAL_MASK + 1;

#[derive(Default)]
pub struct Condvar {
    state: AtomicUsize,
    _p: PhantomData<*const Waiter>,
}

impl Condvar {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(EMPTY),
            _p: PhantomData,
        }
    }

    pub fn wait<T: ?Sized>(&self, mutex_guard: &mut MutexGuard<'_, T>) {
        let result = self.wait_with(mutex_guard, None);
        assert!(!result.timed_out());
    }

    pub fn wait_for<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Duration,
    ) -> WaitTimeoutResult {
        self.wait_until(mutex_guard, Instant::now() + timeout)
    }

    pub fn wait_until<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Instant,
    ) -> WaitTimeoutResult {
        self.wait_with(mutex_guard, Some(timeout))
    }

    #[cold]
    fn wait_with<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Option<Instant>,
    ) -> WaitTimeoutResult {
        Waiter::with(|waiter| unsafe {
            let is_writer = true;
            waiter.flags.set(is_writer as usize);

            let raw_mutex = MutexGuard::mutex(mutex_guard).raw();
            let rwlock_state = NonNull::from(&raw_mutex.rwlock.state);

            waiter.waiting_on.set(Some(rwlock_state));
            waiter.prev.set(None);

            let mut state = self.state.load(Ordering::Relaxed);
            loop {
                let head = NonNull::new((state & Waiter::MASK) as *mut Waiter);
                waiter.next.set(head);

                let waiter_ptr = &*waiter as *const Waiter as usize;
                let mut new_state = (state & !Waiter::MASK) | waiter_ptr;

                if head.is_some() {
                    waiter.tail.set(Some(NonNull::from(&*waiter)));
                } else {
                    new_state |= SIGNAL_LOCKED;
                    waiter.tail.set(None);
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

                if head.is_some() && (state & SIGNAL_LOCKED == 0) {
                    self.link_queue_or_unpark(new_state);
                }

                raw_mutex.unlock();
                break;
            }

            let timed_out = !waiter.parker.park(timeout);
            if timed_out {
                self.notify_all();
                assert!(waiter.parker.park(None));
            }

            raw_mutex.lock();
            WaitTimeoutResult(timed_out)
        })
    }

    #[inline]
    pub fn notify_one(&self) {
        let state = self.state.load(Ordering::Relaxed);
        if state == EMPTY {
            self.notify_one_slow(state);
        }
    }

    #[cold]
    fn notify_one_slow(&self, mut state: usize) {
        while state != EMPTY {
            if state & SIGNAL_LOCKED != 0 {
                // Try to acquire the signal lock to wake up the queued threads.
                let new_state = state | SIGNAL_LOCKED;
                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                unsafe { self.unpark(new_state) };
                return;
            }

            // Bail if all threads are going to be woken up eventually.
            let signals = state & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return;
            }

            // Tell the signal lock holder to wake up the thread in our place.
            match self.state.compare_exchange_weak(
                state,
                state + SIGNAL,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(e) => state = e,
            }
        }
    }

    #[inline]
    pub fn notify_all(&self) {
        let state = self.state.load(Ordering::Relaxed);
        if state != EMPTY {
            self.notify_all_slow(state);
        }
    }

    #[cold]
    fn notify_all_slow(&self, mut state: usize) {
        while state != EMPTY {
            // If no thread is currently waking up the waiters, grab all of them to wake up.
            if state & SIGNAL_LOCKED == 0 {
                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    EMPTY,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                unsafe { self.unpark_waiters(state) };
                return;
            }

            let signals = state & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return;
            }

            match self.state.compare_exchange_weak(
                state,
                state | SIGNAL_MASK,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn link_queue_or_unpark(&self, mut state: usize) {
        loop {
            assert_eq!(state & SIGNAL_LOCKED, 0);

            let signals = state & SIGNAL_MASK;
            if signals > 0 {
                return self.unpark(state);
            }

            fence(Ordering::Acquire);
            let _ = Waiter::get_and_link_queue(state, |_| {});

            match self.state.compare_exchange_weak(
                state,
                state & !SIGNAL_LOCKED,
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
        let mut scanned = 0;
        let mut unparked = None;

        loop {
            assert_ne!(state & SIGNAL_LOCKED, 0);

            let signals = state & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return self.unpark_all();
            }

            fence(Ordering::Acquire);
            let (head, tail) = Waiter::get_and_link_queue(state, |_| {});

            let (mut front, back) = unparked.unwrap_or_else(|| {
                scanned += 1;
                (tail, tail)
            });

            let max_scan = signals + 1;
            while scanned < max_scan {
                if let Some(prev) = front.as_ref().prev.get() {
                    front = prev;
                    scanned += 1;
                } else {
                    break;
                }
            }

            if scanned >= SIGNAL_MASK {
                return self.unpark_all();
            }

            let mut new_state = state & !SIGNAL_LOCKED;
            new_state -= signals.saturating_sub(scanned) * SIGNAL;

            if let Some(new_tail) = front.as_ref().prev.get() {
                head.as_ref().tail.set(Some(new_tail));
            } else {
                new_state &= !Waiter::MASK;
            }

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                head.as_ref().tail.set(Some(back));
                unparked = Some((front, back));
                state = e;
                continue;
            }

            front.as_ref().prev.set(None);
            self.unpark_requeue(head, tail);
            return;
        }
    }

    #[cold]
    unsafe fn unpark_all(&self) {
        let state = self.state.swap(EMPTY, Ordering::Acquire);
        assert_ne!(state & SIGNAL_LOCKED, 0);
        assert_eq!(state & SIGNAL_MASK, SIGNAL_MASK);

        self.unpark_waiters(state);
    }

    #[cold]
    unsafe fn unpark_waiters(&self, state: usize) {
        let (head, tail) = Waiter::get_and_link_queue(state, |_| {});
        self.unpark_requeue(head, tail);
    }

    #[cold]
    unsafe fn unpark_requeue(&self, head: NonNull<Waiter>, tail: NonNull<Waiter>) {
        let waiting_on = head.as_ref().waiting_on.get();
        let rwlock_state = waiting_on.expect("Condvar waiter not waiting on anything");

        // SAFETY:
        // RawRwLock is repr(transparent) to it's state.
        // RawMutex is repr(transparent) to RawRwLock.
        let raw_rwlock = rwlock_state.cast::<RawRwLock>();
        raw_rwlock.as_ref().unpark_requeue(head, tail);
    }
}

/// A type indicating whether a timed wait on a condition variable returned
/// due to a time out or not.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct WaitTimeoutResult(bool);

impl WaitTimeoutResult {
    /// Returns whether the wait was known to have timed out.
    #[inline]
    pub fn timed_out(self) -> bool {
        self.0
    }
}
