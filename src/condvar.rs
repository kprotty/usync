use super::{
    wait_queue::{self, WaitResult},
    MutexGuard,
};
use std::{
    sync::atomic::{AtomicUsize, Ordering},
    time::{Duration, Instant},
};

#[derive(Copy, Clone, Eq, PartialEq)]
pub struct WaitTimeoutResult(bool);

impl WaitTimeoutResult {
    pub fn timed_out(&self) -> bool {
        self.0
    }
}

const BITS: u32 = usize::BITS / 2;
const MASK: usize = (1 << BITS) - 1;

const WAITER_SHIFT: u32 = BITS * 0;
const SIGNAL_SHIFT: u32 = BITS * 1;

#[derive(Default)]
pub struct Condvar {
    state: AtomicUsize,
}

impl Condvar {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(0),
        }
    }

    pub fn wait<T>(&self, guard: &mut MutexGuard<'_, T>) {
        let wait_timeout_result = self.wait_with(guard, None);
        assert!(!wait_timeout_result.timed_out());
    }

    pub fn wait_for<T>(
        &self,
        guard: &mut MutexGuard<'_, T>,
        duration: Duration,
    ) -> WaitTimeoutResult {
        self.wait_until(guard, Instant::now() + duration)
    }

    pub fn wait_until<T>(
        &self,
        guard: &mut MutexGuard<'_, T>,
        deadline: Instant,
    ) -> WaitTimeoutResult {
        self.wait_with(guard, Some(deadline))
    }

    fn wait_with<T>(
        &self,
        guard: &mut MutexGuard<'_, T>,
        deadline: Option<Instant>,
    ) -> WaitTimeoutResult {
        let state = self.state.fetch_add(1 << WAITER_SHIFT, Ordering::Relaxed);
        let waiters = (state >> WAITER_SHIFT) & MASK;
        assert_ne!(waiters, MASK, "Too many Condvar waiters");

        let mut timed_out = false;
        guard.mutex.release();

        while let Err(_) = self
            .state
            .fetch_update(Ordering::Acquire, Ordering::Relaxed, |state| {
                let waiters = (state >> WAITER_SHIFT) & MASK;
                let waiters = waiters
                    .checked_sub(1)
                    .expect("Waiter waiting without being registered");

                let signaled = (state >> SIGNAL_SHIFT) & MASK;
                if let Some(signaled) = signaled.checked_sub(1) {
                    return Some((waiters << WAITER_SHIFT) | (signaled << SIGNAL_SHIFT));
                }

                if timed_out {
                    return Some(waiters << WAITER_SHIFT);
                }

                None
            })
        {
            let address = self as *const _ as usize;
            let validate = || {
                let state = self.state.load(Ordering::Relaxed);
                let signaled = (state >> SIGNAL_SHIFT) & MASK;
                signaled == 0
            };

            let wait_result = wait_queue::wait(address, validate, deadline);
            timed_out = matches!(wait_result, WaitResult::TimedOut);
        }

        guard.mutex.acquire_waiting();
        WaitTimeoutResult(timed_out)
    }

    pub fn notify_one(&self) {
        self.signal(1)
    }

    pub fn notify_all(&self) {
        self.signal(usize::MAX)
    }

    fn signal(&self, max_wake: usize) {
        if let Ok(state) = self
            .state
            .fetch_update(Ordering::Release, Ordering::Relaxed, |state| {
                let waiters = (state >> WAITER_SHIFT) & MASK;
                if waiters == 0 {
                    return None;
                }

                let mut signaled = (state >> SIGNAL_SHIFT) & MASK;
                if waiters == signaled {
                    return None;
                }

                assert!(waiters < signaled);
                signaled += (signaled - waiters).min(max_wake);
                Some((waiters << WAITER_SHIFT) | (signaled << SIGNAL_SHIFT))
            })
        {
            let waiters = (state >> WAITER_SHIFT) & MASK;
            let signaled = (state >> SIGNAL_SHIFT) & MASK;
            let notified = (signaled - waiters).min(max_wake);

            let address = self as *const _ as usize;
            wait_queue::wake(address, notified);
        }
    }
}
