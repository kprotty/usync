#![allow(unstable_name_collisions)]
use super::{
    shared::{fence_acquire, invalid_mut, StrictProvenance, Waiter},
    MutexGuard, RawRwLock,
};
use lock_api::RawMutex as _RawMutex;
use std::{
    fmt,
    pin::Pin,
    ptr::NonNull,
    sync::atomic::{AtomicPtr, Ordering},
    time::{Duration, Instant},
};

const EMPTY: usize = 0;
const SIGNAL: usize = 1;
const SIGNAL_MASK: usize = 0b111;
const QUEUE_LOCKED: usize = SIGNAL_MASK + 1;

/// A Condition Variable
///
/// Condition variables represent the ability to block a thread such that it
/// consumes no CPU time while waiting for an event to occur. Condition
/// variables are typically associated with a boolean predicate (a condition)
/// and a mutex. The predicate is always verified inside of the mutex before
/// determining that thread must block.
///
/// Note that each condvar can be used with multiple mutexes at a time.
/// This is different compared to `parking_lot`'s condvar, which doesn't allow
/// multiple threads waiting on the same condvar with different mutexes.
///
/// # Differences from the standard library `Condvar`
///
/// - Spurious wake ups are avoided. This means a wait will try to not return early
///   unless woken up from a call to `notify_one` or `notify_all`. This is not fool-proof
///   as events such as timeouts or stacked `notify_one` calls could cause a spurious wake up to occur.
/// - `Condvar::notify_all` will try to only wake up a single thread with the rest being
///   requeued to wait for the `Mutex` to be unlocked by the thread that was
///   woken up.
/// - Only requires 1 word of space, whereas the standard library boxes the
///   `Condvar` due to platform limitations.
/// - Can be statically constructed (requires the `const_fn` nightly feature).
/// - Does not require any drop glue when dropped.
/// - Inline fast path for the uncontended case.
///
/// # Examples
///
/// ```
/// use usync::{Mutex, Condvar};
/// use std::sync::Arc;
/// use std::thread;
///
/// let pair = Arc::new((Mutex::new(false), Condvar::new()));
/// let pair2 = pair.clone();
///
/// // Inside of our lock, spawn a new thread, and then wait for it to start
/// thread::spawn(move|| {
///     let &(ref lock, ref cvar) = &*pair2;
///     let mut started = lock.lock();
///     *started = true;
///     cvar.notify_one();
/// });
///
/// // wait for the thread to start up
/// let &(ref lock, ref cvar) = &*pair;
/// let mut started = lock.lock();
/// if !*started {
///     cvar.wait(&mut started);
/// }
/// // Note that we used an if instead of a while loop above. This is only
/// // possible because usync's Condvar will only spuriously wake up when timeouts
/// // are involved. This means that wait() will only return after notify_one or
/// // notify_all is called in this instance.
/// ```
#[derive(Default)]
pub struct Condvar {
    /// This atomic integer holds the current state of the Condvar instance.
    /// The four least significant bits are used to notify_one calls and the state of the Condvar.
    ///
    /// # State table:
    ///
    /// SIGNAL_MASK | QUEUE_LOCKED | Remaining | Description
    ///       0     |       0       |     0     | The condvar is empty and there's nothing waiting on it.
    /// ------------+---------------+-----------+-----------------------------------------------------------------
    ///       0     |       0       |  *Waiter  | The Remaining bits point to the head Waiter node of the
    ///             |               |           | waiting thread queue.
    /// ------------+---------------+-----------+-----------------------------------------------------------------
    ///       0     |       1       |  *Waiter  | The Remaining bits point to the head Waiter node of the
    ///             |               |           | waiting thread queue. There is also a thread which is
    ///             |               |           | updating the waiting-thread queue and possibly waking from it.
    /// ------------+---------------+-----------+-----------------------------------------------------------------
    ///      n>0    |       1       |  *Waiter  | The Remaining bits point to the head Waiter node of the
    ///             |               |           | waiting thread queue. There is also a thread which is
    ///             |               |           | updating the waiting-thread queue and waking from it.
    ///             |               |           | `n` is the amount of `notify_one` calls that happened since the
    ///             |               |           | QUEUE_LOCKED bit was taken for waiting-thread queue updating/waking.
    //              |               |           | If `n == SIGNAL_MASK` then all threads in the queue are woken up.
    /// ------------+---------------+-----------+-----------------------------------------------------------------
    state: AtomicPtr<Waiter>,
}

impl fmt::Debug for Condvar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Condvar { .. }")
    }
}

unsafe impl Send for Condvar {}
unsafe impl Sync for Condvar {}

impl Condvar {
    /// Creates a new condition variable which is ready to be waited on and
    /// notified.
    pub const fn new() -> Self {
        Self {
            state: AtomicPtr::new(invalid_mut(EMPTY)),
        }
    }

    /// Blocks the current thread until this condition variable receives a
    /// notification.
    ///
    /// This function will atomically unlock the mutex specified (represented by
    /// `mutex_guard`) and block the current thread. This means that any calls
    /// to `notify_*()` which happen logically after the mutex is unlocked are
    /// candidates to wake this thread up. When this function call returns, the
    /// lock specified will have been re-acquired.
    pub fn wait<T: ?Sized>(&self, mutex_guard: &mut MutexGuard<'_, T>) {
        let result = self.wait_with(mutex_guard, None);
        assert!(!result.timed_out());
    }

    /// Waits on this condition variable for a notification, timing out after
    /// the specified time instant.
    ///
    /// The semantics of this function are equivalent to `wait()` except that
    /// the thread will be blocked roughly until `timeout` is reached. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that may not cause the maximum
    /// amount of time waited to be precisely `timeout`.
    ///
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time.
    ///
    /// The returned `WaitTimeoutResult` value indicates if the timeout is
    /// known to have elapsed.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    pub fn wait_until<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Instant,
    ) -> WaitTimeoutResult {
        match timeout.checked_duration_since(Instant::now()) {
            Some(until_deadline) => self.wait_for(mutex_guard, until_deadline),
            None => WaitTimeoutResult(true),
        }
    }

    /// Waits on this condition variable for a notification, timing out after a
    /// specified duration.
    ///
    /// The semantics of this function are equivalent to `wait()` except that
    /// the thread will be blocked for roughly no longer than `timeout`. This
    /// method should not be used for precise timing due to anomalies such as
    /// preemption or platform differences that may not cause the maximum
    /// amount of time waited to be precisely `timeout`.
    ///
    /// Note that the best effort is made to ensure that the time waited is
    /// measured with a monotonic clock, and not affected by the changes made to
    /// the system time.
    ///
    /// The returned `WaitTimeoutResult` value indicates if the timeout is
    /// known to have elapsed.
    ///
    /// Like `wait`, the lock specified will be re-acquired when this function
    /// returns, regardless of whether the timeout elapsed or not.
    pub fn wait_for<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Duration,
    ) -> WaitTimeoutResult {
        self.wait_with(mutex_guard, Some(timeout))
    }

    #[cold]
    fn wait_with<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Option<Duration>,
    ) -> WaitTimeoutResult {
        Waiter::with(|waiter| unsafe {
            // MutexGuard acquired the internal RawRwLock as a writer
            let is_writer = true;
            waiter.flags.set(is_writer as usize);

            // RawMutex is just a wrapper around RawRwLock.
            let raw_mutex = MutexGuard::mutex(mutex_guard).raw();
            let raw_rwlock = NonNull::from(&raw_mutex.rwlock);

            waiter.waiting_on.set(Some(raw_rwlock.cast()));
            waiter.prev.set(None);

            // Push our waiter to the wait queue and report if we acquired the QUEUE_LOCKED bit
            let mut state = self.state.load(Ordering::Relaxed);
            let signal_locked = loop {
                let head = NonNull::new(state.map_addr(|addr| addr & Waiter::MASK));
                waiter.next.set(head);

                let waiter_ptr = NonNull::from(&*waiter).as_ptr();
                let mut new_state = waiter_ptr.map_addr(|addr| {
                    let state_bits = state.addr() & !Waiter::MASK;
                    addr | state_bits
                });

                // If we're the first waiter, set our tail to be ourselves.
                // This allows Waiter::get_and_link_queue() to found our tail.
                // If we're not the first waiter, try to acquire the QUEUE_LOCKED bit to link the queue.
                if head.is_some() {
                    waiter.tail.set(None);
                    new_state = new_state.map_addr(|addr| addr | QUEUE_LOCKED);
                } else {
                    waiter.tail.set(Some(NonNull::from(&*waiter)));
                }

                // Release barrier to ensure that our waiter writes above
                // happen before the QUEUE_LOCKED bit holder operates on the queue visible from state.
                match self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break head.is_some() && (state.addr() & QUEUE_LOCKED == 0),
                    Err(e) => state = e,
                }
            };

            struct DropGuard<'a>(&'a crate::RawMutex);
            impl<'a> Drop for DropGuard<'a> {
                fn drop(&mut self) {
                    self.0.lock();
                }
            }

            // Now that our waiter is registered on the state, unlock the mutex in order to block the thread.
            // Make sure to re-acquire the mutex back when returning (even in the case of a panic).
            raw_mutex.unlock();
            let _drop_guard = DropGuard(raw_mutex);

            // Make sure to link and unset the QUEUE_LOCKED
            if signal_locked {
                state = self.state.load(Ordering::Relaxed);
                self.link_queue_or_unpark(state);
            }

            // Block the thread and wait for a wake up or timeout.
            let timed_out = !waiter.parker.park(timeout);

            // On timeout, we must ensure that our waiter is no longer in the waiting-thread queue.
            // We could try to grab the QUEUE_LOCKED bit and remove ourselves, but it's not guaranteed
            // that we're still in the waiting-thread queue; We could have been requeued to the RawRWLock.
            // Instead, just wake everything up and wait for our waiter specifically to be woken up.
            if timed_out {
                self.notify_all();
                assert!(waiter.parker.park(None));
            }

            // return whether we timed out (will re-acquire the mutex when returning)
            WaitTimeoutResult(timed_out)
        })
    }

    #[cold]
    unsafe fn link_queue_or_unpark(&self, mut state: *mut Waiter) {
        loop {
            assert_ne!(state.addr() & QUEUE_LOCKED, 0);

            // If `notify_*` calls occured while we we're trying to link the queue,
            // then we are now responsible for doing the wake up from the notifications.
            let signals = state.addr() & SIGNAL_MASK;
            if signals > 0 {
                return self.unpark(state, 0);
            }

            // Fix the prev links in the waiter queue now that we hold the QUEUE_LOCKED bit.
            // Acquire barrier to ensure writes to waiters pushed to the queue happen before we start fixing it.
            fence_acquire(&self.state);
            let _ = Waiter::get_and_link_queue(state, |_| {});

            // Finally, try to the release the QUEUE_LOCKED bit.
            // Release barrier to ensure the writes we did above happen before the next QUEUE_LOCKED bit holder.
            match self.state.compare_exchange_weak(
                state,
                state.map_addr(|addr| addr & !QUEUE_LOCKED),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(e) => state = e,
            }
        }
    }

    /// Wakes up one blocked thread on this condvar.
    ///
    /// Returns **a hint** as to whether a thread was woken up.
    ///
    /// If there is a blocked thread on this condition variable, then it will
    /// be woken up from its call to `wait` or `wait_timeout`. Calls to
    /// `notify_one` are not buffered in any way *to subsequent waiters*.
    ///
    /// To wake up all threads, see `notify_all()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use usync::Condvar;
    ///
    /// let condvar = Condvar::new();
    ///
    /// // do something with condvar, share it with other threads
    ///
    /// if !condvar.notify_one() {
    ///     println!("Nobody was listening for this.");
    /// }
    /// ```
    #[inline]
    pub fn notify_one(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        if state.addr() == EMPTY {
            return false;
        }

        self.notify_one_slow(state)
    }

    #[cold]
    fn notify_one_slow(&self, mut state: *mut Waiter) -> bool {
        loop {
            if state.addr() == EMPTY {
                return false;
            }

            if state.addr() & QUEUE_LOCKED == 0 {
                // Try to acquire the QUEUE_LOCKED bit to wake up the queued threads.
                let new_state = state.map_addr(|addr| addr | QUEUE_LOCKED);
                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                unsafe { self.unpark(new_state, 1) };
                return true;
            }

            // Bail if all threads are going to be woken up eventually.
            let signals = state.addr() & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return false;
            }

            // Tell the QUEUE_LOCKED bit holder to wake up the thread in our place.
            // Release barrier to ensure this notify_one() happens before
            // the wake ups done by the QUEUE_LOCKED bit holder.
            match self.state.compare_exchange_weak(
                state,
                state.map_addr(|addr| addr + SIGNAL),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(e) => state = e,
            }
        }
    }

    /// Wakes up all blocked threads on this condvar.
    ///
    /// Returns **a hint** as to whether threads were woken up.
    ///
    /// This method will ensure that any current waiters on the condition
    /// variable are awoken. Calls to `notify_all()` are not buffered in any
    /// way *to subsequent waiters*.
    ///
    /// To wake up only one thread, see `notify_one()`.
    #[inline]
    pub fn notify_all(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        if state.addr() == EMPTY {
            return false;
        }

        self.notify_all_slow(state)
    }

    #[cold]
    fn notify_all_slow(&self, mut state: *mut Waiter) -> bool {
        loop {
            if state.addr() == EMPTY {
                return false;
            }

            // If no thread is currently waking up the waiters, grab all of them to wake up.
            // Acquire barrier to ensure writes to pushed waiters happen before we start waking them up.
            if state.addr() & QUEUE_LOCKED == 0 {
                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    state.with_addr(EMPTY),
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                unsafe { self.unpark_waiters(state) };
                return true;
            }

            let signals = state.addr() & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return false;
            }

            // Tell the QUEUE_LOCKED bit holder to wake up all threads in our place.
            // Release barrier to ensure this notify_one() happens before
            // the wake ups done by the QUEUE_LOCKED bit holder.
            match self.state.compare_exchange_weak(
                state,
                state.map_addr(|addr| addr | SIGNAL_MASK),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn unpark(&self, mut state: *mut Waiter, also_wake: usize) {
        let mut scanned = 0;
        let mut unparked = None;

        loop {
            assert_ne!(state.addr() & QUEUE_LOCKED, 0);

            // If enough threads have sent notifications, just wake up all waiters.
            let signals = state.addr() & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return self.unpark_all();
            }

            // Fix and get the ends of the wait queue in order to wake up waiters starting from the tail.
            // Acquire barrier ensures that writes to waiters pushed to the queue
            // happen before we start fixing/getting it.
            fence_acquire(&self.state);
            let (head, tail) = Waiter::get_and_link_queue(state, |_| {});

            // Get the head of the waiter nodes we plan on waking up.
            let mut front = unparked.unwrap_or_else(|| {
                scanned += 1;
                tail
            });

            // Bounded scan to collect enough waiter nodes to match current buffered signals.
            let max_scan = signals + also_wake;
            while scanned < max_scan {
                if let Some(prev) = front.as_ref().prev.get() {
                    front = prev;
                    scanned += 1;
                } else {
                    break;
                }
            }

            // If enough threads have been scanned, just wake up all waiters.
            unparked = Some(front);
            if scanned >= SIGNAL_MASK {
                return self.unpark_all();
            }

            // If we're only waking up a portion of the queue,
            // try to modify that queue to remove said portion only.
            if let Some(new_tail) = front.as_ref().prev.get() {
                head.as_ref().tail.set(Some(new_tail));
                new_tail.as_ref().next.set(None);

                // Use saturating sub as we may have scanned to wake up a bit more than whats signaled
                // if unpark() is being called by `notify_one()` which wakes without adding a SIGNAL.
                let new_state = state.map_addr(|mut addr| {
                    addr &= !QUEUE_LOCKED;
                    addr -= signals.saturating_sub(scanned) * SIGNAL;
                    addr
                });

                // Release barrier ensures the head/tail access above happen before we release the QUEUE_LOCKED bit before wake up.
                match self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return self.unpark_requeue(front),
                    Err(e) => state = e,
                }

                // Reverse wha we did above
                new_tail.as_ref().next.set(Some(front));
                head.as_ref().tail.set(Some(tail));
                continue;
            }

            // Wake all by zeroing out all the SIGNALS, unsetting the QUEUE_LOCKED bit, and unsetting the waiter queue head pointer.
            // Release barrier ensures the head/tail access above happen before we release the QUEUE_LOCKED bit before wake up.
            match self.state.compare_exchange_weak(
                state,
                state.with_addr(EMPTY),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return self.unpark_requeue(head),
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn unpark_all(&self) {
        // Wake all by zeroing everything.
        // Acquire barrier ensures that writes done to pushed waiters happen before we start waking them.
        let state = self.state.swap(invalid_mut(EMPTY), Ordering::Acquire);
        assert_ne!(state.addr() & QUEUE_LOCKED, 0);
        assert_ne!(state.addr() & SIGNAL_MASK, 0);

        self.unpark_waiters(state)
    }

    #[cold]
    unsafe fn unpark_waiters(&self, state: *mut Waiter) {
        // Get the head waiter node from the queue and wake the entire queue.
        let head = NonNull::new(state.map_addr(|addr| addr & Waiter::MASK));
        let head = head.expect("Condvar waking up waiters with invalid state");

        self.unpark_requeue(head)
    }

    #[cold]
    unsafe fn unpark_requeue(&self, head: NonNull<Waiter>) {
        let mut waiters = Some(head);
        while let Some(waiter) = waiters {
            waiters = waiter.as_ref().next.get();

            let waiting_on = waiter.as_ref().waiting_on.get();
            let waiting_on = waiting_on.expect("Condvar waiter not waiting on anything");

            // Storing the lock the waiter is waiting on inside the waiter
            // allows the Condvar to support waiting on multiples mutexes at once.
            let raw_rwlock = waiting_on.cast::<RawRwLock>();
            let waiter = Pin::new_unchecked(waiter.as_ref());

            // Try to requeue the waiter onto the RwLock (really, Mutex) it was waiting on.
            // Failure to do so means the lock is unlocked and we should unpark directly in
            // hopes that the waiter will immediately acquire it.
            if !raw_rwlock.as_ref().try_requeue(waiter) {
                waiter.parker.unpark();
            }
        }
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

#[cfg(test)]
mod tests {
    use crate::{Condvar, Mutex};
    use std::{
        sync::{mpsc::channel, Arc},
        thread,
        time::{Duration, Instant},
    };

    #[test]
    fn smoke() {
        let c = Condvar::new();
        c.notify_one();
        c.notify_all();
    }

    #[test]
    fn notify_one() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let _t = thread::spawn(move || {
            let _g = m2.lock();
            c2.notify_one();
        });
        c.wait(&mut g);
    }

    #[test]
    fn notify_all() {
        const N: usize = 10;

        let data = Arc::new((Mutex::new(0), Condvar::new()));
        let (tx, rx) = channel();
        for _ in 0..N {
            let data = data.clone();
            let tx = tx.clone();
            thread::spawn(move || {
                let &(ref lock, ref cond) = &*data;
                let mut cnt = lock.lock();
                *cnt += 1;
                if *cnt == N {
                    tx.send(()).unwrap();
                }
                while *cnt != 0 {
                    cond.wait(&mut cnt);
                }
                tx.send(()).unwrap();
            });
        }
        drop(tx);

        let &(ref lock, ref cond) = &*data;
        rx.recv().unwrap();
        let mut cnt = lock.lock();
        *cnt = 0;
        cond.notify_all();
        drop(cnt);

        for _ in 0..N {
            rx.recv().unwrap();
        }
    }

    #[test]
    fn notify_one_return_true() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let _t = thread::spawn(move || {
            let _g = m2.lock();
            assert!(c2.notify_one());
        });
        c.wait(&mut g);
    }

    #[test]
    fn notify_one_return_false() {
        let m = Arc::new(Mutex::new(()));
        let c = Arc::new(Condvar::new());

        let _t = thread::spawn(move || {
            let _g = m.lock();
            assert!(!c.notify_one());
        });
    }

    #[test]
    fn notify_all_return() {
        const N: usize = 10;

        let data = Arc::new((Mutex::new(0), Condvar::new()));
        let (tx, rx) = channel();
        for _ in 0..N {
            let data = data.clone();
            let tx = tx.clone();
            thread::spawn(move || {
                let &(ref lock, ref cond) = &*data;
                let mut cnt = lock.lock();
                *cnt += 1;
                if *cnt == N {
                    tx.send(()).unwrap();
                }
                while *cnt != 0 {
                    cond.wait(&mut cnt);
                }
                tx.send(()).unwrap();
            });
        }
        drop(tx);

        let &(ref lock, ref cond) = &*data;
        rx.recv().unwrap();
        let mut cnt = lock.lock();
        *cnt = 0;
        assert_eq!(cond.notify_all(), true);
        drop(cnt);

        for _ in 0..N {
            rx.recv().unwrap();
        }

        assert_eq!(cond.notify_all(), false);
    }

    #[test]
    fn wait_for() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let no_timeout = c.wait_for(&mut g, Duration::from_millis(1));
        assert!(no_timeout.timed_out());

        let _t = thread::spawn(move || {
            let _g = m2.lock();
            c2.notify_one();
        });
        let timeout_res = c.wait_for(&mut g, Duration::from_secs(u64::max_value()));
        assert!(!timeout_res.timed_out());

        drop(g);
    }

    #[test]
    fn wait_until() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let no_timeout = c.wait_until(&mut g, Instant::now() + Duration::from_millis(1));
        assert!(no_timeout.timed_out());
        let _t = thread::spawn(move || {
            let _g = m2.lock();
            c2.notify_one();
        });
        let timeout_res = c.wait_until(
            &mut g,
            Instant::now() + Duration::from_millis(u32::max_value() as u64),
        );
        assert!(!timeout_res.timed_out());
        drop(g);
    }

    #[test]
    fn two_mutexes() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let m3 = Arc::new(Mutex::new(()));
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        // Make sure we don't leave the child thread dangling
        struct PanicGuard<'a>(&'a Condvar);
        impl<'a> Drop for PanicGuard<'a> {
            fn drop(&mut self) {
                self.0.notify_one();
            }
        }

        let (tx, rx) = channel();
        let g = m.lock();
        let _t = thread::spawn(move || {
            let mut g = m2.lock();
            tx.send(()).unwrap();
            c2.wait(&mut g);
        });
        drop(g);
        rx.recv().unwrap();
        let _g = m.lock();
        let _guard = PanicGuard(&*c);

        let result = c.wait_for(&mut m3.lock(), Duration::from_millis(100));
        assert!(result.timed_out());
    }

    #[test]
    fn two_mutexes_disjoint() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let m3 = Arc::new(Mutex::new(()));
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let _t = thread::spawn(move || {
            let _g = m2.lock();
            c2.notify_one();
        });
        c.wait(&mut g);
        drop(g);

        let _ = c.wait_for(&mut m3.lock(), Duration::from_millis(1));
    }

    #[test]
    fn test_debug_condvar() {
        let c = Condvar::new();
        assert_eq!(format!("{:?}", c), "Condvar { .. }");
    }

    #[test]
    fn test_condvar_requeue() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();
        let t = thread::spawn(move || {
            let mut g = m2.lock();
            c2.wait(&mut g);
        });

        let mut g = m.lock();
        while !c.notify_one() {
            // Wait for the thread to get into wait()

            //MutexGuard::bump(&mut g);
            drop(g);
            thread::yield_now();
            g = m.lock();

            // Yield, so the other thread gets a chance to do something.
            // (At least Miri needs this, because it doesn't preempt threads.)
            thread::yield_now();
        }
        // The thread should have been requeued to the mutex, which we wake up now.
        drop(g);
        t.join().unwrap();
    }

    #[test]
    fn test_parking_lot_issue_129() {
        let locks = Arc::new((Mutex::new(()), Condvar::new()));

        let (tx, rx) = channel();
        for _ in 0..4 {
            let locks = locks.clone();
            let tx = tx.clone();
            thread::spawn(move || {
                let mut guard = locks.0.lock();
                locks.1.wait(&mut guard);
                locks.1.wait_for(&mut guard, Duration::from_millis(1));
                locks.1.notify_one();
                tx.send(()).unwrap();
            });
        }

        thread::sleep(Duration::from_millis(100));
        locks.1.notify_one();

        for _ in 0..4 {
            assert_eq!(rx.recv_timeout(Duration::from_millis(500)), Ok(()));
        }
    }
}

/// This module contains an integration test that is heavily inspired from WebKit's own integration
/// tests for it's own Condvar.
#[cfg(test)]
mod webkit_queue_test {
    use crate::{Condvar, Mutex, MutexGuard};
    use std::{collections::VecDeque, sync::Arc, thread, time::Duration};

    #[derive(Clone, Copy)]
    enum Timeout {
        Bounded(Duration),
        Forever,
    }

    #[derive(Clone, Copy)]
    enum NotifyStyle {
        One,
        All,
    }

    struct Queue {
        items: VecDeque<usize>,
        should_continue: bool,
    }

    impl Queue {
        fn new() -> Self {
            Self {
                items: VecDeque::new(),
                should_continue: true,
            }
        }
    }

    fn wait<T: ?Sized>(
        condition: &Condvar,
        lock: &mut MutexGuard<'_, T>,
        predicate: impl Fn(&mut MutexGuard<'_, T>) -> bool,
        timeout: &Timeout,
    ) {
        while !predicate(lock) {
            match timeout {
                Timeout::Forever => condition.wait(lock),
                Timeout::Bounded(bound) => {
                    condition.wait_for(lock, *bound);
                }
            }
        }
    }

    fn notify(style: NotifyStyle, condition: &Condvar, should_notify: bool) {
        match style {
            NotifyStyle::One => {
                condition.notify_one();
            }
            NotifyStyle::All => {
                if should_notify {
                    condition.notify_all();
                }
            }
        }
    }

    fn run_queue_test(
        num_producers: usize,
        num_consumers: usize,
        max_queue_size: usize,
        messages_per_producer: usize,
        notify_style: NotifyStyle,
        timeout: Timeout,
        delay: Duration,
    ) {
        let input_queue = Arc::new(Mutex::new(Queue::new()));
        let empty_condition = Arc::new(Condvar::new());
        let full_condition = Arc::new(Condvar::new());

        let output_vec = Arc::new(Mutex::new(vec![]));

        let consumers = (0..num_consumers)
            .map(|_| {
                consumer_thread(
                    input_queue.clone(),
                    empty_condition.clone(),
                    full_condition.clone(),
                    timeout,
                    notify_style,
                    output_vec.clone(),
                    max_queue_size,
                )
            })
            .collect::<Vec<_>>();
        let producers = (0..num_producers)
            .map(|_| {
                producer_thread(
                    messages_per_producer,
                    input_queue.clone(),
                    empty_condition.clone(),
                    full_condition.clone(),
                    timeout,
                    notify_style,
                    max_queue_size,
                )
            })
            .collect::<Vec<_>>();

        thread::sleep(delay);

        for producer in producers.into_iter() {
            producer.join().expect("Producer thread panicked");
        }

        {
            let mut input_queue = input_queue.lock();
            input_queue.should_continue = false;
        }
        empty_condition.notify_all();

        for consumer in consumers.into_iter() {
            consumer.join().expect("Consumer thread panicked");
        }

        let mut output_vec = output_vec.lock();
        assert_eq!(output_vec.len(), num_producers * messages_per_producer);
        output_vec.sort();
        for msg_idx in 0..messages_per_producer {
            for producer_idx in 0..num_producers {
                assert_eq!(msg_idx, output_vec[msg_idx * num_producers + producer_idx]);
            }
        }
    }

    fn consumer_thread(
        input_queue: Arc<Mutex<Queue>>,
        empty_condition: Arc<Condvar>,
        full_condition: Arc<Condvar>,
        timeout: Timeout,
        notify_style: NotifyStyle,
        output_queue: Arc<Mutex<Vec<usize>>>,
        max_queue_size: usize,
    ) -> thread::JoinHandle<()> {
        thread::spawn(move || loop {
            let (should_notify, result) = {
                let mut queue = input_queue.lock();
                wait(
                    &*empty_condition,
                    &mut queue,
                    |state| -> bool { !state.items.is_empty() || !state.should_continue },
                    &timeout,
                );
                if queue.items.is_empty() && !queue.should_continue {
                    return;
                }
                let should_notify = queue.items.len() == max_queue_size;
                let result = queue.items.pop_front();
                std::mem::drop(queue);
                (should_notify, result)
            };
            notify(notify_style, &*full_condition, should_notify);

            if let Some(result) = result {
                output_queue.lock().push(result);
            }
        })
    }

    fn producer_thread(
        num_messages: usize,
        queue: Arc<Mutex<Queue>>,
        empty_condition: Arc<Condvar>,
        full_condition: Arc<Condvar>,
        timeout: Timeout,
        notify_style: NotifyStyle,
        max_queue_size: usize,
    ) -> thread::JoinHandle<()> {
        thread::spawn(move || {
            for message in 0..num_messages {
                let should_notify = {
                    let mut queue = queue.lock();
                    wait(
                        &*full_condition,
                        &mut queue,
                        |state| state.items.len() < max_queue_size,
                        &timeout,
                    );
                    let should_notify = queue.items.is_empty();
                    queue.items.push_back(message);
                    std::mem::drop(queue);
                    should_notify
                };
                notify(notify_style, &*empty_condition, should_notify);
            }
        })
    }

    macro_rules! run_queue_tests {
        ( $( $name:ident(
            num_producers: $num_producers:expr,
            num_consumers: $num_consumers:expr,
            max_queue_size: $max_queue_size:expr,
            messages_per_producer: $messages_per_producer:expr,
            notification_style: $notification_style:expr,
            timeout: $timeout:expr,
            delay_seconds: $delay_seconds:expr);
        )* ) => {
            $(#[test]
            fn $name() {
                let delay = Duration::from_secs($delay_seconds);
                run_queue_test(
                    $num_producers,
                    $num_consumers,
                    $max_queue_size,
                    $messages_per_producer,
                    $notification_style,
                    $timeout,
                    delay,
                    );
            })*
        };
    }

    run_queue_tests! {
        sanity_check_queue(
            num_producers: 1,
            num_consumers: 1,
            max_queue_size: 1,
            messages_per_producer: if cfg!(miri) { 100 } else { 100_000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Bounded(Duration::from_secs(1)),
            delay_seconds: 0
        );
        sanity_check_queue_timeout(
            num_producers: 1,
            num_consumers: 1,
            max_queue_size: 1,
            messages_per_producer: if cfg!(miri) { 100 } else { 100_000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        new_test_without_timeout_5(
            num_producers: 1,
            num_consumers: 5,
            max_queue_size: 1,
            messages_per_producer: if cfg!(miri) { 100 } else { 100_000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        one_producer_one_consumer_one_slot(
            num_producers: 1,
            num_consumers: 1,
            max_queue_size: 1,
            messages_per_producer: if cfg!(miri) { 100 } else { 100_000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        one_producer_one_consumer_one_slot_timeout(
            num_producers: 1,
            num_consumers: 1,
            max_queue_size: 1,
            messages_per_producer: if cfg!(miri) { 100 } else { 100_000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 1
        );
        one_producer_one_consumer_hundred_slots(
            num_producers: 1,
            num_consumers: 1,
            max_queue_size: if cfg!(miri) { 10 } else { 100 },
            messages_per_producer: if cfg!(miri) { 100 } else { 1000_000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        ten_producers_one_consumer_one_slot(
            num_producers: 10,
            num_consumers: 1,
            max_queue_size: 1,
            messages_per_producer: if cfg!(miri) { 50 } else { 10000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        ten_producers_one_consumer_hundred_slots_notify_all(
            num_producers: 10,
            num_consumers: 1,
            max_queue_size: 100,
            messages_per_producer: if cfg!(miri) { 50 } else { 10000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        ten_producers_one_consumer_hundred_slots_notify_one(
            num_producers: 10,
            num_consumers: 1,
            max_queue_size: 100,
            messages_per_producer: if cfg!(miri) { 50 } else { 10000 },
            notification_style: NotifyStyle::One,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        one_producer_ten_consumers_one_slot(
            num_producers: 1,
            num_consumers: 10,
            max_queue_size: 1,
            messages_per_producer: if cfg!(miri) { 50 } else { 10000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        one_producer_ten_consumers_hundred_slots_notify_all(
            num_producers: 1,
            num_consumers: 10,
            max_queue_size: 100,
            messages_per_producer: if cfg!(miri) { 100 } else { 100_000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        one_producer_ten_consumers_hundred_slots_notify_one(
            num_producers: 1,
            num_consumers: 10,
            max_queue_size: 100,
            messages_per_producer: if cfg!(miri) { 100 } else { 100_000 },
            notification_style: NotifyStyle::One,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        ten_producers_ten_consumers_one_slot(
            num_producers: 10,
            num_consumers: 10,
            max_queue_size: 1,
            messages_per_producer: if cfg!(miri) { 50 } else { 50000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        ten_producers_ten_consumers_hundred_slots_notify_all(
            num_producers: 10,
            num_consumers: 10,
            max_queue_size: 100,
            messages_per_producer: if cfg!(miri) { 50 } else { 50000 },
            notification_style: NotifyStyle::All,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
        ten_producers_ten_consumers_hundred_slots_notify_one(
            num_producers: 10,
            num_consumers: 10,
            max_queue_size: 100,
            messages_per_producer: if cfg!(miri) { 50 } else { 50000 },
            notification_style: NotifyStyle::One,
            timeout: Timeout::Forever,
            delay_seconds: 0
        );
    }
}
