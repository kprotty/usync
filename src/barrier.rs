#![allow(unstable_name_collisions)]
use crate::shared::{fence_acquire, invalid_mut, StrictProvenance, Waiter};
use std::{
    fmt,
    ptr::{self, NonNull},
    sync::atomic::{AtomicPtr, Ordering},
};

const QUEUED: usize = 1;
const QUEUE_LOCKED: usize = 2;
const COMPLETED: usize = 0;
const COUNT_SHIFT: u32 = QUEUED.trailing_zeros();

/// A barrier enables multiple threads to synchronize the beginning
/// of some computation.
///
/// # Examples
///
/// ```
/// use usync::Barrier;
/// use std::sync::Arc;
/// use std::thread;
///
/// let mut handles = Vec::with_capacity(10);
/// let barrier = Arc::new(Barrier::new(10));
/// for _ in 0..10 {
///     let c = Arc::clone(&barrier);
///     // The same messages will be printed together.
///     // You will NOT see any interleaving.
///     handles.push(thread::spawn(move|| {
///         println!("before wait");
///         c.wait();
///         println!("after wait");
///     }));
/// }
/// // Wait for other threads to finish.
/// for handle in handles {
///     handle.join().unwrap();
/// }
/// ```
#[derive(Default)]
pub struct Barrier {
    /// This atomic integer holds the current state of the Barrier instance.
    /// The QUEUED bit switches between counting the barrier value and recording the waiters.
    ///
    /// # State table:
    ///
    /// QUEUED | QUEUE_LOCKED | Remaining | Description
    ///    0   |      0       |     0     | The barrier was completed and wait()s will return without blocking.
    /// -------+--------------+-----------+----------------------------------------------------------------------
    ///    0   |      barrier count       | The barrier was initialized with a barrier count and has no waiting threads.
    /// -------+--------------+-----------+----------------------------------------------------------------------
    ///    1   |      0       |  *Waiter  | The barrier has waiting threads where the head of the queue is in Remaining bits.
    ///        |              |           | The barrier count was moved to the tail of the waiting-threads queue.
    /// -------+--------------+-----------+----------------------------------------------------------------------
    ///    1   |      1       |  *Waiter  | The barrier has waiting threads where the head of the queue is in Remaining bits.
    ///        |              |           | There is also a thread updating the waiting-threads queue.
    ///        |              |           | Said thread is counting how many threads are queued and may possibly
    ///        |              |           | complete the barrier if the amount waiting matches or goes above the barrier count.
    /// -------+--------------+-----------+----------------------------------------------------------------------
    state: AtomicPtr<Waiter>,
}

unsafe impl Send for Barrier {}
unsafe impl Sync for Barrier {}

impl fmt::Debug for Barrier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Barrier").finish_non_exhaustive()
    }
}

impl Barrier {
    /// Creates a new barrier that can block a given number of threads.
    ///
    /// A barrier will block `n`-1 threads which call [`wait()`] and then wake
    /// up all threads at once when the `n`th thread calls [`wait()`].
    ///
    /// [`wait()`]: Barrier::wait
    ///
    /// # Examples
    ///
    /// ```
    /// use usync::Barrier;
    ///
    /// let barrier = Barrier::new(10);
    /// ```
    #[must_use]
    pub const fn new(n: usize) -> Self {
        let state = invalid_mut(n << COUNT_SHIFT);
        Self {
            state: AtomicPtr::new(state),
        }
    }

    /// Blocks the current thread until all threads have rendezvoused here.
    ///
    /// Barriers are re-usable after all threads have rendezvoused once, and can
    /// be used continuously.
    ///
    /// A single (arbitrary) thread will receive a [`BarrierWaitResult`] that
    /// returns `true` from [`BarrierWaitResult::is_leader()`] when returning
    /// from this function, and all other threads will receive a result that
    /// will return `false` from [`BarrierWaitResult::is_leader()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use usync::Barrier;
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// let mut handles = Vec::with_capacity(10);
    /// let barrier = Arc::new(Barrier::new(10));
    /// for _ in 0..10 {
    ///     let c = Arc::clone(&barrier);
    ///     // The same messages will be printed together.
    ///     // You will NOT see any interleaving.
    ///     handles.push(thread::spawn(move|| {
    ///         println!("before wait");
    ///         c.wait();
    ///         println!("after wait");
    ///     }));
    /// }
    /// // Wait for other threads to finish.
    /// for handle in handles {
    ///     handle.join().unwrap();
    /// }
    /// ```
    #[inline]
    pub fn wait(&self) -> BarrierWaitResult {
        let mut is_leader = false;

        // Quick check if the Barrier was already completed.
        // Acquire barrier to ensure Barrier completions happens before we return.
        let state = self.state.load(Ordering::Acquire);
        if state.addr() != COMPLETED {
            is_leader = self.wait_slow(state);
        }

        BarrierWaitResult(is_leader)
    }

    #[cold]
    fn wait_slow(&self, mut state: *mut Waiter) -> bool {
        Waiter::with(|waiter| {
            waiter.waiting_on.set(None);
            waiter.prev.set(None);

            loop {
                // If the queue became completed, return that we are not the leader.
                // Acqire barrier to ensure the queue completion happens before we return.
                if state.addr() == COMPLETED {
                    fence_acquire(&self.state);
                    return false;
                }

                // Special case to complete the queue if there's only an n=1.
                // This avoids going throught the queue + QUEUE_LOCKED case below.
                // On success, returns true for being the leader as we completed the Barrier.
                // Release barrier ensures the Barrier completions happens before waiting threads return.
                if state.addr() == (1 << COUNT_SHIFT) {
                    match self.state.compare_exchange_weak(
                        state,
                        state.with_addr(COMPLETED),
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return true,
                        Err(e) => state = e,
                    }
                    continue;
                }

                // Prepare the waiter to be queued onto the state.
                // NOTE: Don't keep the non Waiter::MASK bits!
                //       The first queued waiter will have the counter in those bits.
                let waiter_ptr = NonNull::from(&*waiter).as_ptr();
                let mut new_state = waiter_ptr.map_addr(|addr| addr | QUEUED);

                if state.addr() & QUEUED == 0 {
                    // If we're the first waiter, we move the counter to our node.
                    // We also subtract one from the counter to *account* (pun) for our waiting thread.
                    let counter = (state.addr() >> COUNT_SHIFT)
                        .checked_sub(1)
                        .expect("Barrier counter with zero value when waiting");

                    // The first waiter also sets the tail to itself
                    // so that Waiter::get_and_link_queue() can find the queue tail.
                    waiter.counter.store(counter, Ordering::Relaxed);
                    waiter.next.set(None);
                    waiter.tail.set(Some(NonNull::from(&*waiter)));
                } else {
                    // Other waiters push to the queue in a stack-like manner.
                    // They also try to grab the QUEUE_LOCKED bit in order to fix/link the queue
                    // and possibly complete the Barrier in the process (depending on how many waiters there are).
                    let head = NonNull::new(state.map_addr(|addr| addr & Waiter::MASK));
                    new_state = new_state.map_addr(|addr| addr | QUEUE_LOCKED);
                    waiter.next.set(head);
                    waiter.tail.set(None);
                }

                // Release barrier synchronizes with Acquire barrier by the QUEUE_LOCKED bit holder
                // doing Waiter::get_and_link_queue() to ensure that it sees the waiter writes we did
                // above when observing the state.
                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                // If we acquired the QUEUE_LOCKED bit, try to link the queue or complete the Barrier.
                // NOTE: The bits must be checked separately!
                //       When the counter is still there, it could pose as a QUEUE_LOCKED bit.
                if (state.addr() & QUEUED != 0) && (state.addr() & QUEUE_LOCKED == 0) {
                    // If we manage to complete the Barrier, return is_leader=true here.
                    // SAFETY: we hold the QUEUE_LOCKED bit now.
                    if unsafe { self.link_queue_or_complete(new_state) } {
                        return true;
                    }
                }

                // Wait until we're woken up with the barrier completed.
                assert!(waiter.parker.park(None));

                // Ensure that once we're woken up, the barrier was completed.
                // Acqire barrier to ensure the queue completion happens before we return.
                state = self.state.load(Ordering::Acquire);
                assert_eq!(state.addr(), COMPLETED);
                return false;
            }
        })
    }

    #[cold]
    unsafe fn link_queue_or_complete(&self, mut state: *mut Waiter) -> bool {
        loop {
            assert_ne!(state.addr() & QUEUED, 0);
            assert_ne!(state.addr() & QUEUE_LOCKED, 0);

            // Fix the prev links in the waiter queue now that we hold the QUEUE_LOCKED bit.
            // Also track how many waiters we discovered while trying to fix the waiter links.
            // Acquire barrier to ensure writes to waiters pushed to the queue happen before we start fixing it.
            fence_acquire(&self.state);
            let mut discovered = 0;
            let (_, tail) = Waiter::get_and_link_queue(state, |_| discovered += 1);

            // The barrier count is stored at the tail.
            // Subtract the amount of newly discovered nodes from the count.
            // Use saturating_sub() as technically more threads than the count could try to wait().
            let mut counter = tail.as_ref().counter.load(Ordering::Relaxed);
            counter = counter.saturating_sub(discovered);

            // When the count hits zero, complete the barrier.
            tail.as_ref().counter.store(counter, Ordering::Relaxed);
            if counter == 0 {
                return self.complete();
            }

            // The barrier count isnt zero yet.
            // Unset the QUEUE_LOCKED bit since we've updated the queue links for the next wait()'er to grab it.
            // Release barrier ensures the waiter writes to head/tail we did above happen before the next QUEUE_LOCKED bit holder.
            match self.state.compare_exchange_weak(
                state,
                state.map_addr(|addr| addr & !QUEUE_LOCKED),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return false,
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn complete(&self) -> bool {
        // Complete the barrier while also dequeueing all the waiters.
        // AcqRel as Acquire barrier to ensure the writes to the pushed waiters happens before we iterate & wake them below.
        // AcqRel as Release barrier to ensure that the barrier completion happens before the wait() calls return.
        let completed = ptr::null_mut::<Waiter>().with_addr(COMPLETED);
        let state = self.state.swap(completed, Ordering::AcqRel);

        assert_ne!(state.addr() & QUEUED, 0);
        assert_ne!(state.addr() & QUEUE_LOCKED, 0);

        let mut waiters = NonNull::new(state.map_addr(|addr| addr & Waiter::MASK));
        while let Some(waiter) = waiters {
            waiters = waiter.as_ref().next.get();
            waiter.as_ref().parker.unpark();
        }

        // Since we completed the barrier, we are the leader.
        true
    }
}

/// A `BarrierWaitResult` is returned by [`Barrier::wait()`] when all threads
/// in the [`Barrier`] have rendezvoused.
///
/// # Examples
///
/// ```
/// use usync::Barrier;
///
/// let barrier = Barrier::new(1);
/// let barrier_wait_result = barrier.wait();
/// ```
pub struct BarrierWaitResult(bool);

impl fmt::Debug for BarrierWaitResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BarrierWaitResult")
            .field("is_leader", &self.is_leader())
            .finish()
    }
}

impl BarrierWaitResult {
    /// Returns `true` if this thread is the "leader thread" for the call to
    /// [`Barrier::wait()`].
    ///
    /// Only one thread will have `true` returned from their result, all other
    /// threads will have `false` returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use usync::Barrier;
    ///
    /// let barrier = Barrier::new(1);
    /// let barrier_wait_result = barrier.wait();
    /// println!("{:?}", barrier_wait_result.is_leader());
    /// ```
    #[must_use]
    pub fn is_leader(&self) -> bool {
        self.0
    }
}
