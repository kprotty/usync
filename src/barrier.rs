use crate::shared::Waiter;
use std::{
    fmt,
    marker::PhantomData,
    ptr::NonNull,
    sync::atomic::{fence, AtomicUsize, Ordering},
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
    state: AtomicUsize,
    _p: PhantomData<*const Waiter>,
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
        Self {
            state: AtomicUsize::new(n << COUNT_SHIFT),
            _p: PhantomData,
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
        let state = self.state.load(Ordering::Acquire);

        if state != COMPLETED {
            is_leader = self.wait_slow(state);
        }

        BarrierWaitResult(is_leader)
    }

    #[cold]
    fn wait_slow(&self, mut state: usize) -> bool {
        Waiter::with(|waiter| {
            waiter.waiting_on.set(None);
            waiter.prev.set(None);

            loop {
                if state == COMPLETED {
                    fence(Ordering::Acquire);
                    return false;
                }

                if state == (1 << COUNT_SHIFT) {
                    match self.state.compare_exchange_weak(
                        state,
                        COMPLETED,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return true,
                        Err(e) => state = e,
                    }
                    continue;
                }

                let waiter_ptr = &*waiter as *const Waiter as usize;
                let mut new_state = (state & !Waiter::MASK) | waiter_ptr | QUEUED;

                if state & QUEUED == 0 {
                    waiter
                        .counter
                        .store(state >> COUNT_SHIFT, Ordering::Relaxed);
                    waiter.next.set(None);
                    waiter.tail.set(Some(NonNull::from(&*waiter)));
                } else {
                    new_state |= QUEUE_LOCKED;
                    waiter
                        .next
                        .set(NonNull::new((state & Waiter::MASK) as *mut Waiter));
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

                if state & (QUEUED | QUEUE_LOCKED) == QUEUED {
                    if unsafe { self.link_queue_or_complete(new_state) } {
                        return true;
                    }
                }

                assert!(waiter.parker.park(None));
                debug_assert_eq!(self.state.load(Ordering::Relaxed), COMPLETED);
                return false;
            }
        })
    }

    #[cold]
    unsafe fn link_queue_or_complete(&self, mut state: usize) -> bool {
        loop {
            assert_ne!(state & QUEUED, 0);
            assert_ne!(state & QUEUE_LOCKED, 0);

            fence(Ordering::Acquire);
            let mut discovered = 0;
            let (_, tail) = Waiter::get_and_link_queue(state, |_| discovered += 1);

            let mut counter = tail.as_ref().counter.load(Ordering::Relaxed);
            counter = counter.saturating_sub(discovered);

            tail.as_ref().counter.store(counter, Ordering::Relaxed);
            if counter == 0 {
                return self.complete();
            }

            match self.state.compare_exchange_weak(
                state,
                state & QUEUE_LOCKED,
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
        let state = self.state.swap(COMPLETED, Ordering::AcqRel);
        assert_ne!(state & QUEUED, 0);
        assert_ne!(state & QUEUE_LOCKED, 0);

        let mut waiters = NonNull::new((state & Waiter::MASK) as *mut Waiter);
        while let Some(waiter) = waiters {
            waiters = waiter.as_ref().next.get();
            waiter.as_ref().parker.unpark();
        }

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
