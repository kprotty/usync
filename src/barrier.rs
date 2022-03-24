use std::fmt;

/// A barrier enables multiple threads to synchronize the beginning
/// of some computation.
///
/// # Examples
///
/// ```
/// use usync::{Arc, Barrier};
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
pub struct Barrier {}

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
    pub const fn new(n: usize) -> Barrier {
        Self {}
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
    /// use usync::{Arc, Barrier};
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
    pub fn wait(&self) -> BarrierWaitResult {
        unimplemented!("TODO")
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
