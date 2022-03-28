use crate::shared::{SpinWait, Waiter};
use std::{
    fmt,
    marker::PhantomData,
    ptr::NonNull,
    sync::atomic::{fence, AtomicUsize, Ordering},
};

const UNINIT: usize = 0;
const CALLING: usize = 1;
const POISONED: usize = 2;
const COMPLETED: usize = 3;

/// A synchronization primitive which can be used to run a one-time
/// initialization. Useful for one-time initialization for globals, FFI or
/// related functionality.
///
/// # Differences from the standard library `Once`
///
/// - Only requires 1 byte of space, instead of 1 word.
/// - Not required to be `'static`.
/// - Relaxed memory barriers in the fast path, which can significantly improve
///   performance on some architectures.
/// - Efficient handling of micro-contention using adaptive spinning.
///
/// # Examples
///
/// ```
/// use usync::Once;
///
/// static START: Once = Once::new();
///
/// START.call_once(|| {
///     // run initialization here
/// });
/// ```
#[derive(Default)]
pub struct Once {
    /// This atomic integer holds the current state of the Barrier instance.
    /// The QUEUED bit switches between counting the barrier value and recording the waiters.
    ///
    /// # State table:
    ///
    /// state 0b11 | Remaining | Description
    ///   UNINIT   |     0     | The once state is fresh and empty.
    /// -----------+-----------+---------------------------------------------------------------------
    ///   CALLING  | ?*Waiter  | There is a thread calling a function on the Once state.
    ///            |           | The Remaining bits point to the head of the waiting-thread queue
    //             |           | if there is any.
    /// -----------+-----------+--------------------------------------------------------------------
    ///  POISONED  |     0     | The once was once calling and the function panicked, poisoning the state.
    /// -----------+-----------+--------------------------------------------------------------------
    ///  COMPLETED |     0     | The once was once calling and the function completed, resolving the state.
    /// -----------+-----------+--------------------------------------------------------------------
    state: AtomicUsize,
    _p: PhantomData<*const Waiter>,
}

unsafe impl Send for Once {}
unsafe impl Sync for Once {}

impl fmt::Debug for Once {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Once")
            .field("state", &self.state())
            .finish()
    }
}

impl Once {
    /// Creates a new `Once` value.
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(UNINIT),
            _p: PhantomData,
        }
    }

    /// Returns the current state of this `Once`.
    pub fn state(&self) -> OnceState {
        let state = self.state.load(Ordering::Relaxed);
        match state & !Waiter::MASK {
            UNINIT => OnceState::New,
            CALLING => OnceState::InProgress,
            POISONED => OnceState::Poisoned,
            COMPLETED => OnceState::Done,
            _ => unreachable!("invalid state"),
        }
    }

    /// Performs an initialization routine once and only once. The given closure
    /// will be executed if this is the first time `call_once` has been called,
    /// and otherwise the routine will *not* be invoked.
    ///
    /// This method will block the calling thread if another initialization
    /// routine is currently running.
    ///
    /// When this function returns, it is guaranteed that some initialization
    /// has run and completed (it may not be the closure specified). It is also
    /// guaranteed that any memory writes performed by the executed closure can
    /// be reliably observed by other threads at this point (there is a
    /// happens-before relation between the closure and code executing after the
    /// return).
    ///
    /// # Examples
    ///
    /// ```
    /// use usync::Once;
    ///
    /// static mut VAL: usize = 0;
    /// static INIT: Once = Once::new();
    ///
    /// // Accessing a `static mut` is unsafe much of the time, but if we do so
    /// // in a synchronized fashion (e.g. write once or read all) then we're
    /// // good to go!
    /// //
    /// // This function will only call `expensive_computation` once, and will
    /// // otherwise always return the value returned from the first invocation.
    /// fn get_cached_val() -> usize {
    ///     unsafe {
    ///         INIT.call_once(|| {
    ///             VAL = expensive_computation();
    ///         });
    ///         VAL
    ///     }
    /// }
    ///
    /// fn expensive_computation() -> usize {
    ///     // ...
    /// # 2
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// The closure `f` will only be executed once if this is called
    /// concurrently amongst many threads. If that closure panics, however, then
    /// it will *poison* this `Once` instance, causing all future invocations of
    /// `call_once` to also panic.
    #[inline]
    pub fn call_once<F>(&self, f: F)
    where
        F: FnOnce(),
    {
        // Fast path to check if the state was completed.
        // Acquire barrier to ensure that Once function call and completion happens before we return.
        let state = self.state.load(Ordering::Acquire);
        if state == COMPLETED {
            return;
        }

        self.call_once_slow(false, |_: OnceState| f());
    }

    /// Performs the same function as `call_once` except ignores poisoning.
    ///
    /// If this `Once` has been poisoned (some initialization panicked) then
    /// this function will continue to attempt to call initialization functions
    /// until one of them doesn't panic.
    ///
    /// The closure `f` is yielded a structure which can be used to query the
    /// state of this `Once` (whether initialization has previously panicked or
    /// not).
    #[inline]
    pub fn call_once_force<F>(&self, f: F)
    where
        F: FnOnce(OnceState),
    {
        // Fast path to check if the state was completed.
        // Acquire barrier to ensure that Once function call and completion happens before we return.
        let state = self.state.load(Ordering::Acquire);
        if state == COMPLETED {
            return;
        }

        self.call_once_slow(true, f);
    }

    #[cold]
    fn call_once_slow<F>(&self, ignore_poison: bool, f: F)
    where
        F: FnOnce(OnceState),
    {
        Waiter::with(|waiter| {
            let mut spin = SpinWait::default();
            let mut state = self.state.load(Ordering::Relaxed);

            loop {
                // Once the state is completed, we can return.
                // Acquire barrier to ensure the Once function call and completion happen before we return.
                if state == COMPLETED {
                    fence(Ordering::Acquire);
                    return;
                }
                
                // Check for poision and panic if the caller can't ignore it.
                // Acquire barrier to ensure the Once function call panic happened before we return. 
                if state == POISONED && !ignore_poison {
                    fence(Ordering::Acquire);
                    panic!("Once instance was previously poisoned");
                }

                // There is a thread in the middle of calling their function on the Once.
                // Queue our waiter in order to wait for them to finish calling.
                if state & 0b11 == CALLING {
                    // Try to spin a little bit in hopes that they finish the function call soon.
                    // Don't spin if there's already threads waiting as we should start waiting too. 
                    let head = NonNull::new((state & Waiter::MASK) as *mut Waiter);
                    if head.is_none() && spin.try_yield_now() {
                        state = self.state.load(Ordering::Relaxed);
                        continue;
                    }

                    // Push our waiter to the queue in a stack-like manner.
                    waiter.next.set(head);
                    let waiter_ptr = &*waiter as *const Waiter as usize;
                    let new_state = waiter_ptr | CALLING;

                    // Release barrier to ensure our waiter's writes happen before the calling thread
                    // iterates the queue in order to wake us up.
                    if let Err(e) = self.state.compare_exchange_weak(
                        state,
                        new_state,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ) {
                        state = e;
                        continue;
                    }
                    
                    // Sleep and check the Once state again.
                    assert!(waiter.parker.park(None));
                    state = self.state.load(Ordering::Relaxed);
                    continue;
                }

                match self.state.compare_exchange_weak(
                    state,
                    CALLING,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return self.do_call(state, f),
                    Err(e) => state = e,
                }
            }
        })
    }

    #[cold]
    fn do_call<F>(&self, old_state: usize, f: F)
    where
        F: FnOnce(OnceState),
    {
        /// The state guard is used to ensure that waiting threads are woken up
        /// regardless of it a panic occurs when calling f() or not.
        struct StateGuard<'a> {
            once: &'a Once,
            reset_to: usize,
        }

        impl<'a> Drop for StateGuard<'a> {
            fn drop(&mut self) {
                // Complete the once state using the reset_to.
                // AcqRel as Acquire to ensure writes to pushed waiters happen before we iterate and wake them below.
                // AcqRel as Release to ensure our function call happens before the waiters return from call_once_*. 
                let state = self.once.state.swap(self.reset_to, Ordering::AcqRel);
                assert_eq!(state & 0b11, CALLING);

                let mut waiters = NonNull::new((state & Waiter::MASK) as *mut Waiter);
                while let Some(waiter) = waiters {
                    unsafe {
                        waiters = waiter.as_ref().next.get();
                        waiter.as_ref().parker.unpark();
                    }
                }
            }
        }

        // Initialize the StateGuard to complete with POISONED state.
        // If the function call below panics, it will poison the Once.
        let mut state_guard = StateGuard {
            once: self,
            reset_to: POISONED,
        };

        f(match old_state {
            UNINIT => OnceState::New,
            POISONED => OnceState::Poisoned,
            _ => unreachable!("invalid once state on invokation"),
        });

        // The function call completed safely, 
        // so resolve the Once with COMPLETED instead of POISONED.
        state_guard.reset_to = COMPLETED;
        std::mem::drop(state_guard);
    }
}

/// Current state of a `Once`.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum OnceState {
    /// A closure has not been executed yet
    New,

    /// A closure was executed but panicked.
    Poisoned,

    /// A thread is currently executing a closure.
    InProgress,

    /// A closure has completed successfully.
    Done,
}

impl OnceState {
    /// Returns whether the associated `Once` has been poisoned.
    ///
    /// Once an initialization routine for a `Once` has panicked it will forever
    /// indicate to future forced initialization routines that it is poisoned.
    #[inline]
    pub fn poisoned(self) -> bool {
        self == Self::Poisoned
    }

    /// Returns whether the associated `Once` has successfully executed a
    /// closure.
    #[inline]
    pub fn done(self) -> bool {
        self == Self::Done
    }
}

#[cfg(test)]
mod tests {
    use crate::Once;
    use std::{panic, sync::mpsc::channel, thread};

    #[test]
    fn smoke_once() {
        static O: Once = Once::new();
        let mut a = 0;
        O.call_once(|| a += 1);
        assert_eq!(a, 1);
        O.call_once(|| a += 1);
        assert_eq!(a, 1);
    }

    #[test]
    fn stampede_once() {
        static O: Once = Once::new();
        static mut RUN: bool = false;

        let (tx, rx) = channel();
        for _ in 0..10 {
            let tx = tx.clone();
            thread::spawn(move || {
                for _ in 0..4 {
                    thread::yield_now()
                }
                unsafe {
                    O.call_once(|| {
                        assert!(!RUN);
                        RUN = true;
                    });
                    assert!(RUN);
                }
                tx.send(()).unwrap();
            });
        }

        unsafe {
            O.call_once(|| {
                assert!(!RUN);
                RUN = true;
            });
            assert!(RUN);
        }

        for _ in 0..10 {
            rx.recv().unwrap();
        }
    }

    #[test]
    fn poison_bad() {
        static O: Once = Once::new();

        // poison the once
        let t = panic::catch_unwind(|| {
            O.call_once(|| panic!());
        });
        assert!(t.is_err());

        // poisoning propagates
        let t = panic::catch_unwind(|| {
            O.call_once(|| {});
        });
        assert!(t.is_err());

        // we can subvert poisoning, however
        let mut called = false;
        O.call_once_force(|p| {
            called = true;
            assert!(p.poisoned())
        });
        assert!(called);

        // once any success happens, we stop propagating the poison
        O.call_once(|| {});
    }

    #[test]
    fn wait_for_force_to_finish() {
        static O: Once = Once::new();

        // poison the once
        let t = panic::catch_unwind(|| {
            O.call_once(|| panic!());
        });
        assert!(t.is_err());

        // make sure someone's waiting inside the once via a force
        let (tx1, rx1) = channel();
        let (tx2, rx2) = channel();
        let t1 = thread::spawn(move || {
            O.call_once_force(|p| {
                assert!(p.poisoned());
                tx1.send(()).unwrap();
                rx2.recv().unwrap();
            });
        });

        rx1.recv().unwrap();

        // put another waiter on the once
        let t2 = thread::spawn(|| {
            let mut called = false;
            O.call_once(|| {
                called = true;
            });
            assert!(!called);
        });

        tx2.send(()).unwrap();

        assert!(t1.join().is_ok());
        assert!(t2.join().is_ok());
    }

    #[test]
    fn test_once_debug() {
        static O: Once = Once::new();

        assert_eq!(format!("{:?}", O), "Once { state: New }");
    }
}
