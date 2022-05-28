use std::{
    cell::Cell,
    marker::PhantomPinned,
    pin::Pin,
    sync::atomic::{AtomicBool, Ordering},
    thread,
    time::{Duration, Instant},
};

/// The primary blocking primitive used by all the synchronization data structures.
pub(super) struct Event {
    thread: Cell<Option<thread::Thread>>,
    is_set: AtomicBool,
    _pinned: PhantomPinned,
}

impl Event {
    pub(super) const fn new() -> Self {
        Self {
            thread: Cell::new(None),
            is_set: AtomicBool::new(false),
            _pinned: PhantomPinned,
        }
    }

    pub(super) fn with<F>(f: impl FnOnce(Pin<&Self>) -> F) -> F {
        // SAFETY: The event lives on the thread's stack.
        let event = Self::new();
        event.thread.set(Some(thread::current()));
        f(unsafe { Pin::new_unchecked(&event) })
    }

    #[cold]
    pub(super) fn wait(self: Pin<&Self>, timeout: Option<Duration>) -> bool {
        let mut started = None;
        loop {
            // Returns true when the event is set.
            // Acquire barrier ensures that the set() happens before we return.
            if self.is_set.load(Ordering::Acquire) {
                return true;
            }

            match timeout {
                None => thread::park(),
                Some(timeout) => {
                    // Get the current time and lazily compute when we started waiting.
                    let now = Instant::now();
                    let start = started.unwrap_or_else(|| now);
                    started = Some(start);

                    // Check if we've been waiting for longer than the timeout
                    let elapsed = now - start;
                    match timeout.checked_sub(elapsed) {
                        Some(until_timeout) => thread::park_timeout(until_timeout),
                        None => return false,
                    }
                }
            }
        }
    }

    #[cold]
    pub(super) unsafe fn set(self: Pin<&Self>) {
        let thread = self.thread.take();
        let thread = thread.expect("Event waiting without a thread");

        // Try to not leave dangling references when returning (see below)
        let is_set_ptr = &self.is_set as *const AtomicBool;
        drop(self);

        // FIXME (maybe): This is a case of https://github.com/rust-lang/rust/issues/55005.
        // `store()` has a potentially dangling ref to `is_set` once wait() thread sees true and returns.
        // Release barrier ensures `thread.take()` happens before is_set is true and wait() thread returns.
        (*is_set_ptr).store(true, Ordering::Release);
        thread.unpark();
    }
}
