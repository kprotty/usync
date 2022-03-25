use std::{
    cell::Cell,
    marker::PhantomPinned,
    pin::Pin,
    sync::atomic::{AtomicBool, Ordering},
    thread,
    time::{Duration, Instant},
};

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
        let event = Self::new();
        event.thread.set(Some(thread::current()));
        f(unsafe { Pin::new_unchecked(&event) })
    }

    #[cold]
    pub(super) fn wait(self: Pin<&Self>, timeout: Option<Duration>) -> bool {
        let mut started = None;
        loop {
            if self.is_set.load(Ordering::Acquire) {
                return true;
            }

            match timeout {
                None => thread::park(),
                Some(timeout) => {
                    let now = Instant::now();
                    let start = started.unwrap_or_else(|| Instant::now());
                    started = Some(start);

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
