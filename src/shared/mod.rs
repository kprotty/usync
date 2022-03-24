use crate::atomic::{AtomicBool, AtomicPtr, AtomicUsize, Ordering};
use std::{
    cell::Cell,
    hint::spin_loop,
    marker::PhantomPinned,
    pin::Pin,
    ptr::{self, NonNull},
    thread,
    time::Instant,
};

#[derive(Default)]
#[repr(align(16))]
pub(super) struct Waiter {
    pub(super) next: Cell<Option<NonNull<Self>>>,
    pub(super) prev: AtomicWaiterCell,
    pub(super) tail: AtomicWaiterCell,
    pub(super) waiting_on: Cell<Option<NonNull<AtomicUsize>>>,
    pub(super) counter: AtomicUsize,
    pub(super) flags: Cell<usize>,
    parker: Parker,
    _pinned: PhantomPinned,
}

impl Waiter {
    pub const MASK: usize = !0b1111usize;

    pub(super) fn with<F>(f: impl FnOnce(Pin<&Self>) -> F) -> F {
        let waiter = Self::default();
        f(unsafe { Pin::new_unchecked(&waiter) })
    }

    pub(super) fn try_yield_now(attempt: &mut usize) -> bool {
        if *attempt >= 10 {
            return false;
        }

        *attempt += 1;
        spin_loop();
        true
    }

    pub(super) fn force_yield_now(attempt: &mut usize) {
        *attempt += 1;

        for _ in 0..(1 << attempt.min(3)) {
            spin_loop();
        }
    }
}

#[derive(Default)]
struct Parker {
    event: AtomicPtr<Event>,
}

impl Parker {
    /// Provides a stub pointer which is used as a sentinel to indicate "unparked"
    fn notified() -> NonNull<Event> {
        struct SyncEvent(Event);
        unsafe impl Send for SyncEvent {}
        unsafe impl Sync for SyncEvent {}

        static NOTIFIED: SyncEvent = SyncEvent(Event {
            thread: Cell::new(None),
            is_set: AtomicBool::new(false),
            _pinned: PhantomPinned,
        });

        NonNull::from(&NOTIFIED.0)
    }

    fn park_complete(&self, event: *mut Event) -> bool {
        assert_eq!(NonNull::new(event), Some(Self::notified()));
        self.event.set(ptr::null_mut(), Ordering::Relaxed);
        true
    }

    fn park(&self, deadline: Option<Instant>) -> bool {
        // Spin a little bit in hopes that another thread wakes us up.
        let mut spin = SpinWait::default();
        loop {
            if !spin.try_yield_now() {
                return self.park_slow(deadline);
            }

            let event = self.event.load(Ordering::Acquire);
            if NonNull::new(event) == Some(Self::notified()) {
                return self.park_complete(event);
            }
        }
    }

    #[cold]
    fn park_slow(&self, deadline: Option<Instant>) -> bool {
        Event::with(|ev| {
            // Register our event for waiting, bailing out if we we're notified.
            // AcqRel as Release on success which ensures the ev writes in Event::with() happen before unpark() tries to set() it.
            // Acquire on failure to ensure that the unpark() happens before we return.
            if let Err(event) = self.event.compare_exchange(
                ptr::null_mut(),
                NonNull::from(&*ev).as_ptr(),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                return self.park_complete(event);
            }
            
            // Do a wait on the event and check if we timed out.
            let timed_out = !ev.wait(deadline);
            if timed_out {
                // On timeout, we must remove our event from self.event
                // before returning to ensure that unpark() doesn't access invalid memory.
                // If we fail to do so, we must wait until unpark() wakes up our event it took.
                // This cancels our timeout and ensures that unpark() will always be accessing valid Event memory.
                // Release barrier on succcess to ensure ev.wait() happens before the timeout.
                match self.event.compare_exchange(
                    NonNull::from(&*ev).as_ptr(),
                    ptr::null_mut(),
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return false,
                    Err(_) => assert!(ev.wait(None)),
                }
            }
            
            // Check that the state was notified and reset it for the next park().
            // Acquire barrier ensures unpark() happens before we reset and return.
            let event = self.event.load(Ordering::Acquire);
            self.park_complete(event)
        })
    }

    pub(super) fn unpark(&self) {
        unsafe {
            // Try not to leave a dangling ref to the parker (see below).
            let event_ptr = &self.event as *const AtomicPtr<Event>;
            drop(self);
            
            // FIXME (maybe): This is a case of https://github.com/rust-lang/rust/issues/55005.
            // `swap()` has a potentially dangling ref to `event_ptr` once park() thread sees notified and returns.
            // AcqRel as Acquire barrier to ensure Event::with() writes in park() happen before we Event::set() it below.
            // AcqRel as Release barrier to ensure that unpark() itself happens before park() returns for caller reasons.
            let notified_ptr = Self::notified().as_ptr();
            let event = (*event_ptr).swap(notified_ptr, Ordering::AcqRel);

            if let Some(event) = NonNull::new(event) {
                assert_ne!(event, Self::notified(), "multiple threads unparked same Parker");
                event.as_ref().set();
            }
        }
    }
}

struct Event {
    thread: Cell<Option<thread::Thread>>,
    is_set: AtomicBool,
    _pinned: PhantomPinned,
}

impl Event {
    fn with<F>(f: impl FnOnce(Pin<&Self>) -> F) -> F {
        let event = Event {
            thread: Cell::new(Some(thread::current())),
            is_set: AtomicBool::new(false),
            _pinned: PhantomPinned,
        };

        f(unsafe { Pin::new_unchecked(&event) })
    }

    #[cold]
    fn wait(self: Pin<&Self>, deadline: Option<Instant>) -> bool {
        loop {
            if self.is_set.load(Ordering::Acquire) {
                return true;
            }

            match deadline {
                None => thread::park(),
                Some(deadline) => {
                    match deadline.checked_duration_since(Instant::now()) {
                        Some(until_deadline) => thread::park_timeout(until_deadline),
                        None => return false,
                    }
                }
            }
        }
    }

    #[cold]
    unsafe fn set(self: Pin<&Self>) {
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