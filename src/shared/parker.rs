use super::{event::Event, SpinWait};
use std::{
    pin::Pin,
    ptr::{self, NonNull},
    sync::atomic::{AtomicPtr, Ordering},
    time::Duration,
};

#[derive(Default)]
pub(crate) struct Parker {
    event: AtomicPtr<Event>,
}

impl Parker {
    pub(super) const fn new() -> Self {
        Self {
            event: AtomicPtr::new(ptr::null_mut()),
        }
    }

    /// Provides a stub pointer which is used as a sentinel to indicate "unparked"
    fn notified() -> NonNull<Event> {
        NonNull::dangling()
    }

    fn park_complete(&self, event: *mut Event) -> bool {
        assert_eq!(NonNull::new(event), Some(Self::notified()));
        self.event.store(ptr::null_mut(), Ordering::Relaxed);
        true
    }

    pub(crate) fn park(&self, timeout: Option<Duration>) -> bool {
        // Spin a little bit in hopes that another thread wakes us up.
        let mut spin = SpinWait::default();
        loop {
            if !spin.try_yield_now() {
                return self.park_slow(timeout);
            }

            let event = self.event.load(Ordering::Acquire);
            if NonNull::new(event) == Some(Self::notified()) {
                return self.park_complete(event);
            }
        }
    }

    #[cold]
    fn park_slow(&self, timeout: Option<Duration>) -> bool {
        Event::with(|ev| {
            let ev_ptr = NonNull::from(&*ev).as_ptr();
            assert!(!ptr::eq(ev_ptr, Self::notified().as_ptr()));

            // Register our event for waiting, bailing out if we we're notified.
            // AcqRel as Release on success which ensures the ev writes in Event::with() happen before unpark() tries to set() it.
            // Acquire on failure to ensure that the unpark() happens before we return.
            if let Err(event) = self.event.compare_exchange(
                ptr::null_mut(),
                ev_ptr,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                return self.park_complete(event);
            }

            // Do a wait on the event and check if we timed out.
            let timed_out = !ev.wait(timeout);
            if timed_out {
                // On timeout, we must remove our event from self.event
                // before returning to ensure that unpark() doesn't access invalid memory.
                // If we fail to do so, we must wait until unpark() wakes up our event it took.
                // This cancels our timeout and ensures that unpark() will always be accessing valid Event memory.
                // Release barrier on succcess to ensure ev.wait() happens before the timeout.
                match self.event.compare_exchange(
                    ev_ptr,
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

    pub(crate) fn unpark(&self) {
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
                assert_ne!(
                    event,
                    Self::notified(),
                    "multiple threads tried to unpark the same Parker"
                );
                Pin::new_unchecked(event.as_ref()).set();
            }
        }
    }
}
