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
    pub(crate) const fn new() -> Self {
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
            let event_ptr = NonNull::from(&self.event).as_ptr();
            drop(self);

            // FIXME (maybe): This is a case of https://github.com/rust-lang/rust/issues/55005.
            // A successful `fetch_update()` or other event_ptr usages could have a potentially
            // dangling ref to `event_ptr` once the park() thread sees `notified` and returns.
            //
            // This uses fetch_update() which uses compare_exchange_weak() internally.
            // Reason for not using swap() is to avoid unnecessary stores when unpark() is called frequently by multiple threads.
            // Stores are more expensive over loads as invalid the cache line and force other threads
            // (even unpark threads, not just the park thread) to refetch/resynchronize this cache-lines memory.
            //
            // AcqRel as Acquire barrier to ensure Event::with() writes in park() happen before we Event::set() it below.
            // AcqRel as Release barrier to ensure that unpark() itself happens before park() returns for caller's reasons.
            (*event_ptr)
                .fetch_update(Ordering::AcqRel, Ordering::Relaxed, |event| {
                    let notified = Self::notified().as_ptr();
                    if ptr::eq(event, notified) {
                        return None;
                    }

                    Some(notified)
                })
                .map(|event| {
                    if let Some(event) = NonNull::new(event) {
                        Pin::new_unchecked(event.as_ref()).set();
                    }
                })
                .unwrap_or(())
        }
    }
}
