use core::{
    cell::Cell,
    pin::Pin,
    marker::PhantomPinned,
    ptr::{self, NonNull},
    sync::atomic::{AtomicUsize, AtomicPtr, Ordering},
};

pub(super) type WaiterCell = Cell<Option<NonNull<Waiter>>>;

#[derive(Default)]
pub(super) struct AtomicWaiterCell {
    ptr: AtomicPtr<Waiter>,
}

impl AtomicWaiterCell {
    pub(super) fn set(&self, waiter: Option<NonNull<Waiter>>) {
        let waiter_ptr = waiter.map(|w| w.as_ptr()).unwrap_or(ptr::null_mut());
        self.ptr.store(waiter_ptr, Ordering::Relaxed);
    }

    pub(super) fn get(&self) -> Option<NonNull<Waiter>> {
        let waiter_ptr = self.ptr.load(Ordering::Relaxed);
        NonNull::new(waiter_ptr)
    }
}

#[repr(align(16))]
#[derive(Default)]
pub(super) struct Waiter {
    pub(super) prev: WaiterCell,
    pub(super) next: WaiterCell,
    pub(super) tail: AtomicWaiterCell,
    pub(super) resource: Cell<Option<NonNull<()>>>,
    pub(super) counter: AtomicUsize,
    pub(super) flags: Cell<usize>,
    event_ref: AtomicPtr<EventRef>,
    _pinned: PhantomPinned,
}

impl Waiter {
    pub(super) const MASK: usize = !0b1111usize;

    pub(super) fn with<F>(&self, f: impl FnOnce(Pin<&Self>) -> F) -> F {
        let waiter = Self::default();
        f(unsafe { Pin::new_unchecked(&waiter) })
    }

    pub(super) unsafe fn get_and_link_queue(
        value: usize,
        mut on_discover: impl FnMut(NonNull<Self>),
    ) -> (NonNull<Self>, NonNull<Self>) {
        let head = NonNull::new((value & Self::MASK) as *mut Self);
        let head = head.expect("looking for wait queue on invalid value");

        let tail = head.as_ref().tail.get().unwrap_or_else(|| {
            let mut current = head;
            loop {
                let next = current.as_ref().next.get();
                let next = next.expect("waiter in queue with invalid link");
                
                assert_eq!(next.as_ref().prev.get(), None);
                next.as_ref().prev.set(Some(current));

                current = next;
                on_discover(current);

                if let Some(tail) = current.as_ref().tail.get() {
                    head.as_ref().tail.set(Some(tail));
                    return tail;
                }
            }
        });

        (head, tail)
    }
}

struct EventRef {
    ptr: NonNull<()>,
    unpark_fn: unsafe fn(NonNull<()>),
}

impl Waiter {
    #[inline(always)]
    fn notified() -> Option<NonNull<EventRef>> {
        static NOTIFIED: EventRef = EventRef {
            ptr: NonNull::dangling(),
            unpark_fn: |_: NonNull<()>| unreachable!("invalid EventRef unpark"),
        };
        Some(NonNull::from(&NOTIFIED))
    }

    #[inline]
    pub(super) fn park<E: Event>(self: Pin<&Self>, timeout: Option<Duration>) -> bool {
        let event_ref = self.event_ref.load(Ordering::Acquire);
        
        if NonNull::new(event_ref) == Self::notified() {
            self.park_reset(event_ref)
        } else {
            self.park_slow::<E>(timeout)
        }
    }

    #[cold]
    fn park_slow<E: Event>(&self, timeout: Option<Duration>) -> bool {
        E::with(|event| {
            struct EventUnpark<E>(E);
            impl<E: Event> EventUnpark<E> {
                unsafe fn on_unpark(ptr: NonNull<()>) {
                    let event = ptr.cast::<E>().as_ref();
                    let event = Pin::new_unchecked(event);
                    event.set();
                }
            }

            let this_event_ref = EventRef {
                ptr: NonNull::from(&*event).cast::<()>(),
                unpark_fn: EventUnpark::<E>::on_unpark,
            };

            if let Err(event_ref) = self.event_ref.compare_exchange(
                ptr::null_mut(),
                NonNull::from(&this_event_ref).as_ptr(),
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                return self.park_reset(event_ref);
            }

            let timed_out = !event.wait(timeout);
            if timed_out {
                match self.event_ref.compare_exchange(
                    NonNull::from(&this_event_ref).as_ptr(),
                    ptr::null_mut(),
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => return false,
                    Err(_) => assert!(event.wait(None)),
                }
            }

            let event_ref = self.event_ref.load(Ordering::Acquire);
            self.park_reset(event_ref)
        })
    }

    #[inline]
    fn park_reset(&self, event_ref: *mut EventRef) -> bool {
        assert_eq!(NonNull::new(event_ref), Self::notified());
        self.event_ref.store(ptr::null_mut(), Ordering::Relaxed);
        true
    }

    #[inline]
    pub(super) unsafe fn unpark(self: Pin<&Self>) {
        let event_ref_ptr = &self.event_ref as *const AtomicPtr<EventRef>;
        core::mem::drop(self);

        let notified_ptr = Self::notified().unwrap().as_ptr();
        let event_ref = (*event_ref_ptr).swap(notified_ptr, Ordering::AcqRel);

        if let Some(event_ref) = NonNull::new(event_ref) {
            self.unpark_slow(event_ref)
        }
    }

    #[cold]
    unsafe fn unpark_slow(&self, event_ref: NonNull<EventRef>) {
        assert_ne!(Some(event_ref), Self::notified());
        
        let event_ref = ptr::read(event_ref.as_ptr());
        (event_ref.unpark_fn)(event_ref.ptr)
    }
}