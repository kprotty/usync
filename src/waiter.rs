use super::parker::Parker;
use std::{
    cell::Cell,
    thread,
    hint::spin_loop,
    pin::Pin,
    marker::PhantomPinned,
    ptr::{self, NonNull},
    time::Instant,
    sync::atomic::{AtomicPtr, AtomicUsize, AtomicBool, Ordering},
};

type WaiterCell = Cell<Option<NonNull<Waiter>>>;

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
    thread: Cell<Option<thread::Thread>>,
    unparked: AtomicBool,
}

impl Waiter {
    pub(super) const MASK: usize = !0b1111usize;

    pub(super) fn with<F>(&self, f: impl FnOnce(Pin<&Self>) -> F) -> F {
        let waiter = Self::default();
        f(unsafe { Pin::new_unchecked(&waiter) })
    }

    pub(super) unsafe fn get_queue(
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

    #[inline]
    pub(super) fn prepare(&self) {
        let thread = self.thread.take();
        let thread = thread.unwrap_or_else(|| thread::current());

        self.thread.set(Some(thread));
        self.unparked.store(false, Ordering::Relaxed);
    }

    #[cold]
    pub(super) fn park(&self, deadline: Option<Instant>) -> bool {
        let mut deadline = None;
        loop {
            if self.unparked.load(Ordering::Acquire) {
                return true;
            }

            match deadline {
                None => thread::park(),
                Some(deadline) => {
                    match expires.checked_duration_since(Instant::now()) {
                        Some(timeout) => thread::park_timeout(timeout),
                        None => return false,
                    }
                }
            }
        }
    }

    #[cold]
    pub(super) fn unpark(&self) {
        let thread = self.thread.take();
        let unparked = &self.unparked as *const AtomicBool;

        drop(self);
        unsafe { (&*unparked).store(true, Ordering::Release) };

        let thread = thread.expect("Waiter unparked without being prepared.");
        thread.unpark()
    }

    #[inline]
    pub(super) fn try_spin(attempt: usize) -> bool {
        attempt < 32 && {
            spin_loop();
            true
        }
    }
}