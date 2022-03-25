use super::parker::Parker;
use std::{
    cell::Cell,
    marker::PhantomPinned,
    pin::Pin,
    ptr::{self, NonNull},
    sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
};

#[derive(Default)]
pub(crate) struct AtomicWaiterCell(AtomicPtr<Waiter>);

impl AtomicWaiterCell {
    fn set(&self, ptr: Option<NonNull<Waiter>>) {
        let ptr = ptr.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
        self.0.store(ptr, Ordering::Relaxed);
    }

    fn get(&self) -> Option<NonNull<Waiter>> {
        let ptr = self.0.load(Ordering::Relaxed);
        NonNull::new(ptr)
    }
}

#[derive(Default)]
#[repr(align(16))]
pub(crate) struct Waiter {
    pub(crate) next: Cell<Option<NonNull<Self>>>,
    pub(crate) prev: AtomicWaiterCell,
    pub(crate) tail: AtomicWaiterCell,
    pub(crate) waiting_on: Cell<Option<NonNull<AtomicUsize>>>,
    pub(crate) counter: AtomicUsize,
    pub(crate) flags: Cell<usize>,
    pub(crate) parker: Parker,
    _pinned: PhantomPinned,
}

impl Waiter {
    pub(crate) const MASK: usize = !0b1111usize;

    pub(crate) fn with<F>(f: impl FnOnce(Pin<&Self>) -> F) -> F {
        let waiter = Self::default();
        f(unsafe { Pin::new_unchecked(&waiter) })
    }

    pub(crate) unsafe fn get_and_link_queue(
        value: usize,
        mut on_waiter_discovered: impl FnMut(NonNull<Self>),
    ) -> (NonNull<Self>, NonNull<Self>) {
        let head = NonNull::new((value & Self::MASK) as *mut Waiter);
        let head = head.expect("invalid Waiter queue head pointer");

        let tail = head.as_ref().tail.get().unwrap_or_else(|| {
            let mut current = head;
            loop {
                let next = current.as_ref().next.get();
                let next = next.expect("Waiter queue with unreachable tail");

                next.as_ref().prev.set(Some(current));
                on_waiter_discovered(next);
                current = next;

                if let Some(tail) = current.as_ref().tail.get() {
                    head.as_ref().tail.set(Some(tail));
                    return tail;
                }
            }
        });

        (head, tail)
    }
}
