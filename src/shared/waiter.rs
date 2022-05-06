use super::{parker::Parker, StrictProvenance};
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
    #[inline]
    pub(crate) fn set(&self, ptr: Option<NonNull<Waiter>>) {
        let ptr = ptr.map(|p| p.as_ptr()).unwrap_or(ptr::null_mut());
        self.0.store(ptr, Ordering::Relaxed);
    }

    #[inline]
    pub(crate) fn get(&self) -> Option<NonNull<Waiter>> {
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
    pub(crate) waiting_on: Cell<Option<NonNull<()>>>,
    pub(crate) counter: AtomicUsize,
    pub(crate) flags: Cell<usize>,
    pub(crate) parker: Parker,
    _pinned: PhantomPinned,
}

impl Waiter {
    // The waiter is aligned to 16 from the repr to allow ample tagging bits.
    pub(crate) const MASK: usize = !0b1111usize;

    pub(crate) fn with<F>(f: impl FnOnce(Pin<&Self>) -> F) -> F {
        // SAFETY: the waiter lives on stack.
        let waiter = Self::default();
        f(unsafe { Pin::new_unchecked(&waiter) })
    }

    pub(crate) unsafe fn get_and_link_queue(
        value: *mut Waiter,
        mut on_waiter_discovered: impl FnMut(NonNull<Self>),
    ) -> (NonNull<Self>, NonNull<Self>) {
        let head = NonNull::new(value.map_address(|addr| addr & Self::MASK));
        let head = head.expect("invalid Waiter queue head pointer");

        // Check if the tail is cached at the head from a previous get_and_link_queue() call.
        let tail = head.as_ref().tail.get().unwrap_or_else(|| {
            let mut current = head;
            loop {
                // Scan through the link following the `next` fields to find the tail of the queue.
                let next = current.as_ref().next.get();
                let next = next.expect("Waiter queue with unreachable tail");

                // While scanning, set the prev fields to make the queue a doubly-linked list
                next.as_ref().prev.set(Some(current));
                on_waiter_discovered(next);
                current = next;

                // Stop when we find a waiter with the tail set.
                // It was set either due to being cached as a previous head
                // or if it really is the tail of the queue.
                if let Some(tail) = current.as_ref().tail.get() {
                    head.as_ref().tail.set(Some(tail));
                    return tail;
                }
            }
        });

        (head, tail)
    }
}
