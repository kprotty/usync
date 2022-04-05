use std::{marker::PhantomData, num::NonZeroUsize, time::Duration};

pub(crate) struct Queue<T> {
    x: PhantomData<T>,
}

impl<T> Queue<T> {
    pub(crate) const fn new(n: NonZeroUsize) -> Self {
        Self { x: PhantomData }
    }

    pub(crate) fn try_send(&self, item: T) -> Result<(), Result<T, T>> {
        unimplemented!("TODO")
    }

    pub(crate) fn send(&self, item: T) -> Result<(), T> {
        unimplemented!("TODO")
    }

    pub(crate) unsafe fn try_recv(&self) -> Result<Option<T>, ()> {
        unimplemented!("TODO")
    }

    pub(crate) unsafe fn recv(&self, timeout: Option<Duration>) -> Result<Option<T>, ()> {
        unimplemented!("TODO")
    }

    pub(crate) fn disconnect(&self) {
        unimplemented!("TODO")
    }
}
