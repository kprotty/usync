use std::{marker::PhantomData, time::Duration};

pub(crate) struct Queue<T> {
    x: PhantomData<T>,
}

impl<T> Queue<T> {
    pub(crate) const fn new() -> Self {
        Self { x: PhantomData }
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
