use std::{marker::PhantomData, num::NonZeroUsize};

pub(crate) struct Queue<T> {
    x: PhantomData<T>,
}

impl<T> Queue<T> {
    pub(crate) const fn new(n: NonZeroUsize) -> Self {
        Self { x: PhantomData }
    }

    pub(crate) fn disconnect(&self) {
        unimplemented!("TODO")
    }
}
