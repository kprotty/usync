use std::marker::PhantomData;

pub(crate) struct Queue<T> {
    x: PhantomData<T>,
}

impl<T> Queue<T> {
    pub(crate) const fn new() -> Self {
        Self { x: PhantomData }
    }

    pub(crate) fn disconnect(&self) {
        unimplemented!("TODO")
    }
}
