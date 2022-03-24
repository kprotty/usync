use super::Futex;
use crate::sync::atomic::{AtomicU32, Ordering};
use std::marker::PhantomData;

pub struct RwLock<F> {
    state: AtomicU32,
    epoch: AtomicU32,
    _futex: PhantomData<F>,
}

impl<F> RwLock<F> {
    pub const fn new() -> Self {

    }
}

impl<F: Futex> RwLock<F> {
    #[inline]
    pub fn try_write(&self) -> bool {

    }

    #[inline]
    pub fn write(&self) {

    }

    #[inline]
    pub unsafe fn unlock_write(&self) {

    }

    #[inline]
    pub fn try_read(&self) -> bool {

    }

    #[inline]
    pub fn read(&self) {

    }

    #[inline]
    pub unsafe fn unlock_read(&self) {

    }
}