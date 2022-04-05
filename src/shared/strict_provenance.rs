//! #![feature(strict_provenance)] is currently a nightly api at the time of writing.
//!
//! It's a way to maintain pointer meta-data useful to both the compiler and required
//! for soundless by certain platforms like CHERI or other segmented memory systems.
//!
//! This API for interacting with pointers was designed in this issue:
//! https://github.com/rust-lang/rust/issues/95228
//! and extention methods required for AtomicPtr usage were added manually as well.

pub(crate) const fn invalid_mut<T>(addr: usize) -> *mut T {
    addr as *mut T
}

pub(crate) unsafe trait StrictProvenance {
    fn addr(self) -> usize;

    fn with_addr(self, addr: usize) -> Self;

    fn map_addr(self, f: impl FnOnce(usize) -> usize) -> Self;
}

unsafe impl<T> StrictProvenance for *mut T {
    fn addr(self) -> usize {
        self as usize
    }

    fn with_addr(self, addr: usize) -> Self {
        addr as Self
    }

    fn map_addr(self, f: impl FnOnce(usize) -> usize) -> Self {
        self.with_addr(f(self.addr()))
    }
}

use std::{
    ptr::NonNull,
    sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
};

pub(crate) trait AtomicPtrRmw<T> {
    fn fetch_add(&self, value: T, ordering: Ordering) -> T;

    fn fetch_sub(&self, value: T, ordering: Ordering) -> T;
}

impl<T> AtomicPtrRmw<*mut T> for AtomicPtr<T> {
    fn fetch_add(&self, value: *mut T, ordering: Ordering) -> *mut T {
        unsafe {
            NonNull::from(self)
                .cast::<AtomicUsize>()
                .as_ref()
                .fetch_add(value.addr(), ordering) as *mut T
        }
    }

    fn fetch_sub(&self, value: *mut T, ordering: Ordering) -> *mut T {
        unsafe {
            NonNull::from(self)
                .cast::<AtomicUsize>()
                .as_ref()
                .fetch_sub(value.addr(), ordering) as *mut T
        }
    }
}
