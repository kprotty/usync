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

pub(crate) unsafe trait StrictProvenance: Copy {
    fn address(self) -> usize;

    fn with_address(self, addr: usize) -> Self;

    fn map_address(self, f: impl FnOnce(usize) -> usize) -> Self {
        self.with_address(f(self.address()))
    }
}

unsafe impl<T> StrictProvenance for *mut T {
    fn address(self) -> usize {
        self as usize
    }

    #[cfg(not(miri))]
    fn with_address(self, addr: usize) -> Self {
        addr as Self
    }

    #[cfg(miri)]
    fn with_address(self, new_addr: usize) -> Self {
        let old_addr = self as usize;
        let diff = new_addr.wrapping_sub(old_addr);
        self.cast::<u8>().wrapping_add(diff).cast::<T>()
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
                .fetch_add(value.address(), ordering) as *mut T
        }
    }

    fn fetch_sub(&self, value: *mut T, ordering: Ordering) -> *mut T {
        unsafe {
            NonNull::from(self)
                .cast::<AtomicUsize>()
                .as_ref()
                .fetch_sub(value.address(), ordering) as *mut T
        }
    }
}
