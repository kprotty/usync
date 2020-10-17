// Copyright (c) 2020 kprotty
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Wrappers for [`core::sync`] which allow a central place to substitute platform atomics and shared mutability.

pub(crate) use core::sync::atomic::{fence, spin_loop_hint, Ordering};

#[cfg(target_atomic_usize)]
pub(crate) use core::sync::atomic::AtomicUsize;

#[cfg(target_atomic_u8)]
pub(crate) use core::sync::atomic::AtomicU8;

pub(crate) use atomic_bool::*;
pub(crate) use atomic_int::*;

#[cfg(target_atomic_u8)]
mod atomic_int {
    pub(crate) type Int = u8;
    pub(crate) type AtomicInt = super::AtomicU8;
}

#[cfg(not(target_atomic_u8))]
mod atomic_int {
    pub(crate) type Int = usize;
    pub(crate) type AtomicInt = super::AtomicUsize;
}

#[cfg(target_atomic_bool)]
mod atomic_bool {
    pub(crate) type AtomicBool = core::sync::atomic::AtomicBool;
    pub(crate) const TRUE: bool = true;
    pub(crate) const FALSE: bool = false;
}

#[cfg(all(not(target_atomic_bool), target_atomic_u8))]
mod atomic_bool {
    pub(crate) type AtomicBool = super::AtomicU8;
    pub(crate) const TRUE: u8 = 1;
    pub(crate) const FALSE: u8 = 0;
}

#[cfg(all(not(target_atomic_bool), not(target_atomic_u8), target_atomic_usize))]
mod atomic_bool {
    pub(crate) type AtomicBool = super::AtomicUsize;
    pub(crate) const TRUE: usize = 1;
    pub(crate) const FALSE: usize = 0;
}

#[derive(Debug, Default)]
pub(crate) struct UnsafeCell<T>(core::cell::UnsafeCell<T>);

impl<T> UnsafeCell<T> {
    pub(crate) const fn new(value: T) -> Self {
        Self(core::cell::UnsafeCell::new(value))
    }

    pub(crate) fn with<F>(&self, f: impl FnOnce(*const T) -> F) -> F {
        f(self.0.get())
    }

    pub(crate) fn with_mut<F>(&self, f: impl FnOnce(*mut T) -> F) -> F {
        f(self.0.get())
    }

    pub(crate) fn into_inner(self) -> T {
        self.0.into_inner()
    }
}