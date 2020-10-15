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

use super::sync::UnsafeCell;
use core::{cell::Cell, marker::PhantomPinned, pin::Pin, ptr::NonNull};

/// An intrusive, Doubly linked list Node with internal data.
pub(crate) struct Node<T> {
    pub(crate) prev: Cell<Option<NonNull<Self>>>,
    pub(crate) next: Cell<Option<NonNull<Self>>>,
    pub(crate) tail: Cell<Option<NonNull<Self>>>,
    value: UnsafeCell<T>,
    _pinned: PhantomPinned,
}

impl<T> Node<T> {
    pub(crate) fn new(value: T) -> Self {
        Self {
            prev: Cell::new(None),
            next: Cell::new(None),
            tail: Cell::new(None),
            value: UnsafeCell::new(value),
            _pinned: PhantomPinned,
        }
    }

    #[inline]
    pub(crate) fn with<F>(&self, f: impl FnOnce(*const T) -> F) -> F {
        self.value.with(f)
    }

    #[inline]
    pub(crate) fn with_mut<F>(&self, f: impl FnOnce(*mut T) -> F) -> F {
        self.value.with_mut(f)
    }
}

/// A Doubly-linked lists of of [`Node`]s
pub(crate) struct Queue<T> {
    head: Option<NonNull<Node<T>>>,
}
