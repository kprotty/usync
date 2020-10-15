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

use crate::parker::Parker;
use core::{fmt, marker::PhantomData};

/// A SpinWait wraps the `yield_now` funciton of a `Parker` to implement context based yielding.
pub struct SpinWait<P> {
    iteration: Option<usize>,
    _parker: PhantomData<*mut P>,
}

impl<P> fmt::Debug for SpinWait<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SpinWait").finish()
    }
}

impl<P> Default for SpinWait<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P> SpinWait<P> {
    /// Create a new SpinWait with a reset state.
    pub const fn new() -> Self {
        Self {
            iteration: Some(0),
            _parker: PhantomData,
        }
    }

    /// Reset the SpinWait back to the starting state.
    pub fn reset(&mut self) {
        self.iteration = Some(0);
    }
}

impl<P: Parker> SpinWait<P> {
    /// Yield on the parker, using the context if available and
    /// falling back to no-context yielding when saturated.
    pub fn spin(&mut self) {
        if !self.try_spin() {
            P::yield_now(None);
        }
    }

    /// Try to yield using the context if it hasn't been saturated yet.
    /// Returns true if the caller can or should spin again.
    pub fn try_spin(&mut self) -> bool {
        self.iteration = self.iteration.and_then(|iteration| {
            if P::yield_now(Some(iteration)) {
                Some(iteration.wrapping_add(1))
            } else {
                None
            }
        });

        self.iteration.is_some()
    }
}
