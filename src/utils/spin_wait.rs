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
use core::marker::PhantomData;

pub struct SpinWait<P> {
    iteration: Option<usize>,
    _parker: PhantomData<*mut P>,
}

impl<P> SpinWait<P> {
    pub const fn new() -> Self {
        Self {
            iteration: Some(0),
            _parker: PhantomData,
        }
    }

    pub fn reset(&mut self) {
        self.iteration = Some(0);
    }
}

impl<P: Parker> SpinWait<P> {
    pub fn force_spin(&mut self) {
        if !self.try_spin() {
            P::yield_now(None);
        }
    }

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
