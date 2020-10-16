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

use super::Parker;
use crate::utils::sync::{spin_loop_hint, AtomicBool, Ordering, FALSE, TRUE};
use core::{fmt, ops::Add, time::Duration};

/// A [`Parker`] implementation which spins to simulate blocking and uses a no-op `Instant`.
pub struct SpinParker {
    is_parked: AtomicBool,
}

impl fmt::Debug for SpinParker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let is_parked = self.is_parked.load(Ordering::Relaxed);
        let is_parked = is_parked == TRUE;

        f.debug_struct("SpinParker")
            .field("is_parked", &is_parked)
            .finish()
    }
}

impl Default for SpinParker {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Parker for SpinParker {
    type Instant = SpinInstant;

    fn now() -> Self::Instant {
        Self::Instant {}
    }

    fn yield_now(_iteration: Option<usize>) -> bool {
        spin_loop_hint();
        true
    }

    fn new() -> Self {
        Self {
            is_parked: AtomicBool::new(FALSE),
        }
    }

    fn prepare(&mut self) {
        self.is_parked = AtomicBool::new(TRUE);
    }

    fn park(&self) {
        while self.is_parked.load(Ordering::Acquire) == TRUE {
            spin_loop_hint();
        }
    }

    fn park_until(&self, _deadline: Self::Instant) -> bool {
        self.park();
        true
    }

    unsafe fn unpark(&self) {
        self.is_parked.store(FALSE, Ordering::Release);
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct SpinInstant;

impl Add<Duration> for SpinInstant {
    type Output = Self;

    fn add(self, _duration: Duration) -> Self {
        self
    }
}
