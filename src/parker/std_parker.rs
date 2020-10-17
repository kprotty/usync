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
use crate::utils::sync::{AtomicBool, Ordering, TRUE, FALSE, spin_loop_hint};
use std::{fmt, cell::Cell, thread, time::Instant};

/// A [`Parker`] implementation powered by `std::{thread, time::Instant}`
pub struct StdParker {
    is_parked: AtomicBool,
    thread: Cell<Option<thread::Thread>>,
}

unsafe impl Sync for StdParker {}

impl fmt::Debug for StdParker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let is_parked = self.is_parked.load(Ordering::Relaxed);
        let is_parked = is_parked == TRUE;

        f.debug_struct("StdParker")
            .field("is_parked", &is_parked)
            .finish()
    }
}

impl Default for StdParker {
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl Parker for StdParker {
    type Instant = Instant;

    fn now() -> Self::Instant {
        Self::Instant::now()
    }

    fn yield_now(iteration: Option<usize>) -> bool {
        let iteration = match iteration {
            Some(iteration) => iteration,
            None => {
                thread::yield_now();
                return true;
            }
        };

        if iteration >= 10 {
            return false;
        }

        if iteration <= 3 {
            (0..(1 << iteration)).for_each(|_| spin_loop_hint());
        } else {
            thread::yield_now();
        }

        true
    }

    fn new() -> Self {
        Self {
            is_parked: AtomicBool::new(FALSE),
            thread: Cell::new(None),
        }
    }

    fn prepare(&mut self) {
        let is_parked = *self.is_parked.get_mut();
        if is_parked == FALSE {
            *self = Self {
                is_parked: AtomicBool::new(TRUE),
                thread: Cell::new(Some(thread::current())),
            };
        }
    }

    fn park(&self) {
        while self.is_parked.load(Ordering::Acquire) == TRUE {
            thread::park();
        }
    }

    fn park_until(&self, deadline: Self::Instant) -> bool {
        loop {
            if self.is_parked.load(Ordering::Acquire) == FALSE {
                return true;
            }

            let now = Self::Instant::now();
            if now >= deadline {
                return false;
            }

            thread::park_timeout(deadline - now);
        }
    }

    unsafe fn unpark(&self) {
        let thread = self.thread.take();
        self.is_parked.store(FALSE, Ordering::Release);

        thread
            .expect("StdParker unparked when not prepared")
            .unpark()
    }
}