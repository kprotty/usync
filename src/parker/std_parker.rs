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
use std::{cell::Cell, fmt, thread, time::Instant};

/// A [`Parker`] implementation powered by `std::{thread, time::Instant}`
pub struct StdParker {
    is_notified: AtomicBool,
    thread: Cell<Option<thread::Thread>>,
}

impl fmt::Debug for StdParker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let is_notified = self.is_notified.load(Ordering::Relaxed);
        let is_notified = is_notified == TRUE;

        f.debug_struct("StdParker")
            .field("unparked", &is_notified)
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
            is_notified: AtomicBool::new(FALSE),
            thread: Cell::new(None),
        }
    }

    fn prepare(&self) {
        // Safety: we should effectively have a &mut self atm
        let is_prepared = unsafe {
            let thread = &*self.thread.as_ptr();
            thread.is_some()
        };

        if !is_prepared {
            self.thread.set(Some(thread::current()));
            self.is_notified.store(FALSE, Ordering::Relaxed);
        }
    }

    fn park(&self) {
        while self.is_notified.load(Ordering::Acquire) == FALSE {
            thread::park();
        }
    }

    fn park_until(&self, deadline: Self::Instant) -> bool {
        loop {
            if self.is_notified.load(Ordering::Acquire) != FALSE {
                return true;
            }

            let now = Self::Instant::now();
            if now >= deadline {
                return false;
            }

            thread::park_timeout(deadline - now);
        }
    }

    fn unpark(&self) {
        let thread = self.thread.take();
        self.is_notified.store(TRUE, Ordering::Release);
        thread
            .expect("StdParker unparked when not prepared")
            .unpark()
    }
}
