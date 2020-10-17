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

use self::inner::InnerParker;
use super::Parker;
use crate::utils::sync::spin_loop_hint;
use std::{fmt, time::Instant};

/// A [`Parker`] implementation powered by `std::{thread, time::Instant}`
pub struct StdParker {
    inner: InnerParker,
}

unsafe impl Sync for StdParker {}

impl fmt::Debug for StdParker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StdParker")
            .field("is_parked", &self.inner.is_parked())
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
                InnerParker::yield_now();
                return true;
            }
        };

        if iteration >= 10 {
            return false;
        }

        if iteration <= 3 {
            (0..(1 << iteration)).for_each(|_| spin_loop_hint());
        } else {
            InnerParker::yield_now();
        }

        true
    }

    fn new() -> Self {
        Self {
            inner: InnerParker::new(),
        }
    }

    fn prepare(&mut self) {
        self.inner.prepare();
    }

    fn park(&self) {
        assert!(self.inner.park(None))
    }

    fn park_until(&self, deadline: Self::Instant) -> bool {
        self.inner.park(Some(deadline))
    }

    unsafe fn unpark(&self) {
        self.inner.unpark();
    }
}

#[cfg(feature = "loom")]
mod inner {
    use super::Instant;
    use loom::{
        sync::{Condvar, Mutex},
        thread,
    };

    pub(crate) struct InnerParker {
        waiter: Condvar,
        is_parked: Mutex<bool>,
    }

    impl InnerParker {
        pub(crate) fn new() -> Self {
            Self {
                waiter: Condvar::new(),
                is_parked: Mutex::new(false),
            }
        }

        pub(crate) fn yield_now() {
            thread::yield_now()
        }

        pub(crate) fn is_parked(&self) -> bool {
            *self.is_parked.lock().unwrap()
        }

        pub(crate) fn prepare(&mut self) {
            *self.is_parked.lock().unwrap() = true;
        }

        pub(crate) fn park(&self, deadline: Option<Instant>) -> bool {
            let mut is_parked = self.is_parked.lock().unwrap();

            loop {
                if !(*is_parked) {
                    return true;
                }

                let timeout = if let Some(deadline) = deadline {
                    let now = Instant::now();
                    if now >= deadline {
                        *is_parked = false;
                        return false;
                    } else {
                        Some(deadline - now)
                    }
                } else {
                    None
                };

                is_parked = if let Some(timeout) = timeout {
                    self.waiter.wait_timeout(is_parked, timeout).unwrap().0
                } else {
                    self.waiter.wait(is_parked).unwrap()
                };
            }
        }

        pub(crate) fn unpark(&self) {
            let was_parked = {
                let mut is_parked = self.is_parked.lock().unwrap();
                std::mem::replace(&mut *is_parked, false)
            };

            if was_parked {
                self.waiter.notify_one();
            }
        }
    }
}

#[cfg(not(feature = "loom"))]
mod inner {
    use crate::utils::sync::{AtomicBool, Ordering, FALSE, TRUE};
    use std::{cell::Cell, thread, time::Instant};

    pub(crate) struct InnerParker {
        is_parked: AtomicBool,
        thread: Cell<Option<thread::Thread>>,
    }

    impl InnerParker {
        pub(crate) fn new() -> Self {
            Self {
                is_parked: AtomicBool::new(FALSE),
                thread: Cell::new(None),
            }
        }

        pub(crate) fn yield_now() {
            thread::yield_now()
        }

        pub(crate) fn is_parked(&self) -> bool {
            let is_parked = self.is_parked.load(Ordering::Relaxed);
            is_parked == TRUE
        }

        pub(crate) fn prepare(&mut self) {
            let is_parked = *self.is_parked.get_mut();
            if is_parked == FALSE {
                *self = Self {
                    is_parked: AtomicBool::new(TRUE),
                    thread: Cell::new(Some(thread::current())),
                };
            }
        }

        pub(crate) fn park(&self, deadline: Option<Instant>) -> bool {
            loop {
                if self.is_parked.load(Ordering::Acquire) == FALSE {
                    return true;
                }

                let timeout = if let Some(deadline) = deadline {
                    let now = Instant::now();
                    if now >= deadline {
                        return false;
                    } else {
                        Some(deadline - now)
                    }
                } else {
                    None
                };

                match timeout {
                    Some(timeout) => thread::park_timeout(timeout),
                    None => thread::park(),
                }
            }
        }

        pub(crate) fn unpark(&self) {
            let thread = self.thread.take();
            self.is_parked.store(FALSE, Ordering::Release);

            thread
                .expect("StdParker unparked when not prepared")
                .unpark()
        }
    }
}
