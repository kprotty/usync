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

use super::util::{Instant, Parker};
use std::{
    cell::{Cell, UnsafeCell},
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
};

struct Waiter {
    next: Cell<Option<NonNull<Self>>>,
    tail: Cell<NonNull<Self>>,
    parker: Parker,
    acquired: Cell<bool>,
}

struct Inner {
    prng: u32,
    fair_at: Instant,
    head: Option<NonNull<Waiter>>,
}

const UNLOCKED: usize = 0;
const LOCKED: usize = 1;
const PARKED: usize = 2;

// type InnerLock = super::usync_lock::Lock;
type InnerLock = super::word_lock_waking::Lock;

pub struct Lock {
    state: AtomicUsize,
    lock: InnerLock,
    inner: UnsafeCell<Inner>,
}

unsafe impl Send for Lock {}
unsafe impl Sync for Lock {}

unsafe impl super::Lock for Lock {
    const NAME: &'static str = "sym_lock";

    fn new() -> Self {
        Self {
            state: AtomicUsize::new(UNLOCKED),
            lock: InnerLock::new(),
            inner: UnsafeCell::new(Inner {
                prng: 0xdeadbeef,
                fair_at: Instant::now(),
                head: None,
            }),
        }
    }

    fn with(&self, f: impl FnOnce()) {
        self.acquire();
        f();
        self.release();
    }
}

impl Lock {
    #[inline]
    fn with_inner<T>(&self, f: impl FnOnce(&mut Inner) -> T) -> T {
        use super::Lock;
        let mut result = None;
        self.lock
            .with(|| result = Some(f(unsafe { &mut *self.inner.get() })));
        result.unwrap()
    }

    #[inline]
    fn acquire(&self) {
        if self
            .state
            .compare_exchange_weak(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            self.acquire_slow();
        }
    }

    #[cold]
    fn acquire_slow(&self) {
        let mut spin = 0;
        let waiter = Cell::new(None);
        let mut state = self.state.load(Ordering::Relaxed);

        loop {
            if state & LOCKED == 0 {
                match self.state.compare_exchange_weak(
                    state,
                    state | LOCKED,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(e) => state = e,
                }
                continue;
            }

            if state & PARKED == 0 {
                if spin < 10 {
                    spin += 1;
                    if spin <= 3 {
                        (0..(1 << spin)).for_each(|_| std::sync::atomic::spin_loop_hint());
                    } else if cfg!(windows) {
                        std::thread::sleep(std::time::Duration::new(0, 0));
                    } else {
                        std::thread::yield_now();
                    }
                    state = self.state.load(Ordering::Relaxed);
                    continue;
                }

                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    state | PARKED,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }
            }

            let is_waiting = self.with_inner(|inner| unsafe {
                state = self.state.load(Ordering::Relaxed);
                if state != (LOCKED | PARKED) {
                    return false;
                }

                if (&*waiter.as_ptr()).as_ref().is_none() {
                    waiter.set(Some(Waiter {
                        next: Cell::new(None),
                        tail: Cell::new(NonNull::dangling()),
                        parker: Parker::new(),
                        acquired: Cell::new(false),
                    }));
                }

                let waiter_ref = (&*waiter.as_ptr()).as_ref().unwrap();
                waiter_ref.next.set(None);
                if let Some(head_ptr) = inner.head {
                    let tail = head_ptr.as_ref().tail.replace(NonNull::from(waiter_ref));
                    tail.as_ref().next.set(Some(NonNull::from(waiter_ref)));
                } else {
                    inner.head = Some(NonNull::from(waiter_ref));
                    waiter_ref.tail.set(NonNull::from(waiter_ref));
                }

                waiter_ref.parker.prepare();
                true
            });

            if is_waiting {
                let waiter_ref = unsafe { (&*waiter.as_ptr()).as_ref().unwrap() };
                waiter_ref.parker.park();
                if waiter_ref.acquired.get() {
                    return;
                }
            }

            spin = 0;
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[inline]
    fn release(&self) {
        if self
            .state
            .compare_exchange(LOCKED, UNLOCKED, Ordering::Release, Ordering::Relaxed)
            .is_err()
        {
            self.release_slow();
        }
    }

    #[cold]
    fn release_slow(&self) {
        let waiter = self.with_inner(|inner| unsafe {
            let waiter = inner.head.map(|waiter| {
                inner.head = waiter.as_ref().next.get();
                if let Some(head) = inner.head {
                    head.as_ref().tail.set(waiter.as_ref().tail.get());
                }
                waiter
            });

            let has_more = inner.head.is_some();
            let be_fair = waiter
                .map(|waiter| {
                    let now = Instant::now();
                    now > inner.fair_at && {
                        waiter.as_ref().acquired.set(true);
                        inner.fair_at = now
                            + std::time::Duration::new(0, {
                                let mut x = inner.prng;
                                x ^= x << 13;
                                x ^= x >> 17;
                                x ^= x << 5;
                                inner.prng = x;
                                x % 1_000_000
                            });
                        true
                    }
                })
                .unwrap_or(false);

            if be_fair {
                if !has_more {
                    self.state.store(LOCKED, Ordering::Relaxed);
                }
            } else {
                let state = if has_more { PARKED } else { UNLOCKED };
                self.state.store(state, Ordering::Release);
            }

            waiter
        });

        if let Some(waiter) = waiter {
            unsafe { waiter.as_ref().parker.unpark() };
        }
    }
}
