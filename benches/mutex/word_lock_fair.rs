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

use super::util::{Instant, Parker, SpinWait};
use std::{
    cell::Cell,
    ptr::NonNull,
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

const UNLOCKED: usize = 0;
const LOCKED: usize = 1;
const WAITING: usize = !LOCKED;

#[repr(align(2))]
struct Waiter {
    prev: Cell<Option<NonNull<Self>>>,
    next: Cell<Option<NonNull<Self>>>,
    tail: Cell<Option<NonNull<Self>>>,
    event: Cell<Option<(Parker, Instant)>>,
    acquired: Cell<bool>,
}

pub struct Lock {
    state: AtomicUsize,
}

unsafe impl super::Lock for Lock {
    const NAME: &'static str = "word_lock_fair";

    fn new() -> Self {
        Self {
            state: AtomicUsize::new(UNLOCKED),
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
    pub fn acquire(&self) {
        if self
            .state
            .compare_exchange_weak(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
            .is_err()
        {
            unsafe { self.acquire_slow() };
        }
    }

    #[cold]
    unsafe fn acquire_slow(&self) {
        let waiter = Waiter {
            prev: Cell::new(None),
            next: Cell::new(None),
            tail: Cell::new(None),
            event: Cell::new(None),
            acquired: Cell::new(false),
        };

        let mut spin = SpinWait::new();
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

            let head = NonNull::new((state & WAITING) as *mut Waiter);
            if head.is_none() && spin.yield_now() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            if (&*waiter.event.as_ptr()).is_none() {
                waiter.event.set(Some((Parker::new(), {
                    use std::convert::TryInto;
                    let ptr = head.unwrap_or(NonNull::from(&waiter));
                    let ptr = (ptr.as_ptr() as usize).wrapping_mul(31);
                    let timeout: u32 = ((ptr >> 16) & 0xffffffff).try_into().unwrap();
                    let timeout = 500_000 + (timeout % 500_000);
                    Instant::now() + Duration::new(0, timeout)
                })));
            }

            waiter.prev.set(None);
            waiter.next.set(head);
            waiter.tail.set(match head {
                Some(_) => None,
                None => Some(NonNull::from(&waiter)),
            });

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                (state & !WAITING) | (&waiter as *const _ as usize),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                state = e;
                continue;
            }

            let parker = &(&*waiter.event.as_ptr()).as_ref().unwrap().0;
            parker.park();
            if waiter.acquired.get() {
                return;
            } else {
                parker.prepare();
            }

            spin.reset();
            state = self.state.load(Ordering::Relaxed);
        }
    }

    #[inline]
    pub fn release(&self) {
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
        let mut released_at = None;
        let mut state = self.state.load(Ordering::Acquire);

        loop {
            unsafe {
                let head = NonNull::new((state & WAITING) as *mut Waiter);
                let head = head.expect("release() with no waiting head");

                let tail = head.as_ref().tail.get();
                let tail = tail.unwrap_or_else(|| {
                    let mut current = head;
                    loop {
                        let next = current.as_ref().next.get();
                        let next = next.expect("no next link in waiter queue");
                        next.as_ref().prev.set(Some(current));
                        current = next;
                        if let Some(tail) = current.as_ref().tail.get() {
                            head.as_ref().tail.set(Some(tail));
                            break tail;
                        }
                    }
                });

                let event = &*tail.as_ref().event.as_ptr();
                let (parker, force_fair_at) =
                    event.as_ref().expect("waiter enqueued without an event");

                let be_fair = {
                    let released = released_at.unwrap_or_else(|| {
                        released_at = Some(Instant::now());
                        released_at.unwrap()
                    });
                    released > *force_fair_at
                };

                match tail.as_ref().prev.get() {
                    Some(new_tail) => {
                        head.as_ref().tail.set(Some(new_tail));
                        if !be_fair {
                            self.state.fetch_and(!LOCKED, Ordering::Release);
                        }
                    }
                    _ => match self.state.compare_exchange_weak(
                        state,
                        if be_fair { LOCKED } else { UNLOCKED },
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => {}
                        Err(e) => {
                            state = e;
                            continue;
                        }
                    },
                }

                tail.as_ref().acquired.set(be_fair);
                parker.unpark();
                return;
            }
        }
    }
}
