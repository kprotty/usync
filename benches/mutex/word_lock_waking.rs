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

use super::util::{Parker, SpinWait};
use std::{
    cell::Cell,
    ptr::NonNull,
    sync::atomic::{AtomicU8, AtomicUsize, Ordering},
};

const UNLOCKED: u8 = 0;
const LOCKED: u8 = 1;
const WAKING: usize = 1 << 8;
const WAITING: usize = !((1usize << 9) - 1);

#[repr(align(512))]
struct Waiter {
    prev: Cell<Option<NonNull<Self>>>,
    next: Cell<Option<NonNull<Self>>>,
    tail: Cell<Option<NonNull<Self>>>,
    waiters: Cell<usize>,
    parker: Parker,
}

impl Waiter {
    fn new() -> Self {
        Waiter {
            prev: Cell::new(None),
            next: Cell::new(None),
            tail: Cell::new(None),
            waiters: Cell::new(0),
            parker: Parker::new(),
        }
    }

    #[inline(always)]
    fn with<T>(f: impl FnOnce(&Waiter) -> T) -> T {
        let mut ptr = std::ptr::null();

        if !Parker::IS_CHEAP_TO_CONSTRUCT {
            thread_local!(static WAITER: Waiter = Waiter::new());
            if let Ok(waiter_ptr) = WAITER.try_with(|x| x as *const Waiter) {
                ptr = waiter_ptr;
            }
        }

        let mut stack_waiter = None;
        if ptr.is_null() {
            ptr = stack_waiter.get_or_insert_with(Waiter::new);
        }

        f(unsafe { &*ptr })
    }
}

pub struct Lock {
    state: AtomicUsize,
}

unsafe impl super::Lock for Lock {
    const NAME: &'static str = "word_lock_waking";

    fn new() -> Self {
        Self {
            state: AtomicUsize::new(UNLOCKED as usize),
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
    fn byte_state(&self) -> &AtomicU8 {
        unsafe { &*(&self.state as *const _ as *const _) }
    }

    #[inline]
    fn try_acquire(&self) -> bool {
        self.byte_state().swap(LOCKED, Ordering::Acquire) == UNLOCKED
    }

    #[inline]
    pub fn acquire(&self) {
        if !self.try_acquire() {
            self.acquire_slow();
        }
    }

    #[cold]
    fn acquire_slow(&self) {
        let mut spin = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);

        loop {
            if state & (LOCKED as usize) == 0 {
                if self.try_acquire() {
                    return;
                }
                std::thread::yield_now();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            let head = NonNull::new((state & WAITING) as *mut Waiter);
            if head.is_none() && spin.yield_now() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            Waiter::with(|waiter| {
                waiter.parker.prepare();
                waiter.waiters.set(1);
                waiter.prev.set(None);
                waiter.next.set(head);
                waiter.tail.set(match head {
                    Some(_) => None,
                    None => Some(NonNull::from(waiter)),
                });

                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    (state & !WAITING) | (waiter as *const _ as usize),
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    return;
                }

                waiter.parker.park();
                spin.reset();

                if waiter.waiters.get() == 0 {
                    state = self.state.load(Ordering::Relaxed);
                } else {
                    state = self.state.fetch_sub(WAKING, Ordering::Relaxed) - WAKING;
                }
            });
        }
    }

    #[inline]
    pub fn release(&self) {
        self.byte_state().store(UNLOCKED, Ordering::Release);

        let state = self.state.load(Ordering::Relaxed);
        if (state & WAITING != 0) && (state & WAKING == 0) {
            self.release_slow();
        }
    }

    #[cold]
    fn release_slow(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if (state & WAITING == 0) || (state & ((LOCKED as usize) | WAKING) != 0) {
                return;
            }
            match self.state.compare_exchange_weak(
                state,
                state | WAKING,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(e) => state = e,
            }
        }

        state |= WAKING;
        loop {
            unsafe {
                let head = NonNull::new((state & WAITING) as *mut Waiter);
                let head = head.expect("release() with no waiting head");

                let tail = head.as_ref().tail.get();
                let tail = tail.unwrap_or_else(|| {
                    let mut current = head;
                    let mut waiters = 0;
                    loop {
                        let next = current.as_ref().next.get();
                        let next = next.expect("no next link in waiter queue");
                        next.as_ref().prev.set(Some(current));
                        current = next;
                        waiters += 1;
                        if let Some(tail) = current.as_ref().tail.get() {
                            waiters += tail.as_ref().waiters.get();
                            tail.as_ref().waiters.set(waiters);
                            head.as_ref().tail.set(Some(tail));
                            break tail;
                        }
                    }
                });

                if state & (LOCKED as usize) != 0 {
                    match self.state.compare_exchange_weak(
                        state,
                        state & !WAKING,
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => return,
                        Err(e) => state = e,
                    }
                    continue;
                }

                let waiters = tail.as_ref().waiters.get();
                let waiters = std::num::NonZeroUsize::new_unchecked(waiters);
                let should_wake = {
                    match waiters.get() {
                        0 => unreachable!(),
                        1 => false,
                        x => x % 2 == 0,
                    }
                };

                match tail.as_ref().prev.get() {
                    Some(new_tail) => {
                        head.as_ref().tail.set(Some(new_tail));
                        new_tail.as_ref().waiters.set(waiters.get() - 1);

                        if should_wake {
                            std::sync::atomic::fence(Ordering::Release);
                        } else {
                            self.state.fetch_and(!WAKING, Ordering::Release);
                        }
                    }
                    _ => match self.state.compare_exchange_weak(
                        state,
                        if should_wake {
                            WAKING
                        } else {
                            UNLOCKED as usize
                        },
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

                tail.as_ref()
                    .waiters
                    .set(if should_wake { waiters.get() } else { 0 });
                tail.as_ref().parker.unpark();
                return;
            }
        }
    }
}
