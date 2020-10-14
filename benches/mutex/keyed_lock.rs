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
const WAITING: usize = 1 << 9;

const EMPTY: usize = 0;
const NOTIFIED: usize = 1;

#[repr(align(2))]
struct Waiter {
    prev: Cell<Option<NonNull<Self>>>,
    next: Cell<Option<NonNull<Self>>>,
    tail: Cell<Option<NonNull<Self>>>,
    parker: Parker,
}

pub struct Lock {
    state: AtomicUsize,
    waiters: AtomicUsize,
}

unsafe impl super::Lock for Lock {
    const NAME: &'static str = "keyed_lock";

    fn new() -> Self {
        Self {
            state: AtomicUsize::new(UNLOCKED as usize),
            waiters: AtomicUsize::new(EMPTY),
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
    fn acquire(&self) {
        if !self.try_acquire() {
            self.acquire_slow();
        }
    }

    #[cold]
    fn acquire_slow(&self) {
        let waiter = Cell::new(None);
        let mut spin = SpinWait::new();
        let mut state = self.state.load(Ordering::Relaxed);

        loop {
            if state & (LOCKED as usize) == 0 {
                if self.try_acquire() {
                    return;
                }
                std::sync::atomic::spin_loop_hint();
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            if (state < WAITING) && spin.yield_now() {
                state = self.state.load(Ordering::Relaxed);
                continue;
            }

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                state + WAITING,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                state = e;
                continue;
            }

            unsafe { self.wait(&waiter) };

            spin.reset();
            state = self.state.fetch_sub(WAKING, Ordering::Relaxed);
            state -= WAKING;
        }
    }

    #[inline]
    fn release(&self) {
        self.byte_state().store(UNLOCKED, Ordering::Release);

        let state = self.state.load(Ordering::Relaxed);
        if (state >= WAITING) && (state & WAKING == 0) {
            self.release_slow();
        }
    }

    #[cold]
    fn release_slow(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if (state & ((LOCKED as usize) | WAKING)) != 0 {
                return;
            } else if state < WAITING {
                return;
            }
            match self.state.compare_exchange_weak(
                state,
                (state - WAITING) | WAKING,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return unsafe { self.notify() },
                Err(e) => state = e,
            }
        }
    }

    unsafe fn wait(&self, waiter: &Cell<Option<Waiter>>) {
        let mut waiters = self.waiters.load(Ordering::Relaxed);

        loop {
            if waiters == NOTIFIED {
                match self.waiters.compare_exchange_weak(
                    waiters,
                    EMPTY,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(e) => waiters = e,
                }
                continue;
            }

            if (&*waiter.as_ptr()).is_none() {
                waiter.set(Some(Waiter {
                    prev: Cell::new(None),
                    next: Cell::new(None),
                    tail: Cell::new(None),
                    parker: Parker::new(),
                }))
            }

            let head = NonNull::new(waiters as *mut Waiter);
            let waiter_ref = (&*waiter.as_ptr()).as_ref().unwrap();
            waiter_ref.prev.set(None);
            waiter_ref.next.set(head);
            waiter_ref.tail.set(match head {
                Some(_) => None,
                None => Some(NonNull::from(waiter_ref)),
            });

            if let Err(e) = self.waiters.compare_exchange_weak(
                waiters,
                waiter_ref as *const _ as usize,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                waiters = e;
                continue;
            }

            waiter_ref.parker.park();
            waiter_ref.parker.prepare();
            return;
        }
    }

    unsafe fn notify(&self) {
        let mut waiters = self.waiters.load(Ordering::Relaxed);

        while waiters <= NOTIFIED {
            if waiters == NOTIFIED {
                return;
            }
            match self.waiters.compare_exchange_weak(
                waiters,
                NOTIFIED,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(e) => waiters = e,
            }
        }

        waiters = self.waiters.load(Ordering::Acquire);
        loop {
            let head = NonNull::new(waiters as *mut Waiter);
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

            match tail.as_ref().prev.get() {
                Some(new_tail) => {
                    head.as_ref().tail.set(Some(new_tail));
                    std::sync::atomic::fence(Ordering::Release);
                }
                _ => match self.waiters.compare_exchange_weak(
                    waiters,
                    EMPTY,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => {}
                    Err(e) => {
                        waiters = e;
                        continue;
                    }
                },
            }

            tail.as_ref().parker.unpark();
            return;
        }
    }
}
