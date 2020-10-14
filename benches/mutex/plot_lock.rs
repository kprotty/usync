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
    cell::{Cell, UnsafeCell},
    ptr::NonNull,
    sync::atomic::{AtomicU8, Ordering},
    time::Duration,
};

const UNLOCKED: u8 = 0;
const LOCKED: u8 = 1;
const PARKED: u8 = 2;

pub struct Lock {
    state: AtomicU8,
}

unsafe impl super::Lock for Lock {
    const NAME: &'static str = "plot_lock";

    fn new() -> Self {
        Self {
            state: AtomicU8::new(UNLOCKED),
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
            self.acquire_slow();
        }
    }

    #[cold]
    fn acquire_slow(&self) {
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

            if state & PARKED == 0 {
                if spin.yield_now() {
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

            let acquired = Waiter::with(|waiter| {
                let address = &self.state as *const _ as usize;
                let is_waiting = Bucket::get(address).with(|bucket| unsafe {
                    state = self.state.load(Ordering::Relaxed);
                    if state != (LOCKED | PARKED) {
                        return false;
                    }

                    waiter.parker.prepare();
                    waiter.next.set(None);
                    waiter.acquired.set(false);
                    waiter.address.set(address);

                    if let Some(tail) = bucket.tail {
                        waiter.prev.set(Some(tail));
                        tail.as_ref().next.set(Some(NonNull::from(waiter)));
                    } else {
                        waiter.prev.set(None);
                        bucket.head = Some(NonNull::from(waiter));
                    }
                    bucket.tail = Some(NonNull::from(waiter));
                    true
                });

                if is_waiting {
                    waiter.parker.park();
                }

                waiter.acquired.get()
            });

            if acquired {
                return;
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
        let force_fair = false;
        let address = &self.state as *const _ as usize;
        let waiter = Bucket::get(address).with(|bucket| unsafe {
            // find and dequeue a waiter with the same address
            let mut waiter = bucket.head;
            let mut waiter_next = None;
            while let Some(w) = waiter {
                if w.as_ref().address.get() == address {
                    let prev = w.as_ref().prev.get();
                    let next = w.as_ref().next.get();
                    waiter_next = next;
                    if let Some(p) = prev {
                        p.as_ref().next.set(next);
                    }
                    if let Some(n) = next {
                        n.as_ref().prev.set(prev);
                    }
                    if bucket.head == Some(w) {
                        bucket.head = next;
                    }
                    if bucket.tail == Some(w) {
                        bucket.tail = prev;
                    }
                    break;
                } else {
                    waiter = w.as_ref().next.get();
                }
            }

            let waiter = waiter.map(|w| &*w.as_ptr());
            if let Some(waiter) = waiter {
                let has_more = {
                    let mut has_more = false;
                    let mut current = waiter_next;
                    while let Some(c) = current {
                        if c.as_ref().address.get() == address {
                            has_more = true;
                            break;
                        } else {
                            current = c.as_ref().next.get();
                        }
                    }
                    has_more
                };

                // eventual fairness
                let be_fair = force_fair || {
                    let now = Instant::now();
                    now > bucket.timeout && {
                        bucket.prng ^= bucket.prng << 13;
                        bucket.prng ^= bucket.prng >> 17;
                        bucket.prng ^= bucket.prng << 5;
                        let nanos = bucket.prng % 1_000_000;
                        bucket.timeout = now + Duration::new(0, nanos);
                        true
                    }
                };

                if be_fair {
                    waiter.acquired.set(true);
                    if !has_more {
                        self.state.store(LOCKED, Ordering::Relaxed);
                    }
                } else if has_more {
                    self.state.store(PARKED, Ordering::Release);
                } else {
                    self.state.store(UNLOCKED, Ordering::Release);
                }
            } else {
                self.state.store(UNLOCKED, Ordering::Release);
            }

            waiter
        });

        if let Some(waiter) = waiter {
            waiter.parker.unpark();
        }
    }
}

struct Waiter {
    prev: Cell<Option<NonNull<Self>>>,
    next: Cell<Option<NonNull<Self>>>,
    address: Cell<usize>,
    parker: Parker,
    acquired: Cell<bool>,
}

impl Waiter {
    fn new() -> Self {
        Self {
            prev: Cell::new(None),
            next: Cell::new(None),
            address: Cell::new(0),
            parker: Parker::new(),
            acquired: Cell::new(false),
        }
    }

    #[inline(always)]
    fn with<T>(f: impl FnOnce(&Waiter) -> T) -> T {
        let mut stack_waiter = None;
        thread_local!(static WAITER: Waiter = Waiter::new());

        let waiter_ptr = WAITER
            .try_with(|x| x as *const Waiter)
            .unwrap_or_else(|_| stack_waiter.get_or_insert_with(Waiter::new));

        f(unsafe { &*waiter_ptr })
    }
}

type WordLock = super::word_lock_waking::Lock;

struct BucketInner {
    head: Option<NonNull<Waiter>>,
    tail: Option<NonNull<Waiter>>,
    timeout: Instant,
    prng: u32,
}

struct Bucket {
    lock: WordLock,
    inner: UnsafeCell<BucketInner>,
}

impl Bucket {
    fn new() -> Self {
        use super::Lock;
        Self {
            lock: WordLock::new(),
            inner: UnsafeCell::new(BucketInner {
                head: None,
                tail: None,
                timeout: Instant::now(),
                prng: 0xdeadbeef,
            }),
        }
    }

    fn with<T>(&self, f: impl FnOnce(&mut BucketInner) -> T) -> T {
        use super::Lock;
        let mut result = None;
        self.lock.with(|| {
            result = Some(f(unsafe { &mut *self.inner.get() }));
        });
        result.unwrap()
    }

    fn get(_address: usize) -> &'static Self {
        use std::{ptr::null_mut, sync::atomic::AtomicPtr};

        struct Init;

        impl Init {
            #[inline]
            fn ptr() -> &'static AtomicPtr<Bucket> {
                static PTR: AtomicPtr<Bucket> = AtomicPtr::new(null_mut());
                &PTR
            }

            #[inline]
            unsafe fn get() -> *mut Bucket {
                let bucket_ptr = Self::ptr().load(Ordering::Acquire);
                if bucket_ptr.is_null() {
                    Self::get_slow()
                } else {
                    bucket_ptr
                }
            }

            #[cold]
            unsafe fn get_slow() -> *mut Bucket {
                let bucket_ptr = Box::into_raw(Box::new(Bucket::new()));
                match Self::ptr().compare_exchange(
                    null_mut(),
                    bucket_ptr,
                    Ordering::AcqRel,
                    Ordering::Acquire,
                ) {
                    Ok(_) => bucket_ptr,
                    Err(new_bucket_ptr) => {
                        std::mem::drop(Box::from_raw(bucket_ptr));
                        new_bucket_ptr
                    }
                }
            }
        }

        unsafe { &*Init::get() }
    }
}
