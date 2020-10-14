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

use super::util::SpinWait;
use std::sync::atomic::{AtomicI32, Ordering};

pub trait Futex: Send + Sync + 'static {
    const LOCK_NAME: &'static str;

    fn new() -> Self;

    unsafe fn wait(&self, ptr: &AtomicI32, cmp: i32);

    unsafe fn wake(&self, ptr: &AtomicI32);
}

const UNLOCKED: i32 = 0;
const LOCKED: i32 = 1;
const PARKED: i32 = 2;

pub struct FutexLock<F: Futex> {
    state: AtomicI32,
    futex: F,
}

unsafe impl<F: Futex> super::Lock for FutexLock<F> {
    const NAME: &'static str = F::LOCK_NAME;

    fn new() -> Self {
        Self {
            state: AtomicI32::new(UNLOCKED),
            futex: F::new(),
        }
    }

    fn with(&self, f: impl FnOnce()) {
        self.acquire();
        f();
        self.release();
    }
}

impl<F: Futex> FutexLock<F> {
    #[inline]
    pub fn acquire(&self) {
        let state = self.state.swap(LOCKED, Ordering::Acquire);
        if state != UNLOCKED {
            self.acquire_slow(state);
        }
    }

    #[cold]
    fn acquire_slow(&self, mut acquire_state: i32) {
        loop {
            let mut spin = SpinWait::new();
            loop {
                let state = self.state.load(Ordering::Relaxed);
                if state == UNLOCKED {
                    if self
                        .state
                        .compare_exchange_weak(
                            state,
                            acquire_state,
                            Ordering::Acquire,
                            Ordering::Relaxed,
                        )
                        .is_ok()
                    {
                        return;
                    }
                }
                if !spin.yield_now() {
                    break;
                }
            }

            let state = self.state.swap(PARKED, Ordering::Acquire);
            if state == UNLOCKED {
                return;
            }

            acquire_state = PARKED;
            unsafe { self.futex.wait(&self.state, PARKED) };
        }
    }

    #[inline]
    pub fn release(&self) {
        let state = self.state.swap(UNLOCKED, Ordering::Release);
        if state == PARKED {
            self.release_slow();
        }
    }

    #[cold]
    fn release_slow(&self) {
        unsafe { self.futex.wake(&self.state) };
    }
}

#[cfg(windows)]
#[allow(dead_code)]
pub type OsFutex = windows::Futex;

#[cfg(target_os = "linux")]
#[allow(dead_code)]
pub type OsFutex = linux::Futex;

#[cfg(not(any(windows, target_os = "linux")))]
#[allow(dead_code)]
pub type OsFutex = generic::Futex;

#[cfg(windows)]
pub mod windows {
    use super::super::util::sys;
    use std::{
        mem::transmute,
        sync::atomic::{AtomicI32, AtomicUsize, Ordering},
    };

    static WAIT_FN: AtomicUsize = AtomicUsize::new(0);
    static WAKE_FN: AtomicUsize = AtomicUsize::new(0);

    type WaitOnAddressFn = extern "system" fn(usize, usize, usize, u32) -> u32;
    type WakeByAddressSingleFn = extern "system" fn(usize);

    pub struct Futex;

    impl super::Futex for Futex {
        const LOCK_NAME: &'static str = "futex_windows";

        fn new() -> Self {
            Self {}
        }

        unsafe fn wait(&self, ptr: &AtomicI32, cmp: i32) {
            let mut wait_fn_ptr = WAIT_FN.load(Ordering::Relaxed);
            if wait_fn_ptr == 0 {
                Self::load_fn_ptr();
                wait_fn_ptr = WAIT_FN.load(Ordering::Relaxed);
            }

            let wait_fn: WaitOnAddressFn = transmute(wait_fn_ptr);
            let _ = wait_fn(
                ptr as *const _ as usize,
                &cmp as *const _ as usize,
                std::mem::size_of::<i32>(),
                !0u32,
            );
        }

        unsafe fn wake(&self, ptr: &AtomicI32) {
            let mut wake_fn_ptr = WAKE_FN.load(Ordering::Relaxed);
            if wake_fn_ptr == 0 {
                Self::load_fn_ptr();
                wake_fn_ptr = WAKE_FN.load(Ordering::Relaxed);
            }
            let wake_fn: WakeByAddressSingleFn = transmute(wake_fn_ptr);
            let _ = wake_fn(ptr as *const _ as usize);
        }
    }

    impl Futex {
        #[cold]
        unsafe fn load_fn_ptr() {
            let dll = sys::GetModuleHandleA(b"api-ms-win-core-synch-l1-2-0.dll\0".as_ptr());
            assert_ne!(dll, 0, "failed to load ntdll.dll");

            let wait_fn = sys::GetProcAddress(dll, b"WaitOnAddress\0".as_ptr());
            assert_ne!(wait_fn, 0, "failed to load WaitOnAddress");

            let wake_fn = sys::GetProcAddress(dll, b"WakeByAddressSingle\0".as_ptr());
            assert_ne!(wake_fn, 0, "failed to load WakeByAddressSingle");

            WAIT_FN.store(wait_fn, Ordering::Relaxed);
            WAKE_FN.store(wake_fn, Ordering::Relaxed);
        }
    }
}

#[cfg(target_os = "linux")]
pub mod linux {
    use super::super::util::sys;
    use std::sync::atomic::AtomicI32;

    pub struct Futex;

    impl super::Futex for Futex {
        const LOCK_NAME: &'static str = "futex_linux";

        fn new() -> Self {
            Self {}
        }

        unsafe fn wait(&self, ptr: &AtomicI32, cmp: i32) {
            let _ = sys::syscall(
                sys::SYS_FUTEX,
                ptr as *const _ as usize,
                sys::FUTEX_PRIVATE_FLAG | sys::FUTEX_WAIT,
                cmp,
                0usize,
            );
        }

        unsafe fn wake(&self, ptr: &AtomicI32) {
            let _ = sys::syscall(
                sys::SYS_FUTEX,
                ptr as *const _ as usize,
                sys::FUTEX_PRIVATE_FLAG | sys::FUTEX_WAKE,
                1i32,
            );
        }
    }
}

pub mod generic {
    use super::super::util::Parker;
    use std::{
        cell::{Cell, UnsafeCell},
        ptr::NonNull,
        sync::atomic::{AtomicI32, Ordering},
    };

    type InnerLock = super::super::word_lock_waking::Lock;

    struct Waiter {
        next: Cell<Option<NonNull<Self>>>,
        tail: Cell<NonNull<Self>>,
        parker: Parker,
    }

    pub struct Futex {
        lock: InnerLock,
        queue: UnsafeCell<Option<NonNull<Waiter>>>,
    }

    unsafe impl Send for Futex {}
    unsafe impl Sync for Futex {}

    impl Futex {
        fn with_queue<T>(&self, f: impl FnOnce(&mut Option<NonNull<Waiter>>) -> T) -> T {
            use super::super::Lock;
            let mut result = None;
            self.lock
                .with(|| result = Some(f(unsafe { &mut *self.queue.get() })));
            result.unwrap()
        }
    }

    impl super::Futex for Futex {
        const LOCK_NAME: &'static str = "futex_generic";

        fn new() -> Self {
            use super::super::Lock;
            Self {
                lock: InnerLock::new(),
                queue: UnsafeCell::new(None),
            }
        }

        unsafe fn wait(&self, ptr: &AtomicI32, cmp: i32) {
            let mut waiter = None;

            self.with_queue(|queue| {
                if ptr.load(Ordering::Acquire) != cmp {
                    return;
                }

                waiter = Some(Waiter {
                    next: Cell::new(None),
                    tail: Cell::new(NonNull::dangling()),
                    parker: Parker::new(),
                });

                let waiter_ref = waiter.as_ref().unwrap();
                if let Some(head) = *queue {
                    let tail = head.as_ref().tail.replace(NonNull::from(waiter_ref));
                    tail.as_ref().next.set(Some(NonNull::from(waiter_ref)));
                } else {
                    waiter_ref.tail.set(NonNull::from(waiter_ref));
                    *queue = Some(NonNull::from(waiter_ref));
                }
            });

            if let Some(waiter_ref) = waiter.as_ref() {
                waiter_ref.parker.park();
            }
        }

        unsafe fn wake(&self, _ptr: &AtomicI32) {
            if let Some(waiter) = self.with_queue(|queue| {
                (*queue).map(|head| {
                    *queue = head.as_ref().next.get();
                    if let Some(next) = *queue {
                        next.as_ref().tail.set(head.as_ref().tail.get());
                    }
                    &*head.as_ptr()
                })
            }) {
                waiter.parker.unpark();
            }
        }
    }
}
