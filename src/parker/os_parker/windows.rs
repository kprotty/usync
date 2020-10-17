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

use super::OsInstant as Instant;
use crate::utils::sync::{AtomicInt, Int, AtomicUsize, Ordering};
use core::{cell::Cell, convert::TryInto, fmt, mem, ptr};

static WAIT_FN: AtomicUsize = AtomicUsize::new(0);
static WAKE_FN: AtomicUsize = AtomicUsize::new(0);

type NtKeyedEventFn = extern "system" fn(
    handle: winapi::HANDLE,
    key: winapi::PVOID,
    alertable: winapi::BOOLEAN,
    timeout: *const winapi::LARGE_INTEGER,
) -> winapi::NTSTATUS;

#[cold]
unsafe fn load_keyed_event_fns() {
    let ntdll = winapi::GetModuleHandleA(b"ntdll.dll\x00".as_ptr());
    assert_eq!(ntdll.is_null(), false, "failed to load ntdll.dll");

    let wait_fn = winapi::GetProcAddress(ntdll, b"NtWaitForKeyedEvent\x00".as_ptr());
    assert_eq!(
        wait_fn.is_null(),
        false,
        "failed to load NtWaitForKeyedEvent"
    );

    let wake_fn = winapi::GetProcAddress(ntdll, b"NtReleaseKeyedEvent\x00".as_ptr());
    assert_eq!(
        wake_fn.is_null(),
        false,
        "failed to load NtReleaseKeyedEvent"
    );

    WAIT_FN.store(wait_fn as usize, Ordering::Relaxed);
    WAKE_FN.store(wake_fn as usize, Ordering::Relaxed);
}

const EMPTY: Int = 0;
const WAITING: Int = 1;
const NOTIFIED: Int = 2;

#[repr(align(4))]
pub(crate) struct Parker {
    state: AtomicInt,
}

impl fmt::Debug for Parker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OsParker").finish()
    }
}

impl Parker {
    pub(crate) fn yield_now() {
        unsafe { winapi::Sleep(0) }
    }

    pub(crate) fn new() -> Self {
        Self {
            state: AtomicInt::new(EMPTY),
        }
    }

    pub(crate) fn prepare(&mut self) {}

    #[inline]
    pub(crate) fn park(&self, deadline: Option<Instant>) -> bool {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            match state {
                EMPTY => match self.state.compare_exchange_weak(
                    state,
                    WAITING,
                    Ordering::Acquire,
                    Ordering::Acquire,
                ) {
                    Ok(_) => return self.wait(deadline),
                    Err(e) => state = e,
                },
                WAITING => {
                    unreachable!("multiple threads parking on the same OsParker");
                }
                NOTIFIED => {
                    self.state.store(EMPTY, Ordering::Relaxed);
                    return true;
                }
                _ => {
                    unreachable!("invalid OsParker state {:?}", state);
                }
            }
        }
    }

    #[cold]
    fn wait(&self, deadline: Option<Instant>) -> bool {
        let timeout = Cell::new(0);
        let mut timeout_ptr = ptr::null();

        if let Some(deadline) = deadline {
            let now = Instant::now();
            timeout_ptr = timeout.as_ptr();
            timeout.set(if now > deadline {
                0
            } else {
                let ns: winapi::LARGE_INTEGER = (deadline - now)
                    .as_nanos()
                    .try_into()
                    .expect("deadline too long");
                // Windows works with units of 100ns.
                // A negative value indicates a relative timeout.
                -(ns / 100)
            })
        }

        unsafe {
            #[allow(non_snake_case)]
            let NtWaitForKeyedEvent: NtKeyedEventFn = {
                let mut wait_fn = WAIT_FN.load(AtomicUsizeOrdering::Relaxed);
                if wait_fn == 0 {
                    load_keyed_event_fns();
                    wait_fn = WAIT_FN.load(AtomicUsizeOrdering::Relaxed);
                }
                mem::transmute(wait_fn)
            };

            match NtWaitForKeyedEvent(
                ptr::null(),
                &self.state as *const _ as winapi::PVOID,
                winapi::FALSE,
                timeout_ptr,
            ) {
                winapi::STATUS_SUCCESS => {}
                winapi::STATUS_TIMEOUT => {
                    match self.state.compare_exchange(
                        WAITING,
                        EMPTY,
                        Ordering::Acquire,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => return false,
                        Err(state) => {
                            debug_assert_eq!(state, EMPTY, "invalid OsParker state on timeout",);
                            assert_eq!(
                                NtWaitForKeyedEvent(
                                    ptr::null(),
                                    &self.state as *const _ as winapi::PVOID,
                                    winapi::FALSE,
                                    ptr::null(),
                                ),
                                winapi::STATUS_SUCCESS,
                                "invalid NtWaitForKeyedEvent timeout status",
                            );
                        }
                    }
                }
                status => {
                    unreachable!("invalid NtWaitForKeyedEvent status: {:x?}", status);
                }
            }

            true
        }
    }

    pub(crate) unsafe fn unpark(&self) {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            match state {
                EMPTY => match self.state.compare_exchange_weak(
                    state,
                    NOTIFIED,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(e) => state = e,
                },
                WAITING => match self.state.compare_exchange_weak(
                    state,
                    EMPTY,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return self.notify(),
                    Err(e) => state = e,
                },
                NOTIFIED => {
                    unreachable!("OsParker unparked when already unparked");
                }
                _ => {
                    unreachable!("invalid OsParker state {:?}", state);
                }
            }
        }
    }

    #[cold]
    unsafe fn notify(&self) {
        #[allow(non_snake_case)]
        let NtReleaseKeyedEvent: NtKeyedEventFn = {
            let mut wake_fn = WAKE_FN.load(AtomicUsizeOrdering::Relaxed);
            if wake_fn == 0 {
                load_keyed_event_fns();
                wake_fn = WAKE_FN.load(AtomicUsizeOrdering::Relaxed);
            }
            mem::transmute(wake_fn)
        };

        assert_eq!(
            NtReleaseKeyedEvent(
                ptr::null(),
                &self.state as *const _ as winapi::PVOID,
                winapi::FALSE,
                ptr::null(),
            ),
            winapi::STATUS_SUCCESS,
            "invalid NtReleaseKeyedEvent status",
        );
    }
}

pub(crate) mod clock {
    use super::winapi;
    use core::{
        mem::{transmute, MaybeUninit},
        ops::Div,
    };

    pub(crate) type Frequency = u64;

    #[cold]
    pub(crate) fn frequency() -> Frequency {
        unsafe {
            let mut frequency = MaybeUninit::uninit();
            let status = winapi::QueryPerformanceFrequency(frequency.as_mut_ptr());
            debug_assert_eq!(status, winapi::TRUE);
            transmute(frequency.assume_init())
        }
    }

    pub(crate) const IS_ACTUALLY_MONOTONIC: bool = false;

    pub(crate) fn nanotime(frequency: Frequency) -> u64 {
        let counter: u64 = unsafe {
            let mut counter = MaybeUninit::uninit();
            let status = winapi::QueryPerformanceCounter(counter.as_mut_ptr());
            debug_assert_eq!(status, winapi::TRUE);
            transmute(counter.assume_init())
        };

        counter.wrapping_mul(1_000_000_000).div(frequency).div(100)
    }
}

#[allow(non_camel_case_types)]
mod winapi {
    pub(crate) type DWORD = u32;
    pub(crate) type NTSTATUS = DWORD;
    pub(crate) type BOOLEAN = i32;
    pub(crate) type PVOID = *const u8;
    pub(crate) type HANDLE = PVOID;
    pub(crate) type HMODULE = HANDLE;
    pub(crate) type LARGE_INTEGER = i64;

    pub(crate) const TRUE: BOOLEAN = 1;
    pub(crate) const FALSE: BOOLEAN = 0;
    pub(crate) const STATUS_SUCCESS: NTSTATUS = 0x00000000;
    pub(crate) const STATUS_TIMEOUT: NTSTATUS = 0x00000102;

    #[link(name = "kernel32")]
    extern "system" {
        pub(crate) fn Sleep(dwMilliseconds: DWORD);
        pub(crate) fn QueryPerformanceCounter(counter: *mut LARGE_INTEGER) -> BOOLEAN;
        pub(crate) fn QueryPerformanceFrequency(frequency: *mut LARGE_INTEGER) -> BOOLEAN;
        pub(crate) fn GetModuleHandleA(dll: *const u8) -> HMODULE;
        pub(crate) fn GetProcAddress(dll: HMODULE, name: *const u8) -> HANDLE;
    }
}
