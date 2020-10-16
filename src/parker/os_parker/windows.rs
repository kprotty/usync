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
use crate::utils::sync::{AtomicBool, AtomicUsize, Ordering, FALSE, TRUE};
use core::{convert::TryInto, mem, ptr};

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
    assert_ne!(ntdll.is_null(), false, "failed to load ntdll.dll");

    let wait_fn = winapi::GetProcAddress(ntdll, b"NtWaitForKeyedEvent\x00".as_ptr());
    assert_ne!(
        wait_fn.is_null(),
        false,
        "failed to load NtWaitForKeyedEvent"
    );

    let wake_fn = winapi::GetProcAddress(ntdll, b"NtReleaseKeyedEvent\x00".as_ptr());
    assert_ne!(
        wake_fn.is_null(),
        false,
        "failed to load NtReleaseKeyedEvent"
    );

    WAIT_FN.store(wait_fn as usize, Ordering::Relaxed);
    WAKE_FN.store(wake_fn as usize, Ordering::Relaxed);
}

#[repr(align(4))]
pub(crate) struct Parker {
    is_parked: AtomicBool,
}

impl Parker {
    pub(crate) fn yield_now() {
        unsafe { winapi::Sleep(0) }
    }

    pub(crate) fn new() -> Self {
        Self {
            is_parked: AtomicBool::new(FALSE),
        }
    }

    pub(crate) fn prepare(&mut self) {
        self.is_parked = AtomicBool::new(TRUE);
    }

    pub(crate) fn park(&self, deadline: Option<Instant>) -> bool {
        let mut timeout: winapi::LARGE_INTEGER = 0;
        let mut timeout_ptr = ptr::null();

        if let Some(deadline) = deadline {
            let now = Instant::now();
            timeout_ptr = &timeout;
            timeout = if now > deadline {
                0
            } else {
                let ns: winapi::LARGE_INTEGER = (deadline - now)
                    .as_nanos()
                    .try_into()
                    .expect("deadline too long");
                // Windows works with units of 100ns.
                // A negative value indicates a relative timeout.
                -(ns / 100)
            }
        }

        unsafe {
            let NtWaitForKeyedEvent: NtKeyedEventFn = {
                let mut wait_fn = WAIT_FN.load(Ordering::Relaxed);
                if wait_fn == 0 {
                    load_keyed_event_fns();
                    wait_fn = WAIT_FN.load(Ordering::Relaxed);
                }
                mem::transmute(wait_fn)
            };

            match NtWaitForKeyedEvent(
                ptr::null(),
                &self.is_parked as *const _ as winapi::PVOID,
                winapi::FALSE,
                timeout_ptr,
            ) {
                winapi::STATUS_SUCCESS => {}
                winapi::STATUS_TIMEOUT => {
                    match self.is_parked.compare_exchange(
                        TRUE,
                        FALSE,
                        Ordering::Acquire,
                        Ordering::Acquire,
                    ) {
                        Ok(_) => return false,
                        Err(is_parked) => {
                            debug_assert_eq!(
                                is_parked, FALSE,
                                "invalid is_parked value on timeout",
                            );
                            assert_eq!(
                                NtWaitForKeyedEvent(
                                    ptr::null(),
                                    &self.is_parked as *const _ as winapi::PVOID,
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

            debug_assert_eq!(self.is_parked.load(Ordering::Relaxed), FALSE);
            true
        }
    }

    pub(crate) unsafe fn unpark(&self) {
        self.is_parked.store(FALSE, Ordering::Release);

        let NtReleaseKeyedEvent: NtKeyedEventFn = {
            let mut wake_fn = WAKE_FN.load(Ordering::Relaxed);
            if wake_fn == 0 {
                load_keyed_event_fns();
                wake_fn = WAKE_FN.load(Ordering::Relaxed);
            }
            mem::transmute(wake_fn)
        };

        assert_eq!(
            NtReleaseKeyedEvent(
                ptr::null(),
                &self.is_parked as *const _ as winapi::PVOID,
                winapi::FALSE,
                ptr::null(),
            ),
            winapi::STATUS_SUCCESS,
            "invalid NtReleaseKeyedEvent status",
        );
    }
}

#[allow(non_camel_case_types)]
mod winapi {
    pub type DWORD = u32;
    pub type NTSTATUS = DWORD;
    pub type BOOLEAN = i32;
    pub type PVOID = *const ();
    pub type HANDLE = PVOID;
    pub type HMODULE = HANDLE;
    pub type LARGE_INTEGER = i64;

    pub const TRUE: BOOLEAN = 1;
    pub const FALSE: BOOLEAN = 0;
    pub const STATUS_SUCCESS: NTSTATUS = 0x00000000;
    pub const STATUS_TIMEOUT: NTSTATUS = 0x00000102;

    #[link(name = "kernel32")]
    extern "system" {
        pub fn Sleep(dwMilliseconds: DWORD);
        pub fn GetModuleHandleA(dll: *const u8) -> HMODULE;
        pub fn GetProcAddress(dll: HMODULE, name: *const u8) -> HANDLE;
    }
}
