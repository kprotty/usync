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

use crate::utils::sync::{AtomicUsize, Ordering};
use super::OsInstant as Instant;
use core::{
    ptr,
    mem,
    convert::TryInto,
};

#[repr(usize)]
#[derive(Copy, Clone, Debug)]
enum State {
    Empty = 0,
    Waiting = 1,
    Notified = 2,
}

impl From<usize> for State {
    fn from(value: usize) -> Self {
        match value {
            0 => Self::Empty,
            1 => Self::Waiting,
            2 => Self::Notified,
            _ => unreachable!("invalid State value {:?}", value),
        }
    }
}

type DWORD = u32;
type NTSTATUS = DWORD;
type BOOLEAN = i32;
type PVOID = *const ();
type HANDLE = PVOID;
type HMODULE = HANDLE;
type LARGE_INTEGER = i64;

const TRUE: BOOLEAN = 1;
const FALSE: BOOLEAN = 0;
const STATUS_SUCCESS: NTSTATUS = 0x00000000;
const STATUS_TIMEOUT: NTSTATUS = 0x00000102;

type NtKeyedEventFn = extern "system" fn(
    handle: HANDLE,
    key: PVOID,
    alertable: BOOLEAN,
    timeout: *const LARGE_INTEGER,
) NTSTATUS;

#[link(name = "kernel32")]
extern "system" {
    fn Sleep(dwMilliseconds: DWORD);
    fn GetModuleHandleA(dll: *const u8) -> HMODULE;
    fn GetProcAddress(dll: HMODULE, name: *const u8) -> usize;
}

static WAIT_FN: AtomicUsize = AtomicUsize::new(0);
static WAKE_FN: AtomicUsize = AtomicUsize::new(0);

unsafe fn load_fn() {

}

#[repr(align(4))]
pub(crate) struct Parker {
    state: AtomicUsize,
}

impl Parker {
    pub(crate) fn yield_now() {
        unsafe { Sleep(0) }
    }

    pub(crate) fn new() -> Self {
        Self {
            state: AtomicUsize::new(State::Empty as usize),
        }
    }

    pub(crate) fn prepare(&self) {}

    pub(crate) fn park(&self, deadline: Option<Instant>) -> bool {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            match State::from(state) {
                State::Empty => match self.state.compare_exchange_weak(
                    State::Empty as usize,
                    State::Waiting as usize,
                    Ordering::Acquire,
                    Ordering::Acquire,
                ) {
                    Ok(_) => return self.wait(None),
                    Err(e) => state = e,
                },
                State::Waiting => {
                    unreachable!("multiple threads parked on the same OsParker");
                },
                State::Notified => {
                    self.state.store(State::Empty as usize, Ordering::Relaxed);
                    return true;
                },
            }
        }
    }

    pub(crate) fn unpark(&self) -> bool {
        let mut state = self.state.load(Ordering::Acquire);
        loop {
            match State::from(state) {
                State::Empty => match self.state.compare_exchange_weak(
                    State::Empty as usize,
                    State::Waiting as usize,
                    Ordering::Acquire,
                    Ordering::Acquire,
                ) {
                    Ok(_) => return self.wait(None),
                    Err(e) => state = e,
                },
                State::Waiting => {
                    unreachable!("multiple threads parked on the same OsParker");
                },
                State::Notified => {
                    self.state.store(State::Empty as usize, Ordering::Relaxed);
                    return true;
                },
            }
        }
    }

    #[cold]
    fn wait(&self, deadline: Option<Instant>) -> bool {
        let mut timeout: LARGE_INTEGER = 0;
        let mut timeout_ptr = ptr::null();

        if let Some(deadline) = deadline {
            let now = Instant::now();
            if now > deadline {
                return false;
            } else {
                let ns: LARGE_INTEGER = (deadline - now)
                    .as_nanos()
                    .try_into()
                    .expect("deadline too long");
                timeout = -(ns / 100);
                timeout_ptr = &timeout;
            }
        }

        unsafe {
            let wait_fn: NtKeyedEventFn = {
                let mut wait_fn = WAIT_FN.load(Ordering::Relaxed);
                if wait_fn == 0 {
                    load_fn();
                    wait_fn = WAIT_FN.load(Ordering::Relaxed);
                }
                transmute(wait_fn)
            };

            match wait_fn(
                ptr::null(),
                &self.state as *const _ as PVOID,
                FALSE,
                timeout_ptr,
            ) {
                STATUS_TIMEOUT => {},
                STATUS_SUCCESS => return true,
                status => unreachable!("NtWaitForKeyedEvent: {:x?}", status),
            }

            match self.state.compare_exchange(
                State::Waiting as usize,
                State::Empty as usize,
                Ordering::Acquire,
                Ordering::Acquire,
            ) {
                Ok(_) => return false,
                Err(e) => assert_eq!(State::from(e), State::Empty),
            }

            match wait_fn(
                ptr::null(),
                &self.state as *const _ as PVOID,
                FALSE,
                ptr::null(),
            ) {
                STATUS_SUCCESS => return true,
                status => unreachable!("NtWaitForKeyedEvent: {:x?}", status),
            }
        }
    }
}