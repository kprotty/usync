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

#[cfg(windows)]
pub use windows::Parker;

#[cfg(windows)]
mod windows {
    use super::super::sys;
    use std::{
        mem::transmute,
        sync::atomic::{AtomicU32, AtomicUsize, Ordering},
    };

    static WAIT_FN: AtomicUsize = AtomicUsize::new(0);
    static WAKE_FN: AtomicUsize = AtomicUsize::new(0);
    type KeyedEventFn = extern "system" fn(usize, usize, u32, usize) -> u32;

    pub struct Parker(AtomicU32);

    impl Parker {
        pub const IS_CHEAP_TO_CONSTRUCT: bool = true;

        pub fn new() -> Self {
            Self(AtomicU32::new(0))
        }

        #[inline]
        pub fn prepare(&self) {
            self.0.store(0, Ordering::Relaxed);
        }

        #[inline]
        pub fn park(&self) {
            if self.0.swap(1, Ordering::Acquire) == 0 {
                unsafe { self.park_slow() };
            }
        }

        #[inline]
        pub fn unpark(&self) {
            if self.0.swap(1, Ordering::Release) != 0 {
                unsafe { self.unpark_slow() };
            }
        }

        #[cold]
        unsafe fn park_slow(&self) {
            let mut wait_fn_ptr = WAIT_FN.load(Ordering::Relaxed);
            if wait_fn_ptr == 0 {
                Self::load_fn_ptr();
                wait_fn_ptr = WAIT_FN.load(Ordering::Relaxed);
            }
            let wait_fn: KeyedEventFn = transmute(wait_fn_ptr);
            let _ = wait_fn(0, &self.0 as *const _ as usize, 0, 0);
        }

        #[cold]
        unsafe fn unpark_slow(&self) {
            let mut wake_fn_ptr = WAKE_FN.load(Ordering::Relaxed);
            if wake_fn_ptr == 0 {
                Self::load_fn_ptr();
                wake_fn_ptr = WAKE_FN.load(Ordering::Relaxed);
            }
            let wake_fn: KeyedEventFn = transmute(wake_fn_ptr);
            let _ = wake_fn(0, &self.0 as *const _ as usize, 0, 0);
        }

        #[cold]
        unsafe fn load_fn_ptr() {
            let dll = sys::GetModuleHandleA(b"ntdll.dll\0".as_ptr());
            assert_ne!(dll, 0, "failed to load ntdll.dll");

            let wait_fn = sys::GetProcAddress(dll, b"NtWaitForKeyedEvent\0".as_ptr());
            assert_ne!(wait_fn, 0, "failed to load NtWaitForKeyedEvent");

            let wake_fn = sys::GetProcAddress(dll, b"NtReleaseKeyedEvent\0".as_ptr());
            assert_ne!(wake_fn, 0, "failed to load NtReleaseKeyedEvent");

            WAIT_FN.store(wait_fn, Ordering::Relaxed);
            WAKE_FN.store(wake_fn, Ordering::Relaxed);
        }
    }
}

#[cfg(target_os = "linux")]
pub use linux::Parker;

#[cfg(target_os = "linux")]
mod linux {
    use super::super::super::futex_lock::{linux, Futex};
    use std::sync::atomic::{AtomicI32, Ordering};

    pub struct Parker {
        state: AtomicI32,
        futex: linux::Futex,
    }

    impl Parker {
        pub const IS_CHEAP_TO_CONSTRUCT: bool = true;

        pub fn new() -> Self {
            Self {
                state: AtomicI32::new(0),
                futex: linux::Futex::new(),
            }
        }

        pub fn prepare(&self) {
            self.state.store(0, Ordering::Relaxed);
        }

        pub fn park(&self) {
            while self.state.load(Ordering::Acquire) == 0 {
                unsafe { self.futex.wait(&self.state, 0) };
            }
        }

        pub fn unpark(&self) {
            self.state.store(1, Ordering::Release);
            unsafe { self.futex.wake(&self.state) };
        }
    }
}

#[cfg(all(unix, not(target_os = "linux")))]
pub use posix::Parker;

#[cfg(all(unix, not(target_os = "linux")))]
mod posix {
    use std::{
        sync::atomic::{AtomicBool, Ordering},
        thread,
    };

    pub struct Parker {
        notified: AtomicBool,
        thread: thread::Thread,
    }

    impl Parker {
        pub const IS_CHEAP_TO_CONSTRUCT: bool = false;

        pub fn new() -> Self {
            Self {
                notified: AtomicBool::new(false),
                thread: thread::current(),
            }
        }

        pub fn prepare(&self) {
            self.notified.store(false, Ordering::Relaxed);
        }

        pub fn park(&self) {
            while !self.notified.load(Ordering::Acquire) {
                thread::park();
            }
        }

        pub fn unpark(&self) {
            let thread = self.thread.clone();
            self.notified.store(true, Ordering::Release);
            thread.unpark();
        }
    }
}
