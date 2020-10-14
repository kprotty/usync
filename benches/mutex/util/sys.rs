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

#![allow(unused, non_camel_case_types)]

#[cfg(windows)]
pub use windows::*;

#[cfg(windows)]
mod windows {
    pub type SRWLOCK = usize;
    pub const SRWLOCK_INIT: SRWLOCK = 0;

    #[link(name = "kernel32")]
    extern "system" {
        pub fn AcquireSRWLockExclusive(p: *mut SRWLOCK);
        pub fn ReleaseSRWLockExclusive(p: *mut SRWLOCK);
        pub fn Sleep(dwMillisecond: u32);
        pub fn GetModuleHandleA(p: *const u8) -> usize;
        pub fn GetProcAddress(dll: usize, p: *const u8) -> usize;
        pub fn QueryPerformanceCounter(p: *mut u64) -> i32;
    }
}

#[cfg(target_os = "linux")]
pub use linux::*;

#[cfg(target_os = "linux")]
mod linux {
    #[cfg(target_arch = "x86_64")]
    pub const SYS_FUTEX: i32 = 202;
    #[cfg(target_arch = "x86")]
    pub const SYS_FUTEX: i32 = 240;
    #[cfg(target_arch = "aarch64")]
    pub const SYS_FUTEX: i32 = 98;

    pub const FUTEX_WAIT: i32 = 0;
    pub const FUTEX_WAKE: i32 = 1;
    pub const FUTEX_PRIVATE_FLAG: i32 = 128;

    #[link(name = "c")]
    extern "C" {
        pub fn syscall(num: i32, ...) -> i32;
    }
}

#[cfg(unix)]
pub use posix::*;

#[cfg(unix)]
mod posix {
    #[repr(C, align(16))]
    pub struct pthread_t(pub std::mem::MaybeUninit<[u8; 64]>);

    pub type pthread_mutex_t = pthread_t;
    pub type pthread_mutexattr_t = pthread_t;

    pub type pthread_cond_t = pthread_t;
    pub type pthread_condattr_t = pthread_t;

    #[link(name = "c")]
    extern "C" {
        pub fn pthread_mutex_init(m: *mut pthread_mutex_t, a: *const pthread_mutexattr_t) -> i32;
        pub fn pthread_mutex_lock(m: *mut pthread_mutex_t) -> i32;
        pub fn pthread_mutex_unlock(m: *mut pthread_mutex_t) -> i32;
        pub fn pthread_mutex_destroy(m: *mut pthread_mutex_t) -> i32;

        pub fn pthread_cond_init(c: *mut pthread_cond_t, a: *const pthread_condattr_t) -> i32;
        pub fn pthread_cond_wait(c: *mut pthread_cond_t, m: *mut pthread_mutex_t) -> i32;
        pub fn pthread_cond_signal(c: *mut pthread_cond_t) -> i32;
        pub fn pthread_cond_destroy(c: *mut pthread_cond_t) -> i32;
    }
}
