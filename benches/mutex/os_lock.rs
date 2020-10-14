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
pub use windows::Lock;

#[cfg(windows)]
mod windows {
    use super::super::util::sys;
    use std::cell::UnsafeCell;

    pub struct Lock(UnsafeCell<sys::SRWLOCK>);

    unsafe impl Send for Lock {}
    unsafe impl Sync for Lock {}

    unsafe impl super::super::Lock for Lock {
        const NAME: &'static str = "SRWLOCK";

        fn new() -> Self {
            Self(UnsafeCell::new(sys::SRWLOCK_INIT))
        }

        fn with(&self, f: impl FnOnce()) {
            unsafe {
                sys::AcquireSRWLockExclusive(self.0.get());
                f();
                sys::ReleaseSRWLockExclusive(self.0.get());
            }
        }
    }
}

#[cfg(unix)]
pub use posix::Lock;

#[cfg(unix)]
mod posix {
    use super::super::util::sys;
    use std::cell::UnsafeCell;

    pub struct Lock(Box<UnsafeCell<sys::pthread_mutex_t>>);

    unsafe impl Send for Lock {}
    unsafe impl Sync for Lock {}

    impl Drop for Lock {
        fn drop(&mut self) {
            unsafe {
                let _ = sys::pthread_mutex_destroy(self.0.get());
            }
        }
    }

    unsafe impl super::super::Lock for Lock {
        const NAME: &'static str = "pthread_mutex_t";

        fn new() -> Self {
            Self(unsafe {
                let mutex = sys::pthread_t(std::mem::MaybeUninit::uninit());
                let mutex = Box::new(UnsafeCell::new(mutex));
                let _ = sys::pthread_mutex_init(mutex.get(), std::ptr::null());
                mutex
            })
        }

        fn with(&self, f: impl FnOnce()) {
            unsafe {
                let _ = sys::pthread_mutex_lock(self.0.get());
                f();
                let _ = sys::pthread_mutex_unlock(self.0.get());
            }
        }
    }
}
