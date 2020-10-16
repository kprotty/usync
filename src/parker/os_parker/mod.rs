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

use super::Parker;

#[cfg(windows)]
mod windows;
#[cfg(windows)]
use windows as os;

#[cfg(target_os = "linux")]
mod linux;
#[cfg(target_os = "linux")]
use linux as os;

#[cfg(all(unix, not(target_os = "linux")))]
mod posix;
#[cfg(all(unix, not(target_os = "linux")))]
use posix as os;

pub struct OsParker {
    parker: os::Parker,
}

unsafe impl Parker for OsParker {
    type Instant = OsInstant;

    fn now() -> Self::Instant {
        Self::Instant::now()
    }

    fn yield_now(iteration: Option<usize>) -> bool {
        let iteration = match iteration {
            Some(iteration) => iteration,
            None => {
                os::Parker::yield_now();
                return true;
            }
        };

        if iteration >= 10 {
            return false;
        }

        if iteration <= 3 {
            (0..(1 << iteration)).for_each(|_| spin_loop_hint());
        } else {
            os::Parker::yield_now();
        }

        true
    }

    fn new() -> Self {
        Self { parker: os::Parker::new() }
    }

    fn prepare(&self) {
        self.parker.prepare()
    }

    fn park(&self) {
        self.parker.park(None)
    }

    fn park_until(&self, deadline: Self::Instant) -> bool {
        self.parker.park(Some(deadline))
    }

    fn unpark(&self) {
        self.parker.unpark()
    }
}