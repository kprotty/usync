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

#[cfg(not(windows))]
pub use std::time::Instant;

#[cfg(windows)]
pub use windows::Instant;

#[cfg(windows)]
mod windows {
    use super::super::sys;
    use std::{convert::TryInto, ops::Add, time::Duration};

    #[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
    pub struct Instant(u64);

    impl Instant {
        pub fn now() -> Self {
            let mut counter = 0u64;
            let _ = unsafe { sys::QueryPerformanceCounter(&mut counter) };
            Self(counter)
        }
    }

    impl Add<Duration> for Instant {
        type Output = Self;

        fn add(self, duration: Duration) -> Self {
            let nanos: u64 = duration.as_nanos().try_into().unwrap();
            Self(self.0 + nanos)
        }
    }
}
