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

use crate::{parker::Parker, utils::sync::spin_loop_hint};
use core::{
    convert::TryInto,
    fmt,
    ops::{Add, AddAssign, Sub, SubAssign},
    time::Duration,
};

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
        Self {
            parker: os::Parker::new(),
        }
    }

    fn prepare(&mut self) {
        self.parker.prepare()
    }

    fn park(&self) {
        self.parker.park(None);
    }

    fn park_until(&self, deadline: Self::Instant) -> bool {
        self.parker.park(Some(deadline))
    }

    unsafe fn unpark(&self) {
        self.parker.unpark()
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct OsInstant(u64);

impl fmt::Debug for OsInstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OsInstant").finish()
    }
}

impl OsInstant {
    pub fn now() -> Self {
        Self(Self::nanotime())
    }

    fn nanotime() -> u64 {
        let mut now = os::Clock::nanotime();
        if os::Clock::IS_ACTUALLY_MONOTONIC {
            return now;
        }

        #[cfg(target_pointer_width = "64")]
        {
            use crate::utils::sync::{AtomicUsize, Ordering};

            static LAST: AtomicUsize = AtomicUsize::new(0);

            let mut last = LAST.load(Ordering::Relaxed) as u64;
            loop {
                if last >= now {
                    now = last;
                    break;
                }
                match LAST.compare_exchange_weak(
                    last as usize,
                    now as usize,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => break,
                    Err(e) => last = e as u64,
                }
            }
        }

        #[cfg(not(target_pointer_width = "64"))]
        {
            use crate::{parker::DefaultParker, sync::Lock};

            static LAST: Lock<u64> = Lock::new(0);

            let mut last = LAST.lock::<DefaultParker>();
            if *last >= now {
                now = *last;
            } else {
                *last = now;
            }
        }

        now
    }

    pub fn duration_since(&self, earlier: Self) -> Duration {
        self.checked_duration_since(earlier)
            .expect("supplied instant is later than self")
    }

    pub fn checked_duration_since(&self, earlier: Self) -> Option<Duration> {
        self.checked_sub(Duration::from_nanos(earlier.0))
            .map(|instant| Duration::from_nanos(instant.0))
    }

    pub fn saturating_duration_since(&self, earlier: Self) -> Duration {
        self.checked_duration_since(earlier)
            .unwrap_or(Duration::new(0, 0))
    }

    pub fn elapsed(&self) -> Duration {
        Self::now().duration_since(*self)
    }

    pub fn checked_add(&self, duration: Duration) -> Option<Self> {
        Duration::from_nanos(self.0)
            .checked_add(duration)
            .and_then(|duration| duration.as_nanos().try_into().ok())
            .map(|nanos| Self(nanos))
    }

    pub fn checked_sub(&self, duration: Duration) -> Option<Self> {
        Duration::from_nanos(self.0)
            .checked_sub(duration)
            .and_then(|duration| duration.as_nanos().try_into().ok())
            .map(|nanos| Self(nanos))
    }
}

impl Add<Duration> for OsInstant {
    type Output = Self;

    fn add(self, duration: Duration) -> Self {
        self.checked_add(duration)
            .expect("overflowed when adding duration to instant")
    }
}

impl AddAssign<Duration> for OsInstant {
    fn add_assign(&mut self, duration: Duration) {
        *self = *self + duration;
    }
}

impl Sub<Self> for OsInstant {
    type Output = Duration;

    fn sub(self, other: Self) -> Duration {
        self.duration_since(other)
    }
}

impl Sub<Duration> for OsInstant {
    type Output = Self;

    fn sub(self, duration: Duration) -> Self {
        self.checked_sub(duration)
            .expect("overflowed when subtracting duration from instant")
    }
}

impl SubAssign<Duration> for OsInstant {
    fn sub_assign(&mut self, duration: Duration) {
        *self = *self - duration;
    }
}
