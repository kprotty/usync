use core::{
    marker::PhantomData,
    ops::{Add, AddAssign, Sub, SubAssign},
    time::Duration,
};

pub trait InstantClock {
    fn nanotime() -> u64;

    fn is_monotonic() -> bool;
}

#[derive(Debug, Default, Hash)]
pub struct Instant<C: InstantClock> {
    timestamp: u64,
    _clock: PhantomData<C>,
}

impl<C: InstantClock> Clone for Instant<C> {
    fn clone(&self) -> Self {
        Self {
            timestamp: self.timestamp,
            _clock: self._clock,
        }
    }
}

impl<C: InstantClock> PartialEq for Instant<C> {
    fn eq(&self, instant: &Self) -> bool {
        self.timestamp == instant.timestamp
    }
}

impl<C: InstantClock> PartialOrd for Instant<C> {
    fn partial_cmp(&self, instant: &Self) -> Option<core::cmp::Ordering> {
        Some(self.timestamp.cmp(&instant.timestamp))
    }
}

impl<C: InstantClock> super::Instant for Instant<C> {
    fn now() -> Self {
        Self {
            timestamp: Self::nanotime(),
            _clock: PhantomData,
        }
    }
}

impl<C: InstantClock> Instant<C> {
    fn nanotime() -> u64 {
        let mut timestamp = C::nanotime();

        if !C::is_monotonic() {
            #[cfg(not(target_pointer_width = "64"))]
            {
                use super::Lock;
                static mut PREV: u64 = 0;
                static LOCK: super::default::Lock = super::default::Lock::new();

                LOCK.with(|| unsafe {
                    if PREV < timestamp {
                        PREV = timestamp;
                    } else {
                        timestamp = PREV;
                    }
                });
            }

            #[cfg(target_pointer_width = "64")]
            {
                use core::sync::atomic::{AtomicU64, Ordering};
                static PREV: AtomicU64 = AtomicU64::new(0);

                let mut prev = PREV.load(Ordering::Relaxed);
                loop {
                    if timestamp < prev {
                        return prev;
                    }
                    match PREV.compare_exchange_weak(
                        prev,
                        timestamp,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return timestamp,
                        Err(e) => prev = e,
                    }
                }
            }
        }

        timestamp
    }

    pub fn elapsed(&self) -> Duration {
        use super::Instant;
        Self::now() - *self
    }

    pub fn duration_since(&self, earlier: Self) -> Duration {
        self.checked_duration_since(earlier)
            .expect("supplied instant is later than self")
    }

    pub fn saturating_duration_since(&self, earlier: Self) -> Duration {
        self.checked_duration_since(earlier)
            .unwrap_or(Duration::new(0, 0))
    }

    pub fn checked_duration_since(&self, earlier: Self) -> Option<Duration> {
        self.as_duration().checked_sub(earlier.as_duration())
    }

    pub fn checked_add(&self, duration: Duration) -> Option<Self> {
        self.as_duration()
            .checked_add(duration)
            .and_then(Self::from_duration)
    }

    pub fn checked_sub(&self, duration: Duration) -> Option<Self> {
        self.as_duration()
            .checked_sub(duration)
            .and_then(Self::from_duration)
    }

    fn as_duration(&self) -> Duration {
        Duration::from_nanos(self.timestamp)
    }

    fn from_duration(duration: Duration) -> Option<Self> {
        use std::convert::TryInto;
        duration.as_nanos().try_into().ok().map(|timestamp| Self {
            timestamp,
            _clock: PhantomData,
        })
    }
}

impl<C: InstantClock> Add<Duration> for Instant<C> {
    type Output = Self;

    fn add(self, duration: Duration) -> Self {
        self.checked_add(duration)
            .expect("overflow when adding duration to instant")
    }
}

impl<C: InstantClock> AddAssign<Duration> for Instant<C> {
    fn add_assign(&mut self, duration: Duration) {
        *self = *self + duration;
    }
}

impl<C: InstantClock> SubAssign<Duration> for Instant<C> {
    fn sub_assign(&mut self, duration: Duration) {
        *self = *self - duration;
    }
}

impl<C: InstantClock> Sub<Duration> for Instant<C> {
    type Output = Self;

    fn sub(self, duration: Duration) -> Self::Output {
        self.checked_sub(duration)
            .expect("overflow when subtracting duration from instant")
    }
}

impl<C: InstantClock> Sub<Self> for Instant<C> {
    type Output = Duration;

    fn sub(self, instant: Self) -> Self::Output {
        self.duration_since(instant)
    }
}
