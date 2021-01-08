
use core::{
    ops::{Add, Sub},
    pin::Pin,
    sync::atomic::{spin_loop_hint, AtomicBool, Ordering},
    time::Duration,
};

pub struct Platform;

impl super::Platform for Platform {
    type Lock = Lock;
    type Parker = Parker;
}

#[derive(Default, Debug)]
pub struct Lock {
    is_locked: AtomicBool,
}

impl Lock {
    pub const fn new() -> Self {
        Self {
            is_locked: AtomicBool::new(false),
        }
    }

    #[inline]
    pub fn try_lock(&self) -> Option<LockGuard<'_>> {
        match self.is_locked.swap(true, Ordering::Acquire) {
            false => Some(LockGuard { lock: self }),
            _ => None,
        }
    }

    pub fn lock(&self) -> LockGuard<'_> {
        loop {
            match self.try_lock() {
                Some(guard) => return guard,
                None => spin_loop_hint(),
            }
        }
    }
}

pub struct LockGuard<'a> {
    lock: &'a Lock,
}

impl<'a> Drop for LockGuard<'a> {
    fn drop(&mut self) {
        self.lock.is_locked.store(false, Ordering::Release);
    }
}

unsafe impl super::Lock for Lock {
    fn with(self: Pin<&Self>, critical_section: impl FnOnce()) {
        let _guard = self.lock();
        critical_section()
    }
}

#[derive(Debug, Default)]
pub struct Parker {
    is_unparked: AtomicBool,
}

impl Parker {
    pub const fn new() -> Self {
        Self {
            is_unparked: AtomicBool::new(false),
        }
    }
}

unsafe impl super::Parker for Parker {
    type Instant = Instant;

    fn park(self: Pin<&Self>, deadline: Option<Self::Instant>) -> bool {
        loop {
            if self.is_unparked.load(Ordering::Acquire) {
                return true;
            }

            let timeout = match deadline {
                None => None,
                Some(deadline) => {
                    use super::Instant;
                    let now = Self::Instant::now();
                    if now > deadline {
                        return false;
                    } else {
                        Some(deadline - now)
                    }
                }
            };

            spin_loop_hint();
            drop(timeout);
        }
    }

    fn unpark(self: Pin<&Self>) {
        self.is_unparked.store(true, Ordering::Release);
    }
}

pub type Instant = super::shared::Instant<Clock>;

struct Clock;

impl super::shared::InstantClock for Clock {
    fn is_monotonic() -> bool {
        true
    }

    fn nanotime() -> u64 {
        0
    }
}
