use super::wait_queue;
use std::{
    cell::UnsafeCell,
    hint::spin_loop,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, Ordering},
    thread,
};

struct Backoff {
    spin: u8,
}

impl Backoff {
    #[cfg(target_arch = "x86_64")]
    const MAX_SPIN: u8 = 100;
    #[cfg(not(target_arch = "x86_64"))]
    const MAX_SPIN: u8 = 10;

    fn new() -> Self {
        Self {
            spin: Self::MAX_SPIN,
        }
    }

    fn spin(&mut self) -> bool {
        self.spin
            .checked_sub(1)
            .map(|new_spin| {
                self.spin = new_spin;
                spin_loop();
            })
            .is_some()
    }

    fn snooze(&mut self) {
        if !self.spin() {
            *self = Self::new();
            thread::yield_now();
        }
    }
}

const UNLOCKED: usize = 0b0000;
const PARKED: usize = 0b0001;
const WRITER_PARKED: usize = 0b0010;
const WRITER: usize = 0b0100;
const READER: usize = 0b1000;
const READER_MASK: usize = !(READER - 1);

pub struct RwLock<T> {
    value: UnsafeCell<T>,
    state: AtomicUsize,
}

unsafe impl<T: Send> Send for RwLock<T> {}
unsafe impl<T: Send> Sync for RwLock<T> {}

impl<T: Default> Default for RwLock<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> From<T> for RwLock<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> RwLock<T> {
    pub const fn new(value: T) -> Self {
        Self {
            value: UnsafeCell::new(value),
            state: AtomicUsize::new(UNLOCKED),
        }
    }

    pub fn try_read(&self) -> Option<RwLockReadGuard<'_, T>> {
        if self.try_lock_read() {
            Some(RwLockReadGuard { rwlock: self })
        } else {
            None
        }
    }

    pub fn read(&self) -> RwLockReadGuard<'_, T> {
        self.lock_read();
        RwLockReadGuard { rwlock: self }
    }

    pub fn try_write(&self) -> Option<RwLockWriteGuard<'_, T>> {
        if self.try_lock_write() {
            Some(RwLockWriteGuard { rwlock: self })
        } else {
            None
        }
    }

    pub fn write(&self) -> RwLockWriteGuard<'_, T> {
        self.lock_write();
        RwLockWriteGuard { rwlock: self }
    }

    fn try_lock_read(&self) -> bool {
        self.state
            .fetch_update(Ordering::Acquire, Ordering::Relaxed, |state| {
                match state & WRITER {
                    0 => state.checked_add(READER),
                    _ => None,
                }
            })
            .is_ok()
    }

    fn lock_read(&self) {
        let state = self.state.load(Ordering::Relaxed);
        if state & WRITER == 0 {
            if let Some(new_state) = state.checked_add(READER) {
                if let Ok(_) = self.state.compare_exchange(
                    state,
                    new_state,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    return;
                }
            }
        }

        self.acquire_with(
            READER,
            PARKED,
            |state| state & (WRITER | PARKED) == (WRITER | PARKED),
            || {
                let mut backoff = Backoff::new();
                loop {
                    let state = self.state.load(Ordering::Relaxed);
                    if state & WRITER != 0 {
                        return Some(state);
                    }

                    let new_state = state
                        .checked_add(READER)
                        .expect("RwLock reader count overflowed");

                    match self.state.compare_exchange(
                        state,
                        new_state,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return None,
                        Err(_) => backoff.snooze(),
                    }
                }
            },
        );
    }

    fn unlock_read(&self) {
        let state = self.state.fetch_sub(READER, Ordering::Release);
        if state & (READER_MASK | WRITER_PARKED) != (READER | WRITER_PARKED) {
            return;
        }

        self.state.fetch_and(!WRITER_PARKED, Ordering::Relaxed);
        self.notify(WRITER_PARKED, |has_more| assert!(!has_more));
    }

    fn try_lock_write(&self) -> bool {
        self.state
            .compare_exchange(UNLOCKED, WRITER, Ordering::Acquire, Ordering::Relaxed)
            .is_ok()
    }

    fn lock_write(&self) {
        if let Ok(_) =
            self.state
                .compare_exchange_weak(UNLOCKED, WRITER, Ordering::Acquire, Ordering::Relaxed)
        {
            return;
        }

        self.acquire_with(
            WRITER,
            PARKED,
            |state| state & (WRITER | PARKED) == (WRITER | PARKED),
            || {
                let mut state = self.state.load(Ordering::Relaxed);
                loop {
                    if state & WRITER == 0 {
                        return Some(state);
                    }

                    match self.state.compare_exchange_weak(
                        state,
                        state | WRITER,
                        Ordering::Acquire,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => return None,
                        Err(e) => state = e,
                    }
                }
            },
        );

        self.acquire_with(
            WRITER,
            WRITER_PARKED,
            |state| {
                assert_ne!(state & WRITER, 0);
                if state & READER_MASK == 0 {
                    return false;
                }

                assert_ne!(state & WRITER_PARKED, 0);
                true
            },
            || {
                let state = self.state.load(Ordering::Acquire);
                match state & READER_MASK {
                    0 => None,
                    _ => Some(state),
                }
            },
        );
    }

    fn unlock_write(&self) {
        if let Ok(_) =
            self.state
                .compare_exchange(WRITER, UNLOCKED, Ordering::Release, Ordering::Relaxed)
        {
            return;
        }

        self.notify(PARKED, |has_more| {
            let new_state = if has_more { PARKED } else { UNLOCKED };
            self.state.store(new_state, Ordering::Release);
        });
    }

    #[cold]
    fn acquire_with(
        &self,
        park_token: usize,
        park_addr: usize,
        mut park_validate: impl FnMut(usize) -> bool,
        mut try_lock: impl FnMut() -> Option<usize>,
    ) {
        let mut backoff = Backoff::new();
        loop {
            let state = match try_lock() {
                Some(state) => state,
                None => return,
            };

            if state & park_addr == 0 {
                if backoff.spin() {
                    continue;
                }

                if let Err(_) = self.state.compare_exchange_weak(
                    state,
                    state | park_addr,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    spin_loop();
                    continue;
                }
            }

            let address = match park_token {
                READER => self as *const _ as usize,
                WRITER => (self as *const _ as usize) + 1,
                _ => unreachable!("invalid park_token for acquire_with"),
            };

            let validate = || match park_validate(self.state.load(Ordering::Relaxed)) {
                true => Some(park_token),
                false => None,
            };

            let _ = wait_queue::wait_with(address, validate, None);
            backoff = Backoff::new();
            continue;
        }
    }

    #[cold]
    fn notify(&self, park_token: usize, park_notified: impl FnOnce(bool)) {
        let address = match park_token {
            READER => self as *const _ as usize,
            WRITER => (self as *const _ as usize) + 1,
            _ => unreachable!("invalid park_token for notify"),
        };

        let mut unparked = 0;
        let filter = |token: usize| {
            if unparked & WRITER != 0 {
                return None;
            }

            unparked |= token;
            Some(token)
        };

        wait_queue::wake_filter(address, filter, park_notified);
    }
}

pub struct RwLockWriteGuard<'a, T> {
    rwlock: &'a RwLock<T>,
}

impl<'a, T> Drop for RwLockWriteGuard<'a, T> {
    fn drop(&mut self) {
        self.rwlock.unlock_write();
    }
}

impl<'a, T> DerefMut for RwLockWriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.rwlock.value.get() }
    }
}

impl<'a, T> Deref for RwLockWriteGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.rwlock.value.get() }
    }
}

pub struct RwLockReadGuard<'a, T> {
    rwlock: &'a RwLock<T>,
}

impl<'a, T> Drop for RwLockReadGuard<'a, T> {
    fn drop(&mut self) {
        self.rwlock.unlock_read();
    }
}

impl<'a, T> Deref for RwLockReadGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.rwlock.value.get() }
    }
}
