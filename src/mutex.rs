use super::wait_queue;
use std::{
    cell::UnsafeCell,
    hint::spin_loop,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicU8, Ordering},
};

const UNLOCKED: u8 = 0;
const LOCKED: u8 = 1;
const CONTENDED: u8 = 2;

pub struct Mutex<T> {
    value: UnsafeCell<T>,
    state: AtomicU8,
}

unsafe impl<T: Send> Send for Mutex<T> {}
unsafe impl<T: Send> Sync for Mutex<T> {}

impl<T: Default> Default for Mutex<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> From<T> for Mutex<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> Mutex<T> {
    pub const fn new(value: T) -> Self {
        Self {
            value: UnsafeCell::new(value),
            state: AtomicU8::new(UNLOCKED),
        }
    }

    pub fn try_lock(&self) -> Option<MutexGuard<'_, T>> {
        self.state
            .compare_exchange(UNLOCKED, LOCKED, Ordering::Acquire, Ordering::Relaxed)
            .ok()
            .map(|_| MutexGuard { mutex: self })
    }

    pub fn lock(&self) -> MutexGuard<'_, T> {
        self.acquire();
        MutexGuard { mutex: self }
    }

    fn acquire(&self) {
        #[cfg(target_arch = "x86_64")]
        const MAX_SPIN: u8 = 100;
        #[cfg(not(target_arch = "x86_64"))]
        const MAX_SPIN: u8 = 10;

        let mut lock_state = self.state.swap(LOCKED, Ordering::Acquire);
        if lock_state == UNLOCKED {
            return;
        }

        let mut state = LOCKED;
        let mut spin = MAX_SPIN;
        loop {
            if state == UNLOCKED {
                state = match self.state.compare_exchange(
                    state,
                    lock_state,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(e) => e,
                };
            }

            if state == LOCKED {
                if let Some(new_spin) = spin.checked_sub(1) {
                    spin = new_spin;
                    spin_loop();
                    state = self.state.load(Ordering::Relaxed);
                    continue;
                }

                state = self.state.swap(CONTENDED, Ordering::Acquire);
                if state == UNLOCKED {
                    return;
                }
            }

            let address = &self.state as *const _ as usize;
            let validate = || self.state.load(Ordering::Relaxed) == CONTENDED;
            let _ = wait_queue::wait(address, validate, None);

            state = self.state.load(Ordering::Relaxed);
            lock_state = CONTENDED;
            spin = MAX_SPIN;
        }
    }

    pub(super) fn acquire_waiting(&self) {
        while self.state.swap(CONTENDED, Ordering::Acquire) != UNLOCKED {
            let address = &self.state as *const _ as usize;
            let validate = || self.state.load(Ordering::Relaxed) == CONTENDED;
            let _ = wait_queue::wait(address, validate, None);
        }
    }

    pub(super) fn release(&self) {
        if self.state.swap(UNLOCKED, Ordering::Release) == CONTENDED {
            let address = &self.state as *const _ as usize;
            wait_queue::wake(address, 1);
        }
    }
}

pub struct MutexGuard<'a, T> {
    pub(super) mutex: &'a Mutex<T>,
}

impl<'a, T> Drop for MutexGuard<'a, T> {
    fn drop(&mut self) {
        self.mutex.release();
    }
}

impl<'a, T> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.mutex.value.get() }
    }
}

impl<'a, T> Deref for MutexGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.mutex.value.get() }
    }
}
