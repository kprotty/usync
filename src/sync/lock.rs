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

#[cfg(target_atomic_u8)]
use crate::utils::sync::AtomicU8;

#[cfg(any(
    target_atomic_u8,
    all(feature = "nightly", any(target_arch = "x86", target_arch = "x86_64"))
))]
use core::mem::size_of;

use crate::utils::sync::{AtomicUsize, Ordering, UnsafeCell};
use core::{
    fmt,
    ops::{Deref, DerefMut},
};

const UNLOCKED: u8 = 0;
const LOCKED: u8 = 1;

#[cfg(not(target_atomic_u8))]
const WAKING: usize = 2;
#[cfg(target_atomic_u8)]
const WAKING: usize = 256;

#[cfg(not(target_atomic_u8))]
const WAITING: usize = !3;
#[cfg(target_atomic_u8)]
const WAITING: usize = !511;

#[cfg_attr(not(target_atomic_u8), repr(align(4)))]
#[cfg_attr(target_atomic_u8, repr(align(512)))]
struct LockWaiter(());

pub struct Lock<T> {
    state: AtomicUsize,
    value: UnsafeCell<T>,
}

unsafe impl<T: Send> Send for Lock<T> {}
unsafe impl<T: Send> Sync for Lock<T> {}

impl<T: Default> Default for Lock<T> {
    fn default() -> Self {
        Self::from(T::default())
    }
}

impl<T> From<T> for Lock<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> AsMut<T> for Lock<T> {
    fn as_mut(&mut self) -> &mut T {
        self.value.with_mut(|ptr| unsafe { &mut *ptr })
    }
}

impl<T> Lock<T> {
    pub const fn new(value: T) -> Self {
        Self {
            state: AtomicUsize::new(UNLOCKED as usize),
            value: UnsafeCell::new(value),
        }
    }

    #[cfg(not(feature = "loom"))]
    // loom's UnsafeCell doesn't appear to have `into_inner`
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }

    /// For platforms which support byte-level atomics,
    /// get a reference to the state as an AtomicU8 as opposed to an AtomicUsize.
    #[cfg(target_atomic_u8)]
    fn byte_state(&self) -> &AtomicU8 {
        assert!(
            size_of::<AtomicU8>() <= size_of::<AtomicUsize>(),
            "AtomicU8 is larger than AtomicUsize for this platform",
        );
        assert!(
            size_of::<AtomicU8>() <= size_of::<u8>(),
            "AtomicU8 for this platform does not fit in a u8",
        );
        unsafe { &*(&self.state as *const _ as *const _) }
    }

    /// Try to acquire the Lock in a non-blocking manner
    #[cfg(all(feature = "nightly", any(target_arch = "x86", target_arch = "x86_64")))]
    #[inline(always)]
    pub fn try_lock(&self) -> Option<LockGuard<'_, T>> {
        let mut locked: bool;

        // For x86 platforms, although it should support byte level atomic instructions,
        // it can be better to use the atomic bit-test-and-set (`bts`) instruction instead.
        //
        // This is due to not requiring register setup like swap (`xchg`) does
        // which can increase instruction cache pressure and has been seen to be
        // a small but noticeable performance increase for many unconteded operations.
        //
        // Another advantage over swap (`xchg`) is that it need not invalidate the
        // cache line if the bit is already set.
        assert!(
            size_of::<AtomicUsize>() >= size_of::<u16>(),
            "AtomicUsize cannot be used with `lock btsw`",
        );
        unsafe {
            llvm_asm!(
                "lock btsw $$0, $1"
                : "={@ccnc}" (locked)
                : "*m" (&self.state)
                : "cc", "memory"
            );
        }

        if locked {
            Some(LockGuard::new(self))
        } else {
            None
        }
    }

    /// Try to acquire the Lock in a non-blocking manner.
    #[cfg(all(
        target_atomic_u8,
        not(all(feature = "nightly", any(target_arch = "x86", target_arch = "x86_64")))
    ))]
    #[inline(always)]
    pub fn try_lock(&self) -> Option<LockGuard<'_, T>> {
        // On platforms which support byte level atomics
        // we can swap the lower byte of the state in order to acquire the lock.
        // This is because all the state queueing happens in the bits above the lower byte
        // meaning that this operation doesn't have to race against queueing LockWaiters.
        //
        // In general (x86, ARM, riscv) a swap() as opposed to a compare_exchange()
        // less code which incurs less of a hit on the instruction cache when inlined.
        match self.byte_state().swap(LOCKED, Ordering::Acquire) {
            UNLOCKED => Some(LockGuard::new(self)),
            _ => None,
        }
    }

    /// Try to acquire the Lock in a non-blocking manner.
    #[cfg(not(all(
        target_atomic_u8,
        not(all(feature = "nightly", any(target_arch = "x86", target_arch = "x86_64")))
    )))]
    #[inline]
    pub fn try_lock(&self) -> Option<LockGuard<'_, T>> {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & (LOCKED as usize) != 0 {
                return None;
            }
            match self.state.compare_exchange_weak(
                state,
                state | (LOCKED as usize),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return LockGuard::<'_, T>::new(self),
                Err(e) => state = e,
            }
        }
    }

    /// `lock*()` fast path - tries to acquire the lock assuming no contention.
    #[cfg(any(
        target_atomic_u8,
        all(feature = "nightly", any(target_arch = "x86", target_arch = "x86_64"))
    ))]
    #[inline(always)]
    fn lock_fast(&self) -> Option<LockGuard<'_, T>> {
        // For platforms which support byte-level atomics or use custom assembly,
        // using the custom code will be faster than compare exchange in some desirable metric.
        self.try_lock()
    }

    /// `lock*()` fast path - tries to acquire the lock assuming no contention.
    #[cfg(not(any(
        target_atomic_u8,
        all(feature = "nightly", any(target_arch = "x86", target_arch = "x86_64"))
    )))]
    #[inline(always)]
    fn lock_fast(&self) -> Option<LockGuard<'_, T>> {
        // For normal platforms, a compare exchange works well and is near the perf of spinlocks.
        // The compare exchange can fail spuriously as the lock algorithm will try again in the slow path.
        self.state
            .compare_exchange_weak(
                UNLOCKED as usize,
                LOCKED as usize,
                Ordering::Acquire,
                Ordering::Relaxed,
            )
            .ok()
            .map(|_| LockGuard { lock: self })
    }

    /// Unlocks the Lock and potentially wakes up any LockWaiter waiting on the lock.
    ///
    /// # Safety
    ///
    /// This assumes that the caller has ownership of the lock
    /// and is exposed for finer-grain control such as in a C-ffi setting.
    #[cfg(not(target_atomic_u8))]
    #[inline]
    pub unsafe fn unlock(&self) {
        // Unlock the Lock using a fetch_sub as opposed to a fetch_and.
        // The former can be done in a wait-free manner on x86 cpus using the `xadd` instruction.
        let state = self.state.fetch_sub(LOCKED, Ordering::Release);

        // Go to the slow path to wake up a waiting LockWaiter
        // if there are any queued LockWaiters and
        // if one isn't currently in the process of waking up.
        if (state & WAITING != 0) && (state & WAKING == 0) {
            self.unlock_slow();
        }
    }

    /// Unlocks the Lock and potentially wakes up any LockWaiter waiting on the lock.
    ///
    /// # Safety
    ///
    /// This assumes that the caller has ownership of the lock
    /// and is exposed for finer-grain control such as in a C-ffi setting.
    #[cfg(target_atomic_u8)]
    #[inline]
    pub unsafe fn unlock(&self) {
        // Unlock the Lock using an atomic store as opposed to usize
        // a read-modify-write operation like above, which is generally faster.
        //
        // This is possible due to the LockWaiter queue bits residing in the bits
        // above the lower byte meaning the lower byte can be entirely cleared out.
        self.byte_state().store(UNLOCKED, Ordering::Release);

        // Go to the slow path to wake up a waiting LockWaiter
        // if there are any queued LockWaiters,
        // if one isn't currently in the process of waking up and
        // if the Lock isn't currently locked as the lock-holder can take care of the wake-up.
        let state = self.state.load(Ordering::Relaxed);
        if (state & WAITING != 0) && (state & (WAKING | (LOCKED as usize)) == 0) {
            self.unlock_slow();
        }
    }

    #[cold]
    fn unlock_slow(&self) {
        unimplemented!("TODO")
    }
}

pub struct LockFuture<'a, T> {
    lock: &'a Lock<T>,
}

pub struct LockGuard<'a, T> {
    lock: &'a Lock<T>,
}

impl<'a, T> LockGuard<'a, T> {
    fn new(lock: &'a Lock<T>) -> Self {
        Self { lock }
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for LockGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (&&*self).fmt(f)
    }
}

impl<'a, T> Deref for LockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.lock.value.with(|ptr| unsafe { &*ptr })
    }
}

impl<'a, T> DerefMut for LockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.lock.value.with_mut(|ptr| unsafe { &mut *ptr })
    }
}
