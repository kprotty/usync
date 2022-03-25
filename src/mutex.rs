use super::RawRwLock;
use lock_api::RawRwLock as _RawRwLock;

#[derive(Default)]
#[repr(transparent)]
pub struct RawMutex {
    pub(super) rwlock: RawRwLock,
}

unsafe impl lock_api::RawMutex for RawMutex {
    type GuardMarker = crate::GuardMarker;

    const INIT: Self = Self {
        rwlock: RawRwLock::INIT,
    };

    #[inline]
    fn is_locked(&self) -> bool {
        self.rwlock.is_locked_exclusive()
    }

    #[inline]
    fn lock(&self) {
        self.rwlock.lock_exclusive()
    }

    #[inline]
    fn try_lock(&self) -> bool {
        self.rwlock.try_lock_exclusive()
    }

    #[inline]
    unsafe fn unlock(&self) {
        self.rwlock.unlock_exclusive()
    }
}

pub type Mutex<T> = lock_api::Mutex<RawMutex, T>;
pub type MutexGuard<'a, T> = lock_api::MutexGuard<'a, RawMutex, T>;
pub type MappedMutexGuard<'a, T> = lock_api::MappedMutexGuard<'a, RawMutex, T>;

pub const fn const_mutex<T>(value: T) -> Mutex<T> {
    Mutex::const_new(<RawMutex as lock_api::RawMutex>::INIT, value)
}
