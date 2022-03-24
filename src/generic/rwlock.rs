use super::{waiter::Waiter};
use core::{
    fmt,
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, fence, Ordering},
};

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
pub enum RwLockState {
    Unlocked,
    Exclusive,
    Shared,
}

#[derive(Default)]
pub struct RawRwLock {
    state: AtomicUsize,
}

impl RawRwLock {
    pub const fn new() -> Self {
        Self {
            raw_rwlock: RawRwLock::new(),
        }
    }

    #[inline]
    pub fn state(&self) -> RwLockState {
        
    }

    #[inline]
    pub fn try_lock(&self) -> bool {
        self.raw_rwlock.try_write()
    }

    #[inline]
    pub fn lock<E: Event>(&self) {
        self.raw_rwlock.write::<E>()
    }

    #[inline]
    pub unsafe fn unlock(&self) {
        self.raw_rwlock.unlock_write()
    }
}

pub struct RwLock<T: ?Sized> {
    raw_rwlock: RawRwLock,
    value: UnsafeCell<T>,
}

unsafe impl<T: Send + ?Sized> Send for RwLock<T> {}
unsafe impl<T: Send + Sync + ?Sized> Sync for RwLock<T> {}

impl<T: fmt::Debug + ?Sized> fmt::Debug for RwLock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.rwlock, f)
    }
}

impl<T: Default + ?Sized> Default for RwLock<T> {
    fn default() -> Self {
        Self::from(T::default())
    }
}

impl<T: ?Sized> From<T> for RwLock<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> RwLock<T> {
    pub const fn new(value: T) -> Self {
        Self {
            raw_rwlock: RawRwLock::new(),
            value: RwLock::new(value),
        }
    }
}

impl<T: ?Sized> RwLock<T> {
    #[inline]
    pub fn data_ptr(&self) -> *mut T {
        self.value.get()
    }

    #[inline]
    pub fn raw(&self) -> &RawRWLock {
        &self.raw_rwlock
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { &mut *self.data_ptr() }
    }

    #[inline]
    pub fn state(&self) -> bool {
        
    }

    #[inline]
    pub fn try_write(&self) -> Option<RwLockWriteGuard<'a, T>> {
        
    }

    #[inline]
    pub fn write(&self) -> RwLockWriteGuard<'a, T> {
        
    }

    #[inline]
    pub unsafe fn force_unlock_write(&self) {
        
    }

    pub unsafe fn force_unlock_read(&self) {

    }
}

pub struct RwLockWriteGuard<'a, T: ?Sized> {
    rwlock: &'a RwLock<T>,
}

impl<'a, T: ?Sized> Drop for RwLockWriteGuard<'a, T> {
    fn drop(&mut self) {
        unsafe { self.rwlock.force_unlock_write() }
    }
}

impl<'a, T: ?Sized> RwLockWriteGuard<'a, T> {
    pub fn rwlock(this: &Self) -> &'a RwLock<T> {
        self.rwlock
    }
}

impl<'a, T: ?Sized> Deref for RwLockWriteGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { &*self.rwlock.data_ptr() }
    }
}

impl<'a, T: ?Sized> DerefMut for RwLockWriteGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.rwlock.data_ptr() }
    }
}

impl<'a, T: fmt::Debug + ?Sized> fmt::Debug for RwLockWriteGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T: fmt::Display + ?Sized> fmt::Display for RwLockWriteGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (**self).fmt(f)
    }
}

