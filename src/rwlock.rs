use super::{waiter::Waiter};
use std::{
    fmt,
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, fence, Ordering},
};

pub struct RwLock<T: ?Sized> {
    state: AtomicUsize,
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
            rwlock: RwLock::new(value),
        }
    }
}

impl<T: ?Sized> RwLock<T> {
    #[inline]
    pub fn data_ptr(&self) -> *mut T {
        self.rwlock.data_ptr()
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut T {
        self.rwlock.get_mut()
    }

    #[inline]
    pub fn is_locked(&self) -> bool {
        
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

    #[cold]
    pub(super) unsafe fn unpark_requeue(
        &self,
        is_writer: bool,
        head: NonNull<Waiter>,
        tail: NonNull<Waiter>,
    ) {
        
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

