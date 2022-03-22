use super::{waiter::Waiter, rwlock::{RwLock, RwLockWriteGuard}};
use std::{
    fmt,
    mem::transmute,
    ops::{Deref, DerefMut},
};

#[repr(transparent)]
pub struct Mutex<T: ?Sized> {
    rwlock: RwLock<T>,
}

unsafe impl<T: Send + ?Sized> Sync for Mutex<T> {}

impl<T: fmt::Debug + ?Sized> fmt::Debug for Mutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.rwlock, f)
    }
}

impl<T: Default + ?Sized> Default for Mutex<T> {
    fn default() -> Self {
        Self::from(T::default())
    }
}

impl<T: ?Sized> From<T> for Mutex<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> Mutex<T> {
    pub const fn new(value: T) -> Self {
        Self {
            rwlock: RwLock::new(value),
        }
    }
}

impl<T: ?Sized> Mutex<T> {
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
        self.rwlock.is_locked_exclusive()
    }

    #[inline]
    pub fn try_lock(&self) -> Option<MutexGuard<'a, T>> {
        self.rwlock
            .try_write()
            .map(|guard| MutexGuard { guard })
    }

    #[inline]
    pub fn lock(&self) -> MutexGuard<'a, T> {
        let guard = self.rwlock.write();
        MutexGuard { guard }
    }

    #[inline]
    pub unsafe fn force_unlock(&self) {
        self.rwlock.force_unlock_write()
    }

    #[inline]
    pub(super) unsafe fn unpark_requeue(
        &self,
        head: NonNull<Waiter>,
        tail: NonNull<Waiter>,
    ) {
        let is_writer = true;
        self.rwlock.unpark_requeue(is_writer, head, tail)
    }
}

pub struct MutexGuard<'a, T: ?Sized> {
    guard: RwLockWriteGuard<'a, T>,
}

impl<'a, T: ?Sized> MutexGuard<'a, T> {
    pub fn mutex(this: &Self) -> &'a Mutex<T> {
        let rwlock = RwLockWriteGuard::rwlock(&this.guard);
        unsafe { transmute(rwlock) } // SAFETY: repr(transparent)
    }
}

impl<'a, T: ?Sized> Deref for MutexGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        Deref::deref(&self.guard)
    }
}

impl<'a, T: ?Sized> DerefMut for MutexGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        DerefMut::deref_mut(&mut self.guard)
    }
}

impl<'a, T: fmt::Debug + ?Sized> fmt::Debug for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.guard, f)
    }
}

impl<'a, T: fmt::Display + ?Sized> fmt::Display for MutexGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.guard, f)
    }
}

