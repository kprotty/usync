use super::{RawMutex, RawThreadId};
use lock_api;



pub type ReentrantMutex<T> = lock_api::ReentrantMutex<RawMutex, RawThreadId, T>;
pub type ReentrantMutexGuard<'a, T> = lock_api::ReentrantMutexGuard<'a, RawMutex, RawThreadId, T>;
pub type MappedReentrantMutexGuard<'a, T> =
    lock_api::MappedReentrantMutexGuard<'a, RawMutex, RawThreadId, T>;

pub const fn const_reentrant_mutex<T>(value: T) -> ReentrantMutex<T> {
    ReentrantMutex::const_new(
        <RawMutex as lock_api::RawMutex>::INIT,
        <RawThreadId as lock_api::GetThreadId>::INIT,
        value,
    )
}
