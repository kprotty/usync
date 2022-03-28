#![warn(
    rust_2018_idioms,
    unreachable_pub,
    // missing_docs,
    // missing_debug_implementations,
)]

mod barrier;
mod condvar;
mod mutex;
mod once;
mod reentrant_mutex;
mod rwlock;
mod shared;
mod thread_id;

pub use ::lock_api;

#[cfg(feature = "send_guard")]
type GuardMarker = lock_api::GuardSend;
#[cfg(not(feature = "send_guard"))]
type GuardMarker = lock_api::GuardNoSend;

pub use self::{
    barrier::{Barrier, BarrierWaitResult},
    condvar::{Condvar, WaitTimeoutResult},
    mutex::{const_mutex, MappedMutexGuard, Mutex, MutexGuard, RawMutex},
    once::{Once, OnceState},
    reentrant_mutex::{
        const_reentrant_mutex, MappedReentrantMutexGuard, ReentrantMutex, ReentrantMutexGuard,
    },
    rwlock::{
        const_rwlock, MappedRwLockReadGuard, MappedRwLockWriteGuard, RawRwLock, RwLock,
        RwLockReadGuard, RwLockWriteGuard,
    },
    thread_id::RawThreadId,
};
