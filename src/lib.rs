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
mod backend;
mod rwlock;

pub use self::{
    barrier::{Barrier, BarrierWaitResult},
    condvar::{Condvar, WaitTimeoutResult},
    mutex::{Mutex, MutexGuard},
    once::{Once, OnceState},
    rwlock::{RwLock, RwLockReadGuard, RwLockWriteGuard},
};

pub use std::sync::{
    atomic, mpsc, Arc, LockResult, PoisonError, TryLockError, TryLockResult, Weak,
};
