use std::{
    fmt,
    sync::atomic::{AtomicUsize, fence, Ordering},
};

#[derive(Default)]
pub struct Condvar {
    state: AtomicUsize,
}

impl Condvar {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(),
        }
    }
}

#[derive(Default, Copy, Clone)]
pub struct WaitTimeoutResult {
    timed_out: bool,
}

impl WaitTimeoutResult {
    const fn timed_out(&self) -> bool {
        self.timed_out
    }
}