use core::{
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
