use crate::sync::atomic::AtomicU32;
use std::time::Duration;

pub trait Futex {
    fn wait(ptr: &AtomicU32, cmp: u32, timeout: Option<Duration>) -> bool;

    fn wake(ptr: *const AtomicU32, max_wake: u32);

    fn requeue(
        ptr &AtomicU32,
        cmp: u32,
        requeue_ptr: *const AtomicU32,
        max_requeue: u32,
    );

    fn yield_now(attempt: usize) -> bool;
}