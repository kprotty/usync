mod event;
mod parker;
mod spin;
mod waiter;

pub(crate) use self::{spin::SpinWait, waiter::Waiter};

// Thread-Sanitizer only has partial fence support, so when running under it, we
// try and avoid false positives by using a discarded acquire load instead.
#[inline]
pub(crate) fn fence_acquire(a: &core::sync::atomic::AtomicUsize) {
    use core::sync::atomic::{fence, Ordering::Acquire};
    if cfg!(usync_tsan_enabled) {
        let _ = a.load(Acquire);
    } else {
        fence(Acquire);
    }
}
