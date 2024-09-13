mod event;
mod parker;
mod spin;
mod waiter;

pub(crate) use self::{spin::SpinWait, waiter::Waiter};
pub(crate) use sptr::{invalid_mut, Strict as StrictProvenance};

use std::sync::atomic::{fence, AtomicPtr, Ordering};

// Thread-Sanitizer only has partial fence support, so when running under it, we
// try and avoid false positives by using a discarded acquire load instead.
#[inline]
pub(crate) fn fence_acquire<T>(ptr: &AtomicPtr<T>) {
    if cfg!(usync_tsan_enabled) {
        let _ = ptr.load(Ordering::Acquire);
    } else {
        fence(Ordering::Acquire);
    }
}
