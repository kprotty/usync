mod cache_aligned;
mod event;
mod parker;
mod spin;
mod strict_provenance;
mod waiter;

pub(crate) use self::{
    cache_aligned::CacheAligned,
    spin::SpinWait,
    strict_provenance::{invalid_mut, AtomicPtrRmw, StrictProvenance},
    waiter::Waiter,
};

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
