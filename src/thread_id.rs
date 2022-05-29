use std::num::NonZeroUsize;

/// Implementation of the `GetThreadId` trait for `lock_api::ReentrantMutex`.
#[derive(Default, Debug)]
pub struct RawThreadId;

unsafe impl lock_api::GetThreadId for RawThreadId {
    const INIT: Self = Self;

    fn nonzero_thread_id(&self) -> NonZeroUsize {
        // The address of a thread-local is guaranteed to
        // be unique to the current thread and non-zero (null)
        thread_local!(static ID: bool = false);
        ID.with(|id| NonZeroUsize::new(id as *const _ as usize).unwrap())
    }
}
