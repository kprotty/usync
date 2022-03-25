use std::{
    mem::size_of,
    num::NonZeroUsize,
    ptr,
    thread::{self, ThreadId},
};

#[derive(Default, Debug)]
pub struct RawThreadId;

unsafe impl lock_api::GetThreadId for RawThreadId {
    const INIT: Self = Self;

    fn nonzero_thread_id(&self) -> NonZeroUsize {
        let thread_id = thread::current().id();
        let id_ptr = &thread_id as *const ThreadId;
        assert!(size_of::<ThreadId>() >= size_of::<NonZeroUsize>());
        unsafe { ptr::read_unaligned(id_ptr as *const NonZeroUsize) }
    }
}
