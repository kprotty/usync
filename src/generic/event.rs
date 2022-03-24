use core::{
    time::Duration,
    pin::Pin,
};

pub unsafe trait Event: Sync {
    fn with<F>(with_event: impl FnOnce(Pin<&Self>) -> F) -> F;

    fn wait(self: Pin<&Self>, timeout: Option<Duration>) -> bool;

    fn set(self: Pin<&Self>);

    fn yield_now(attempt: usize) -> bool;
}