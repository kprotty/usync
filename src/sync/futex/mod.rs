use core::sync::atomic::AtomicI32;

pub unsafe trait Futex {
    type Instant;

    fn now() -> Self::Instant;

    fn wait(ptr: &AtomicI32, cmp: i32, deadline: Option<&Self::Instant>) -> bool;

    fn wake(ptr: &AtomicI32, notify_all: bool);
}

cfg_if! {
    if #[cfg(feature = "os")] {
        pub type DefaultFutex = OsFutex;
    } else if #[cfg(feature = "std")] {
        pub type DefaultFutex = StdFutex;
    } else {
        pub type DefaultFutex = SpinFutex;
    }
}

pub use spin::Futex as SpinFutex;
mod spin;

#[cfg(feature = "std")]
pub use standard::Futex as StdFutex;
#[cfg(feature = "std")]
#[path = "std.rs"]
mod standard;

#[cfg(feature = "os")]
pub use os::Futex as OsFutex;
#[cfg(feature = "os")]
cfg_if! {
    if #[cfg(windows)] {
        #[path = "windows.rs"]
        mod os;
    } else if #[cfg(target_os = "linux")] {
        #[path = "linux.rs"]
        mod os;
    } else if #[cfg(target_vendor = "apple")] {
        #[path = "darwin.rs"]
        mod os;
    } else if #[cfg(unix)] {
        #[path = "posix.rs"]
        mod os;
    } else {
        use spin as os;
    }
}