use core::pin::Pin;

pub trait Platform {
    type Lock: Lock;
    type Parker: Parker;
}

pub unsafe trait Lock: Send + Sync {
    fn with(self: Pin<&Self>, f: impl FnOnce());
}

pub unsafe trait Parker: Sync {
    type Instant: Instant;

    fn park(self: Pin<&Self>, deadline: Option<Self::Instant>) -> bool;
    fn unpark(self: Pin<&Self>);
}

pub trait Instant: Clone {
    fn now() -> Self;
}

mod shared;

pub mod spin;

#[cfg(feature = "std")]
#[path = "std.rs"]
pub mod standard;

#[cfg(feature = "os")]
crate::cfg_if! {
    if #[cfg(windows)] {
        #[path = "windows.rs"]
        pub mod os;
    } else if #[cfg(target_os = "linux")] {
        #[path = "linux.rs"]
        pub mod os;
    } else if #[cfg(target_vendor = "apple")] {
        #[path = "darwin.rs"]
        pub mod os;
    } else if #[cfg(unix)] {
        #[path = "posix.rs"]
        pub mod os;
    } else {
        #[path = "spin.rs"]
        pub mod os;
    }
}

crate::cfg_if! {
    if #[cfg(feature = "std")] {
        pub use self::standard as default;
    } else if #[cfg(feature = "os")] {
        pub use self::os as default;
    } else {
        pub use self::spin as default;
    }
}
