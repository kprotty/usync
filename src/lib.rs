#![warn(
    rust_2018_idioms,
    unreachable_pub,
    // missing_docs
    // missing_debug_implementations    
)]

pub mod generic;

#[cfg(feature = "std")]
pub use std_sync::*;

#[cfg(feature = "std")]
mod std_sync;