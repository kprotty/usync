//! Contains core primitives which pause & unpause the caller's OS thread execution.
//! These serve as the building block for all other data structures in the library.

// Copyright (c) 2020 kprotty
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use core::{ops::Add, time::Duration};

/// A `Parker` is an interface that abstracts out the mechanism in which
/// a thread can use to pause and unpause execution.
///
/// Once a [`Parker`] is created, it can go through the pause/unpause cycle multiple times.
/// - The thread which owns the Parker called [prepare] to ensure that it can start parking.
/// - [park] is then called to pause the execution of the calling thread until signalled.
/// - [unpark] is finally called from another thread to reschedule/continue the execution of the parked thread.
///
/// [prepare]: Parker::prepare
/// [park]: Parker::park
/// [unpark]: Parker::unpark
pub unsafe trait Parker {
    /// Value type which represents a specific point in time for the platform.
    type Instant: Copy + PartialOrd + Add<Duration, Output = Self::Instant>;

    /// Returns the current timestamp as seen from the platform. 
    /// The instant returned must be monotonic in the sense that no `Instant` returned from a `now()` call in the future can be smaller than one in the past. 
    /// It is still allowed to never progress, as in the returned Instant can represent the same timestamp for an undefined period of time, but never go backwards.
    fn now() -> Self::Instant;

    fn yield_now(iteration: Option<usize>) -> bool;

    fn new() -> Self;

    fn prepare(&self);

    fn park(&self);

    fn try_park_until(&self, deadline: Self::Instant) -> bool;

    fn unpark(&self);
}

#[cfg(any(feature = "os", feature = "std"))]
pub type DefaultParker = SystemParker;
#[cfg(not(any(feature = "os", feature = "std")))]
pub type DefaultParker = SpinParker;

#[cfg(all(feature = "std", not(feature = "os")))]
pub type SystemParker = StdParker;
#[cfg(all(feature = "os", not(feature = "std")))]
pub type SystemParker = OsParker;
#[cfg(any(feature = "std", feature = "os"))]
pub type SystemParker = StdParker; // OsParker;

mod spin_parker;
pub use spin_parker::SpinParker;

#[cfg(feature = "std")]
mod std_parker;
#[cfg(feature = "std")]
pub use std_parker::StdParker;

// #[cfg(feature = "os")]
// mod os_parker;
// #[cfg(feature = "os")]
// pub use os_parker::OsParker;
