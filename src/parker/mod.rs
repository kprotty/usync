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

//! Contains core primitives which pause & unpause the caller's OS thread execution.
//! These serve as the building block for all other data structures in the library.

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
pub unsafe trait Parker: Sync {
    /// Value type which represents a specific point in time for the Parker platform.
    type Instant: Copy + PartialOrd + Add<Duration, Output = Self::Instant>;

    /// Return the current timestamp as known by the Parker platform.
    /// The returned `Instant` returned must guarantee to be no less than any previously created Instant.
    /// It is however O.K to return an instant in which time stops, slows down or speed up.
    /// But it must always be monotonic and never go backwards.
    fn now() -> Self::Instant;

    /// Provides a hint to the Parker platform to yield execution of the caller
    /// indicating that it is free to schedule anything else for a breif moment.
    ///
    /// The iteration represents how many times it has been called under a given context.
    /// No iteration provided (`None`) indicates that there is no context and any type of yielding is fine.
    ///
    /// Returns whether or not the caller is allowed to yield again given the iteration context.
    /// This can be used to indicate to the caller that its better to [park] instead of yielding.
    ///
    /// [park]: Parker::park
    fn yield_now(iteration: Option<usize>) -> bool;

    /// Creates an instance of the `Parker` which can be used to repeatedly
    /// pause and unpause execution of the calling thread.
    fn new() -> Self;

    /// Prepare the parker to be parked.
    /// This must be called before [park] and [park_until].
    /// Failing to do so may result in a panic, deadlock, etc. but not undefined behavior.
    ///
    /// [park]: Parker::park
    /// [park_until]: Parker::park_until
    fn prepare(&mut self);

    /// Pause execution of the calling thread until another thread invokes [unpark].
    /// [prepare] must be called before hand.
    ///
    /// [prepare]: Parker::prepare
    /// [unpark]: Parker::unpark
    fn park(&self);

    /// Pause execution of the calling thread until another thread invokes [unpark]
    /// or until the deadline provided is reached. [prepare] must be called before hand.
    /// Returns false if the call timed out and reached the deadline.
    ///
    /// [prepare]: Parker::prepare
    /// [unpark]: Parker::unpark
    fn park_until(&self, deadline: Self::Instant) -> bool;

    /// Unpause execution of the thread that is paused under a call to [park] or [park_until].
    /// It is not necessary that the caller switch to execution of the parked thread,
    /// only that it schedules it to eventually continue execution.
    ///
    /// [prepare] must be called before-hand and after a successfull call to `unpark`,
    /// [prepare] must be called again in if the thread wishes to pause execution again.
    ///
    /// # Safety
    ///
    /// Although the type is `Sync` and `unpark` is called from a shared reference, it must not be called by multiple threads.
    /// Only one thread is allowed to unpark() a parked `Parker` at a given moment in time.
    ///
    /// [prepare]: Parker::prepare
    /// [park]: Parker::park
    /// [park_until]: Parker::park_until
    unsafe fn unpark(&self);
}

/// Aliases some [`Parker`] that is available to the current target.
/// It may use OS blocking primitives if available or it may use spinning.
#[cfg(any(feature = "os", feature = "std"))]
pub type DefaultParker = SystemParker;

/// Aliases some [`Parker`] that is available to the current target.
/// It may use OS blocking primitives if available or it may use spinning.
#[cfg(not(any(feature = "os", feature = "std")))]
pub type DefaultParker = SpinParker;

/// Aliases a [`Parker`] that is available to the current target
/// which communicates with the underlying OS for `Instant` and blocking/unblocking.
#[cfg(all(feature = "std", not(feature = "os")))]
pub type SystemParker = StdParker;

/// Aliases a [`Parker`] that is available to the current target
/// which communicates with the underlying OS for `Instant` and blocking/unblocking.
#[cfg(all(feature = "os", not(feature = "std")))]
pub type SystemParker = OsParker;

/// Aliases a [`Parker`] that is available to the current target
/// which communicates with the underlying OS for `Instant` and blocking/unblocking.
#[cfg(any(feature = "std", feature = "os"))]
pub type SystemParker = OsParker;

mod spin_parker;
pub use spin_parker::SpinParker;

#[cfg(feature = "std")]
mod std_parker;
#[cfg(feature = "std")]
pub use std_parker::StdParker;

#[cfg(feature = "os")]
mod os_parker;
#[cfg(feature = "os")]
pub use os_parker::OsParker;
