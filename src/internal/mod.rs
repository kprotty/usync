// Copyright (c) 2021 kprotty
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

use std::time::Instant;

mod spin;
mod event;
mod futex;
mod queue;

cfg_if! {
    if #[cfg(windows)] {
        #[path = "backend/windows.rs"]
        mod backend;
    } else if #[cfg(target_vendor = "apple")] {
        #[path = "backend/darwin.rs"]
        mod backend;
    } else if #[cfg(any(target_os = "linux", target_os = "android"))] {
        #[path = "backend/linux.rs"]
        mod backend;
    } else if #[cfg(unix)] {
        #[path = "backend/posix.rs"]
        mod backend;
    } else {
        #[path = "backend/generic.rs"]
        mod backend;
    }
}

pub use self::{
    futex::Futex,
    spin::SpinWait,
    queue::{Token, Waiter, Parked, FilterOp, RequeueOp},
};

struct Config;

impl queue::Config for Config {
    type Lock = futex::Lock<Futex>;
    type Event = futex::Event<Futex>;
}

pub unsafe fn park(
    address: usize,
    deadline: Option<Instant>,
    validate: impl FnOnce() -> Option<Token>,
    before_wait: impl FnOnce(),
    timed_out: impl FnOnce(&Waiter),
) -> Parked {
    queue::park::<Config>(
        address,
        deadline,
        validate,
        before_wait,
        timed_out,
    )
}

pub unsafe fn unpark_filter(
    address: usize,
    filter: impl FnMut(&Waiter) -> FilterOp,
    before_wake: impl FnOnce(),
) {
    queue::unpark::<Config>(
        address,
        queue::UnparkOp::Filter(filter),
        before_wake,
    )
}

pub unsafe fn unpark_requeue(
    address: usize,
    requeue_address: usize,
    requeue: impl FnOnce() -> RequeueOp,
    before_wake: impl FnOnce(),
) {
    queue::unpark::<Config>(
        address,
        queue::UnparkOp::Requeue(requeue_address, requeue),
        before_wake,
    )
}

pub unsafe fn unpark_all(
    address: usize,
    token: Token,
) {
    unpark_filter(
        address,
        |_| FilterOp::Unpark(token),
        || {},
    )
}

#[derive(Copy, Clone, Debug, Hash)]
pub struct Unparked {
    pub token: Option<Token>,
    pub has_more: bool,
    pub be_fair: bool,
}

pub unsafe fn unpark_one(
    address: usize,
    unparked: impl FnOnce(Unparked) -> Token,
) {
    let mut unpark_token = None;
    let mut unparked = Some(unparked);

    unpark_filter(
        address,
        |waiter| match unpark_token {
            Some(_) => FilterOp::Stop,
            None => {
                let token = (unparked.take().unwrap())(Unparked {
                    token: waiter.token(),
                    has_more: waiter.has_more(),
                    be_fair: waiter.token().map(|_| waiter.be_fair()).unwrap_or(false),
                });
                unpark_token = Some(token);
                FilterOp::Unpark(token)
            }
        },
        || unpark_token
            .map(|_| {})
            .unwrap_or_else(|| {
                let _ = (unparked.take().unwrap())(Unparked {
                    token: None,
                    has_more: false,
                    be_fair: false,
                });
            }),
    )
}