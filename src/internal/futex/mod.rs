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

mod lock;
mod event;

pub use self::{
    lock::Lock,
    event::Event,
};

use std::{
    time::Instant,
    sync::atomic::{AtomicI32, Ordering},
};

pub unsafe trait Futex {
    fn wait(ptr: &AtomicI32, expect: i32, deadline: Option<Instant>) -> bool;

    fn wake(ptr: &AtomicI32);

    fn yield_now(iteration: usize) -> bool;
}