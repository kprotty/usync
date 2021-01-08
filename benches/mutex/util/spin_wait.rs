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

pub struct SpinWait {
    counter: u32,
}

impl SpinWait {
    pub const fn new() -> Self {
        Self { counter: 0 }
    }

    pub fn reset(&mut self) {
        self.counter = 0;
    }

    #[cfg(windows)]
    pub fn yield_now(&mut self) -> bool {
        if self.counter > 1000 {
            return false;
        }
        
        self.counter += 1;
        std::sync::atomic::spin_loop_hint();
        true
    }

    #[cfg(not(windows))]
    pub fn yield_now(&mut self) -> bool {
        if self.counter >= 10 {
            return false;
        }

        self.counter += 1;
        if self.counter <= 3 {
            (0..(1 << self.counter)).for_each(|_| std::sync::atomic::spin_loop_hint());
        } else {
            std::thread::yield_now();
        }

        true
    }
}
