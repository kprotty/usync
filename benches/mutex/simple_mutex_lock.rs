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

type Mutex = simple_mutex::Mutex<()>;

pub struct Lock(Mutex);

unsafe impl super::Lock for Lock {
    const NAME: &'static str = "simple_mutex";

    fn new() -> Self {
        Self(Mutex::new(()))
    }

    fn with(&self, f: impl FnOnce()) {
        let guard = self.0.lock();
        f();
        std::mem::drop(guard);
    }
}
