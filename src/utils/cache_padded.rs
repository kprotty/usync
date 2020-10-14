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

use core::{
    fmt,
    ops::{Deref, DerefMut},
};

/// Pads and aligns a value to the estimated size of a cache line.
///
/// Under many CPUs, memory is read and written in large blocks called cache lines.
/// This means that atomic operations on a value can cause the entire cache line the
/// value resides in to incur the cost of cache synchronization. This is otherwise
/// known as [false sharing](#false-sharing) and can be mitigated by putting synchronized
/// values on their own cache lines to prevent cache invalidations of unrelated memory.
///
/// This type is useful in that regard as it provides a generic wrapper around data
/// to keep it on its own cache line to the best of its ability.
///
/// [false-sharing]: https://en.wikipedia.org/wiki/False_sharing
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Default, Hash)]
// Cache lines on architectures like the s390x are assumed to be 256 bytes wide.
// Some 64-bit architectures also access cache lines in sizes of 128 bytes:
//
// - On Intel chips starting from Sandy Bridge, the spatial prefetcher can access
//   64-byte pairs of cache lines at a time when storing to L2 cache.
//      * https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-optimization-manual.pdf
//      * https://github.com/facebook/folly/blob/1b5288e6eea6df074758f877c849b6e73bbb9fbb/folly/lang/Align.h#L107
//
// - On ARM64 big.LITTLE arch, there can be "big" cores which have 128 byte wide cache lines.
//      * https://www.mono-project.com/news/2016/09/12/arm64-icache/
//
// Other cache line sizes are collectively derived from other projects:
//      * https://golang.org/search?q=CacheLinePadSize
#[cfg_attr(target_arch = "s390x", repr(align(256)))]
#[cfg_attr(
    any(
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "powerpc64"
    ),
    repr(align(128))
)]
#[cfg_attr(
    any(
        target_arch = "mips",
        target_arch = "arm",
        target_arch = "riscv32",
        target_arch = "riscv64"
    ),
    repr(align(32))
)]
#[cfg_attr(
    not(any(
        target_arch = "s390x",
        target_arch = "x86_64",
        target_arch = "aarch64",
        target_arch = "powerpc64",
        target_arch = "mips",
        target_arch = "arm",
        target_arch = "riscv32",
        target_arch = "riscv64",
    )),
    repr(align(64))
)]
pub struct CachePadded<T>(T);

unsafe impl<T: Send> Send for CachePadded<T> {}
unsafe impl<T: Sync> Sync for CachePadded<T> {}

impl<T: fmt::Debug> fmt::Debug for CachePadded<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (&&*self).fmt(f)
    }
}

impl<T> From<T> for CachePadded<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> AsRef<T> for CachePadded<T> {
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T> AsMut<T> for CachePadded<T> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}

impl<T> CachePadded<T> {
    /// Pads and aligns a value to the pessimistic estimate of the platform's cache-line.
    pub const fn new(value: T) -> Self {
        Self(value)
    }

    /// Returns the internal padded/aligned value
    pub fn into_inner(self) -> T {
        self.0
    }
}

impl<T> Deref for CachePadded<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.as_ref()
    }
}

impl<T> DerefMut for CachePadded<T> {
    fn deref_mut(&mut self) -> &mut T {
        self.as_mut()
    }
}
