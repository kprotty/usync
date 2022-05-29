usync
============

[![Crates.io](https://img.shields.io/crates/v/usync.svg)](https://crates.io/crates/usync)
[![Documentation](https://docs.rs/usync/badge.svg)](https://docs.rs/usync/)
[![MSRV: 1.59.0](https://flat.badgen.net/badge/MSRV/1.59.0/purple)](https://blog.rust-lang.org/2022/02/24/Rust-1.59.0.html)

This library provides implementations of `Mutex`, `RwLock`, `Condvar`, `Barrier` and
`Once` that are word-sized and generally fast as those in [`parking_lot`](https://crates.io/crates/parking_lot).
It also provides a `ReentrantMutex` type which supports recursive locking. 

## Features

The primitives provided by this library have several advantages over those
in the Rust standard library:

1. All types require only require 1 word of storage space. On the other hand the
   standard library primitives require a dynamically allocated `Box` to hold
   OS-specific synchronization primitives. The small size of `Mutex` in
   particular encourages the use of fine-grained locks to increase
   parallelism.
2. Since they consist of just a single atomic variable, have constant
   initializers and don't need destructors, these primitives can be used as
   `static` global variables. The standard library primitives require
   dynamic initialization and thus need to be lazily initialized with
   `lazy_static!`.
3. Uncontended lock acquisition and release is done through fast inline
   paths which only require a single atomic operation.
4. Microcontention (a contended lock with a short critical section) is
   efficiently handled by spinning a few times while trying to acquire a
   lock.
5. The locks are adaptive and will suspend a thread after a few failed spin
   attempts. This makes the locks suitable for both long and short critical
   sections.
6. `Condvar::notify_all` will generally only wake up a single thread and requeue the
    rest to wait on the associated `Mutex`. This avoids a thundering herd
    problem where all threads try to acquire the lock at the same time.
7. `Mutex` and `RwLock` allow raw unlocking without a RAII guard object.
8. `Mutex<()>` and `RwLock<()>` allow raw locking without a RAII guard
    object.
9. A `ReentrantMutex` type which supports recursive locking.
10. Lock guards can be sent to other threads when the `send_guard` feature is
    enabled.

## Userspace queues

To keep these primitives word sized, their state is multiplexed between 
counters, queues of threads, and combinations of both. This draws similarities
to Windows' [Slim Synchronization Primitives](https://docs.microsoft.com/en-us/archive/msdn-magazine/2007/june/concurrency-synchronization-primitives-new-to-windows-vista). No external locking
of global queues as seen in Linux futex or parking_lot is employed. The queues are all
embedded in each primitive and interacted with lock-free operations to decrease worst-case contention latency.

Having to juggle around queues with the synchronization state unfortunately means
that "no spurious wakeups" cannot be guaranteed for `Condvar` and that extreme read-only workflows
for `RwLock` can't use optimized atomics to improve throughput. These perf limits shouldn't matter
in practice though, even more so when other cache effects come into play. On the bright side, 
writer/exclusive heavy workloads scale much better than existing solutions and are heavily
optimized for micro-contention.

## Nightly vs stable

There are a few restrictions when using this library on stable Rust:

- You will have to use the `const_*` functions (e.g. `const_mutex(val)`) to
  statically initialize the locking primitives. Using e.g. `Mutex::new(val)`
  does not work on stable Rust yet.

To enable nightly-only functionality, you need to enable the `nightly` feature
in Cargo (see below).

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
usync = "0.2.1"
```

To enable nightly-only features, add this to your `Cargo.toml` instead:

```toml
[dependencies]
usync = { version = "0.2.1", features = ["nightly"] }
```

To allow sending `MutexGuard`s and `RwLock*Guard`s to other threads, enable the
`send_guard` option.

## License

Licensed under MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT).
