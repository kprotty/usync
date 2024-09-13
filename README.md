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

1. All types require only 1 word of storage (unlike stdlib which stores
   more state for poison detection).
2. Inline uncontested paths and micro-contention handled with bounded,
   adaptive spinning.
3. `Condvar::notify_all` will generally only wake up a single thread and requeue the
    rest to wait on the associated `Mutex`. This avoids a thundering herd
    problem where all threads try to acquire the lock at the same time.
4. `Mutex` and `RwLock` allow raw locking and unlocking without a RAII guard object.
5. A `ReentrantMutex` type which supports recursive locking.
6. Lock guards can be sent to other threads when the `send_guard` feature is
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
