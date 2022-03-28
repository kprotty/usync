use std::{
    hint::spin_loop,
    num::NonZeroUsize,
    sync::atomic::{AtomicUsize, Ordering},
    thread::available_parallelism,
};

#[derive(Default)]
pub(crate) struct SpinWait {
    counter: usize,
}

impl SpinWait {
    pub(crate) fn try_yield_now(&mut self) -> bool {
        // Don't spin if we're on a uni-core system (e.g. docker instance or low-end vps/vm)
        if !is_multi_core() {
            return false;
        }

        // Spin for at most 100 times.
        // This could be lower but this works as is also the default spin count in musl
        // as well as glibc PTHREAD_MUTEX_ADAPTIVE_SPIN.
        if self.counter >= 100 {
            return false;
        }

        self.counter += 1;
        spin_loop();
        true
    }

    pub(crate) fn yield_now(&mut self) {
        // Don't spin if we're on a uni-core system (e.g. docker instance or low-end vps/vm)
        if !is_multi_core() {
            return;
        }

        // Spin using exponential backoff.
        // parking_lot has the spin count capped at (1 << 10) = 1024
        // but we probably don't need to spin that long to avoid cache-line contention
        // so we cap it at (1 << 5) = 32 instead (this is still fairly arbitrary).
        self.counter += 1;
        for _ in 0..(1 << self.counter.min(5)) {
            spin_loop();
        }
    }
}

#[inline]
fn is_multi_core() -> bool {
    num_cpus().get() > 1
}

static NUM_CPUS: AtomicUsize = AtomicUsize::new(0);

#[inline]
fn num_cpus() -> NonZeroUsize {
    // fast path to get the num cpus as provided by libstd
    let num_cpus = NUM_CPUS.load(Ordering::Relaxed);
    NonZeroUsize::new(num_cpus).unwrap_or_else(|| num_cpus_slow())
}

#[cold]
fn num_cpus_slow() -> NonZeroUsize {
    let num_cpus = available_parallelism()
        .ok()
        .or(NonZeroUsize::new(1))
        .unwrap();

    NUM_CPUS.store(num_cpus.get(), Ordering::Relaxed);
    num_cpus
}
