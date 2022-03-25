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
        if !is_multi_core() {
            return false;
        }

        if self.counter >= 10 {
            return false;
        }

        self.counter += 1;
        spin_loop();
        true
    }

    pub(crate) fn yield_now(&mut self) {
        if !is_multi_core() {
            return;
        }

        self.counter += 1;
        for _ in 0..(1 << self.counter.min(3)) {
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
