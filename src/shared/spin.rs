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

        // On ARM64 systems, spin with WFE for a while as its often more efficient for contention than yield.
        // The value of 10 comes from apple libdispatch/GCD:
        // https://github.com/apple/swift-corelibs-libdispatch/blob/29babc17e2559339e48c163f4c02ed3356a7123f/src/shims/yield.h#L63
        #[cfg(all(not(miri), target_arch = "aarch64"))]
        {
            if self.counter >= 10 {
                return false;
            }

            unsafe { std::arch::asm!("wfe", options(preserves_flags, nostack)) };
            self.counter += 1;
            return true;
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
