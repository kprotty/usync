use super::Futex;
use crate::sync::atomic::{AtomicU32, Ordering};
use std::marker::PhantomData;

const EVENT_EMPTY: u32 = 0;
const EVENT_WAITING: u32 = 1;
const EVENT_SET: u32 = 2;

#[derive(Default)]
struct Event<F> {
    state: AtomicU32,
    _futex: PhantomData<F>,
}

impl<F> Event<F> {
    const fn new() -> Self {
        Self {
            state: AtomicU32::new(EVENT_EMPTY),
            _futex: PhantomData,
        }
    }
}

impl<F: Futex> Event<F> {
    #[cold]
    fn wait(&self) {
        let mut state = EVENT_EMPTY;

        let mut spin = 0;
        while state == EVENT_EMPTY && F::yield_now(spin) {
            state = self.event.load(Ordering::Acquire);
            spin += 1;
        }

        if state == EVENT_EMPTY {
            state = self
                .state
                .compare_exchange(
                    EVENT_EMPTY,
                    EVENT_WAITING,
                    Ordering::Acquire,
                    Ordering::Acquire,
                )
                .map(|_| EVENT_WAITING)
                .unwrap_or_else(|e| e);
        }

        while state == EVENT_WAITING {
            assert!(F::wait(&self.state, EVENT_WAITING, None));
            state = self.state.load(Ordering::Acquire);
        }
    }

    #[cold]
    fn wake(&self) {
        if self.state.swap(EVENT_SET, Ordering::Release) == EVENT_WAITING {
            F::wake(&self.state, u32::MAX);
        }
    }
}

#[derive(Default)]
pub struct Barrier<F> {
    count: AtomicU32,
    event: Event<F>,
}

impl<F> Barrier<F> {
    pub const fn new(n: usize) -> Self {
        Self {
            count: AtomicU32::new(n as u32),
            event: Event::<F>::new(),
        }
    }
}

impl<F: Futex> Barrier<F> {
    pub fn wait(&self) -> bool {
        match self.count.fetch_update(
            Ordering::Relaxed,
            Ordering::Relaxed,
            |count| count.checked_sub(1),
        ) {
            Err(_) => false,
            Ok(1) => self.event.wake(),
            Err(_) => self.event.wait(),
        }
    }
}
