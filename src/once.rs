use super::wait_queue;
use std::{
    hint::spin_loop,
    sync::atomic::{AtomicU8, Ordering},
};

const UNCALLED: u8 = 0;
const CALLING: u8 = 1;
const WAITING: u8 = 2;
const CALLED: u8 = 4;

#[derive(Default)]
pub struct Once {
    state: AtomicU8,
}

impl Once {
    pub const fn new() -> Self {
        Self {
            state: AtomicU8::new(UNCALLED),
        }
    }

    pub fn call_once(&self, once_fn: impl FnOnce()) {
        let mut state = self.state.load(Ordering::Acquire);
        if state == CALLED {
            return;
        }

        if state == UNCALLED {
            state = match self.state.compare_exchange(
                UNCALLED,
                CALLING,
                Ordering::Acquire,
                Ordering::Acquire,
            ) {
                Err(e) => e,
                Ok(_) => {
                    once_fn();
                    if self.state.swap(CALLED, Ordering::Release) == WAITING {
                        let address = self as *const _ as usize;
                        wait_queue::wake(address, usize::MAX);
                    }
                    return;
                }
            };
        }

        #[cfg(target_arch = "x86_64")]
        let mut spin = 100;
        #[cfg(not(target_arch = "x86_64"))]
        let mut spin = 0;

        while state == CALLING && spin > 0 {
            spin -= 1;
            spin_loop();
            state = self.state.load(Ordering::Acquire);
        }

        if state == CALLING {
            state = match self.state.compare_exchange(
                CALLING,
                WAITING,
                Ordering::Acquire,
                Ordering::Acquire,
            ) {
                Ok(_) => WAITING,
                Err(e) => e,
            };
        }

        while state == WAITING {
            let address = self as *const _ as usize;
            let validate = || self.state.load(Ordering::Relaxed) == WAITING;
            let _ = wait_queue::wait(address, validate, None);
            state = self.state.load(Ordering::Acquire);
        }

        assert_eq!(state, CALLED);
    }
}
