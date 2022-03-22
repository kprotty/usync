use super::waiter::Waiter;
use std::{
    fmt,
    sync::atomic::{AtomicUsize, fence, Ordering},
};

const COMPLETED: usize = 0;
const QUEUED: usize = 0b001;
const UPDATING: usize = 0b010;

#[derive(Default)]
pub struct Barrier {
    state: AtomicUsize,
}

impl Barrier {
    pub const fn new(n: usize) -> Self {
        Self {
            state: AtomicUsize::new(n << 1),
        }
    }
    
    #[inline]
    pub fn wait(&self) -> BarrierWaitResult {
        let mut is_leader = false;
        let state = self.state.load(Ordering::Acquire);
    
        if state != COMPLETED {
            is_leader = self.wait_slow(state);
        }

        BarrierWaitResult { is_leader }
    }

    #[cold]
    fn wait_slow(&self, mut state: usize) -> bool {
        Waiter::with(|waiter| {
            waiter.resource.set(Some(NonNull::from(self).cast()));
            waiter.parker.prepare();
            waiter.prev.set(None);

            loop {
                if state == COMPLETED {
                    fence(Ordering::Acquire);
                    return false;
                }

                if state & QUEUED == 0 {
                    waiter.counter.store(state >> 1, Ordering::Relaxed);
                    waiter.tail.set(Some(NonNull::from(&*waiter)));
                    waiter.next.set(None);
                } else {
                    let head = NonNull::new((state & Waiter::MASK) as *mut Waiter);
                    waiter.next.set(head);
                    waiter.tail.set(None);
                }

                let waiter_ptr = &*waiter as *const Waiter as usize;
                let new_state = waiter_ptr | QUEUED | UPDATING;

                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                if (state & QUEUED == 0) || (state & UPDATING == 0) {
                    if self.update(new_state) {
                        return true;
                    }
                }

                assert!(waiter.parker.park(None));
                return false;
            }
        })
    }

    #[cold]
    unsafe fn update(&self, mut state: usize) -> bool {
        loop {
            assert_ne!(state, COMPLETED);
            assert_ne!(state & QUEUED, 0);
            assert_ne!(state & UPDATING, 0);

            fence(Ordering::Acquire);
            let mut discovered = 0;
            let (head, tail) = Waiter::get_queue(state, |_| discovered += 1);
            
            let mut counter = tail.as_ref().counter.load(Ordering::Relaxed);
            assert_ne!(counter, 0);

            counter = counter.saturating_sub(discovered);
            if counter == 0 {
                self.complete();
                return true;
            }

            tail.as_ref().counter.store(counter, Ordering::Relaxed);
            match self.state.compare_exchange_weak(
                state,
                state & !UPDATING,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return false,
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn complete(&self) {
        let state = self.state.swap(COMPLETED, Ordering::AcqRel);
        assert_ne!(state, COMPLETED);
        assert_ne!(state & QUEUED, 0);
        assert_ne!(state & UPDATING, 0);

        let mut waiters = NonNull::new((state & Waiter::MASK) as *mut Waiter);
        while let Some(waiter) = waiters {
            waiters = waiter.as_ref().next.get();
            waiter.as_ref().unpark();
        }
    }
}

#[derive(Default, Copy, Clone)]
pub struct BarrierWaitResult {
    is_leader: bool,
}

impl BarrierWaitResult {
    const fn is_leader(&self) -> bool {
        self.is_leader
    }
}