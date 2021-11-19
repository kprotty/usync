use once_cell::sync::OnceCell;
use std::{
    cell::RefCell,
    collections::{btree_map::Entry, BTreeMap},
    mem::drop,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
    sync::{Arc, Mutex},
    thread::{self, Thread},
    time::Instant,
};

struct Waiter {
    thread: Thread,
    token: AtomicUsize,
    queued: AtomicBool,
    notified: AtomicBool,
    address: AtomicUsize,
}

impl Waiter {
    fn with<F>(f: impl FnOnce(&Arc<Self>) -> F) -> F {
        thread_local!(static TLS_WAITER: Arc<Waiter> = Arc::new(Waiter {
            thread: thread::current(),
            token: AtomicUsize::new(0),
            queued: AtomicBool::new(false),
            notified: AtomicBool::new(false),
            address: AtomicUsize::new(0),
        }));
        TLS_WAITER.with(f)
    }

    fn wait(&self, deadline: Option<Instant>) -> bool {
        loop {
            if self.notified.load(Ordering::Acquire) {
                return true;
            }

            match deadline {
                None => thread::park(),
                Some(deadline) => match deadline.checked_duration_since(Instant::now()) {
                    Some(timeout) => thread::park_timeout(timeout),
                    None => return false,
                },
            }
        }
    }

    fn wake(&self) {
        self.notified.store(true, Ordering::Release);
        self.thread.unpark();
    }
}

type Queue = Vec<Arc<Waiter>>;

#[derive(Default)]
struct State {
    tree: RefCell<BTreeMap<usize, Queue>>,
    cache: RefCell<Vec<Queue>>,
}

impl State {
    fn insert(&self, address: usize, waiter: &Arc<Waiter>) {
        waiter.notified.store(false, Ordering::Relaxed);
        waiter.queued.store(true, Ordering::Relaxed);
        waiter.address.store(address, Ordering::Relaxed);

        match self.tree.borrow_mut().entry(address) {
            Entry::Occupied(mut entry) => {
                entry.get_mut().push(waiter.clone());
            }
            Entry::Vacant(entry) => {
                entry.insert(self.alloc_queue()).push(waiter.clone());
            }
        }
    }

    fn try_remove(&self, address: usize, waiter: &Arc<Waiter>) -> Option<Arc<Waiter>> {
        if !waiter.queued.load(Ordering::Relaxed) {
            return None;
        }

        match self.tree.borrow_mut().entry(address) {
            Entry::Vacant(_) => unreachable!("Waiter queued without a wait queue"),
            Entry::Occupied(mut entry) => {
                let mut removed = None;
                for index in 0..entry.get().len() {
                    if Arc::ptr_eq(waiter, &entry.get()[index]) {
                        removed = Some(entry.get_mut().swap_remove(index));
                        break;
                    }
                }

                if entry.get().len() == 0 {
                    self.free_queue(entry.remove());
                }

                let removed = removed.expect("Waiter queued without being in wait queue");
                waiter.queued.store(false, Ordering::Relaxed);
                Some(removed)
            }
        }
    }

    fn drain_into(
        &self,
        address: usize,
        drain_queue: &mut Queue,
        mut filter: impl FnMut(usize) -> Option<usize>,
    ) -> bool {
        if let Entry::Occupied(mut entry) = self.tree.borrow_mut().entry(address) {
            for _ in 0..entry.get().len() {
                let token = entry.get()[0].token.load(Ordering::Relaxed);
                let token = match filter(token) {
                    Some(token) => token,
                    None => break,
                };

                let waiter = entry.get_mut().swap_remove(0);
                waiter.queued.store(false, Ordering::Relaxed);
                waiter.token.store(token, Ordering::Relaxed);
                drain_queue.push(waiter);
            }

            if entry.get().len() > 0 {
                return true;
            } else {
                self.free_queue(entry.remove());
            }
        }

        false
    }

    fn alloc_queue(&self) -> Queue {
        let mut cache = self.cache.borrow_mut();
        let index = cache.len().checked_sub(1);
        index.map(|i| cache.swap_remove(i)).unwrap_or(Queue::new())
    }

    fn free_queue(&self, queue: Queue) {
        let mut cache = self.cache.borrow_mut();
        if cache.len() < 64 {
            cache.push(queue);
        }
    }
}

#[derive(Default)]
struct Bucket {
    state: Mutex<State>,
}

impl Bucket {
    fn from(address: usize) -> &'static Bucket {
        const NUM_BUCKETS: usize = 64;
        static BUCKETS: OnceCell<Box<[Bucket]>> = OnceCell::new();
        let buckets = BUCKETS.get_or_init(|| (0..NUM_BUCKETS).map(|_| Bucket::default()).collect());

        #[cfg(target_pointer_width = "64")]
        const HASH_MULT: usize = 0x9E3779B97F4A7C15;
        #[cfg(target_pointer_width = "32")]
        const HASH_MULT: usize = 0x9E3779B9;

        let hash = address.wrapping_mul(HASH_MULT);
        let index = hash % NUM_BUCKETS;
        &buckets[index]
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum WaitResult {
    Invalidated,
    TimedOut,
    Notified(usize),
}

pub fn wait(
    address: usize,
    validate: impl FnOnce() -> bool,
    deadline: Option<Instant>,
) -> WaitResult {
    let validate_fn = || match validate() {
        true => Some(0),
        false => None,
    };

    wait_with(address, validate_fn, deadline)
}

pub fn wait_with(
    address: usize,
    validate: impl FnOnce() -> Option<usize>,
    deadline: Option<Instant>,
) -> WaitResult {
    let bucket = Bucket::from(address);
    let state = bucket.state.lock().unwrap();

    let token = match validate() {
        Some(token) => token,
        None => return WaitResult::Invalidated,
    };

    Waiter::with(|waiter| {
        waiter.token.store(token, Ordering::Relaxed);
        state.insert(address, waiter);
        drop(state);

        if waiter.wait(deadline) {
            let token = waiter.token.load(Ordering::Relaxed);
            return WaitResult::Notified(token);
        }

        let state = bucket.state.lock().unwrap();
        let removed = state.try_remove(address, waiter);
        drop(state);

        if let Some(_removed) = removed {
            return WaitResult::TimedOut;
        }

        waiter.wait(None);
        let token = waiter.token.load(Ordering::Relaxed);
        WaitResult::Notified(token)
    })
}

pub fn wake_filter(
    address: usize,
    filter: impl FnMut(usize) -> Option<usize>,
    before_wake: impl FnOnce(bool),
) {
    thread_local!(static NOTIFIED: RefCell<Queue> = RefCell::new(Queue::new()));
    NOTIFIED.with(|notified| {
        let mut notified = notified.borrow_mut();

        let bucket = Bucket::from(address);
        let state = bucket.state.lock().unwrap();

        let has_more = state.drain_into(address, &mut *notified, filter);
        before_wake(has_more);
        drop(state);

        for waiter in notified.drain(..) {
            waiter.wake();
        }
    });
}

pub fn wake(address: usize, max_wake: usize) {
    let mut n = max_wake;
    if n == 0 {
        return;
    }

    let filter = |token: usize| {
        n.checked_sub(1).map(|new_n| {
            n = new_n;
            token
        })
    };

    wake_filter(address, filter, |_has_more: bool| {});
}
