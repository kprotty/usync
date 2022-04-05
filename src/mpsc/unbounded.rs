use crate::shared::{CacheAligned, Parker, SpinWait, StrictProvenance};
use std::{
    cell::{Cell, UnsafeCell},
    mem::{drop, MaybeUninit},
    ptr::{self, NonNull},
    sync::atomic::{AtomicBool, AtomicPtr, Ordering},
    time::Duration,
};

struct Value<T>(UnsafeCell<MaybeUninit<T>>);

impl<T> Value<T> {
    const EMPTY: Self = Self(UnsafeCell::new(MaybeUninit::uninit()));

    unsafe fn write(&self, value: T) {
        self.0.get().write(MaybeUninit::new(value))
    }

    unsafe fn read(&self) -> T {
        self.0.get().read().assume_init()
    }
}

const BLOCK_SIZE: usize = 32;
const BLOCK_MASK: usize = BLOCK_SIZE - 1;

#[repr(align(32))]
struct Block<T> {
    values: [Value<T>; BLOCK_SIZE],
    stored: [AtomicBool; BLOCK_SIZE],
    next: AtomicPtr<Self>,
}

impl<T> Block<T> {
    const UNSTORED: AtomicBool = AtomicBool::new(false);
    const EMPTY: Self = Self {
        values: [Value::<T>::EMPTY; BLOCK_SIZE],
        stored: [Self::UNSTORED; BLOCK_SIZE],
        next: AtomicPtr::new(ptr::null_mut()),
    };
}

struct Producer<T> {
    block_and_index: AtomicPtr<Block<T>>,
}

struct Consumer<T> {
    block: AtomicPtr<Block<T>>,
    index: Cell<usize>,
}

struct Shared {
    disconnected: AtomicBool,
    parker: Parker,
}

pub(crate) struct Queue<T> {
    producer: CacheAligned<Producer<T>>,
    consumer: CacheAligned<Consumer<T>>,
    shared: CacheAligned<Shared>,
}

unsafe impl<T: Send> Send for Queue<T> {}
unsafe impl<T: Send> Sync for Queue<T> {}

impl<T> Queue<T> {
    pub(crate) const fn new() -> Self {
        Self {
            producer: CacheAligned(Producer {
                block_and_index: AtomicPtr::new(ptr::null_mut()),
            }),
            consumer: CacheAligned(Consumer {
                block: AtomicPtr::new(ptr::null_mut()),
                index: Cell::new(0),
            }),
            shared: CacheAligned(Shared {
                disconnected: AtomicBool::new(false),
                parker: Parker::new(),
            }),
        }
    }

    pub(crate) fn send(&self, item: T) -> Result<(), T> {
        let mut backoff = SpinWait::default();
        let mut next_block = ptr::null_mut::<Block<T>>();

        loop {
            if self.shared.disconnected.load(Ordering::Relaxed) {
                if !next_block.is_null() {
                    drop(unsafe { Box::from_raw(next_block) });
                }

                return Err(item);
            }

            let block_and_index = self.producer.block_and_index.load(Ordering::Relaxed);
            let block = block_and_index.map_addr(|addr| addr & !BLOCK_MASK);
            let index = block_and_index.addr() & BLOCK_MASK;

            let mut new_block = block;
            let mut new_index = (index + 1) & BLOCK_MASK;

            if block.is_null() || new_index == 0 {
                if next_block.is_null() {
                    next_block = Box::into_raw(Box::new(Block::EMPTY));
                }

                debug_assert!(!next_block.is_null());
                new_block = next_block;
            }

            if let Err(_) = self.producer.block_and_index.compare_exchange(
                block_and_index,
                new_block.map_addr(|addr| addr | new_index),
                Ordering::AcqRel,
                Ordering::Relaxed,
            ) {
                backoff.yield_now();
                continue;
            }

            return Ok(unsafe {
                if block.is_null() {
                    debug_assert!(!new_block.is_null());
                    block = new_block;

                    debug_assert!(self.consumer.block.load(Ordering::Relaxed).is_null());
                    self.consumer.block.store(block, Ordering::Release);
                }

                if new_index == 0 {
                    debug_assert!(!block.is_null());
                    debug_assert!(!new_block.is_null());

                    debug_assert!((*block).next.load(Ordering::Relaxed).is_null());
                    (*block).next.store(new_block, Ordering::Release);
                }

                if !next_block.is_null() && !ptr::eq(next_block, new_block) {
                    drop(Box::from_raw(next_block));
                }

                // FIXME (maybe): This could be a case of https://github.com/rust-lang/rust/issues/55005.
                // Once the last slot is stored, the consumer could read it and possibly dealloc
                // it's block before we return. This could potentially have a dangling ref to &block.stored[-1].
                (*block).values.get_unchecked(index).write(item);
                (*block).stored.get_unchecked(index).store(true, Ordering::Release);
            });
        }
    }

    pub(crate) unsafe fn try_recv(&self) -> Result<Option<T>, ()> {
        // This `loop` is just used as a labeled block since those are still unstable after years...
        loop {
            // Check if the producer has set the first block for us yet.
            // Acquire barrier ensures the producer's block alloc/initialization happens before we observe it.
            let mut block = self.consumer.block.load(Ordering::Acquire);
            if block.is_null() {
                break;
            }

            // Get the current index into the block to try and read from.
            // Once we reach the end, check if there's a `next` block to read from instead.
            let mut index = self.consumer.index.get();
            if index == BLOCK_SIZE {
                // Acquire barrier ensures the producer's new block alloc/initialization happens before we observe it.
                let next_block = (*block).next.load(Ordering::Acquire);
                if next_block.is_null() {
                    break;
                }

                // Deallocate the old block and start with the newly discovered one.
                drop(Box::from_raw(block));
                block = next_block;
                index = 0;

                self.consumer.block.store(block, Ordering::Relaxed);
                self.consumer.index.set(index);
            }

            // Check if the producer has stored a value at this slot yet.
            // Acquire barrier ensures the producer's `values` write happens before we observe `stored` as true.
            if !(*block).stored.get_unchecked(index).load(Ordering::Acquire) {
                break;
            }
                
            let value = (*block).values.get_unchecked(index).read();
            self.consumer.index.set(index + 1);
            return Ok(value);
        }

        // Before we report empty, check if the queue was disconnected by a sender.
        if self.shared.disconnected.load(Ordering::Relaxed) {
            return Err(());
        }

        Ok(None)
    }

    pub(crate) unsafe fn recv(&self, timeout: Option<Duration>) -> Result<Option<T>, ()> {
        // Poll the queue once to try and get a value or check for disconnected.
        if let Some(value) = self.try_recv()? {
            return Ok(Some(value));
        }

        // Nothing was immediately available, so wait until notified by send() or disconnect().
        let timed_out = !self.shared.parker.park(timeout);

        // Check the queue again for a new value or disconnect after waking up.
        if let Some(value) = self.try_recv()? {
            return Ok(Some(value));
        }

        assert!(timed_out, "receiver unparked with the queue being empty");
        Ok(None)
    }

    pub(crate) fn disconnect(&self, is_sender: bool) {
        if !self.shared.disconnected.load(Ordering::Relaxed) {
            self.shared.disconnected.store(true, Ordering::Relaxed);

            // Wake up the receiver for it to observe disconnected.
            // This internally is a Release barrier.
            if is_sender {
                self.shared.parker.unpark();
            }
        }
    }
}

impl<T> Drop for Queue<T> {
    fn drop(&mut self) {
        // Safety: we're the only thread using the queue (mut self)
        // so we're allowed to call the receive methods and deallocate.
        unsafe {
            // Drain the queue values and drop them each
            while let Ok(Some(value)) = self.try_recv() {
                drop(value);
            }

            // Deallocate the current block if any.
            // No need for Acquire barrier as that would've happened in try_recv().
            let block = self.consumer.block.load(Ordering::Relaxed);
            if !block.is_null() {
                debug_assert!((*block).next.load(Ordering::Relaxed).is_null());
                drop(Box::from_raw(block));
            }
        }
    }
}
