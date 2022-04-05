use crate::shared::{CacheAligned, Parker, StrictProvenance};
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
    disconnected: AtomicBool,
}

struct Consumer<T> {
    block: AtomicPtr<Block<T>>,
    index: Cell<usize>,
    disconnected: AtomicBool,
    parker: Parker,
}

pub(crate) struct Queue<T> {
    producer: CacheAligned<Producer<T>>,
    consumer: CacheAligned<Consumer<T>>,
}

unsafe impl<T: Send> Send for Queue<T> {}
unsafe impl<T: Send> Sync for Queue<T> {}

impl<T> Queue<T> {
    pub(crate) const fn new() -> Self {
        Self {
            producer: CacheAligned(Producer {
                block_and_index: AtomicPtr::new(ptr::null_mut()),
                disconnected: AtomicBool::new(false),
            }),
            consumer: CacheAligned(Consumer {
                block: AtomicPtr::new(ptr::null_mut()),
                index: Cell::new(0),
                disconnected: AtomicBool::new(false),
                parker: Parker::new(),
            }),
        }
    }

    pub(crate) fn send(&self, item: T) -> Result<(), T> {
        unimplemented!("TODO")
    }

    pub(crate) unsafe fn try_recv(&self) -> Result<Option<T>, ()> {
        unimplemented!("TODO")
    }

    pub(crate) unsafe fn recv(&self, timeout: Option<Duration>) -> Result<Option<T>, ()> {
        unimplemented!("TODO")
    }

    pub(crate) fn disconnect(&self, is_sender: bool) {
        unimplemented!("TODO")
    }
}
