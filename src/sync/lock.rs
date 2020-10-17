// Copyright (c) 2020 kprotty
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#[cfg(target_atomic_u8)]
use crate::utils::sync::AtomicU8;
use crate::{
    parker::Parker,
    utils::{
        sync::{fence, AtomicUsize, Ordering, UnsafeCell},
        waiter::Node as WaiterNode,
        SpinWait, WakerParker,
    },
};
use core::{
    fmt,
    future::Future,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::NonNull,
    task::{Context, Poll},
};

const UNLOCKED: u8 = 0;
const LOCKED: u8 = 1;

#[cfg(not(target_atomic_u8))]
const WAKING: usize = 2;
#[cfg(target_atomic_u8)]
const WAKING: usize = 256;

#[cfg(not(target_atomic_u8))]
const WAITING: usize = !3;
#[cfg(target_atomic_u8)]
const WAITING: usize = !511;

#[cfg_attr(not(target_atomic_u8), repr(C, align(4)))]
#[cfg_attr(target_atomic_u8, repr(C, align(512)))]
struct LockWaiter(WaiterNode<WakerParker>);

/// A mutual exclusioin primitive useful for protecting shared data.
///
/// This Lock uses a barging/unfair acquire scheme and is throughput oriented.
/// While this increases the lock's general performance, there is still the theoretical possibility of a live-lock.
/// Other restrictions also include the lack of cancellation for [`LockFuture`] which allows for more optimizations.
///
/// Most times, this is not the mutex that you should be using unless you are writing your own synchronization
/// primitives which aim to have specific attributes. If so, this throughput oriented mutex could be the right
/// fit with the following advantages:
///
/// * it fits in an `AtomicUsize`
/// * it supports `const fn` initialization
/// * it supports both async & thread blocking via [`Parker`]
/// * it scales almost linearly under condition on modern OS's
pub struct Lock<T> {
    state: AtomicUsize,
    value: UnsafeCell<T>,
}

unsafe impl<T: Send> Send for Lock<T> {}
unsafe impl<T: Send> Sync for Lock<T> {}

impl<T: Default> Default for Lock<T> {
    fn default() -> Self {
        Self::from(T::default())
    }
}

impl<T> From<T> for Lock<T> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

impl<T> AsMut<T> for Lock<T> {
    fn as_mut(&mut self) -> &mut T {
        self.value.with_mut(|ptr| unsafe { &mut *ptr })
    }
}

impl<T: fmt::Debug> fmt::Debug for Lock<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_struct("Lock");
        let f = if let Some(guard) = self.try_lock() {
            f.field("value", &&*guard)
        } else {
            f.field("state", &"<locked>")
        };
        f.finish()
    }
}

impl<T> Lock<T> {
    /// Create a new Lock in an unlocked state.
    pub const fn new(value: T) -> Self {
        Self {
            state: AtomicUsize::new(UNLOCKED as usize),
            value: UnsafeCell::new(value),
        }
    }

    /// Consumes the mutex and returns the underlying value.
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }

    /// Returns true if the Lock is currently owned by a thread.
    #[inline]
    pub fn is_locked(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        state & (LOCKED as usize) != 0
    }

    /// For platforms which support byte-level atomics,
    /// get a reference to the state as an AtomicU8 as opposed to an AtomicUsize.
    #[cfg(target_atomic_u8)]
    fn byte_state(&self) -> &AtomicU8 {
        use core::mem::size_of;
        assert!(
            size_of::<AtomicU8>() <= size_of::<AtomicUsize>(),
            "AtomicU8 is larger than AtomicUsize for this platform",
        );
        assert!(
            size_of::<AtomicU8>() <= size_of::<u8>(),
            "AtomicU8 for this platform does not fit in a u8",
        );
        unsafe { &*(&self.state as *const _ as *const _) }
    }

    /// Try to acquire the Lock in a non-blocking manner.
    #[cfg(target_atomic_u8)]
    #[inline(always)]
    pub fn try_lock(&self) -> Option<LockGuard<'_, T>> {
        // On platforms which support byte level atomics
        // we can swap the lower byte of the state in order to acquire the lock.
        // This is because all the state queueing happens in the bits above the lower byte
        // meaning that this operation doesn't have to race against queueing LockWaiters.
        //
        // In general (x86, ARM, riscv) a swap() as opposed to a compare_exchange()
        // less code which incurs less of a hit on the instruction cache when inlined.
        match self.byte_state().swap(LOCKED, Ordering::Acquire) {
            UNLOCKED => Some(LockGuard::new(self)),
            _ => None,
        }
    }

    /// Try to acquire the Lock in a non-blocking manner.
    #[cfg(not(target_atomic_u8))]
    #[inline]
    pub fn try_lock(&self) -> Option<LockGuard<'_, T>> {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if state & (LOCKED as usize) != 0 {
                return None;
            }
            match self.state.compare_exchange_weak(
                state,
                state | (LOCKED as usize),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Some(LockGuard::<'_, T>::new(self)),
                Err(e) => state = e,
            }
        }
    }

    /// `lock*()` fast path - tries to acquire the lock assuming no contention.
    #[cfg(target_atomic_u8)]
    #[inline(always)]
    fn lock_fast(&self) -> Option<LockGuard<'_, T>> {
        // For platforms which support byte-level atomics or use custom assembly,
        // using the custom code will be faster than compare exchange in some desirable metric.
        self.try_lock()
    }

    /// `lock*()` fast path - tries to acquire the lock assuming no contention.
    #[cfg(not(target_atomic_u8))]
    #[inline(always)]
    fn lock_fast(&self) -> Option<LockGuard<'_, T>> {
        // For normal platforms, a compare exchange works well and is near the perf of spinlocks.
        // The compare exchange can fail spuriously as the lock algorithm will try again in the slow path.
        self.state
            .compare_exchange_weak(
                UNLOCKED as usize,
                LOCKED as usize,
                Ordering::Acquire,
                Ordering::Relaxed,
            )
            .ok()
            .map(|_| LockGuard { lock: self })
    }

    /// Returns a [`Future`] which acquires the `Lock`.
    pub fn lock_async<P: Parker>(&self) -> LockFuture<'_, P, T> {
        LockFuture::new(match self.lock_fast() {
            Some(guard) => LockFutureState::Acquired(guard),
            None => LockFutureState::Locking {
                lock: self,
                is_waking: false,
            },
        })
    }

    /// Acquires the `Lock`, blocking the current thread using
    /// and instance of the provided [`Parker`] until it is able to take ownership.
    #[inline]
    pub fn lock<P: Parker>(&self) -> LockGuard<'_, T> {
        self.lock_fast().unwrap_or_else(|| self.lock_slow::<P>())
    }

    #[cold]
    fn lock_slow<P: Parker>(&self) -> LockGuard<'_, T> {
        let parker = P::new();
        let waker = unsafe { WakerParker::of(&parker) };

        let mut ctx = Context::from_waker(&waker);
        let mut future = LockFuture::<'_, P, T>::new(LockFutureState::Locking {
            lock: self,
            is_waking: false,
        });

        loop {
            let pinned = unsafe { Pin::new_unchecked(&mut future) };
            match pinned.poll(&mut ctx) {
                Poll::Ready(guard) => return guard,
                Poll::Pending => parker.park(),
            }
        }
    }

    /// Unlocks the Lock and potentially wakes up any LockWaiter waiting on the lock.
    ///
    /// # Safety
    ///
    /// This assumes that the caller has ownership of the lock
    /// and is exposed for finer-grain control such as in a C-ffi setting.
    #[cfg(not(target_atomic_u8))]
    #[inline]
    pub unsafe fn unlock(&self) {
        // Unlock the Lock using a fetch_sub as opposed to a fetch_and.
        // The former can be done in a wait-free manner on x86 cpus using the `xadd` instruction.
        let state = self.state.fetch_sub(LOCKED as usize, Ordering::Release);

        // Go to the slow path to wake up a waiting LockWaiter
        // if there are any queued LockWaiters and
        // if one isn't currently in the process of waking up.
        if (state & WAITING != 0) && (state & WAKING == 0) {
            self.unlock_slow();
        }
    }

    /// Unlocks the Lock and potentially wakes up any LockWaiter waiting on the lock.
    ///
    /// # Safety
    ///
    /// This assumes that the caller has ownership of the lock
    /// and is exposed for finer-grain control such as in a C-ffi setting.
    #[cfg(target_atomic_u8)]
    #[inline]
    pub unsafe fn unlock(&self) {
        // Unlock the Lock using an atomic store as opposed to usize
        // a read-modify-write operation like above, which is generally faster.
        //
        // This is possible due to the LockWaiter queue bits residing in the bits
        // above the lower byte meaning the lower byte can be entirely cleared out.
        self.byte_state().store(UNLOCKED, Ordering::Release);

        // Go to the slow path to wake up a waiting LockWaiter
        // if there are any queued LockWaiters,
        // if one isn't currently in the process of waking up and
        // if the Lock isn't currently locked as the lock-holder can take care of the wake-up.
        let state = self.state.load(Ordering::Relaxed);
        if (state & WAITING != 0) && (state & (WAKING | (LOCKED as usize)) == 0) {
            self.unlock_slow();
        }
    }

    #[cold]
    fn unlock_slow(&self) {
        // Try to acquire the rights to waking up a waiting thread which will retry acquiring the lock.
        //
        // If there are no waiting threads then we bail.
        // If theres already a thread waking, no need to wake another, so we bail.
        // If the Lock is currently owned by another thread, bail and have that other thread do the waking.
        //
        // See the 'dequeue loop comment for justification about the Acquire success ordering.
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            if (state & WAITING == 0) || (state & (WAKING | (LOCKED as usize)) != 0) {
                return;
            }
            match self.state.compare_exchange_weak(
                state,
                state | WAKING,
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                Ok(_) => break state |= WAKING,
                Err(e) => state = e,
            }
        }

        'dequeue: loop {
            // Starting from the head WaiterNode of the queue,
            // traverse the doubly-linked list queue until a node with a set tail is found.
            // The first node to enqueue itself sets the tail so the loop is eventually bounded.
            //
            // Once the tail is found, cache it on the head node so that future traversals
            // don't have to re-trace the queue again, effectively making this traversal
            // amortized O(n) where n = amount of LockWaiters/WaiterNode's in the queue.
            //
            // # Safety:
            //
            // There exist an acquire barrier when control flow reaches this point
            // so the head/tail reads here synchronize with any Release updates
            // done by the previous `unlock_slow()` thread.
            //
            // We also acquired ownership of the `WAKING` bit above and ensured that
            // there is at least one thread in the queue for us to dequeue & wake up.
            let (head, tail) = unsafe {
                let head = NonNull::new((state & WAITING) as *mut LockWaiter);
                let head = head.expect("Lock::unlock_slow() without any LockWaiters");
                let head = NonNull::from(&head.as_ref().0);

                let tail = head.as_ref().tail.get().unwrap_or_else(|| {
                    let mut current = head;
                    loop {
                        let next = current.as_ref().next.get();
                        let next = next.expect("Lock::unlock_slow() invalid link");
                        next.as_ref().prev.set(Some(current));
                        current = next;
                        if let Some(tail) = current.as_ref().tail.get() {
                            head.as_ref().tail.set(Some(tail));
                            break tail;
                        }
                    }
                });

                (
                    &*head.cast::<LockWaiter>().as_ptr(),
                    &*tail.cast::<LockWaiter>().as_ptr(),
                )
            };

            // If the `Lock` is currently owned by another thread,
            // its better to have that thread do the waking instead.
            //
            // Release barrier on success so future `unlock_slow()` threads see the head/tail writes we did above.
            // Acquire barrier on re-loop as explained in the 'dequeue loop comment.
            if state & (LOCKED as usize) != 0 {
                match self.state.compare_exchange_weak(
                    state,
                    state & !WAKING,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    Ok(_) => return,
                    Err(e) => state = e,
                }
                fence(Ordering::Acquire);
                continue;
            }

            // Try to dequeue the tail node
            match tail.0.prev.replace(None) {
                // If there are more nodes than the tail in the queue,
                // then update the head to point to the new tail, effectively dequeueing ours.
                //
                // Release ordering to synchronize the head write as explained in the `dequeue loop commment.
                Some(new_tail) => {
                    head.0.tail.set(Some(new_tail));
                    fence(Ordering::Release);
                }
                // If the queue will be empty after dequeueing the tail node,
                // then zero out the head node which effectively marks the queue as empty.
                //
                // If a new node was enqueued when we were trying to zero out the head node,
                // then the new node may point to the tail we're trying to dequeue so we have
                // to loop back around again to do the dequeue process and ensure the links remain valid.
                //
                // Acquire ordering as explained from the `dequeue loop comment
                None => loop {
                    match self.state.compare_exchange_weak(
                        state,
                        (state & (LOCKED as usize)) | WAKING,
                        Ordering::Relaxed,
                        Ordering::Relaxed,
                    ) {
                        Ok(_) => break,
                        Err(e) => state = e,
                    }
                    if state & WAITING != 0 {
                        fence(Ordering::Acquire);
                        continue 'dequeue;
                    }
                },
            }

            // We successfully dequeued the tail node from the wait queue.
            // Wake up its waiter which will try to acquire the lock again.
            tail.0.with(|waker_parker_ptr| unsafe {
                let waker_parker = &*waker_parker_ptr;
                if let Some(waker) = waker_parker.unpark(0) {
                    waker.wake();
                }
            });

            return;
        }
    }
}

enum LockFutureState<'a, T> {
    Locking { lock: &'a Lock<T>, is_waking: bool },
    Waiting(&'a Lock<T>),
    Acquired(LockGuard<'a, T>),
    Completed,
}

/// A Future which blocks until the Lock is acquired.
///
/// This type does not support cancellation.
#[must_use = "LockFuture will not try to acquire the lock unless polled"]
pub struct LockFuture<'a, P, T> {
    state: LockFutureState<'a, T>,
    waiter: LockWaiter,
    _parker: PhantomData<*mut P>,
}

impl<'a, P, T> Drop for LockFuture<'a, P, T> {
    fn drop(&mut self) {
        if let LockFutureState::Waiting(_) = self.state {
            unreachable!("LockFuture does not support cancellation");
        }
    }
}

unsafe impl<'a, P, T: Send> Send for LockFuture<'a, P, T> {}

impl<'a, P, T: fmt::Debug> fmt::Debug for LockFuture<'a, P, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LockFuture")
            .field(
                "state",
                &match &self.state {
                    LockFutureState::Locking { .. } => "<locking>",
                    LockFutureState::Waiting(_) => "<waiting>",
                    LockFutureState::Acquired(_) => "<acquired>",
                    LockFutureState::Completed => "<completed>",
                },
            )
            .finish()
    }
}

impl<'a, P: Parker, T> Future for LockFuture<'a, P, T> {
    type Output = LockGuard<'a, T>;

    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        // Safety: Pin promises that the access to the LockFuture is safe
        // as we don't move the WaiterNode or this future until its dropped.
        let mut_self = unsafe { Pin::get_unchecked_mut(self) };

        loop {
            match &mut_self.state {
                LockFutureState::Locking { lock, is_waking } => {
                    match Self::poll_lock(lock, *is_waking, ctx, &mut_self.waiter) {
                        Poll::Ready(guard) => mut_self.state = LockFutureState::Acquired(guard),
                        Poll::Pending => {
                            mut_self.state = LockFutureState::Waiting(lock);
                            return Poll::Pending;
                        }
                    }
                }
                LockFutureState::Waiting(lock) => match Self::poll_wait(ctx, &mut_self.waiter) {
                    Poll::Ready(_) => {
                        mut_self.state = LockFutureState::Locking {
                            lock,
                            is_waking: true,
                        };
                    }
                    Poll::Pending => return Poll::Pending,
                },
                LockFutureState::Acquired(_) => {
                    match core::mem::replace(&mut mut_self.state, LockFutureState::Completed) {
                        LockFutureState::Acquired(guard) => return Poll::Ready(guard),
                        _ => unreachable!(),
                    }
                }
                LockFutureState::Completed => {
                    unreachable!("LockFuture polled after completion");
                }
            }
        }
    }
}

impl<'a, P: Parker, T> LockFuture<'a, P, T> {
    fn new(state: LockFutureState<'a, T>) -> Self {
        Self {
            state,
            waiter: LockWaiter(WaiterNode::new(WakerParker::new())),
            _parker: PhantomData,
        }
    }

    #[cfg(target_atomic_u8)]
    #[inline(always)]
    fn lock_acquire(lock: &'a Lock<T>, _state: usize) -> Result<LockGuard<'a, T>, usize> {
        lock.try_lock().ok_or_else(|| {
            P::yield_now(None);
            lock.state.load(Ordering::Relaxed)
        })
    }

    #[cfg(not(target_atomic_u8))]
    #[inline(always)]
    fn lock_acquire(lock: &'a Lock<T>, state: usize) -> Result<LockGuard<'a, T>, usize> {
        lock.state
            .compare_exchange_weak(
                state,
                state | (LOCKED as usize),
                Ordering::Acquire,
                Ordering::Relaxed,
            )
            .map(|_| LockGuard::new(lock))
            .map_err(|_| {
                P::yield_now(None);
                lock.state.load(Ordering::Relaxed)
            })
    }

    fn poll_lock(
        lock: &'a Lock<T>,
        is_waking: bool,
        ctx: &Context<'_>,
        waiter: &LockWaiter,
    ) -> Poll<LockGuard<'a, T>> {
        let mut spin_wait = SpinWait::<P>::new();
        let mut state = if is_waking {
            lock.state.fetch_sub(WAKING, Ordering::Relaxed) - WAKING
        } else {
            lock.state.load(Ordering::Relaxed)
        };

        loop {
            if state & (LOCKED as usize) == 0 {
                match Self::lock_acquire(lock, state) {
                    Ok(guard) => return Poll::Ready(guard),
                    Err(e) => state = e,
                }
                continue;
            }

            let head = NonNull::new((state & WAITING) as *mut LockWaiter);
            if head.is_none() && spin_wait.try_spin() {
                state = lock.state.load(Ordering::Relaxed);
                continue;
            }

            unsafe {
                waiter.0.with_mut(|waker_parker_ptr| {
                    (&mut *waker_parker_ptr).prepare(ctx);
                });
                waiter
                    .0
                    .next
                    .set(head.map(|head_ptr| head_ptr.cast::<WaiterNode<WakerParker>>()));
                waiter.0.tail.set(match head {
                    Some(_) => None,
                    None => Some(NonNull::from(&waiter.0)),
                });
            }

            match lock.state.compare_exchange_weak(
                state,
                (state & !WAITING) | (waiter as *const _ as usize),
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return Poll::Pending,
                Err(e) => state = e,
            }
        }
    }

    fn poll_wait(ctx: &Context<'_>, waiter: &LockWaiter) -> Poll<()> {
        waiter.0.with(|waker_parker_ptr| unsafe {
            match (&*waker_parker_ptr).park(ctx) {
                Poll::Ready(0) => Poll::Ready(()),
                Poll::Ready(t) => unreachable!("invalid waker notification token {}", t),
                Poll::Pending => Poll::Pending,
            }
        })
    }
}

/// A RAII based implementation of a scoped lock for the [`Lock`] mutex.
/// When it is dropped, the mutex is unlocked.
///
/// The internal data protected by the mutex can be accessed through
/// `Deref` and `DerefMut` from this type.
pub struct LockGuard<'a, T> {
    lock: &'a Lock<T>,
}

impl<'a, T> LockGuard<'a, T> {
    fn new(lock: &'a Lock<T>) -> Self {
        Self { lock }
    }
}

impl<'a, T> Drop for LockGuard<'a, T> {
    fn drop(&mut self) {
        // Safety: our existence implies lock ownership of the Lock
        unsafe { self.lock.unlock() }
    }
}

impl<'a, T: fmt::Debug> fmt::Debug for LockGuard<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (&&*self).fmt(f)
    }
}

impl<'a, T> Deref for LockGuard<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        // Safety: our existence implies ownership of the Lock's value
        self.lock.value.with(|ptr| unsafe { &*ptr })
    }
}

impl<'a, T> DerefMut for LockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        // Safety: our existence implies ownership of the Lock's value
        self.lock.value.with_mut(|ptr| unsafe { &mut *ptr })
    }
}

#[cfg(feature = "lock_api")]
pub use if_lock_api::*;

#[cfg(feature = "lock_api")]
mod if_lock_api {
    use super::{Lock, Parker, PhantomData};

    pub struct RawLock<P> {
        lock: Lock<()>,
        _parker: PhantomData<P>,
    }

    unsafe impl<P: Parker> lock_api::RawMutex for RawLock<P> {
        type GuardMarker = lock_api::GuardSend;

        const INIT: Self = Self {
            lock: Lock::new(()),
            _parker: PhantomData,
        };

        fn is_locked(&self) -> bool {
            self.lock.is_locked()
        }

        fn try_lock(&self) -> bool {
            self.lock
                .try_lock()
                .map(|guard| {
                    core::mem::drop(guard);
                    true
                })
                .unwrap_or(false)
        }

        fn lock(&self) {
            self.lock.lock::<P>();
        }

        unsafe fn unlock(&self) {
            self.lock.unlock();
        }
    }
}
