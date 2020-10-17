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

use crate::{
    parker::Parker,
    utils::sync::{Ordering, UnsafeCell},
};
use core::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

#[cfg(target_atomic_u8)]
use super::sync::AtomicU8;
#[cfg(not(target_atomic_u8))]
use super::sync::AtomicUsize as AtomicU8;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum WakerState {
    Waiting,
    Updating,
    Consuming,
    Notified(u8),
}

impl WakerState {
    #[cfg(target_atomic_u8)]
    fn decode(value: u8) -> Self {
        Self::decode_inner(value)
    }

    #[cfg(not(target_atomic_u8))]
    fn decode(value: usize) -> Self {
        use core::convert::TryInto;
        Self::decode_inner((value & 0xff).try_into().unwrap())
    }

    #[inline]
    fn decode_inner(value: u8) -> Self {
        match value & 0b11 {
            0 => Self::Waiting,
            1 => Self::Updating,
            2 => Self::Consuming,
            3 => Self::Notified(value >> 2),
            _ => unreachable!(),
        }
    }

    #[cfg(target_atomic_u8)]
    fn encode(self) -> u8 {
        self.encode_inner()
    }

    #[cfg(not(target_atomic_u8))]
    fn encode(self) -> usize {
        self.encode_inner() as usize
    }

    #[inline]
    fn encode_inner(self) -> u8 {
        match self {
            Self::Waiting => 0,
            Self::Updating => 1,
            Self::Consuming => 2,
            Self::Notified(token) => (token << 2) | 3,
        }
    }
}

pub(crate) struct WakerParker {
    state: AtomicU8,
    waker: UnsafeCell<Option<Waker>>,
}

impl WakerParker {
    pub(crate) fn new() -> Self {
        Self {
            state: AtomicU8::new(WakerState::Waiting.encode()),
            waker: UnsafeCell::new(None),
        }
    }

    pub(crate) fn prepare(&mut self, ctx: &Context<'_>) {
        // Safety: we own the self.waker from `&mut self`
        let is_waiting = self
            .waker
            .with_mut(|waker_ptr| unsafe { (&*waker_ptr).as_ref().is_some() });

        if !is_waiting {
            #[cfg(feature = "loom")]
            {
                self.state
                    .store(WakerState::Waiting.encode(), Ordering::Relaxed);
                self.waker.with_mut(|waker_ptr| unsafe {
                    *waker_ptr = Some(ctx.waker().clone());
                });
            }
            #[cfg(not(feature = "loom"))]
            {
                *self = Self {
                    state: AtomicU8::new(WakerState::Waiting.encode()),
                    waker: UnsafeCell::new(Some(ctx.waker().clone())),
                };
            }
        }
    }

    pub(crate) fn park(&self, ctx: &Context<'_>) -> Poll<u8> {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            match WakerState::decode(state) {
                WakerState::Waiting => {}
                WakerState::Updating => {
                    unreachable!("multiple threads trying to park on the same WakerParker");
                }
                WakerState::Consuming => {
                    return Poll::Pending;
                }
                WakerState::Notified(token) => {
                    return Poll::Ready(token);
                }
            }

            if let Err(e) = self.state.compare_exchange_weak(
                WakerState::Waiting.encode(),
                WakerState::Updating.encode(),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                state = e;
                continue;
            }

            self.waker.with_mut(|waker_ptr| unsafe {
                if !(&*waker_ptr)
                    .as_ref()
                    .expect("WakerParker parking when not prepared")
                    .will_wake(ctx.waker())
                {
                    *waker_ptr = Some(ctx.waker().clone());
                }
            });

            let x = self.state.compare_exchange(
                WakerState::Updating.encode(),
                WakerState::Waiting.encode(),
                Ordering::Release,
                Ordering::Relaxed,
            );

            match x {
                Ok(_) => return Poll::Pending,
                Err(e) => state = e,
            }

            match WakerState::decode(state) {
                WakerState::Notified(token) => {
                    return Poll::Ready(token);
                }
                waker_state => {
                    unreachable!(
                        "WakerParker updating & observed invalid waker state {:?}",
                        waker_state
                    );
                }
            }
        }
    }

    pub(crate) fn unpark(&self, token: u8) -> Option<Waker> {
        let mut state = self.state.load(Ordering::Relaxed);
        loop {
            let new_waker_state = match WakerState::decode(state) {
                WakerState::Waiting => WakerState::Consuming,
                WakerState::Updating => WakerState::Notified(token),
                WakerState::Consuming => {
                    unreachable!("multiple threads trying to unpark the same WakerParker");
                }
                WakerState::Notified(token) => {
                    unreachable!(
                        "WakerParker being unparked when already unparked with token {:?}",
                        token
                    );
                }
            };

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                new_waker_state.encode(),
                Ordering::Acquire,
                Ordering::Relaxed,
            ) {
                state = e;
                continue;
            }

            return match new_waker_state {
                WakerState::Consuming => {
                    let waker = self
                        .waker
                        .with_mut(|waker_ptr| unsafe { core::mem::replace(&mut *waker_ptr, None) });
                    let state = WakerState::Notified(token).encode();
                    self.state.store(state, Ordering::Release);
                    Some(waker.expect("WakerParker waking without a Waker"))
                }
                WakerState::Notified(_) => None,
                _ => unreachable!(),
            };
        }
    }

    /// Create a Waker from a Parker refernece
    ///
    /// # Safety:
    ///
    /// The caller must ensure that the Waker created, and the one cloned, both live as long as the parker reference.
    /// The caller must also ensure that clone() is only called by the thread the Parker belongs to.
    pub(crate) unsafe fn of<P: Parker>(parker: &P) -> Waker {
        use core::marker::PhantomData;
        struct ParkerVTable<P>(PhantomData<*mut P>);

        impl<P: Parker> ParkerVTable<P> {
            const VTABLE: RawWakerVTable = RawWakerVTable::new(
                |parker_ptr| unsafe {
                    (&mut *(parker_ptr as *mut P)).prepare();
                    RawWaker::new(parker_ptr, &Self::VTABLE)
                },
                |parker_ptr| unsafe {
                    (&*(parker_ptr as *const P)).unpark();
                },
                |parker_ptr| unsafe {
                    (&*(parker_ptr as *const P)).unpark();
                },
                |_parker_ptr| {},
            );
        }

        let parker_ptr = parker as *const P as *const ();
        let raw_waker = RawWaker::new(parker_ptr, &ParkerVTable::<P>::VTABLE);
        Waker::from_raw(raw_waker)
    }
}
