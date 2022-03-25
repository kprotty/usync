use super::{shared::Waiter, MutexGuard, RawRwLock};
use lock_api::RawMutex as _RawMutex;
use std::{
    fmt,
    marker::PhantomData,
    ptr::NonNull,
    sync::atomic::{fence, AtomicUsize, Ordering},
    time::{Duration, Instant},
};

const EMPTY: usize = 0;
const SIGNAL: usize = 1;
const SIGNAL_MASK: usize = 0b111;
const SIGNAL_LOCKED: usize = SIGNAL_MASK + 1;

#[derive(Default)]
pub struct Condvar {
    state: AtomicUsize,
    _p: PhantomData<*const Waiter>,
}

impl fmt::Debug for Condvar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("Condvar { .. }")
    }
}

unsafe impl Send for Condvar {}
unsafe impl Sync for Condvar {}

impl Condvar {
    pub const fn new() -> Self {
        Self {
            state: AtomicUsize::new(EMPTY),
            _p: PhantomData,
        }
    }

    pub fn wait<T: ?Sized>(&self, mutex_guard: &mut MutexGuard<'_, T>) {
        let result = self.wait_with(mutex_guard, None);
        assert!(!result.timed_out());
    }

    pub fn wait_until<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Instant,
    ) -> WaitTimeoutResult {
        match timeout.checked_duration_since(Instant::now()) {
            Some(until_deadline) => self.wait_for(mutex_guard, until_deadline),
            None => WaitTimeoutResult(true),
        }
    }

    pub fn wait_for<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Duration,
    ) -> WaitTimeoutResult {
        self.wait_with(mutex_guard, Some(timeout))
    }

    #[cold]
    fn wait_with<T: ?Sized>(
        &self,
        mutex_guard: &mut MutexGuard<'_, T>,
        timeout: Option<Duration>,
    ) -> WaitTimeoutResult {
        Waiter::with(|waiter| unsafe {
            let is_writer = true;
            waiter.flags.set(is_writer as usize);

            let raw_mutex = MutexGuard::mutex(mutex_guard).raw();
            let rwlock_state = NonNull::from(&raw_mutex.rwlock.state);

            waiter.waiting_on.set(Some(rwlock_state));
            waiter.prev.set(None);

            let mut state = self.state.load(Ordering::Relaxed);
            loop {
                let head = NonNull::new((state & Waiter::MASK) as *mut Waiter);
                waiter.next.set(head);

                let waiter_ptr = &*waiter as *const Waiter as usize;
                let mut new_state = (state & !Waiter::MASK) | waiter_ptr;

                if head.is_none() {
                    waiter.tail.set(Some(NonNull::from(&*waiter)));
                } else {
                    new_state |= SIGNAL_LOCKED;
                    waiter.tail.set(None);
                }

                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Release,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                if head.is_some() && (state & SIGNAL_LOCKED == 0) {
                    self.link_queue_or_unpark(new_state);
                }

                raw_mutex.unlock();
                break;
            }

            let timed_out = !waiter.parker.park(timeout);
            if timed_out {
                self.notify_all();
                assert!(waiter.parker.park(None));
            }

            raw_mutex.lock();
            WaitTimeoutResult(timed_out)
        })
    }

    #[inline]
    pub fn notify_one(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        if state == EMPTY {
            return false;
        }

        self.notify_one_slow(state)
    }

    #[cold]
    fn notify_one_slow(&self, mut state: usize) -> bool {
        loop {
            if state == EMPTY {
                return false;
            }

            if state & SIGNAL_LOCKED == 0 {
                // Try to acquire the signal lock to wake up the queued threads.
                let new_state = state | SIGNAL_LOCKED;
                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    new_state,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                unsafe { self.unpark(new_state) };
                return true;
            }

            // Bail if all threads are going to be woken up eventually.
            let signals = state & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return false;
            }

            // Tell the signal lock holder to wake up the thread in our place.
            match self.state.compare_exchange_weak(
                state,
                state + SIGNAL,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(e) => state = e,
            }
        }
    }

    #[inline]
    pub fn notify_all(&self) -> bool {
        let state = self.state.load(Ordering::Relaxed);
        if state == EMPTY {
            return false;
        }

        self.notify_all_slow(state)
    }

    #[cold]
    fn notify_all_slow(&self, mut state: usize) -> bool {
        loop {
            if state == EMPTY {
                return false;
            }

            // If no thread is currently waking up the waiters, grab all of them to wake up.
            if state & SIGNAL_LOCKED == 0 {
                if let Err(e) = self.state.compare_exchange_weak(
                    state,
                    EMPTY,
                    Ordering::Acquire,
                    Ordering::Relaxed,
                ) {
                    state = e;
                    continue;
                }

                unsafe { self.unpark_waiters(state) };
                return true;
            }

            let signals = state & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return false;
            }

            match self.state.compare_exchange_weak(
                state,
                state | SIGNAL_MASK,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn link_queue_or_unpark(&self, mut state: usize) {
        loop {
            assert_eq!(state & SIGNAL_LOCKED, 0);

            let signals = state & SIGNAL_MASK;
            if signals > 0 {
                return self.unpark(state);
            }

            fence(Ordering::Acquire);
            let _ = Waiter::get_and_link_queue(state, |_| {});

            match self.state.compare_exchange_weak(
                state,
                state & !SIGNAL_LOCKED,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                Ok(_) => return,
                Err(e) => state = e,
            }
        }
    }

    #[cold]
    unsafe fn unpark(&self, mut state: usize) {
        let mut scanned = 0;
        let mut unparked = None;

        loop {
            assert_ne!(state & SIGNAL_LOCKED, 0);

            let signals = state & SIGNAL_MASK;
            if signals == SIGNAL_MASK {
                return self.unpark_all();
            }

            fence(Ordering::Acquire);
            let (head, tail) = Waiter::get_and_link_queue(state, |_| {});

            let (mut front, back) = unparked.unwrap_or_else(|| {
                scanned += 1;
                (tail, tail)
            });

            let max_scan = signals + 1;
            while scanned < max_scan {
                if let Some(prev) = front.as_ref().prev.get() {
                    front = prev;
                    scanned += 1;
                } else {
                    break;
                }
            }

            if scanned >= SIGNAL_MASK {
                return self.unpark_all();
            }

            let mut new_state = state & !SIGNAL_LOCKED;
            new_state -= signals.saturating_sub(scanned) * SIGNAL;

            if let Some(new_tail) = front.as_ref().prev.get() {
                head.as_ref().tail.set(Some(new_tail));
            } else {
                new_state &= !Waiter::MASK;
            }

            if let Err(e) = self.state.compare_exchange_weak(
                state,
                new_state,
                Ordering::Release,
                Ordering::Relaxed,
            ) {
                head.as_ref().tail.set(Some(back));
                unparked = Some((front, back));
                state = e;
                continue;
            }

            front.as_ref().prev.set(None);
            self.unpark_requeue(head, tail);
            return;
        }
    }

    #[cold]
    unsafe fn unpark_all(&self) {
        let state = self.state.swap(EMPTY, Ordering::Acquire);
        assert_ne!(state & SIGNAL_LOCKED, 0);
        assert_eq!(state & SIGNAL_MASK, SIGNAL_MASK);

        self.unpark_waiters(state);
    }

    #[cold]
    unsafe fn unpark_waiters(&self, state: usize) {
        let (head, tail) = Waiter::get_and_link_queue(state, |_| {});
        self.unpark_requeue(head, tail);
    }

    #[cold]
    unsafe fn unpark_requeue(&self, head: NonNull<Waiter>, tail: NonNull<Waiter>) {
        let waiting_on = head.as_ref().waiting_on.get();
        let rwlock_state = waiting_on.expect("Condvar waiter not waiting on anything");

        // SAFETY:
        // RawRwLock is repr(transparent) to it's state.
        // RawMutex is repr(transparent) to RawRwLock.
        let raw_rwlock = rwlock_state.cast::<RawRwLock>();
        raw_rwlock.as_ref().unpark_requeue(head, tail);
    }
}

/// A type indicating whether a timed wait on a condition variable returned
/// due to a time out or not.
#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct WaitTimeoutResult(bool);

impl WaitTimeoutResult {
    /// Returns whether the wait was known to have timed out.
    #[inline]
    pub fn timed_out(self) -> bool {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use crate::{Condvar, Mutex, MutexGuard};
    use std::{
        sync::{mpsc::channel, Arc},
        thread,
        time::{Duration, Instant},
    };

    #[test]
    fn smoke() {
        let c = Condvar::new();
        c.notify_one();
        c.notify_all();
    }

    #[test]
    fn notify_one() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let _t = thread::spawn(move || {
            let _g = m2.lock();
            c2.notify_one();
        });
        c.wait(&mut g);
    }

    #[test]
    fn notify_all() {
        const N: usize = 10;

        let data = Arc::new((Mutex::new(0), Condvar::new()));
        let (tx, rx) = channel();
        for _ in 0..N {
            let data = data.clone();
            let tx = tx.clone();
            thread::spawn(move || {
                let &(ref lock, ref cond) = &*data;
                let mut cnt = lock.lock();
                *cnt += 1;
                if *cnt == N {
                    tx.send(()).unwrap();
                }
                while *cnt != 0 {
                    cond.wait(&mut cnt);
                }
                tx.send(()).unwrap();
            });
        }
        drop(tx);

        let &(ref lock, ref cond) = &*data;
        rx.recv().unwrap();
        let mut cnt = lock.lock();
        *cnt = 0;
        cond.notify_all();
        drop(cnt);

        for _ in 0..N {
            rx.recv().unwrap();
        }
    }

    #[test]
    fn notify_one_return_true() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let _t = thread::spawn(move || {
            let _g = m2.lock();
            assert!(c2.notify_one());
        });
        c.wait(&mut g);
    }

    #[test]
    fn notify_one_return_false() {
        let m = Arc::new(Mutex::new(()));
        let c = Arc::new(Condvar::new());

        let _t = thread::spawn(move || {
            let _g = m.lock();
            assert!(!c.notify_one());
        });
    }

    #[test]
    fn notify_all_return() {
        const N: usize = 10;

        let data = Arc::new((Mutex::new(0), Condvar::new()));
        let (tx, rx) = channel();
        for _ in 0..N {
            let data = data.clone();
            let tx = tx.clone();
            thread::spawn(move || {
                let &(ref lock, ref cond) = &*data;
                let mut cnt = lock.lock();
                *cnt += 1;
                if *cnt == N {
                    tx.send(()).unwrap();
                }
                while *cnt != 0 {
                    cond.wait(&mut cnt);
                }
                tx.send(()).unwrap();
            });
        }
        drop(tx);

        let &(ref lock, ref cond) = &*data;
        rx.recv().unwrap();
        let mut cnt = lock.lock();
        *cnt = 0;
        assert_eq!(cond.notify_all(), true);
        drop(cnt);

        for _ in 0..N {
            rx.recv().unwrap();
        }

        assert_eq!(cond.notify_all(), false);
    }

    #[test]
    fn wait_for() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let no_timeout = c.wait_for(&mut g, Duration::from_millis(1));
        assert!(no_timeout.timed_out());

        let _t = thread::spawn(move || {
            let _g = m2.lock();
            c2.notify_one();
        });
        let timeout_res = c.wait_for(&mut g, Duration::from_secs(u64::max_value()));
        assert!(!timeout_res.timed_out());

        drop(g);
    }

    #[test]
    fn wait_until() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let no_timeout = c.wait_until(&mut g, Instant::now() + Duration::from_millis(1));
        assert!(no_timeout.timed_out());
        let _t = thread::spawn(move || {
            let _g = m2.lock();
            c2.notify_one();
        });
        let timeout_res = c.wait_until(
            &mut g,
            Instant::now() + Duration::from_millis(u32::max_value() as u64),
        );
        assert!(!timeout_res.timed_out());
        drop(g);
    }

    #[test]
    #[should_panic]
    fn two_mutexes() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let m3 = Arc::new(Mutex::new(()));
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        // Make sure we don't leave the child thread dangling
        struct PanicGuard<'a>(&'a Condvar);
        impl<'a> Drop for PanicGuard<'a> {
            fn drop(&mut self) {
                self.0.notify_one();
            }
        }

        let (tx, rx) = channel();
        let g = m.lock();
        let _t = thread::spawn(move || {
            let mut g = m2.lock();
            tx.send(()).unwrap();
            c2.wait(&mut g);
        });
        drop(g);
        rx.recv().unwrap();
        let _g = m.lock();
        let _guard = PanicGuard(&*c);
        c.wait(&mut m3.lock());
    }

    #[test]
    fn two_mutexes_disjoint() {
        let m = Arc::new(Mutex::new(()));
        let m2 = m.clone();
        let m3 = Arc::new(Mutex::new(()));
        let c = Arc::new(Condvar::new());
        let c2 = c.clone();

        let mut g = m.lock();
        let _t = thread::spawn(move || {
            let _g = m2.lock();
            c2.notify_one();
        });
        c.wait(&mut g);
        drop(g);

        let _ = c.wait_for(&mut m3.lock(), Duration::from_millis(1));
    }

    #[test]
    fn test_debug_condvar() {
        let c = Condvar::new();
        assert_eq!(format!("{:?}", c), "Condvar { .. }");
    }

    // #[test]
    // fn test_condvar_requeue() {
    //     let m = Arc::new(Mutex::new(()));
    //     let m2 = m.clone();
    //     let c = Arc::new(Condvar::new());
    //     let c2 = c.clone();
    //     let t = thread::spawn(move || {
    //         let mut g = m2.lock();
    //         c2.wait(&mut g);
    //     });

    //     let mut g = m.lock();
    //     while !c.notify_one() {
    //         // Wait for the thread to get into wait()
    //         MutexGuard::bump(&mut g);
    //         // Yield, so the other thread gets a chance to do something.
    //         // (At least Miri needs this, because it doesn't preempt threads.)
    //         thread::yield_now();
    //     }
    //     // The thread should have been requeued to the mutex, which we wake up now.
    //     drop(g);
    //     t.join().unwrap();
    // }

    #[test]
    fn test_parking_lot_issue_129() {
        let locks = Arc::new((Mutex::new(()), Condvar::new()));

        let (tx, rx) = channel();
        for _ in 0..4 {
            let locks = locks.clone();
            let tx = tx.clone();
            thread::spawn(move || {
                let mut guard = locks.0.lock();
                locks.1.wait(&mut guard);
                locks.1.wait_for(&mut guard, Duration::from_millis(1));
                locks.1.notify_one();
                tx.send(()).unwrap();
            });
        }

        thread::sleep(Duration::from_millis(100));
        locks.1.notify_one();

        for _ in 0..4 {
            assert_eq!(rx.recv_timeout(Duration::from_millis(500)), Ok(()));
        }
    }
}

// This module contains an integration test that is heavily inspired from WebKit's own integration
// tests for it's own Condvar.

// #[cfg(test)]
// mod webkit_queue_test {
//     use crate::{Condvar, Mutex, MutexGuard};
//     use std::{collections::VecDeque, sync::Arc, thread, time::Duration};

//     #[derive(Clone, Copy)]
//     enum Timeout {
//         Bounded(Duration),
//         Forever,
//     }

//     #[derive(Clone, Copy)]
//     enum NotifyStyle {
//         One,
//         All,
//     }

//     struct Queue {
//         items: VecDeque<usize>,
//         should_continue: bool,
//     }

//     impl Queue {
//         fn new() -> Self {
//             Self {
//                 items: VecDeque::new(),
//                 should_continue: true,
//             }
//         }
//     }

//     fn wait<T: ?Sized>(
//         condition: &Condvar,
//         lock: &mut MutexGuard<'_, T>,
//         predicate: impl Fn(&mut MutexGuard<'_, T>) -> bool,
//         timeout: &Timeout,
//     ) {
//         while !predicate(lock) {
//             match timeout {
//                 Timeout::Forever => condition.wait(lock),
//                 Timeout::Bounded(bound) => {
//                     condition.wait_for(lock, *bound);
//                 }
//             }
//         }
//     }

//     fn notify(style: NotifyStyle, condition: &Condvar, should_notify: bool) {
//         match style {
//             NotifyStyle::One => {
//                 condition.notify_one();
//             }
//             NotifyStyle::All => {
//                 if should_notify {
//                     condition.notify_all();
//                 }
//             }
//         }
//     }

//     fn run_queue_test(
//         num_producers: usize,
//         num_consumers: usize,
//         max_queue_size: usize,
//         messages_per_producer: usize,
//         notify_style: NotifyStyle,
//         timeout: Timeout,
//         delay: Duration,
//     ) {
//         let input_queue = Arc::new(Mutex::new(Queue::new()));
//         let empty_condition = Arc::new(Condvar::new());
//         let full_condition = Arc::new(Condvar::new());

//         let output_vec = Arc::new(Mutex::new(vec![]));

//         let consumers = (0..num_consumers)
//             .map(|_| {
//                 consumer_thread(
//                     input_queue.clone(),
//                     empty_condition.clone(),
//                     full_condition.clone(),
//                     timeout,
//                     notify_style,
//                     output_vec.clone(),
//                     max_queue_size,
//                 )
//             })
//             .collect::<Vec<_>>();
//         let producers = (0..num_producers)
//             .map(|_| {
//                 producer_thread(
//                     messages_per_producer,
//                     input_queue.clone(),
//                     empty_condition.clone(),
//                     full_condition.clone(),
//                     timeout,
//                     notify_style,
//                     max_queue_size,
//                 )
//             })
//             .collect::<Vec<_>>();

//         thread::sleep(delay);

//         for producer in producers.into_iter() {
//             producer.join().expect("Producer thread panicked");
//         }

//         {
//             let mut input_queue = input_queue.lock();
//             input_queue.should_continue = false;
//         }
//         empty_condition.notify_all();

//         for consumer in consumers.into_iter() {
//             consumer.join().expect("Consumer thread panicked");
//         }

//         let mut output_vec = output_vec.lock();
//         assert_eq!(output_vec.len(), num_producers * messages_per_producer);
//         output_vec.sort();
//         for msg_idx in 0..messages_per_producer {
//             for producer_idx in 0..num_producers {
//                 assert_eq!(msg_idx, output_vec[msg_idx * num_producers + producer_idx]);
//             }
//         }
//     }

//     fn consumer_thread(
//         input_queue: Arc<Mutex<Queue>>,
//         empty_condition: Arc<Condvar>,
//         full_condition: Arc<Condvar>,
//         timeout: Timeout,
//         notify_style: NotifyStyle,
//         output_queue: Arc<Mutex<Vec<usize>>>,
//         max_queue_size: usize,
//     ) -> thread::JoinHandle<()> {
//         thread::spawn(move || loop {
//             let (should_notify, result) = {
//                 let mut queue = input_queue.lock();
//                 wait(
//                     &*empty_condition,
//                     &mut queue,
//                     |state| -> bool { !state.items.is_empty() || !state.should_continue },
//                     &timeout,
//                 );
//                 if queue.items.is_empty() && !queue.should_continue {
//                     return;
//                 }
//                 let should_notify = queue.items.len() == max_queue_size;
//                 let result = queue.items.pop_front();
//                 std::mem::drop(queue);
//                 (should_notify, result)
//             };
//             notify(notify_style, &*full_condition, should_notify);

//             if let Some(result) = result {
//                 output_queue.lock().push(result);
//             }
//         })
//     }

//     fn producer_thread(
//         num_messages: usize,
//         queue: Arc<Mutex<Queue>>,
//         empty_condition: Arc<Condvar>,
//         full_condition: Arc<Condvar>,
//         timeout: Timeout,
//         notify_style: NotifyStyle,
//         max_queue_size: usize,
//     ) -> thread::JoinHandle<()> {
//         thread::spawn(move || {
//             for message in 0..num_messages {
//                 let should_notify = {
//                     let mut queue = queue.lock();
//                     wait(
//                         &*full_condition,
//                         &mut queue,
//                         |state| state.items.len() < max_queue_size,
//                         &timeout,
//                     );
//                     let should_notify = queue.items.is_empty();
//                     queue.items.push_back(message);
//                     std::mem::drop(queue);
//                     should_notify
//                 };
//                 notify(notify_style, &*empty_condition, should_notify);
//             }
//         })
//     }

//     macro_rules! run_queue_tests {
//         ( $( $name:ident(
//             num_producers: $num_producers:expr,
//             num_consumers: $num_consumers:expr,
//             max_queue_size: $max_queue_size:expr,
//             messages_per_producer: $messages_per_producer:expr,
//             notification_style: $notification_style:expr,
//             timeout: $timeout:expr,
//             delay_seconds: $delay_seconds:expr);
//         )* ) => {
//             $(#[test]
//             fn $name() {
//                 let delay = Duration::from_secs($delay_seconds);
//                 run_queue_test(
//                     $num_producers,
//                     $num_consumers,
//                     $max_queue_size,
//                     $messages_per_producer,
//                     $notification_style,
//                     $timeout,
//                     delay,
//                     );
//             })*
//         };
//     }

//     run_queue_tests! {
//         sanity_check_queue(
//             num_producers: 1,
//             num_consumers: 1,
//             max_queue_size: 1,
//             messages_per_producer: 100_000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Bounded(Duration::from_secs(1)),
//             delay_seconds: 0
//         );
//         sanity_check_queue_timeout(
//             num_producers: 1,
//             num_consumers: 1,
//             max_queue_size: 1,
//             messages_per_producer: 100_000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         new_test_without_timeout_5(
//             num_producers: 1,
//             num_consumers: 5,
//             max_queue_size: 1,
//             messages_per_producer: 100_000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         one_producer_one_consumer_one_slot(
//             num_producers: 1,
//             num_consumers: 1,
//             max_queue_size: 1,
//             messages_per_producer: 100_000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         one_producer_one_consumer_one_slot_timeout(
//             num_producers: 1,
//             num_consumers: 1,
//             max_queue_size: 1,
//             messages_per_producer: 100_000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 1
//         );
//         one_producer_one_consumer_hundred_slots(
//             num_producers: 1,
//             num_consumers: 1,
//             max_queue_size: 100,
//             messages_per_producer: 1_000_000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         ten_producers_one_consumer_one_slot(
//             num_producers: 10,
//             num_consumers: 1,
//             max_queue_size: 1,
//             messages_per_producer: 10000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         ten_producers_one_consumer_hundred_slots_notify_all(
//             num_producers: 10,
//             num_consumers: 1,
//             max_queue_size: 100,
//             messages_per_producer: 10000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         ten_producers_one_consumer_hundred_slots_notify_one(
//             num_producers: 10,
//             num_consumers: 1,
//             max_queue_size: 100,
//             messages_per_producer: 10000,
//             notification_style: NotifyStyle::One,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         one_producer_ten_consumers_one_slot(
//             num_producers: 1,
//             num_consumers: 10,
//             max_queue_size: 1,
//             messages_per_producer: 10000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         one_producer_ten_consumers_hundred_slots_notify_all(
//             num_producers: 1,
//             num_consumers: 10,
//             max_queue_size: 100,
//             messages_per_producer: 100_000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         one_producer_ten_consumers_hundred_slots_notify_one(
//             num_producers: 1,
//             num_consumers: 10,
//             max_queue_size: 100,
//             messages_per_producer: 100_000,
//             notification_style: NotifyStyle::One,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         ten_producers_ten_consumers_one_slot(
//             num_producers: 10,
//             num_consumers: 10,
//             max_queue_size: 1,
//             messages_per_producer: 50000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         ten_producers_ten_consumers_hundred_slots_notify_all(
//             num_producers: 10,
//             num_consumers: 10,
//             max_queue_size: 100,
//             messages_per_producer: 50000,
//             notification_style: NotifyStyle::All,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//         ten_producers_ten_consumers_hundred_slots_notify_one(
//             num_producers: 10,
//             num_consumers: 10,
//             max_queue_size: 100,
//             messages_per_producer: 50000,
//             notification_style: NotifyStyle::One,
//             timeout: Timeout::Forever,
//             delay_seconds: 0
//         );
//     }
// }
