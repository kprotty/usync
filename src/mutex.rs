use super::RawRwLock;
use lock_api::RawRwLock as _RawRwLock;
use std::fmt;

#[derive(Default)]
#[repr(transparent)]
pub struct RawMutex {
    pub(super) rwlock: RawRwLock,
}

impl fmt::Debug for RawMutex {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad("RawMutex { .. }")
    }
}

unsafe impl lock_api::RawMutex for RawMutex {
    type GuardMarker = crate::GuardMarker;

    const INIT: Self = Self {
        rwlock: RawRwLock::INIT,
    };

    #[inline]
    fn is_locked(&self) -> bool {
        self.rwlock.is_locked_exclusive()
    }

    #[inline]
    fn lock(&self) {
        self.rwlock.lock_exclusive()
    }

    #[inline]
    fn try_lock(&self) -> bool {
        self.rwlock.try_lock_exclusive()
    }

    #[inline]
    unsafe fn unlock(&self) {
        self.rwlock.unlock_exclusive()
    }
}

pub type Mutex<T> = lock_api::Mutex<RawMutex, T>;
pub type MutexGuard<'a, T> = lock_api::MutexGuard<'a, RawMutex, T>;
pub type MappedMutexGuard<'a, T> = lock_api::MappedMutexGuard<'a, RawMutex, T>;

pub const fn const_mutex<T>(value: T) -> Mutex<T> {
    Mutex::const_new(<RawMutex as lock_api::RawMutex>::INIT, value)
}

#[cfg(test)]
mod tests {
    use crate::{Condvar, Mutex};
    use std::{
        sync::{
            atomic::{AtomicUsize, Ordering},
            mpsc::channel,
            Arc,
        },
        thread,
    };

    struct Packet<T>(Arc<(Mutex<T>, Condvar)>);

    #[derive(Eq, PartialEq, Debug)]
    struct NonCopy(i32);

    unsafe impl<T: Send> Send for Packet<T> {}
    unsafe impl<T> Sync for Packet<T> {}

    #[test]
    fn smoke() {
        let m = Mutex::new(());
        drop(m.lock());
        drop(m.lock());
    }

    #[test]
    fn lots_and_lots() {
        const J: u32 = 1000;
        const K: u32 = 3;

        let m = Arc::new(Mutex::new(0));

        fn inc(m: &Mutex<u32>) {
            for _ in 0..J {
                *m.lock() += 1;
            }
        }

        let (tx, rx) = channel();
        for _ in 0..K {
            let tx2 = tx.clone();
            let m2 = m.clone();
            thread::spawn(move || {
                inc(&m2);
                tx2.send(()).unwrap();
            });
            let tx2 = tx.clone();
            let m2 = m.clone();
            thread::spawn(move || {
                inc(&m2);
                tx2.send(()).unwrap();
            });
        }

        drop(tx);
        for _ in 0..2 * K {
            rx.recv().unwrap();
        }
        assert_eq!(*m.lock(), J * K * 2);
    }

    #[test]
    fn try_lock() {
        let m = Mutex::new(());
        *m.try_lock().unwrap() = ();
    }

    #[test]
    fn test_into_inner() {
        let m = Mutex::new(NonCopy(10));
        assert_eq!(m.into_inner(), NonCopy(10));
    }

    #[test]
    fn test_into_inner_drop() {
        struct Foo(Arc<AtomicUsize>);
        impl Drop for Foo {
            fn drop(&mut self) {
                self.0.fetch_add(1, Ordering::SeqCst);
            }
        }
        let num_drops = Arc::new(AtomicUsize::new(0));
        let m = Mutex::new(Foo(num_drops.clone()));
        assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        {
            let _inner = m.into_inner();
            assert_eq!(num_drops.load(Ordering::SeqCst), 0);
        }
        assert_eq!(num_drops.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_get_mut() {
        let mut m = Mutex::new(NonCopy(10));
        *m.get_mut() = NonCopy(20);
        assert_eq!(m.into_inner(), NonCopy(20));
    }

    #[test]
    fn test_mutex_arc_condvar() {
        let packet = Packet(Arc::new((Mutex::new(false), Condvar::new())));
        let packet2 = Packet(packet.0.clone());
        let (tx, rx) = channel();
        let _t = thread::spawn(move || {
            // wait until parent gets in
            rx.recv().unwrap();
            let &(ref lock, ref cvar) = &*packet2.0;
            let mut lock = lock.lock();
            *lock = true;
            cvar.notify_one();
        });

        let &(ref lock, ref cvar) = &*packet.0;
        let mut lock = lock.lock();
        tx.send(()).unwrap();
        assert!(!*lock);
        while !*lock {
            cvar.wait(&mut lock);
        }
    }

    #[test]
    fn test_mutex_arc_nested() {
        // Tests nested mutexes and access
        // to underlying data.
        let arc = Arc::new(Mutex::new(1));
        let arc2 = Arc::new(Mutex::new(arc));
        let (tx, rx) = channel();
        let _t = thread::spawn(move || {
            let lock = arc2.lock();
            let lock2 = lock.lock();
            assert_eq!(*lock2, 1);
            tx.send(()).unwrap();
        });
        rx.recv().unwrap();
    }

    #[test]
    fn test_mutex_arc_access_in_unwind() {
        let arc = Arc::new(Mutex::new(1));
        let arc2 = arc.clone();
        let _ = thread::spawn(move || {
            struct Unwinder {
                i: Arc<Mutex<i32>>,
            }
            impl Drop for Unwinder {
                fn drop(&mut self) {
                    *self.i.lock() += 1;
                }
            }
            let _u = Unwinder { i: arc2 };
            panic!();
        })
        .join();
        let lock = arc.lock();
        assert_eq!(*lock, 2);
    }

    #[test]
    fn test_mutex_unsized() {
        let mutex: &Mutex<[i32]> = &Mutex::new([1, 2, 3]);
        {
            let b = &mut *mutex.lock();
            b[0] = 4;
            b[2] = 5;
        }
        let comp: &[i32] = &[4, 2, 5];
        assert_eq!(&*mutex.lock(), comp);
    }

    #[test]
    fn test_mutexguard_sync() {
        fn sync<T: Sync>(_: T) {}

        let mutex = Mutex::new(());
        sync(mutex.lock());
    }

    #[test]
    fn test_mutex_debug() {
        let mutex = Mutex::new(vec![0u8, 10]);

        assert_eq!(format!("{:?}", mutex), "Mutex { data: [0, 10] }");
        let _lock = mutex.lock();
        assert_eq!(format!("{:?}", mutex), "Mutex { data: <locked> }");
    }
}
