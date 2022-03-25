use super::{RawMutex, RawThreadId};

pub type ReentrantMutex<T> = lock_api::ReentrantMutex<RawMutex, RawThreadId, T>;
pub type ReentrantMutexGuard<'a, T> = lock_api::ReentrantMutexGuard<'a, RawMutex, RawThreadId, T>;
pub type MappedReentrantMutexGuard<'a, T> =
    lock_api::MappedReentrantMutexGuard<'a, RawMutex, RawThreadId, T>;

pub const fn const_reentrant_mutex<T>(value: T) -> ReentrantMutex<T> {
    ReentrantMutex::const_new(
        <RawMutex as lock_api::RawMutex>::INIT,
        <RawThreadId as lock_api::GetThreadId>::INIT,
        value,
    )
}

#[cfg(test)]
mod tests {
    use crate::ReentrantMutex;
    use std::{cell::RefCell, sync::Arc, thread};

    #[test]
    fn smoke() {
        let m = ReentrantMutex::new(2);
        {
            let a = m.lock();
            {
                let b = m.lock();
                {
                    let c = m.lock();
                    assert_eq!(*c, 2);
                }
                assert_eq!(*b, 2);
            }
            assert_eq!(*a, 2);
        }
    }

    #[test]
    fn is_mutex() {
        let m = Arc::new(ReentrantMutex::new(RefCell::new(0)));
        let m2 = m.clone();
        let lock = m.lock();
        let child = thread::spawn(move || {
            let lock = m2.lock();
            assert_eq!(*lock.borrow(), 4950);
        });
        for i in 0..100 {
            let lock = m.lock();
            *lock.borrow_mut() += i;
        }
        drop(lock);
        child.join().unwrap();
    }

    #[test]
    fn trylock_works() {
        let m = Arc::new(ReentrantMutex::new(()));
        let m2 = m.clone();
        let _lock = m.try_lock();
        let _lock2 = m.try_lock();
        thread::spawn(move || {
            let lock = m2.try_lock();
            assert!(lock.is_none());
        })
        .join()
        .unwrap();
        let _lock3 = m.try_lock();
    }

    #[test]
    fn test_reentrant_mutex_debug() {
        let mutex = ReentrantMutex::new(vec![0u8, 10]);

        assert_eq!(format!("{:?}", mutex), "ReentrantMutex { data: [0, 10] }");
    }
}
