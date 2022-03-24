pub type Mutex<T> = lock_api::Mutex<RawMutex, T>;
pub type MutexGuard<'a, T> = lock_api::MutexGuard<'a, RawMutex, T>;
pub type MappedMutexGuard<'a, T> = lock_api::MappedMutexGuard<'a, RawMutex, T>;

pub const fn const_mutex<T>(value: T) -> Mutex<T> {
    Mutex::const_new(<RawMutex as lock_api::RawMutex>::INIT, value)
}
