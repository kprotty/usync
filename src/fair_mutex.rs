pub type FairMutex<T> = lock_api::FairMutex<RawFairMutex, T>;
pub type FairMutexGuard<'a, T> = lock_api::FairMutexGuard<'a, RawFairMutex, T>;
pub type MappedFairMutexGuard<'a, T> = lock_api::MappedFairMutexGuard<'a, RawFairMutex, T>;

pub const fn const_fair_mutex<T>(value: T) -> FairMutex<T> {
    FairMutex::const_new(<RawFairMutex as lock_api::RawFairMutex>::INIT, value)
}
