//!
//! Support for the Anvil chunk format.

#![no_std]

pub extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

#[cfg(feature = "std")]
///
/// A fixed-size thread [`Pool`] implementation that's dependent on `std`.
pub mod fixed_size;

///
/// A pool to which work may be submitted, typically for execution on another thread (though this is
/// not required).
pub trait Pool {
    ///
    /// Submits some work to the pool.
    ///
    /// It is unspecified whether this function will return before or after `func` has executed.
    /// Implementations may provide stronger guarantees.
    ///
    /// If `func` panics, the behavior is unspecified: the panic may propagate to the caller, it may
    /// be silently swallowed, logged by the pool implementation, or anything else (as long as it
    /// does not cause undefined behavior).
    ///
    /// It is unspecified what happens to the execution of `func` when [`self`] is dropped. It may
    /// continue until completion or panic.
    fn submit<F>(&self, func: F)
    where
        F: FnOnce() + Send + 'static;
}

#[cfg(feature = "std")]
pub use fixed_size::new_fixed_size_pool;

#[cfg(test)]
mod tests {
    use crate::{Pool};
    use crate::std;
    use crate::std::sync::atomic::{AtomicUsize, Ordering};
    use crate::std::sync::mpsc::sync_channel;
    use crate::std::time::Duration;
    use crate::fixed_size::new_fixed_size_pool;

    #[test]
    fn simple_run() {
        let pool = new_fixed_size_pool(16);
        let (tx, rx) = sync_channel(10);
        pool.submit(move || {
            let _ = tx.send(true);
        });

        assert_eq!(rx.recv(), Ok(true))
    }

    #[test]
    fn large_queue() {
        let pool = new_fixed_size_pool(16);

        static COUNT: AtomicUsize = AtomicUsize::new(0);
        const ITERS: usize = 256;

        for x in 0..ITERS {
            pool.submit(move || {
                std::thread::sleep(Duration::from_millis(50));
                COUNT.fetch_add(1, Ordering::SeqCst);
            })
        }

        while COUNT.load(Ordering::SeqCst) != ITERS {}
    }
}
