use crate::{switch, ParkingWake};
use core::task::{Context, Poll, Waker};

///
/// Drives a single future to completion on the current thread, and returns the result. The future
/// is not polled in a hot loop; the calling thread will park until woken.
///
/// Since this function is blocking, it should not be used in an asynchronous context.
///
/// Requires the `std` feature to be enabled, since it relies on thread parking.
pub fn block_on<F, R>(fut: F) -> R
where
    F: core::future::Future<Output = R>,
{
    let arc = alloc::sync::Arc::new(ParkingWake {
        woken: switch::AtomicBool::new(false),
        parked_thread: switch::thread::current(),
    });

    let waker = Waker::from(alloc::sync::Arc::clone(&arc));
    let mut context = Context::from_waker(&waker);

    let mut pinned = core::pin::pin!(fut);

    loop {
        match core::future::Future::poll(pinned.as_mut(), &mut context) {
            Poll::Ready(result) => return result,

            Poll::Pending => {
                loop {
                    // since we are Pending, poll will have registered our Waker
                    switch::thread::park();

                    // relaxed is fine, park() has Acquire memory effects...
                    // and ParkingWake writes to `woken` before unpark
                    if arc.woken.load(switch::Ordering::Relaxed) {
                        break;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::runner::block_on;

    #[test]
    fn simple_future() {
        assert_eq!(block_on(async { 42 }), 42);
    }

    #[test]
    fn nested_future() {
        async fn other_async_fn() -> i32 {
            42
        }

        let nested_fut = async {
            let first = other_async_fn().await;
            let second = other_async_fn().await;

            first + second
        };

        assert_eq!(block_on(nested_fut), 84);
    }
}
