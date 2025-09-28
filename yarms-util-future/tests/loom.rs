//!
//! Integration tests for `yarms-util-future` concurrency primitives. Uses `loom` to test most
//! possible atomic memory orderings.

#[cfg(feature = "loom")]
mod tests {
    use core::future::Future;
    use core::pin::Pin;
    use loom::sync::atomic::AtomicBool;
    use loom::sync::Arc;
    use loom::thread::Thread;

    pub(crate) extern crate alloc;

    use alloc::task::Wake;
    use core::task::{Context, Poll, Waker};

    ///
    /// Using a (simulated) async executor, tests that polling a receiver returns the correct value,
    /// even when the corresponding sender signals from another thread, potentially in parallel with
    /// polling the receiver future for the first time.
    #[test]
    fn parallel_signal_wakeup() {
        struct ParkingWaker(AtomicBool, Thread);

        impl Wake for ParkingWaker {
            fn wake(self: alloc::sync::Arc<Self>) {
                self.0.store(true, loom::sync::atomic::Ordering::Relaxed);
                self.1.unpark();
            }
        }

        let evaluated_immediate_ready =
            alloc::sync::Arc::new(core::sync::atomic::AtomicBool::new(false));
        let evaluated_delayed_ready =
            alloc::sync::Arc::new(core::sync::atomic::AtomicBool::new(false));

        loom::model({
            let evaluated_immediate_ready = alloc::sync::Arc::clone(&evaluated_immediate_ready);
            let evaluated_delayed_ready = alloc::sync::Arc::clone(&evaluated_delayed_ready);

            move || {
                let (send, mut recv) = yarms_util_future::signal::channel();

                let parking_waker = alloc::sync::Arc::new(ParkingWaker(
                    Default::default(),
                    loom::thread::current(),
                ));

                let waker = Waker::from(alloc::sync::Arc::clone(&parking_waker));
                let mut context = Context::from_waker(&waker);

                let send = Arc::new(send);
                let signalled_var = Arc::new(AtomicBool::new(false));

                let thread = loom::thread::spawn({
                    let send = Arc::clone(&send);
                    let signalled_var = Arc::clone(&signalled_var);

                    move || {
                        // we use Relaxed because signal should synchronize with `poll` when the latter returns
                        // Ready for the first time
                        signalled_var.store(true, loom::sync::atomic::Ordering::Relaxed);

                        send.signal();
                    }
                });

                // `poll` may be called at the same time as `signal`
                let result = Pin::new(&mut recv).poll(&mut context);

                if result != Poll::Pending {
                    // if we are Ready, the store to signalled_var must happen-before
                    assert!(signalled_var.load(loom::sync::atomic::Ordering::Relaxed));

                    evaluated_immediate_ready.store(true, core::sync::atomic::Ordering::Relaxed);

                    // we returned Ready, so don't poll again, just return
                    return;
                }

                // simulate an executor that only polls one future
                loop {
                    loom::thread::park();

                    // handle spurious wakeup
                    // loom doesn't seem to make these happen but this is "correct" even if that changes
                    if parking_waker.0.load(loom::sync::atomic::Ordering::Relaxed) {
                        break;
                    }
                }

                let result = Pin::new(&mut recv).poll(&mut context);

                assert!(signalled_var.load(loom::sync::atomic::Ordering::Relaxed));
                assert_eq!(result, Poll::Ready(()));

                thread.join().expect("thread should not panic");

                evaluated_delayed_ready.store(true, core::sync::atomic::Ordering::Relaxed);
            }
        });

        assert!(
            evaluated_immediate_ready.load(core::sync::atomic::Ordering::Relaxed),
            "test did not model an important ordering: immediate `Ready`"
        );
        assert!(
            evaluated_delayed_ready.load(core::sync::atomic::Ordering::Relaxed),
            "test did not model an important ordering: delayed `Ready`"
        );
    }

    #[test]
    #[cfg(feature = "std")]
    fn signal_block_on_sync() {
        loom::model(|| {
            let (send, recv) = yarms_util_future::signal::channel();

            let unsafe_cell = Arc::new(loom::cell::UnsafeCell::new(None));

            let thread = loom::thread::spawn({
                let unsafe_cell = Arc::clone(&unsafe_cell);

                move || {
                    unsafe_cell.with_mut(|cell| {
                        let r = unsafe { &mut *cell };
                        *r = Some(42);
                    });

                    send.signal();
                }
            });

            recv.block_on();

            unsafe_cell.with(|cell| {
                let r = unsafe { &*cell };

                assert_eq!(*r, Some(42));
            });

            thread.join().expect("thread should not panic");
        });
    }

    #[test]
    #[cfg(feature = "std")]
    fn signal_parallel_drop() {
        loom::model(|| {
            let (send, recv) = yarms_util_future::signal::channel();

            let status = Arc::new(AtomicBool::new(false));
            let handle = loom::thread::spawn({
                let status = Arc::clone(&status);

                move || {
                    recv.block_on();
                    status.store(true, loom::sync::atomic::Ordering::Relaxed);
                }
            });

            loom::thread::spawn({
                let send = send.clone();

                move || {
                    drop(send);
                }
            });

            drop(send);

            handle.join().expect("thread should not panic");
            assert!(status.load(loom::sync::atomic::Ordering::Relaxed));
        });
    }
}
