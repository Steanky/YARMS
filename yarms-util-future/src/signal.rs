use core::future::Future;
use core::pin::Pin;

use crate::{switch, Signaller, Unsync};
use core::marker::PhantomData;
use core::task::{Context, Poll};

///
/// Sender half of a signaller. Can be cloned for use across multiple threads.
pub struct Sender {
    state: switch::Arc<(switch::AtomicUsize, Signaller)>,
}

///
/// Receiver half of a signaller. Can be sent across threads, but not shared between them, as there
/// can only be one receiver, but many senders.
///
/// Receiver implements [`Future`], and can be directly awaited on.
#[must_use = "futures do nothing unless you `.await` or poll them"]
pub struct Receiver {
    state: switch::Arc<(switch::AtomicUsize, Signaller)>,

    // prevents receiver from being Sync
    // not strictly necessary for soundness (as we need &mut self anyway to poll) but helps prevent
    // semantically questionable usage
    _marker: Unsync,
}

///
/// A dead-simple, nonblocking, efficient signalling mechanism similar to "oneshot channels", meant
/// for communicating between _synchronous_ and _asynchronous_ code, but does not support
/// transmitting a value. Rather, this allows synchronous code to efficiently "unblock" an
/// asynchronous method.
///
/// The receiver will be woken up when calling [`Sender::signal`], or when all senders have been
/// dropped.
///
/// # Usage
///
/// ```
/// use std::time::Duration;
/// use yarms_util_future::signal::channel;
///
/// async fn example() {
///     let (send, recv) = channel();
///
///     std::thread::spawn(move || {
///        std::thread::sleep(Duration::from_secs(1));
///
///        // wakes up the receiver
///        // dropping it would have the same effect!
///        send.signal();
///     });
///
///     // will await for ~1 second
///     recv.await
/// }
/// ```
pub fn channel() -> (Sender, Receiver) {
    let state = switch::Arc::new((switch::AtomicUsize::new(1), Signaller::new()));
    (
        Sender {
            state: switch::Arc::clone(&state),
        },
        Receiver {
            state,
            _marker: PhantomData,
        },
    )
}

impl Sender {
    ///
    /// Signals the paired receiver to wake up.
    ///
    /// If the receiver has been dropped, this function does nothing. If the receiver has not been
    /// awaited yet, the next call to `await` will be immediately ready. Calling [`Sender::signal`]
    /// more than once does not do anything, beyond the first invocation waking up the receiver.
    ///
    /// # Memory effects
    /// Writes made before a call to [`Sender::signal`] _happen-before_ a call to [`Receiver::poll`]
    /// returns [`Poll::Ready`] for the first time.
    pub fn signal(&self) {
        self.state.1.signal();
    }
}

impl Drop for Sender {
    fn drop(&mut self) {
        // relaxed is fine, we don't depend on memory orderings of our sender count, just atomics
        let old_sender_count = self.state.0.fetch_sub(1, switch::Ordering::Relaxed);

        // a count of 1 means we are the last sender, so we do not have to worry about a call to
        // clone() increasing the count again
        if old_sender_count == 1 {
            self.signal();
        }
    }
}

impl Clone for Sender {
    ///
    /// Creates a copy of this `Sender`, that can be used to wake up the same receiver.
    fn clone(&self) -> Self {
        let state = switch::Arc::clone(&self.state);

        // no overflow check here - Arc already has a check to abort the program if there's too
        // many outstanding references, and its reference counter is always >= our sender count
        let _ = state.0.fetch_add(1, switch::Ordering::Relaxed);
        Self { state }
    }
}

impl Future for Receiver {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        self.state.1.poll_state(cx)
    }
}

#[cfg(feature = "std")]
impl Receiver {
    ///
    /// _Blocks_ the calling thread until any corresponding sender calls [`Sender::signal`]. **This
    /// should not be used** in an asynchronous context, as it will block the calling thread and may
    /// lead to deadlocks!
    ///
    /// If all paired senders are dropped, this method will return.
    ///
    /// # Memory effects
    /// Writes made before the first call to [`Sender::signal`] _happen-before_ this method
    /// unblocks.
    pub fn block_on(self) {
        self.state.1.block_on();
    }
}

#[cfg(all(test, not(feature = "loom")))]
mod tests {
    use crate::signal::{channel, Receiver, Sender};
    use crate::test_util::{MockWaker, _assert_send, _assert_sync};
    use core::future::Future;
    use core::pin::Pin;
    use core::sync::atomic::Ordering;
    use core::task::{Context, Poll, Waker};

    #[allow(dead_code)]
    fn static_asserts() {
        _assert_send::<Receiver>();

        _assert_sync::<Sender>();
        _assert_send::<Sender>();
    }

    #[test]
    fn ready_immediately() {
        let inner_waker = alloc::sync::Arc::new(MockWaker(Default::default()));

        let waker = Waker::from(inner_waker.clone());
        let mut context = Context::from_waker(&waker);

        let (send, mut recv) = channel();

        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 0);
        assert_eq!(Pin::new(&mut recv).poll(&mut context), Poll::Pending);
        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 0);

        send.signal();
        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 1);

        assert_eq!(Pin::new(&mut recv).poll(&mut context), Poll::Ready(()));
        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 1);
    }
}
