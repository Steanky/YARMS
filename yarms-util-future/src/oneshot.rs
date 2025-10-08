use crate::{switch, Signaller, Unsync};

use core::future::Future;
use core::marker::PhantomData;
use core::pin::Pin;
use core::task::{Context, Poll};

type Container<T> = Option<Option<T>>;

///
/// Internal state shared between Sender and Receiver.
struct State<T> {
    data: switch::UnsafeCell<Container<T>>,
    signaller: Signaller,
}

///
/// Sender half of the `oneshot` channel. Use [`Sender::signal`] to send a value to the associated
/// receiver and wake it up, or simply drop to wake up the receiver without sending anything.
pub struct Sender<T> {
    state: switch::Arc<State<T>>,
    _marker: Unsync,
}

///
/// Receiver half of the `oneshot` channel. Implements [`Future`], and so should generally be
/// directly awaited.
#[must_use = "futures do nothing unless you `.await` or poll them"]
pub struct Receiver<T> {
    state: switch::Arc<State<T>>,
    _marker: Unsync,
}

// SAFETY:
// - access to `state.data` is controlled via `state.signaller`
unsafe impl<T: Send> Send for Sender<T> {}

// SAFETY:
// - access to `state.data` is controlled via `state.signaller`
unsafe impl<T: Send> Send for Receiver<T> {}

///
/// An efficient, minimal-footprint channel capable of sending a single value from a synchronous
/// task to an asynchronous one. Conceptually quite similar to [`crate::signal::channel`], except it
/// supports transmitting data in addition to just telling a Future to wake up.
///
/// To enable a simpler and more efficient implementation, neither the sender nor receiver are
/// `Sync`. References cannot be safely shared across threads. Both, however, implement `Send` when
/// `T` is `Send`.
///
/// Dropping the sender without calling [`Sender::signal`] will cause the receiver to wake up and
/// yield `None`.
///
/// # Usage
///
/// ```
/// use std::time::Duration;
/// use yarms_util_future::oneshot::channel;
///
/// // just used for running the async function in this example
/// use yarms_util_future::runner;
///
/// async fn example() -> Option<u32> {
///     let (send, recv) = channel();
///
///     // spawn a "cpu-intensive" task on a thread...
///     std::thread::spawn(move || {
///        // simulates some work being done
///        std::thread::sleep(Duration::from_millis(500));
///
///        // wakes up the receiver with the value `42`
///        send.signal(42);
///
///        // if we DIDN'T call signal above, send would get dropped...
///        // and `recv.await` would return None
///     });
///
///     // await the signal asynchronously
///     recv.await
/// }
///
/// assert_eq!(runner::block_on(example()), Some(42))
/// ```
pub fn channel<T>() -> (Sender<T>, Receiver<T>) {
    let state = switch::Arc::new(State {
        data: switch::UnsafeCell::new(Some(None)),
        signaller: Signaller::new(),
    });

    (
        Sender {
            state: switch::Arc::clone(&state),
            _marker: PhantomData,
        },
        Receiver {
            state,
            _marker: PhantomData,
        },
    )
}

impl<T> Sender<T> {
    ///
    /// Sends the single value to the receiver, consuming this sender. If the receiver has been
    /// dropped, this function has no visible effect, aside from just dropping `value`.
    ///
    /// Dropping the [`Sender`] will also signal the receiver, though it will return [`None`]
    /// instead of [`Some`] in this case.
    pub fn signal(self, value: T) {
        // SAFETY:
        // - we haven't called `signal` on our Signaller yet
        // - the receiver only touches `data` when the signaller yields "Ready"
        // - we take ownership of `self`, which guarantees no other thread tries to signal
        unsafe {
            crate::borrow_mut(&self.state.data, |container| {
                *container = Some(Some(value));
            });
        }

        // not necessary, but makes it clear we are running drop code
        drop(self);
    }
}

impl<T> Drop for Sender<T> {
    fn drop(&mut self) {
        self.state.signaller.signal();
    }
}

impl<T> Future for Receiver<T> {
    type Output = Option<T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.state.signaller.poll_state(cx) {
            // `poll_state` will set up our waker for us
            Poll::Pending => Poll::Pending,

            Poll::Ready(()) => {
                // SAFETY:
                // - atomic operations ensure exclusive access
                unsafe {
                    crate::borrow_mut(&self.state.data, |container| {
                        // it is acceptable to just panic if an executor polls us again after ready
                        Poll::Ready((*container).take().expect("polled after complete"))
                    })
                }
            }
        }
    }
}

#[cfg(feature = "std")]
impl<T> Receiver<T> {
    ///
    /// _Blocks_ the calling thread until the receiver is signalled. **This should not be used** in
    /// an asynchronous context, as it will block the calling thread and may lead to deadlocks!
    ///
    /// If the paired sender is dropped, this function will return `None`.
    #[allow(clippy::missing_panics_doc, reason = "Can't actually panic")]
    #[must_use]
    pub fn block_on(self) -> Option<T> {
        self.state.signaller.block_on();

        // SAFETY:
        // - the call to `block_on` returned, so (another thread?) called `signal`
        // - `signal` is only called when dropping the sender, so it no longer exists
        // - there can only be 1 sender
        // - if the sender no longer exists, there is no one else to mutate `data`
        // - we take `self`, guaranteeing we have exclusive access
        unsafe { crate::borrow_mut(&self.state.data, |container| (*container).take().unwrap()) }
    }
}

#[cfg(all(test, not(feature = "loom")))]
mod tests {
    use crate::oneshot::{channel, Receiver, Sender};
    use crate::switch::Ordering;
    use crate::test_util::{MockWaker, _assert_send};
    use core::future::Future;
    use core::pin::Pin;
    use core::task::{Context, Poll, Waker};

    #[allow(dead_code)]
    fn static_asserts<T: Send>() {
        _assert_send::<Receiver<T>>();
        _assert_send::<Sender<T>>();
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
        send.signal(42);
        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 1);

        assert_eq!(
            Pin::new(&mut recv).poll(&mut context),
            Poll::Ready(Some(42))
        );
        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn dropping_sender() {
        let inner_waker = alloc::sync::Arc::new(MockWaker(Default::default()));

        let waker = Waker::from(inner_waker.clone());
        let mut context = Context::from_waker(&waker);

        let (send, mut recv) = channel::<u32>();

        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 0);
        assert_eq!(Pin::new(&mut recv).poll(&mut context), Poll::Pending);
        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 0);

        drop(send);

        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 1);
        assert_eq!(Pin::new(&mut recv).poll(&mut context), Poll::Ready(None));
        assert_eq!(inner_waker.0.load(Ordering::Relaxed), 1);
    }
}
