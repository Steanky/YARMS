///
/// A simple utility for asynchronously awaiting a Rayon task that can produce a single value.
///
/// The provided function `f` is executed using [`rayon::spawn`]. If the function does not produce
/// a panic, the returned option will be `Some(R)`; otherwise it will be `None`.
///
/// As it is intended for use in asynchronous contexts, this function does not block. However, note
/// that the returned future *may* not actually need to be polled at all in order for `f` to
/// execute (the current implementation behaves this way, though this may change in the future, and
/// users should not depend upon this behavior).
pub async fn spawn_async<F, R>(f: F) -> Option<R>
where
    R: Send + 'static,
    F: FnOnce() -> R + Send + 'static,
{
    let (send, recv) = crate::oneshot::channel();
    rayon::spawn(move || {
        send.signal(f());
    });

    recv.await
}
