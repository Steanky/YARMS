//!
//! Minimal utilities for working with futures. Usable with `no_std` environments, but requires
//! `alloc`. Enabling the `std` feature will only enable a few additional functions for blocking
//! threads using parking/unparking.
//!
//! This crate provides the [`oneshot::channel`] and [`signal::channel`] methods, which are designed
//! for communicating between synchronous and asynchronous tasks. Optional Rayon-supporting
//! utilities can be enabled using the `rayon` feature.
//!
//! These utilities are generally "specialized" and trade off flexibility for simplicity and
//! performance. In particular, [`oneshot::Sender::signal`] does not support more than a single
//! sender per receiver.
//!
//! # Features
//!
//! All usable features are listed below, ordered alphabetically. Entries tagged with `(default)`
//! are enabled by default.
//!
//! * `loom`: Enables [loom](https://docs.rs/loom/latest/loom/) concurrency testing types, useful
//!   for ensuring correctness of code that relies on
//!   [atomic memory orderings](https://en.cppreference.com/w/cpp/atomic/memory_order). These will
//!   be used in place of core implementations of e.g. atomics whenever possible. **Not useful** for
//!   consumers of this library outside of tests that also use Loom.
//!
//! * `rayon`: Enables [`rayon::spawn_async`], for spawning a value-returning task on a `Rayon`
//!   thread from asynchronous code, and awaiting the result. Usable without this crate's `std`
//!   feature, but note that Rayon itself requires the standard library.
//!
//! * `std` (default): For code that requires the Rust standard library. Currently, this just
//!   enables several functions intended for use in synchronous code:
//!   [`oneshot::Receiver::block_on`] and [`signal::Receiver::block_on`].
//!

#![no_std]

pub(crate) extern crate alloc;
#[cfg(feature = "std")]
pub(crate) extern crate std;

use core::task::{Context, Poll, Waker};

use alloc::task::Wake;

///
/// "oneshot" channel for sending data _once_ from a synchronous task to an asynchronous one.
pub mod oneshot;

///
/// Channel to signal completion of a future from synchronous code.
pub mod signal;

#[cfg(feature = "rayon")]
///
/// Rayon utilities, access gated via the `rayon` feature.
pub mod rayon;

#[cfg(feature = "std")]
///
/// Utility for running a single future to completion.
pub mod runner;

///
/// Enables switching between `loom` and `core`/`std` types based on whether the `loom` feature is
/// enabled.
pub(crate) mod switch {
    #[cfg(not(feature = "loom"))]
    pub(crate) use alloc::sync::Arc;

    #[cfg(not(feature = "loom"))]
    pub(crate) use core::cell::UnsafeCell;

    #[cfg(not(feature = "loom"))]
    pub(crate) use core::hint;

    #[cfg(not(feature = "loom"))]
    pub(crate) use core::hint::spin_loop;

    #[cfg(not(feature = "loom"))]
    pub(crate) use core::sync::atomic::AtomicBool;

    #[cfg(not(feature = "loom"))]
    pub(crate) use core::sync::atomic::AtomicU8;

    #[cfg(not(feature = "loom"))]
    pub(crate) use core::sync::atomic::AtomicUsize;

    #[cfg(not(feature = "loom"))]
    pub(crate) use core::sync::atomic::Ordering;

    #[cfg(all(not(feature = "loom"), feature = "std"))]
    pub(crate) use std::thread;

    #[cfg(all(not(feature = "loom"), feature = "std"))]
    pub(crate) use std::thread::Thread;

    #[cfg(feature = "loom")]
    pub(crate) use loom::cell::UnsafeCell;

    #[cfg(feature = "loom")]
    pub(crate) use loom::hint;

    #[cfg(feature = "loom")]
    pub(crate) use loom::hint::spin_loop;

    #[cfg(feature = "loom")]
    pub(crate) use loom::sync::Arc;

    #[cfg(feature = "loom")]
    pub(crate) use loom::sync::atomic::AtomicBool;

    #[cfg(feature = "loom")]
    pub(crate) use loom::sync::atomic::AtomicU8;

    #[cfg(feature = "loom")]
    pub(crate) use loom::sync::atomic::AtomicUsize;

    #[cfg(feature = "loom")]
    pub(crate) use loom::sync::atomic::Ordering;

    #[cfg(feature = "loom")]
    pub(crate) use loom::thread;

    #[cfg(feature = "loom")]
    pub(crate) use loom::thread::Thread;
}

const WAKER_FREE: u8 = 0;
const WAKER_INIT: u8 = 1;
const WOKEN: u8 = 2;

///
/// Synchronization primitive that works in `no_std` environments. It's not public because it's
/// really only useful as a building block for more user-friendly constructs, e.g.
/// [`signal::channel`] -- and has some surprising behaviors when used incorrectly. These are
/// documented on the appropriate methods.
///
/// A signaller encapsulates a [`Waker`] and an internal state, which may be "woken" or "unwoken".
/// A woken signaller may never again return to its "unwoken" state, so instances are effectively
/// single-use.
pub(crate) struct Signaller {
    state: switch::AtomicU8,
    waker: switch::UnsafeCell<Option<Waker>>,
}

// SAFETY:
// - Access to non-sync field `waker` is guarded by atomic operations on `state`
unsafe impl Sync for Signaller {}

///
/// Zero-sized marker type added to structs to make them not Sync.
pub(crate) type Unsync = core::marker::PhantomData<core::cell::Cell<()>>;

///
/// Mutably borrows the contents of an [`core::cell::UnsafeCell`], and invokes `f` with a mutable
/// pointer representing its contents.
///
/// Switches to Loom's `UnsafeCell` implementation, if the `loom` feature flag is enabled. This is
/// necessary because the two types have a different API.
///
/// # Panics
/// When `loom` is enabled, this function will panic if access to `cell` is invalid under the Rust
/// memory model.
#[allow(
    clippy::inline_always,
    reason = "Only used internally, inlining is performance-critical"
)]
#[inline(always)]
pub(crate) fn borrow_mut<T, F, R>(cell: &switch::UnsafeCell<T>, f: F) -> R
where
    F: FnOnce(*mut T) -> R,
{
    #[cfg(not(feature = "loom"))]
    {
        f(cell.get())
    }

    #[cfg(feature = "loom")]
    {
        cell.with_mut(|ptr| f(ptr))
    }
}

///
/// Internal spinlock implementation. Expected to be _very_ cold, only called in very
/// specific unlucky situations. So, we never inline it and keep it away from the "hot"
/// path.
///
/// Returns `true` if we observe the `WOKEN` state, meaning that we can NEVER (soundly)
/// acquire exclusive access to the waker again. So we should stop trying.
///
/// Returns `false` if we observed the waker in the `WAKER_FREE` state, meaning we should
/// try to compare-exchange.
#[cold]
#[inline(never)]
fn spin(signaller: &Signaller) -> bool {
    loop {
        // use `Relaxed` loads in our spin loop, to be friendlier towards the CPU caches:
        // this mirrors the spinlock in `std::sync::Mutex`
        match signaller.state.load(switch::Ordering::Relaxed) {
            // observed WAKER_FREE? try to actually CAS again
            WAKER_FREE => return false,

            // still initializing waker, spin
            WAKER_INIT => switch::spin_loop(),

            // another thread got to CAS, return
            WOKEN => return true,

            // SAFETY:
            // - `state` can only be WAKER_FREE, WAKER_INIT, or WOKEN
            _ => unsafe { switch::hint::unreachable_unchecked() },
        }
    }
}

impl Signaller {
    ///
    /// Creates a new, un-woken signaller without any registered waker.
    pub(crate) fn new() -> Self {
        Self {
            state: switch::AtomicU8::new(WAKER_FREE),
            waker: switch::UnsafeCell::new(None),
        }
    }

    #[cfg(feature = "std")]
    ///
    /// _Blocks_ the calling thread until another thread calls [`Signaller::signal`]. The caller
    /// thread will be parked until signalled.
    ///
    /// Similarly to [`Signaller::poll_state`], calling this function from more than one thread, or
    /// in parallel with threads calling `poll_state`, will result in some threads "spuriously"
    /// returning even though `signal` was never called.
    pub(crate) fn block_on(&self) {
        let arc = alloc::sync::Arc::new(ParkingWake {
            woken: switch::AtomicBool::new(false),
            parked_thread: switch::thread::current(),
        });

        let waker = Waker::from(alloc::sync::Arc::clone(&arc));
        let mut context = Context::from_waker(&waker);

        loop {
            match self.poll_state(&mut context) {
                Poll::Ready(()) => return,

                Poll::Pending => {
                    loop {
                        // since we are Pending, poll_state will have registered our Waker
                        switch::thread::park();

                        // relaxed is fine, park() has Acquire memory effects
                        if arc.woken.load(switch::Ordering::Relaxed) {
                            break;
                        }
                    }
                }
            }
        }
    }

    ///
    /// Updates this signaller's state to "woken", and wakes the registered waker, if it exists. May
    /// be called in either an asynchronous or synchronous context.
    ///
    /// Multiple threads may call this function simultaneously, though the waker will only be woken
    /// once. If no waker is registered, only the signaller's state is updated, and any subsequent
    /// calls to [`Signaller::poll_state`] will immediately return [`Poll::Ready`].
    ///
    /// Calls to this method are almost always non-blocking. They can only block if another thread
    /// is setting the waker via a `poll_state` call that will yield [`Poll::Pending`] when it has
    /// completed. Blocking is implemented using a naive spinlock, which should be acceptable for
    /// our use case:
    ///
    /// * Contention with threads calling `poll_state` is extremely unlikely to begin with, since
    ///   any reasonable executor does not repeatedly poll in a hot loop
    /// * The critical section is generally quite short, and only involves (possibly) cloning a
    ///   [`Waker`]
    /// * Perhaps most importantly, this works just as well in a `no_std` environment, unlike a
    ///   `std::sync::Mutex` that may perform syscalls.
    #[inline]
    pub(crate) fn signal(&self) {
        loop {
            // Acquire is needed here so we know we can observe the updated Waker
            if let Err(old_state) = self.state.compare_exchange(
                WAKER_FREE,
                WOKEN,
                switch::Ordering::AcqRel,
                switch::Ordering::Acquire,
            ) {
                if old_state == WOKEN || spin(self) {
                    return;
                }
            } else {
                // SAFETY:
                // - the atomic compare-exchange succeeded, meaning we atomically switched to WOKEN
                // - once WOKEN, we ensure no other thread can touch `waker`
                unsafe {
                    borrow_mut(&self.waker, |waker| {
                        if let Some(waker) = (*waker).take() {
                            waker.wake();
                        }
                    });
                }

                return;
            }
        }
    }

    ///
    /// Core polling logic for futures that use [`Signaller`].
    ///
    /// Responsible for (atomically) setting our waker from the context, such that it can be woken
    /// by a thread that calls [`Signaller::signal`]. If this function returns [`Poll::Pending`],
    /// any subsequent call to `signal` will result in `cx`s waker being woken.
    ///
    /// If this function is called by more than one thread at a time, some threads may return with
    /// [`Poll::Ready`] even if `signal` was not called. This does not cause soundness concerns on
    /// its own, and thus this function is not marked unsafe, though this is still typically
    /// undesirable behavior. Callers should be aware of this possibility, and ensure that only one
    /// thread will ever call this function at a time, by requiring e.g. `&mut self` for the
    /// referencing struct.
    #[inline]
    pub(crate) fn poll_state(&self, cx: &mut Context<'_>) -> Poll<()> {
        if self
            .state
            .compare_exchange(
                WAKER_FREE,
                WAKER_INIT,
                switch::Ordering::AcqRel,
                switch::Ordering::Acquire,
            )
            .is_ok()
        {
            // SAFETY:
            // - we successfully switched to WAKER_INIT because the compare-exchange succeeded
            // - no other thread may acquire access `waker` while we are in WAKER_INIT
            unsafe {
                borrow_mut(&self.waker, |waker| {
                    let waker_mut = &mut *waker;
                    match waker_mut {
                        None => *waker_mut = Some(cx.waker().clone()),
                        Some(waker) => waker.clone_from(cx.waker()),
                    }
                });
            }

            // ensure visibility of our updated waker by using Release ordering
            self.state.store(WAKER_FREE, switch::Ordering::Release);
            Poll::Pending
        } else {
            Poll::Ready(())
        }
    }
}

#[cfg(feature = "std")]
///
/// Simple [`Wake`] implementation that just unparks a single thread. Used internally to facilitate
/// "bridge" methods like [`oneshot::Receiver::block_on`].
pub(crate) struct ParkingWake {
    woken: switch::AtomicBool,
    parked_thread: switch::Thread,
}

#[cfg(feature = "std")]
impl Wake for ParkingWake {
    fn wake(self: alloc::sync::Arc<Self>) {
        // relaxed is fine, unpark() has Release memory effects
        self.woken.store(true, switch::Ordering::Relaxed);
        self.parked_thread.unpark();
    }
}

#[cfg(test)]
pub(crate) mod test_util {
    use alloc::sync::Arc;
    use alloc::task::Wake;
    use core::sync::atomic::{AtomicUsize, Ordering};

    ///
    /// Basic Waker that just counts how often its `wake` method is called, but doesn't do anything
    /// else.
    pub(crate) struct MockWaker(pub(crate) AtomicUsize);

    impl Wake for MockWaker {
        fn wake(self: Arc<Self>) {
            // count how often we are woken, but don't impose any stronger memory ordering
            self.0.fetch_add(1, Ordering::Relaxed);
        }
    }

    ///
    /// Statically assert that T is Send.
    pub(crate) fn _assert_send<T: Send>() {}

    ///
    /// Statically assert that T is Sync.
    pub(crate) fn _assert_sync<T: Sync>() {}
}

#[cfg(test)]
mod tests {
    use crate::test_util::{_assert_send, _assert_sync};
    use crate::Signaller;

    #[allow(dead_code)]
    fn static_asserts() {
        _assert_send::<Signaller>();
        _assert_sync::<Signaller>();
    }
}
