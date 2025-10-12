use crate::Pool;
use alloc::boxed::Box;
use alloc::format;
use alloc::sync::Arc;
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc::{sync_channel, Receiver, SyncSender, TryRecvError};
use std::sync::{Condvar, Mutex, MutexGuard, PoisonError};

///
/// Creates a new [`FixedSizePool`] instance, that will always maintain exactly `size` running
/// threads available for executing tasks.
///
/// # Panics
/// This function panics if `size` is `0`.
#[must_use]
pub fn new_fixed_size_pool(size: usize) -> FixedSizePool {
    assert_ne!(size, 0, "expected `size` to be non-zero");

    let (tx, rx) = sync_channel::<Thunk>(size);

    let data = Arc::new(SharedData {
        rx: Mutex::new(rx),
        has_work: Condvar::new(),
        has_free_thread: Condvar::new(),
        busy_count: AtomicUsize::new(size),
        max_threads: size,
        terminated: AtomicBool::new(false),
        thread_ids: AtomicUsize::new(0),
    });

    for _ in 0..size {
        spawn_thread(Arc::clone(&data));
    }

    FixedSizePool { data, tx, size }
}

///
/// A fixed-size thread pool. [`new_fixed_size_pool`] to create a new instance.
///
/// Dropping a `ThreadPool` will cause any worker threads to exit normally after their current tasks
/// are completed.
pub struct FixedSizePool {
    data: Arc<SharedData>,
    tx: SyncSender<Thunk>,
    size: usize,
}

impl Pool for FixedSizePool {
    ///
    /// Enqueue some work to the pool. If there is a thread available, the work will be submitted
    /// and this function will return immediately. If all threads are busy, this function will
    /// block until one comes free.
    ///
    /// If this thread is a thread pool worker thread, calling `submit` may result in a deadlock!
    fn submit<F>(&self, func: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let _ = self.submit_internal(func);
    }
}

impl FixedSizePool {
    // internal implementation, with a result type to make the code neater
    #[inline]
    fn submit_internal<F>(
        &self,
        func: F,
    ) -> Result<(), PoisonError<MutexGuard<'_, Receiver<Thunk>>>>
    where
        F: FnOnce() + Send + 'static,
    {
        let mut rx = self.data.rx.lock()?;

        loop {
            if self.data.busy_count.load(Ordering::Relaxed) == self.size {
                // all threads are busy.
                // release the mutex and wait until we get signalled
                rx = self.data.has_free_thread.wait(rx)?;
            } else {
                // send over the work
                self.tx
                    .try_send(Box::from(func))
                    .expect("`try_send` should not err");

                // mark a thread as "busy"
                self.data.busy_count.fetch_add(1, Ordering::Relaxed);

                // notify exactly one worker
                self.data.has_work.notify_one();

                // the worker thread now may progress
                drop(rx);

                return Ok(());
            }
        }
    }
}

impl Drop for FixedSizePool {
    fn drop(&mut self) {
        if let Ok(guard) = self.data.rx.lock() {
            // we're already terminated, don't do anything
            if self.data.terminated.load(Ordering::Relaxed) {
                return;
            }

            self.data.terminated.store(true, Ordering::Relaxed);
            self.data.has_work.notify_all();

            drop(guard);
        }
    }
}

trait FnBox {
    fn call_box(self: Box<Self>);
}

impl<F: FnOnce()> FnBox for F {
    fn call_box(self: Box<F>) {
        (*self)();
    }
}

type Thunk = Box<dyn FnBox + Send>;

struct SharedData {
    rx: Mutex<Receiver<Thunk>>,
    has_work: Condvar,
    has_free_thread: Condvar,
    busy_count: AtomicUsize,
    max_threads: usize,
    terminated: AtomicBool,
    thread_ids: AtomicUsize,
}

struct Sentinel<'a> {
    shared_data: &'a Arc<SharedData>,
    active: bool,
}

impl Sentinel<'_> {
    fn cancel(mut self) {
        self.active = false;
    }
}

impl Drop for Sentinel<'_> {
    fn drop(&mut self) {
        if self.active {
            // a thread panicked while executing a user-supplied task:
            // recreate the thread
            spawn_thread(Arc::clone(self.shared_data));
        }
    }
}

fn spawn_thread(shared_data: Arc<SharedData>) {
    std::thread::Builder::new()
        .name(format!(
            "yarms-threadpool-worker-{}",
            shared_data.thread_ids.fetch_add(1, Ordering::Relaxed)
        ))
        .spawn(move || {
            let sentinel = Sentinel {
                shared_data: &shared_data,
                active: true,
            };

            let _ = shared_data.do_work();

            // panic detection:
            // if sentinel is dropped before cancel is called, it will spawn a new thread to replace
            // the one that died
            sentinel.cancel();
        })
        .expect("should have been able to spawn worker thread");
}

impl SharedData {
    fn do_work(&self) -> Result<(), PoisonError<MutexGuard<'_, Receiver<Thunk>>>> {
        loop {
            // it shouldn't really be possible to get poisoned...
            // but at least we try to handle it nicely
            let mut rx = self.rx.lock()?;

            // we were terminated while in the middle of a job
            if self.terminated.load(Ordering::Relaxed) {
                return Ok(());
            }

            // we use Relaxed ordering, because we ONLY modify this when `rx` is locked!
            let cnt = self.busy_count.fetch_sub(1, Ordering::Relaxed);

            if cnt == self.max_threads {
                // we were previously at maximum utilization
                // if there's a submission thread waiting, notify it
                self.has_free_thread.notify_one();
            }

            let job = loop {
                // this releases `lock`, we'll re-acquire it after signalling
                rx = self.has_work.wait(rx)?;

                // we were terminated while waiting for a job
                if self.terminated.load(Ordering::Relaxed) {
                    return Ok(());
                }

                match rx.try_recv() {
                    // we got a job to run
                    Ok(job) => break job,

                    // the sender hung up, so just exit
                    Err(TryRecvError::Disconnected) => return Ok(()),

                    // spurious wakeup
                    Err(TryRecvError::Empty) => {}
                };
            };

            // don't hold any locks while we're performing the work
            drop(rx);

            // execute our task
            job.call_box();
        }
    }
}
