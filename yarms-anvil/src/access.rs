use alloc::sync::Arc;
use core::cell::RefCell;

///
/// Something that provides scoped mutable access to a single target type.
pub trait Accessor: Clone {
    ///
    /// The inner type, to which mutable access is desired.
    type Target: ?Sized;

    ///
    /// Mutably access the contents of the type.
    fn access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> R;
}

#[cfg(feature = "std")]
impl<Target> Accessor for &'static std::thread::LocalKey<RefCell<Target>> {
    type Target = Target;

    #[inline]
    fn access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> R {
        self.with_borrow_mut(callback)
    }
}

#[cfg(feature = "std")]
impl<Target: ?Sized> Accessor for Arc<std::sync::Mutex<Target>> {
    type Target = Target;

    #[inline]
    fn access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> R {
        let mut guard = self.lock().unwrap();
        callback(&mut *guard)
    }
}

impl<Target> Accessor for RefCell<Target>
where
    Target: Clone,
{
    type Target = Target;

    #[inline]
    fn access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> R {
        let mut guard = self.borrow_mut();
        callback(&mut *guard)
    }
}
