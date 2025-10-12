use alloc::sync::Arc;
use core::cell::RefCell;

///
/// Something that provides scoped mutable access to a single target type.
///
/// There exist a variety of `Accessor` implementations. The motivation for this trait is to enable
/// a common API between e.g. thread locals (which provide threadsafe mutable access to some inner
/// type) and something like a [`RefCell`] (that isn't threadsafe but does provide mutable access
/// with only a shared reference).
///
/// Implementations include:
/// * `RefCell<T>` (not Sync)
/// * `Arc<Mutex<T>>` (Sync, but requires `std`)
/// * `&'static LocalKey<T>` (Sync, but requires `std`)
/// * `CloningAccessor<T: Clone>` (Sync, but copies `T` on every access)
pub trait Accessor {
    ///
    /// The inner type, to which mutable access is desired.
    type Target: ?Sized;

    ///
    /// Mutably access the contents of the type. The default implementation delegates to
    /// [`Accessor::try_access`].
    ///
    /// # Panics
    /// May panic if the target cannot be accessed. See [`Accessor::try_access`] for a
    /// non-panicking variant.
    #[inline]
    fn access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> R {
        self.try_access(callback)
            .expect("should have been able to access type")
    }

    ///
    /// Non-panicking version of [`Accessor::access`]. Returns `None` if the value could not be
    /// accessed.
    ///
    /// ```
    /// use std::cell::RefCell;
    /// use yarms_anvil::access::Accessor;
    /// let mut access = RefCell::new(10);
    ///
    /// let guard = access.borrow_mut();
    ///
    /// // can't access the target mutably while we have an outstanding borrow
    /// let result = access.try_access(|_| panic!("this shouldn't run!"));
    /// assert!(result.is_none())
    ///
    /// ```
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R>;
}

#[cfg(feature = "std")]
impl<Target> Accessor for &'static std::thread::LocalKey<RefCell<Target>> {
    type Target = Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        Some(self.with_borrow_mut(callback))
    }
}

#[cfg(feature = "std")]
impl<Target: ?Sized> Accessor for Arc<std::sync::Mutex<Target>> {
    type Target = Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        let mut guard = self.lock().ok()?;
        Some(callback(&mut *guard))
    }
}

impl<Target> Accessor for RefCell<Target> {
    type Target = Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        let mut guard = self.try_borrow_mut().ok()?;
        Some(callback(&mut *guard))
    }
}

///
/// Wrapper struct to implement [`Accessor`] on any `T: Clone`.
///
/// `CloningAccessor` will clone the inner value once every time [`Accessor::access`] is called.
///
/// ```
/// use yarms_anvil::access::CloningAccessor;
/// use yarms_anvil::access::Accessor;
///
/// let value = 10;
/// let access = CloningAccessor(10);
///
/// let result = access.access(|value| {
///     assert_eq!(*value, 10);
///     true
/// });
///
/// assert!(result);
/// assert_eq!(access.0, 10, "underlying value shouldn't change");
///
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct CloningAccessor<T>(pub T);

impl<T> Accessor for CloningAccessor<T>
where
    T: Clone,
{
    type Target = T;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        let mut cloned = self.clone();
        Some(callback(&mut cloned.0))
    }
}
