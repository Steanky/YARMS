use core::cell::RefCell;

///
/// Something that provides scoped mutable access to a single target type, while only requiring a
/// shared reference.
///
/// There exist a variety of `Accessor` implementations. The motivation for this trait is to enable
/// a common API between e.g. thread locals (which provide threadsafe mutable access to some inner
/// type) and something like a [`RefCell`] (that isn't threadsafe but does provide mutable access
/// with only a shared reference).
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
    /// non-panicking variant. For example, trying to access an already-borrowed `RefCell` would
    /// result in a panic here.
    #[inline]
    fn access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> R {
        self.try_access(callback)
            .expect("should have been able to access type")
    }

    ///
    /// Non-panicking version of [`Accessor::access`]. Returns `None` if the value could not be
    /// accessed for any reason.
    ///
    /// ```
    /// use std::cell::RefCell;
    /// use yarms_std::access::Accessor;
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
impl<T> Accessor for &'static std::thread::LocalKey<RefCell<T>> {
    type Target = T;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        self.try_with(|key| {
            key.try_borrow_mut()
                .ok()
                .map(|mut cell| callback(&mut *cell))
        })
        .ok()?
    }

    #[inline]
    fn access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> R {
        self.with_borrow_mut(callback)
    }
}

#[cfg(feature = "std")]
impl<T> Accessor for std::sync::Mutex<T>
where
    T: ?Sized,
{
    type Target = T;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        let mut guard = self.lock().ok()?;
        Some(callback(&mut *guard))
    }
}

impl<T> Accessor for RefCell<T>
where
    T: ?Sized,
{
    type Target = T;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        let mut guard = self.try_borrow_mut().ok()?;
        Some(callback(&mut *guard))
    }
}

impl<T> Accessor for alloc::sync::Arc<T>
where
    T: Accessor + ?Sized,
{
    type Target = <T as Accessor>::Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        T::try_access(self, callback)
    }
}

impl<T> Accessor for alloc::rc::Rc<T>
where
    T: Accessor + ?Sized,
{
    type Target = <T as Accessor>::Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        T::try_access(self, callback)
    }
}

impl<T> Accessor for alloc::boxed::Box<T>
where
    T: Accessor + ?Sized,
{
    type Target = <T as Accessor>::Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        T::try_access(self, callback)
    }
}

impl<T> Accessor for alloc::borrow::Cow<'_, T>
where
    T: Accessor + alloc::borrow::ToOwned + ?Sized,
{
    type Target = <T as Accessor>::Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        T::try_access(self, callback)
    }
}

impl<T> Accessor for &T
where
    T: Accessor + ?Sized,
{
    type Target = <T as Accessor>::Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        T::try_access(self, callback)
    }
}

impl<T> Accessor for &mut T
where
    T: Accessor + ?Sized,
{
    type Target = <T as Accessor>::Target;

    #[inline]
    fn try_access<Call: FnOnce(&mut Self::Target) -> R, R>(&self, callback: Call) -> Option<R> {
        T::try_access(self, callback)
    }
}
