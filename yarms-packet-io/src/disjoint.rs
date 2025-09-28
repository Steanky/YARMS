use alloc::vec::Vec;
use bytes::{Buf, BufMut, Bytes, BytesMut};
use core::iter::FusedIterator;
use std::mem;
use std::ops::{Deref, DerefMut};

///
/// A trait for data that can be represented as an iterator over nonoverlapping immutable byte
/// slices of (mostly) arbitrary length.
///
/// Usually, types that implement Disjoint should also implement [`Buf`].
///
/// See also [`DisjointMut`], the equivalent trait for mutable byte slices.
pub trait Disjoint {
    ///
    /// Reports if this type is "contiguous", that is, if [`Disjoint::chunk_iter`] will _always_
    /// return an iterator of length 1. It is appropriate to return `false` if the source is only
    /// sometimes contiguous.
    ///
    /// Some algorithms can make use of this for efficiency. Generally, implementations shouldn't
    /// put any logic here, rather they should just return a constant `true` or `false`. This allows
    /// the compiler to easily optimize calling code, often to the point of avoiding a branch
    /// entirely.
    ///
    /// If this `Disjoint` is also a [`Buf`], `contiguous` has an additional meaning: [`Buf::chunk`]
    /// should always return a chunk of size equal to [`Buf::remaining`]. This allows further
    /// optimizations of algorithms that would otherwise need to make special allowances for
    /// potentially non-contiguous buffers.
    fn contiguous() -> bool;

    ///
    /// Returns an iterator over the immutable byte chunks contained in this data structure.
    ///
    /// # Implementation requirements
    /// The returned iterator should never be empty (zero-length). It also shouldn't yield any
    /// zero-length slices _unless the iterator is yielding exactly 1 slice_.
    ///
    /// Note that because this method returns `FusedIterator`, callers can expect that the iterator
    /// will never again return `Some` after returning `None` for the first time.
    ///
    /// For efficiency reasons, implementations should strive to return as few slices as possible.
    /// For example, `[u8]` implements `Chunk`, and yields an iterator with exactly 1 element
    /// containing simply `&self`. A non-contiguous data structure, however, may be split into
    /// multiple contiguous segments, which should be iterated individually.
    fn chunk_iter(&self) -> impl FusedIterator<Item = &[u8]>;
}

///
/// A trait for data that can be represented as an iterator over nonoverlapping mutable byte slices
/// of (mostly) arbitrary length.
///
/// Inherits from [`Disjoint`]. If you only need immutable access, that trait should be used as a
/// bound instead, as more data structures can safely implement it.
///
/// Types that implement this trait should often implement [`BufMut`] too.
pub trait DisjointMut: Disjoint {
    ///
    /// Returns an iterator over the mutable byte chunks contained in this data structure.
    ///
    /// # Implementation requirements
    /// The requirements and behavior of this function are semantically identical to
    /// [`Disjoint::chunk_iter`], though with mutable rather than immutable slices.
    fn chunk_iter_mut(&mut self) -> impl FusedIterator<Item = &mut [u8]>;
}

impl Disjoint for [u8] {
    #[inline]
    fn contiguous() -> bool {
        true
    }

    #[inline]
    fn chunk_iter(&self) -> impl FusedIterator<Item = &[u8]> {
        core::iter::once(self)
    }
}

impl DisjointMut for [u8] {
    #[inline]
    fn chunk_iter_mut(&mut self) -> impl FusedIterator<Item = &mut [u8]> {
        core::iter::once(self)
    }
}

impl Disjoint for Vec<u8> {
    #[inline]
    fn contiguous() -> bool {
        true
    }

    #[inline]
    fn chunk_iter(&self) -> impl FusedIterator<Item = &[u8]> {
        core::iter::once(&self[..])
    }
}

impl DisjointMut for Vec<u8> {
    #[inline]
    fn chunk_iter_mut(&mut self) -> impl FusedIterator<Item = &mut [u8]> {
        core::iter::once(&mut self[..])
    }
}

impl Disjoint for Bytes {
    #[inline]
    fn contiguous() -> bool {
        true
    }

    #[inline]
    fn chunk_iter(&self) -> impl FusedIterator<Item = &[u8]> {
        core::iter::once(self.as_ref())
    }
}

impl Disjoint for BytesMut {
    #[inline]
    fn contiguous() -> bool {
        true
    }

    #[inline]
    fn chunk_iter(&self) -> impl FusedIterator<Item = &[u8]> {
        core::iter::once(self.as_ref())
    }
}

impl DisjointMut for BytesMut {
    #[inline]
    fn chunk_iter_mut(&mut self) -> impl FusedIterator<Item = &mut [u8]> {
        core::iter::once(self.as_mut())
    }
}

#[cfg(feature = "tokio")]
impl Disjoint for tokio::io::ReadBuf {
    #[inline]
    fn contiguous() -> bool {
        true
    }

    #[inline]
    fn chunk_iter(&self) -> impl FusedIterator<Item = &[u8]> {
        core::iter::once(self.filled())
    }
}

#[cfg(feature = "tokio")]
impl DisjointMut for tokio::io::ReadBuf {
    #[inline]
    fn chunk_iter_mut(&mut self) -> impl FusedIterator<Item = &mut [u8]> {
        core::iter::once(self.filled_mut())
    }
}

impl<T: Disjoint + ?Sized> Disjoint for &mut T {
    #[inline]
    fn contiguous() -> bool {
        T::contiguous()
    }

    #[inline]
    fn chunk_iter(&self) -> impl FusedIterator<Item = &[u8]> {
        (**self).chunk_iter()
    }
}

impl<T: DisjointMut + ?Sized> DisjointMut for &mut T {
    #[inline]
    fn chunk_iter_mut(&mut self) -> impl FusedIterator<Item = &mut [u8]> {
        (**self).chunk_iter_mut()
    }
}

///
/// An adapter that implements both [`Buf`] and [`DisjointMut`] on a backing `&mut [u8]`. This is
/// useful for APIs that want the methods of `Buf`, while still allowing the mutation of its
/// contents so long as it does not impact the "length" of the buffer.
///
/// This type has the same in-memory representation as `&mut [u8]`.
///
/// # Usage
/// ```rust
/// use bytes::Buf;
/// use yarms_packet_io::disjoint::SliceBuf;
///
/// let mut backing = [0u8; 4];
/// let mut slice_buf = SliceBuf(&mut backing);
///
/// // SliceBuf is contiguous, so `chunk` gives us the entire array
/// assert_eq!(slice_buf.chunk(), &[0, 0, 0, 0]);
///
/// // write to the backing store:
/// // SliceBuf dereferences to `&mut [u8]`, and so can be indexed directly
/// slice_buf[0] = 42;
///
/// // `chunk` is now different
/// assert_eq!(slice_buf.chunk(), &[42, 0, 0, 0]);
///
/// slice_buf.advance(1);
///
/// // advancing changes the start of the slice
/// assert_eq!(slice_buf.chunk(), &[0, 0, 0]);
///
/// // the backing array is modified, too
/// assert_eq!(&backing, &[42, 0, 0, 0]);
/// ```
#[repr(transparent)]
pub struct SliceBuf<'a>(pub &'a mut [u8]);

impl<'a> Deref for SliceBuf<'a> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> DerefMut for SliceBuf<'a> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl Buf for SliceBuf<'_> {
    #[inline]
    fn remaining(&self) -> usize {
        (&*self.0).remaining()
    }

    #[inline]
    fn chunk(&self) -> &[u8] {
        &*self.0
    }

    #[inline]
    fn advance(&mut self, cnt: usize) {
        // some nonsense to make the borrow checker happy
        self.0 = &mut mem::replace(&mut self.0, &mut [])[cnt..];
    }
}

impl Disjoint for SliceBuf<'_> {
    #[inline]
    fn contiguous() -> bool {
        true
    }

    #[inline]
    fn chunk_iter(&self) -> impl FusedIterator<Item = &[u8]> {
        core::iter::once(self.as_ref())
    }
}

impl DisjointMut for SliceBuf<'_> {
    #[inline]
    fn chunk_iter_mut(&mut self) -> impl FusedIterator<Item = &mut [u8]> {
        self.0.chunk_iter_mut()
    }
}

impl<'a> Into<&'a mut [u8]> for SliceBuf<'a> {
    #[inline]
    fn into(self) -> &'a mut [u8] {
        self.0
    }
}

#[cfg(test)]
mod tests {
    use crate::disjoint::SliceBuf;
    use bytes::Buf;
    use std::vec;

    #[test]
    fn slice_buf() {
        let mut backing_vec = vec![0u8; 16];
        let mut slice_buf = SliceBuf(&mut backing_vec);

        assert_eq!(slice_buf.remaining(), 16);
        slice_buf.advance(1);
        assert_eq!(slice_buf.remaining(), 15);
        slice_buf.advance(2);
        assert_eq!(slice_buf.remaining(), 13);

        let chunk = slice_buf.chunk();
        assert_eq!(chunk.len(), 13);
    }
}
