use bytes::Buf;
use core::mem;
use core::ops::{Deref, DerefMut};

///
/// An adapter that implements [`Buf`] on a backing `&mut [u8]`. This is useful for APIs that want
/// the methods of `Buf`, while still allowing the mutation of its contents so long as it does not
/// impact the "length" of the buffer.
///
/// This type has the same in-memory representation as `&mut [u8]`, and will also dereference to
/// it. This allows all methods on `[u8]` to be callable directly on a `SliceBuf`.
///
/// # Usage
/// ```rust
/// use bytes::Buf;
/// use yarms_std::disjoint::SliceBuf;
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

impl Deref for SliceBuf<'_> {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SliceBuf<'_> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl AsRef<[u8]> for SliceBuf<'_> {
    fn as_ref(&self) -> &[u8] {
        &*self.0
    }
}

impl AsMut<[u8]> for SliceBuf<'_> {
    fn as_mut(&mut self) -> &mut [u8] {
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

impl<'a> From<SliceBuf<'a>> for &'a mut [u8] {
    #[inline]
    fn from(value: SliceBuf<'a>) -> Self {
        value.0
    }
}

impl<'a> From<&'a mut [u8]> for SliceBuf<'a> {
    #[inline]
    fn from(value: &'a mut [u8]) -> Self {
        SliceBuf(value)
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
