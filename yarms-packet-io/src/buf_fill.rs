use alloc::vec::Vec;
use bytes::BufMut;
use core::future::Future;
use core::num::NonZeroUsize;
use yarms_protocol::ErrorReason;

///
/// Type alias for `core::result::Result<usize, FillError>`.
pub type FillResult = Result<usize, FillError>;

///
/// An error that can occur when calling [`BufFill::fill_buf`].
///
/// If the `std` feature is enabled, this may be converted into a `std::io::Error` via the [`From`]
/// trait, and vice-versa.
///
/// Converts into [`yarms_protocol::ReadError`].
#[derive(Debug)]
#[non_exhaustive]
pub enum FillError {
    ///
    /// Not enough bytes to fill the buffer. When filling from an in-memory source, this can mean
    /// the caller requested more bytes than are available. When filling from an IO source, this can
    /// mean an "EOF" was encountered, and the source is no longer likely to produce any more bytes.
    NotEnoughBytes,

    #[cfg(feature = "std")]
    ///
    /// Generic IO error, encapsulating [`std::io::Error`].
    ///
    /// This variant is only available if the `std` feature is enabled.
    Io(std::io::Error),
}

static NOT_ENOUGH_BYTES_ERR_MSG: &str = "not enough bytes to fill buffer";

#[cfg(feature = "std")]
impl From<std::io::Error> for FillError {
    fn from(e: std::io::Error) -> Self {
        Self::Io(e)
    }
}

#[cfg(feature = "std")]
impl From<FillError> for std::io::Error {
    fn from(value: FillError) -> Self {
        match value {
            FillError::NotEnoughBytes => {
                std::io::Error::new(std::io::ErrorKind::Other, NOT_ENOUGH_BYTES_ERR_MSG)
            }
            FillError::Io(inner) => inner,
        }
    }
}

impl From<FillError> for yarms_protocol::ReadError {
    fn from(error: FillError) -> Self {
        match error {
            FillError::NotEnoughBytes => {
                yarms_protocol::ReadError::new(ErrorReason::NotEnoughBytes)
            }
            FillError::Io(io) => yarms_protocol::ReadError::new(ErrorReason::Io(io)),
        }
    }
}

impl core::fmt::Display for FillError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FillError::NotEnoughBytes => f.write_str(NOT_ENOUGH_BYTES_ERR_MSG),

            #[cfg(feature = "std")]
            FillError::Io(e) => e.fmt(f),
        }
    }
}

impl core::error::Error for FillError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            FillError::NotEnoughBytes => None,

            #[cfg(feature = "std")]
            FillError::Io(source) => Some(source),
        }
    }
}

///
/// Something that can asynchronously fill a [`BufMut`] with a potentially unspecified number of
/// bytes.
///
/// This operation _may_ perform IO. If the implementation is doing IO, it should do so
/// asynchronously, and `fill_buf` should be non-blocking. If the implementation is not doing IO,
/// for example if it is copying bytes from memory, it will generally be synchronous.
pub trait BufFill {
    ///
    /// Fills the buffer `buf` with a certain number of bytes. Returns the number of bytes read. If
    /// the result is `Err`, the number of bytes written into the buffer is _unspecified_.
    ///
    /// The minimum number of bytes may be specified by passing `Some` to `target`. Implementations
    /// should ensure that for any call where `target` is `Some(x)`, and the returned future's
    /// output `Ok(y)`, `y >= x && y > 0`. If `target` is `None`, implementations may read any
    /// *nonzero* number of bytes.
    ///
    /// Implementations also must ensure that for any returned future's output `Ok(y)`, the number
    /// of bytes actually written into `buf` is exactly `y`, unless the number of bytes written
    /// overflows `usize`, in which case implementations should return `usize::MAX`.
    ///
    /// Violating these expectations is a logic error, but should not result in undefined behavior.
    /// Unsafe code must defensively guard against bad implementations of `fill_buf`.
    ///
    /// Implementations are free to dump as many bytes as they want into the buffer, as long as they
    /// write at least 1 byte (if `target == None`) or `x` bytes (if `target == Some(x)`),
    /// particularly if doing so would improve performance (such as when reading a file in chunks).
    ///
    /// Note that implementations should be aware of the buffer's capacity. Say for example that an
    /// I/O based `BufFill` wants to read a chunk of 2048 bytes from a file, with `target` set to
    /// 512, and [`BufMut::remaining_mut`] returning 1024. In this case, the implementation should
    /// just enter 1024 bytes to avoid over-filling and potentially causing a panic.
    ///
    /// # Other considerations
    /// Implementations that perform IO are encouraged to make a best-effort attempt to yield a
    /// result as soon as it is correct to do so. For example, if a call to `fill_buf` requests 1025
    /// bytes, and some I/O method enters 1024 bytes into the buffer, returning `Ok(1024)` would be
    /// an implementation error (as explained above). However, it is also semantically correct to
    /// (for example) read 11 more 1024-byte chunks, then return `Ok(12 * 1024)`, but doing so is
    /// not encouraged. Once an implementation is able to efficiently check if it has fulfilled the
    /// minimum required amount, it should do so, and return `Ok`.
    ///
    /// For these purposes, `target == None` can be considered the same as `target == Some(1)`.
    ///
    /// # Errors
    /// This method returns `Err` if `Some(x)` was specified but `x` bytes were not available, or if
    /// `None` was specified and no bytes were available. Either of these situations can happen if
    /// the supplied buffer does not have enough capacity to fit the required number of bytes, as
    /// well as `self` lacking the requested bytes.
    ///
    /// If the implementation performs actual I/O operations, `Err` should also be returned whenever
    /// an I/O related error occurs, and we don't already have the minimum amount of bytes.
    ///
    /// # Panics
    /// Implementations are encouraged to _not_ panic unless they need to allocate bytes, and the
    /// allocation fails.
    fn fill_buf<B>(
        &mut self,
        buf: &mut B,
        target: Option<NonZeroUsize>,
    ) -> impl Future<Output = FillResult>
    where
        B: BufMut + ?Sized;
}

impl BufFill for &[u8] {
    async fn fill_buf<B>(&mut self, buf: &mut B, target: Option<NonZeroUsize>) -> FillResult
    where
        B: BufMut + ?Sized,
    {
        let len = core::cmp::min(self.len(), buf.remaining_mut());

        if len < usize::from(target.unwrap_or(NonZeroUsize::MIN)) {
            return Err(FillError::NotEnoughBytes);
        }

        buf.put_slice(&self[..len]);
        *self = &self[len..];

        Ok(len)
    }
}

impl BufFill for Vec<u8> {
    async fn fill_buf<B>(&mut self, buf: &mut B, target: Option<NonZeroUsize>) -> FillResult
    where
        B: BufMut + ?Sized,
    {
        let len = core::cmp::min(self.len(), buf.remaining_mut());
        if len < usize::from(target.unwrap_or(NonZeroUsize::MIN)) {
            return Err(FillError::NotEnoughBytes);
        }

        let drain = self.drain(..len);
        buf.put_slice(drain.as_slice());

        Ok(len)
    }
}

#[cfg(feature = "tokio")]
///
/// Adapter implementing [`BufFill`] on [`tokio::io::AsyncRead`]. Needs to have the `tokio` feature
/// enabled.
///
/// # Usage
/// ```
/// use tokio::io;
/// use yarms_packet_io::buf_fill::{AsyncReadAdapter, BufFill};
///
/// let async_read = io::empty();
/// let mut adapter = AsyncReadAdapter(async_read);
///
/// let mut buf_mut = Vec::new();
///
/// let result = yarms_util_future::runner::block_on(adapter.fill_buf(&mut buf_mut, None));
/// assert!(result.is_err())
/// ```
#[repr(transparent)]
pub struct AsyncReadAdapter<R>(pub R);

#[cfg(feature = "tokio")]
impl<R> BufFill for AsyncReadAdapter<R>
where
    R: tokio::io::AsyncRead,
{
    async fn fill_buf<B>(&mut self, buf: &mut B, target: Option<NonZeroUsize>) -> FillResult
    where
        B: BufMut + ?Sized,
    {
        let min = usize::from(target.unwrap_or(NonZeroUsize::MIN));
        let mut total = 0_usize;

        loop {
            let read = tokio::io::AsyncReadExt::read_buf(&mut self.0, buf).await?;
            if read == 0 {
                return Err(FillError::NotEnoughBytes);
            }

            total = match total.checked_add(read) {
                None => return Ok(usize::MAX),
                Some(result) => result,
            };

            if total >= min {
                return Ok(total);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::buf_fill::BufFill;
    use alloc::vec::Vec;
    use yarms_util_future::runner;

    #[test]
    fn simple_fill() {
        let mut storage = [0_u8, 1, 2, 3, 42];
        let mut fill = &mut &storage[..];

        let mut buf_mut = Vec::new();
        let result =
            runner::block_on(fill.fill_buf(&mut buf_mut, None)).expect("failed to fill buffer");

        assert_eq!(result, 5);
        assert_eq!(buf_mut.len(), 5);
        assert_eq!(storage[..], buf_mut);
    }
}
