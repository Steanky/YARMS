//!
//! Basic support for Minecraft protocol types. Can be used in a `no_std` environment, but can't be
//! used without `alloc`.
//!
//! This crate does not include packet definitions (see `yarms-packet` for that), but _does_ include
//! all the types that make up packets, including but not limited to:
//!
//! * [`types::VarInt`]
//! * [`types::VarLong`]
//! * [`types::VarString`]
//! * [`types::Boolean`]
//!
//! The implementation of these types is considered fairly "stable" between Minecraft protocol
//! versions. Therefore, it will not need to be updated as much as packet definitions might.
//!
//! # Features
//!
//! * `bmi2-intrinsics`: Compiles with intrinsics making use of the BMI2 extension, which can make
//!   some operations faster on certain hardware. This flag doesn't do anything if compiling for a
//!   target that does not support BMI2. For more information, see the documentation on
//!   [`util::BMI2_INTRINSICS`].
//! * `libdeflater`: Enables support for the `libdeflater` crate. This just allows for conversion
//!   between (de)compression error types and [`ReadError`].
//! * `std` (default): Enables `std` support. Currently, this just allows conversion between
//!   from [`ReadError`] to `std::io::Error`, and support for the `Io` variant of the [`ReadError`]
//!   enum.

#![no_std]

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

#[cfg(target_pointer_width = "16")]
///
/// We may need to index slices larger than 65535 for full support of the MC protocol.
compile_error!("This crate does not support 16-bit targets");

///
/// Basic protocol type definitions.
pub mod types;

///
/// Useful utilities.
pub mod util;

#[cfg(feature = "identifier")]
///
/// [`ProtocolRead`] and [`ProtocolWrite`] support for [`yarms_identifier::Identifier`].
pub mod identifier;

use alloc::string::String;
use bytes::{Buf, BufMut, TryGetError};
use core::fmt::{Debug, Display, Formatter};
use core::hash::{Hash, Hasher};

///
/// A type that can be read from a [`Buf`]. For the equivalent used when writing, see
/// [`ProtocolWrite`]. Most types that implement this trait will also want to implement
/// `ProtocolWrite`.
pub trait ProtocolRead {
    ///
    /// The output type. Commonly this is just `Self`, though it differs on e.g. unsized types.
    type Output;

    ///
    /// Reads the output type from an in-memory buffer. Advances the buffer by the number of bytes
    /// read.
    ///
    /// The `end_remaining` parameter is unused by the vast majority of implementations. It is
    /// necessary for some variable-length types whose size is defined as "the rest of the bytes in
    /// the packet". An example of such a type is [`types::RemainingByteArray`].
    ///
    /// For types that need it, `end_remaining` is the expected value returned by [`Buf::remaining`]
    /// when the entire packet has been read. Thus, it should generally be smaller than the current
    /// value of `.remaining()`, before this type has been fully read.
    ///
    /// If called on such a type, `end_remaining` _may_ be any valid `usize`, and implementations
    /// that need to make use of it should validate accordingly and return an appropriate error
    /// rather than panicking. In particular, it may be larger than [`Buf::remaining`].
    ///
    /// # Errors
    /// This function returns `Err` if the data encountered in the buffer is invalid for the output
    /// type, or if there are not enough bytes to read everything.
    fn read_from<B: Buf + ?Sized>(read: &mut B, end_remaining: usize) -> Result<Self::Output>;
}

///
/// A type that can be written to a [`BufMut`]. See [`ProtocolRead`] for the equivalent type used
/// when reading. Most types that implement this trait will also want to implement [`ProtocolRead`].
pub trait ProtocolWrite {
    ///
    /// Writes this type to an in-memory buffer, and returns the number of bytes that were written.
    ///
    /// # Panics
    /// This method panics if the size of the type exceeds the buffer's capacity. The size of any
    /// [`ProtocolWrite`] can be obtained via [`ProtocolWrite::len`]. The capacity of any [`BufMut`]
    /// can be obtained via [`BufMut::remaining_mut`].
    fn write_to<B: BufMut + ?Sized>(&self, write: &mut B) -> usize;

    ///
    /// Gets the length of this type, in bytes. This is the number of bytes that will be written
    /// if calling [`ProtocolWrite::write_to`] on this instance.
    ///
    /// Can be used to pre-size buffers ahead of time to ensure they can be written fully without
    /// possibility of panic.
    ///
    /// Reporting the wrong length is a logic error. Unsafe code must not place guarantees on the
    /// correct behavior of this function.
    ///
    /// Be aware that precomputing the size for some types might not be very efficient. A `Vec<T>`
    /// might need to be iterated to compute the total number of bytes, for example.
    fn len(&self) -> usize;
}

///
/// Type alias used for the result of reading a [`ProtocolType`] from a buffer.
pub type Result<T> = core::result::Result<T, ReadError>;

///
/// Common error type indicating an issue was encountered when attempting to read something from a
/// buffer, often (though not necessarily) in the context of network I/O. This includes validation
/// failures (bad data) as well as generic I/O problems.
#[derive(Debug)]
pub struct ReadError {
    reason: ErrorReason,
}

impl ReadError {
    ///
    /// Creates a new [`ReadError`] from the specified [`ErrorReason`].
    ///
    /// For a more ergonomic alternative in the common case of needing a static error message, see
    /// the [`validation_error`] macro.
    pub const fn new(reason: ErrorReason) -> Self {
        Self { reason }
    }
}

///
/// Reason for a read or write error. See [`ReadError`].
///
/// This enum is non-exhaustive, to ensure that variants can be added in minor releases.
/// Additionally, some variants (currently [`ErrorReason::Io`]) only exist when certain feature
/// flags are enabled.
#[derive(Debug)]
#[non_exhaustive]
pub enum ErrorReason {
    ///
    /// Validation failure. Optionally supplies a [`Message`] explaining the reason for the failure.
    ///
    /// Validation failure typically indicates that some parameter was intact, but its value is
    /// invalid for the given context, or in general.
    Validation(Option<Message>),

    ///
    /// Not enough bytes to read the full type.
    NotEnoughBytes,

    #[cfg(feature = "std")]
    ///
    /// Read error was caused by some sort of I/O failure. Only available if the `std` feature is
    /// enabled.
    Io(std::io::Error),
}

///
/// An error message. Can either be [`Message::Static`] (representing a fixed message) or
/// [`Message::Owned`] (representing a dynamic message constructed at runtime).
#[derive(Clone, Debug)]
pub enum Message {
    ///
    /// A static message, generally just a string literal. Useful for avoiding allocating a string,
    /// if the message won't change.
    Static(&'static str),

    ///
    /// An owned message. Prefer using [`Message::Static`] unless the error message has to be
    /// constructed dynamically.
    Owned(String),
}

impl Display for ReadError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "read {}", self.reason)
    }
}

impl core::error::Error for ReadError {}

impl Display for ErrorReason {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            ErrorReason::Validation(message) => match message {
                None => write!(f, "validation error"),
                Some(message) => write!(f, "validation error: {message}"),
            },
            ErrorReason::NotEnoughBytes => write!(f, "not enough bytes"),

            #[cfg(feature = "std")]
            ErrorReason::Io(io) => write!(f, "I/O error: {io}"),
        }
    }
}

impl AsRef<str> for Message {
    fn as_ref(&self) -> &str {
        match self {
            Message::Static(string) => string,
            Message::Owned(string) => string.as_str(),
        }
    }
}

impl PartialEq for Message {
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl Eq for Message {}

impl Hash for Message {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_ref().hash(state);
    }
}

impl Display for Message {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.as_ref())
    }
}

impl From<String> for Message {
    fn from(s: String) -> Self {
        Message::Owned(s)
    }
}

impl From<&'static str> for Message {
    fn from(s: &'static str) -> Self {
        Message::Static(s)
    }
}

#[cfg(feature = "std")]
impl From<ReadError> for std::io::Error {
    fn from(value: ReadError) -> Self {
        std::io::Error::new(std::io::ErrorKind::InvalidData, value)
    }
}

#[cfg(feature = "libdeflater")]
impl From<libdeflater::DecompressionError> for ReadError {
    fn from(value: libdeflater::DecompressionError) -> Self {
        let msg = match value {
            libdeflater::DecompressionError::BadData => "invalid compressed data",
            libdeflater::DecompressionError::InsufficientSpace => {
                "not enough space in output buffer for decompressed data"
            }
        };

        ReadError::new(ErrorReason::Validation(Some(Message::Static(msg))))
    }
}

impl From<TryGetError> for ReadError {
    fn from(_: TryGetError) -> Self {
        ReadError::new(ErrorReason::NotEnoughBytes)
    }
}
