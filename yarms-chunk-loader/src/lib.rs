//!
//! General traits for loading chunks.
//!
//! Doesn't implement any actual chunk loading. See the `yarms-anvil` crate for an implementation of
//! the Anvil format.
//!
//! # Features
//! * `std` (default): Enables conversion between `std::io::Error` and [`ChunkReadError`].
//! * `buf-fill` (default): Enables conversion between [`yarms_std::buf_fill::FillError`] and
//! [`ChunkReadError`].

#![no_std]

#[cfg(feature = "std")]
pub(crate) extern crate std;

use core::error::Error;
use core::fmt::{Display, Formatter};
use yarms_nbt::NbtDeserializeError;

///
/// Result type returned by functions that decode Minecraft chunks. The error type is
/// [`ChunkReadError`].
pub type ChunkReadResult<T> = Result<T, ChunkReadError>;

///
/// Error enum indicating problems that can arise when trying to read a chunk from some source.
/// Variants may be added to this enum in the future, and so it is marked `non_exhaustive`.
#[derive(Debug)]
#[non_exhaustive]
pub enum ChunkReadError {
    ///
    /// An I/O related error occurred. This variant is a thin wrapper around
    /// [`yarms_std::io::Error`].
    Io(yarms_std::io::Error),

    #[cfg(feature = "buf-fill")]
    ///
    /// A (usually I/O related) error occurred while filling up a buffer. This variant is a thin
    /// wrapper around [`yarms_std::buf_fill::FillError`].
    Fill(yarms_std::buf_fill::FillError),

    ///
    /// The length of some piece of data was not as expected.
    Length,

    BadHeader,

    ///
    /// Chunk NBT data was invalid.
    Nbt(NbtDeserializeError),

    UnknownCompressionType(u8),

    ///
    /// Couldn't decompress the chunk.
    Decompression,
}

impl From<NbtDeserializeError> for ChunkReadError {
    fn from(value: NbtDeserializeError) -> Self {
        Self::Nbt(value)
    }
}

impl From<yarms_std::io::Error> for ChunkReadError {
    fn from(value: yarms_std::io::Error) -> Self {
        Self::Io(value)
    }
}

#[cfg(feature = "std")]
impl From<std::io::Error> for ChunkReadError {
    fn from(value: std::io::Error) -> Self {
        Self::Io(yarms_std::io::Error::Io(value))
    }
}

#[cfg(feature = "std")]
impl From<ChunkReadError> for std::io::Error {
    fn from(value: ChunkReadError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, value)
    }
}

#[cfg(feature = "buf-fill")]
impl From<yarms_std::buf_fill::FillError> for ChunkReadError {
    fn from(value: yarms_std::buf_fill::FillError) -> Self {
        ChunkReadError::Fill(value)
    }
}

impl Display for ChunkReadError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        use ChunkReadError::*;

        match self {
            Io(e) => e.fmt(f),
            #[cfg(feature = "buf-fill")]
            Fill(e) => e.fmt(f),
            Length => f.write_str("bad length"),
            Nbt(e) => e.fmt(f),
            Decompression => f.write_str("decompression failed"),
            BadHeader => f.write_str("invalid Anvil header"),
            UnknownCompressionType(x) => write!(f, "unsupported compression type: {x}"),
        }
    }
}

impl Error for ChunkReadError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ChunkReadError::Io(cause) => Some(cause),

            #[cfg(feature = "buf-fill")]
            ChunkReadError::Fill(cause) => Some(cause),

            ChunkReadError::Nbt(cause) => Some(cause),
            _ => None,
        }
    }
}
