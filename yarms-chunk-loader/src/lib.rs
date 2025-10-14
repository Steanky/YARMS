//!
//! General traits for loading chunks.
//!
//! Doesn't implement any actual chunk loading. See the `yarms-anvil` crate for an implementation of
//! the Anvil format.
//!
//! # Features
//! * `std` (default): Enables conversion between `std::io::Error` and [`ChunkReadError`].

#![no_std]

#[cfg(feature = "std")]
pub(crate) extern crate std;

use core::error::Error;
use core::fmt::{Display, Formatter};
use yarms_nbt::{NbtDeserializeError, Tag};

///
/// Something that can load Minecraft chunk data.
pub trait ChunkLoader {
    ///
    /// Loads a chunk from somewhere, often the filesystem, but that's not a requirement. `callback`
    /// is invoked with `None` if the chunk can't be loaded, and `Some` with a [`Tag`] containing
    /// the chunk data (see [chunk format](https://minecraft.wiki/w/Chunk_format) on the wiki). In
    /// either case, the method returns whatever `callback` did.
    ///
    /// # Errors
    /// Returns `Err` if an error occurred, such as if the chunk data was invalid, or couldn't be
    /// loaded correctly due to an I/O error. When this occurs, implementations should guarantee
    /// that `callback` was _not_ invoked.
    ///
    /// # Panics
    /// This function _may_ panic if the callback function tries to invoke any methods on this
    /// `ChunkLoader` instance. Implementations are not required to do so, however.
    fn load_chunk_sync<Callback, R>(
        &self,
        chunk_x: i32,
        chunk_z: i32,
        callback: Callback,
    ) -> ChunkReadResult<R>
    where
        Callback: for<'tag> FnOnce(Option<Tag<'tag>>) -> R;

    ///
    /// Checks if the chunk exists without loading it.
    ///
    /// The default implementation just calls [`ChunkLoader::load_chunk_sync`] and checks if `None`
    /// is received by the callback. Implementations are encouraged to override this behavior if it
    /// enhances efficiency.
    ///
    /// # Errors
    /// This function may have to perform I/O to check if the chunk exists.
    ///
    /// # Panics
    /// This function _may_ panic if the callback function tries to invoke any methods on this
    /// `ChunkLoader` instance. Implementations are not required to do so, however.
    fn has_chunk(&self, chunk_x: i32, chunk_z: i32) -> ChunkReadResult<bool> {
        self.load_chunk_sync(chunk_x, chunk_z, |chunk| chunk.is_some())
    }
}

///
/// Extension of [`ChunkLoader`] that specifies asynchronous methods of chunk loading.
pub trait ThreadedChunkLoader: ChunkLoader {
    ///
    /// Equivalent to [`ChunkLoader::load_chunk_sync`] but offloads the chunk loading to another
    /// thread.
    ///
    /// This method may return immediately, or it may block depending on conditions (such as
    /// available threads or other resource limitations). However, implementations should make a
    /// best-effort attempt to avoid blocking the calling thread.
    ///
    /// # Panics
    /// This function _may_ panic if the callback function(s) try to invoke any methods on this
    /// `ChunkLoader` instance. Implementations are not required to do so, however.
    fn load_chunk_async<Call, Err>(
        &self,
        chunk_x: i32,
        chunk_z: i32,
        callback: Call,
        err_callback: Err,
    ) where
        Call: for<'tag> FnOnce(Option<Tag<'tag>>) + Send + 'static,
        Err: FnOnce(ChunkReadError) + Send + 'static;
}

///
/// Result type returned by functions that decode Minecraft chunks.
pub type ChunkReadResult<T> = Result<T, ChunkReadError>;

///
/// Error enum indicating problems that can arise when trying to read a chunk from some source.
/// Variants may be added to this enum in the future, and so it is marked `non_exhaustive`.
#[derive(Debug)]
#[non_exhaustive]
pub enum ChunkReadError {
    #[cfg(feature = "std")]
    ///
    /// An I/O related error occurred.
    Io(yarms_std::io::Error),

    ///
    /// The length of some piece of data was not as expected.
    BadLength,

    ///
    /// Chunk NBT data was invalid.
    BadNbt(NbtDeserializeError),

    ///
    /// Couldn't decompress the chunk.
    FailedDecompression,
}

impl From<NbtDeserializeError> for ChunkReadError {
    fn from(value: NbtDeserializeError) -> Self {
        Self::BadNbt(value)
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

impl Display for ChunkReadError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match self {
            ChunkReadError::Io(e) => write!(f, "I/O error when reading chunk: {e}"),
            ChunkReadError::BadLength => write!(f, "bad length field when decoding chunk"),
            ChunkReadError::BadNbt(e) => write!(f, "chunk had invalid NBT data: {e}"),
            ChunkReadError::FailedDecompression => write!(f, "couldn't decompress chunk"),
        }
    }
}

impl Error for ChunkReadError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ChunkReadError::Io(cause) => Some(cause),
            ChunkReadError::BadNbt(cause) => Some(cause),
            _ => None,
        }
    }
}
