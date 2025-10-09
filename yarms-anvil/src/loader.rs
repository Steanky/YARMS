use libdeflater::DecompressionError;
use yarms_nbt::{NbtDeserializeError, Tag};

///
/// Trait for something that can load Anvil chunks.
pub trait AnvilLoader {
    ///
    /// Loads a chunk from somewhere. This is (often) the filesystem.
    ///
    /// This may be performed asynchronously, depending on the implementation. `callback` will be
    /// invoked with the resulting [`Tag`] containing the actual data when the chunk is done
    /// loading, or `None` if the chunk did not exist.
    ///
    /// # Errors
    /// This function doesn't itself return errors, because they may happen on a different thread.
    /// Instead, the callback function `err_callback` is provided, which implementations can call
    /// with an [`AnvilReadError`].
    fn load_chunk<Callback, ErrHandler>(
        &self,
        chunk_x: i32,
        chunk_z: i32,
        callback: Callback,
        err_callback: ErrHandler,
    ) where
        Callback: for<'tag> FnOnce(Option<Tag<'tag>>) + Send + 'static,
        ErrHandler: FnOnce(AnvilReadError) + Send + 'static;

    ///
    /// Checks if the chunk exists.
    ///
    /// # Errors
    /// This function may have to perform I/O to check if the chunk exists.
    fn has_chunk(&self, chunk_x: i32, chunk_z: i32) -> AnvilReadResult<bool>;
}

///
/// Error enum indicating problems that can arise when trying to read Anvil data.
#[derive(Debug)]
pub enum AnvilReadError {
    #[cfg(feature = "std")]
    ///
    /// An I/O related error occurred.
    Io(std::io::Error),

    ///
    /// The length of the data found was not as expected.
    BadLength,

    ///
    /// An unrecognized or unsupported chunk compression type was found.
    UnrecognizedCompressionType(u8),

    ///
    /// Chunk NBT data was invalid.
    BadNbt(NbtDeserializeError),

    ///
    /// A compressed chunk could not be decompressed.
    FailedDecompression(DecompressionError),
}

impl From<NbtDeserializeError> for AnvilReadError {
    fn from(value: NbtDeserializeError) -> Self {
        Self::BadNbt(value)
    }
}

impl From<DecompressionError> for AnvilReadError {
    fn from(value: DecompressionError) -> Self {
        Self::FailedDecompression(value)
    }
}

///
/// Result type used across most of this crate to represent a fallible result when attempting to
/// interpret Anvil data, read Anvil data from I/O, etc.
pub type AnvilReadResult<T> = Result<T, AnvilReadError>;

///
/// Type indicator showing we should decompress the chunk as `gzip` data. This is part of the Anvil
/// specification.
pub const GZIP_COMPRESSION: u8 = 1;

///
/// Type indicator showing we should decompress a chunk as `zlib` data. This is the most common type
/// found in vanilla.
pub const ZLIB_COMPRESSION: u8 = 2;

///
/// The chunk is uncompressed.
pub const NO_COMPRESSION: u8 = 3;

#[cfg(feature = "lz4")]
///
/// The chunk is using `lz4` compression. Requires enabling the `lz4` feature.
pub const LZ4_COMPRESSION: u8 = 4;

#[cfg(feature = "std")]
#[allow(clippy::std_instead_of_core, reason = "This module is std-only")]
#[allow(clippy::std_instead_of_alloc, reason = "This module is std-only")]
///
/// Loader-related features that require `std`.
pub mod std_dependent {
    use crate::buffer::VecBuf;
    use crate::chunk_decoder::ChunkDecoder;
    use crate::loader::{AnvilLoader, AnvilReadError, AnvilReadResult};
    use crate::region::{FileRegionLoader, RegionLoader, RegionLoaderAccessor};
    use alloc::vec::Vec;
    use dashmap::DashMap;
    use maybe_owned::MaybeOwned;
    use std::cell::RefCell;
    use std::io::{Read, Seek};
    use std::marker::PhantomData;
    use std::sync::Arc;
    use std::{io, thread_local};
    use yarms_nbt::Tag;
    use yarms_threadpool::ThreadPool;

    ///
    /// A cache shared between threads. Used to provide Anvil header data to all interested parties.
    pub type TableCache = Arc<DashMap<(i32, i32), Vec<u8>>>;

    impl From<io::Error> for AnvilReadError {
        fn from(value: io::Error) -> Self {
            AnvilReadError::Io(value)
        }
    }

    ///
    /// An [`AnvilLoader`] implementation that uses a thread pool for parallelizing chunk loads,
    /// owns its own [`TableCache`], and expects to read chunks from files in a specific directory.
    pub struct ThreadedAnvilLoader<'pool, LoaderAccessor, Source, Region, Decoder> {
        thread_pool: MaybeOwned<'pool, ThreadPool>,
        table_cache: TableCache,
        loader_accessor: LoaderAccessor,
        _marker: PhantomData<(Source, Region, Decoder)>,
    }

    ///
    /// Helper method to load a chunk given a mutable reference to a [`RegionLoader`], the chunk
    /// location itself, and a cache of information about the chunk offsets.
    ///
    /// # Errors
    /// Returns `Err` if there's a problem loading the chunk.
    pub fn load_from_region_loader<Source, Region, Callback, Decoder>(
        region_loader: &mut Region,
        chunk_x: i32,
        chunk_z: i32,
        table_cache: &TableCache,
        callback: Callback,
    ) -> AnvilReadResult<()>
    where
        Source: Read + Seek,
        Region: RegionLoader<Source>,
        Callback: for<'tag> FnOnce(Option<Tag<'tag>>) + Send + 'static,
        Decoder: ChunkDecoder,
    {
        thread_local! {
            static BUFFERS: RefCell<(VecBuf, VecBuf)> = const {
                RefCell::new((VecBuf::new(), VecBuf::new()))
            };
        }

        let region_x = chunk_x >> 5;
        let region_z = chunk_z >> 5;

        let Some(region) = region_loader.load_region(region_x, region_z)? else {
            callback(None);
            return Ok(());
        };

        let Some((chunk_offset, chunk_size)) =
            Region::offset_and_size(table_cache, region, chunk_x, chunk_z)?
        else {
            callback(None);
            return Ok(());
        };

        BUFFERS.with_borrow_mut(|(chunk_read_buffer, decompression_buffer)| {
            Decoder::decode(
                chunk_offset,
                chunk_size,
                region,
                chunk_read_buffer,
                decompression_buffer,
                move |tag| callback(Some(tag)),
            )
        })
    }

    thread_local! {
        static REGION_LOADERS: RefCell<Option<FileRegionLoader>> = const {
            RefCell::new(None)
        };
    }

    impl<Source, Region, LoaderProvider, Decoder> AnvilLoader
        for ThreadedAnvilLoader<'_, LoaderProvider, Source, Region, Decoder>
    where
        Source: Read + Seek,
        Region: RegionLoader<Source>,
        LoaderProvider: RegionLoaderAccessor<Source, Region> + Send + 'static,
        Decoder: ChunkDecoder,
    {
        fn load_chunk<Callback, ErrHandle>(
            &self,
            chunk_x: i32,
            chunk_z: i32,
            callback: Callback,
            err_handle: ErrHandle,
        ) where
            Callback: for<'tag> FnOnce(Option<Tag<'tag>>) + Send + 'static,
            ErrHandle: FnOnce(AnvilReadError) + Send + 'static,
        {
            let table_cache = Arc::clone(&self.table_cache);
            let loader_accessor = self.loader_accessor.copy_for_thread();

            self.thread_pool.submit(move || {
                let result = loader_accessor.access_region_loader(|region_loader| {
                    load_from_region_loader::<_, _, _, Decoder>(
                        region_loader,
                        chunk_x,
                        chunk_z,
                        &table_cache,
                        callback,
                    )
                });

                if let Err(read_error) = result {
                    err_handle(read_error);
                }
            });
        }

        fn has_chunk(&self, chunk_x: i32, chunk_z: i32) -> AnvilReadResult<bool> {
            self.loader_accessor
                .copy_for_thread()
                .access_region_loader(|region_loader| {
                    let region = match region_loader.load_region(chunk_x >> 5, chunk_z >> 5)? {
                        None => return Ok(false),
                        Some(file) => file,
                    };

                    Ok(
                        Region::offset_and_size(&self.table_cache, region, chunk_x, chunk_z)?
                            .is_some(),
                    )
                })
        }
    }
}
