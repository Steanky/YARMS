use crate::ChunkData;
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
        Callback: for<'tag> FnOnce(Option<ChunkData<'tag>>) + Send + 'static,
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
    use crate::region::{FileRegionLoader, RegionLoader};
    use crate::ChunkData;
    use alloc::vec::Vec;
    use dashmap::DashMap;
    use maybe_owned::MaybeOwned;
    use std::cell::RefCell;
    use std::io::{Read, Seek};
    use std::num::NonZero;
    use std::path::PathBuf;
    use std::sync::Arc;
    use std::{io, thread_local};
    use yarms_threadpool::{new_thread_pool, ThreadPool};

    ///
    /// A thread-safe cache shared between threads. Used to provide Anvil header data to all
    /// interested parties.
    pub type TableCache = Arc<DashMap<(i32, i32), Vec<u8>>>;

    impl From<io::Error> for AnvilReadError {
        fn from(value: io::Error) -> Self {
            AnvilReadError::Io(value)
        }
    }

    ///
    /// An [`AnvilLoader`] implementation that uses a thread pool for parallelizing chunk loads,
    /// owns its own [`TableCache`], and expects to read chunks from files in a specific directory.
    pub struct ThreadedAnvilLoader<'pool, Decoder>
    where
        Decoder: ChunkDecoder,
    {
        thread_pool: MaybeOwned<'pool, ThreadPool>,
        region_directory: Arc<PathBuf>,
        table_cache: TableCache,
        _decoder: Decoder,
    }

    ///
    /// Helper method to load a chunk given a mutable reference to a [`RegionLoader`], the chunk
    /// location itself, and a cache of information about the chunk offsets.
    ///
    /// # Errors
    /// Returns `Err` if there's a problem loading the chunk.
    pub fn load_from_region_loader<Src, Loader, F, Decoder>(
        region_loader: &mut Loader,
        chunk_x: i32,
        chunk_z: i32,
        table_cache: &TableCache,
        callback: F,
    ) -> AnvilReadResult<()>
    where
        Src: Read + Seek,
        Loader: RegionLoader<Src>,
        F: for<'tag> FnOnce(Option<ChunkData<'tag>>) + Send + 'static,
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
            Loader::offset_and_size(table_cache, region, chunk_x, chunk_z)?
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
                move |tag| {
                    callback(Some(ChunkData {
                        tag,
                        chunk_x,
                        chunk_z,
                    }));
                },
            )
        })
    }

    thread_local! {
        static REGION_LOADERS: RefCell<Option<FileRegionLoader>> = const {
            RefCell::new(None)
        };
    }

    impl<Decoder> AnvilLoader for ThreadedAnvilLoader<'_, Decoder>
    where
        Decoder: ChunkDecoder,
    {
        fn load_chunk<Callback, ErrHandle>(
            &self,
            chunk_x: i32,
            chunk_z: i32,
            callback: Callback,
            err_handle: ErrHandle,
        ) where
            Callback: for<'tag> FnOnce(Option<ChunkData<'tag>>) + Send + 'static,
            ErrHandle: FnOnce(AnvilReadError) + Send + 'static,
        {
            let save_folder = Arc::clone(&self.region_directory);
            let table_cache = Arc::clone(&self.table_cache);

            self.thread_pool.submit(move || {
                let result = REGION_LOADERS.with_borrow_mut(move |file_region_loader| {
                    load_from_region_loader::<_, _, _, Decoder>(
                        file_region_loader
                            .get_or_insert_with(|| FileRegionLoader::new((*save_folder).clone())),
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
            REGION_LOADERS.with_borrow_mut(|file_region_loader| {
                let loader = file_region_loader
                    .get_or_insert_with(|| FileRegionLoader::new((*self.region_directory).clone()));

                let file = match loader.load_region(chunk_x >> 5, chunk_z >> 5)? {
                    None => return Ok(false),
                    Some(file) => file,
                };

                Ok(
                    FileRegionLoader::offset_and_size(&self.table_cache, file, chunk_x, chunk_z)?
                        .is_some(),
                )
            })
        }
    }

    ///
    /// Creates a new [`ThreadedAnvilLoader`] with its own dedicated [`ThreadPool`]. The number of
    /// threads used depends on the value of [`std::thread::available_parallelism`]:
    /// * If `available_parallelism` returns `Err`, the default parallelism is 4
    /// * Otherwise, the maximum value used is limited to 32, to preserve memory
    ///
    /// The loader will be able to load chunks from Anvil region files (.mca) in `region_directory`
    /// using its [`AnvilLoader::load_chunk`] method.
    pub fn threaded_loader<D: ChunkDecoder>(
        region_directory: PathBuf,
        decoder: D,
    ) -> ThreadedAnvilLoader<'static, D> {
        let threads = std::thread::available_parallelism()
            .map(NonZero::get)
            .unwrap_or(4);

        let thread_pool = new_thread_pool(core::cmp::min(threads, 32));
        ThreadedAnvilLoader {
            thread_pool: MaybeOwned::from(thread_pool),
            region_directory: Arc::new(region_directory),
            table_cache: Arc::new(DashMap::new()),
            _decoder: decoder,
        }
    }

    ///
    /// Creates a new [`ThreadedAnvilLoader`] from either a borrowed or owned [`ThreadPool`]. This
    /// allows multiple loaders to share the same pool.
    ///
    /// Otherwise, operates similarly to [`threaded_loader`].
    pub fn threaded_loader_with_pool<'pool, Decoder, Pool>(
        region_directory: PathBuf,
        pool: Pool,
        decoder: Decoder,
    ) -> ThreadedAnvilLoader<'pool, Decoder>
    where
        Decoder: ChunkDecoder,
        Pool: Into<MaybeOwned<'pool, ThreadPool>>,
    {
        ThreadedAnvilLoader {
            thread_pool: pool.into(),
            region_directory: Arc::new(region_directory),
            table_cache: Arc::new(DashMap::new()),
            _decoder: decoder,
        }
    }
}
