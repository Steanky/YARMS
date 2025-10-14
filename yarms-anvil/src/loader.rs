use crate::buffer::Buffer;
use crate::buffer::VecBuf;
use crate::chunk_decoder::ChunkDecoder;
use crate::header::HeaderLookup;
use crate::region::RegionLoader;
use core::cell::RefCell;
use libdeflater::Decompressor;
use maybe_owned::MaybeOwned;
use yarms_chunk_loader::ChunkReadResult;
use yarms_chunk_loader::{ChunkLoader, ChunkReadError, ThreadedChunkLoader};
use yarms_nbt::Tag;
use yarms_std::access::Accessor;
use yarms_threadpool::fixed_size::FixedSizePool;
use yarms_threadpool::new_fixed_size_pool;

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
///
/// Type alias for `&'static std::thread::LocalKey<RefCell<T>>`.
pub type ThreadLocal<T> = &'static std::thread::LocalKey<RefCell<T>>;

///
/// Helper method to load a chunk from an Anvil region, decode it, and execute a callback with the
/// resulting NBT data. This is used internally by [`AnvilLoader`], but it's designed to be useful
/// for custom implementations as well.
///
/// `callback` is invoked with `None` if the chunk can't be found in the region. However, if the
/// chunk can't be loaded (such as if there's an IO error) `callback` won't be invoked and the
/// function will return `Err`.
///
/// # Errors
/// Returns `Err` if there's a problem loading the chunk.
///
/// # Panics
/// This function may panic if `buffer_access` couldn't be accessed. This can occur if, for
/// example, `Buffers` is a [`RefCell`] that is already borrowed
pub fn load_from_region_loader<Buf, Buffers, Header, Source, Loader, Decoder, Call, R>(
    buffer_access: &Buffers,
    header_lookup: &Header,
    region_loader: &mut Loader,
    decoder: &Decoder,
    chunk_x: i32,
    chunk_z: i32,
    callback: Call,
) -> ChunkReadResult<R>
where
    Buf: Buffer,
    Buffers: Accessor<Target = (Buf, Buf)>,
    Header: HeaderLookup<Source> + ?Sized,
    Source: ?Sized,
    Loader: RegionLoader<Source = Source> + ?Sized,
    Decoder: ChunkDecoder<Source> + ?Sized,
    Call: for<'tag> FnOnce(Option<Tag<'tag>>) -> R,
{
    let Some(region) = region_loader.load_region(chunk_x >> 5, chunk_z >> 5)? else {
        return Ok(callback(None));
    };

    let Some((chunk_offset, chunk_size)) = header_lookup.lookup(region, chunk_x, chunk_z)? else {
        return Ok(callback(None));
    };

    buffer_access.access(|(chunk_read_buffer, decompression_buffer)| {
        decoder.decode(
            chunk_offset,
            chunk_size,
            region,
            chunk_read_buffer,
            decompression_buffer,
            move |tag| callback(Some(tag)),
        )
    })
}

///
/// A [`ChunkLoader`] implementation supporting the Anvil format. Conditionally supports parallel
/// chunk loads, if constructed using appropriate types.
pub struct AnvilLoader<'pool, Pool, Buffers, Header, Access, Decoder> {
    pool: MaybeOwned<'pool, Pool>,
    buffers: Buffers,
    header_lookup: Header,
    region_loader: Access,
    chunk_decoder: Decoder,
}

///
/// Builder struct used to construct instances of [`AnvilLoader`]. Use [`builder`] to create an
/// empty instance for configuration.
pub struct AnvilLoaderBuilder<'pool, Pool, Buffers, Header, Access, Decoder> {
    pool: Option<MaybeOwned<'pool, Pool>>,
    buffers: Option<Buffers>,
    header_lookup: Option<Header>,
    region_loader: Option<Access>,
    chunk_decoder: Option<Decoder>,
}

impl<'pool, Pool, Buffers, Header, Access, Decoder>
    AnvilLoaderBuilder<'pool, Pool, Buffers, Header, Access, Decoder>
{
    fn create_empty() -> Self {
        AnvilLoaderBuilder {
            pool: None,
            buffers: None,
            header_lookup: None,
            region_loader: None,
            chunk_decoder: None,
        }
    }

    ///
    /// Consumes this builder and returns a new [`AnvilLoader`].
    ///
    /// # Panics
    /// This function will panic if the builder has any missing (unspecified) fields.
    #[must_use]
    pub fn build(self) -> AnvilLoader<'pool, Pool, Buffers, Header, Access, Decoder> {
        macro_rules! expect {
            ( $i:ident ) => {
                self.$i
                    .expect(stringify!($i, " should have been specified"))
            };
        }

        AnvilLoader {
            pool: expect!(pool),
            buffers: expect!(buffers),
            header_lookup: expect!(header_lookup),
            region_loader: expect!(region_loader),
            chunk_decoder: expect!(chunk_decoder),
        }
    }
}

impl<Pool, Buffers, Header, Access, Decoder>
    AnvilLoaderBuilder<'_, Pool, Buffers, Header, Access, Decoder>
where
    Pool: yarms_threadpool::Pool,
{
    ///
    /// Use an owned [`yarms_threadpool::Pool`] instance to execute chunk loads.
    #[must_use]
    #[inline]
    pub fn with_owned_pool(self, pool: Pool) -> Self {
        AnvilLoaderBuilder {
            pool: Some(MaybeOwned::Owned(pool)),
            buffers: self.buffers,
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }

    ///
    /// Equivalent of [`Self::with_owned_pool`], but borrows the pool instead. This enables sharing
    /// a pool across multiple loaders.
    #[must_use]
    #[inline]
    pub fn with_borrowed_pool(
        self,
        pool: &'_ Pool,
    ) -> AnvilLoaderBuilder<'_, Pool, Buffers, Header, Access, Decoder> {
        AnvilLoaderBuilder {
            pool: Some(MaybeOwned::Borrowed(pool)),
            buffers: self.buffers,
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

impl<Buffers, Header, Access, Decoder>
    AnvilLoaderBuilder<'static, FixedSizePool, Buffers, Header, Access, Decoder>
{
    ///
    /// Use an owned [`FixedSizePool`] running `threads` threads.
    ///
    /// # Panics
    /// This function panics if `threads` is `0`.
    #[must_use]
    #[inline]
    pub fn with_fixed_pool(self, threads: usize) -> Self {
        AnvilLoaderBuilder {
            pool: Some(MaybeOwned::Owned(new_fixed_size_pool(threads))),
            buffers: self.buffers,
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

impl<Buffers, Header, Access, Decoder>
    AnvilLoaderBuilder<'static, (), Buffers, Header, Access, Decoder>
{
    ///
    /// Don't use a threadpool at all.
    #[must_use]
    #[inline]
    pub fn with_no_pool(self) -> Self {
        AnvilLoaderBuilder {
            pool: Some(MaybeOwned::Owned(())),
            buffers: self.buffers,
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

impl<Pool, Buf, Buffers, Header, Access, Decoder>
    AnvilLoaderBuilder<'_, Pool, Buffers, Header, Access, Decoder>
where
    Buf: Buffer,
    Buffers: Accessor<Target = (Buf, Buf)>,
{
    ///
    /// Use the provided chunk data and decompression buffers.
    #[must_use]
    pub fn with_buffers(self, buffers: Buffers) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: Some(buffers),
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

#[cfg(feature = "std")]
impl<Pool, Header, Access, Decoder>
    AnvilLoaderBuilder<
        '_,
        Pool,
        &'static std::thread::LocalKey<RefCell<(VecBuf, VecBuf)>>,
        Header,
        Access,
        Decoder,
    >
{
    ///
    /// Use thread local chunk data and decompression buffers. This is unnecessary if only a
    /// synchronous loader is needed.
    #[must_use]
    pub fn with_thread_local_buffers(self) -> Self {
        std::thread_local! {
            static BUFFERS: RefCell<(VecBuf, VecBuf)> = const {
                RefCell::new((VecBuf::new(), VecBuf::new()))
            }
        }

        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: Some(&BUFFERS),
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

impl<Pool, Header, Access, Decoder>
    AnvilLoaderBuilder<'_, Pool, RefCell<(VecBuf, VecBuf)>, Header, Access, Decoder>
{
    ///
    /// Use basic, non-thread-safe buffers.
    #[must_use]
    pub fn with_basic_buffers(self) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: Some(RefCell::new((VecBuf::new(), VecBuf::new()))),
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

impl<Pool, Buffers, Header, Access, Loader, Decoder>
    AnvilLoaderBuilder<'_, Pool, Buffers, Header, Access, Decoder>
where
    Header: HeaderLookup<Loader::Source>,
    Access: Accessor<Target = Loader>,
    Loader: RegionLoader,
{
    ///
    /// Use the provided [`HeaderLookup`] to read and cache Anvil header data. Its `Source`
    /// type parameter must match the type produced by [`RegionLoader`].
    #[must_use]
    pub fn with_header_lookup(self, header_lookup: Header) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: self.buffers,
            header_lookup: Some(header_lookup),
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

#[cfg(feature = "dashmap-header-lookup")]
impl<Pool, Buffers, Access, Decoder>
    AnvilLoaderBuilder<
        '_,
        Pool,
        Buffers,
        alloc::sync::Arc<dashmap::DashMap<(i32, i32), alloc::vec::Vec<u8>>>,
        Access,
        Decoder,
    >
{
    ///
    /// Uses a [`dashmap::DashMap`] to cache header information. This can share the data across
    /// threads, and so might be more efficient than a thread local (which would entail maintaining
    /// a separate cache for every thread).
    #[inline]
    #[must_use]
    pub fn with_dashmap_header_lookup(self) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: self.buffers,
            header_lookup: Some(alloc::sync::Arc::new(dashmap::DashMap::new())),
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

impl<Pool, Buffers, Access, Decoder>
    AnvilLoaderBuilder<
        '_,
        Pool,
        Buffers,
        core::cell::RefCell<lru::LruCache<(i32, i32), alloc::vec::Vec<u8>>>,
        Access,
        Decoder,
    >
{
    ///
    /// Use a [`lru::LruCache`] with the specified maximum `capacity` to cache Anvil header data.
    ///
    /// # Panics
    /// Panics if `capacity` is 0.
    #[inline]
    #[must_use]
    pub fn with_lru_header_lookup(self, capacity: usize) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: self.buffers,
            header_lookup: Some(RefCell::new(lru::LruCache::new(
                core::num::NonZeroUsize::try_from(capacity)
                    .expect("capacity should have been non-zero"),
            ))),
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
        }
    }
}

impl<Pool, Buffers, Header, Access, Loader, Decoder>
    AnvilLoaderBuilder<'_, Pool, Buffers, Header, Access, Decoder>
where
    Header: HeaderLookup<Loader::Source>,
    Access: Accessor<Target = Loader>,
    Loader: RegionLoader,
{
    ///
    /// Use the provided [`RegionLoader`] to load region sources. [`RegionLoader::Source`] must
    /// match the `Source` parameter of the [`HeaderLookup`].
    ///
    /// Since this function takes an [`Accessor`], you may pass a `&'static
    /// LocalKey<RegionLoader>`, `RefCell<RegionLoader>`, or `Arc<Mutex<RegionLoader>>`.
    #[inline]
    #[must_use]
    pub fn with_region_loader(self, region_loader: Access) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: self.buffers,
            header_lookup: self.header_lookup,
            region_loader: Some(region_loader),
            chunk_decoder: self.chunk_decoder,
        }
    }
}

impl<Pool, Buffers, Header, Access, Loader, Decoder>
    AnvilLoaderBuilder<'_, Pool, Buffers, Header, Access, Decoder>
where
    Access: Accessor<Target = Loader>,
    Loader: RegionLoader,
    Decoder: ChunkDecoder<Loader::Source>,
{
    ///
    /// Use the provided [`ChunkDecoder`] to decode chunks.
    #[inline]
    #[must_use]
    pub fn with_chunk_decoder(self, chunk_decoder: Decoder) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: self.buffers,
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: Some(chunk_decoder),
        }
    }
}

impl<Pool, Buffers, Header, Access, Loader, Decompress>
    AnvilLoaderBuilder<
        '_,
        Pool,
        Buffers,
        Header,
        Access,
        crate::chunk_decoder::Standard<Decompress>,
    >
where
    Access: Accessor<Target = Loader>,
    Loader: RegionLoader,
    <Loader as RegionLoader>::Source: yarms_std::io::Read + yarms_std::io::Seek,
    Decompress: Accessor<Target = Option<Decompressor>>,
{
    ///
    /// Use the standard decoder, that decodes from a seekable source, using the provided
    /// decompressor accessor.
    ///
    /// This requires a [`RegionLoader`] whose source is [`yarms_std::io::Read`] +
    /// [`yarms_std::io::Seek`].
    #[inline]
    #[must_use]
    pub fn with_standard_decoder(self, decompressors: Decompress) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: self.buffers,
            header_lookup: self.header_lookup,
            region_loader: self.region_loader,
            chunk_decoder: Some(crate::chunk_decoder::Standard::new(decompressors)),
        }
    }
}

impl<Pool, Buf, Buffers, Header, Source, Access, Loader, Decoder> ChunkLoader
    for AnvilLoader<'_, Pool, Buffers, Header, Access, Decoder>
where
    Buf: Buffer,
    Buffers: Accessor<Target = (Buf, Buf)>,
    Header: HeaderLookup<Source>,
    Access: Accessor<Target = Loader>,
    Source: ?Sized,
    Loader: RegionLoader<Source = Source>,
    Decoder: ChunkDecoder<Source>,
{
    fn load_chunk_sync<Callback, R>(
        &self,
        chunk_x: i32,
        chunk_z: i32,
        callback: Callback,
    ) -> ChunkReadResult<R>
    where
        Callback: for<'tag> FnOnce(Option<Tag<'tag>>) -> R,
    {
        self.region_loader.access(|region_loader| {
            load_from_region_loader(
                &self.buffers,
                &self.header_lookup,
                region_loader,
                &self.chunk_decoder,
                chunk_x,
                chunk_z,
                callback,
            )
        })
    }

    fn has_chunk(&self, chunk_x: i32, chunk_z: i32) -> ChunkReadResult<bool> {
        self.region_loader.access(|region_loader| {
            let Some(region) = region_loader.load_region(chunk_x >> 5, chunk_z >> 5)? else {
                return Ok(false);
            };

            Ok(self
                .header_lookup
                .lookup(region, chunk_x, chunk_z)?
                .is_some())
        })
    }
}

impl<Pool, Buf, Buffers, Header, Source, Access, Loader, Decoder> ThreadedChunkLoader
    for AnvilLoader<'_, Pool, Buffers, Header, Access, Decoder>
where
    Pool: yarms_threadpool::Pool,
    Buf: Buffer,
    Buffers: Accessor<Target = (Buf, Buf)> + Clone + Send + 'static,
    Header: HeaderLookup<Source> + Clone + Send + 'static,
    Access: Accessor<Target = Loader> + Clone + Send + 'static,
    Source: ?Sized,
    Loader: RegionLoader<Source = Source>,
    Decoder: ChunkDecoder<Source> + Clone + Send + 'static,
{
    fn load_chunk_async<Call, Err>(
        &self,
        chunk_x: i32,
        chunk_z: i32,
        callback: Call,
        err_handle: Err,
    ) where
        Call: for<'tag> FnOnce(Option<Tag<'tag>>) + Send + 'static,
        Err: FnOnce(ChunkReadError) + Send + 'static,
    {
        let loader_accessor = self.region_loader.clone();
        let buffer_accessor = self.buffers.clone();
        let header_lookup = self.header_lookup.clone();
        let decoder = self.chunk_decoder.clone();

        self.pool.submit(move || {
            let result = loader_accessor.access(|region_loader| {
                load_from_region_loader(
                    &buffer_accessor,
                    &header_lookup,
                    region_loader,
                    &decoder,
                    chunk_x,
                    chunk_z,
                    callback,
                )
            });

            if let Err(read_error) = result {
                err_handle(read_error);
            }
        });
    }
}

///
/// Constructs a new [`AnvilLoaderBuilder`], which can be used to create custom [`AnvilLoader`]
/// instances.
#[must_use]
pub fn builder<'pool, Pool, Buffers, Header, Access, Decoder>(
) -> AnvilLoaderBuilder<'pool, Pool, Buffers, Header, Access, Decoder> {
    AnvilLoaderBuilder::create_empty()
}
