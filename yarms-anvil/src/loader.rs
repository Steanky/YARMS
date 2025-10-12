use crate::access::Accessor;
use crate::buffer::Buffer;
use crate::chunk_decoder::ChunkDecoder;
use crate::header::HeaderLookup;
use crate::region::RegionLoader;
use core::cell::RefCell;
use derive_builder::Builder;
use maybe_owned::MaybeOwned;
use yarms_chunk_loader::ChunkReadResult;
use yarms_chunk_loader::{ChunkLoader, ChunkReadError, ThreadedChunkLoader};
use yarms_nbt::Tag;
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
/// resulting NBT data.
///
/// # Errors
/// Returns `Err` if there's a problem loading the chunk.
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
/// A [`ChunkLoader`] implementation supporting the Anvil format.
#[derive(Builder)]
#[builder(pattern = "owned")]
#[builder(no_std, setter(prefix = "with"))]
pub struct AnvilLoader<'pool, Pool, Buffers, Header, Access, Decoder> {
    #[builder(setter(custom))]
    pool: MaybeOwned<'pool, Pool>,

    ///
    /// Set an [`Accessor`] providing access to a pair of [`Buffer`] implementations. These are used
    /// as scratch space by the chunk decoder when reading compressed bytes from a source, and
    /// temporarily writing the decompressed result, before decoding the contained NBT data.
    ///
    /// If the provided object is not `Send + 'static`, the resulting loader will not
    /// support asynchronous chunk loads.
    ///
    /// When loading asyncronously, note that `buffers` is cloned before each chunk is loaded. Be
    /// sure to use something like a thread local or `Arc` that can be efficiently cloned.
    buffers: Buffers,

    ///
    /// Define the storage space for Anvil header data.
    ///
    /// This can be anything that implements [`crate::header::HeaderLookup`], but only
    /// `Send + Sync + 'static` types will work if asynchronous loads are required.
    ///
    /// As with `buffers`, this field is cloned before every asynchronous chunk load, so care
    /// should be taken to ensure an efficient implementation is available.
    header_lookup: Header,

    ///
    /// Set a [`crate::region::RegionLoader`] that defines how regions are loaded into memory.
    ///
    /// A provided implementation is [`crate::region::FileRegionLoader`], which loads region files
    /// from a Minecraft region directory.
    region_loader: Access,

    ///
    /// Defines how chunks are actually decoded. Should implement
    /// [`crate::chunk_decoder::ChunkDecoder`]. Is also ultimately responsible for invoking the
    /// callback with the NBT data of the chunk.
    ///
    /// A provided implementation is [`crate::chunk_decoder::Standard`].
    chunk_decoder: Decoder,
}

impl<'pool, Pool, Buffers, Header, Access, Decoder>
    AnvilLoaderBuilder<'pool, Pool, Buffers, Header, Access, Decoder>
where
    Pool: yarms_threadpool::Pool,
{
    ///
    /// Use an owned [`yarms_threadpool::Pool`] instance to execute chunk loads.
    ///
    /// # Thread Safety
    /// This method is _compatible_ with a multithreaded loader.
    #[must_use]
    #[inline]
    pub fn with_owned_pool(
        self,
        pool: Pool,
    ) -> AnvilLoaderBuilder<'static, Pool, Buffers, Header, Access, Decoder> {
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
    ///
    /// # Thread Safety
    /// This method is _compatible_ with a multithreaded loader.
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
    /// # Thread Safety
    /// This method is compatible with a multithreaded loader.
    #[must_use]
    #[inline]
    pub fn with_fixed_pool(
        self,
        threads: usize,
    ) -> AnvilLoaderBuilder<'static, FixedSizePool, Buffers, Header, Access, Decoder> {
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
    ///
    /// # Thread Safety
    /// This method will cause the resulting builder to be _incompatible_ with parallel loads.
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

impl<'pool, Pool, Buffers, Access, Decoder>
    AnvilLoaderBuilder<
        'pool,
        Pool,
        Buffers,
        dashmap::DashMap<(i32, i32), alloc::vec::Vec<u8>>,
        Access,
        Decoder,
    >
{
    ///
    /// Uses a [`dashmap::DashMap`] to cache header information and share across threads.
    ///
    /// # Thread Safety
    /// This method is _compatible_ with a parallel loader.
    #[inline]
    pub fn with_dashmap_header_lookup(self) -> Self {
        AnvilLoaderBuilder {
            pool: self.pool,
            buffers: self.buffers,
            header_lookup: Some(dashmap::DashMap::new()),
            region_loader: self.region_loader,
            chunk_decoder: self.chunk_decoder,
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
/// Constructs a new [`AnvilLoaderBuilder`].
pub fn builder<'pool, Pool, Buffers, Header, Access, Decoder>(
) -> AnvilLoaderBuilder<'pool, Pool, Buffers, Header, Access, Decoder> {
    AnvilLoaderBuilder::create_empty()
}
