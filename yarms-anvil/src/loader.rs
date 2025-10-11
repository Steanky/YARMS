use crate::access::Accessor;
use crate::buffer::Buffer;
use crate::chunk_decoder::ChunkDecoder;
use crate::header::HeaderLookup;
use crate::region::RegionLoader;
use core::cell::RefCell;
use maybe_owned::MaybeOwned;
use yarms_chunk_loader::ChunkReadResult;
use yarms_chunk_loader::{ChunkLoader, ChunkReadError, ThreadedChunkLoader};
use yarms_nbt::Tag;

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
pub struct AnvilLoader<'pool, Pool, Buffers, Header, Access, Decoder> {
    thread_pool: MaybeOwned<'pool, Pool>,
    buffers: Buffers,
    header_lookup: Header,
    region_loader: Access,
    decoder: Decoder,
}

impl<Pool, Buf, Buffers, Header, Access, Source, Loader, Decoder> ChunkLoader
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
                &self.decoder,
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

impl<Pool, Buf, Buffers, Header, Access, Source, Loader, Decoder> ThreadedChunkLoader
    for AnvilLoader<'_, Pool, Buffers, Header, Access, Decoder>
where
    Pool: yarms_threadpool::Pool,
    Buf: Buffer,
    Buffers: Accessor<Target = (Buf, Buf)> + Send + 'static,
    Header: HeaderLookup<Source> + Clone + Send + 'static,
    Access: Accessor<Target = Loader> + Send + 'static,
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
        let decoder = self.decoder.clone();

        self.thread_pool.submit(move || {
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
