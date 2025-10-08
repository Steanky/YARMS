use crate::buffer::Buffer;
use crate::loader;
use crate::loader::{AnvilReadError, AnvilReadResult};
use libdeflater::Decompressor;
use std::cell::RefCell;
use std::io::{Read, Seek, SeekFrom};
use std::thread_local;
use yarms_nbt::Tag;

///
/// Trait specifying something that can decode a single chunk from an Anvil region file (.mca).
/// Implementations typically need to handle decompressing
///
/// This library provides a single "standard" implementation: [`Standard`].
pub trait ChunkDecoder {
    ///
    /// Given an offset into a region, a chunk size, and appropriate buffers, decodes a single
    /// chunk and passes the corresponding [`Tag`] to `callback`.
    ///
    /// # Errors
    /// Should return `Ok` if the callback was successfully invoked. Otherwise, the error type
    /// [`AnvilReadError`] will indicate which problem occurred.
    fn decode<Buf, Src, Callback>(
        chunk_offset: u64,
        chunk_size: usize,
        region: &mut Src,
        read_buffer: &mut Buf,
        decompress_buffer: &mut Buf,
        callback: Callback,
    ) -> AnvilReadResult<()>
    where
        Buf: Buffer,
        Callback: for<'tag> FnOnce(Tag<'tag>) + Send + 'static,
        Src: Read + Seek;
}

///
/// Standard chunk decoder.
///
/// Supports uncompressed, gzip, zlib and (if the feature flag is enabled) lz4 compression schemes.
/// Decompressors are stored in a thread local.
///
/// Uses [`yarms_nbt`] to decode the chunk data.
pub struct Standard;

impl ChunkDecoder for Standard {
    fn decode<Buf, Src, Callback>(
        chunk_offset: u64,
        chunk_size: usize,
        region: &mut Src,
        read_buffer: &mut Buf,
        decompress_buffer: &mut Buf,
        callback: Callback,
    ) -> AnvilReadResult<()>
    where
        Buf: Buffer,
        Callback: for<'tag> FnOnce(Tag<'tag>) + Send + 'static,
        Src: Read + Seek,
    {
        thread_local! {
            static DECOMPRESSORS: RefCell<Option<Decompressor>> = const { RefCell::new(None) };
        }

        let chunk_data = read_buffer.prepare(chunk_size, true);

        // seek to the start of the chunk
        region.seek(SeekFrom::Start(chunk_offset))?;

        // read the entire chunk, including padding at the end!
        region.read_exact(chunk_data)?;

        // get the length without padding
        let exact_length: usize = i32::from_be_bytes(
            chunk_data
                .get(0..4)
                .ok_or(AnvilReadError::BadLength)?
                .try_into()
                .expect("should always slice 4 bytes"),
        )
        .checked_sub(1)
        .ok_or(AnvilReadError::BadLength)?
        .try_into()
        .map_err(|_| AnvilReadError::BadLength)?;

        let compression_type = *chunk_data.get(4).ok_or(AnvilReadError::BadLength)?;

        let chunk_data = chunk_data
            .get(5..5 + exact_length)
            .ok_or(AnvilReadError::BadLength)?;

        let decompressed_chunk_data: &[u8] = match compression_type {
            loader::GZIP_COMPRESSION => {
                // this is part of the gzip specification:
                // the last 4 bytes are the decompressed length
                // we can use this to exactly size the output buffer
                let decompressed_len = u32::from_le_bytes(
                    chunk_data
                        .get(chunk_data.len() - 4..)
                        .ok_or(AnvilReadError::BadLength)?
                        .try_into()
                        .expect("should always slice 4 bytes"),
                ) as usize;

                DECOMPRESSORS.with_borrow_mut(|decompressor| {
                    let buffer = decompress_buffer.prepare(decompressed_len, true);

                    decompressor
                        .get_or_insert_with(Decompressor::new)
                        .gzip_decompress(chunk_data, buffer)?;

                    Ok::<_, AnvilReadError>(buffer)
                })?
            }

            loader::ZLIB_COMPRESSION => DECOMPRESSORS.with_borrow_mut(|decompressor| {
                let decompressor = decompressor.get_or_insert_with(Decompressor::new);

                let mut try_size = decompress_buffer
                    .all()
                    .map_or(chunk_size << 2, |slice| slice.len());

                let decompressed_length = loop {
                    // give the decompressor as much space as we have available!
                    let buffer = decompress_buffer.prepare(try_size, false);

                    match decompressor.zlib_decompress(chunk_data, buffer) {
                        Ok(bytes) => break bytes,

                        // we don't have enough space, double the buffer capacity and try again
                        Err(libdeflater::DecompressionError::InsufficientSpace) => try_size <<= 1,
                        Err(other) => return Err(other),
                    }
                };

                Ok(&decompress_buffer
                    .all()
                    .expect("should have initialized buffer")[..decompressed_length])
            })?,

            loader::NO_COMPRESSION => chunk_data,

            #[cfg(feature = "lz4")]
            loader::LZ4_COMPRESSION => {
                todo!()
            }

            ty => return Err(AnvilReadError::UnrecognizedCompressionType(ty)),
        };

        callback(yarms_nbt::deserialize_file(decompressed_chunk_data)?);
        Ok(())
    }
}
