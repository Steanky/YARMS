use alloc::vec;
use alloc::vec::Vec;
use core::cell::RefCell;
use yarms_chunk_loader::ChunkReadResult;

///
/// A data structure that stores Anvil header information. Implementations will generally want to
/// perform caching.
pub trait HeaderLookup<Source: ?Sized> {
    ///
    /// Looks up header information for the chunk, reading from `src` if necessary. Returns
    /// `Ok(None)` if the chunk doesn't exist (but otherwise no error occurred).
    ///
    /// If the result is `Ok(Some(x))`, the first parameter of the tuple `x` is the offset of the
    /// chunk within source `src`, and the second parameter is the length of the chunk. Both of
    /// these values must be in multiples of `4096`.
    ///
    /// # Errors
    /// Returns `Err` if an I/O error occurs, or if the data contained in the target source does
    /// not constitute a valid Anvil header.
    fn lookup(
        &self,
        src: &mut Source,
        chunk_x: i32,
        chunk_z: i32,
    ) -> ChunkReadResult<Option<(u64, usize)>>;
}

///
/// The size, in bytes, of the Anvil header which contains information about where chunks are
/// located in the file.
pub const HEADER_SIZE: usize = 8192;

///
///The size. in bytes, of the part of the Anvil header dedicated to storing chunk offsets.
pub const OFFSET_TABLE_SIZE: usize = 4096;

///
/// Compute the index into the header table for the specific chunk (world coordinates, not relative
/// to any region). See [`read_table`].
///
/// For all values of `chunk_x, chunk_z`, the returned value will be a multiple of 4 in range
/// `(0..4096)`.
#[inline]
#[must_use]
pub fn table_index(chunk_x: i32, chunk_z: i32) -> usize {
    #[allow(
        clippy::cast_sign_loss,
        reason = "No sign loss; bitwise AND already removes high bits"
    )]
    let index = (((chunk_x & 31) | ((chunk_z & 31) << 5)) << 2) as usize;
    index
}

///
/// Given an Anvil header table and an index, returns the recorded chunk offset (first parameter
/// of returned tuple) and padded chunk length (second parameter).
///
/// Both of these will be multiples of 4096.
///
/// # Panics
/// The length of `table` must be exactly `4096` bytes. If it isn't, this function will panic.
#[must_use]
pub fn read_chunk_offset(table: &[u8], table_index: usize) -> Option<(u64, usize)> {
    assert_eq!(
        table.len(),
        OFFSET_TABLE_SIZE,
        "chunk offset table must be exactly 4096 bytes"
    );

    let bytes = &table[table_index..table_index + 4];
    let sector_count = bytes[3];

    let mut offset = [0_u8; 4];
    offset[1] = bytes[0];
    offset[2] = bytes[1];
    offset[3] = bytes[2];

    let offset = u32::from_be_bytes(offset);
    if offset == 0 && sector_count == 0 {
        // chunk has not been loaded yet
        return None;
    }

    let chunk_offset = u64::from(offset) * 4096;
    let chunk_size = usize::from(sector_count) * 4096;

    Some((chunk_offset, chunk_size))
}

#[cfg(feature = "std")]
impl<Source> HeaderLookup<Source> for RefCell<lru::LruCache<(i32, i32), Vec<u8>>>
where
    Source: yarms_std::io::Read + yarms_std::io::Seek + ?Sized,
{
    fn lookup(
        &self,
        src: &mut Source,
        chunk_x: i32,
        chunk_z: i32,
    ) -> ChunkReadResult<Option<(u64, usize)>> {
        let mut borrow = self.borrow_mut();

        let table = borrow.try_get_or_insert::<_, yarms_std::io::Error>(
            (chunk_x >> 5, chunk_z >> 5),
            || {
                let mut vec = vec![0_u8; HEADER_SIZE];

                src.seek(yarms_std::io::SeekFrom::Start(0))?;
                src.read_exact(&mut vec)?;

                Ok(vec)
            },
        )?;

        Ok(read_chunk_offset(
            &table[..OFFSET_TABLE_SIZE],
            table_index(chunk_x, chunk_z),
        ))
    }
}

#[cfg(feature = "dashmap-header-lookup")]
impl<Source> HeaderLookup<Source> for dashmap::DashMap<(i32, i32), Vec<u8>>
where
    Source: yarms_std::io::Read + yarms_std::io::Seek + ?Sized,
{
    fn lookup(
        &self,
        src: &mut Source,
        chunk_x: i32,
        chunk_z: i32,
    ) -> ChunkReadResult<Option<(u64, usize)>> {
        let region_x = chunk_x >> 5;
        let region_z = chunk_z >> 5;

        let table = match self.get(&(region_x, region_z)) {
            Some(cache) => cache,
            None => self
                .entry((region_x, region_z))
                .or_try_insert_with::<yarms_chunk_loader::ChunkReadError>(|| {
                    let mut vec = vec![0_u8; HEADER_SIZE];

                    src.seek(yarms_std::io::SeekFrom::Start(0))?;
                    src.read_exact(&mut vec)?;

                    Ok(vec)
                })?
                .downgrade(),
        };

        Ok(read_chunk_offset(
            &table[..OFFSET_TABLE_SIZE],
            table_index(chunk_x, chunk_z),
        ))
    }
}

impl<Source, Inner> HeaderLookup<Source> for alloc::sync::Arc<Inner>
where
    Inner: HeaderLookup<Source>,
{
    #[inline]
    fn lookup(
        &self,
        src: &mut Source,
        chunk_x: i32,
        chunk_z: i32,
    ) -> ChunkReadResult<Option<(u64, usize)>> {
        let inner = alloc::sync::Arc::as_ref(self);
        inner.lookup(src, chunk_x, chunk_z)
    }
}

impl<Source, Inner> HeaderLookup<Source> for alloc::rc::Rc<Inner>
where
    Inner: HeaderLookup<Source>,
{
    #[inline]
    fn lookup(
        &self,
        src: &mut Source,
        chunk_x: i32,
        chunk_z: i32,
    ) -> ChunkReadResult<Option<(u64, usize)>> {
        let inner = alloc::rc::Rc::as_ref(self);
        inner.lookup(src, chunk_x, chunk_z)
    }
}
