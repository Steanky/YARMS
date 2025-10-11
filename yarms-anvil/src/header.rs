use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::RefCell;
use core::ops::Deref;
use yarms_chunk_loader::ChunkReadResult;

///
/// A data structure that stores Anvil header information. Implementations will generally perform
/// caching.
pub trait HeaderLookup<Source: ?Sized> {
    ///
    /// Looks up header information, reading from `src` if necessary.
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
/// Compute the index into the header table for the specific chunk (world coordinates, not relative
/// to any region).
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
/// Given a table and an index, returns the recorded chunk offset (first parameter of returned
/// tuple) and padded chunk length (second parameter).
///
/// Both of these will be multiples of 4096.
pub fn read_table<Bytes, Table>(table: Table, table_index: usize) -> Option<(u64, usize)>
where
    Bytes: AsRef<[u8]>,
    Table: Deref<Target = Bytes>,
{
    let slice = table.as_ref();

    let bytes = &slice[table_index..table_index + 4];
    let sector_count = bytes[3];

    let mut offset = [0_u8; 4];
    offset[1] = bytes[0];
    offset[2] = bytes[1];
    offset[3] = bytes[2];

    // table might be some sort of reference guard or lock:
    // explicitly drop as soon as we're done with it
    drop(table);

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
impl<Source, Inner> HeaderLookup<Source> for Arc<std::sync::Mutex<Inner>>
where
    Source: std::io::Read + std::io::Seek + ?Sized,
    Inner: HeaderLookup<Source>,
{
    #[inline]
    fn lookup(
        &self,
        src: &mut Source,
        chunk_x: i32,
        chunk_z: i32,
    ) -> ChunkReadResult<Option<(u64, usize)>> {
        self.lock().unwrap().lookup(src, chunk_x, chunk_z)
    }
}

#[cfg(feature = "std")]
impl<Source> HeaderLookup<Source> for RefCell<lru::LruCache<(i32, i32), Vec<u8>>>
where
    Source: std::io::Read + std::io::Seek + ?Sized,
{
    fn lookup(
        &self,
        src: &mut Source,
        chunk_x: i32,
        chunk_z: i32,
    ) -> ChunkReadResult<Option<(u64, usize)>> {
        let mut borrow = self.borrow_mut();

        let table = borrow.try_get_or_insert((chunk_x >> 5, chunk_z >> 5), || {
            let mut vec = vec![0_u8; HEADER_SIZE];

            src.seek(std::io::SeekFrom::Start(0))?;
            src.read_exact(&mut vec)?;

            Ok::<_, std::io::Error>(vec)
        })?;

        Ok(read_table(table, table_index(chunk_x, chunk_z)))
    }
}

#[cfg(feature = "dashmap-header-lookup")]
impl<Source> HeaderLookup<Source> for dashmap::DashMap<(i32, i32), Vec<u8>>
where
    Source: std::io::Read + std::io::Seek + ?Sized,
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

                    src.seek(std::io::SeekFrom::Start(0))?;
                    src.read_exact(&mut vec)?;

                    Ok(vec)
                })?
                .downgrade(),
        };

        Ok(read_table(table, table_index(chunk_x, chunk_z)))
    }
}
