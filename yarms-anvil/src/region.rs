use crate::loader::{AnvilReadError, AnvilReadResult};
use crate::{region_file_name, TableCache};
use hashbrown::hash_map::Entry;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::path::PathBuf;
use std::vec;

///
/// Loads Anvil regions from some source.
pub trait RegionLoader<Src: Read + Seek> {
    ///
    /// Loads a region, given its coordinates.
    ///
    /// Returns `Ok(None)` if no such region exists.
    ///
    /// # Errors
    /// Returns `Err` if there's an issue (usually IO) loading the region.
    fn load_region(&mut self, region_x: i32, region_z: i32) -> AnvilReadResult<Option<&mut Src>>;

    ///
    /// Computes the chunk offset and length (both in multiples of 4096) in the given region source
    /// `region`.
    ///
    /// Returns Ok(None) if the chunk isn't loaded yet, and thus does not exist in the region.
    ///
    /// This function should re-use data from `cache` if possible, and store new data for future
    /// use.
    ///
    /// # Errors
    /// Returns `Err` if there's an IO problem, or if the region contains invalid Anvil data.
    fn offset_and_size(
        cache: &TableCache,
        region: &mut Src,
        chunk_x: i32,
        chunk_z: i32,
    ) -> AnvilReadResult<Option<(u64, usize)>>;
}

///
/// [`RegionLoader`] implementation that assumes region files are available together in the same
/// root directory. Maintains a map of file handles, which are opened as needed.
pub struct FileRegionLoader {
    region_directory: PathBuf,
    region_files: hashbrown::HashMap<(i32, i32), File>,
}

impl RegionLoader<File> for FileRegionLoader {
    fn load_region(&mut self, region_x: i32, region_z: i32) -> AnvilReadResult<Option<&mut File>> {
        match self.region_files.entry((region_x, region_z)) {
            Entry::Occupied(value) => Ok(Some(value.into_mut())),

            Entry::Vacant(vacant) => {
                let buf = self
                    .region_directory
                    .join(region_file_name(region_x, region_z));

                if !std::fs::exists(&buf)? {
                    return Ok(None);
                }

                Ok(Some(vacant.insert(File::open(buf)?)))
            }
        }
    }

    fn offset_and_size(
        cache: &TableCache,
        region: &mut File,
        chunk_x: i32,
        chunk_z: i32,
    ) -> AnvilReadResult<Option<(u64, usize)>> {
        let region_x = chunk_x >> 5;
        let region_z = chunk_z >> 5;

        #[allow(
            clippy::cast_sign_loss,
            reason = "No sign loss; bitwise AND already removes high bits"
        )]
        let table_index = (((chunk_x & 31) | ((chunk_z & 31) << 5)) << 2) as usize;

        let table = match cache.get(&(region_x, region_z)) {
            Some(cache) => cache,
            None => cache
                .entry((region_x, region_z))
                .or_try_insert_with::<AnvilReadError>(|| {
                    let mut vec = vec![0_u8; 8192];

                    region.seek(SeekFrom::Start(0))?;
                    region.read_exact(&mut vec)?;

                    Ok(vec)
                })?
                .downgrade(),
        };

        let bytes = &table[table_index..table_index + 4];
        let sector_count = bytes[3];

        let mut offset = [0_u8; 4];
        offset[1] = bytes[0];
        offset[2] = bytes[1];
        offset[3] = bytes[2];

        drop(table);

        let offset = u32::from_be_bytes(offset);
        if offset == 0 && sector_count == 0 {
            // chunk has not been loaded yet
            return Ok(None);
        }

        let chunk_offset = u64::from(offset) * 4096;
        let chunk_size = usize::from(sector_count) * 4096;

        Ok(Some((chunk_offset, chunk_size)))
    }
}

impl FileRegionLoader {
    ///
    /// Creates a new [`FileRegionLoader`] that will load Anvil files present inside
    /// `region_directory`.
    #[must_use]
    pub fn new(region_directory: PathBuf) -> FileRegionLoader {
        FileRegionLoader {
            region_directory,
            region_files: hashbrown::HashMap::new(),
        }
    }
}
