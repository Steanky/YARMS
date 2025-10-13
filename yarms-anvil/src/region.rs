use crate::region_to_file_name;
use core::num::NonZeroUsize;
use lru::LruCache;
use yarms_chunk_loader::ChunkReadResult;

///
/// Loads Anvil regions.
pub trait RegionLoader {
    ///
    /// The type containing the region data. This could be a [`std::fs::File`], for example. This
    /// is the type returned a successful call to [`RegionLoader::load_region`].
    type Source: ?Sized;

    ///
    /// Loads a region, given its coordinates.
    ///
    /// Returns `Ok(None)` if no such region exists.
    ///
    /// # Errors
    /// Returns `Err` if there's an issue (usually IO) loading the region.
    fn load_region(
        &mut self,
        region_x: i32,
        region_z: i32,
    ) -> ChunkReadResult<Option<&mut Self::Source>>;

    ///
    /// If this `RegionLoader` is caching a region, invalidates whatever the cached value is. This
    /// entails dropping the corresponding [`Self::Source`], if present.
    ///
    /// Returns `true` if calling this method actually did anything. False otherwise.
    /// Implementations that don't perform any caching don't need to implement this; the default
    /// always returns `false`.
    ///
    /// Even for implementations that do perform caching, this function may still return false if
    /// it can be determined that the underlying data did not actually change, and thus
    /// invalidating the cache would be wasteful.
    fn invalidate_cache(&mut self, _: i32, _: i32) -> bool {
        false
    }
}

#[cfg(feature = "std")]
///
/// [`RegionLoader`] implementation that assumes region files are available together in the same
/// root directory.
///
/// Stores file handles to regions in an [`LruCache`] for efficiency, the capacity of which can be
/// set in [`FileRegionLoader::new`].
pub struct FileRegionLoader {
    region_directory: std::path::PathBuf,
    region_files: LruCache<(i32, i32), Option<std::fs::File>>,
}

#[cfg(feature = "std")]
impl RegionLoader for FileRegionLoader {
    type Source = std::fs::File;

    fn load_region(
        &mut self,
        region_x: i32,
        region_z: i32,
    ) -> ChunkReadResult<Option<&mut Self::Source>> {
        self.region_files
            .try_get_or_insert_mut((region_x, region_z), || {
                let buf = self
                    .region_directory
                    .join(region_to_file_name(region_x, region_z));

                if !std::fs::exists(&buf)? {
                    return Ok(None);
                }

                Ok(Some(std::fs::File::open(buf)?))
            })
            .map(Option::as_mut)
    }

    fn invalidate_cache(&mut self, region_x: i32, region_z: i32) -> bool {
        self.region_files.pop(&(region_x, region_z)).is_some()
    }
}

#[cfg(feature = "std")]
impl FileRegionLoader {
    ///
    /// Creates a new [`FileRegionLoader`] that will load Anvil files present inside
    /// `region_directory`.
    ///
    /// Each instance will hold at most `max_file_handles` at one time.
    ///
    /// # Panics
    /// This function panics if `max_file_handles` is `0`.
    #[must_use]
    pub fn new(region_directory: std::path::PathBuf, max_file_handles: usize) -> FileRegionLoader {
        assert_ne!(
            max_file_handles, 0,
            "`max_file_handles` should have been at least 1"
        );

        FileRegionLoader {
            region_directory,
            region_files: LruCache::new(NonZeroUsize::try_from(max_file_handles).unwrap()),
        }
    }
}

#[cfg(feature = "std")]
///
/// Storage type for [`CursorRegionLoader`].
pub type InMemoryRegions = hashbrown::HashMap<(i32, i32), std::io::Cursor<alloc::vec::Vec<u8>>>;

#[cfg(feature = "std")]
///
/// An in-memory [`RegionLoader`]. Useful for testing and perhaps some caching schemes.
///
/// This loader will never fail to return `Ok` (though the contained `Option` may still be empty
/// depending on what data is stored).
pub struct CursorRegionLoader {
    regions: InMemoryRegions,
}

impl RegionLoader for CursorRegionLoader {
    type Source = std::io::Cursor<alloc::vec::Vec<u8>>;

    fn load_region(
        &mut self,
        region_x: i32,
        region_z: i32,
    ) -> ChunkReadResult<Option<&mut Self::Source>> {
        Ok(self.regions.get_mut(&(region_x, region_z)))
    }
}
