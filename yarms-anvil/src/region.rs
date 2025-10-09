use crate::loader::{AnvilReadError, AnvilReadResult};
use crate::{region_file_name, TableCache};
use lru::LruCache;
use std::cell::RefCell;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::num::NonZeroUsize;
use std::ops::DerefMut;
use std::path::PathBuf;
use std::sync::{Arc, Mutex};
use std::thread::LocalKey;
use std::{io, vec};

///
/// Loads Anvil regions from some source.
pub trait RegionLoader<Src> {
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
/// Provides scoped mutable access to a [`RegionLoader`] implementation.
///
/// The main motivation behind this trait is to enable region loaders to be stored in thread locals.
/// However, general implementations also exist for `Arc<Mutex<L>> where L: RegionLoader` and
/// `Arc<L> where L: RegionLoader + Clone`. The former supports safe shared access with locking, the
/// latter is lock-free but may be expensive (as the region loader is cloned every time).
///
/// Thread locals are both cheap and lock-free, and so should be preferred over these other options
/// where possible.
pub trait RegionLoaderAccessor<Source, Loader> {
    ///
    /// Access the region loader by calling the provided callback function and returning its result.
    fn access_region_loader<R, Callback: FnOnce(&mut Loader) -> R>(self, callback: Callback) -> R;

    ///
    /// Creates a copy of this accessor, to be passed across thread boundaries.
    ///
    /// Note that `Self` must be `Send + 'static`!
    fn copy_for_thread(&self) -> Self
    where
        Self: Send + 'static;
}

impl<Source, Loader: RegionLoader<Source>> RegionLoaderAccessor<Source, Loader>
    for &'static LocalKey<RefCell<Loader>>
{
    #[inline]
    fn access_region_loader<R, Callback: FnOnce(&mut Loader) -> R>(self, callback: Callback) -> R {
        self.with_borrow_mut(|region_loader| callback(region_loader))
    }

    #[inline]
    fn copy_for_thread(&self) -> Self {
        self
    }
}

impl<Source, Loader: RegionLoader<Source>> RegionLoaderAccessor<Source, Loader>
    for Arc<Mutex<Loader>>
{
    #[inline]
    fn access_region_loader<R, Callback: FnOnce(&mut Loader) -> R>(self, callback: Callback) -> R {
        let mut guard = self.lock().unwrap();
        callback(guard.deref_mut())
    }

    #[inline]
    fn copy_for_thread(&self) -> Self {
        self.clone()
    }
}

impl<Source, Loader: RegionLoader<Source> + Clone> RegionLoaderAccessor<Source, Loader>
    for Arc<Loader>
{
    #[inline]
    fn access_region_loader<R, Callback: FnOnce(&mut Loader) -> R>(self, callback: Callback) -> R {
        let mut loader = self.as_ref().clone();
        callback(&mut loader)
    }

    #[inline]
    fn copy_for_thread(&self) -> Self {
        Arc::clone(self)
    }
}

///
/// [`RegionLoader`] implementation that assumes region files are available together in the same
/// root directory.
///
/// Stores file handles to regions in an [`LruCache`] for efficiency, the capacity of which can be
/// set in [`FileRegionLoader::new`].
pub struct FileRegionLoader {
    region_directory: PathBuf,
    region_files: LruCache<(i32, i32), File>,
}

impl RegionLoader<File> for FileRegionLoader {
    fn load_region(&mut self, region_x: i32, region_z: i32) -> AnvilReadResult<Option<&mut File>> {
        let result = self
            .region_files
            .try_get_or_insert_mut((region_x, region_z), || {
                let buf = self
                    .region_directory
                    .join(region_file_name(region_x, region_z));

                if !std::fs::exists(&buf).map_err(Some)? {
                    return Err(None::<io::Error>);
                }

                Ok(File::open(buf).map_err(Some)?)
            });

        match result {
            Ok(handle) => Ok(Some(handle)),

            // Err(None) is a special case that signals the file doesn't exist
            Err(None) => Ok(None),
            Err(Some(error)) => Err(AnvilReadError::Io(error)),
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
    ///
    /// Each instance will hold at most `max_file_handles` at one time.
    ///
    /// # Panics
    /// This function panics if `max_file_handles` is `0`.
    #[must_use]
    pub fn new(region_directory: PathBuf, max_file_handles: usize) -> FileRegionLoader {
        assert_ne!(max_file_handles, 0);

        FileRegionLoader {
            region_directory,
            region_files: LruCache::new(NonZeroUsize::new(max_file_handles).unwrap()),
        }
    }
}
