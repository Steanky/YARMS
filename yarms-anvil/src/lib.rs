//!
//! Basic support for the Anvil protocol.
//!
//! This crate is always `no-std` compatible and doesn't perform any allocation.
//!
//! # Features
//! * `std` (default): enables conversion between error types for dependent crates. Currently doesn't
//!   modify any of this crate's own code.

#![no_std]

use bytes::BufMut;
use core::num::{NonZeroU32, NonZeroU64, NonZeroUsize};
use yarms_chunk_loader::{ChunkReadError, ChunkReadResult};
use yarms_std::{buf_fill::BufSeek, io::SeekFrom};

#[cfg(target_pointer_width = "16")]
// We need to be capable of putting an entire chunk in a slice.
// The largest (compressed) chunk is 1048576 bytes, which is notably
// larger than u16::MAX.
compile_error!("This crate does not support 16-bit pointers!");

///
/// Maximum length of a chunk, as it appears before decompression.
/// Decompressed chunks may theoretically exceed this maximum size.
pub const MAX_CHUNK_BYTES: usize = (u8::MAX as usize) * (SECTOR_BYTES as usize);

///
/// Size, in bytes, of a single chunk "sector": `4096`.
pub const SECTOR_BYTES: u16 = 4096;

///
/// Compression type identifier for GZIP.
pub const GZIP_COMPRESSION: u8 = 1;

///
/// Compression type identifier for ZLIB.
pub const ZLIB_COMPRESSION: u8 = 2;

///
/// Compression type identifier for no compression.
pub const NO_COMPRESSION: u8 = 3;

///
/// Compression type identifier for LZ4.
pub const LZ4_COMPRESSION: u8 = 4;

///
/// Compression type identifier for custom compression.
pub const CUSTOM_COMPRESSION: u8 = 127;

///
/// Describes how chunk data is compressed (or if it is even compressed at all).
///
/// This enum can also represent "custom" compression types using the Custom variant.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum Compression<'b> {
    ///
    /// The chunk data was compressed with gzip.
    Gzip,

    ///
    /// The chunk data was compressed with Zlib. This is the typical format used by the modern
    /// Vanilla client.
    Zlib,

    ///
    /// The chunk data wasn't compressed at all.
    None,

    ///
    /// This chunk was compressed using the Lz4 algorithm.
    Lz4,

    ///
    /// A custom compression method was used to compress the chunk data. The contained string slice
    /// identifies it.
    Custom(&'b str),
}

///
/// Location and size information about a chunk stored in a seekable stream of Anvil data. Needed
/// to load chunk data using the [`prepare_buffer`] function.
///
/// This is derived from an Anvil header.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ChunkPointer {
    // NonZeroU32 to enable useful layout optimizations as well as efficient loading of
    // ChunkPointers from an Anvil header
    repr: NonZeroU32,
}

///
/// Contains information about a chunk before it has been decoded. This includes the compression
/// type used as well as the length of the (compressed) data.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct ChunkMeta<'b> {
    length: NonZeroU32,
    compression_type: Compression<'b>,
}

impl<'b> ChunkMeta<'b> {
    ///
    /// Creates a new [`ChunkMeta`].
    #[inline]
    #[must_use]
    pub fn new(length: i32, compression_type: Compression) -> Option<ChunkMeta> {
        if length <= 0 {
            return None;
        }

        // SAFETY:
        // * we check above that length is positive and non-zero
        // * all positive i32 can be losslessly converted to u32
        let length = unsafe { NonZeroU32::new_unchecked(u32::try_from(length).unwrap_unchecked()) };

        Some(ChunkMeta {
            length,
            compression_type,
        })
    }

    ///
    /// # Safety
    /// `length` must be non-negative and non-zero.
    unsafe fn new_unchecked(length: i32, compression_type: Compression) -> ChunkMeta {
        ChunkMeta {
            length: NonZeroU32::new_unchecked(u32::try_from(length).unwrap_unchecked()),
            compression_type,
        }
    }

    ///
    /// The exact length of the chunk data.
    #[inline]
    #[must_use]
    pub fn len(&self) -> NonZeroUsize {
        // SAFETY:
        // - the invariant that length is losslessly convertible to `usize` is established by the
        //   fact that we only support 32 bit or higher pointer widths
        unsafe { NonZeroUsize::try_from(self.length).unwrap_unchecked() }
    }

    ///
    /// The compression type used by the chunk data.
    #[inline]
    #[must_use]
    pub fn compression_type(&self) -> Compression<'b> {
        self.compression_type
    }

    ///
    /// Where the chunk data starts, relative to the beginning of a buffer filled by a call to
    /// [`prepare_buffer`].
    #[inline]
    #[must_use]
    pub fn chunk_data_start(&self) -> usize {
        match self.compression_type {
            Compression::Custom(string) => 7 + string.len(),
            _ => 5,
        }
    }
}

const OFFSET_MASK: u32 = 0x00_FF_FF_FF_u32;
const LENGTH_MASK: u32 = 0xFF_00_00_00_u32;

#[inline]
fn valid_repr(repr: u32) -> bool {
    repr & OFFSET_MASK != 0 && repr & LENGTH_MASK != 0
}

impl ChunkPointer {
    ///
    /// Try to construct a [`ChunkPointer`] from 4 _big-endian_ bytes.
    ///
    /// Returns `None` if the _most significant_ 8 bits are zero, or the least significant 24 bits
    /// are zero, or all bits are zero.
    #[allow(
        clippy::missing_panics_doc,
        reason = "this function shouldn't actually panic"
    )]
    #[must_use]
    pub fn try_from_bytes(bytes: [u8; 4]) -> Option<Self> {
        let repr = u32::from_be_bytes(bytes);

        // prevent from constructing an invalid ChunkLocation; this must also ensure that repr != 0
        if !valid_repr(repr) {
            return None;
        }

        #[cfg(debug_assertions)]
        {
            Some(Self {
                repr: NonZeroU32::new(repr).expect("repr should be non-zero"),
            })
        }

        #[cfg(not(debug_assertions))]
        // SAFETY:
        // * we just checked that `repr` is non-zero, because OFFSET_MASK and LENGTH_MASK cover all
        //   bits of `repr`, and neither masked region is 0
        unsafe {
            Some(Self {
                repr: NonZeroU32::new_unchecked(repr),
            })
        }
    }

    ///
    /// Defines where the chunk data is, relative to the start of the Anvil region. Similarly to
    /// [`ChunkPointer::length_bytes`], this is always a multiple of `SECTOR_BYTES` (4096).
    #[inline]
    #[must_use]
    pub fn offset_bytes(self) -> NonZeroU64 {
        let sectors = u64::from(self.repr.get() & OFFSET_MASK);

        // to catch UB in tests. this is NOT relied upon for safety in release builds!
        debug_assert!(
            (1..=0xFF_FF_FF_u64).contains(&sectors),
            "sectors out of range 0x01..=0xFFFFFF"
        );

        let result = sectors * u64::from(SECTOR_BYTES);

        // SAFETY:
        // * we know the 24 least-significant bits taken as a whole are non-zero due to the
        //   invariant enforced in `try_from_bytes`
        // * overflow cannot occur because the largest value for `result` is
        //   16777216 * 4096 = 68719476736, which is within the bounds of a `u64`
        unsafe { NonZeroU64::new_unchecked(result) }
    }

    ///
    /// Gets the imprecise length of the chunk. This is strictly larger than or equal to the actual
    /// size of the chunk. It is always a multiple of `SECTOR_BYTES` (4096).
    #[inline]
    #[must_use]
    pub fn length_bytes(self) -> NonZeroUsize {
        // get the 8 most significant bits
        let sectors: u32 = (self.repr.get() & LENGTH_MASK) >> (u32::BITS - 8);

        // to catch UB in tests. this is NOT relied upon for safety in release builds!
        debug_assert!(
            (1..=u32::from(u8::MAX)).contains(&sectors),
            "sectors out of range 0x01..=0xFF: {sectors}"
        );

        // SAFETY:
        // * all means of safely constructing a ChunkLocation ensure that the upper 8 bits are
        //   non-zero
        // * the largest value for `sectors` is 256, which means the largest value passed to the
        //   try_from is 256 * 4096 = 1048579, which is within the bounds of a 32-bit unsigned
        //   integer
        // * we only support 32-bit or higher pointer widths, so usize will never be smaller than a
        //   u32
        unsafe {
            let result = usize::try_from(sectors * u32::from(SECTOR_BYTES)).unwrap_unchecked();
            NonZeroUsize::new_unchecked(result)
        }
    }
}

///
/// Converts a "world chunk coordinate" into a region coordinate. This is the _coordinate of a
/// region_, NOT a chunk _within_ the region. For that, use [`region_relative_coordinate`].
#[inline]
#[must_use]
pub fn region_coordinate(world_c: i32) -> i32 {
    world_c >> 5
}

///
/// Converts a world chunk coordinate into the region relative coordinate of the region it belongs
/// to. The returned value will be in range (0..32).
#[inline]
#[must_use]
pub fn region_relative_coordinate(world_c: i32) -> i32 {
    world_c & 31
}

///
/// Number of entries in in an Anvil header. This corresponds to a single entry for each chunk in a
/// 32x32 region.
pub const HEADER_ENTRIES: usize = 1024;

///
/// Newtype wrapper representing an Anvil header.
pub struct AnvilHeader<'a>(pub &'a mut [Option<ChunkPointer>; HEADER_ENTRIES]);

impl AnvilHeader<'_> {
    ///
    /// Looks up a [`ChunkPointer`] in this header.
    ///
    /// Both `region_relative_x` and `region_relative_z` should be in range `0..32`. If this is not
    /// the case, this function will not panic, but the value it actually returns is not specified.
    #[inline]
    #[must_use]
    pub fn pointer_at(
        &self,
        region_relative_x: i32,
        region_relative_z: i32,
    ) -> Option<ChunkPointer> {
        #[allow(
            clippy::cast_sign_loss,
            reason = "this method is allowed to return anything when given numbers outside 0..32"
        )]
        self.0
            .get((region_relative_x | (region_relative_z << 5)) as usize)
            .and_then(|x| *x)
    }
}

///
/// Loads an Anvil header from `fill` into `storage`.
///
/// Returns `Ok` if data was correctly loaded.
/// This function will read exactly 4096 bytes from the _beginning_ of `fill`.
///
/// # Errors
/// Returns `Err` if there is a problem, which can occur when there is an IO error while trying to
/// read bytes from `fill`.
///
/// # Panics
/// This function will not panic (modulo library bugs) unless some implementation of `fill` panics.
/// In this instance, the contents of `storage` are _unspecified_: they may be left unmodified,
/// reset to `None`, partially modified, or anything else that doesn't result in UB or soundness
/// issues for the caller.
pub async fn load_header<F: BufSeek + ?Sized>(
    fill: &mut F,
    storage: &mut [Option<ChunkPointer>; HEADER_ENTRIES],
) -> ChunkReadResult<()> {
    // should always be 4, because of null pointer optimization
    static CHUNK_POINTER_SIZE: usize = core::mem::size_of::<Option<ChunkPointer>>();
    static BYTES: NonZeroUsize = NonZeroUsize::new(HEADER_ENTRIES * CHUNK_POINTER_SIZE).unwrap();

    // sanity check, Option<ChunkPointer> should always be 4 bytes
    static __: () = const {
        assert!(
            CHUNK_POINTER_SIZE == 4,
            "unexpected mem::size_of::<Option<ChunkPointer>>()"
        );
    };

    struct CleanOnDrop<'a>(&'a mut [u8]);

    impl Drop for CleanOnDrop<'_> {
        fn drop(&mut self) {
            // this usage of chunks_exact_mut seems to reliably lower to SIMD instructions
            for chunk in self.0.chunks_exact_mut(CHUNK_POINTER_SIZE) {
                #[cfg(target_endian = "little")]
                // Anvil header information is in big-endian by definition, so for little-endian
                // platforms we must reverse the byte order.
                chunk.reverse();

                // we perform a native endian transform because we already reverse the bytes
                // manually above; which must be done regardless in order for the resulting
                // ChunkPointers to be meaningful.
                let repr = u32::from_ne_bytes(chunk.try_into().unwrap());

                // ensure the ChunkPointer invariant is upheld
                // note that calling any of the SAFE methods of the ChunkPointers BEFORE this
                // validation step could result in UB if the validation would have failed (in other
                // words, there is transient unsoundness, but this is not actually a problem because
                // it is never exposed to the end user).
                if repr != 0 && !valid_repr(repr) {
                    chunk.fill(0);
                }
            }
        }
    }

    fill.seek(SeekFrom::Start(0)).await?;

    // SAFETY:
    // - Option<ChunkPointer> has size 4
    // - `storage` has ENTRIES elements
    // - BYTES = HEADER_ENTRIES * 4
    // - u8 has size 1
    // - therefore storage has BYTES u8 initialized and valid for both reads and writes
    let as_u8 = unsafe {
        core::slice::from_raw_parts_mut::<u8>(storage.as_mut_ptr().cast::<u8>(), BYTES.get())
    };

    // if this is dropped before having fully run through all of the chunks, this will clear the
    // entire byte array to avoid exposing ChunkPointer instances with an invalid internal state
    // that could lead to unsoundness.
    let clean = CleanOnDrop(as_u8);
    fill.fill_buf(&mut &mut *clean.0, Some(BYTES)).await?;

    Ok(())
}

///
/// Loads the data pointed at by `pointer` into the [`BufMut`] `buf`. Returns a [`ChunkMeta`]
/// describing the chunk data that was just filled into memory. The actual chunk data itself is not
/// validated.
///
/// This function will not allocate any new memory, with the exception of any allocation performed
/// by `buf` during filling.
///
/// # Errors
/// This function returns `Err` if there is an IO error loading chunk data from `fill`.
#[allow(
    clippy::missing_panics_doc,
    reason = "this function shouldn't actually panic"
)]
pub async fn prepare_buffer<'b, B: BufMut + AsRef<[u8]>, F: BufSeek>(
    pointer: ChunkPointer,
    buf: &'b mut B,
    fill: &mut F,
) -> ChunkReadResult<ChunkMeta<'b>> {
    //
    // The smallest chunk we care to consider is 4 bytes
    // note that this is way smaller than any real chunks will end up being, but it's a reasonable
    // lower bound as it's the smallest valid uncompressed TAG_Compound using file variant NBT
    const MIN_CHUNK_DATA_LEN: i32 = 4;

    //
    // The smallest chunk, plus 1 byte for the compression type.
    const MIN_LEN_PREFIX: i32 = MIN_CHUNK_DATA_LEN + 1;

    fill.seek(SeekFrom::Start(pointer.offset_bytes().get()))
        .await?;

    // smallest value for length is SECTOR_BYTES
    let length = pointer.length_bytes();

    fill.fill_buf(buf, Some(length)).await?;

    let buf = (*buf).as_ref();

    debug_assert!(
        buf.len() >= usize::from(SECTOR_BYTES),
        "buf.len() was less than SECTOR_BYTES"
    );

    // buf is at least SECTOR_BYTES long, so this shouldn't panic
    let mut actual_length = i32::from_be_bytes(buf[..4].try_into().unwrap());

    #[allow(
        clippy::cast_sign_loss,
        reason = "we check actual_length is non-negative"
    )]
    if actual_length < MIN_LEN_PREFIX || (actual_length as usize) > length.get() - 4 {
        return Err(ChunkReadError::Length);
    }

    let compression = match buf[4] {
        GZIP_COMPRESSION => Compression::Gzip,
        ZLIB_COMPRESSION => Compression::Zlib,
        NO_COMPRESSION => Compression::None,
        LZ4_COMPRESSION => Compression::Lz4,
        CUSTOM_COMPRESSION => {
            let str_len = u16::from_be_bytes(buf[5..7].try_into().unwrap());

            #[allow(
                clippy::cast_sign_loss,
                reason = "we checked actual_length is non-negative"
            )]
            if (3 + usize::from(str_len) + (MIN_CHUNK_DATA_LEN as usize)) > (actual_length as usize)
            {
                return Err(ChunkReadError::Length);
            }

            // subtract the string prefix bytes
            actual_length -= 2;

            // subtract the length of the compression type string
            actual_length -= i32::from(str_len);

            let compression_name = str::from_utf8(&buf[7..7 + usize::from(str_len)])
                .map_err(|_| ChunkReadError::UnknownCompressionType(CUSTOM_COMPRESSION))?;

            Compression::Custom(compression_name)
        }
        x => return Err(ChunkReadError::UnknownCompressionType(x)),
    };

    // the "compression type" byte is included in the length
    // now, actual_length is the length of our (possibly compressed) chunk data, excluding the
    // prefix bytes that we just interpreted
    actual_length -= 1;

    debug_assert!(
        actual_length >= MIN_CHUNK_DATA_LEN,
        "actual_length was less than MIN_CHUNK_DATA_LEN"
    );

    // SAFETY:
    // - actual_length is nonzero and non-negative
    Ok(unsafe { ChunkMeta::new_unchecked(actual_length, compression) })
}
