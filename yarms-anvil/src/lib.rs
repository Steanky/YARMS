//!
//! Basic support for the Anvil protocol.
//!
//! This crate is always `no-std` compatible.
//!
//! # Features
//! * `alloc` (default): Enables convenience methods that can perform allocation.

#![no_std]

use bytes::BufMut;
use core::num::{NonZeroU32, NonZeroU64, NonZeroUsize};
use yarms_chunk_loader::{ChunkReadError, ChunkReadResult};
use yarms_std::{buf_fill::BufSeek, io::SeekFrom};

#[cfg(feature = "alloc")]
pub(crate) extern crate alloc;

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

const OFFSET_MASK: u32 = 0xFF_FF_FF_00_u32;
const LENGTH_MASK: u32 = 0x00_00_00_FF_u32;

#[inline]
fn valid_repr(repr: u32) -> bool {
    repr & OFFSET_MASK != 0 && repr & LENGTH_MASK != 0
}

impl ChunkPointer {
    ///
    /// Try to construct a [`ChunkPointer`] from 4 _big-endian_ bytes.
    ///
    /// Returns `None` if the _most significant_ 24 bits are zero, or the least significant 8 bits
    /// are zero, or all bits are zero.
    #[allow(
        clippy::missing_panics_doc,
        reason = "this function shouldn't actually panic"
    )]
    #[must_use]
    pub fn try_from_be_bytes(be_bytes: [u8; 4]) -> Option<Self> {
        let repr = u32::from_be_bytes(be_bytes);

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
        // get the 24 most significant bits and shift
        let sectors = u64::from((self.repr.get() & OFFSET_MASK) >> u8::BITS);

        // to catch UB in tests. this is NOT relied upon for safety in release builds!
        debug_assert!(
            (1..=0xFF_FF_FF_u64).contains(&sectors),
            "sectors out of range 0x01..=0xFFFFFF: {sectors}"
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
        // get the 8 least significant bits
        let sectors: u32 = self.repr.get() & LENGTH_MASK;

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
pub const fn region_coordinate(world_c: i32) -> i32 {
    world_c >> 5
}

///
/// Converts a world chunk coordinate into the region relative coordinate of the region it belongs
/// to. The returned value will be in range (0..32).
#[inline]
#[must_use]
pub const fn region_relative_coordinate(world_c: i32) -> i32 {
    world_c & 31
}

///
/// Number of entries in in an Anvil header. This corresponds to a single entry for each chunk in a
/// 32x32 region.
pub const HEADER_ENTRIES: usize = 1024;

///
/// Newtype wrapper representing an Anvil header.
#[derive(Debug, PartialEq, Eq, Hash)]
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
            reason = "this method is allowed to return anything for parameters outside 0..32"
        )]
        self.0
            .get((region_relative_x | (region_relative_z << 5)) as usize)
            .and_then(|x| *x)
    }
}

#[allow(clippy::cast_sign_loss, reason = "bithacking")]
const fn printed_length(n: i32) -> usize {
    match n {
        // special case i32::MIN because it will cause abs to overflow
        i32::MIN => 11,

        // special case 0 because it will cause ilog10 to panic
        0 => 1,

        // for all other values, compute the length by using ilog10, and add 1 if the original
        // value is negative
        n => (n.abs().ilog10() + ((n as u32) >> 31) + 1) as usize,
    }
}

#[allow(clippy::cast_sign_loss, reason = "bithacking")]
#[allow(clippy::cast_possible_truncation, reason = "bithacking")]
fn fill_region(mut region: i32, mut offset: usize, arr: &mut [u8]) {
    loop {
        arr[offset] = b'0' + ((region % 10).unsigned_abs() as u8);
        region /= 10;
        offset -= 1;

        if region == 0 {
            break;
        }
    }
}

///
/// The largest possible region file name. This can be used to pre-size e.g. an array on the stack
/// that can be used in a call to [`region_file_name_borrowed`].
pub const LARGEST_REGION_FILE_NAME: usize = region_file_name_len(i32::MIN, i32::MIN);

///
/// The smallest possible region file name.
pub const SMALLEST_REGION_FILE_NAME: usize = region_file_name_len(0, 0);

const BASE_REGION_NAME_LEN: usize = 7;

///
/// Computes the exact length that a particular region file name will need.
///
/// The smallest value is `SMALLEST_REGION_FILE_NAME`. The largest is `LARGEST_REGION_FILE_NAME`.
#[must_use]
pub const fn region_file_name_len(region_x: i32, region_z: i32) -> usize {
    BASE_REGION_NAME_LEN + printed_length(region_x) + printed_length(region_z)
}

#[cfg(feature = "alloc")]
///
/// Works exactly like [`region_file_name_borrowed`] but returns an owned
/// [`alloc::string::String`].
#[must_use]
#[allow(
    clippy::missing_panics_doc,
    reason = "only reason this would panic is a library bug"
)]
pub fn region_file_name_owned(region_x: i32, region_z: i32) -> alloc::string::String {
    use alloc::vec;

    let len = region_file_name_len(region_x, region_z);
    let mut storage = vec![0_u8; len];

    #[cfg(not(debug_assertions))]
    // SAFETY:
    // * we precisely pre-size our storage based on region_file_name_len, so region_file_name can't
    //   return None
    // * `region_file_name_borrowed` will write exactly `len` ASCII bytes to `storage`
    unsafe {
        region_file_name_borrowed(region_x, region_z, &mut storage).unwrap_unchecked();
        alloc::string::String::from_utf8_unchecked(storage)
    }

    #[cfg(debug_assertions)]
    {
        region_file_name_borrowed(region_x, region_z, &mut storage)
            .expect("storage should have enough room");
        alloc::string::String::from_utf8(storage).expect("string should be valid UTF-8")
    }
}

///
/// Computes a "region file name" (example: "r.0.-1.mca") from two given coordinates.
///
/// This function does not allocate, so it uses the bytes provided by `storage` to write the
/// result. If there aren't enough bytes, `None` is returned. Otherwise, it is guaranteed to write
/// precisely [`region_file_name_len`] bytes into the buffer. This function will _never_ write more
/// than [`LARGEST_REGION_FILE_NAME`] bytes.
///
/// If the `alloc` feature is enabled, users may also call [`region_file_name_owned`] to construct
/// an owned string.
///
/// # Example
/// ```
/// let mut storage = [0_u8; yarms_anvil::region_file_name_len(42, -42)];
/// let name = yarms_anvil::region_file_name_borrowed(42, -42, &mut storage).expect("should be a valid name");
///
/// let expected = "r.42.-42.mca";
/// assert_eq!(expected, name);
/// assert_eq!(storage, expected.as_ref());
/// ```
#[allow(
    clippy::missing_panics_doc,
    reason = "only reason this would panic is a library bug"
)]
pub fn region_file_name_borrowed(region_x: i32, region_z: i32, storage: &mut [u8]) -> Option<&str> {
    let x_len = printed_length(region_x);
    let z_len = printed_length(region_z);

    let total_len = BASE_REGION_NAME_LEN + x_len + z_len;

    if storage.len() < total_len {
        return None;
    }

    storage[0] = b'r';
    storage[1] = b'.';
    storage[2 + x_len] = b'.';
    storage[3 + x_len + z_len] = b'.';
    storage[4 + x_len + z_len] = b'm';
    storage[5 + x_len + z_len] = b'c';
    storage[6 + x_len + z_len] = b'a';

    if region_x < 0 {
        storage[2] = b'-';
    }

    if region_z < 0 {
        storage[3 + x_len] = b'-';
    }

    fill_region(region_x, 2 + x_len - 1, storage);
    fill_region(region_z, 3 + x_len + z_len - 1, storage);

    #[cfg(not(debug_assertions))]
    {
        // SAFETY:
        // * every byte in 0..total_len has been written, and is a valid ASCII byte
        Some(unsafe { str::from_utf8_unchecked(&storage[..total_len]) })
    }

    #[cfg(debug_assertions)]
    {
        Some(str::from_utf8(&storage[..total_len]).expect("string should be valid UTF-8"))
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

    struct DropGuard<'a>(&'a mut [u8]);

    impl Drop for DropGuard<'_> {
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
    // - Option<ChunkPointer> has size 4, is `repr(transparent)` to a `NonZero<u32>`, which is
    //   guaranteed to have the same and alignment as `u32`
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
    let clean = DropGuard(as_u8);
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
/// This function _may_ return `Err` if the chunk data pointed at by `pointer` is invalid. Exactly
/// which validity checks will be performed is unspecified.
///
/// This function will _always_ return `Err` if an IO error occurs while seeking to the offset of
/// `pointer`, or filling the buffer with the chunk bytes.
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

#[cfg(test)]
mod tests {
    extern crate alloc;
    extern crate std;

    use alloc::string::String;
    use alloc::string::ToString;
    use bytes::BytesMut;
    use yarms_nbt::tag;

    use crate::load_header;
    use crate::prepare_buffer;
    use crate::region_file_name_borrowed;
    use crate::AnvilHeader;
    use crate::Compression;
    use crate::HEADER_ENTRIES;
    use crate::LARGEST_REGION_FILE_NAME;
    use crate::NO_COMPRESSION;
    use crate::SECTOR_BYTES;

    use yarms_util_future::runner::block_on;

    fn check_name(expected: &mut String, storage: &mut [u8], x: i32, z: i32) {
        expected.clear();
        expected.push_str("r.");
        expected.push_str(x.to_string().as_str());
        expected.push_str(".");
        expected.push_str(z.to_string().as_str());
        expected.push_str(".mca");

        let actual = region_file_name_borrowed(x, z, storage).expect("should have enough storage");

        assert_eq!(expected, actual);
    }

    #[test]
    fn simple_chunk_load() {
        const S: usize = 8192;

        let mut storage = alloc::vec![0_u8; S + usize::from(SECTOR_BYTES)];

        // write the header: offset is 2 sectors (8192 bytes), length is 1 sector (4096 bytes)
        storage[0] = 0x00;
        storage[1] = 0x00;
        storage[2] = 0x02;
        storage[3] = 0x01;

        // write length prefix of 7
        storage[S] = 0x00;
        storage[S + 1] = 0x00;
        storage[S + 2] = 0x00;
        storage[S + 3] = 0x07;

        // this test chunk doesn't use compression
        storage[S + 4] = NO_COMPRESSION;

        // remainder of the data is chunk NBT:

        // root type is TAG_Compound
        storage[S + 5] = yarms_nbt::TAG_COMPOUND;

        // length of name is 2
        storage[S + 6] = 0x00;
        storage[S + 7] = 0x02;

        // the name of the root tag
        storage[S + 8] = b'H';
        storage[S + 9] = b'i';

        // end of the root tag
        storage[S + 10] = yarms_nbt::TAG_END;

        let mut cursor = std::io::Cursor::new(storage);
        let mut headers = [None; HEADER_ENTRIES];

        block_on(load_header(&mut cursor, &mut headers))
            .expect("should have enough bytes in cursor");

        let ptr = AnvilHeader(&mut headers)
            .pointer_at(0, 0)
            .expect("chunk 0, 0 should have a pointer");

        let mut buf = BytesMut::new();
        let meta = block_on(prepare_buffer(ptr, &mut buf, &mut cursor))
            .expect("chunk data should be valid and no IO error should occur");

        assert_eq!(meta.compression_type(), Compression::None);

        let start = meta.chunk_data_start();
        let len = meta.len().get();

        let buf = buf.as_ref();
        let chunk_data = &buf[start..start + len];

        let nbt = yarms_nbt::deserialize_file(chunk_data).expect("chunk should contain valid NBT");

        assert_eq!(nbt, tag!(Compound["Hi"]: {}));
    }

    #[test]
    fn basic_header_load() {
        let mut header = [0_u8; HEADER_ENTRIES * 4];
        header[0] = 0x00;
        header[1] = 0x00;
        header[2] = 0x42;
        header[3] = 0x10;

        let mut cursor = std::io::Cursor::new(header);

        let mut storage = [None; HEADER_ENTRIES];
        block_on(load_header(&mut cursor, &mut storage))
            .expect("should have enough bytes in cursor");

        let chunk = AnvilHeader(&mut storage)
            .pointer_at(0, 0)
            .expect("chunk 0, 0 should have a pointer");

        assert_eq!(chunk.offset_bytes().get(), 0x42 * u64::from(SECTOR_BYTES));
        assert_eq!(chunk.length_bytes().get(), 0x10 * usize::from(SECTOR_BYTES));
    }

    #[test]
    fn small_region_names() {
        let mut storage = [0u8; LARGEST_REGION_FILE_NAME];
        let mut expected = String::new();

        for x in i32::MIN..=(i32::MIN + 1000) {
            for z in i32::MIN..=(i32::MIN + 1000) {
                check_name(&mut expected, &mut storage, x, z);
            }
        }
    }

    #[test]
    fn around_zero_region_names() {
        let mut storage = [0u8; LARGEST_REGION_FILE_NAME];
        let mut expected = String::new();

        for x in -1000_i32..=1000 {
            for z in -1000_i32..=1000 {
                check_name(&mut expected, &mut storage, x, z);
            }
        }
    }

    #[test]
    fn large_region_names() {
        let mut storage = [0u8; LARGEST_REGION_FILE_NAME];
        let mut expected = String::new();

        for x in (i32::MAX - 1000)..=i32::MAX {
            for z in (i32::MAX - 1000)..=i32::MAX {
                check_name(&mut expected, &mut storage, x, z);
            }
        }
    }
}
