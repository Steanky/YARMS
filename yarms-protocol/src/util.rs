use crate::types::{VarInt, MAX_VAR_INT_BYTES};

use bytes::{Buf, BufMut};
use core::num::{NonZeroI64, NonZeroU64};

const SEGMENT_BITS: u8 = 0x7F;
const CONTINUE_BIT: u8 = 0x80;

const ALL_CONT_BITS: u64 = 0x0080_8080_8080;
const ALL_NUM_BITS: u64 = 0x007F_7F7F_7F7F;
const LOW_NUM_BITS: u64 = SEGMENT_BITS as u64;

///
/// Indicates the progress of reading or writing a VarInt/VarLong byte-by-byte.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum LebFlow {
    ///
    /// Indicates there are more bytes to be read or written.
    Continue,

    ///
    /// Indicates that the number has been read completely.
    Done,
}

const fn var_len_lookup_table<const LEN: usize>() -> [usize; LEN] {
    assert!(
        LEN <= (i32::MAX as usize),
        "LEN cannot be greater than i32::MAX"
    );

    let mut array = [0; LEN];

    let mut i = 0;

    #[allow(
        clippy::cast_possible_wrap,
        reason = "Wrapping can't happen because of above check"
    )]
    #[allow(
        clippy::cast_possible_truncation,
        reason = "Truncation can't happen because of above check"
    )]
    #[allow(
        clippy::cast_sign_loss,
        reason = "Sign loss can't happen because of above check"
    )]
    loop {
        if i >= LEN {
            break;
        }

        array[i] = (((((LEN - 2) as i32) - (i as i32)) / 7) + 1) as usize;
        i += 1;
    }

    array
}

static VAR_LONG_LEN_TABLE: [usize; 65] = var_len_lookup_table::<65>();

///
/// Returns the number of bytes required to encode the given value as a [`VarInt`]. The returned
/// value will _always_ be in range `[1, MAX_VAR_INT_BYTES]`, for all possible [`i32`]. Unsafe code
/// may use this as a guarantee.
#[inline]
#[allow(
    clippy::cast_sign_loss,
    reason = "Cast needed to get the lower bits of a value"
)]
#[must_use]
pub const fn var_int_len(val: i32) -> usize {
    ((var_int_len_bits(val as u32 as u64) >> 3) + 1) as usize
}

#[inline(always)]
#[allow(
    clippy::inline_always,
    reason = "This function is only used internally; inlining it is critical for performance"
)]
const fn var_int_len_bits(num: u64) -> u32 {
    // SAFETY:
    // - `x | 1` is nonzero for all x
    let non_zero_num = unsafe { NonZeroU64::new_unchecked(num | 1) };

    // since we are non-zero, this avoids needing to branch for the case num == 0
    let x = non_zero_num.ilog2();

    (x * 37) >> 5
}

#[inline(always)]
#[allow(
    clippy::inline_always,
    reason = "This function is only used internally; inlining it is critical for performance"
)]
fn select_sig_bits(significant_bits: u32, num: u64) -> u64 {
    #[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
    // SAFETY:
    // - we only use this intrinsic if we are on x86_64, and `bmi2` is available
    {
        unsafe { core::arch::x86_64::_bzhi_u64(num, significant_bits) }
    }

    #[cfg(not(all(target_arch = "x86_64", target_feature = "bmi2")))]
    // bithacking equivalent to `bzhi`
    {
        num & ((1 << u64::from(significant_bits)) - 1)
    }
}

///
/// Returns the number of bytes required to encode the given value as a `VarLong`. The returned
/// value will _always_ be in range `[1, MAX_VAR_LONG_BYTES]`, no matter the input. Unsafe code may
/// use this as a guarantee.
#[inline]
#[must_use]
pub const fn var_long_len(val: i64) -> usize {
    // SAFETY:
    // - `x | 1` is nonzero for all x
    let non_zero_val = unsafe { NonZeroI64::new_unchecked(val | 1) };
    VAR_LONG_LEN_TABLE[non_zero_val.leading_zeros() as usize]
}

///
/// Computes the length of some number of bytes, when prefixed by a [`VarInt`]. To do this, `length`
/// must first be converted to `i32`: it will saturate at [`i32::MAX`]. The returned value will
/// saturate at [`usize::MAX`].
#[must_use]
pub fn prefixed_len(length: usize) -> usize {
    var_int_len(i32::try_from(length).unwrap_or(i32::MAX)).saturating_add(length)
}

///
/// Shorthand for creating a validation error with a static message.
///
/// # Example
/// ```
/// use std::num::NonZeroUsize;
/// use yarms_protocol::validation_error;
///
/// // use `*Read` if you want a `yarms_protocol::ReadError` instead of a Result
/// let res = NonZeroUsize::new(0).ok_or_else(|| validation_error!(*Read "Expected non-zero value"));
///
/// assert!(res.is_err());
///
/// // result with an error type of `yarms_protocol::ReadError`
/// let err: yarms_protocol::Result<()> = validation_error!(Read "Read validation error occurred");
///
/// assert!(err.is_err())
/// ```
#[macro_export]
macro_rules! validation_error {
    ( Read $lit:expr ) => {
        core::result::Result::Err($crate::ReadError::new($crate::ErrorReason::Validation(
            core::option::Option::Some($crate::Message::Static($lit)),
        )))
    };

    ( *Read $lit:expr ) => {
        $crate::ReadError::new($crate::ErrorReason::Validation(core::option::Option::Some(
            $crate::Message::Static($lit),
        )))
    };
}

///
/// Macro for automatically generating an implementation of [`crate::ProtocolType`] on any
/// [`crate::ProtocolEnum`].
#[macro_export]
macro_rules! protocol_enum_impl {
    ( $enum_type:ty ) => {
        impl $crate::ProtocolType for $enum_type {
            fn read_from<B: bytes::buf::Buf + ?Sized>(
                read: &mut B,
            ) -> $crate::Result<Self> {
                const __ERROR_MSG: &str = concat!(
                    "invalid value for ",
                    stringify!($enum_type)
                );

                <Self as $crate::ProtocolEnum>::from_id(
                    <Self as $crate::ProtocolEnum>::Id::read_from(read)?,
                )
                .ok_or_else(|| {
                    $crate::validation_error!(*Read __ERROR_MSG)
                })
            }

            fn write_to<B: bytes::buf::BufMut + ?Sized>(
                &self,
                write: &mut B,
            ) -> usize {
                <Self as $crate::ProtocolEnum>::protocol_id().write_to(write)
            }

            fn len(&self) -> usize {
                <Self as $crate::ProtocolEnum>::protocol_id().len()
            }
        }
    };
}

#[cold]
#[inline(never)]
fn var_int_err() -> crate::Result<(usize, VarInt)> {
    validation_error!(Read "32-bit LEB-128 number out of range")
}

macro_rules! leb_128_impl {
    ( $val:ty, $uval:ty, $bits:literal, $read_name:ident, $write_name:ident ) => {
        ///
        /// Takes a single byte `next_byte` and attempts to interpret it as part of a LEB-128
        /// number. Call repeatedly until the returned result is [`LebFlow::Done`] to read the
        /// whole number.
        ///
        /// If the number is in-range but there are additional values
        /// to be read, returns [`LebFlow::Continue`]. If the number is in-range and there are no
        /// additional values, returns [`LebFlow::Done`].
        ///
        /// The resulting value is accumulated in `value`. The position is kept track of with `pos`.
        /// Both should be initially zero.
        ///
        /// # Errors
        /// If the number goes out of range for the given type (32 bits for a [`VarInt`], 64 for a
        /// [`crate::types::VarLong`]), returns an error.
        #[inline]
        pub const fn $read_name(byte_in: u8, pos: &mut usize, value: &mut $val) -> $crate::Result<$crate::util::LebFlow> {
            #[cold]
            #[inline(never)]
            const fn err() -> $crate::Result<$crate::util::LebFlow> {
                return $crate::validation_error!(Read concat!($bits, "-bit LEB128 number out of range"));
            }

            *value |= ((byte_in & SEGMENT_BITS) as $val) << *pos;
            if byte_in & CONTINUE_BIT == 0 {
                return core::result::Result::Ok($crate::util::LebFlow::Done);
            }

            *pos += 7;
            if *pos >= $bits {
                return err();
            }

            core::result::Result::Ok($crate::util::LebFlow::Continue)
        }

        ///
        /// Writes exactly 1 byte from `value` to `byte_out`, as an LEB-128 encoded number. Call
        /// repeatedly until the returned result is [`LebFlow::Done`] to convert the entire value.
        ///
        /// `value` is constantly modified by this function, until it has been fully written. This
        /// conversion cannot fail.
        #[inline]
        #[allow(
            clippy::cast_sign_loss,
            reason = "Cast needed to get the lower bits of a value"
        )]
        #[allow(
            clippy::cast_possible_truncation,
            reason = "Cast needed to get the lower bits of a value"
        )]
        #[allow(clippy::cast_possible_wrap, reason = "Only the bits are important")]
        pub const fn $write_name(byte_out: &mut u8, value: &mut $val) -> $crate::util::LebFlow {
            let byte = *value as u8;

            if (*value & !(SEGMENT_BITS as $val)) == 0 {
                *byte_out = byte;
                return $crate::util::LebFlow::Done;
            }

            *value = ((*value as $uval) >> 7) as $val;
            *byte_out = byte | CONTINUE_BIT;
            $crate::util::LebFlow::Continue
        }
    };
}

leb_128_impl!(i32, u32, 32, var_int_advance_read, var_int_advance_write);
leb_128_impl!(i64, u64, 64, var_long_advance_read, var_long_advance_write);

///
/// Constant indicating whether `BMI2` intrinsics are enabled.
///
/// `BMI2` is a "Bit Manipulation Instruction" set which is an extension for x86. It is not
/// supported by all x86 processors. It is used by this crate to enable significant performance
/// enhancements for some operations, particularly encoding and decoding [`VarInt`]s. However, on
/// some CPUs, this may instead result in performance _degradation_ due to some of the intrinsics
/// being implemented in microcode, and thus lacking true "hardware support". Consider running the
/// benchmarks to determine if this is a problem for your target system.
///
/// `BMI2` intrinsics are disabled by default, and can be enabled with the feature flag
/// `bmi2-intrinsics`. If the target architecture does not support `BMI2`, enabling the feature will
/// have no effect (this constant will remain `false`).
///
/// Unsafe code may rely on this constant to indicate the following conditions are _all_ true:
/// * The target architecture is `x86_64`
/// * The target architecture supports `bmi2` instructions
/// * The `bmi2-intrinsics` feature flag is enabled
pub const BMI2_INTRINSICS: bool = cfg!(all(
    target_arch = "x86_64",
    target_feature = "bmi2",
    feature = "bmi2-intrinsics"
));

#[inline(always)]
#[allow(
    clippy::inline_always,
    reason = "This function is only used internally; inlining it is critical for performance"
)]
fn compute_var_int(packed_num: u64) -> i32 {
    if BMI2_INTRINSICS {
        #[cfg(target_arch = "x86_64")]
        #[allow(
            clippy::cast_possible_truncation,
            reason = "The upper 32 bits are always zero"
        )]
        // SAFETY:
        // - we only use this intrinsic if `bmi2` is available, and we are on x86_64
        unsafe {
            core::arch::x86_64::_pext_u64(packed_num, ALL_NUM_BITS) as i32
        }

        #[cfg(not(target_arch = "x86_64"))]
        // SAFETY:
        // - on non-x86_64 targets, this cannot be reached because `cfg` will return false
        unsafe {
            core::hint::unreachable_unchecked()
        }
    } else {
        #[allow(
            clippy::cast_possible_truncation,
            reason = "The upper 32 bits are always zero"
        )]
        #[allow(clippy::identity_op, reason = "Code clarity")]
        #[allow(clippy::erasing_op, reason = "Code clarity")]
        {
            let mut result: u64 = 0;
            result |= (packed_num >> 0) & (LOW_NUM_BITS << (0 * 7));
            result |= (packed_num >> 1) & (LOW_NUM_BITS << (1 * 7));
            result |= (packed_num >> 2) & (LOW_NUM_BITS << (2 * 7));
            result |= (packed_num >> 3) & (LOW_NUM_BITS << (3 * 7));
            result |= (packed_num >> 4) & (LOW_NUM_BITS << (4 * 7));

            result as i32
        }
    }
}

///
/// Reads a 32-bit signed integer as a [`VarInt`] from an array of length [`MAX_VAR_INT_BYTES`]. The
/// actual `VarInt` can be encoded in fewer bytes, or it can be encoded "inefficiently" (use more
/// bytes than strictly necessary).
///
/// Only as many bytes as necessary are read. Bytes after the first valid `VarInt` encoded value are
/// ignored.
///
/// The first parameter of the returned tuple is the number of bytes that actually made up the
/// `VarInt`. It is possible for this value to differ from [`VarInt::len`], as it currently assumes
/// the most compact possible encoding, while this function allows for "inefficient" encodings up to
/// the maximum number of bytes [`MAX_VAR_INT_BYTES`]. To use networking as an example, a client
/// might send the length prefix `42` encoded in 5 bytes:
///
/// ```rust
/// use yarms_protocol::ProtocolWrite;
/// use yarms_protocol::util::var_int_read;
///
/// // 42 in VarInt, but encoded using 5 bytes instead of 1...
/// let inefficient_encoding = [0xAA, 0x80, 0x80, 0x80, 0x00];
///
/// let (length, value) = var_int_read(&inefficient_encoding).expect("VarInt should be valid");
///
/// assert_eq!(42, *value);
///
/// // length is 5 because that's how many bytes we needed to read the value...
/// assert_eq!(5, length);
///
/// // ...however, `.len()` returns 1, because if we WROTE `value`, we'd use the more
/// // space-efficient encoding!
/// assert_eq!(1, value.len());
/// ```
///
/// # Errors
/// If the slice contains no valid `VarInt`, returns `Err`.
#[inline]
pub fn var_int_read(input: &[u8; MAX_VAR_INT_BYTES]) -> crate::Result<(usize, VarInt)> {
    let mut buf = [0_u8; size_of::<u64>()];
    buf[..MAX_VAR_INT_BYTES].copy_from_slice(input);

    let num = u64::from_le_bytes(buf);

    // we invert num so we can use `trailing_zeros` to get the number of bits we care about
    let inverted_cont_bits = !num & ALL_CONT_BITS;

    // if zero, means we didn't get a termination bit so the number is invalid
    if inverted_cont_bits == 0 {
        // this is a cold path, optimize accordingly
        return var_int_err();
    }

    // number of bits we care about, there may be garbage data in `num`
    let significant_bits = inverted_cont_bits.trailing_zeros() + 1;

    // selects only our needed bits from `num`
    let num = select_sig_bits(significant_bits, num);

    // actually compute the VarInt
    let res = compute_var_int(num);

    Ok(((significant_bits >> 3) as usize, VarInt::from(res)))
}

///
/// Encodes a [`VarInt`] directly to a [`BufMut`]. The buffer will be advanced by the number of
/// bytes written (the value returned by this function).
///
/// The number of bytes written is _guaranteed_ to equal `var_int_len(input)` for all possible
/// values of `input`.
///
/// # Panics
/// This function panics if and only if the [`BufMut::put_slice`] function panics when called with
/// a slice of `var_int_len(input)` bytes.
#[inline]
pub fn var_int_write_buf<B: BufMut + ?Sized>(input: i32, output: &mut B) -> usize {
    #[allow(
        clippy::cast_sign_loss,
        reason = "We only care about the raw bits, not the sign"
    )]
    let input = u64::from(input as u32);

    let len = var_int_len_bits(input);

    let num = var_int_write(input, len);
    let len = ((len >> 3) + 1) as usize;

    let array: [u8; size_of::<u64>()] = num.to_le_bytes();

    // SAFETY:
    // - `len` is always in range [1, MAX_VAR_INT_BYTES], which is always smaller than 8 bytes
    unsafe {
        output.put_slice(array.get_unchecked(..len));
    }

    len
}

#[cold]
#[inline(never)]
fn read_disjoint<B: Buf + ?Sized>(read: &mut B) -> crate::Result<(usize, VarInt)> {
    let mut pos = 0;
    let mut value = 0;
    let mut len = 0;
    loop {
        len += 1;

        if var_int_advance_read(read.try_get_u8()?, &mut pos, &mut value)? == LebFlow::Done {
            return Ok((len, VarInt::from(value)));
        }
    }
}

///
/// Reads a [`VarInt`] directly from a buffer [`Buf`]. Advances it by the number of bytes read.
///
/// This function is specifically optimized for the case where [`Buf::chunk`] returns a slice of at
/// least [`MAX_VAR_INT_BYTES`]. It may be less efficient on non-contiguous buffers where a `VarInt`
/// is split across chunk boundaries.
///
/// # Errors
/// Returns `Err` if the buffer does not contain enough bytes.
#[inline]
#[allow(clippy::missing_panics_doc, reason = "Shouldn't actually panic")]
pub fn var_int_read_buf<B: Buf + ?Sized>(read: &mut B) -> crate::Result<(usize, VarInt)> {
    let chunk = read.chunk();

    if chunk.len() >= MAX_VAR_INT_BYTES {
        // can't actually panic, due to the above length check
        let array: &[u8; MAX_VAR_INT_BYTES] = &chunk[..MAX_VAR_INT_BYTES].try_into().unwrap();

        let (len, var_int) = var_int_read(array)?;

        // shouldn't panic because we observed at least `len` bytes
        read.advance(len);

        Ok((len, var_int))
    } else if chunk.len() == read.remaining() {
        match var_int_partial_read(chunk) {
            PartialRead::NeedsBytes => var_int_err(),
            PartialRead::Done(len, value) => {
                // shouldn't panic because we observed at least `len` bytes
                read.advance(len);

                Ok((len, value))
            }
        }
    } else {
        // slow path:
        // - the buffer is non-contiguous
        // - we have a tiny buffer size < MAX_VAR_INT_BYTES
        read_disjoint(read)
    }
}

///
/// Encodes a [`VarInt`] to an output slice. Unlike [`var_int_write_slice`], this
/// cannot panic because the length is statically proven to be at least [`MAX_VAR_INT_BYTES`].
///
/// The number of bytes written is _guaranteed_ to equal `var_int_len(input)` for all possible
/// values of `input`.
#[inline]
pub fn var_int_write_array(input: i32, output: &mut [u8; MAX_VAR_INT_BYTES]) -> usize {
    #[allow(
        clippy::cast_sign_loss,
        reason = "We only care about the raw bits, not the sign"
    )]
    let input = u64::from(input as u32);

    let len = var_int_len_bits(input);

    let num = var_int_write(input, len);
    let len = ((len >> 3) + 1) as usize;

    let array: [u8; size_of::<u64>()] = num.to_le_bytes();

    // SAFETY:
    // - `len` is guaranteed to be in range [1, MAX_VAR_INT_BYTES]
    // - `output` is exactly MAX_VAR_INT_BYTES
    // - `array` is always 8 bytes long
    unsafe {
        output
            .get_unchecked_mut(..len)
            .copy_from_slice(array.get_unchecked(..len));
    }

    len
}

///
/// Writes a `VarInt` directly to a [`u64`]. Only useful internally. Will use appropriate intrinsics
/// when enabled for the target.
#[inline(always)]
#[allow(
    clippy::inline_always,
    reason = "This function is only used internally; inlining it is critical for performance"
)]
fn var_int_write(input: u64, len: u32) -> u64 {
    let mut num = if BMI2_INTRINSICS {
        #[cfg(target_arch = "x86_64")]
        // SAFETY:
        // - we only use this intrinsic if `bmi2` is available, and we are on x86_64
        unsafe {
            core::arch::x86_64::_pdep_u64(input, ALL_NUM_BITS)
        }

        #[cfg(not(target_arch = "x86_64"))]
        // SAFETY:
        // - on non-x86_64 targets, this cannot be reached because `BMI_INTRINSICS` will be false
        unsafe {
            core::hint::unreachable_unchecked()
        }
    } else {
        #[allow(clippy::identity_op, reason = "Code clarity")]
        #[allow(clippy::erasing_op, reason = "Code clarity")]
        {
            // build up the VarInt in a single u64
            let mut num = 0_u64;

            // could be represented more elegantly with a loop, but that's much slower than this
            // "unrolled" branch-free version
            num |= (input & (LOW_NUM_BITS << (0 * 7))) << 0;
            num |= (input & (LOW_NUM_BITS << (1 * 7))) << 1;
            num |= (input & (LOW_NUM_BITS << (2 * 7))) << 2;
            num |= (input & (LOW_NUM_BITS << (3 * 7))) << 3;
            num |= (input & (LOW_NUM_BITS << (4 * 7))) << 4;
            num
        }
    };

    #[cfg(not(all(target_arch = "x86_64", target_feature = "bmi2")))]
    // place all of our continue bits by ORing with a masked ALL_CONT_BITS
    {
        num |= ALL_CONT_BITS & ((1 << u64::from(len)) - 1);
    }

    #[cfg(all(target_arch = "x86_64", target_feature = "bmi2"))]
    {
        num |= unsafe { core::arch::x86_64::_bzhi_u64(ALL_CONT_BITS, len) }
    }

    num
}

///
/// A (maybe partial) read of a [`VarInt`]. Returned by [`var_int_partial_read`], and anywhere else
/// that needs to read a `VarInt` from potentially-incomplete data, such as packet prefixes.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[must_use]
pub enum PartialRead {
    ///
    /// The [`VarInt`] is incomplete, more bytes are expected.
    NeedsBytes,

    ///
    /// The [`VarInt`] was fully read.
    ///
    /// The first value is the number of bytes that were read, guaranteed to be in range
    /// `[1, MAX_VAR_INT_BYTES]`. The second value is the actual [`VarInt`].
    Done(usize, VarInt),
}

///
/// Works similarly to [`var_int_read`], but can only be used on input slices of length less than
/// [`MAX_VAR_INT_BYTES`]. Since the slice may represent *part of* a valid `VarInt`, returns a
/// [`PartialRead`] indicating if the value was able to compute, or if more bytes are necessary.
///
/// Because the input is always less than `MAX_VAR_INT_BYTES`, this function cannot tell if the
/// `VarInt` is going to be invalid; hence it does not return a Result.
///
/// # Panics
/// This function panics if the input length is greater than or equal to `MAX_VAR_INT_BYTES`.
#[inline]
pub fn var_int_partial_read(input: &[u8]) -> PartialRead {
    assert!(
        input.len() < MAX_VAR_INT_BYTES,
        "input length must be less than MAX_VAR_INT_BYTES"
    );

    let mut buf = [0_u8; size_of::<u64>()];
    buf[..input.len()].copy_from_slice(input);

    let num = u64::from_le_bytes(buf);

    // we invert num so we can use `trailing_zeros` to get the number of bits we care about
    let inverted_cont_bits = !num & ALL_CONT_BITS;

    // number of bits we care about, there may be garbage data in `num`
    let significant_bits = inverted_cont_bits.trailing_zeros() + 1;

    // precompute the length of the VarInt in bytes
    let len = (significant_bits >> 3) as usize;

    if len > input.len() {
        PartialRead::NeedsBytes
    } else {
        // selects only our needed bits from `num`
        let num = select_sig_bits(significant_bits, num);

        // actually compute the VarInt
        let val = compute_var_int(num);

        PartialRead::Done(len, VarInt::from(val))
    }
}

#[cfg(test)]
mod tests {
    use crate::types::{VarInt, MAX_VAR_INT_BYTES};
    use crate::util::{var_int_len, var_int_partial_read, var_int_read, PartialRead};
    use crate::ProtocolWrite;

    #[test]
    fn all_len_in_range() {
        for i in i32::MIN..=i32::MAX {
            let res = var_int_len(i);
            assert!((1..=MAX_VAR_INT_BYTES).contains(&res));
        }
    }

    #[test]
    fn full_read_zero() {
        let (len, result) = var_int_read(&[0, 0, 0, 0, 0]).unwrap();

        assert_eq!(result, VarInt::from(0));
        assert_eq!(len, result.len());
    }

    #[test]
    fn partial_read_zero() {
        let t = var_int_partial_read(&[0]);
        assert_eq!(t, PartialRead::Done(1, VarInt::from(0)));
    }

    #[test]
    fn full_read_one() {
        let bytes = [1, 0, 0, 0, 0];
        let (len, result) = var_int_read(&bytes).unwrap();

        assert_eq!(result, VarInt::from(1));
        assert_eq!(len, result.len());
    }

    #[test]
    fn partial_read_one() {
        let t = var_int_partial_read(&[1]);

        assert_eq!(t, PartialRead::Done(1, VarInt::from(1)));
    }

    #[test]
    fn full_read_min() {
        let bytes = [0x80, 0x80, 0x80, 0x80, 0x08];
        let (len, result) = var_int_read(&bytes).unwrap();

        assert_eq!(result, VarInt::from(i32::MIN));
        assert_eq!(len, result.len());
    }

    #[test]
    fn full_read_invalid() {
        let mut bytes = [0x80, 0x80, 0x80, 0x80, 0x80];
        let res = var_int_read(&mut bytes);

        assert!(res.is_err());
    }

    #[test]
    fn len_128() {
        assert_eq!(var_int_len(128), 2);
    }

    #[test]
    fn len_1() {
        assert_eq!(var_int_len(1), 1);
    }

    #[test]
    fn len_0() {
        assert_eq!(var_int_len(0), 1);
    }

    #[test]
    fn len_neg1() {
        assert_eq!(var_int_len(-1), 5);
    }

    #[test]
    fn incomplete_partial_all() {
        let mut bytes = [0u8; MAX_VAR_INT_BYTES];

        for i in 0..=i32::MAX {
            if var_int_len(i) == MAX_VAR_INT_BYTES {
                // skip all full-length reads
                continue;
            }

            let written = VarInt::from(i).write_to(&mut &mut bytes[..]);
            if written == 1 {
                continue;
            }

            let result = var_int_partial_read(&bytes[..written - 1]);
            assert_eq!(result, PartialRead::NeedsBytes);
        }
    }

    #[test]
    fn partial_read_16384() {
        let mut bytes = [0u8; MAX_VAR_INT_BYTES];

        let i = 16384;

        let written = VarInt::from(i).write_to(&mut &mut bytes[..]);
        let result = var_int_partial_read(&bytes[..written]);

        assert_eq!(
            result,
            PartialRead::Done(var_int_len(i), VarInt::from(i)),
            "for {}, written {}",
            i,
            written
        );
    }

    #[test]
    fn full_partial_read_round_trip_all() {
        let mut bytes = [0u8; MAX_VAR_INT_BYTES];

        for i in 0..=i32::MAX {
            if var_int_len(i) == MAX_VAR_INT_BYTES {
                // skip all full-length reads
                continue;
            }

            let written = VarInt::from(i).write_to(&mut &mut bytes[..]);
            let result = var_int_partial_read(&bytes[..written]);

            assert_eq!(
                result,
                PartialRead::Done(var_int_len(i), VarInt::from(i)),
                "for {}",
                i
            );
        }
    }

    #[test]
    fn full_read_round_trip_all() {
        let mut bytes = [0u8; MAX_VAR_INT_BYTES];

        for i in i32::MIN..=i32::MAX {
            let written = VarInt::from(i).write_to(&mut &mut bytes[..]);
            let (len, result) = var_int_read(&bytes).unwrap();

            assert_eq!(result, VarInt::from(i));
            assert_eq!(len, result.len());
        }
    }

    #[test]
    fn zero() {
        let mut bytes = [0u8; MAX_VAR_INT_BYTES];

        for i in 0..1 {
            let written = VarInt::from(i).write_to(&mut &mut bytes[..]);
            let (len, result) = var_int_read(&bytes).unwrap();

            assert_eq!(result, VarInt::from(i));
            assert_eq!(len, result.len());
        }
    }
}
