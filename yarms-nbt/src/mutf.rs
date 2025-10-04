use alloc::borrow::Cow;
use alloc::vec::Vec;
use core::str::FromStr;

const NONASCII_MASK: usize = usize::from_ne_bytes([0x80; size_of::<usize>()]);

const fn contains_nonascii(x: usize) -> bool {
    (x & NONASCII_MASK) != 0
}

const IS_TEST: bool = cfg!(test);

///
/// Given an input `str`, produces a byte array of valid MUTF-8 data. This is the inverse of
/// [`from_mutf8`]. Unlike that function, this one is infallible. Any `str` may be
/// converted into MUTF-8.
///
/// Converting a UTF-8 encoded `str` to MUTF-8 requires allocation if the input string contains
/// any null bytes or supplementary characters. Otherwise, a borrow to the string is returned
/// instead, and no allocation is performed.
///
/// # Examples
/// ```
/// use std::borrow::Cow;
/// let input = "null\0";
///
/// let mutf8 = yarms_nbt::mutf::into_mutf8(input);
///
/// // null byte will be replaced with the overlong encoding 0xC0 0x80
/// assert_eq!(&mutf8, &[b'n', b'u', b'l', b'l', 0xC0, 0x80].as_slice());
/// ```
///
/// # Panics
/// This function will only panic if there is an internal bug, or an allocation failure.
#[must_use]
pub fn into_mutf8(str: &str) -> Cow<[u8]> {
    let bytes = str.as_bytes();

    let mut idx = 0;
    let mut alloc = Vec::new();

    while idx < bytes.len() {
        let sample = bytes[idx];

        if sample == 0 {
            if alloc.is_empty() {
                alloc.reserve(bytes.len() + 1);
                alloc.extend_from_slice(&bytes[..idx]);
            }

            alloc.push(0xC0);
            alloc.push(0x80);

            idx += 1;
        } else if sample < 128 {
            if !alloc.is_empty() {
                alloc.push(sample);
            }

            idx += 1;
        } else {
            let width = usize::from(UTF8_CHAR_WIDTH[usize::from(sample)]);

            if width == 4 {
                let target_slice = &bytes[idx..idx + width];

                if IS_TEST {
                    let slice = core::str::from_utf8(target_slice);
                    let slice = slice.expect("should have been valid UTF-8");
                    let _ = char::from_str(slice)
                        .expect("decoded string should have been a single character");
                }

                // SAFETY:
                // - `target_slice` should always be valid UTF-8
                // - `target_slice` is exactly 1 codepoint, so converting to a char always succeeds
                let char = unsafe {
                    let substr = core::str::from_utf8_unchecked(target_slice);
                    u32::from(char::from_str(substr).unwrap_unchecked()) - 0x10000
                };

                #[allow(clippy::cast_possible_truncation, reason = "Truncation is deliberate here")]
                let hi = ((char >> 10) | 0xD800) as u16;

                #[allow(clippy::cast_possible_truncation, reason = "Truncation is deliberate here")]
                let lo = ((char & 0x3FF) | 0xDC00) as u16;

                let hi = encode_cesu_surrogate(hi);
                let lo = encode_cesu_surrogate(lo);

                if alloc.is_empty() {
                    alloc.reserve(bytes.len());
                    alloc.extend_from_slice(&bytes[..idx]);
                }

                alloc.extend_from_slice(&hi);
                alloc.extend_from_slice(&lo);
            } else if !alloc.is_empty() {
                alloc.extend_from_slice(&bytes[idx..idx + width]);
            }

            idx += width;
        }
    }

    if alloc.is_empty() {
        Cow::Borrowed(bytes)
    } else {
        Cow::Owned(alloc)
    }
}

///
/// Converts Java's "modified UTF-8", also known as MUTF-8, to a regular UTF-8 `str`. This is the
/// inverse of [`into_mutf8`].
///
/// This function will attempt to avoid allocation whenever possible. It will not allocate unless a
/// conversion from MUTF-8 to UTF-8 would change the length of the slice. If an allocation occurs,
/// the resulting `Cow` will be the owned variant. Otherwise, it will be the borrowed variant, with
/// a lifetime tied to `bytes`.
///
/// This function is optimized under the assumption that most bytes are ASCII, or at least do not
/// require any modification to convert from MUTF-8 to UTF-8.
///
/// It will return `None` if the input is invalid MUTF-8. MUTF-8, unlike UTF-8, does not support the
/// null byte `0x0`. Null bytes must be encoded as `0xC0 0x80`. Supplementary characters must use a
/// special 6-byte encoding as defined [here](https://www.unicode.org/reports/tr26/tr26-4.html). It
/// does not support 4-byte supplementary character sequences.
///
/// # Examples
/// ```
/// let utf_string = "\u{004D}\u{0061}\u{F0000}";
///
/// // from the example in https://www.unicode.org/reports/tr26/tr26-4.html
/// // this is the above string, encoded in MUTF-8
/// let mutf_bytes = [0x4D, 0x61, 0xED, 0xAE, 0x80, 0xED, 0xB0, 0x80];
///
/// let result = yarms_nbt::mutf::from_mutf8(&mutf_bytes).expect("should have been valid MUTF-8");
/// assert_eq!(&result, &utf_string);
/// ```
///
/// # Panics
/// This function will only panic if there is an internal bug or allocation failure.
#[must_use]
pub fn from_mutf8(bytes: &[u8]) -> Option<Cow<str>> {
    const USIZE_BYTES: usize = size_of::<usize>();
    const ASCII_BLOCK_SIZE: usize = 2 * USIZE_BYTES;

    if memchr::memchr(0x0, bytes).is_some() {
        // null byte is not valid in MUTF-8
        // by filtering this out early, we can use an optimized routine to quickly skip over valid
        // ASCII later (as 0x0 is the only ASCII that is not allowed in MUTF-8)
        return None;
    }

    let mut decoded = Vec::new();
    let len = bytes.len();

    let align = bytes.as_ptr().align_offset(USIZE_BYTES);
    let blocks_end = if len >= ASCII_BLOCK_SIZE {
        len - ASCII_BLOCK_SIZE + 1
    } else {
        0
    };

    let mut pos = 0;
    while pos < len {
        let old_pos = pos;

        macro_rules! next {
            () => {{
                pos += 1;
                if pos >= len {
                    return None;
                }

                bytes[pos]
            }};
        }

        macro_rules! next_continue {
            () => {{
                let next = next!();

                #[allow(clippy::cast_possible_wrap, reason = "Wrapping is acceptable here")]
                if next as i8 >= -64 {
                    return None;
                }

                next
            }};
        }

        let first = bytes[pos];

        // ascii case
        if first < 128 {
            // borrowed from core::str::to_utf8's internal UTF-8 validity check:
            // effectively iterates units of `2 * usize`, looking for non-ASCII chars
            if align != usize::MAX && align.wrapping_sub(pos) % USIZE_BYTES == 0 {
                let ptr = bytes.as_ptr();
                while pos < blocks_end {
                    // SAFETY:
                    // `pos` is aligned as we just checked that it's divisible by USIZE_BYTES
                    // dereferencing `block`, therefore, is safe
                    #[allow(clippy::cast_ptr_alignment, reason = "We check for alignment with usize")]
                    unsafe {
                        let block = ptr.add(pos).cast::<usize>();

                        let zu = contains_nonascii(*block);
                        let zv = contains_nonascii(*block.add(1));

                        if zu || zv {
                            break;
                        }
                    }

                    pos += ASCII_BLOCK_SIZE;
                }

                // advance until we hit the non-ascii byte
                while pos < len && bytes[pos] < 128 {
                    pos += 1;
                }

                if !decoded.is_empty() {
                    decoded.extend_from_slice(&bytes[old_pos..pos]);
                }

                // we already updated our position, continue
                continue;
            } else if !decoded.is_empty() {
                decoded.push(first);
            }
        } else if first == 0xC0 {
            match next!() {
                0x80 => {
                    // initialize our storage, if we haven't already
                    if decoded.is_empty() {
                        decoded.reserve_exact(bytes.len() - 1);
                        decoded.copy_from_slice(&bytes[..pos - 1]);
                    }

                    decoded.push(0);
                }

                _ => return None,
            }
        } else {
            let second = next_continue!();
            match UTF8_CHAR_WIDTH[usize::from(first)] {
                // 2-byte characters are in the BMP
                // this conversion is zero-cost
                2 => {
                    if !decoded.is_empty() {
                        decoded.push(first);
                        decoded.push(second);
                    }
                }

                // 3 bytes, we may need to worry about decoding surrogate pairs
                3 => {
                    let third = next_continue!();

                    match (first, second) {
                        // valid UTF-8 bytes
                        // these are just passed through and incur zero cost
                        (0xE0, 0xA0..=0xBF)
                        | (0xE1..=0xEC | 0xEE..=0xEF, 0x80..=0xBF)
                        | (0xED, 0x80..=0x9F) => {
                            if !decoded.is_empty() {
                                decoded.push(first);
                                decoded.push(second);
                                decoded.push(third);
                            }
                        }

                        // found a high surrogate (codepoints in range U+D800 to U+DBFF)
                        (0xED, 0xA0..=0xAF) => {
                            // we don't care about the first byte of the low surrogate
                            // (fourth byte of our 6-byte supplementary character sequence)
                            // (it should always be the same value, just validate it)
                            if next!() != 0xED {
                                return None;
                            }

                            let fifth = next!();

                            // ensure the 2nd byte of the low surrogate is in a valid range
                            // (this also checks that it's a valid CESU-8 code unit)
                            if !(0xB0..=0xBF).contains(&fifth) {
                                return None;
                            }

                            // third byte of the low surrogate
                            // (sixth byte of the supplementary character sequence)
                            let sixth = next_continue!();

                            // convert the surrogate bytes into their UTF-8 equivalents
                            let utf8 = surrogate_to_utf8(second, third, fifth, sixth);

                            // this operation changes our length...
                            if decoded.is_empty() {
                                decoded.reserve_exact(bytes.len() - 2);
                                decoded.extend_from_slice(&bytes[..old_pos]);
                            }

                            decoded.extend_from_slice(&utf8);
                        }

                        _ => return None,
                    }
                }

                // MUTF-8, as it is derived from CESU-8, doesn't have 4-byte sequences:
                // https://www.unicode.org/reports/tr26/tr26-4.html
                _ => return None,
            }
        }

        pos += 1;
    }

    if IS_TEST {
        let bytes = if decoded.is_empty() { bytes } else { &*decoded };

        // we perform this assert here instead of in a test function for several reasons:
        // - this function returns a `str`, any UTF-8 validation done in such a test function may
        //   happen after technical UB from a bug resulting in invalid UTF-8
        // - a debug_assert would work, but would rather not miss UB due to running tests with
        //   --release
        let _ = core::str::from_utf8(bytes).expect("should have produced valid UTF-8");
    }

    Some(if decoded.is_empty() {
        // SAFETY:
        // we checked that `bytes` is valid UTF-8
        Cow::Borrowed(unsafe { core::str::from_utf8_unchecked(bytes) })
    } else {
        // SAFETY:
        // we only push valid UTF-8 bytes to `decoded`
        Cow::Owned(unsafe { alloc::string::String::from_utf8_unchecked(decoded) })
    })
}

fn surrogate_to_utf8(second: u8, third: u8, fifth: u8, sixth: u8) -> [u8; 4] {
    fn decode_surrogate(second: u8, third: u8) -> u16 {
        0xD0_00 | ((u16::from(second) & 0x3F) << 6) | (u16::from(third) & 0x3F)
    }

    // the actual utf-16 codepoint, as a surrogate pair
    // this will always decode to a 4-byte UTF-8 sequence
    let high = u32::from(decode_surrogate(second, third));
    let low = u32::from(decode_surrogate(fifth, sixth));

    // the plain unicode codepoint
    let codepoint = ((high - 0xD800) << 10) + (low - 0xDC00) + 0x10000;

    let b4 = 0x80 | ((codepoint & 0x3F) as u8);
    let b3 = 0x80 | (((codepoint >> 6) & 0x3F) as u8);
    let b2 = 0x80 | (((codepoint >> 12) & 0x3F) as u8);
    let b1 = 0xF0 | (((codepoint >> 18) & 0x07) as u8);

    [b1, b2, b3, b4]
}

fn encode_cesu_surrogate(v: u16) -> [u8; 3] {
    let b3 = 0x80 | (v & 0x3F) as u8;
    let b2 = 0x80 | ((v >> 6) & 0x3F) as u8;
    let b1 = 0xE0 | ((v >> 12) & 0x0F) as u8;

    [b1, b2, b3]
}

// same table used to validate UTF in the rust core lib
const UTF8_CHAR_WIDTH: &[u8; 256] = &[
    // 1  2  3  4  5  6  7  8  9  A  B  C  D  E  F
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 0
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 1
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 2
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 3
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 4
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 5
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 6
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 7
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 8
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 9
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // A
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // B
    0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // C
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // D
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, // E
    4, 4, 4, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // F
];

#[cfg(test)]
mod tests {
    use crate::mutf::{from_mutf8, into_mutf8, IS_TEST};
    use alloc::borrow::Cow;
    use alloc::vec::Vec;
    use std::io::Read;
    use std::prelude::v1::String;
    use std::vec;

    // tests byte sequences that are the same in UTF-8 and MUTF-8
    fn test_equivalent_utf8<I: IntoIterator<Item = u8>>(bytes: I) {
        let input_bytes = bytes.into_iter().collect::<Vec<_>>();

        let result = from_mutf8(&input_bytes).expect("input should be valid MUTF-8");
        assert_eq!(
            result,
            core::str::from_utf8(&input_bytes).expect("output should be valid UTF-8")
        );
    }

    fn roundtrip_utf8<I: IntoIterator<Item = u8>>(bytes: I) {
        let input_bytes = bytes.into_iter().collect::<Vec<_>>();
        let str =
            core::str::from_utf8(&input_bytes[..]).expect("input bytes should be valid UTF-8");

        let mutf8 = into_mutf8(str);
        let new_utf8 = from_mutf8(&mutf8).expect("input bytes should be valid MUTF-8");

        assert_eq!(str, new_utf8);
    }

    #[test]
    fn is_test() {
        assert!(IS_TEST)
    }

    #[test]
    fn null_byte_is_none() {
        assert!(from_mutf8(&[42, 42, 42, 0]).is_none())
    }

    #[test]
    fn encoded_null_byte() {
        let mutf8 = [0xC0, 0x80];
        let out = from_mutf8(&mutf8).expect("input should be valid MUTF-8");
        assert_eq!(
            out,
            String::from_utf8(vec![0]).expect("input should be valid UTF-8")
        );
    }

    #[test]
    fn basic_ascii() {
        test_equivalent_utf8(1_u8..128)
    }

    #[test]
    fn bmp_unicode() {
        test_equivalent_utf8("€€€€€".bytes())
    }

    #[test]
    fn bmp_unicode_between_ascii() {
        test_equivalent_utf8((1_u8..128).chain("€€€€€".bytes()).chain(1_u8..128))
    }

    #[test]
    fn supplementary_unicode() {
        let utf_string = "\u{004D}\u{0061}\u{F0000}";

        // from the example in https://www.unicode.org/reports/tr26/tr26-4.html
        let cesu_bytes = [0x4D, 0x61, 0xED, 0xAE, 0x80, 0xED, 0xB0, 0x80];

        let result = from_mutf8(&cesu_bytes).expect("should have been valid MUTF-8");
        assert!(matches!(result, Cow::Owned(_)));
        assert_eq!(result, utf_string);
    }

    #[test]
    fn roundtrip_simple() {
        roundtrip_utf8(b"this is a test".iter().cloned());
    }

    #[test]
    fn roundtrip_test_file() {
        let test = include_str!("utf8_test_file");
        roundtrip_utf8(test.as_bytes().iter().cloned());
    }
}
