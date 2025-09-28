use crate::NbtError;

pub(crate) fn parse_name(bytes: &[u8]) -> Result<alloc::borrow::Cow<str>, NbtError> {
    const SIZE: usize = size_of::<u16>();
    if bytes.len() < SIZE {
        return Err(NbtError::UnexpectedEOF);
    }

    let result = usize::from(u16::from_be_bytes((&bytes[..SIZE]).try_into().unwrap()));
    if bytes.len() - SIZE < result {
        return Err(NbtError::UnexpectedEOF);
    }

    crate::mutf::from_modified_utf8(&bytes[SIZE..SIZE + result])
        .ok_or_else(|| NbtError::InvalidMUTF8)
}

macro_rules! parse_num_impl {
    ($base:ty, $fn_name:ident) => {
        pub(crate) fn $fn_name(bytes: &mut &[u8]) -> Result<$base, $crate::NbtError> {
            const __SIZE: usize = size_of::<$base>();

            if bytes.len() < __SIZE {
                return Err($crate::NbtError::UnexpectedEOF);
            }

            let result = <$base>::from_be_bytes((&bytes[..__SIZE]).try_into().unwrap());
            *bytes = &bytes[__SIZE..];

            Ok(result)
        }
    };
}

parse_num_impl!(i8, parse_i8);
parse_num_impl!(i16, parse_i16);
parse_num_impl!(i32, parse_i32);
parse_num_impl!(i64, parse_i64);
