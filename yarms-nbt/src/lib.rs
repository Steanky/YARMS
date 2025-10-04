//!
//! Support for NBT (named binary tag) format as used by Minecraft. `no-std` compatible.

#![no_std]

///
/// A very simple array-based stack.
mod array_stack;

///
/// Convert to and from Java's "modified UTF-8" (MUTF-8) format and normal, sane UTF-8 strings.
pub mod mutf;

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

use alloc::borrow::Cow;
use alloc::format;
use alloc::vec::Vec;
use core::fmt;
use core::fmt::{Debug, Display, Formatter};
use hashbrown::hash_map::Entry;
use hashbrown::HashMap;

#[doc(hidden)]
pub use hashbrown as __hash_map;

///
/// The name of an NBT tag. Type alias for `Option<Cow<'a, str>>`.
pub type Name<'a> = Option<Cow<'a, str>>;

///
/// Type identifier for [`Tag::End`].
pub const TAG_END: u8 = 0;

///
/// Type identifier for [`Tag::Byte`].
pub const TAG_BYTE: u8 = 1;

///
/// Type identifier for [`Tag::Short`].
pub const TAG_SHORT: u8 = 2;

///
/// Type identifier for [`Tag::Int`].
pub const TAG_INT: u8 = 3;

///
/// Type identifier for [`Tag::Long`].
pub const TAG_LONG: u8 = 4;

///
/// Type identifier for [`Tag::Float`].
pub const TAG_FLOAT: u8 = 5;

///
/// Type identifier for [`Tag::Double`].
pub const TAG_DOUBLE: u8 = 6;

///
/// Type identifier for [`Tag::ByteArray`].
pub const TAG_BYTE_ARRAY: u8 = 7;

///
/// Type identifier for [`Tag::String`].
pub const TAG_STRING: u8 = 8;

///
/// Type identifier for [`Tag::List`].
pub const TAG_LIST: u8 = 9;

///
/// Type identifier for [`Tag::Compound`].
pub const TAG_COMPOUND: u8 = 10;

///
/// Type identifier for [`Tag::IntArray`].
pub const TAG_INT_ARRAY: u8 = 11;

///
/// Type identifier for [`Tag::LongArray`].
pub const TAG_LONG_ARRAY: u8 = 12;

///
/// Current "recursion" limit for NBT deserialization.
pub const DEPTH_LIMIT: usize = 64;

#[doc(hidden)]
#[macro_export]
macro_rules! __keys_internal {
    () => {};

    ( {$v:expr} ) => {
        $crate::TagKey::Name($v)
    };

    ( $v:expr ) => {
        $crate::TagKey::Index($v)
    };

    ( $( $tail:tt ),+ ) => {
        $( tag_keys_internal!( $tail ) ),+
    };
}

///
/// Generates an array of [`TagKey`]s.
///
/// The syntax supports a more compact delineation of name and index keys:
/// ```
/// use yarms_nbt::{keys, TagKey};
///
/// // statements enclosed in curly braces are considered strings
/// let generated = keys!(42, {"test"});
/// let equivalent = [TagKey::Index(42), TagKey::Name("test")];
///
/// assert_eq!(generated, equivalent);
///
/// fn str_ret_fn() -> &'static str {
///   "static string"
/// }
///
/// // expressions are allowed, not just literals
/// let generated = keys!(10, {str_ret_fn()}, 20);
/// let equivalent = [TagKey::Index(10), TagKey::Name(str_ret_fn()), TagKey::Index(20)];
///
/// assert_eq!(generated, equivalent);
/// ```
#[macro_export]
macro_rules! keys {
    () => { [$crate::TagKey::Index(0); 0] };

    ( $( $tail:tt ),+ ) => {[
        $( $crate::__keys_internal!($tail) ),+
    ]};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __tag_name {
    () => {
        core::option::Option::None
    };

    ( $e:literal ) => {{
        extern crate alloc;
        core::option::Option::Some(alloc::borrow::Cow::Borrowed($e))
    }};

    ( $e:expr ) => {{
        extern crate alloc;

        let string = $e.to_string();
        core::option::Option::Some(alloc::borrow::Cow::Owned(string))
    }};

    ( ref $e:expr ) => {{
        extern crate alloc;
        core::option::Option::Some(alloc::borrow::Cow::Borrowed($e))
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __gen_list_array {
    ( $element_type:ident, ) => {{
        [$crate::Tag::End; 0]
    }};

    ( $element_type:ident, $( $sublist_type:ident : $value:tt ),+ ) => {[
        $({
            tag!($sublist_type List : $value)
        }),+
    ]};

    ( $element_type:ident, $( $value:tt ),+ ) => {[
        $({
            tag!($element_type : $value)
        }),+
    ]};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __gen_compound_array {
    () => {{
        extern crate alloc;
        [(alloc::borrow::Cow::Borrowed(""), $crate::Tag::End); 0]
    }};

    ( $( $tag_type:ident $( $list:ident )? [$( $tag_name:tt )+] : $value:tt ),+ ) => {[
        $({
        let tag = tag!($tag_type $( $list )? [$( $tag_name )+] : $value);
        (tag.name().unwrap().clone(), tag)
        }),+
    ]};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __resolve_ty {
    (End) => {
        $crate::TAG_END
    };
    (Byte) => {
        $crate::TAG_BYTE
    };
    (Short) => {
        $crate::TAG_SHORT
    };
    (Int) => {
        $crate::TAG_INT
    };
    (Long) => {
        $crate::TAG_LONG
    };
    (Float) => {
        $crate::TAG_FLOAT
    };
    (Double) => {
        $crate::TAG_DOUBLE
    };
    (ByteArray) => {
        $crate::TAG_BYTE_ARRAY
    };
    (String) => {
        $crate::TAG_STRING
    };
    (List) => {
        $crate::TAG_LIST
    };
    (Compound) => {
        $crate::TAG_COMPOUND
    };
    (IntArray) => {
        $crate::TAG_INT_ARRAY
    };
    (LongArray) => {
        $crate::TAG_LONG_ARRAY
    };
}

///
/// Easy way of constructing predefined [`Tag`] variants in code.
///
/// ```
/// use yarms_nbt::tag;
///
/// let example = tag!(Compound: {
///     Byte["value"]: 42,
///     List List["list of lists"]: [ Byte: [0, 2, 3], Int: [4, 5, 897342] ],
///     Compound List ["list of compounds"]: [
///         {  }, // empty compound
///         {
///             String["test1"]: "a string",
///
///             // empty list
///             String List["test"]: [ "succ", "memes" ]
///         }
///     ]
/// });
///
/// ```
#[macro_export]
macro_rules! tag {
    () => {};

    ( Byte$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        $crate::Tag::Byte($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    }};

    ( Short$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        $crate::Tag::Short($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    }};

    ( Int$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        $crate::Tag::Int($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    }};

    ( Long$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        $crate::Tag::Long($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    }};

    ( Float$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        $crate::Tag::Int($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    }};

    ( Double$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        $crate::Tag::Double($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    }};

    ( ByteArray$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        extern crate alloc;
        let owned: Vec<u8> = $tag_value.into();
        $crate::Tag::ByteArray($crate::__tag_name!($( $( $tag_name )+ )?), alloc::borrow::Cow::Owned(owned))
    }};

    ( ByteArray$( [$( $tag_name:tt )+] )? : ref $tag_value:expr ) => {{
        extern crate alloc;
        $crate::Tag::ByteArray($crate::__tag_name!($( $( $tag_name )+ )?), alloc::borrow::Cow::Borrowed($tag_value))
    }};

    ( String$( [$( $tag_name:tt )+] )? : $tag_value:literal ) => {{
        extern crate alloc;
        $crate::Tag::String($crate::__tag_name!($( $( $tag_name )+ )?), alloc::borrow::Cow::Borrowed($tag_value))
    }};

    ( String$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        extern crate alloc;
        $crate::Tag::String($crate::__tag_name!($( $( $tag_name )+ )?), alloc::borrow::Cow::Owned($tag_value.to_string()))
    }};

    ( String$( [$( $tag_name:tt )+] )? : ref $tag_value:expr ) => {{
        extern crate alloc;
        $crate::Tag::String($crate::__tag_name!($( $( $tag_name )+ )?), alloc::borrow::Cow::Borrowed($tag_value))
    }};

    ( IntArray$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        extern crate alloc;
        let owned: alloc::vec::Vec<i32> = $tag_value.into();
        $crate::Tag::IntArray($crate::__tag_name!($( $( $tag_name )+ )?), owned)
    }};

    ( LongArray$( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {{
        extern crate alloc;
        let owned: alloc::vec::Vec<i64> = $tag_value.into();
        $crate::Tag::LongArray($crate::__tag_name!($( $( $tag_name )+ )?), owned)
    }};

    ( Compound$( [$( $tag_name:tt )+] )? : { $( $tag_value:tt )* } ) => {{
        let map = $crate::__hash_map::HashMap::from($crate::__gen_compound_array!($( $tag_value )*));
        $crate::Tag::Compound($crate::__tag_name!($( $( $tag_name )+ )?), map)
    }};

    ( $element_type:ident List $( [$( $tag_name:tt )+] )? : [ $( $list_body:tt )* ] ) => {{
        extern crate alloc;

        let list = alloc::vec::Vec::from($crate::__gen_list_array!($element_type, $( $list_body )*));
        $crate::Tag::List($crate::__tag_name!($( $( $tag_name )+ )?), $crate::__resolve_ty!($element_type), list)
    }};
}

///
/// Enum representing all valid NBT tag types and their payload, if any.
///
/// Tags have an associated lifetime, which allows variants that need it to borrow directly from an
/// underlying byte slice. This can significantly cut down on allocations, though the tag will be
/// bound to the lifetime of the storage. Tags can be cloned if a longer lifetime is needed.
///
/// [`Tag::List`] and [`Tag::Compound`] may themselves contain other tags. and thus complex nested
/// data structures may be formed.
///
/// Use [`deserialize_internal`] to construct a tag from network data.
#[derive(Clone, PartialEq)]
pub enum Tag<'a> {
    ///
    /// A special tag that is only used to terminate a `TAG_Compound`, or as the type of an empty
    /// `TAG_List`. It never appears in deserialized data and is only useful during the
    /// deserialization process.
    ///
    /// This tag, unlike all others, cannot have a name under any circumstances.
    End,

    ///
    /// A tag containing a signed 8-bit integer.
    Byte(Name<'a>, i8),

    ///
    /// A tag containing a signed 16-bit integer.
    Short(Name<'a>, i16),

    ///
    /// A tag containing  a signed 32-bit integer.
    Int(Name<'a>, i32),

    ///
    /// A tag containing a signed 64-bit integer.
    Long(Name<'a>, i64),

    ///
    /// A tag containing a 32-bit floating point number.
    Float(Name<'a>, f32),

    ///
    /// A tag containing a 64-bit floating point number.
    Double(Name<'a>, f64),

    ///
    /// A tag containing a raw byte slice. May be allocated separately, or it may point directly at
    /// a segment of the input data.
    ByteArray(Name<'a>, Cow<'a, [u8]>),

    ///
    /// A tag containing a string. May be allocated separately, or it may point directly at a
    /// segment of the input data.
    String(Name<'a>, Cow<'a, str>),

    ///
    /// A tag containing a list of other tags, and a type indicating the homogenous type of its
    /// elements.
    ///
    /// When deserializing, none of the tags directly contained in a list will have names.
    List(Name<'a>, u8, Vec<Tag<'a>>),

    ///
    /// A tag containing a map of other tags, keyed by their names, which must be present.
    ///
    /// Uses [`hashbrown::HashMap`] to avoid a dependency on `std`.
    Compound(Name<'a>, HashMap<Cow<'a, str>, Tag<'a>>),

    ///
    /// A variable-length array of 32-bit signed integers.
    IntArray(Name<'a>, Vec<i32>),

    ///
    /// A variable length array of 64-bit signed integers.
    LongArray(Name<'a>, Vec<i64>),
}

///
/// A key pointing at a tag in either a [`Tag::List`] or a [`Tag::Compound`].
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TagKey<'a> {
    ///
    /// A key into a [`Tag::List`].
    Index(usize),

    ///
    /// A key into a [`Tag::Compound`].
    Name(&'a str),
}

///
/// Helps with nicer debug formatting for tags.
fn debug_tag(
    f: &mut Formatter<'_>,
    name: &str,
    tag_name: &Name<'_>,
    field: &dyn Debug,
) -> fmt::Result {
    match tag_name {
        None => f.debug_tuple(name).field(field).finish(),
        Some(tag_name) => f
            .debug_tuple(format!("{name}['{tag_name}']").as_ref())
            .field(field)
            .finish(),
    }
}

impl Debug for Tag<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Tag::End => f.debug_tuple("TAG_End").finish(),
            Tag::Byte(name, byte) => debug_tag(f, "TAG_Byte", name, byte),
            Tag::Short(name, short) => debug_tag(f, "TAG_Short", name, short),
            Tag::Int(name, int) => debug_tag(f, "TAG_Int", name, int),
            Tag::Long(name, long) => debug_tag(f, "TAG_Long", name, long),
            Tag::Float(name, float) => debug_tag(f, "TAG_Float", name, float),
            Tag::Double(name, double) => debug_tag(f, "TAG_Double", name, double),
            Tag::ByteArray(name, byte_array) => debug_tag(f, "TAG_Byte_Array", name, byte_array),
            Tag::String(name, string) => debug_tag(f, "TAG_String", name, string),
            Tag::List(name, _, list) => debug_tag(f, "TAG_List", name, list),
            Tag::Compound(name, compound) => debug_tag(f, "TAG_Compound", name, compound),
            Tag::IntArray(name, int_array) => debug_tag(f, "TAG_Int_Array", name, int_array),
            Tag::LongArray(name, long_array) => debug_tag(f, "TAG_Long_Array", name, long_array),
        }
    }
}

macro_rules! tag_get_impl {
    ( $s:ident, $keys:ident, $func:ident ) => {{
        let mut ctx = $s;

        for key in $keys {
            match ctx {
                Tag::List(_, _, storage) => {
                    if let TagKey::Index(index) = key {
                        ctx = storage.$func(*index)?;
                    } else {
                        return None;
                    }
                }

                Tag::Compound(_, storage) => {
                    if let TagKey::Name(key) = key {
                        ctx = storage.$func(*key)?;
                    } else {
                        return None;
                    }
                }

                _ => return None,
            }
        }

        Some(ctx)
    }};
}

impl<'a> Tag<'a> {
    ///
    /// Fetch a reference to the name of this tag. May not be present if the tag is of type
    /// [`Tag::End`], present in a list, or the root [`Tag::Compound`] itself.
    #[must_use]
    pub fn name(&self) -> Option<&Cow<'a, str>> {
        match self {
            Tag::End => None,
            Tag::Byte(name, _)
            | Tag::Short(name, _)
            | Tag::Int(name, _)
            | Tag::Long(name, _)
            | Tag::Float(name, _)
            | Tag::Double(name, _)
            | Tag::ByteArray(name, _)
            | Tag::String(name, _)
            | Tag::List(name, _, _)
            | Tag::Compound(name, _)
            | Tag::IntArray(name, _)
            | Tag::LongArray(name, _) => name.as_ref(),
        }
    }

    ///
    /// Fetch the identifier associated with the type of this tag.
    #[must_use]
    pub fn id(&self) -> u8 {
        match self {
            Tag::End => TAG_END,
            Tag::Byte(_, _) => TAG_BYTE,
            Tag::Short(_, _) => TAG_SHORT,
            Tag::Int(_, _) => TAG_INT,
            Tag::Long(_, _) => TAG_LONG,
            Tag::Float(_, _) => TAG_FLOAT,
            Tag::Double(_, _) => TAG_DOUBLE,
            Tag::ByteArray(_, _) => TAG_BYTE_ARRAY,
            Tag::String(_, _) => TAG_STRING,
            Tag::List(_, _, _) => TAG_LIST,
            Tag::Compound(_, _) => TAG_COMPOUND,
            Tag::IntArray(_, _) => TAG_INT_ARRAY,
            Tag::LongArray(_, _) => TAG_LONG_ARRAY,
        }
    }

    ///
    /// Adds a tag to this one. If the tag can't be added, it is returned to the caller. Otherwise,
    /// returns `None`.
    ///
    /// If `self` isn't a [`Tag::List`] or [`Tag::Compound`], `tag` can't be added, and this method
    /// will return `Some`. It will also return `Some` when `tag` is named and `self` is a
    /// [`Tag::List`], or when adding an unnamed tag to a [`Tag::Compound`].
    ///
    /// If `replace` is true, and when `self` is a [`Tag::Compound`], the entry with the same name
    /// as `tag` will be replaced, if present. If `replace` is false, such an entry would not be
    /// updated, and this method will return Some to indicate that.
    pub fn add(&mut self, tag: Tag<'a>, replace: bool) -> Option<Tag<'a>> {
        match self {
            Tag::List(_, _, storage) => {
                if tag.name().is_some() {
                    return Some(tag);
                }

                storage.push(tag);
                None
            }

            Tag::Compound(_, storage) => {
                let key = tag.name()?.clone();

                if replace {
                    // old value gets dropped if present
                    let _ = storage.insert(key, tag);
                    None
                } else {
                    match storage.entry(key) {
                        // don't overwrite the existing entry
                        Entry::Occupied(_) => Some(tag),
                        Entry::Vacant(vacant) => {
                            vacant.insert(tag);
                            None
                        }
                    }
                }
            }

            _ => Some(tag),
        }
    }

    ///
    /// Fetches a tag by following a sequence of [`TagKey`]s.
    ///
    /// If `keys` is empty, `self` is returned. Otherwise, each key is followed in turn to traverse
    /// the data.
    #[must_use]
    pub fn get(&self, keys: &[TagKey]) -> Option<&Tag<'a>> {
        tag_get_impl!(self, keys, get)
    }

    ///
    /// Mutable equivalent of [`Tag::get`].
    pub fn get_mut(&mut self, keys: &[TagKey]) -> Option<&mut Tag<'a>> {
        tag_get_impl!(self, keys, get_mut)
    }

    ///
    /// Internal method for adding to container tags `TAG_List` and `TAG_Compound`. Panics if
    /// adding a nameless tag when `self` is a compound, or if `self` isn't a container tag.
    ///
    /// These are conditions that are checked for by the parser, and so shouldn't ever happen
    /// (barring bugs that should be fixed) so this is why we use this instead of the user-facing
    /// method `self.add`.
    pub(crate) fn add_internal(&mut self, tag: Tag<'a>) {
        match self {
            Tag::List(_, _, storage) => storage.push(tag),
            Tag::Compound(_, storage) => {
                let key = tag
                    .name()
                    .expect("tag must have a name when added to a compound")
                    .clone();

                storage.insert(key, tag);
            }

            _ => panic!("should have added to a TAG_List or TAG_Compound"),
        }
    }
}

///
/// Error associated with attempting to deserialize an invalid sequence of NBT bytes.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum NbtDeserializeError {
    ///
    /// The parser encountered the end of the byte sequence when it was expecting more.
    UnexpectedEOF,

    ///
    /// The first type encountered in the data must be a `TAG_Compound`. This error indicates the
    /// parser found a different type, and includes the type it actually found.
    BadRootType(u8),

    ///
    /// The parser found an invalid type identifier.
    UnknownType(u8),

    ///
    /// The parser was expecting a sequence of valid MUTF-8 (Modified UTF-8).
    InvalidMUTF8,

    ///
    /// The parser tried to decode a length prefix, but it couldn't be converted to a `usize`.
    InvalidLengthPrefix(i32),

    ///
    /// The parser exceeded the hardcoded depth limit [`DEPTH_LIMIT`].
    DepthLimitExceeded,

    ///
    /// The parser found a non-empty list of element type `TAG_End`.
    NonEmptyTagEndList,

    ///
    /// The parser expected the end of the data, but more bytes are available.
    ExpectedEOF,
}

impl Display for NbtDeserializeError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            NbtDeserializeError::UnexpectedEOF => f.write_str("unexpected EOF"),
            NbtDeserializeError::BadRootType(ty) => write!(
                f,
                "bad type for root, expected TAG_Compound but got {}",
                *ty
            ),
            NbtDeserializeError::UnknownType(ty) => write!(f, "unknown type identifier {}", *ty),
            NbtDeserializeError::InvalidMUTF8 => f.write_str("invalid MUTF-8 bytes"),
            NbtDeserializeError::InvalidLengthPrefix(p) => {
                write!(f, "invalid length prefix {}", *p)
            }
            NbtDeserializeError::DepthLimitExceeded => f.write_str("exceeded depth limit"),
            NbtDeserializeError::NonEmptyTagEndList => {
                f.write_str("list of element type TAG_End had a non-zero length")
            }
            NbtDeserializeError::ExpectedEOF => f.write_str("expected EOF"),
        }
    }
}

impl core::error::Error for NbtDeserializeError {}

#[cfg(feature = "std")]
impl From<NbtDeserializeError> for std::io::Error {
    fn from(value: NbtDeserializeError) -> Self {
        std::io::Error::new(std::io::ErrorKind::InvalidData, value)
    }
}

///
/// Deserializes "network variant" NBT.
///
/// # Errors
/// If `bytes` contains invalid NBT data, an error will be returned.
pub fn deserialize_network<'tag, 'data: 'tag>(
    bytes: &'data [u8],
) -> Result<Tag<'tag>, NbtDeserializeError> {
    deserialize_internal::<true>(bytes)
}

///
/// Deserializes "file variant" NBT. The root `TAG_Compound` has a name.
///
/// # Errors
/// If `bytes` contains invalid NBT data, an error will be returned.
pub fn deserialize_file<'tag, 'data: 'tag>(
    bytes: &'data [u8],
) -> Result<Tag<'tag>, NbtDeserializeError> {
    deserialize_internal::<false>(bytes)
}

fn deserialize_internal<'tag, 'data: 'tag, const NETWORK_VARIANT: bool>(
    mut bytes: &'data [u8],
) -> Result<Tag<'tag>, NbtDeserializeError> {
    enum ContainerFlow {
        Map,
        List(usize),
        None,
    }

    macro_rules! next_ty {
        () => {{
            if bytes.is_empty() {
                return Err(NbtDeserializeError::UnexpectedEOF);
            }

            // explicit type here helps analyzer determine "return type"
            let __ty: u8 = bytes[0];

            if !(0..=12).contains(&__ty) {
                return Err(NbtDeserializeError::UnknownType(__ty));
            }

            bytes = &bytes[1..];
            __ty
        }};
    }

    macro_rules! next_n {
        ( $size:literal ) => {{
            if bytes.len() < $size {
                return Err(NbtDeserializeError::UnexpectedEOF);
            }

            let __slice: &[u8; $size] = bytes[..$size].try_into().unwrap();
            bytes = &bytes[$size..];
            __slice
        }};

        ( $size:expr ) => {{
            let __size: usize = $size;

            if bytes.len() < __size {
                return Err(NbtDeserializeError::UnexpectedEOF);
            }

            let __slice: &[u8] = &bytes[..__size];
            bytes = &bytes[__size..];
            __slice
        }};
    }

    macro_rules! length_prefix {
        () => {{
            let __len = i32::from_be_bytes(*next_n!(4));
            let __len = usize::try_from(__len)
                .map_err(|_| NbtDeserializeError::InvalidLengthPrefix(__len))?;
            __len
        }};
    }

    macro_rules! array_storage {
        ($t:ty) => {{
            const __BYTES: u32 = <$t>::BITS >> 3;
            const __SHIFT: u32 = __BYTES.trailing_zeros();

            let __len = length_prefix!();

            #[allow(clippy::cast_possible_wrap, reason = "We cast back to i32 to get the original value")]
            #[allow(clippy::cast_possible_truncation, reason = "We never actually overflow an i32")]
            let __len_bytes = __len
                .checked_shl(__SHIFT)
                .ok_or(NbtDeserializeError::InvalidLengthPrefix(__len as i32))?;
            let __contents = next_n!(__len_bytes);

            let mut __storage = Vec::with_capacity(__len);
            for __i in 0..__len {
                let __pos = __i << __SHIFT;
                __storage.push(<$t>::from_be_bytes(
                    __contents[__pos..__pos + (__BYTES as usize)]
                        .try_into()
                        .unwrap(),
                ));
            }

            __storage
        }};
    }

    macro_rules! expect_empty {
        () => {{
            if !bytes.is_empty() {
                return Err(NbtDeserializeError::ExpectedEOF);
            }
        }};
    }

    let root = {
        let ty = next_ty!();
        if ty != TAG_COMPOUND {
            return Err(NbtDeserializeError::BadRootType(ty));
        }

        let name = if NETWORK_VARIANT {
            // network variant NBT omits the name from the root TAG_Compound
            None
        } else {
            let name_len = u16::from_be_bytes(*next_n!(2));
            Some(
                mutf::from_mutf8(next_n!(name_len as usize))
                    .ok_or(NbtDeserializeError::InvalidMUTF8)?,
            )
        };

        Tag::Compound(name, HashMap::default())
    };

    let mut ctx_stack = array_stack::ArrayStack::<_, DEPTH_LIMIT>::new();
    ctx_stack.push((None, root));

    loop {
        let (target_len, ref mut ctx) = ctx_stack.peek_mut().unwrap();

        // will be None unless ctx is TAG_List
        let target_len = *target_len;

        let (ty, name, old_len) = match &ctx {
            Tag::List(_, ty, storage) => (*ty, None, storage.len()),
            Tag::Compound(_, storage) => {
                let ty = next_ty!();

                if ty == TAG_END {
                    // TAG_End doesn't have a name even in a compound
                    (ty, None, storage.len())
                } else {
                    let name_len = u16::from_be_bytes(*next_n!(2));
                    let name = Some(
                        mutf::from_mutf8(next_n!(name_len as usize))
                            .ok_or(NbtDeserializeError::InvalidMUTF8)?,
                    );

                    (ty, name, storage.len())
                }
            }

            // context won't be any other tag types
            _ => panic!("context type should have been TAG_List or TAG_Compound"),
        };

        // our context TAG_List got filled up by a previous call to add_internal
        // we know we're a TAG_List because if not, target_len would be None
        if Some(old_len) == target_len {
            let (_, full_list) = ctx_stack.pop().unwrap();

            // since we're a TAG_List, we know we have a "parent": only TAG_Compound may be the
            // root element!
            ctx_stack
                .peek_mut()
                .expect("should have at least one tag in the context stack")
                .1
                .add_internal(full_list);

            continue;
        }

        let mut flow = ContainerFlow::None;
        let tag = match ty {
            TAG_END => Tag::End,
            TAG_BYTE => Tag::Byte(name, i8::from_be_bytes(*next_n!(1))),
            TAG_SHORT => Tag::Short(name, i16::from_be_bytes(*next_n!(2))),
            TAG_INT => Tag::Int(name, i32::from_be_bytes(*next_n!(4))),
            TAG_LONG => Tag::Long(name, i64::from_be_bytes(*next_n!(8))),
            TAG_FLOAT => Tag::Float(name, f32::from_be_bytes(*next_n!(4))),
            TAG_DOUBLE => Tag::Double(name, f64::from_be_bytes(*next_n!(8))),
            TAG_BYTE_ARRAY => Tag::ByteArray(name, Cow::Borrowed(next_n!(length_prefix!()))),
            TAG_STRING => Tag::String(
                name,
                mutf::from_mutf8(next_n!(u16::from_be_bytes(*next_n!(2)) as usize))
                    .ok_or(NbtDeserializeError::InvalidMUTF8)?,
            ),
            TAG_LIST => {
                let list_ty = next_ty!();
                let len = length_prefix!();

                flow = ContainerFlow::List(len);

                if list_ty == TAG_END && len > 0 {
                    return Err(NbtDeserializeError::NonEmptyTagEndList);
                }

                Tag::List(name, list_ty, Vec::with_capacity(len))
            }
            TAG_COMPOUND => {
                flow = ContainerFlow::Map;
                Tag::Compound(name, HashMap::default())
            }
            TAG_INT_ARRAY => Tag::IntArray(name, array_storage!(i32)),
            TAG_LONG_ARRAY => Tag::LongArray(name, array_storage!(i64)),

            _ => panic!("tag type returned by next_ty! should have been in range 0..=12"),
        };

        let list_len = match flow {
            // tags that can't contain other tags are never added to the stack
            // empty lists also aren't added
            ContainerFlow::None | ContainerFlow::List(0) => {
                // TAG_End is used to indicate the end of a compound
                // it's never added directly
                if ty != TAG_END {
                    ctx.add_internal(tag);
                }

                // we just added the last element
                // if we're in a compound: we found a TAG_End
                // if we're in a list: we just processed the last element
                if ty == TAG_END || Some(old_len + 1) == target_len {
                    // finished is the same tag as ctx, but owned now
                    let (_, mut finished) = ctx_stack.pop().unwrap();

                    if let Tag::Compound(_, storage) = &mut finished {
                        // maps aren't precisely pre-sized because we don't have a length prefix
                        // so we shrink them after they've been filled in
                        storage.shrink_to_fit();
                    }

                    if let Some((_, peek)) = ctx_stack.peek_mut() {
                        // if peek is a list, doing this might fill it up
                        // a full list needs to be popped, but we don't check for that here!
                        // we will check for a full list in the next iteration of the loop
                        peek.add_internal(finished);
                    } else {
                        expect_empty!();
                        return Ok(finished);
                    }
                }

                continue;
            }

            // non-empty lists must go on the context stack
            ContainerFlow::List(list_len) => Some(list_len),

            // all maps must go on the context stack as we can't know their length
            // ahead of time, unlike with lists
            ContainerFlow::Map => None,
        };

        // we must process the elements of the sub-list or sub-compound now
        if !ctx_stack.push((list_len, tag)) {
            // if we ran out of room on our stack, report an error
            return Err(NbtDeserializeError::DepthLimitExceeded);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{deserialize_internal, Tag};
    use alloc::borrow::Cow;
    use alloc::vec::Vec;
    use std::io::Read;

    // adapted from https://minecraft.wiki/w/Minecraft_Wiki:Projects/wiki.vg_merge/NBT#Specification
    #[test]
    fn hello_world() {
        let data = [
            0x0Au8, // type ID (TAG_Compound)
            0x08, 0x00, 0x04, // type ID of String, plus length of name
            0x6E, 0x61, 0x6D, 0x65, // Name ('name')
            0x00, 0x09, // length of tag 'name'
            0x42, 0x61, 0x6e, 0x61, 0x6e, 0x72, 0x61, 0x6d, 0x61, // payload 'Bananrama'
            0x00, // TAG_End
        ];

        let expected = Tag::Compound(
            None,
            [(
                Cow::Borrowed("name"),
                Tag::String(Some(Cow::Borrowed("name")), Cow::Borrowed("Bananrama")),
            )]
            .into_iter()
            .collect(),
        );

        let tag = deserialize_internal::<true>(&data).expect("tag should have been valid");

        assert_eq!(expected, tag);
    }

    #[test]
    fn bigtest() {
        let bytes = include_bytes!("bigtest.nbt");

        let mut decompressed = Vec::new();
        let mut decoder = flate2::read::GzDecoder::new(&bytes[..]);

        decoder
            .read_to_end(&mut decompressed)
            .expect("expected valid GZIP data");

        let tag = deserialize_internal::<false>(&decompressed).expect("tag should have been valid");
    }

    #[test]
    fn test() {
        let tag = Tag::Compound(
            Some(Cow::Borrowed("test")),
            hashbrown::HashMap::from([(Cow::Borrowed("test"), Tag::End)]),
        );
    }
}
