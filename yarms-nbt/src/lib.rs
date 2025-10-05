//!
//! Support for NBT (named binary tag) format as used by Minecraft. `no-std` compatible.
//!
//! # Features
//! * `std` (default): Currently only enables [`NbtDeserializeError`] -> `std::io::Error`
//!   conversion.

#![no_std]

///
/// A very simple array-based stack.
mod array_stack;

///
/// Convert to and from Java's "modified UTF-8" (MUTF-8) format and normal, sane UTF-8 strings.
pub mod mutf;

///
/// Declarative macros for improving the API ergonomics.
pub mod macros;

pub extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

use alloc::borrow::Cow;
use alloc::format;
use alloc::vec::Vec;
use core::fmt;
use core::fmt::{Debug, Display, Formatter};
use hashbrown::hash_map::Entry;

///
/// Public for access from macros, but hidden because it's not supposed to be part of the public
/// API.
#[doc(hidden)]
pub use hashbrown as __hash_map;

///
/// The name of an NBT tag. Type alias for `Option<Cow<'a, str>>`.
pub type Name<'a> = Option<Cow<'a, str>>;

///
/// Type identifier for `TAG_End`.
pub const TAG_END: u8 = 0;

///
/// Type identifier for `TAG_Byte`.
pub const TAG_BYTE: u8 = 1;

///
/// Type identifier for `TAG_Short`.
pub const TAG_SHORT: u8 = 2;

///
/// Type identifier for `TAG_Int`.
pub const TAG_INT: u8 = 3;

///
/// Type identifier for `TAG_Long`.
pub const TAG_LONG: u8 = 4;

///
/// Type identifier for `TAG_Float`.
pub const TAG_FLOAT: u8 = 5;

///
/// Type identifier for `TAG_Double`.
pub const TAG_DOUBLE: u8 = 6;

///
/// Type identifier for `TAG_Byte_Array`.
pub const TAG_BYTE_ARRAY: u8 = 7;

///
/// Type identifier for `TAG_String`.
pub const TAG_STRING: u8 = 8;

///
/// Type identifier for `TAG_List`.
pub const TAG_LIST: u8 = 9;

///
/// Type identifier for `TAG_Compound`.
pub const TAG_COMPOUND: u8 = 10;

///
/// Type identifier for `TAG_Int_Array`.
pub const TAG_INT_ARRAY: u8 = 11;

///
/// Type identifier for `TAG_Long_Array`.
pub const TAG_LONG_ARRAY: u8 = 12;

///
/// Current "recursion" limit for NBT deserialization.
pub const DEPTH_LIMIT: usize = 64;

#[doc(hidden)]
#[inline]
#[must_use]
pub fn __pair(tag: TagRepr) -> (Cow<str>, TagRepr) {
    (tag.name().unwrap().clone(), tag)
}

#[doc(hidden)]
#[inline]
#[allow(
    private_interfaces,
    reason = "This is public for macro access, and hidden as it's not meant to be used."
)]
#[must_use]
pub fn __wrap(repr: TagRepr) -> Tag {
    Tag { repr }
}

///
/// Representation of a single, arbitrary named binary tag. Instances can be created either through
/// deserialization from a byte slice [`deserialize_network`]/[`deserialize_file`], or directly in
/// code using the [`tag`] macro.
///
/// Tags have an associated lifetime, which allows variants that need it to borrow directly from an
/// underlying byte slice. This can significantly cut down on allocations, though the tag will be
/// bound to the lifetime of the storage. Tags can be cloned if a longer lifetime is needed.
///
/// Use [`deserialize_network`] to construct a tag from network data, or [`deserialize_file`] to
/// construct using the file variant.
///
/// Tags provide a family of so-called `as_*` methods that permit access to their underlying
/// payload. These all yield an [`Option`], which will be empty if the type does not match. For
/// example:
/// ```
/// use yarms_nbt::tag;
///
/// // Create a TAG_Byte named "test".
/// let tag = tag!(Byte["test"]: 42);
///
/// // Access its payload.
/// assert_eq!(Some(42), tag.as_byte());
///
/// // The tag isn't a string, so `as_string` yields None.
/// assert_eq!(None, tag.as_string());
/// ```
///
/// Some tags can contain other tags. These are considered "container" tags. One can determine if a
/// tag is a container tag like so:
/// ```
/// use yarms_nbt::tag;
///
/// // Create an unnamed TAG_List of TAG_Int. List elements must be of homogenous type.
/// let list = tag!(Int List: [0, 2, 3]);
///
/// // Create an unnamed TAG_Compound containing one element, a TAG_String named "hello" with
/// // "hello world" as its payload. Compounds can't contain unnamed elements.
/// let compound = tag!(Compound: { String["hello"]: "hello world" });
///
/// // Lists can contain other tags, so they're a container. Compounds are too.
/// assert!(list.is_container());
/// assert!(compound.is_container());
///
/// // Lists are lists, how novel! But compounds aren't.
/// assert!(list.is_list());
/// assert!(!compound.is_list());
///
/// // Lists are not compounds, but compounds are compounds.
/// assert!(!list.is_compound());
/// assert!(compound.is_compound());
/// ```
///
/// One can add tags to containers using the [`Tag::add`] method:
///
/// ```
/// use yarms_nbt::{keys, tag, Tag};
///
/// let mut compound = tag!(Compound: { String["name"]: "John Smith", Byte["age"]: 42 });
///
/// // Adds a new entry to the compound, for height.
/// compound.add(tag!(Short["height"]: 182), false);
///
/// // Oops, a tag named height already existed in the root compound.
/// // `replace` is false so we don't update it.
/// compound.add(tag!(Short["height"]: 200), false);
///
/// assert_eq!(Some(182), compound.get(&keys!({"height"})).and_then(Tag::as_short));
///
/// ```
///
/// Containers can be iterated and modified through various `as_mut_*` methods:
///
/// ```
/// use yarms_nbt::{keys, tag, Tag};
///
/// // A TAG_List of TAG_Int.
/// let mut list = tag!(Int List: [ 0, 1, 2, 3 ]);
///
/// // `replace` doesn't matter when adding to a list.
/// list.add(tag!(Int: 4), false);
///
/// // We can modify the elements if we want.
/// // Note that `elem` is `TagAccess`, not `&mut Tag`!
/// // Users cannot arbitrarily replace existing tags in a container.
/// for mut elem in list.children_mut().expect("should be a container") {
///     if let Some(val) = elem.as_int_mut() {
///         *val += 1;
///     }
/// }
///
/// let expected = tag!(Int List: [ 1, 2, 3, 4, 5 ]);
///
/// assert_eq!(&list, &expected);
///
/// // Trying to add a named tag to a list isn't valid, and so we get our tag back.
/// assert!(list.add(tag!(Int["test"]: 42), false).is_some());
///
/// // Trying to add a TAG_String into a TAG_List of element type TAG_Int also isn't valid.
/// assert!(list.add(tag!(String: "hello"), false).is_some());
///
/// // The list is unchanged.
/// assert_eq!(&list, &expected);
///
/// ```
#[derive(Clone, PartialEq)]
#[repr(transparent)]
pub struct Tag<'a> {
    repr: TagRepr<'a>,
}

///
/// Internal representation of a tag. Should not be accessed by end users.
///
/// This enum may be transmuted to [`Tag`].
#[derive(Clone, PartialEq)]
#[doc(hidden)]
pub enum TagRepr<'a> {
    End,
    Byte(Name<'a>, i8),
    Short(Name<'a>, i16),
    Int(Name<'a>, i32),
    Long(Name<'a>, i64),
    Float(Name<'a>, f32),
    Double(Name<'a>, f64),
    ByteArray(Name<'a>, Cow<'a, [u8]>),
    String(Name<'a>, Cow<'a, str>),
    List(Name<'a>, u8, Vec<TagRepr<'a>>),
    Compound(Name<'a>, hashbrown::HashMap<Cow<'a, str>, TagRepr<'a>>),
    IntArray(Name<'a>, Cow<'a, [i32]>),
    LongArray(Name<'a>, Cow<'a, [i64]>),
}

///
/// A key pointing at a tag in either a `TAG_List` or a `TAG_Compound`.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TagKey<'a> {
    ///
    /// A key into a `TAG_List`.
    Index(usize),

    ///
    /// A key into a `TAG_Compound`.
    Name(&'a str),
}

impl Debug for Tag<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.repr.fmt(f)
    }
}

impl Debug for TagRepr<'_> {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TagRepr::End => f.debug_tuple("TAG_End").finish(),
            TagRepr::Byte(name, byte) => debug_tag(f, "TAG_Byte", name, byte),
            TagRepr::Short(name, short) => debug_tag(f, "TAG_Short", name, short),
            TagRepr::Int(name, int) => debug_tag(f, "TAG_Int", name, int),
            TagRepr::Long(name, long) => debug_tag(f, "TAG_Long", name, long),
            TagRepr::Float(name, float) => debug_tag(f, "TAG_Float", name, float),
            TagRepr::Double(name, double) => debug_tag(f, "TAG_Double", name, double),
            TagRepr::ByteArray(name, byte_array) => {
                debug_tag(f, "TAG_Byte_Array", name, byte_array)
            }
            TagRepr::String(name, string) => debug_tag(f, "TAG_String", name, string),
            TagRepr::List(name, _, list) => debug_tag(f, "TAG_List", name, list),
            TagRepr::Compound(name, compound) => debug_tag(f, "TAG_Compound", name, compound),
            TagRepr::IntArray(name, int_array) => debug_tag(f, "TAG_Int_Array", name, int_array),
            TagRepr::LongArray(name, long_array) => {
                debug_tag(f, "TAG_Long_Array", name, long_array)
            }
        }
    }
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

macro_rules! tag_get_impl {
    ( $s:ident, $keys:ident, $func:ident ) => {{
        let mut ctx = $s;

        for key in $keys {
            match ctx {
                TagRepr::List(_, _, storage) => {
                    if let TagKey::Index(index) = key {
                        ctx = storage.$func(*index)?;
                    } else {
                        return None;
                    }
                }

                TagRepr::Compound(_, storage) => {
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

macro_rules! as_impl {
    ( $s:ident, $ty:ident $( $m:ident )? ) => {{
        match $s.repr {
            $crate::TagRepr::$ty(_, ref $( $m )? val) => Some(val),
            _ => None
        }
    }};
}

impl<'tag> TagRepr<'tag> {
    ///
    /// Macros need to access this function, so it's provided.
    #[doc(hidden)]
    #[must_use]
    pub fn name(&self) -> Option<&Cow<'tag, str>> {
        match self {
            TagRepr::End => None,
            TagRepr::Byte(name, _)
            | TagRepr::Short(name, _)
            | TagRepr::Int(name, _)
            | TagRepr::Long(name, _)
            | TagRepr::Float(name, _)
            | TagRepr::Double(name, _)
            | TagRepr::ByteArray(name, _)
            | TagRepr::String(name, _)
            | TagRepr::List(name, _, _)
            | TagRepr::Compound(name, _)
            | TagRepr::IntArray(name, _)
            | TagRepr::LongArray(name, _) => name.as_ref(),
        }
    }

    fn id(&self) -> u8 {
        match self {
            TagRepr::End => TAG_END,
            TagRepr::Byte(_, _) => TAG_BYTE,
            TagRepr::Short(_, _) => TAG_SHORT,
            TagRepr::Int(_, _) => TAG_INT,
            TagRepr::Long(_, _) => TAG_LONG,
            TagRepr::Float(_, _) => TAG_FLOAT,
            TagRepr::Double(_, _) => TAG_DOUBLE,
            TagRepr::ByteArray(_, _) => TAG_BYTE_ARRAY,
            TagRepr::String(_, _) => TAG_STRING,
            TagRepr::List(_, _, _) => TAG_LIST,
            TagRepr::Compound(_, _) => TAG_COMPOUND,
            TagRepr::IntArray(_, _) => TAG_INT_ARRAY,
            TagRepr::LongArray(_, _) => TAG_LONG_ARRAY,
        }
    }

    fn add(&mut self, tag: TagRepr<'tag>, replace: bool) -> Option<TagRepr<'tag>> {
        match self {
            TagRepr::List(_, ty, storage) => {
                if tag.name().is_some() || *ty != tag.id() {
                    Some(tag)
                } else {
                    storage.push(tag);
                    None
                }
            }

            TagRepr::Compound(_, storage) => {
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

    fn get(&self, keys: &[TagKey]) -> Option<&TagRepr<'tag>> {
        tag_get_impl!(self, keys, get)
    }

    fn get_mut(&mut self, keys: &[TagKey]) -> Option<&mut TagRepr<'tag>> {
        tag_get_impl!(self, keys, get_mut)
    }

    fn add_internal(&mut self, tag: TagRepr<'tag>) {
        match self {
            TagRepr::List(_, _, storage) => storage.push(tag),
            TagRepr::Compound(_, storage) => {
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

enum TagIter<'elem, K, V: 'elem> {
    List(core::slice::Iter<'elem, V>),
    Map(hashbrown::hash_map::Values<'elem, K, V>),
}

enum TagIterMut<'elem, K, V: 'elem> {
    List(core::slice::IterMut<'elem, V>),
    Map(hashbrown::hash_map::ValuesMut<'elem, K, V>),
}

///
/// Used for reference-to-reference conversion of `&TagRepr` to `&Tag`. Not public because `TagRepr`
/// is an implementation detail.
#[inline]
fn repr_to_tag<'item, 'tag>(repr: &'item TagRepr<'tag>) -> &'item Tag<'tag> {
    // SAFETY:
    // - Tag is #[repr(transparent)] and it only contains TagRepr
    // - this operation does not change the lifetimes whatsoever
    unsafe { &*(core::ptr::from_ref::<TagRepr<'tag>>(repr).cast::<Tag<'tag>>()) }
}

impl<'elem, 'tag, K> Iterator for TagIter<'elem, K, TagRepr<'tag>> {
    type Item = &'elem Tag<'tag>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            TagIter::List(list) => list.next(),
            TagIter::Map(values) => values.next(),
        }
        .map(repr_to_tag)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            TagIter::List(list) => list.size_hint(),
            TagIter::Map(values) => values.size_hint(),
        }
    }
}

impl<K> ExactSizeIterator for TagIter<'_, K, TagRepr<'_>> {
    fn len(&self) -> usize {
        match self {
            TagIter::List(inner) => inner.len(),
            TagIter::Map(inner) => inner.len(),
        }
    }
}

impl<'elem, 'tag, K> Iterator for TagIterMut<'elem, K, TagRepr<'tag>> {
    type Item = TagAccess<'elem, 'tag>;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            TagIterMut::List(list) => list.next(),
            TagIterMut::Map(values) => values.next(),
        }
        .map(|repr| TagAccess { repr })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            TagIterMut::List(list) => list.size_hint(),
            TagIterMut::Map(values) => values.size_hint(),
        }
    }
}

impl<K> ExactSizeIterator for TagIterMut<'_, K, TagRepr<'_>> {
    fn len(&self) -> usize {
        match self {
            TagIterMut::List(inner) => inner.len(),
            TagIterMut::Map(inner) => inner.len(),
        }
    }
}

macro_rules! tag_methods {
    () => {
        ///
        /// Gets an optional reference to the name of this tag. This will be `None` if the tag doesn't
        /// have a name.
        ///
        /// It is not possible to change a tag's name.
        #[must_use]
        pub fn name(&self) -> Option<&Cow<'tag, str>> {
            self.repr.name()
        }

        ///
        /// Gets the identifier of this tag.
        #[must_use]
        pub fn id(&self) -> u8 {
            self.repr.id()
        }

        ///
        /// Adds a tag to this one. If the tag can't be added, it is returned to the caller. Otherwise,
        /// returns `None`.
        ///
        /// If `self` isn't a `TAG_List` or `TAG_Compound`, `tag` can't be added, and this method
        /// will return `Some`. It will also return `Some` when `tag` is named and `self` is a
        /// `TAG_List`, or when adding an unnamed tag to a `TAG_Compound`. Finally, when adding to
        /// a list, the type of the tag being added must match the element type of the list.
        ///
        /// If `replace` is true, and when `self` is a `TAG_Compound`, the entry with the same name
        /// as `tag` will be replaced, if present. If `replace` is false, such an entry would not be
        /// updated, and this method will return Some to indicate that.
        pub fn add(&mut self, tag: Tag<'tag>, replace: bool) -> Option<Tag<'tag>> {
            let Tag { repr: tag } = tag;
            self.repr.add(tag, replace).map(|repr| Tag { repr })
        }

        ///
        /// Fetches a tag by following a sequence of [`TagKey`]s.
        ///
        /// If `keys` is empty, `self` is returned. Otherwise, each key is followed in turn to traverse
        /// the data.
        ///
        /// You can use the [`keys`] macro to generate lists more easily.
        #[must_use]
        pub fn get(&self, keys: &[TagKey]) -> Option<&Tag<'tag>> {
            self.repr.get(keys).map(repr_to_tag)
        }

        ///
        /// Mutable equivalent of [`Tag::get`]. Note that this returns [`TagAccess`], which has all
        /// of the same methods, but makes replacing the underlying tag impossible, since
        /// `TagAccess` cannot be freely constructed. This is done to avoid ad hoc violations of
        /// preconditions such as lists not containing named tags or compounds containing unnamed
        /// ones.
        #[must_use]
        pub fn get_mut(&mut self, keys: &[TagKey]) -> Option<TagAccess<'_, 'tag>> {
            self.repr.get_mut(keys).map(|repr| TagAccess { repr })
        }

        ///
        /// Test if this tag is a `TAG_List` or not.
        #[must_use]
        pub fn is_list(&self) -> bool {
            if let TagRepr::List(_, _, _) = &self.repr {
                true
            } else {
                false
            }
        }

        ///
        /// Test if this tag is a `TAG_Compound` or not.
        #[must_use]
        pub fn is_compound(&self) -> bool {
            if let TagRepr::Compound(_, _) = &self.repr {
                true
            } else {
                false
            }
        }

        ///
        /// Test if this tag can contain other tags.
        ///
        /// Equivalent to `tag.is_list() || tag.is_compound()`.
        #[must_use]
        pub fn is_container(&self) -> bool {
            match &self.repr {
                TagRepr::List(_, _, _) | TagRepr::Compound(_, _) => true,

                _ => false,
            }
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_byte(&self) -> Option<i8> {
            as_impl!(self, Byte).map(|n| *n)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_short(&self) -> Option<i16> {
            as_impl!(self, Short).map(|n| *n)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_int(&self) -> Option<i32> {
            as_impl!(self, Int).map(|n| *n)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_long(&self) -> Option<i64> {
            as_impl!(self, Long).map(|n| *n)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_float(&self) -> Option<f32> {
            as_impl!(self, Float).map(|n| *n)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_double(&self) -> Option<f64> {
            as_impl!(self, Double).map(|n| *n)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_byte_array(&self) -> Option<&Cow<'tag, [u8]>> {
            as_impl!(self, ByteArray)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_string(&self) -> Option<&Cow<'tag, str>> {
            as_impl!(self, String)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_int_array(&self) -> Option<&Cow<'tag, [i32]>> {
            as_impl!(self, IntArray)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_long_array(&self) -> Option<&Cow<'tag, [i64]>> {
            as_impl!(self, LongArray)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_byte_mut(&mut self) -> Option<&mut i8> {
            as_impl!(self, Byte mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_short_mut(&mut self) -> Option<&mut i16> {
            as_impl!(self, Short mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_int_mut(&mut self) -> Option<&mut i32> {
            as_impl!(self, Int mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_long_mut(&mut self) -> Option<&mut i64> {
            as_impl!(self, Long mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_float_mut(&mut self) -> Option<&mut f32> {
            as_impl!(self, Float mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_double_mut(&mut self) -> Option<&mut f64> {
            as_impl!(self, Double mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_byte_array_mut(&mut self) -> Option<&Cow<'tag, [u8]>> {
            as_impl!(self, ByteArray mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_string_mut(&mut self) -> Option<&mut Cow<'tag, str>> {
            as_impl!(self, String mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_int_array_mut(&mut self) -> Option<&mut Cow<'tag, [i32]>> {
            as_impl!(self, IntArray mut)
        }

        ///
        /// This is an `as_*` method. See the type level documentation for more details.
        #[inline]
        #[must_use]
        pub fn as_long_array_mut(&mut self) -> Option<&mut Cow<'tag, [i64]>> {
            as_impl!(self, LongArray mut)
        }

        ///
        /// Optionally returns an iterator to the child tags of this one. Will yield `None` if this
        /// tag isn't a list or compound. Will yield `Some` containing an empty iterator if `self`
        /// is an empty list or compound.
        ///
        /// If present, the iterator may iterate either the values of a compound, or the entries of
        /// a list.
        #[must_use]
        pub fn children(&self) -> Option<impl ExactSizeIterator<Item = &Tag<'tag>>> {
            match &self.repr {
                TagRepr::List(_, _, storage) => Some(TagIter::List(storage.iter())),
                TagRepr::Compound(_, storage) => Some(TagIter::Map(storage.values())),
                _ => None,
            }
        }

        ///
        /// Works identically to `children`, but provides mutable access to the tags via
        /// [`TagAccess`].
        #[must_use]
        pub fn children_mut(
            &mut self,
        ) -> Option<impl ExactSizeIterator<Item = TagAccess<'_, 'tag>>> {
            match &mut self.repr {
                TagRepr::List(_, _, storage) => Some(TagIterMut::List(storage.iter_mut())),
                TagRepr::Compound(_, storage) => Some(TagIterMut::Map(storage.values_mut())),
                _ => None,
            }
        }

        ///
        /// Gets the number of elements contained in this tag, if it is a container.
        ///
        /// Note that this does _not_ return `Some` if the tag is a `TAG_Byte_Array`,
        /// `TAG_Int_Array`, `TAG_Long_Array`, or `TAG_String`. It is only meant to fetch the number
        /// of direct child tags contained in a `TAG_List` or `TAG_Compound`.
        #[must_use]
        pub fn len(&self) -> Option<usize> {
            match &self.repr {
                TagRepr::List(_, _, storage) => Some(storage.len()),
                TagRepr::Compound(_, storage) => Some(storage.len()),
                _ => None,
            }
        }

        ///
        /// Tests if this tag is an empty container.
        ///
        /// Returns `None` if this tag isn't a container. Returns `Some(true)` if this tag is an
        /// empty container, and `Some(false)` if it has at least one element.
        #[must_use]
        pub fn is_empty(&self) -> Option<bool> {
            self.len().map(|len| len == 0)
        }

        ///
        /// Updates a list's element type, if it is possible to do so while upholding the following
        /// invariants:
        /// * The new type cannot differ from the types of any elements already in the list
        /// * The new type must be in range `0..=12`
        /// * `self` must actually be a `TAG_List`
        ///
        /// In practice, this means that only an empty list's type may be changed. Note that you
        /// can actually set the element type to [`TAG_END`], though doing so will effectively
        /// prevent any elements from being added, since `TAG_End` is a special case that cannot be
        /// constructed ad hoc.
        ///
        /// Returns true if the list's type was successfully _changed_.
        ///
        /// ```
        /// use yarms_nbt::{tag, TAG_DOUBLE};
        ///
        /// let mut tag = tag!(Int List: [ ]);
        ///
        /// // can't add doubles to an Int list...
        /// assert!(tag.add(tag!(Double: 10.0), false).is_some());
        /// assert!(tag.update_list_type(TAG_DOUBLE), "tag is an empty list so this will work");
        ///
        /// // now we successfully added the tag
        /// assert!(tag.add(tag!(Double: 10.0), false).is_none());
        ///
        /// ```
        pub fn update_list_type(&mut self, new_ty: u8) -> bool {
            if !(0..=12).contains(&new_ty) {
                return false;
            }

            match &mut self.repr {
                TagRepr::List(_, ty, storage) => {
                    if storage.is_empty() && *ty != new_ty {
                        *ty = new_ty;
                        true
                    } else {
                        false
                    }
                }

                _ => false,
            }
        }

        ///
        /// Gets the element type, which will be present if we are a list, absent if not.
        ///
        /// The returned value will be in range `0..=12`.
        #[must_use]
        pub fn get_list_type(&self) -> Option<u8> {
            match &self.repr {
                TagRepr::List(_, ty, _) => Some(*ty),
                _ => None,
            }
        }
    };
}

///
/// Provides mutable access to a tag in a list or compound. This is used instead of just handing out
/// `&mut Tag` because the latter could allow inserting invalid tags for the context (such as a
/// named tag in a list, or an unnamed one in a compound).
///
/// All methods available on [`Tag`] exist on [`TagAccess`], too. See [`Tag`] for complete
/// documentation and examples.
#[derive(Debug, PartialEq)]
#[repr(transparent)]
pub struct TagAccess<'item, 'tag> {
    repr: &'item mut TagRepr<'tag>,
}

impl PartialEq<TagAccess<'_, '_>> for Tag<'_> {
    fn eq(&self, other: &TagAccess<'_, '_>) -> bool {
        self.repr.eq(&*other.repr)
    }
}

impl PartialEq<Tag<'_>> for TagAccess<'_, '_> {
    fn eq(&self, other: &Tag<'_>) -> bool {
        (*self.repr).eq(&other.repr)
    }
}

impl<'tag> Tag<'tag> {
    tag_methods! {}
}

impl<'tag> TagAccess<'_, 'tag> {
    tag_methods! {}
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
/// Deserializes "network variant" NBT. The root `TAG_Compound` doesn't have a name.
///
/// # Errors
/// If `bytes` contains invalid NBT data, an error will be returned.
pub fn deserialize_network<'tag, 'data: 'tag>(
    bytes: &'data [u8],
) -> Result<Tag<'tag>, NbtDeserializeError> {
    deserialize_internal::<true>(bytes).map(|repr| Tag { repr })
}

///
/// Deserializes "file variant" NBT. The root `TAG_Compound` has a name.
///
/// # Errors
/// If `bytes` contains invalid NBT data, an error will be returned.
pub fn deserialize_file<'tag, 'data: 'tag>(
    bytes: &'data [u8],
) -> Result<Tag<'tag>, NbtDeserializeError> {
    deserialize_internal::<false>(bytes).map(|repr| Tag { repr })
}

#[allow(
    clippy::too_many_lines,
    reason = "This function uses a lot of inline macros."
)]
#[inline]
fn deserialize_internal<'tag, 'data: 'tag, const NETWORK_VARIANT: bool>(
    mut bytes: &'data [u8],
) -> Result<TagRepr<'tag>, NbtDeserializeError> {
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

            #[allow(
                clippy::cast_possible_wrap,
                reason = "We cast back to i32 to get the original value"
            )]
            #[allow(
                clippy::cast_possible_truncation,
                reason = "We never actually overflow an i32"
            )]
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

            alloc::borrow::Cow::Owned(__storage)
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

        TagRepr::Compound(name, hashbrown::HashMap::default())
    };

    let mut ctx_stack = array_stack::ArrayStack::<_, DEPTH_LIMIT>::new();
    ctx_stack.push((None, root));

    loop {
        let (target_len, ref mut ctx) = ctx_stack.peek_mut().unwrap();

        // will be None unless ctx is TAG_List
        let target_len = *target_len;

        let (ty, name, old_len) = match &ctx {
            TagRepr::List(_, ty, storage) => (*ty, None, storage.len()),
            TagRepr::Compound(_, storage) => {
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
            TAG_END => TagRepr::End,
            TAG_BYTE => TagRepr::Byte(name, i8::from_be_bytes(*next_n!(1))),
            TAG_SHORT => TagRepr::Short(name, i16::from_be_bytes(*next_n!(2))),
            TAG_INT => TagRepr::Int(name, i32::from_be_bytes(*next_n!(4))),
            TAG_LONG => TagRepr::Long(name, i64::from_be_bytes(*next_n!(8))),
            TAG_FLOAT => TagRepr::Float(name, f32::from_be_bytes(*next_n!(4))),
            TAG_DOUBLE => TagRepr::Double(name, f64::from_be_bytes(*next_n!(8))),
            TAG_BYTE_ARRAY => TagRepr::ByteArray(name, Cow::Borrowed(next_n!(length_prefix!()))),
            TAG_STRING => TagRepr::String(
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

                TagRepr::List(name, list_ty, Vec::with_capacity(len))
            }
            TAG_COMPOUND => {
                flow = ContainerFlow::Map;
                TagRepr::Compound(name, hashbrown::HashMap::default())
            }
            TAG_INT_ARRAY => TagRepr::IntArray(name, array_storage!(i32)),
            TAG_LONG_ARRAY => TagRepr::LongArray(name, array_storage!(i64)),

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

                    if let TagRepr::Compound(_, storage) = &mut finished {
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
    use crate::{deserialize_file, deserialize_network, keys, tag};
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

        let expected = tag!(Compound: {
            String["name"]: "Bananrama"
        });

        let tag = deserialize_network(&data).expect("tag should have been valid");
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

        let tag = deserialize_file(&decompressed).expect("tag should have been valid");

        let mut bytes = Vec::with_capacity(1000);
        for i in 0usize..=999 {
            let result = i
                .wrapping_mul(i)
                .wrapping_mul(255)
                .wrapping_add(i.wrapping_mul(7));
            bytes.push((result % 100) as u8);
        }

        let bytes_tag = tag.get(&keys!({"byteArrayTest (the first 1000 values of (n*n*255+n*7)%100, starting with n=0 (0, 62, 34, 16, 8, ...))"})).expect("should have had bytes key");
        let tag_bytes = bytes_tag.as_byte_array().expect("expected byte array type");

        assert_eq!(&bytes[..], tag_bytes.as_ref());

        let expected = tag!(Compound["Level"]: {
            Compound["nested compound test"]: {
                Compound["egg"]: {
                    String["name"]: "Eggbert",
                    Float["value"]: 0.5
                },
                Compound["ham"]: {
                    String["name"]: "Hampus",
                    Float["value"]: 0.75
                }
            },
            Int["intTest"]: 2147483647,
            Byte["byteTest"]: 127,
            String["stringTest"]: "HELLO WORLD THIS IS A TEST STRING ÅÄÖ!",
            Long List["listTest (long)"]: [
                11, 12, 13, 14, 15
            ],
            Double["doubleTest"]: 0.49312871321823148,
            Float["floatTest"]: 0.49823147058486938,
            Long["longTest"]: 9223372036854775807,
            Compound List["listTest (compound)"]: [
                {
                    Long["created-on"]: 1264099775885,
                    String["name"]: "Compound tag #0"
                },
                {
                    Long["created-on"]: 1264099775885,
                    String["name"]: "Compound tag #1"
                }
            ],
            ByteArray["byteArrayTest (the first 1000 values of (n*n*255+n*7)%100, starting with n=0 (0, 62, 34, 16, 8, ...))"]: bytes,
            Short["shortTest"]: 32767
        });

        assert_eq!(expected, tag);
    }
}
