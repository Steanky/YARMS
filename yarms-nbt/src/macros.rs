///
/// Generates an array of [`TagKey`]s.
///
/// The syntax supports a more compact delineation of name and index keys:
/// ```
/// use yarms_nbt::{keys, TagKey};
///
/// let generated = keys!(42, "test");
/// let equivalent = [TagKey::Index(42), TagKey::Name("test")];
///
/// assert_eq!(generated, equivalent);
///
/// fn str_ret_fn() -> &'static str {
///   "static string"
/// }
///
/// // expressions are allowed, not just literals
/// let generated = keys!(10, str_ret_fn(), 20);
/// let equivalent = [TagKey::Index(10), TagKey::Name(str_ret_fn()), TagKey::Index(20)];
///
/// assert_eq!(generated, equivalent);
/// ```
#[macro_export]
macro_rules! keys {
    () => { [$crate::TagKey::Index(0); 0] };

    ( $( $ex:expr ),+ ) => {[
        $( <$crate::TagKey as core::convert::From<_>>::from($ex) ),+
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

#[doc(hidden)]
#[macro_export]
macro_rules! __gen_list_array {
    ( $element_type:ident, ) => {
        [$crate::TagRepr::End; 0]
    };

    ( $element_type:ident, $( $sublist_type:ident : $value:tt ),+ ) => {[
        $(
            $crate::__tag_repr!($sublist_type List : $value)
        ),+
    ]};

    ( $element_type:ident, $( $value:tt ),+ ) => {[
        $(
            $crate::__tag_repr!($element_type : $value)
        ),+
    ]};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __gen_compound_array {
    () => {
        [($crate::alloc::borrow::Cow::Borrowed(""), $crate::TagRepr::End); 0]
    };

    ( $( $tag_type:ident $( $list:ident )? [$( $tag_name:tt )+] : $value:tt ),+ ) => {[
        $(
            $crate::__pair($crate::__tag_repr!($tag_type $( $list )? [$( $tag_name )+] : $value ))
        ),+
    ]};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __tag_value {
    ( $lit:literal ) => {
        $crate::alloc::borrow::Cow::Borrowed($lit)
    };

    ( $ex:ident ) => {
        $crate::alloc::borrow::Cow::Borrowed(&$ex)
    };

    ( $b:block ) => {
        $crate::alloc::borrow::Cow::Owned(core::convert::Into::into<_>($b))
    };

    ( $ex:expr ) => {
        $crate::alloc::borrow::Cow::Borrowed($ex)
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __tag_name {
    () => {
        core::option::Option::None
    };

    ( $e:literal ) => {
        core::option::Option::Some($crate::alloc::borrow::Cow::Borrowed($e))
    };

    ( $e:ident ) => {
        core::option::Option::Some($crate::alloc::borrow::Cow::Borrowed(&$e))
    };

    ( $e:block ) => {
        core::option::Option::Some($crate::alloc::borrow::Cow::Owned(core::convert::Into::into<_>($e)))
    };

    ( $e:expr ) => {
        core::option::Option::Some($crate::alloc::borrow::Cow::Borrowed($e))
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! __tag_repr {
    ( Byte $( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {
        $crate::TagRepr::Byte($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    };

    ( Short $( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {
        $crate::TagRepr::Short($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    };

    ( Int $( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {
        $crate::TagRepr::Int($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    };

    ( Long $( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {
        $crate::TagRepr::Long($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    };

    ( Float $( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {
        $crate::TagRepr::Float($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    };

    ( Double $( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {
        $crate::TagRepr::Double($crate::__tag_name!($( $( $tag_name )+ )?), $tag_value)
    };

    ( ByteArray $( [$( $tag_name:tt )+] )? : $tag_value:tt ) => {
        $crate::TagRepr::ByteArray($crate::__tag_name!($( $( $tag_name )+ )?),
        $crate::__tag_value!($tag_value))
    };

    ( String $( [$( $tag_name:tt )+] )? : $tag_value:tt ) => {
        $crate::TagRepr::String($crate::__tag_name!($( $( $tag_name )+ )?),
        $crate::__tag_value!($tag_value))
    };

    ( IntArray $( [$( $tag_name:tt )+] )? : $tag_value:tt ) => {
        $crate::TagRepr::IntArray($crate::__tag_name!($( $( $tag_name )+ )?),
        $crate::__tag_value!($tag_value))
    };

    ( LongArray $( [$( $tag_name:tt )+] )? : $tag_value:expr ) => {
        $crate::TagRepr::LongArray($crate::__tag_name!($( $( $tag_name )+ )?),
        $crate::__tag_value!($tag_value))
    };

    ( Compound $( [$( $tag_name:tt )+] )? : { $( $tag_value:tt )* } ) => {
        $crate::TagRepr::Compound($crate::__tag_name!($( $( $tag_name )+ )?),
        $crate::__hash_map::HashMap::from($crate::__gen_compound_array!($( $tag_value )*)))
    };

    ( $element_type:ident List $( [$( $tag_name:tt )+] )? : [ $( $list_body:tt )* ] ) => {
        $crate::TagRepr::List($crate::__tag_name!($( $( $tag_name )+ )?),
        $crate::__resolve_ty!($element_type),
        $crate::alloc::vec::Vec::from($crate::__gen_list_array!($element_type, $( $list_body )*)))
    };
}

///
/// This macro provides a way of constructing predefined [`crate::Tag`] variants in code, without the
/// requirement of runtime parsing. This is the only supported way, aside from deserialization, of
/// constructing ad hoc tags.
///
/// ```
/// use yarms_nbt::{keys, tag};
///
/// let example = tag!(Compound: {
///     Byte["value"]: 42,
///     List List["list of lists"]: [ Byte: [0, 2, 3], Int: [4, 5, 897342] ],
///     Compound List ["list of compounds"]: [
///         {  }, // empty compound
///         {
///             String["test1"]: "a string",
///
///             // string list
///             String List["test"]: [
///                 "hello"
///             ]
///         }
///     ]
/// });
///
/// let tag = example.get(&keys!("list of compounds", 1, "test", 0)).expect("tag should exist");
/// assert_eq!("hello", tag.as_string().expect("tag should be a string"));
///
/// ```
///
/// # Borrowing rules
/// This macro attempts to use borrowed, rather than owned, data whenever possible. In many cases
/// this is entirely transparent: for example, string literals are always borrowed (thus avoiding
/// wasteful allocation), but since these are implicitly `'static`, lifetime issues can't really
/// crop up.
///
/// However, sometimes it is not desirable to borrow variables. The simplest case is to avoid
/// compiler errors when trying to return a tag that was constructed with a local variable in a
/// function. This can be accomplished by encasing the variable in a block, which causes the result
/// of the block to converted to the owned variant using its [`Into`] trait:
///
/// ```
/// use std::borrow::Cow;
/// use yarms_nbt::{keys, tag, Tag};
///
/// fn example() -> Tag<'static> {
///     let name = String::from("hello");
///
///     // The curly braces around `name` cause the variable to be moved.
///     // Without these, we'd get an E0515 compiler error!
///     let tag_using_local_var = tag!(Compound[{name}]: {
///         Byte["test"]: 1,
///         String["test2"]: {"this string is owned too, because it's in a block!"}
///     });
///
///     tag_using_local_var
/// }
///
/// let example = example();
///
/// // Check that the name of the example TAG_Compound is the owned variant.
/// if let Some(Cow::Owned(string)) = example.name() {
///     assert_eq!(string, "hello")
/// } else {
///     panic!("example should have been owned and named")
/// }
///
/// let test_byte = example.get(&keys!("test")).expect("tag should have existed");
///
/// // Check that the name of the byte "test" is a borrowed variant.
/// if let Some(Cow::Borrowed(string)) = test_byte.name() {
///     assert_eq!(*string, "test");
/// } else {
///     panic!("test_byte should have been borrowed and named");
/// }
/// ```
///
#[macro_export]
macro_rules! tag {
    ( $( $everything:tt )* ) => {
        $crate::__wrap($crate::__tag_repr!($( $everything )*))
    };
}
