//!
//! Support for Minecraft "identifiers" (resource locations), of the format `{namespace}:{value}`,
//! via the [`Identifier`] struct.
//!
//! These are typically needed to refer to assets or resources for any remotely modern Minecraft
//! versions.
//!
//! # Features
//! * `default`: Enables the `std` feature.
//! * `std`: Enables conversion between [`IdentifierParseError`] and [`std::io::Error`].

#![no_std]

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

use core::cmp::Ordering;
use core::error::Error;
use core::fmt::{Display, Formatter};
use core::hash::{Hash, Hasher};

use alloc::string::String;

///
/// The default namespace used when one is not provided.
pub static MINECRAFT_NAMESPACE: &str = "minecraft";

///
/// The character used to separate namespace and value. This will always be an ASCII character, and
/// can cast to a `u8` if needed.
pub const NAMESPACE_VALUE_SEPARATOR: char = ':';

///
/// The maximum length of an identifier's internal string.
///
/// Note that, because identifiers are restricted to (a subset of) ASCII characters, this is also
/// the length limit of the string in bytes.
pub const MAX_IDENTIFIER_LEN: usize = 32767;

// used internally to length-check strings with a default namespace
const MAX_DEFAULT_NAMESPACE_LEN: usize = MAX_IDENTIFIER_LEN - (MINECRAFT_NAMESPACE.len()) - 1;

///
/// A Minecraft identifier, such as `minecraft:stone`.
///
/// An identifier conceptually consists of a "namespace" and a "value", separated by a `:`.
/// Both the namespace and value component of an identifier can only consist of a limited subset of
/// ASCII characters, which are detailed [here](Identifier::is_valid_namespace_char) and
/// [here](Identifier::is_valid_value_char).
///
/// Identifiers can be defined with or without a separator. Identifiers without a separator are
/// assumed to use the "default namespace" [`MINECRAFT_NAMESPACE`], which is just `minecraft`.
///
/// An identifier like `:test` is considered to have an _empty_ namespace. This is distinct from
/// `test`, which is semantically equivalent to `minecraft:test`.
///
/// Instances of Identifier can be constructed using [`Identifier::parse`] and [`Identifier::new`].
/// Which one should be preferred depends on the use case. `parse` supports constructing from a
/// single string, `new` supports constructing from a separate namespace and value.
///
/// An identifier's string representation cannot conceptually exceed [`MAX_IDENTIFIER_LEN`] in
/// length, and it is not possible to create one.
#[derive(Debug, Clone)]
pub struct Identifier {
    inner: String,
    separator_index: Option<usize>,
}

impl Hash for Identifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        String::hash(&self.inner, state);
    }
}

impl PartialEq<Self> for Identifier {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl Eq for Identifier {}

impl PartialOrd<Self> for Identifier {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Identifier {
    fn cmp(&self, other: &Self) -> Ordering {
        self.namespace()
            .cmp(other.namespace())
            .then_with(|| self.value().cmp(other.value()))
    }
}

///
/// Error returned when attempting to parse an invalid identifier.
#[derive(Debug)]
pub enum IdentifierParseError {
    ///
    /// The namespace component of the identifier was invalid.
    InvalidNamespace,

    ///
    /// The value component of the identifier was invalid.
    InvalidValue,

    ///
    /// The resulting internal string would have been too long.
    TooLong,
}

impl Error for IdentifierParseError {}

impl Display for IdentifierParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            IdentifierParseError::InvalidNamespace => "invalid namespace",
            IdentifierParseError::InvalidValue => "invalid value",
            IdentifierParseError::TooLong => "too long",
        })
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}:{}", self.namespace(), self.value())
    }
}

#[cfg(feature = "std")]
impl From<IdentifierParseError> for std::io::Error {
    fn from(value: IdentifierParseError) -> Self {
        std::io::Error::new(std::io::ErrorKind::InvalidData, value)
    }
}

fn is_default(namespace: &str) -> bool {
    namespace == MINECRAFT_NAMESPACE
}

impl Identifier {
    ///
    /// Check if the given char is valid for inclusion in a namespace.
    ///
    /// Valid namespace characters are limited to `[a-z0-9-_]` (ASCII lowercase letters,
    /// ASCII digits, plus `-` and `_`).
    #[must_use]
    pub const fn is_valid_namespace_char(char: char) -> bool {
        char.is_ascii_lowercase() || char.is_ascii_digit() || char == '-' || char == '_'
    }

    ///
    /// Check if the given char is valid for inclusion in a value.
    ///
    /// Valid value chars are limited to `[a-z0-9-_/\.]` (ASCII lowercase letters, ASCII digits,
    /// `-`, `_`, `/`, and `.`). Note that values accept all the same characters that namespaces do,
    /// with the addition of allowing `/` and `.`.
    #[must_use]
    pub const fn is_valid_value_char(char: char) -> bool {
        Self::is_valid_namespace_char(char) || char == '/' || char == '.'
    }

    ///
    /// Checks if the given string is valid for the namespace component of an identifier.
    ///
    /// Does not perform length checks: the namespace may be too large to be used to construct an
    /// identifier.
    #[must_use]
    pub fn is_valid_namespace(namespace: &str) -> bool {
        // check that all characters are valid for namespaces
        namespace.chars().all(Self::is_valid_namespace_char)
    }

    ///
    /// Checks if the given string represents a valid identifier; that is, if it may be passed to
    /// [`Self::parse`] without resulting in an error. Also performs a length check on the string,
    /// to ensure it does not exceed [`MAX_IDENTIFIER_LEN`].
    #[must_use]
    pub fn is_valid_identifier(identifier: &str) -> bool {
        match identifier
            .chars()
            .position(|c| c == NAMESPACE_VALUE_SEPARATOR)
        {
            None => {
                identifier.len() <= MAX_DEFAULT_NAMESPACE_LEN && Self::is_valid_value(identifier)
            }
            Some(position) => {
                identifier.len() <= MAX_IDENTIFIER_LEN
                    && Self::is_valid_namespace(&identifier[..position])
                    && Self::is_valid_value(&identifier[position + 1..])
            }
        }
    }

    ///
    /// Checks if the given string is valid for the value component of an identifier.
    #[must_use]
    pub fn is_valid_value(value: &str) -> bool {
        // check that all characters are valid
        value.chars().all(Self::is_valid_value_char)
    }

    ///
    /// Creates a new identifier from a namespace string and value string.
    ///
    /// If `value` is an owned String, and `namespace` is the default namespace, this method can
    /// trivially avoid any additional allocation. When `namespace` is non-default, additional
    /// allocation may not occur depending on the available capacity of `value`.
    ///
    /// # Errors
    /// Returns [`Err`] if the namespace or the value are invalid (contain invalid characters) or if
    /// the resulting identifier would be too long.
    ///
    /// # Panics
    /// This function should never panic, unless there is an allocation failure. Note that due to
    /// optimizations, and depending upon the input, allocation may not happen at all.
    pub fn new<V>(namespace: &str, value: V) -> Result<Identifier, IdentifierParseError>
    where
        V: AsRef<str> + Into<String>,
    {
        let value_ref = value.as_ref();
        let is_default_namespace = is_default(namespace);

        if !is_default_namespace && !Self::is_valid_namespace(namespace) {
            return Err(IdentifierParseError::InvalidNamespace);
        }

        if !Self::is_valid_value(value_ref) {
            return Err(IdentifierParseError::InvalidValue);
        }

        let separator_index = if is_default_namespace {
            if value_ref.len() > MAX_DEFAULT_NAMESPACE_LEN {
                return Err(IdentifierParseError::TooLong);
            }

            None
        } else {
            if namespace
                .len()
                .saturating_add(value_ref.len())
                .saturating_add(1)
                > MAX_IDENTIFIER_LEN
            {
                return Err(IdentifierParseError::TooLong);
            }

            Some(namespace.len())
        };

        let mut value: String = value.into();
        if is_default_namespace {
            // just use inner as-is, but make sure it's not wasting capacity
            value.shrink_to_fit();
        } else {
            let mut bytes = value.into_bytes();
            let end = bytes.len();

            // the extra room we need for namespace and value
            // no overflow here: we length-checked above
            let new_bytes = namespace.len() + 1;

            // the new length of the identifier
            // no overflow here: we length-checked above
            let new_len = new_bytes + bytes.len();

            bytes.resize(new_len, 0);
            bytes.copy_within(..end, new_bytes);

            bytes[..new_bytes - 1].copy_from_slice(namespace.as_bytes());

            // NAMESPACE_VALUE_SEPARATOR encodes to 1 byte
            bytes[new_bytes - 1] = NAMESPACE_VALUE_SEPARATOR as u8;
            bytes.shrink_to_fit();

            // SAFETY:
            // - we started with valid UTF-8 bytes that came from a preexisting String
            // - we prepended valid UTF-8 bytes that come from a preexisting &str
            value = unsafe { String::from_utf8_unchecked(bytes) }
        }

        Ok(Identifier {
            inner: value,
            separator_index,
        })
    }

    ///
    /// Creates an identifier from a pre-existing String, in the format `namespace:value`. If the
    /// separator character `:` is not present, the identifier will use the default namespace
    /// [`MINECRAFT_NAMESPACE`].
    ///
    /// # Errors
    /// Returns [`Err`] if the namespace or the value are invalid, or if the resulting identifier
    /// would be too long.
    pub fn parse<S: Into<String>>(identifier: S) -> Result<Identifier, IdentifierParseError> {
        let mut identifier = identifier.into();

        // search for the first instance of NAMESPACE_VALUE_SEPARATOR
        // if we don't find it, use the default namespace
        // if we do find it, (probably) non-default namespace
        // any additional : will be seen as part of the value, which results in returning Err
        match identifier
            .chars()
            .position(|c| c == NAMESPACE_VALUE_SEPARATOR)
        {
            None => {
                if identifier.len() > MAX_DEFAULT_NAMESPACE_LEN {
                    return Err(IdentifierParseError::TooLong);
                }

                if !Self::is_valid_value(&identifier) {
                    return Err(IdentifierParseError::InvalidValue);
                }

                identifier.shrink_to_fit();

                // no separator means default namespace
                Ok(Identifier {
                    inner: identifier,
                    separator_index: None,
                })
            }

            Some(index) => {
                if identifier.len() > MAX_IDENTIFIER_LEN {
                    return Err(IdentifierParseError::TooLong);
                }

                let namespace = &identifier[..index];
                let value = &identifier[index + 1..];

                let is_default_namespace = is_default(namespace);
                if !is_default_namespace && !Self::is_valid_namespace(namespace) {
                    return Err(IdentifierParseError::InvalidNamespace);
                }

                if !Self::is_valid_value(value) {
                    return Err(IdentifierParseError::InvalidValue);
                }

                // clean up internal representation:
                // empty (rather than default) namespace should have a leading :
                if is_default_namespace {
                    identifier.replace_range(..=index, "");
                }

                identifier.shrink_to_fit();
                Ok(Identifier {
                    inner: identifier,
                    separator_index: if is_default_namespace {
                        None
                    } else {
                        Some(index)
                    },
                })
            }
        }
    }

    ///
    /// Gets a reference to the namespace component.
    ///
    /// This will be [`MINECRAFT_NAMESPACE`] if no namespace was specified during creation.
    #[must_use]
    pub fn namespace(&self) -> &str {
        match self.separator_index {
            // no separator means default namespace
            None => MINECRAFT_NAMESPACE,
            Some(index) => &self.inner[..index],
        }
    }

    ///
    /// Gets a reference to the value component.
    #[must_use]
    pub fn value(&self) -> &str {
        match self.separator_index {
            // no separator means the entire string is the value
            None => &self.inner,
            Some(index) => self.inner.split_at(index + 1).1,
        }
    }

    ///
    /// Returns the inner representation of this identifier: if the namespace is the default
    /// [`MINECRAFT_NAMESPACE`], the identifier is just the value, with no `:`. Otherwise, this is
    /// the standard representation `namespace:value`.
    ///
    /// If you always want the full identifier, use [`Identifier::to_string`]. Note that this will
    /// result in an allocation.
    #[must_use]
    pub fn identifier(&self) -> &str {
        &self.inner
    }

    ///
    /// Converts this identifier into its inner representation. See [`Self::identifier`].
    ///
    /// This differs from calling [`Self::to_string`] because it does not include the default
    /// namespace.
    ///
    /// This method will never allocate.
    #[must_use]
    pub fn into_identifier(self) -> String {
        self.inner
    }
}

#[cfg(test)]
mod tests {
    use crate::Identifier;
    use crate::MINECRAFT_NAMESPACE;
    use alloc::format;
    use alloc::string::{String, ToString};

    const NAMESPACE_CHARS: [char; 38] = [
        '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h',
        'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
        '_', '-',
    ];

    const VALUE_CHARS: [char; 40] = [
        '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h',
        'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
        '_', '-', '.', '/',
    ];

    #[test]
    fn to_string() {
        let namespace_id =
            Identifier::new("test_namespace", "value").expect("Failed to create NamespaceID");

        assert_eq!(namespace_id.to_string(), "test_namespace:value");
        assert_eq!(namespace_id.namespace(), "test_namespace");
        assert_eq!(namespace_id.value(), "value");
    }

    #[test]
    fn parse_default() {
        let namespace_id = Identifier::parse("test_value").expect("Failed to parse NamespaceID");

        assert_eq!(namespace_id.to_string(), "minecraft:test_value");
        assert_eq!(namespace_id.namespace(), MINECRAFT_NAMESPACE);
        assert_eq!(namespace_id.value(), "test_value");
    }

    #[test]
    fn empty_namespace() {
        let namespace_id = Identifier::new("", "test_value").expect("Failed to create NamespaceID");

        assert_eq!(namespace_id.to_string(), ":test_value");
        assert_eq!(namespace_id.namespace(), "");
        assert_eq!(namespace_id.value(), "test_value");
    }

    #[test]
    fn empty_namespace_parse() {
        let namespace_id = Identifier::parse(":test_value").expect("Failed to parse NamespaceID");

        assert_eq!(namespace_id.to_string(), ":test_value");
        assert_eq!(namespace_id.namespace(), "");
        assert_eq!(namespace_id.value(), "test_value");
    }

    #[test]
    fn empty_value() {
        let namespace_id =
            Identifier::new("test_namespace", "").expect("Failed to create NamespaceID");

        assert_eq!(namespace_id.to_string(), "test_namespace:");
        assert_eq!(namespace_id.namespace(), "test_namespace");
        assert_eq!(namespace_id.value(), "");
    }

    #[test]
    fn empty_value_parse() {
        let namespace_id =
            Identifier::parse("test_namespace:").expect("Failed to create NamespaceID");

        assert_eq!(namespace_id.to_string(), "test_namespace:");
        assert_eq!(namespace_id.namespace(), "test_namespace");
        assert_eq!(namespace_id.value(), "");
    }

    #[test]
    fn empty_namespace_and_value() {
        let namespace_id = Identifier::new("", "").expect("Failed to create NamespaceID");

        assert_eq!(namespace_id.to_string(), ":");
        assert_eq!(namespace_id.namespace(), "");
        assert_eq!(namespace_id.value(), "");
    }

    #[test]
    fn empty_namespace_and_value_parse() {
        let namespace_id = Identifier::parse(":").expect("Failed to create NamespaceID");

        assert_eq!(namespace_id.to_string(), ":");
        assert_eq!(namespace_id.namespace(), "");
        assert_eq!(namespace_id.value(), "");
    }

    #[test]
    fn empty_string() {
        let namespace_id = Identifier::parse("").expect("Failed to create NamespaceID");

        assert_eq!(namespace_id.to_string(), "minecraft:");
        assert_eq!(namespace_id.namespace(), "minecraft");
        assert_eq!(namespace_id.value(), "");
    }

    #[test]
    fn validity() {
        assert!(Identifier::is_valid_identifier("minecraft:t"));
        assert!(Identifier::is_valid_identifier("minecraft:"));
        assert!(Identifier::is_valid_identifier(":"));
        assert!(Identifier::is_valid_identifier(""));
        assert!(Identifier::is_valid_identifier("a:testing///"));

        assert!(!Identifier::is_valid_identifier(" "));
        assert!(!Identifier::is_valid_identifier("::"));
        assert!(!Identifier::is_valid_identifier("a/:testing"));
    }

    #[test]
    fn invalid_chars() {
        let result = Identifier::parse("/:test_value");
        let result1 = Identifier::parse(".:test_value");
        let result3 = Identifier::parse(" :");
        let result4 = Identifier::parse(": ");
        let result5 = Identifier::parse(" :test_value");
        let result6 = Identifier::parse(": test_value");
        let result7 = Identifier::parse("test_value ");
        let result8 = Identifier::parse("test_namespace:test_value ");
        let result9 = Identifier::parse("::test_value ");
        let result10 = Identifier::parse("test_namespace::");
        let result11 = Identifier::parse("::");

        assert!(result.is_err());
        assert!(result1.is_err());
        assert!(result3.is_err());
        assert!(result4.is_err());
        assert!(result5.is_err());
        assert!(result6.is_err());
        assert!(result7.is_err());
        assert!(result8.is_err());
        assert!(result9.is_err());
        assert!(result10.is_err());
        assert!(result11.is_err());
    }

    #[test]
    fn parse_many() {
        for namespace_a in NAMESPACE_CHARS {
            for namespace_b in NAMESPACE_CHARS {
                let mut namespace_str = String::with_capacity(2);
                namespace_str.push(namespace_a);
                namespace_str.push(namespace_b);

                assert!(Identifier::is_valid_namespace(&namespace_str));

                for value_a in VALUE_CHARS {
                    for value_b in VALUE_CHARS {
                        let mut value_str = String::with_capacity(2);
                        value_str.push(value_a);
                        value_str.push(value_b);

                        let result = Identifier::new(&namespace_str, &value_str)
                            .expect("Failed to create NamespaceID");
                        let full_string = format!("{}:{}", namespace_str, value_str);

                        assert!(Identifier::is_valid_value(&value_str));
                        assert!(Identifier::is_valid_identifier(&full_string));

                        let result_parse =
                            Identifier::parse(full_string).expect("Failed to parse NamespaceID");

                        assert_eq!(result, result_parse);

                        assert_eq!(result.namespace(), result_parse.namespace());
                        assert_eq!(result.value(), result_parse.value());

                        assert_eq!(result.namespace(), namespace_str);
                        assert_eq!(result.value(), value_str);

                        assert_eq!(result_parse.namespace(), namespace_str);
                        assert_eq!(result_parse.value(), value_str);
                    }
                }
            }
        }
    }
}
