//!
//! Support for NBT (named binary tag) format as used by Minecraft. Uses `serde`. `no_std`
//! compatible.

#![no_std]

///
/// Convert to and from Java's "modified UTF-8" (MUTF-8) format and normal, sane UTF-8 strings.
pub mod mutf;

///
/// Internal deserialization utilities.
mod deserialize;

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

use core::fmt::{Debug, Display, Formatter};
use serde::de::{DeserializeSeed, MapAccess, SeqAccess, StdError, Visitor};
use serde::{Deserializer, Serialize};
use std::error::Error;

pub enum NbtError {
    UnexpectedEOF,
    UnknownType(u16),
    InvalidMUTF8,
}

impl StdError for NbtError {}

impl Debug for NbtError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl Display for NbtError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl serde::de::Error for NbtError {
    fn custom<T>(msg: T) -> Self
    where
        T: Display,
    {
        todo!()
    }
}

pub type Result<T> = core::result::Result<T, NbtError>;

#[derive(Copy, Clone)]
enum TagType {
    End = 0,
    Byte = 1,
    Short = 2,
    Int = 3,
    Long = 4,
    Float = 5,
    Double = 6,
    ByteArray = 7,
    String = 8,
    List = 9,
    Compound = 10,
    IntArray = 11,
    LongArray = 12,
}

pub struct NetworkDeserializer<'de> {
    bytes: &'de [u8],
}

struct NetworkSeqDe<'a, 'de: 'a> {
    de: &'a mut NetworkDeserializer<'de>,
    len: usize,
    visited: usize,
}

impl NetworkDeserializer<'_> {
    fn next_type(&mut self) -> core::result::Result<TagType, NbtError> {
        if self.bytes.len() < size_of::<u16>() {
            return Err(NbtError::UnexpectedEOF);
        }

        let bytes = &self.bytes[..size_of::<u16>()];
        let ty_id = u16::from_be_bytes(bytes.try_into().unwrap());

        self.bytes = &self.bytes[size_of::<u16>()..];

        Ok(match ty_id {
            0 => TagType::End,
            1 => TagType::Byte,
            2 => TagType::Short,
            3 => TagType::Int,
            4 => TagType::Long,
            5 => TagType::Float,
            6 => TagType::Double,
            7 => TagType::ByteArray,
            8 => TagType::String,
            9 => TagType::List,
            10 => TagType::Compound,
            11 => TagType::IntArray,
            12 => TagType::LongArray,
            other => return Err(NbtError::UnknownType(other)),
        })
    }
}

impl<'a, 'de> Deserializer<'de> for &'a mut NetworkDeserializer<'de> {
    type Error = NbtError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        let ty = self.next_type()?;

        let byte_ref = &mut self.bytes;
        match ty {
            TagType::End => {}
            TagType::Byte => return visitor.visit_i8(deserialize::parse_i8(byte_ref)?),
            TagType::Short => return visitor.visit_i16(deserialize::parse_i16(byte_ref)?),
            TagType::Int => return visitor.visit_i32(deserialize::parse_i32(byte_ref)?),
            TagType::Long => return visitor.visit_i64(deserialize::parse_i64(byte_ref)?),
            TagType::Float => {}
            TagType::Double => {}
            TagType::ByteArray => {}
            TagType::String => {}
            TagType::List => {}
            TagType::Compound => {}
            TagType::IntArray => {}
            TagType::LongArray => {}
        }

        self.bytes = byte_ref;
        todo!()
    }

    serde::forward_to_deserialize_any! {
        bool i8 i16 i32 i64 i128 u8 u16 u32 u64 u128 f32 f64 char str string
        bytes byte_buf option unit unit_struct newtype_struct seq tuple
        tuple_struct struct enum identifier ignored_any
    }

    fn deserialize_map<V>(mut self, visitor: V) -> Result<V::Value>
    where
        V: Visitor<'de>,
    {
        visitor.visit_map(NetworkSeqDe {
            de: &mut self,
            len: 0,
            visited: 0,
        })
    }
}

impl<'de, 'a> SeqAccess<'de> for NetworkSeqDe<'a, 'de> {
    type Error = NbtError;

    fn next_element_seed<T>(
        &mut self,
        seed: T,
    ) -> std::result::Result<Option<T::Value>, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        if self.visited >= self.len {
            return Ok(None);
        }

        self.visited += 1;
        seed.deserialize(&mut *self.de).map(Some)
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.len)
    }
}

impl<'de, 'a> MapAccess<'de> for NetworkSeqDe<'a, 'de> {
    type Error = NbtError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>>
    where
        K: DeserializeSeed<'de>,
    {
        if self.visited >= self.len {
            return Ok(None);
        }

        self.visited += 1;
        seed.deserialize(&mut *self.de).map(Some)
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value>
    where
        V: DeserializeSeed<'de>,
    {
        seed.deserialize(&mut *self.de)
    }

    fn size_hint(&self) -> Option<usize> {
        Some(self.len)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn test() {}
}
