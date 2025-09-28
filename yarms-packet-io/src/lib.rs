//!
//! Support for reading/writing Minecraft packets ([`yarms_packet::Packet`]) to and from generic
//! I/O sources, which are abstracted via the [`buf_fill::BufFill`] trait.
//!
//! Similarly to [`yarms_protocol`], this crate is _mostly_ protocol version-agnostic.
//!
//! # Features
//!
//! * `std` (default): Enables `std`-specific features, currently only used for converting I/O
//!   errors (`std::io::Error`).
//! * `tokio`: Enables Tokio `AsyncRead` support, through [`buf_fill::AsyncReadAdapter`].

#![no_std]

pub(crate) extern crate alloc;
#[cfg(feature = "std")]
pub(crate) extern crate std;

#[cfg(target_pointer_width = "16")]
///
/// For proper protocol support, we need to index slices larger than what we'd be able to do with a
/// 16-bit usize!
compile_error!("This crate does not support 16-bit targets!");

///
/// Encryption/decryption of arbitrary byte slices.
pub mod crypto;

///
/// Support for filling a [`bytes::BufMut`] with a specified minimum number of bytes.
pub mod buf_fill;

///
/// Support for types that can be expressed as an iterator over mutable byte chunks.
pub mod disjoint;

///
/// Low-level packet encoding/decoding from byte slices.
pub mod codec;

///
/// The smallest valid packet length. This doesn't include the length prefix byte(s), just the
/// packet identifier and body.
pub const MIN_PACKET_LEN: i32 = 1_i32;

///
/// Maximum length of a packet, not including the packet length field itself. This applies to both
/// compressed and decompressed packets.
///
/// This is an [`i32`] instead of e.g. a [`usize`] to reflect the fact that this value is inherent
/// to the protocol, which mostly uses signed integers. We also primarily compare this against
/// [`yarms_protocol::types::VarInt`]s that themselves dereference to `i32`.
pub const MAX_PACKET_LEN: i32 = 2_097_151_i32;

///
/// Smallest valid "body length". This includes only packet-type-specific data. It does not include
/// the packet identifier, data length, or packet length prefix.
///
/// Empty (zero-length) bodies are valid.
pub const MIN_BODY_LEN: i32 = 0_i32;

///
/// The smallest valid length for compressed packet data. Values smaller than this are definitely
/// invalid and can be rejected trivially.
///
/// This value is based on the ZLIB compressed data format:
/// https://www.rfc-editor.org/rfc/rfc1950#page-4
///
/// Specifically, the first 2 bytes are the `CMF` and `FLG`, whereas the last 4 are an `ADLER32`
/// checksum. The packet data itself must always have at least a single byte (because of the packet
/// id) so 7 bytes is a safe lower bound.
pub const MIN_COMPRESSED_DATA_LEN: i32 = 7_i32;

///
/// The minimum value for the data length field, which is 1 byte for the packet identifier.
pub const MIN_UNCOMPRESSED_DATA_LEN: i32 = 1_i32;

///
/// Maximum size of the "data length" field of a _compressed_ packet. This limit is unused for
/// non-compressed packets.
///
/// This is an [`i32`] instead of e.g. a [`usize`] to reflect the fact that this value is inherent
/// to the protocol, which uses mostly signed integers. We also primarily compare this against
/// [`yarms_protocol::types::VarInt`]s that themselves dereference to `i32`.
pub const MAX_UNCOMPRESSED_DATA_LEN: i32 = 8_388_608_i32;

///
/// Type alias for [`yarms_protocol::Result`].
pub type Result<T> = yarms_protocol::Result<T>;
