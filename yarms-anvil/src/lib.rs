//!
//! Support for the Anvil format.

#![no_std]

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

///
/// A very simple growable buffer of bytes based on `Vec`.
pub mod buffer;

#[cfg(feature = "std")]
#[allow(clippy::std_instead_of_core, reason = "This module is std-only")]
#[allow(clippy::std_instead_of_alloc, reason = "This module is std-only")]
///
/// Decoding chunks from an I/O source.
pub mod chunk_decoder;

///
/// Reading chunks.
pub mod loader;

#[cfg(feature = "std")]
#[allow(clippy::std_instead_of_core, reason = "This module is std-only")]
#[allow(clippy::std_instead_of_alloc, reason = "This module is std-only")]
///
/// Support for loading Anvil regions from some I/O source.
pub mod region;

#[cfg(feature = "std")]
pub use loader::std_dependent::*;

use alloc::string::String;
use alloc::string::ToString;

///
/// Compute the Anvil region file name given the region coordinates.
///
/// Example usage:
///
/// ```
/// use yarms_anvil::region_file_name;
///
/// let name = region_file_name(42, -10);
/// assert_eq!(name, "r.42.-10.mca");
///
/// ```
#[must_use]
pub fn region_file_name(region_x: i32, region_z: i32) -> String {
    let mut file_name = String::with_capacity(16);

    let x_string = region_x.to_string();
    let z_string = region_z.to_string();

    file_name.push('r');
    file_name.push('.');
    file_name.push_str(&x_string);
    file_name.push('.');
    file_name.push_str(&z_string);
    file_name.push('.');
    file_name.push_str("mca");

    file_name
}
