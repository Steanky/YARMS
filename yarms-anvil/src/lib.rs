//!
//! Support for the Anvil format.

#![no_std]

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

///
/// A very simple growable buffer of bytes based on `Vec`.
pub mod buffer;

///
/// Decoding chunks from an I/O source.
pub mod chunk_decoder;

///
/// Reading chunks.
pub mod loader;

///
/// Support for loading Anvil regions from some I/O source.
pub mod region;

///
/// Anvil headers (chunk table).
pub mod header;

///
/// Utility to provide scoped mutable access to types.
pub mod access;

use alloc::string::String;
use alloc::string::ToString;
use core::str::FromStr;

///
/// Compute the Anvil region file name given the region coordinates.
///
/// Example usage:
///
/// ```
/// use yarms_anvil::region_to_file_name;
///
/// let name = region_to_file_name(42, -10);
/// assert_eq!(name, "r.42.-10.mca");
///
/// ```
#[must_use]
pub fn region_to_file_name(region_x: i32, region_z: i32) -> String {
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

///
/// Inverse of [`region_to_file_name`]. Converts a filename to its corresponding region coordinates.
/// Returns `None` if the format is not as expected.
///
/// ```
/// use yarms_anvil::region_from_file_name;
///
/// let file_name = "r.42.-10.mca";
/// let pair = region_from_file_name(file_name).expect("should be a valid Anvil filename");
///
/// assert_eq!(pair, (42, -10))
///
/// ```
#[must_use]
pub fn region_from_file_name(name: &str) -> Option<(i32, i32)> {
    let mut array = [""; 4];

    name.splitn(4, '.')
        .zip(0..)
        .for_each(|(part, idx)| array[idx] = part);

    if array[0] != "r" || array[3] != "mca" {
        return None;
    }

    let region_x = i32::from_str(array[1]).ok()?;
    let region_z = i32::from_str(array[2]).ok()?;

    Some((region_x, region_z))
}
