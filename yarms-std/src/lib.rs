//!
//! Language utilities for `yarms` that are too general-purpose to go in any other crate.

#![no_std]

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

///
/// A simple API for unifying types allowing interior mutability.
pub mod access;

///
/// Non-`std` dependent IO traits.
pub mod io;
