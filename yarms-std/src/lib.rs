//!
//! Language utilities for `yarms` that are too general-purpose to go in any other crate.

#![no_std]

pub(crate) extern crate alloc;

#[cfg(feature = "std")]
pub(crate) extern crate std;

///
/// A simple API for unifying types allowing interior mutability.
pub mod access;

#[cfg(feature = "bound")]
///
/// Utilities for working with bounds.
pub mod bound;

#[cfg(feature = "disjoint")]
///
/// Buffers that may or may not be contiguous.
pub mod disjoint;

#[cfg(feature = "buf-fill")]
///
/// Simple traits for filling buffers with asynchronous IO.
pub mod buf_fill;

///
/// Non-`std` dependent IO traits.
pub mod io;
