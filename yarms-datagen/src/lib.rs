//!
//! Includes all data-generated code used by YARMS. What exactly is generated depends on the
//! enabled feature flags.

#![no_std]

pub(crate) extern crate alloc;

// YARMS_DATAGEN_CODEFILE is set by build.rs, which should dodge portability issues:
// https://github.com/rust-lang/cargo/issues/13919
// https://github.com/rust-lang/rust/issues/75075
include!(env!(
    "YARMS_DATAGEN_CODEFILE",
    "required environment variable `YARMS_DATAGEN_CODEFILE` was unset"
));

#[cfg(test)]
#[cfg(feature = "all")]
mod tests {
    use crate::pvn_769::packet::serverbound::Handshake;
    use yarms_packet::Packet;

    #[test]
    fn it_works() {
        let handshake = Handshake::resource();
    }
}
