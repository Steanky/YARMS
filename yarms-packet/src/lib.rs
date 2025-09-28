//!
//! Common traits and utilities for Minecraft packets. Does not include the packets themselves;
//! those are found in `yarms-datagen`, for specific versions.
//!
//! Implementations of this crate's most central trait, [`Packet`], can be implemented manually or
//! more conveniently through the procedural macro defined at `yarms-derive`.

#![no_std]

pub(crate) extern crate alloc;
pub(crate) extern crate self as yarms_packet;

use alloc::boxed::Box;
use bytes::{Buf, BufMut};
use core::any::{Any, TypeId};
use core::fmt::{Debug, Formatter};
use core::ops::Deref;
use yarms_protocol::types::VarInt;

///
/// A "packet", according to the
/// [Minecraft protocol](https://minecraft.wiki/w/Java_Edition_protocol). Represents "clientbound"
/// and "serverbound" packets, as well as packets of any connection state.
///
/// This trait is not dyn-compatible. For that, see [`PacketDyn`], which has a blanket
/// implementation for all `T: Packet`.
pub trait Packet {
    ///
    /// This packet's protocol identifier. Generally allowed to be any valid [`VarInt`], though most
    /// commonly it will be non-negative.
    ///
    /// Since this identifier determines what the client (and indeed YARMS itself) expects the data
    /// to look like, sending the wrong identifier will almost always result in a client
    /// disconnecting.
    fn protocol_id() -> VarInt;

    ///
    /// Whether this packet is "clientbound"; that is, if it is meant to be sent from the server to
    /// the client or vice versa. The protocol does not contain any packets that are both
    /// clientbound and serverbound, so this is simply a `bool` rather than a more complex type.
    fn clientbound() -> bool;

    ///
    /// This packet's resource string. This is present in more modern versions of the game and is
    /// unlikely to go away. If this packet implementation was created (generated?) for a version of
    /// the game that doesn't have these, this method just returns an empty string.
    fn resource() -> &'static str;

    ///
    /// Reads the packet body from an in-memory buffer.
    ///
    /// `end_remaining` specifies how many bytes should be remaining in the buffer once this packet
    /// has been fully read. It is unused for the majority of packets, though some require it.
    ///
    /// # Errors
    /// Yields an error if the packet data is not as expected; for example if the bytes were invalid
    /// for the type(s) this packet expects.
    fn read_body<B>(buf: &mut B, end_remaining: usize) -> Result<Self>
    where
        Self: Sized + 'static,
        B: Buf + ?Sized;

    ///
    /// Writes this packet's body to an in-memory buffer.
    ///
    /// # Panics
    /// This method panics if the buffer doesn't have enough capacity to hold this packet's data.
    fn write_body<B>(&self, buf: &mut B) -> usize
    where
        B: BufMut + ?Sized;

    ///
    /// The number of bytes a call to [`self.write_body`] will enter into the buffer.
    ///
    /// Note that this is _not_ necessarily equal to the number of bytes that would be required to
    /// _read_ an otherwise-equivalent packet! This is because some [`yarms_protocol::ProtocolType`]
    /// implementations, most notably [`VarInt`], may represent the same value with differing
    /// numbers of bytes.
    fn len(&self) -> usize;
}

///
/// Dyn-compatible version of [`Packet`]. Automatically implemented for all `T: Packet + 'static`.
///
/// This type should sometimes be used in favor of static-dispatching a regular [`Packet`], due to
/// the sheer number of packet implementations available (hundreds per enabled version).
///
/// Most methods are identical, with the exception that all require `&self`, and there is no
/// equivalent implementation of [`Packet::read_body`], as it does not make sense in the context of
/// dynamic dispatch (you would need a `PacketDyn` to read a `PacketDyn`).
pub trait PacketDyn: Any {
    ///
    /// The protocol ID of this packet. Can be used to determine which concrete type to downcast to.
    /// See [`Packet::protocol_id`].
    fn protocol_id(&self) -> VarInt;

    ///
    /// Whether this packet is clientbound or serverbound. See [`Packet::clientbound`].
    fn clientbound(&self) -> bool;

    ///
    /// The resource string representing this packet. See [`Packet::resource`].
    fn resource(&self) -> &'static str;

    ///
    /// Writes the body of this packet to an in-memory buffer. See [`Packet::write_body`].
    fn write_body(&self, buf: &mut dyn BufMut) -> usize;

    ///
    /// The length of this packet, when written. See [`Packet::len`].
    fn len(&self) -> usize;
}

impl<T> PacketDyn for T
where
    T: Packet + 'static,
{
    fn protocol_id(&self) -> VarInt {
        T::protocol_id()
    }

    fn clientbound(&self) -> bool {
        T::clientbound()
    }

    fn resource(&self) -> &'static str {
        T::resource()
    }

    fn write_body(&self, buf: &mut dyn BufMut) -> usize {
        T::write_body(self, buf)
    }

    fn len(&self) -> usize {
        T::len(self)
    }
}

impl Debug for dyn PacketDyn {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "PacketDyn {{ protocol_id: {:?}, clientbound: {}, resource: {} }}",
            self.protocol_id(),
            self.clientbound(),
            self.resource()
        )
    }
}

///
/// (Attempts to) downcast a [`PacketDyn`] to a _sized_, concrete [`Packet`] implementation,
/// consuming the given [`Box`] in the process.
///
/// # Errors
/// Returns `Err` if the packet is the wrong concrete type. The returned value will just contain the
/// original boxed value in this case.
pub fn downcast<P: Packet + Sized + 'static>(
    packet: Box<dyn PacketDyn>,
) -> core::result::Result<P, Box<dyn PacketDyn>> {
    let target_id = TypeId::of::<P>();

    // make it very clear we are calling `type_id` on &dyn PacketDyn
    let reference: &dyn PacketDyn = Box::deref(&packet);
    let given_id = reference.type_id();

    if target_id != given_id {
        // conversion failed, the types differ!
        return Err(packet);
    }

    let raw: *mut dyn PacketDyn = Box::into_raw(packet);

    // SAFETY:
    // - we checked above that `P` has the same type id as the underlying type of `packet`
    // - `raw` is aligned and non-null because it came from Box::into_raw
    // - P is Sized, so we don't have to worry about ?Sized -> ?Sized conversion validity
    // - we will never access `raw` after this point
    unsafe { Ok(core::ptr::read(raw as *const P)) }
}

///
/// Type alias for [`yarms_protocol::Result`].
pub type Result<T> = yarms_protocol::Result<T>;

fn _assert_dyn_compatible(_: &mut dyn PacketDyn) {}

#[cfg(test)]
mod tests {
    use crate::{downcast, Packet};
    use alloc::boxed::Box;
    use bytes::{Buf, BufMut};
    use core::fmt::Debug;
    use yarms_packet::PacketDyn;
    use yarms_protocol::types::VarInt;

    #[derive(Debug)]
    struct TestPacket {
        val: VarInt,
    }

    #[derive(Debug)]
    struct TestPacket2 {
        val: VarInt,
    }

    impl Packet for TestPacket {
        fn protocol_id() -> VarInt {
            VarInt::from(42)
        }

        fn clientbound() -> bool {
            true
        }

        fn resource() -> &'static str {
            "test"
        }

        fn read_body<B>(buf: &mut B, end_remaining: usize) -> crate::Result<Self>
        where
            Self: Sized + 'static,
            B: Buf + ?Sized,
        {
            unimplemented!()
        }

        fn write_body<B>(&self, buf: &mut B) -> usize
        where
            B: BufMut + ?Sized,
        {
            unimplemented!()
        }

        fn len(&self) -> usize {
            unimplemented!()
        }
    }
    impl Packet for TestPacket2 {
        fn protocol_id() -> VarInt {
            VarInt::from(42)
        }

        fn clientbound() -> bool {
            true
        }

        fn resource() -> &'static str {
            "test"
        }

        fn read_body<B>(buf: &mut B, end_remaining: usize) -> crate::Result<Self>
        where
            Self: Sized + 'static,
            B: Buf + ?Sized,
        {
            unimplemented!()
        }

        fn write_body<B>(&self, buf: &mut B) -> usize
        where
            B: BufMut + ?Sized,
        {
            unimplemented!()
        }

        fn len(&self) -> usize {
            unimplemented!()
        }
    }

    #[test]
    fn downcast_ok() {
        let b: Box<dyn PacketDyn> = Box::new(TestPacket {
            val: VarInt::from(42),
        });

        let test = downcast::<TestPacket>(b).expect("downcast should have succeeded");

        assert_eq!(test.val, VarInt::from(42));
    }

    #[test]
    fn downcast_err() {
        let b: Box<dyn PacketDyn> = Box::new(TestPacket2 {
            val: VarInt::from(42),
        });

        let _ = downcast::<TestPacket>(b).expect_err("downcast should have failed");
    }
}
