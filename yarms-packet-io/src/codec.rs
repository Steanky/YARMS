use crate::crypto::DecryptionContext;
use crate::disjoint::{Disjoint, DisjointMut};
use crate::{
    MAX_PACKET_LEN, MAX_UNCOMPRESSED_DATA_LEN, MIN_BODY_LEN, MIN_COMPRESSED_DATA_LEN,
    MIN_PACKET_LEN, MIN_UNCOMPRESSED_DATA_LEN,
};
use alloc::vec::Vec;
use bytes::{Buf, BufMut};
use core::ptr;
use libdeflater::Decompressor;
use std::io::Read;
use yarms_protocol::types::{validate_len, VarInt, MAX_VAR_INT_BYTES};
use yarms_protocol::util::PartialRead;
use yarms_protocol::{util, validation_error, ProtocolRead};

///
/// Lightweight struct that keeps track of the current protocol state.
///
/// Doesn't supply any public-facing methods. Information about the connection can be obtained
/// through [`PacketContext`].
pub struct State<Crypt> {
    decryption_context: Option<Crypt>,
    decompress: bool,
    encryption_start: usize,
}

///
/// Struct passed to a user-provided packet handler function. Provides information about the packet,
/// including its body length and identifier.
pub struct PacketContext<'a, 'b, Buffer, Crypt>
where
    Buffer: ?Sized,
{
    packet_id: VarInt,
    body_len: VarInt,
    buf: &'a mut Buffer,
    decompressed_body: Option<&'a mut &'b [u8]>,
    state: &'a mut State<Crypt>,
}

pub enum Body<'a, 'b, Buffer>
where
    Buffer: ?Sized,
{
    Buffer(&'a mut Buffer),
    Slice(&'a mut &'b [u8]),
}

///
/// The decompressor function type, which is actually responsible for calling
/// [`Decompressor::zlib_decompress`].
///
/// This function is never user-provided, it is privately defined at [`decompress_packet`]. This
/// type only exists to make the generic bounds a bit less painful.
pub type PacketDecompressor<Buffer, Crypt, Handler> = fn(
    DecompressionArgs<'_, Buffer, Crypt, Handler>,
    &'_ mut Decompressor,
    &'_ mut [u8],
) -> crate::Result<()>;

impl<'a, 'b, Buffer, Crypt> PacketContext<'a, 'b, Buffer, Crypt>
where
    Buffer: Buf + DisjointMut + ?Sized,
    Crypt: DecryptionContext,
{
    ///
    /// The packet's identifier. This may be any valid [`VarInt`], including negative values. It is
    /// up to the packet handler to determine which identifiers are valid and which are invalid.
    pub fn packet_id(&self) -> VarInt {
        self.packet_id
    }

    ///
    /// The packet's body length. This will always be non-negative, smaller than or equal to
    /// [`MAX_UNCOMPRESSED_DATA_LEN`], and smaller than or equal to the amount of bytes available in
    /// `body`.
    pub fn body_len(&self) -> VarInt {
        self.body_len
    }

    ///
    /// Test if decompression is enabled.
    pub fn is_decompression_enabled(&self) -> bool {
        self.state.decompress
    }

    ///
    /// Test if decryption is enabled.
    pub fn is_decryption_enabled(&self) -> bool {
        self.state.decryption_context.is_some()
    }

    ///
    /// Enables encryption. Will also decrypt any remaining bytes in the buffer, if necessary.
    ///
    /// Encryption cannot be disabled once it is enabled.
    ///
    /// # Panics
    /// This method panics if encryption was already enabled.
    pub fn enable_encryption(&mut self, mut crypt: Crypt) {
        let state = &mut self.state;
        if state.decryption_context.is_some() {
            panic!("encryption was already enabled")
        }

        let start = if self.decompressed_body.is_none() {
            *self.body_len as usize
        } else {
            0
        };

        decrypt_buffer(self.buf, &mut crypt, start);
        state.decryption_context = Some(crypt);
    }

    ///
    /// Enables decompression. Future packets are expected to use the compressed format.
    ///
    /// # Panics
    /// This method panics if decompression was already enabled.
    pub fn enable_decompression(&mut self) {
        if self.state.decompress {
            panic!("decompression was already enabled")
        }

        self.state.decompress = true;
    }

    ///
    /// Gets the current packet's body. Contains the bytes needed to actually decode the packet.
    ///
    /// This may be either a direct reference to the packet byte buffer, or a mutable reference to
    /// an immutable slice, depending on whether the packet needed to be decompressed first.
    pub fn body<'c, 'z>(&'z mut self) -> Body<'c, 'b, Buffer>
    where
        'z: 'c,
        'a: 'c,
    {
        match &mut self.decompressed_body {
            None => Body::Buffer(&mut self.buf),
            Some(inner) => Body::Slice(inner),
        }
    }
}

///
/// Mostly-opaque container struct for data passed to the decompression buffer provider. Instances
/// of these are constructed and validated by [`decode_packets`]. They are immutable from the
/// perspective of a library user.
pub struct DecompressionArgs<'a, Buffer, Crypt, Handler>
where
    Buffer: ?Sized,
    Handler: ?Sized,
{
    compressed_data_len: VarInt,
    uncompressed_data_len: VarInt,
    buf: &'a mut Buffer,
    state: &'a mut State<Crypt>,
    handler: &'a mut Handler,
}

impl<'a, Buffer, Crypt, Handler> DecompressionArgs<'a, Buffer, Crypt, Handler>
where
    Buffer: ?Sized,
    Handler: ?Sized,
{
    ///
    /// The length of the compressed data. This value is derived from the packet length prefix. It
    /// is always in range `[MIN_COMPRESSED_DATA_LEN, MAX_PACKET_LEN]`.
    pub fn compressed_data_len(&self) -> VarInt {
        self.compressed_data_len
    }

    ///
    /// The length of the packet body when decompressed. This value is always in range
    /// `[1, MAX_UNCOMPRESSED_DATA_LEN]`.
    ///
    /// This value is needed to calculate the required size of the decompression buffer.
    pub fn uncompressed_data_len(&self) -> VarInt {
        self.uncompressed_data_len
    }
}

impl<Crypt> State<Crypt> {
    ///
    /// Creates a new `State`.
    pub fn new() -> Self {
        Self {
            decryption_context: None,
            decompress: false,
            encryption_start: 0,
        }
    }
}

#[cold]
#[inline(never)]
fn disjoint_read_prefix<Buffer>(buf: &mut Buffer) -> crate::Result<PartialRead>
where
    Buffer: Disjoint + ?Sized,
{
    let mut storage = [0_u8; MAX_VAR_INT_BYTES];
    let mut written = 0_usize;

    for chunk in buf.chunk_iter() {
        let len = core::cmp::min(MAX_VAR_INT_BYTES - written, chunk.len());
        storage[written..written + len].copy_from_slice(&chunk[..len]);

        written += len;

        if written < MAX_VAR_INT_BYTES {
            match util::var_int_partial_read(&storage[..]) {
                PartialRead::NeedsBytes => continue,
                done => return Ok(done),
            }
        } else {
            let (bytes, var_int) = util::var_int_read(&storage)?;
            return Ok(PartialRead::Done(bytes, var_int));
        }
    }

    Ok(PartialRead::NeedsBytes)
}

#[inline]
fn read_prefix<Buffer>(buf: &mut Buffer) -> crate::Result<PartialRead>
where
    Buffer: Buf + Disjoint + ?Sized,
{
    let chunk = buf.chunk();

    if chunk.len() >= MAX_VAR_INT_BYTES {
        let (var_int_len, var_int) =
            util::var_int_read(&chunk[..MAX_VAR_INT_BYTES].try_into().unwrap())?;

        Ok(PartialRead::Done(var_int_len, var_int))
    } else if Buffer::contiguous() || chunk.len() == buf.remaining() {
        Ok(util::var_int_partial_read(chunk))
    } else {
        // branch should be omitted entirely for contiguous buffers!
        // (and rarely hit for even non-contiguous ones)
        disjoint_read_prefix(buf)
    }
}

///
/// Helper utilities to make calling [`crate::codec::decode_packets`] a bit less painful.
pub mod helper {
    use crate::codec::{DecompressionArgs, PacketDecompressor};
    use alloc::vec::Vec;
    use core::cell::RefCell;

    ///
    /// Grows `vec` by zero-extending it, if its length is less than `target`.
    #[inline]
    fn prepare_buffer(vec: &mut Vec<u8>, target: usize) {
        let current_len = vec.len();

        if current_len < target {
            vec.resize(target, 0);
        }
    }

    ///
    /// A non-Sync decompression function, suitable for passing to [`crate::codec::decode_packets`].
    /// Works in a `no_std` environment.
    ///
    /// The same decompression function may be used across multiple active connections and will
    /// re-use the same buffer between them (though it cannot be shared across threads).
    pub fn local_decompressor<Buffer, Crypt, Handler>() -> impl Fn(
        DecompressionArgs<'_, Buffer, Crypt, Handler>,
        PacketDecompressor<Buffer, Crypt, Handler>,
    ) -> crate::Result<()>
           + Send {
        let mut local_buffer = RefCell::new(Vec::new());
        let mut local_decompressor = RefCell::new(libdeflater::Decompressor::new());

        move |args, func| {
            let target = *args.uncompressed_data_len() as usize;

            let mut buffer_guard = local_buffer.borrow_mut();
            let mut decompressor_guard = local_decompressor.borrow_mut();

            prepare_buffer(&mut *buffer_guard, target);
            func(args, &mut *decompressor_guard, &mut buffer_guard[..target])
        }
    }

    #[cfg(feature = "std")]
    ///
    /// A decompressor function that implements Sync, but requires the `std` feature to be enabled.
    ///
    /// Uses thread-local buffers and decompressors. This avoids (most) synchronization processing
    /// overhead, at the cost of additional memory usage: a unique buffer (and decompressor) is
    /// maintained per-thread, and dropped when the thread terminates.
    pub fn thread_local_decompressor<Buffer, Crypt, Handler>() -> impl Fn(
        DecompressionArgs<'_, Buffer, Crypt, Handler>,
        PacketDecompressor<Buffer, Crypt, Handler>,
    ) -> crate::Result<()>
           + Send
           + Sync {
        std::thread_local! {
            static BUFFER: RefCell<Vec<u8>> = RefCell::new(Vec::new());
            static DECOMPRESS: RefCell<libdeflater::Decompressor> = RefCell::new(libdeflater::Decompressor::new());
        }

        |args, func| {
            BUFFER.with_borrow_mut(|buffer| {
                let target_length = *args.uncompressed_data_len() as usize;
                prepare_buffer(buffer, target_length);

                DECOMPRESS.with_borrow_mut(|decompressor| {
                    func(args, decompressor, &mut buffer[..target_length])
                })
            })
        }
    }
}

fn decrypt_disjoint<Buffer, Crypt>(buf: &mut Buffer, crypt: &mut Crypt, start: usize)
where
    Buffer: DisjointMut + ?Sized,
    Crypt: DecryptionContext,
{
    let mut iter = buf.chunk_iter_mut();

    let mut pos = 0_usize;
    for chunk in &mut iter {
        let (next, overflow) = pos.overflowing_add(chunk.len());

        if !overflow && next <= start {
            pos = next;
        } else {
            crypt.decrypt_slice(&mut chunk[start - pos..]);
            break;
        }
    }

    // decrypt the rest of the buffer
    for chunk in iter {
        crypt.decrypt_slice(chunk);
    }
}

#[inline]
fn decrypt_buffer<Buffer, Crypt>(buf: &mut Buffer, crypt: &mut Crypt, start: usize)
where
    Buffer: DisjointMut + ?Sized,
    Crypt: DecryptionContext,
{
    // for contiguous buffers, a single call to `decrypt_slice` suffices
    if Buffer::contiguous() {
        let chunk = buf.chunk_iter_mut().next().unwrap();
        crypt.decrypt_slice(&mut chunk[start..]);
    } else {
        decrypt_disjoint(buf, crypt, start)
    }
}

#[inline(never)]
#[cold]
fn packet_err<T>(string: &'static str) -> crate::Result<T> {
    validation_error!(Read string)
}

///
/// Decodes as many packets as possible from the provided buffer. Advances it by the amount of data
/// read.
///
/// The implementation is highly flexible, but as a consequence this function must exist deep within
/// the pits of generic hell. To lessen the pain somewhat, we provide the [`helper`] module, which
/// includes common implementations of functions that'd be passed to `decompress`.
///
/// N.B. Prior knowledge of the Minecraft protocol w.r.t. the packet format is assumed. See
/// https://minecraft.wiki/w/Java_Edition_protocol#Packet_format for a complete description of this.
///
/// # Decompressor functions
/// This function requires a "decompress function", provided through the `decompress` parameter.
/// This is responsible for providing a [`Decompressor`] instance and a buffer to which the packet
/// is written. Examples are provided in [`helper`].
///
/// Note that the decompressor function does _not_, itself, perform any decompression - that's done
/// internally by this library. The decompressor function only serves to provide the actual,
/// internal logic with an appropriately-sized buffer and a decompressor.
///
/// # Packet handlers
/// In addition to the aforementioned decompressor function, this method takes a "packet handler"
/// (the `handler` parameter). This is a user-defined callback that is invoked every time this
/// function encounters a packet prefix, in other words, once per packet.
///
/// The callback is provided with a [`PacketContext`] instance, which provides all information
/// necessary to figure out how to decode the packet.
///
/// # Errors
/// This function returns an error if:
/// * It encounters bad length prefixes (negative, too small, or too large)
/// * It encounters invalid compressed packets:
///     * Compressed packet is not valid ZLIB data
///     * Data length is too small or too large
///     * Packet decompresses into a larger or smaller byte sequence than expected
/// * The packet handler function returns Err
///
/// When an error is returned, the connection should _generally_ be closed, as it's often not
/// possible to recover it. In particular, re-using the [`State`] object that was passed to a
/// previous invocation that returned an error allows this function to behave in an unspecified
/// manner: it may panic, spuriously error, and generally do whatever it wants as long as it does
/// not produce undefined behavior. This _includes_ errors returned as a result of the
/// caller-defined packet handler yielding [`Err`]!
///
/// # Panics
/// This function should not panic unless re-using a [`State`] object that was passed to a previous
/// invocation that returned [`Err`], or if a memory allocation fails. Panicking in other
/// circumstances indicates a bug.
///
/// # Example
///
/// ```rust
/// use bytes::{Buf, BufMut};
/// use yarms_packet::Packet;
/// use yarms_packet_io::codec::{decode_packets, Body, State};
/// use yarms_packet_io::crypto::AESCFB8DecryptionContext;
/// use yarms_packet_io::disjoint::SliceBuf;
/// use yarms_protocol::{ProtocolRead, ProtocolWrite};
/// use yarms_protocol::types::{VarInt, VarLong};
///
/// use yarms_protocol::util::PartialRead;
///
/// // very simple packet definition we use for testing
/// struct ExamplePacket {
///     value: VarLong
/// }
///
/// // explicit packet impl: the proc macro `yarms-derive` can be used to generate code
/// // like this but, we don't do that here because it's not a dependency of this crate
/// impl Packet for ExamplePacket {
///     fn protocol_id() -> VarInt
///     where
///         Self: Sized
///     {
///         VarInt::from(0)
///     }
///
///     fn clientbound() -> bool {
///         true
///     }
///
///     fn resource() -> &'static str {
///         "example"
///     }
///
///     fn read_body<B>(buf: &mut B, end_remaining: usize) -> yarms_packet::Result<Self>
///     where
///         B: Buf + ?Sized
///     {
///         Ok(Self {
///             value: VarLong::read_from(buf, end_remaining)?
///         })
///     }
///
///     fn write_body<B>(&self, buf: &mut B) -> usize
///     where
///         B: BufMut + ?Sized
///     {
///         self.value.write_to(buf)
///     }
///
///     fn len(&self) -> usize {
///         self.value.len()
///     }
/// }
///
/// // first 3 bytes are an encoded ExamplePacket
/// // last byte is the length prefix of the next packet, which is incomplete
/// let mut packet_buffer: Vec<u8> = vec![0x02, 0x00, 0x2A, 0x2A];
///
/// // handles encryption (which this example doesn't use) and decompression state (likewise)
/// // an actual decoding routine would use the same `State` repeatedly in a loop, periodically
/// // filling up the buffer with as many bytes as available/requested
/// let mut state: State<AESCFB8DecryptionContext> = State::new();
///
/// // performs packet decompression... but our packet isn't compressed so this isn't used,
/// // at least in this example
/// let decompressor = yarms_packet_io::codec::helper::local_decompressor();
///
/// // count how many packets we get to read from the buffer
/// let mut packet_count = 0;
///
/// // SliceBuf is needed because it implements both Buf and DisjointMut
/// // if we tried to just use `vec` here we'd run into problems as it does not implement Buf
/// let result = decode_packets(&mut SliceBuf(&mut packet_buffer), &mut state, |mut packet_context| {
///     let body_len = *packet_context.body_len() as usize;
///
///     let packet = match packet_context.body() {
///         // the packet body is stored directly in our buffer (SliceBuf above)
///         // body_len should never be greater than buf.remaining
///         Body::Buffer(buf) => ExamplePacket::read_body(buf, buf.remaining() - body_len)?,
///
///         // the packet body is stored in a mutable reference to an immutable slice
///         // this is primarily used when decompressing a packet, which doesn't happen in this example
///         Body::Slice(slice) => ExamplePacket::read_body(slice, 0)?,
///     };
///
///     packet_count += 1;
///
///     assert_eq!(packet_context.packet_id(), VarInt::from(0), "packet_id should have been zero");
///     assert_eq!(packet_context.body_len(), VarInt::from(1), "body_len should have been 1");
///     assert_eq!(packet.value, VarLong::from(42), "packet.value should have been 42");
///
///     Ok(())
/// }, decompressor);
///
/// // we're out of bytes (our buffer only had 4) so the decoder asks for more:
/// // specifically, it is indicating that the length prefix of the incomplete packet is 42!
/// match result {
///     Ok(read) => assert_eq!(PartialRead::Done(1, VarInt::from(42_i32)), read),
///     _ => panic!("unexpected result"),
/// }
///
/// // should have only read 1 packet
/// assert_eq!(packet_count, 1_i32);
/// ```
pub fn decode_packets<Buffer, Crypt, Handler, Decompress>(
    mut buf: &mut Buffer,
    mut state: &mut State<Crypt>,
    mut handler: Handler,
    mut decompress: Decompress,
) -> crate::Result<PartialRead>
where
    Buffer: Buf + DisjointMut + ?Sized,
    Crypt: DecryptionContext,
    Handler: FnMut(PacketContext<'_, '_, Buffer, Crypt>) -> crate::Result<()>,
    Decompress: FnMut(
        DecompressionArgs<'_, Buffer, Crypt, Handler>,
        PacketDecompressor<Buffer, Crypt, Handler>,
    ) -> crate::Result<()>,
{
    // static error messages
    static INVALID_PACKET_LEN_MSG: &str = "invalid packet length";
    static INVALID_DATA_LEN_MSG: &str = "invalid compressed data length";

    // decrypt all the remaining buffer, if enabled
    if let Some(crypt) = &mut state.decryption_context {
        decrypt_buffer(buf, crypt, state.encryption_start);
    }

    loop {
        // this does NOT advance the buffer yet!
        let (packet_len_len, packet_len) = match read_prefix(buf)? {
            PartialRead::Done(packet_len_len, packet_len) => (packet_len_len, packet_len),
            needs_bytes => {
                // remaining bytes should have already been decrypted
                state.encryption_start = buf.remaining();

                return Ok(needs_bytes);
            }
        };

        // packet length of 1 is possible, but 0 is always invalid
        validate_len(*packet_len, MIN_PACKET_LEN, MAX_PACKET_LEN)?;

        let rem = buf.remaining();

        // packet_len_len <= rem: we actually saw `packet_len_len` bytes in the buffer
        if (*packet_len as usize) > rem - packet_len_len {
            state.encryption_start = rem;

            // we don't have enough bytes to read the rest of this packet
            return Ok(PartialRead::Done(packet_len_len, packet_len));
        }

        // should never panic: `read_prefix` found at least this many bytes in the buffer
        buf.advance(packet_len_len);

        // check if we should expect the alternate packet format
        if !state.decompress {
            let (packet_id_len, packet_id) = util::var_int_read_buf(buf)?;

            let body_len = VarInt::from(*packet_len - (packet_id_len as i32));
            if *body_len < MIN_BODY_LEN {
                return packet_err(INVALID_PACKET_LEN_MSG);
            }

            handler(PacketContext {
                packet_id,
                body_len,
                buf: &mut buf,
                decompressed_body: None,
                state: &mut state,
            })?;

            continue;
        }

        let (uncompressed_data_len_len, uncompressed_data_len) = util::var_int_read_buf(buf)?;
        if *uncompressed_data_len == 0 {
            let (packet_id_len, packet_id) = util::var_int_read_buf(buf)?;

            let body_len = VarInt::from(
                *packet_len - (packet_id_len as i32) - (uncompressed_data_len_len as i32),
            );

            if *body_len < MIN_BODY_LEN {
                return packet_err(INVALID_PACKET_LEN_MSG);
            }

            handler(PacketContext {
                packet_id,
                body_len,
                buf: &mut buf,
                decompressed_body: None,
                state: &mut state,
            })?;

            continue;
        }

        validate_len(
            *uncompressed_data_len,
            MIN_UNCOMPRESSED_DATA_LEN,
            MAX_UNCOMPRESSED_DATA_LEN,
        )?;
        let compressed_data_len = VarInt::from(*packet_len - (uncompressed_data_len_len as i32));

        // `compressed_data_len` may be negative if the client lies about its length
        // this will be caught here before we try to decompress anything
        if *compressed_data_len < MIN_COMPRESSED_DATA_LEN {
            return packet_err(INVALID_DATA_LEN_MSG);
        }

        let args = DecompressionArgs {
            compressed_data_len,
            uncompressed_data_len,
            buf,
            state,
            handler: &mut handler,
        };

        decompress(args, decompress_packet::<Buffer, Crypt, Handler>)?
    }
}

fn decompress(
    decompressor: &mut Decompressor,
    data_in: &[u8],
    data_out: &mut [u8],
) -> crate::Result<()> {
    let written = decompressor.zlib_decompress(data_in, data_out)?;

    if written != data_out.len() {
        return packet_err("data length and actual decompressed length did not match");
    }

    Ok(())
}

#[cold]
#[inline(never)]
fn decompress_disjoint<Buffer>(
    compressed_len: usize,
    buf: &mut Buffer,
    decompressor: &mut Decompressor,
    buf_out: &mut [u8],
) -> crate::Result<()>
where
    Buffer: Buf + ?Sized,
{
    decompress(decompressor, &buf_to_vec(buf, compressed_len)[..], buf_out)
}

fn decompress_packet<Buffer, Crypt, Handler>(
    args: DecompressionArgs<'_, Buffer, Crypt, Handler>,
    decompressor: &mut Decompressor,
    mut buf_out: &'_ mut [u8],
) -> crate::Result<()>
where
    Buffer: Buf + DisjointMut + ?Sized,
    Crypt: DecryptionContext,
    Handler: FnMut(PacketContext<'_, '_, Buffer, Crypt>) -> crate::Result<()>,
{
    let DecompressionArgs {
        compressed_data_len,
        mut buf,
        state,
        handler,
        ..
    } = args;

    // cast should be lossless due to validation done in `decode_packets`
    let compressed_length = *compressed_data_len as usize;
    let chunk = buf.chunk();

    // as per the contract of `contiguous`, when true, chunk.len() == chunk.remaining()
    if Buffer::contiguous() || compressed_length <= chunk.len() {
        decompress(decompressor, &chunk[..compressed_length], buf_out)?;

        // advances the buffer to the beginning of the next packet
        buf.advance(compressed_length);
    } else {
        // cold path: usually we have everything in one chunk
        // no need to advance `buf` after, the function does it for us
        decompress_disjoint(compressed_length, buf, decompressor, buf_out)?;
    }

    let buf_out_ref = &mut &*buf_out;
    let packet_id = VarInt::read_from(buf_out_ref, 0)?;

    handler(PacketContext {
        packet_id,
        body_len: VarInt::from(buf_out.len() as i32),
        buf,
        decompressed_body: Some(buf_out_ref),
        state,
    })?;

    Ok(())
}

///
/// Copies `target` bytes from `buf` into a newly-allocated [`Vec`]. Used when it isn't possible to
/// decompress directly from the network buffer due to e.g. a non-contiguous buffer, and needing
/// a contiguous slice to decompress from.
///
/// This just copies the data in the buffer by repeatedly calling [`Buf::chunk`] and advancing. When
/// this function returns, `buf` will have advanced by a number of bytes equal to the length of the
/// returned vector.
///
/// Since this re-allocates and copies data, this function should not be used unless necessary. It
/// is expected to be called infrequently.
///
/// It is assumed that `B` is a potentially-non-contiguous buffer.
///
/// # Panics
/// This function panics if `target` is greater than `isize::MAX`, if `target` bytes cannot be
/// allocated, or if [`Buf::remaining`] is smaller than `target`.
#[inline]
fn buf_to_vec<B>(buf: &mut B, target: usize) -> Vec<u8>
where
    B: Buf + ?Sized,
{
    // target must not exceed isize::MAX because otherwise we would overflow isize in the loop below
    assert!(
        target <= (isize::MAX as usize),
        "`target` was greater than isize::MAX"
    );

    // N.B: this assertion is a "courtesy" as it fails when the buffer doesn't have enough bytes
    // however, because `Buf` is safe to implement, we must not rely on its contract for safety!
    // currently, a `Buf` that reports the wrong value for `remaining` will cause this function
    // to loop infinitely and never return, but will not lead to UB
    assert!(
        target <= buf.remaining(),
        "`buf` didn't have enough bytes left"
    );

    let mut vec = Vec::<u8>::with_capacity(target);
    let mut vec_offset = 0_isize;

    let mut remaining = target;
    loop {
        if remaining == 0 {
            // SAFETY:
            // - `remaining` is 0, so we wrote exactly `target` bytes
            unsafe {
                vec.set_len(target);
            }

            return vec;
        }

        let chunk = buf.chunk();
        let len = core::cmp::min(chunk.len(), remaining);

        // SAFETY:
        // - `src` and `dst` are both non-null, aligned, and non-overlapping
        // - T is u8, which is Copy
        // - we can't write outside the Vec's capacity
        // - `len` is <= the length of `chunk`
        unsafe {
            ptr::copy_nonoverlapping(chunk.as_ptr(), vec.as_mut_ptr().offset(vec_offset), len);
        }

        buf.advance(len);

        // `remaining` is always less than or equal to isize::MAX, because of the assertion above
        // cast can't be lossy because len is always smaller than or equal to `remaining`
        // `vec_offset` can't overflow because we never increase it by more than `target` bytes
        vec_offset += len as isize;

        // can't underflow due to the `min` call above: `len` <= `remaining`
        remaining -= len;
    }
}
