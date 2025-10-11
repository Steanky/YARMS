use alloc::vec;
use alloc::vec::Vec;

///
/// Trait for a very simple mutable buffer of bytes. Implementations generally need to allocate
/// memory.
pub trait Buffer {
    ///
    /// Provide at least `min` bytes to the caller. The contents of the returned slice are not
    /// specified (though they will be initialized and thus safe, if not meaningful, to access). In
    /// other words, the slice is free to contain "garbage" data from previous accesses, but reading
    /// that data is entirely safe in the sense that it is not undefined behavior.
    ///
    /// If `exact` is true, the returned buffer will be precisely `min` bytes. If `exact` is false,
    /// the buffer length may be any value so long as it is larger than or equal to (but not
    /// smaller than) `min`.
    ///
    /// If the contents of the buffer are uninitialized, this method will initialize them.
    fn prepare(&mut self, min: usize, exact: bool) -> &mut [u8];

    ///
    /// If initialized, returns an immutable reference to the entire buffer. Otherwise, returns
    /// `None`.
    ///
    /// This can be used to access data that was previously written into the buffer.
    fn all(&self) -> Option<&[u8]>;

    #[cfg(feature = "std")]
    ///
    /// Returns a writer that writes into this buffer.
    ///
    /// The writer will start writing at the beginning of the buffer, initializing it if required.
    /// That is, the writer will overwrite the contents of this buffer, starting from the beginning.
    fn writer(&mut self) -> impl std::io::Write;
}

///
/// [`Buffer`] backed by an `Option<Vec<u8>>`.
///
/// This implementation will only grow its buffer.
pub struct VecBuf {
    storage: Option<Vec<u8>>,
}

impl Buffer for VecBuf {
    fn prepare(&mut self, min: usize, exact: bool) -> &mut [u8] {
        match self.storage {
            None => self.storage.insert(vec![0_u8; min]),
            Some(ref mut vec) => {
                if vec.len() < min {
                    vec.resize(min, 0);
                }

                if exact {
                    &mut vec[..min]
                } else {
                    vec
                }
            }
        }
    }

    fn all(&self) -> Option<&[u8]> {
        self.storage.as_deref()
    }

    #[cfg(feature = "std")]
    fn writer(&mut self) -> impl std::io::Write {
        std::io::Cursor::new(self.storage.get_or_insert_with(Vec::new))
    }
}

impl VecBuf {
    ///
    /// Creates a new `VecBuf`. The storage will be lazily initialized (so this is effectively a
    /// no-op).
    #[must_use]
    pub const fn new() -> VecBuf {
        VecBuf { storage: None }
    }
}

impl Default for VecBuf {
    fn default() -> Self {
        Self::new()
    }
}
