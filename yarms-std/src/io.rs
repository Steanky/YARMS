///
/// Wrapper for `std::io::SeekFrom`.
pub enum SeekFrom {
    ///
    /// Seeks from the start of the data.
    Start(u64),

    ///
    /// Seeks relative to the end of the data.
    End(i64),

    ///
    /// Seeks relative to the current position.
    Current(i64),
}

///
/// Wrapper for `std::io::Error`.
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    #[cfg(feature = "std")]
    ///
    /// A `std::io::Error` occurred.
    Io(std::io::Error),

    ///
    /// Generic error variant intended for `no_std` implementations.
    Generic,
}

#[cfg(feature = "std")]
impl From<std::io::SeekFrom> for SeekFrom {
    fn from(value: std::io::SeekFrom) -> Self {
        match value {
            std::io::SeekFrom::Start(start) => SeekFrom::Start(start),
            std::io::SeekFrom::End(end) => SeekFrom::End(end),
            std::io::SeekFrom::Current(current) => SeekFrom::Current(current),
        }
    }
}

#[cfg(feature = "std")]
impl From<SeekFrom> for std::io::SeekFrom {
    fn from(value: SeekFrom) -> Self {
        match value {
            SeekFrom::Start(start) => std::io::SeekFrom::Start(start),
            SeekFrom::End(end) => std::io::SeekFrom::End(end),
            SeekFrom::Current(current) => std::io::SeekFrom::Current(current),
        }
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            #[cfg(feature = "std")]
            Error::Io(error) => error.fmt(f),
            Error::Generic => write!(f, "generic IO error"),
        }
    }
}

impl core::error::Error for Error {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            #[cfg(feature = "std")]
            Error::Io(error) => Some(error),
            Error::Generic => None,
        }
    }
}

#[cfg(feature = "std")]
impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Error::Io(value)
    }
}

#[cfg(feature = "std")]
impl From<Error> for std::io::Error {
    fn from(value: Error) -> Self {
        match value {
            Error::Io(error) => error,
            Error::Generic => std::io::ErrorKind::Other.into(),
        }
    }
}

///
/// Equivalent of `std::io::Result`.
pub type Result<T> = core::result::Result<T, Error>;

///
/// A simpler version of `std::io::Seek`.
pub trait Seek {
    ///
    /// See `std::io::Seek::seek`.
    ///
    /// # Errors
    /// Returns `Err` if an IO error occurs.
    fn seek(&mut self, pos: SeekFrom) -> Result<u64>;
}

///
/// A simpler version of `std::io::Read`.
pub trait Read {
    ///
    /// See `std::io::Read::read`.
    ///
    /// # Errors
    /// Returns `Err` if an IO error occurs.
    fn read(&mut self, buf: &mut [u8]) -> Result<usize>;

    ///
    /// See `std::io::Read::read_exact`.
    ///
    /// # Errors
    /// Returns `Err` if an IO error occurs.
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()>;
}

///
/// A simpler version of `std::io::Write`.
pub trait Write {
    ///
    /// See `std::io::Write::write`.
    ///
    /// # Errors
    /// Returns `Err` if an IO error occurs.
    fn write(&mut self, buf: &[u8]) -> Result<usize>;

    ///
    /// See `std::io::Write::write_all`.
    ///
    /// # Errors
    /// Returns `Err` if an IO error occurs.
    fn write_all(&mut self, buf: &[u8]) -> Result<()>;
}

#[cfg(feature = "std")]
#[repr(transparent)]
///
/// Generic wrapper struct that can contain a `std::io::{Seek, Read, Write}`.
pub struct IOWrapper<T>(pub T);

#[cfg(feature = "std")]
impl<T> Seek for IOWrapper<T>
where
    T: std::io::Seek,
{
    #[inline]
    fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        self.0.seek(pos.into()).map_err(Into::into)
    }
}

#[cfg(feature = "std")]
impl<T> Read for IOWrapper<T>
where
    T: std::io::Read,
{
    #[inline]
    fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        self.0.read(buf).map_err(Into::into)
    }

    #[inline]
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        self.0.read_exact(buf).map_err(Into::into)
    }
}

#[cfg(feature = "std")]
impl<T> Write for IOWrapper<T>
where
    T: std::io::Write,
{
    #[inline]
    fn write(&mut self, buf: &[u8]) -> Result<usize> {
        self.0.write(buf).map_err(Into::into)
    }

    #[inline]
    fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        self.0.write_all(buf).map_err(Into::into)
    }
}
