use crate::{util, validation_error};
use crate::{ProtocolRead, ProtocolWrite, Result};
use yarms_identifier::Identifier;
use yarms_identifier::IdentifierParseError;

impl From<IdentifierParseError> for crate::ReadError {
    fn from(value: IdentifierParseError) -> Self {
        match value {
            IdentifierParseError::InvalidNamespace => validation_error!(*Read "invalid namespace"),
            IdentifierParseError::InvalidValue => validation_error!(*Read "invalid value"),
            IdentifierParseError::TooLong => validation_error!(*Read "identifier too long"),
        }
    }
}

impl ProtocolRead for Identifier {
    type Output = Self;

    fn read_from<B: bytes::Buf + ?Sized>(read: &mut B, _: usize) -> Result<Self::Output> {
        Ok(Identifier::parse(str::read_from(read, 0)?)?)
    }
}

impl ProtocolWrite for Identifier {
    fn write_to<B: bytes::BufMut + ?Sized>(&self, write: &mut B) -> usize {
        // note for any curious parties or my future self:
        // the vanilla client appears to always include the minecraft namespace explicitly
        // this is not strictly necessary as the namespace is assumed to be `minecraft`
        // however, it's best to mimic vanilla where reasonable, and so we do that here.

        let namespace = self.namespace();
        let value = self.value();

        let len = self.len();

        // cast non-lossy due to invariants upheld by Identifier
        util::var_int_write_buf(len as i32, write);

        write.put_slice(&namespace.as_bytes());
        write.put_u8(yarms_identifier::NAMESPACE_VALUE_SEPARATOR as u8);
        write.put_slice(&value.as_bytes());

        len
    }

    fn len(&self) -> usize {
        // protected from overflow here due to the invariants of Identifier
        util::prefixed_len(self.namespace().len() + self.value().len() + 1)
    }
}
