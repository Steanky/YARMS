use aes::cipher::generic_array::GenericArray;
use cfb8::cipher::{BlockDecryptMut, BlockEncryptMut};

///
/// Type alias for [`cfb8::Encryptor`] of type [`aes::Aes128`].
pub type Encryptor = cfb8::Encryptor<aes::Aes128>;

///
/// Type alias for [`cfb8::Decryptor`] of type [`aes::Aes128`].
pub type Decryptor = cfb8::Decryptor<aes::Aes128>;

///
/// Decryptor that operates on an in-place slice of raw bytes.
pub trait DecryptionContext {
    ///
    /// Decrypts a mutable slice of bytes in-place.
    fn decrypt_slice(&mut self, slice: &mut [u8]);
}

///
/// Encryptor that operates on an in-place slice of raw bytes.
pub trait EncryptionContext {
    ///
    /// Encrypts a mutable slice of bytes in-place.
    fn encrypt_slice(&mut self, slice: &mut [u8]);
}

///
/// Standard decryption context for Minecraft, using AES/CFB8 decryption.
pub struct AESCFB8DecryptionContext(Decryptor);

///
/// Standard encryption context for Minecraft, using AES/CFB8 encryption.
pub struct AESCFB8EncryptionContext(Encryptor);

impl DecryptionContext for AESCFB8DecryptionContext {
    fn decrypt_slice(&mut self, slice: &mut [u8]) {
        for chunk in slice.chunks_exact_mut(1) {
            self.0
                .decrypt_block_mut(GenericArray::from_mut_slice(chunk));
        }
    }
}
impl EncryptionContext for AESCFB8EncryptionContext {
    fn encrypt_slice(&mut self, slice: &mut [u8]) {
        for chunk in slice.chunks_exact_mut(1) {
            self.0
                .encrypt_block_mut(GenericArray::from_mut_slice(chunk));
        }
    }
}
