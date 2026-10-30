use crate::PallasScalar;
use crate::auth_proofs::AuthSigningKeys;
use crate::error::Error;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use chacha20poly1305::aead::{Aead, KeyInit};
use chacha20poly1305::{ChaCha20Poly1305, Nonce};
#[cfg(feature = "hardcoded-key")]
use hex_literal::hex;
use rand_core::CryptoRngCore;
use zeroize::Zeroize;

const VERSION: u8 = 1;
const NONCE_LEN: usize = 12;

/// Symmetric key that seals the account keys under the AEAD.
pub type DataKey = [u8; 32];

/// Supplies the data key for sealing. The hardcoded provider returns a fixed key. A KMS provider
/// generates one per seal and wraps it under a CMK. The wrapped bytes are stored in the blob and
/// handed back on unseal.
pub trait DataKeyProvider {
    /// A fresh data key plus its wrapped form to store (empty when unwrapping needs no material).
    fn fresh_data_key(&mut self) -> Result<(DataKey, Vec<u8>), Error>;
    /// Recover the data key from its wrapped form.
    fn unwrap_data_key(&self, wrapped: &[u8]) -> Result<DataKey, Error>;
}

// One key per enclave. Revisit if the enclave must hold multiple accounts.
// Temporary. Sealing key compiled into the enclave image, enabled by the `hardcoded-key` feature.
// The production build injects a KMS `DataKeyProvider` instead.
#[cfg(feature = "hardcoded-key")]
const SEALING_KEY: DataKey =
    hex!("9e1c4a772bd0638f11a55ec3902d7b46e81439ba6df20851cc973a820bd56ef9");

/// `DataKeyProvider` backed by the compiled-in `SEALING_KEY`. No wrapped material.
#[cfg(feature = "hardcoded-key")]
pub struct HardcodedKeyProvider;

#[cfg(feature = "hardcoded-key")]
impl DataKeyProvider for HardcodedKeyProvider {
    fn fresh_data_key(&mut self) -> Result<(DataKey, Vec<u8>), Error> {
        Ok((SEALING_KEY, Vec::new()))
    }

    fn unwrap_data_key(&self, _wrapped: &[u8]) -> Result<DataKey, Error> {
        Ok(SEALING_KEY)
    }
}

// Try AES-GCM later by changing this and the crate dependency.
fn cipher(data_key: &DataKey) -> ChaCha20Poly1305 {
    ChaCha20Poly1305::new_from_slice(data_key).expect("32-byte key")
}

/// Blob layout: `[version u8][wrapped_len u16 LE][wrapped][nonce 12][ciphertext+tag]`.
pub fn seal<R: CryptoRngCore>(
    provider: &mut dyn DataKeyProvider,
    keys: &AuthSigningKeys,
    rng: &mut R,
) -> Result<Vec<u8>, Error> {
    let (mut data_key, wrapped) = provider.fresh_data_key()?;
    let wrapped_len: u16 = wrapped
        .len()
        .try_into()
        .map_err(|_| Error::Device("wrapped key too large".into()))?;

    let mut plaintext =
        Vec::with_capacity(keys.sk_aff.compressed_size() + keys.sk_enc.compressed_size());
    keys.sk_aff.serialize_compressed(&mut plaintext)?;
    keys.sk_enc.serialize_compressed(&mut plaintext)?;
    let mut nonce_bytes = [0u8; NONCE_LEN];
    rng.fill_bytes(&mut nonce_bytes);
    let mut nonce = Nonce::default();
    nonce.copy_from_slice(&nonce_bytes);
    let ciphertext = cipher(&data_key)
        .encrypt(&nonce, plaintext.as_slice())
        .map_err(|_| Error::Device("seal failed".into()))?;
    data_key.zeroize();

    let mut blob = Vec::with_capacity(1 + 2 + wrapped.len() + NONCE_LEN + ciphertext.len());
    blob.push(VERSION);
    blob.extend_from_slice(&wrapped_len.to_le_bytes());
    blob.extend_from_slice(&wrapped);
    blob.extend_from_slice(&nonce_bytes);
    blob.extend_from_slice(&ciphertext);
    Ok(blob)
}

pub fn unseal(provider: &dyn DataKeyProvider, blob: &[u8]) -> Result<AuthSigningKeys, Error> {
    if blob.len() < 3 || blob[0] != VERSION {
        return Err(Error::Device("bad sealed blob".into()));
    }
    let wrapped_len = u16::from_le_bytes([blob[1], blob[2]]) as usize;
    let rest = &blob[3..];
    if rest.len() < wrapped_len + NONCE_LEN {
        return Err(Error::Device("bad sealed blob".into()));
    }
    let wrapped = &rest[..wrapped_len];
    let nonce_bytes = &rest[wrapped_len..wrapped_len + NONCE_LEN];
    let ciphertext = &rest[wrapped_len + NONCE_LEN..];

    let mut data_key = provider.unwrap_data_key(wrapped)?;
    let mut nonce = Nonce::default();
    nonce.copy_from_slice(nonce_bytes);
    let plaintext = cipher(&data_key)
        .decrypt(&nonce, ciphertext)
        .map_err(|_| Error::Device("unseal failed".into()))?;
    data_key.zeroize();

    let mut reader = &plaintext[..];
    let sk_aff = PallasScalar::deserialize_compressed(&mut reader)?;
    let sk_enc = PallasScalar::deserialize_compressed(&mut reader)?;
    // Error if extra bytes
    if !reader.is_empty() {
        return Err(Error::Device("bad sealed blob".into()));
    }
    Ok(AuthSigningKeys { sk_aff, sk_enc })
}
