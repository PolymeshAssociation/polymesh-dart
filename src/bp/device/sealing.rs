use crate::PallasScalar;
use crate::auth_proofs::AuthSigningKeys;
use crate::error::Error;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use chacha20poly1305::aead::{Aead, KeyInit};
use chacha20poly1305::{ChaCha20Poly1305, Nonce};
use hex_literal::hex;
use rand_core::CryptoRngCore;

// One key per enclave. Revisit if the enclave must hold multiple accounts.

// Sealing key put into the enclave image, just for PoC. Replace with a KMS-derived key later.
const SEALING_KEY: [u8; 32] =
    hex!("9e1c4a772bd0638f11a55ec3902d7b46e81439ba6df20851cc973a820bd56ef9");
const VERSION: u8 = 1;
const NONCE_LEN: usize = 12;

// Try AES-GCM later by changing this and the crate dependency.
fn cipher() -> ChaCha20Poly1305 {
    ChaCha20Poly1305::new_from_slice(&SEALING_KEY).expect("32-byte key")
}

/// Blob layout: `[version u8][nonce 12][ciphertext+tag]`.
pub fn seal<R: CryptoRngCore>(keys: &AuthSigningKeys, rng: &mut R) -> Result<Vec<u8>, Error> {
    let mut plaintext =
        Vec::with_capacity(keys.sk_aff.compressed_size() + keys.sk_enc.compressed_size());
    keys.sk_aff.serialize_compressed(&mut plaintext)?;
    keys.sk_enc.serialize_compressed(&mut plaintext)?;
    let mut nonce_bytes = [0u8; NONCE_LEN];
    rng.fill_bytes(&mut nonce_bytes);
    let mut nonce = Nonce::default();
    nonce.copy_from_slice(&nonce_bytes);
    let ciphertext = cipher()
        .encrypt(&nonce, plaintext.as_slice())
        .map_err(|_| Error::Device("seal failed".into()))?;
    let mut blob = Vec::with_capacity(1 + NONCE_LEN + ciphertext.len());
    blob.push(VERSION);
    blob.extend_from_slice(&nonce_bytes);
    blob.extend_from_slice(&ciphertext);
    Ok(blob)
}

pub fn unseal(blob: &[u8]) -> Result<AuthSigningKeys, Error> {
    if blob.len() < 1 + NONCE_LEN || blob[0] != VERSION {
        return Err(Error::Device("bad sealed blob".into()));
    }
    let mut nonce = Nonce::default();
    nonce.copy_from_slice(&blob[1..1 + NONCE_LEN]);
    let plaintext = cipher()
        .decrypt(&nonce, &blob[1 + NONCE_LEN..])
        .map_err(|_| Error::Device("unseal failed".into()))?;
    let mut reader = &plaintext[..];
    let sk_aff = PallasScalar::deserialize_compressed(&mut reader)?;
    let sk_enc = PallasScalar::deserialize_compressed(&mut reader)?;
    Ok(AuthSigningKeys { sk_aff, sk_enc })
}
