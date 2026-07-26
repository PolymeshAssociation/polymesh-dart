use ark_std::vec::Vec;
use codec::{Decode, Encode};
use rand_core::{CryptoRng, RngCore};

use polymesh_dart_bp::auth_proofs::keys::{
    AudMedRegProof, DecKey, EncKey, InvestorKeyRegProof, SigKey, VerKey,
};

use super::{CompressedAffine, PallasA, WrappedCanonical};
use crate::Error;

pub type BPInvestorKeyRegProof = InvestorKeyRegProof<PallasA>;
pub type BPAudMedRegProof = AudMedRegProof<PallasA>;

/// Device response for account (investor) key registration.
#[derive(Clone, Encode, Decode)]
pub struct KeyRegistrationDeviceResponse {
    /// `(account_pk, encryption_pk)` per account, in the order the proof was created.
    pub accounts: Vec<(CompressedAffine, CompressedAffine)>,
    pub inner: WrappedCanonical<BPInvestorKeyRegProof>,
}

/// Device response for auditor/mediator encryption-key registration.
#[derive(Clone, Encode, Decode)]
pub struct EncryptionKeyRegistrationDeviceResponse {
    /// Encryption public keys, in the order the proof was created.
    pub keys: Vec<CompressedAffine>,
    pub inner: WrappedCanonical<BPAudMedRegProof>,
}

/// Device side of account registration: prove knowledge of the account signing and encryption
/// secret keys. `identity` is the registration context (used as the proof nonce).
pub fn create_key_registration_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &[(
        (SigKey<PallasA>, VerKey<PallasA>),
        (DecKey<PallasA>, EncKey<PallasA>),
    )],
    identity: &[u8],
    sig_key_gen: PallasA,
    enc_key_gen: PallasA,
) -> Result<KeyRegistrationDeviceResponse, Error> {
    let mut accounts = Vec::with_capacity(keys.len());
    let mut proof_keys = Vec::with_capacity(keys.len());

    for ((sig, ver), (dec, enc)) in keys {
        accounts.push((
            CompressedAffine::try_from(ver.0)?,
            CompressedAffine::try_from(enc.0)?,
        ));
        proof_keys.push(((ver.0, sig.0), (enc.0, dec.0)));
    }

    let proof = InvestorKeyRegProof::new(rng, proof_keys, identity, sig_key_gen, enc_key_gen)?;

    Ok(KeyRegistrationDeviceResponse {
        accounts,
        inner: WrappedCanonical::wrap(&proof)?,
    })
}

/// Device side of auditor/mediator encryption-key registration: prove knowledge of the encryption
/// secret keys.
pub fn create_encryption_key_registration_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &[(DecKey<PallasA>, EncKey<PallasA>)],
    identity: &[u8],
    enc_key_gen: PallasA,
) -> Result<EncryptionKeyRegistrationDeviceResponse, Error> {
    let mut enc_keys = Vec::with_capacity(keys.len());
    let mut proof_keys = Vec::with_capacity(keys.len());

    for (dec, enc) in keys {
        enc_keys.push(CompressedAffine::try_from(enc.0)?);
        proof_keys.push((enc.0, dec.0));
    }

    let proof = AudMedRegProof::new(rng, proof_keys, identity, enc_key_gen)?;

    Ok(EncryptionKeyRegistrationDeviceResponse {
        keys: enc_keys,
        inner: WrappedCanonical::wrap(&proof)?,
    })
}
