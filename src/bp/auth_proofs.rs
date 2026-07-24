use rand_core::{CryptoRng, RngCore};

use polymesh_dart_auth::wrapper::{self, AuthSigningKey, AuthSigningKeys};

use super::split_types::*;
use super::*;
use crate::Error;

pub type BPAuthProofOnlySks = polymesh_dart_bp::auth_proofs::AuthProofOnlySks<PallasA>;
pub type BPAuthProofOnlySk = polymesh_dart_bp::auth_proofs::AuthProofOnlySk<PallasA>;

impl From<&AccountKeys> for AuthSigningKeys {
    fn from(keys: &AccountKeys) -> Self {
        Self {
            sk_aff: keys.acct.secret.0.0,
            sk_enc: keys.enc.secret.0.0,
        }
    }
}

impl From<&AccountKeyPair> for AuthSigningKey {
    fn from(key: &AccountKeyPair) -> Self {
        Self { sk: key.secret.0.0 }
    }
}

/// Create `AuthProofOnlySk` for fee registration and fee topup proofs (1 key).
pub fn create_fee_account_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AccountKeyPair,
    request: &FeeAccountDeviceRequest,
    sk_gen: PallasA,
) -> Result<SingleSkDeviceResponse, Error> {
    Ok(wrapper::create_fee_account_auth_proof(
        rng,
        &key.into(),
        request,
        sk_gen,
    )?)
}

/// Create `AuthProofOnlySks` for account registration and mint proofs (2 keys).
pub fn create_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AccountKeys,
    request: &RegistrationDeviceRequest,
    sk_gen: PallasA,
    sk_enc_gen: PallasA,
) -> Result<TwoSksDeviceResponse, Error> {
    Ok(wrapper::create_registration_auth_proof(
        rng,
        &keys.into(),
        request,
        sk_gen,
        sk_enc_gen,
    )?)
}

/// Create `AuthProofFeePayment` for fee payment proofs.
pub fn create_fee_payment_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AccountKeyPair,
    request: &FeePaymentDeviceRequest,
    sk_gen: PallasA,
    randomness_gen: PallasA,
    comm_re_rand_gen: PallasA,
) -> Result<FeePaymentDeviceResponse, Error> {
    Ok(wrapper::create_fee_payment_auth_proof(
        rng,
        &key.into(),
        request,
        sk_gen,
        randomness_gen,
        comm_re_rand_gen,
    )?)
}

/// Create `AuthProofAffirmation` for affirmation/claim/reversal/counter-update proofs.
pub fn create_affirmation_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AccountKeys,
    request: &AffirmationDeviceRequest,
    sk_gen: PallasA,
    enc_key_gen: PallasA,
    comm_re_rand_gen: PallasA,
    enc_gen: PallasA,
) -> Result<AffirmationDeviceResponse, Error> {
    Ok(wrapper::create_affirmation_auth_proof(
        rng,
        &keys.into(),
        request,
        sk_gen,
        enc_key_gen,
        comm_re_rand_gen,
        enc_gen,
    )?)
}
