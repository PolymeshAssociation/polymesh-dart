use ark_std::vec::Vec;
use rand_core::{CryptoRng, RngCore};

use polymesh_dart_bp::auth_proofs::{
    self, account::AuthProofAffirmation as BPAuthProofAffirmation,
    fee_account::AuthProofFeePayment as BPAuthProofFeePayment,
};

use super::split_types::*;
use super::*;
use crate::Error;

pub type BPAuthProofOnlySks = auth_proofs::AuthProofOnlySks<PallasA>;
pub type BPAuthProofOnlySk = auth_proofs::AuthProofOnlySk<PallasA>;

/// Construct `ledger_nonce = challenge_h_bytes || nonce`.
fn ledger_nonce(challenge_h_bytes: &[u8], nonce: &[u8]) -> Vec<u8> {
    let mut n = Vec::with_capacity(challenge_h_bytes.len() + nonce.len());
    n.extend_from_slice(challenge_h_bytes);
    n.extend_from_slice(nonce);
    n
}

/// Create `AuthProofOnlySk` for fee registration and fee topup proofs (1 key).
pub fn create_fee_account_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AccountKeyPair,
    request: &FeeAccountDeviceRequest,
    sk_gen: PallasA,
) -> Result<SingleSkDeviceResponse, Error> {
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let pk = PallasA::try_from(&request.pk)?;

    let proof = BPAuthProofOnlySk::new(rng, key.secret.0.0, pk, &nonce, &sk_gen)?;

    Ok(SingleSkDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// Create `AuthProofOnlySks` for account registration and mint proofs (2 keys).
pub fn create_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AccountKeys,
    request: &RegistrationDeviceRequest,
    sk_gen: PallasA,
    sk_enc_gen: PallasA,
) -> Result<TwoSksDeviceResponse, Error> {
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let pk_aff = PallasA::try_from(&request.pk_aff)?;
    let pk_enc = PallasA::try_from(&request.pk_enc)?;

    let proof = BPAuthProofOnlySks::new(
        rng,
        keys.acct.secret.0.0,
        keys.enc.secret.0.0,
        pk_aff,
        pk_enc,
        &nonce,
        &sk_gen,
        &sk_enc_gen,
    )?;

    Ok(TwoSksDeviceResponse(WrappedCanonical::wrap(&proof)?))
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
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let rerandomized_leaf = PallasA::try_from(&request.rerandomized_leaf)?;
    let updated_commitment = PallasA::try_from(&request.updated_account_commitment)?;
    let nullifier = PallasA::try_from(&request.nullifier)?;
    let auth_rerandomization: PallasScalar = request.auth_rerandomization.decode()?;
    let auth_new_randomness: PallasScalar = request.auth_new_randomness.decode()?;

    let proof = BPAuthProofFeePayment::new(
        rng,
        key.secret.0.0,
        auth_rerandomization,
        auth_new_randomness,
        &rerandomized_leaf,
        &updated_commitment,
        nullifier,
        &nonce,
        sk_gen,
        randomness_gen,
        comm_re_rand_gen,
    )?;

    Ok(FeePaymentDeviceResponse(WrappedCanonical::wrap(&proof)?))
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
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let rerandomized_leaf = PallasA::try_from(&request.rerandomized_leaf)?;
    let updated_commitment = PallasA::try_from(&request.updated_account_commitment)?;
    let nullifier = PallasA::try_from(&request.nullifier)?;
    let auth_rerandomization: PallasScalar = request.auth_rerandomization.decode()?;
    let auth_rand_new_comm: PallasScalar = request.auth_rand_new_comm.decode()?;

    let k_amounts: Vec<PallasScalar> = request
        .k_amounts
        .iter()
        .map(|k| k.decode())
        .collect::<Result<_, _>>()?;
    let k_asset_ids: Vec<PallasScalar> = request
        .k_asset_ids
        .iter()
        .map(|k| k.decode())
        .collect::<Result<_, _>>()?;

    let leg_prover_configs = request
        .leg_prover_configs
        .iter()
        .map(|c| c.decode_inner())
        .collect::<Result<Vec<_>, _>>()?;

    let proof = BPAuthProofAffirmation::new(
        rng,
        keys.acct.secret.0.0,
        keys.enc.secret.0.0,
        auth_rerandomization,
        auth_rand_new_comm,
        k_amounts,
        k_asset_ids,
        leg_prover_configs,
        &rerandomized_leaf,
        &updated_commitment,
        nullifier,
        &nonce,
        sk_gen,
        enc_key_gen,
        comm_re_rand_gen,
        enc_gen,
    )?;

    Ok(AffirmationDeviceResponse(WrappedCanonical::wrap(&proof)?))
}
