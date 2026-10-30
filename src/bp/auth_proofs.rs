use super::split_types::*;
use super::*;
use crate::Error;
use ark_std::{format, string::ToString, vec::Vec};
use polymesh_dart_bp::account::state::NUM_GENERATORS;
use polymesh_dart_bp::auth_proofs::{
    self, account::AuthProofAffirmation as BPAuthProofAffirmation,
    fee_account::AuthProofFeePayment as BPAuthProofFeePayment,
};
use polymesh_dart_bp::fee_account::{
    PALLAS_FR_SMOOTH_ORDER, ensure_valid_fee_registration_opening,
};
use rand_core::{CryptoRng, RngCore};

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

    let proof = BPAuthProofOnlySk::new(
        rng,
        key.secret.0.0,
        pk,
        &nonce,
        &request.txn_type.into(),
        &sk_gen,
    )?;

    Ok(SingleSkDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// Create `AuthProofOnlySk` for fee account registration. Rejects a commitment that doesn't open
/// to the request's opening, or an `initial_rho` of small order.
pub fn create_fee_account_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AccountKeyPair,
    request: &FeeAccountRegistrationDeviceRequest,
    sk_gen: PallasA,
) -> Result<SingleSkDeviceResponse, Error> {
    let DeviceTxnType::FeeAccountRegistration { asset_id, balance } = request.txn_type else {
        return Err(Error::ProofGenerationError(
            "Expected a fee account registration txn type".to_string(),
        ));
    };
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let pk = PallasA::try_from(&request.pk)?;
    let account_commitment = PallasA::try_from(&request.account_commitment)?;
    let initial_rho: PallasScalar = request.initial_rho.decode()?;
    let initial_randomness: PallasScalar = request.initial_randomness.decode()?;

    ensure_valid_fee_registration_opening(
        &polymesh_dart_bp::fee_account::FeeAccountStateCommitment(account_commitment),
        &pk,
        asset_id,
        balance,
        initial_rho,
        initial_randomness,
        &PALLAS_FR_SMOOTH_ORDER,
        &dart_gens().account_comm_key(),
    )?;

    let proof = BPAuthProofOnlySk::new_with_account_commitment(
        rng,
        key.secret.0.0,
        pk,
        &account_commitment,
        &nonce,
        &request.txn_type.into(),
        &sk_gen,
    )?;

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
        &request.txn_type.into(),
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
    comm_re_rand_gen: PallasA,
    anchor_gen: PallasA,
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
        &request.txn_type.into(),
        sk_gen,
        comm_re_rand_gen,
        anchor_gen,
    )?;

    Ok(FeePaymentDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// Create `AuthProofAffirmation` for affirmation/claim/reversal/counter-update proofs.
pub fn create_affirmation_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AccountKeys,
    request: &AffirmationDeviceRequest,
    comm_re_rand_gen: PallasA,
    anchor_gen: PallasA,
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

    let new_acc_openings: [PallasScalar; NUM_GENERATORS - 2] = request
        .new_acc_openings
        .iter()
        .map(|o| o.decode())
        .collect::<Result<Vec<_>, _>>()?
        .try_into()
        .map_err(|v: Vec<PallasScalar>| {
            Error::ProofGenerationError(format!(
                "Expected {} new_acc_openings but got {}",
                NUM_GENERATORS - 2,
                v.len()
            ))
        })?;

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
        new_acc_openings,
        leg_prover_configs,
        &rerandomized_leaf,
        &updated_commitment,
        nullifier,
        &nonce,
        &request.txn_type.into(),
        comm_re_rand_gen,
        anchor_gen,
        enc_gen,
        &dart_gens().account_comm_key(),
    )?;

    Ok(AffirmationDeviceResponse(WrappedCanonical::wrap(&proof)?))
}
