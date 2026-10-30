use ark_std::string::ToString;
use ark_std::{format, vec::Vec};
use rand_core::{CryptoRng, RngCore};
use zeroize::{Zeroize, ZeroizeOnDrop};

use polymesh_dart_bp::auth_proofs::account_comm_key::{AccountCommitmentKeyTrait, NUM_GENERATORS};
use polymesh_dart_bp::auth_proofs::fee_account::{
    FeeAccountStateCommitment, PALLAS_FR_SMOOTH_ORDER, ensure_valid_fee_registration_opening,
};
use polymesh_dart_bp::auth_proofs::keys::{keygen_enc_given_sk, keygen_sig_given_sk};
use polymesh_dart_bp::auth_proofs::{
    account::AuthProofAffirmation as BPAuthProofAffirmation,
    fee_account::AuthProofFeePayment as BPAuthProofFeePayment,
};
use polymesh_dart_bp::keys::rand_non_zero;

use super::key_reg_split::{KeyRegistrationDeviceResponse, create_key_registration_proof};
use super::split_types::*;
use super::*;
use crate::Error;

/// Construct `ledger_nonce = challenge_h_bytes || nonce`.
fn ledger_nonce(challenge_h_bytes: &[u8], nonce: &[u8]) -> Vec<u8> {
    let mut n = Vec::with_capacity(challenge_h_bytes.len() + nonce.len());
    n.extend_from_slice(challenge_h_bytes);
    n.extend_from_slice(nonce);
    n
}

/// Device signing keys for the two-secret-key auth proofs
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct AuthSigningKeys {
    pub sk_aff: PallasScalar,
    pub sk_enc: PallasScalar,
}

/// Device signing key for the single-secret-key auth proofs
#[derive(Clone, Zeroize, ZeroizeOnDrop)]
pub struct AuthSigningKey {
    pub sk: PallasScalar,
}

impl AuthSigningKeys {
    pub fn from_seed(seed: &str) -> Result<Self, Error> {
        Self::from_rng(rng_from_seed_str(seed))
    }

    /// Same derivation as `from_seed`, from raw bytes instead of a string.
    pub fn from_seed_bytes(seed: &[u8]) -> Result<Self, Error> {
        Self::from_rng(rng_from_seed_bytes(seed))
    }

    fn from_rng(mut rng: rand_chacha::ChaCha20Rng) -> Result<Self, Error> {
        let sk_enc = rand_non_zero::<PallasScalar, _>(&mut rng);
        let sk_aff = rand_non_zero::<PallasScalar, _>(&mut rng);
        Ok(Self { sk_aff, sk_enc })
    }
}

#[cfg(feature = "host_proofs")]
impl From<&AccountKeys> for AuthSigningKeys {
    fn from(keys: &AccountKeys) -> Self {
        Self {
            sk_aff: keys.acct.secret.0.0,
            sk_enc: keys.enc.secret.0.0,
        }
    }
}

#[cfg(feature = "host_proofs")]
impl From<&AccountKeyPair> for AuthSigningKey {
    fn from(key: &AccountKeyPair) -> Self {
        Self { sk: key.secret.0.0 }
    }
}

/// Create `AuthProofOnlySk` for fee registration and fee topup proofs (1 key).
pub fn create_fee_account_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    request: &FeeAccountDeviceRequest,
    sk_gen: PallasA,
) -> Result<SingleSkDeviceResponse, Error> {
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let pk = PallasA::try_from(&request.pk)?;

    let proof = BPAuthProofOnlySk::new(rng, key.sk, pk, &nonce, &request.txn_type.into(), &sk_gen)?;

    Ok(SingleSkDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// Create `AuthProofOnlySk` for fee account registration. Rejects a commitment that doesn't open
/// to the request's opening, or an `initial_rho` of small order.
pub fn create_fee_account_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    request: &FeeAccountRegistrationDeviceRequest,
    account_comm_key: &impl AccountCommitmentKeyTrait<PallasA>,
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
        &FeeAccountStateCommitment(account_commitment),
        &pk,
        asset_id,
        balance,
        initial_rho,
        initial_randomness,
        &PALLAS_FR_SMOOTH_ORDER,
        account_comm_key,
    )?;

    let proof = BPAuthProofOnlySk::new_with_account_commitment(
        rng,
        key.sk,
        pk,
        &account_commitment,
        &nonce,
        &request.txn_type.into(),
        &account_comm_key.sk_gen(),
    )?;

    Ok(SingleSkDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// The 2-secret-key proof shared by registration and mint.
fn two_sks_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    challenge_h_bytes: &[u8],
    nonce: &[u8],
    pk_aff: &CompressedAffine,
    pk_enc: &CompressedAffine,
    txn_type: DeviceTxnType,
    sk_gen: PallasA,
    sk_enc_gen: PallasA,
) -> Result<TwoSksDeviceResponse, Error> {
    let nonce = ledger_nonce(challenge_h_bytes, nonce);
    let pk_aff = PallasA::try_from(pk_aff)?;
    let pk_enc = PallasA::try_from(pk_enc)?;

    let proof = BPAuthProofOnlySks::new(
        rng,
        keys.sk_aff,
        keys.sk_enc,
        pk_aff,
        pk_enc,
        &nonce,
        &txn_type.into(),
        &sk_gen,
        &sk_enc_gen,
    )?;

    Ok(TwoSksDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// Create `AuthProofOnlySks` for account registration (2 keys).
pub fn create_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    request: &RegistrationDeviceRequest,
    sk_gen: PallasA,
    sk_enc_gen: PallasA,
) -> Result<TwoSksDeviceResponse, Error> {
    two_sks_proof(
        rng,
        keys,
        &request.challenge_h_bytes,
        &request.nonce,
        &request.pk_aff,
        &request.pk_enc,
        request.txn_type,
        sk_gen,
        sk_enc_gen,
    )
}

/// Device side of account key registration for a single account. Derives the account's key material
/// from `keys` and delegates to `create_key_registration_proof`. `identity` is the proof nonce.
/// Self-contained — no host request, unlike account-asset registration.
pub fn create_key_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    identity: &[u8],
    sig_key_gen: PallasA,
    enc_key_gen: PallasA,
) -> Result<KeyRegistrationDeviceResponse, Error> {
    let sig = keygen_sig_given_sk(keys.sk_aff, sig_key_gen);
    let enc = keygen_enc_given_sk(keys.sk_enc, enc_key_gen);
    create_key_registration_proof(rng, &[(sig, enc)], identity, sig_key_gen, enc_key_gen)
}

/// Create `AuthProofOnlySks` for asset mint (2 keys).
pub fn create_mint_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    request: &MintDeviceRequest,
    sk_gen: PallasA,
    sk_enc_gen: PallasA,
) -> Result<AssetMintingDeviceResponse, Error> {
    let response = two_sks_proof(
        rng,
        keys,
        &request.challenge_h_bytes,
        &request.nonce,
        &request.pk_aff,
        &request.pk_enc,
        request.txn_type,
        sk_gen,
        sk_enc_gen,
    )?;
    Ok(AssetMintingDeviceResponse(response))
}

/// Create `AuthProofFeePayment` for fee payment proofs.
pub fn create_fee_payment_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
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
        key.sk,
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
    keys: &AuthSigningKeys,
    request: &AffirmationDeviceRequest,
    comm_re_rand_gen: PallasA,
    anchor_gen: PallasA,
    enc_gen: PallasA,
    account_comm_key: &impl AccountCommitmentKeyTrait<PallasA>,
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
        keys.sk_aff,
        keys.sk_enc,
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
        account_comm_key,
    )?;

    Ok(AffirmationDeviceResponse(WrappedCanonical::wrap(&proof)?))
}
