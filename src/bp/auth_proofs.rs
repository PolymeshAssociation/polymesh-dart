use ark_std::string::ToString;
use ark_std::{format, vec::Vec};
use rand_core::{CryptoRng, RngCore};
use zeroize::{Zeroize, ZeroizeOnDrop};

use polymesh_dart_bp::auth_proofs::account_comm_key::NUM_GENERATORS;
use polymesh_dart_bp::auth_proofs::fee_account::{
    FeeAccountStateCommitment, PALLAS_FR_SMOOTH_ORDER, ensure_valid_fee_registration_opening,
};
use polymesh_dart_bp::auth_proofs::keys::{
    MasterSeed as BPMasterSeed, keygen_enc_given_sk, keygen_sig_given_sk,
};
use polymesh_dart_bp::auth_proofs::{
    account::AuthProofAffirmation as BPAuthProofAffirmation,
    fee_account::AuthProofFeePayment as BPAuthProofFeePayment,
};
use polymesh_dart_common::SkGenCounter;

use super::device::DeviceGenerators;
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
    /// Keys `MasterSeed::derive_keys` derives from `seed`, `path` and `counter` with `Blake2b512`.
    /// Equal to the host's `MasterSeed::derive_account_keys(path)` at `counter = 0`.
    pub fn from_master_seed(
        seed: &BPMasterSeed,
        path: &[u8],
        counter: SkGenCounter,
        gens: &DeviceGenerators,
    ) -> Self {
        let ((sk_aff, _), (sk_enc, _)) = seed.derive_keys::<PallasA, blake2::Blake2b512>(
            path,
            counter,
            gens.sig_key_gen(),
            gens.enc_key_gen(),
        );
        Self {
            sk_aff: sk_aff.0,
            sk_enc: sk_enc.0,
        }
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
    gens: &DeviceGenerators,
) -> Result<SingleSkDeviceResponse, Error> {
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let pk = PallasA::try_from(&request.pk)?;

    let proof = BPAuthProofOnlySk::new(
        rng,
        key.sk,
        pk,
        &nonce,
        &request.txn_type.into(),
        &gens.sig_key_gen(),
    )?;

    Ok(SingleSkDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// Create `AuthProofOnlySk` for fee account registration. Rejects a commitment that doesn't open
/// to the request's opening, or an `initial_rho` of small order.
pub fn create_fee_account_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    request: &FeeAccountRegistrationDeviceRequest,
    gens: &DeviceGenerators,
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
        &gens.account_comm_key,
    )?;

    let proof = BPAuthProofOnlySk::new_with_account_commitment(
        rng,
        key.sk,
        pk,
        &account_commitment,
        &nonce,
        &request.txn_type.into(),
        &gens.sig_key_gen(),
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
    gens: &DeviceGenerators,
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
        &gens.sig_key_gen(),
        &gens.enc_key_gen(),
    )?;

    Ok(TwoSksDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// Create `AuthProofOnlySks` for account registration (2 keys).
pub fn create_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    request: &RegistrationDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<AccountRegistrationDeviceResponse, Error> {
    if !matches!(request.txn_type, DeviceTxnType::AccountRegistration { .. }) {
        return Err(Error::ProofGenerationError(
            "Expected an account registration txn type".to_string(),
        ));
    }
    let response = two_sks_proof(
        rng,
        keys,
        &request.challenge_h_bytes,
        &request.nonce,
        &request.pk_aff,
        &request.pk_enc,
        request.txn_type,
        gens,
    )?;
    Ok(AccountRegistrationDeviceResponse(response))
}

/// Device side of account key registration for a single account. Derives the account's key material
/// from `keys` and delegates to `create_key_registration_proof`. `identity` is the proof nonce.
/// Self-contained — no host request, unlike account-asset registration.
pub fn create_key_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    identity: &[u8],
    gens: &DeviceGenerators,
) -> Result<KeyRegistrationDeviceResponse, Error> {
    let (sig_key_gen, enc_key_gen) = (gens.sig_key_gen(), gens.enc_key_gen());
    let sig = keygen_sig_given_sk(keys.sk_aff, sig_key_gen);
    let enc = keygen_enc_given_sk(keys.sk_enc, enc_key_gen);
    create_key_registration_proof(rng, &[(sig, enc)], identity, sig_key_gen, enc_key_gen)
}

/// Create `AuthProofOnlySks` for asset mint (2 keys).
pub fn create_mint_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    request: &MintDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<AssetMintingDeviceResponse, Error> {
    if !matches!(request.txn_type, DeviceTxnType::Mint { .. }) {
        return Err(Error::ProofGenerationError(
            "Expected a mint txn type".to_string(),
        ));
    }
    let response = two_sks_proof(
        rng,
        keys,
        &request.challenge_h_bytes,
        &request.nonce,
        &request.pk_aff,
        &request.pk_enc,
        request.txn_type,
        gens,
    )?;
    Ok(AssetMintingDeviceResponse(response))
}

/// Create `AuthProofFeePayment` for fee payment proofs.
pub fn create_fee_payment_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    request: &FeePaymentDeviceRequest,
    gens: &DeviceGenerators,
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
        gens.sig_key_gen(),
        gens.comm_re_rand_gen,
        gens.anchor_gen,
    )?;

    Ok(FeePaymentDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

/// Create `AuthProofAffirmation` for affirmation/claim/reversal/counter-update proofs.
pub fn create_affirmation_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    request: &AffirmationDeviceRequest,
    gens: &DeviceGenerators,
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
        gens.comm_re_rand_gen,
        gens.anchor_gen,
        gens.leg_asset_value_gen,
        &gens.account_comm_key,
    )?;

    Ok(AffirmationDeviceResponse(WrappedCanonical::wrap(&proof)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_serialize::CanonicalSerialize;

    /// Pins the seed-to-key derivation the Ledger app uses for its account keys.
    #[test]
    fn from_master_seed_known_answer() {
        let seed = BPMasterSeed::new(vec![7u8; 32]);
        let gens = DeviceGenerators::new().unwrap();
        let keys = AuthSigningKeys::from_master_seed(&seed, b"", 0, &gens);
        let mut bytes = Vec::new();
        keys.sk_aff.serialize_compressed(&mut bytes).unwrap();
        keys.sk_enc.serialize_compressed(&mut bytes).unwrap();
        assert_eq!(
            hex::encode(bytes),
            "1790d5f31a11c8f55d73fbb2b2243126ae71f073ee6a63ee95ab5adb336c3f34b1026b6b7e456588fbd5e184df6b6164c0d89020a2a5526cd439df93eb44b423"
        );
    }

    #[cfg(feature = "host_proofs")]
    #[test]
    fn from_master_seed_matches_host() {
        let gens = DeviceGenerators::new().unwrap();
        let seed_hex = "0x0707070707070707070707070707070707070707070707070707070707070707";
        let host = MasterSeed::from_seed(seed_hex)
            .derive_account_keys("m/0")
            .unwrap();
        let seed = BPMasterSeed::new(vec![7u8; 32]);
        let device = AuthSigningKeys::from_master_seed(&seed, b"m/0", 0, &gens);
        assert_eq!(device.sk_aff, host.acct.secret.0.0);
        assert_eq!(device.sk_enc, host.enc.secret.0.0);
    }

    #[test]
    fn two_sks_proofs_reject_wrong_txn_type() {
        let mut rng = rng_from_seed([0u8; 32]);
        let g = DeviceGenerators::new().unwrap();
        let keys =
            AuthSigningKeys::from_master_seed(&BPMasterSeed::new(b"txn-type".to_vec()), b"", 0, &g);
        let pk = CompressedAffine::try_from(g.sig_key_gen()).unwrap();

        let registration = RegistrationDeviceRequest {
            challenge_h_bytes: Vec::new(),
            nonce: Vec::new(),
            pk_aff: pk.clone(),
            pk_enc: pk.clone(),
            txn_type: DeviceTxnType::Mint {
                asset_id: 1,
                amount: 1,
            },
        };
        assert!(create_registration_auth_proof(&mut rng, &keys, &registration, &g).is_err());

        let mint = MintDeviceRequest {
            challenge_h_bytes: Vec::new(),
            nonce: Vec::new(),
            pk_aff: pk.clone(),
            pk_enc: pk,
            txn_type: DeviceTxnType::AccountRegistration { asset_id: 1 },
        };
        assert!(create_mint_auth_proof(&mut rng, &keys, &mint, &g).is_err());
    }
}
