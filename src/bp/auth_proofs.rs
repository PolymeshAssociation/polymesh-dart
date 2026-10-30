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
    /// Keys `MasterSeed::derive_keys` derives from `seed`, `path` and `counter`.
    /// Equal to the host's `MasterSeed::derive_account_keys(path)` at `counter = 0`.
    pub fn from_master_seed(
        seed: &BPMasterSeed,
        path: &[u8],
        counter: SkGenCounter,
        gens: &DeviceGenerators,
    ) -> Result<Self, Error> {
        let ((sk_aff, _), (sk_enc, _)) =
            seed.derive_keys::<PallasA>(path, counter, gens.sig_key_gen(), gens.enc_key_gen())?;
        Ok(Self {
            sk_aff: sk_aff.0,
            sk_enc: sk_enc.0,
        })
    }
}

/// `MasterSeed::derive_account_randomness` from `seed`, `path` and `counter_s`.
pub fn derive_account_randomness(
    seed: &BPMasterSeed,
    path: &[u8],
    counter_s: SkGenCounter,
    request: &AccountRandomnessDeviceRequest,
) -> Result<AccountRandomnessDeviceResponse, Error> {
    let (randomness, rho_randomness) = seed.derive_account_randomness::<PallasA>(
        path,
        counter_s,
        request.asset_id,
        request.counter,
    )?;
    Ok(AccountRandomnessDeviceResponse {
        randomness: WrappedCanonical::wrap(&randomness)?,
        rho_randomness: WrappedCanonical::wrap(&rho_randomness)?,
    })
}

/// `MasterSeed::derive_fee_account_randomness` from `seed`, `path` and `counter_s`.
pub fn derive_fee_account_randomness(
    seed: &BPMasterSeed,
    path: &[u8],
    counter_s: SkGenCounter,
    request: &AccountRandomnessDeviceRequest,
) -> Result<FeeAccountRandomnessDeviceResponse, Error> {
    let (initial_rho, initial_randomness) = seed.derive_fee_account_randomness::<PallasA>(
        path,
        counter_s,
        request.asset_id,
        request.counter,
    )?;
    Ok(FeeAccountRandomnessDeviceResponse {
        initial_rho: WrappedCanonical::wrap(&initial_rho)?,
        initial_randomness: WrappedCanonical::wrap(&initial_randomness)?,
    })
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

/// Create `AuthProofOnlySk` for fee topup proofs (1 key).
pub fn create_fee_account_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    request: &FeeAccountDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<FeeAccountTopupDeviceResponse, Error> {
    if !matches!(request.txn_type, DeviceTxnType::FeeAccountTopup { .. }) {
        return Err(Error::ProofGenerationError(
            "Expected a fee account topup txn type".to_string(),
        ));
    }
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

    Ok(FeeAccountTopupDeviceResponse(SingleSkDeviceResponse(
        WrappedCanonical::wrap(&proof)?,
    )))
}

/// Create `AuthProofOnlySk` for fee account registration. Rejects a commitment that doesn't open
/// to the request's opening, or an `initial_rho` of small order.
pub fn create_fee_account_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    request: &FeeAccountRegistrationDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<FeeAccountRegistrationDeviceResponse, Error> {
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

    Ok(FeeAccountRegistrationDeviceResponse(
        SingleSkDeviceResponse(WrappedCanonical::wrap(&proof)?),
    ))
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
) -> Result<FeeAccountPaymentDeviceResponse, Error> {
    if !matches!(request.txn_type, DeviceTxnType::FeePayment { .. }) {
        return Err(Error::ProofGenerationError(
            "Expected a fee payment txn type".to_string(),
        ));
    }
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

    Ok(FeeAccountPaymentDeviceResponse(FeePaymentDeviceResponse(
        WrappedCanonical::wrap(&proof)?,
    )))
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
    use ark_std::vec;

    /// Pins the seed-to-key derivation the Ledger app uses for its account keys.
    #[test]
    fn from_master_seed_known_answer() {
        let seed = BPMasterSeed::new(vec![7u8; 32]);
        let gens = DeviceGenerators::new().unwrap();
        let keys = AuthSigningKeys::from_master_seed(&seed, b"", 0, &gens).unwrap();
        let mut bytes = Vec::new();
        keys.sk_aff.serialize_compressed(&mut bytes).unwrap();
        keys.sk_enc.serialize_compressed(&mut bytes).unwrap();
        assert_eq!(
            hex::encode(bytes),
            "8366b68f9fa4a121d8de67c3e4be71373849d1002dbe21957a77c3e0ee4493029900e1bb51bd267c6dfc28b077be5face539354d74bb26b3bed6aea36afaec29"
        );
    }

    /// Pins the seed-to-randomness derivation and the response encoding the Ledger app uses.
    #[test]
    fn derive_account_randomness_known_answer() {
        use codec::Encode;
        let seed = BPMasterSeed::new(vec![7u8; 32]);
        let request = AccountRandomnessDeviceRequest {
            asset_id: 5,
            counter: 3,
        };
        let account = derive_account_randomness(&seed, b"", 0, &request).unwrap();
        let fee = derive_fee_account_randomness(&seed, b"", 0, &request).unwrap();
        assert_eq!(
            hex::encode(account.encode()),
            "805b4f1a1081044299a78562ab3b8b4e9a6669f2e3c765557e1d3573993164a51480b5e8eaf4f978da5735977141343622d80a0f7a9227a73087c942dcd00c923739"
        );
        assert_eq!(
            hex::encode(fee.encode()),
            "80d2c669287607e8ca90edb19c5e0a6296c9935db919ce871324ae892a6bc7b8378008171ba37958458c19b91865096cbeb3a3d8373a6905f2e1d65aedab818c3a3f"
        );
    }

    #[cfg(feature = "host_proofs")]
    #[test]
    fn from_master_seed_matches_host() {
        let gens = DeviceGenerators::new().unwrap();
        let seed_hex = "0x0707070707070707070707070707070707070707070707070707070707070707";
        let host = MasterSeed::from_seed(seed_hex)
            .unwrap()
            .derive_account_keys("m/0")
            .unwrap();
        let seed = BPMasterSeed::new(vec![7u8; 32]);
        let device = AuthSigningKeys::from_master_seed(&seed, b"m/0", 0, &gens).unwrap();
        assert_eq!(device.sk_aff, host.acct.secret.0.0);
        assert_eq!(device.sk_enc, host.enc.secret.0.0);
    }

    #[test]
    fn two_sks_proofs_reject_wrong_txn_type() {
        let mut rng = rng_from_seed([0u8; 32]);
        let g = DeviceGenerators::new().unwrap();
        let keys = AuthSigningKeys::from_master_seed(
            &BPMasterSeed::new(b"txn-type".repeat(4)),
            b"",
            0,
            &g,
        )
        .unwrap();
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

    #[test]
    fn fee_proofs_reject_wrong_txn_type() {
        let mut rng = rng_from_seed([0u8; 32]);
        let g = DeviceGenerators::new().unwrap();
        let key = AuthSigningKey {
            sk: PallasScalar::from(5u64),
        };
        let pk = CompressedAffine::try_from(g.sig_key_gen()).unwrap();
        let wrong_txn_type = DeviceTxnType::FeeAccountRegistration {
            asset_id: 0,
            balance: 1,
        };

        let topup = FeeAccountDeviceRequest {
            challenge_h_bytes: Vec::new(),
            nonce: Vec::new(),
            pk: pk.clone(),
            txn_type: wrong_txn_type,
        };
        assert!(create_fee_account_auth_proof(&mut rng, &key, &topup, &g).is_err());

        let payment = FeePaymentDeviceRequest {
            challenge_h_bytes: Vec::new(),
            nonce: Vec::new(),
            auth_rerandomization: WrappedCanonical::wrap(&PallasScalar::from(1u64)).unwrap(),
            auth_new_randomness: WrappedCanonical::wrap(&PallasScalar::from(1u64)).unwrap(),
            rerandomized_leaf: pk.clone(),
            updated_account_commitment: pk.clone(),
            nullifier: pk,
            txn_type: wrong_txn_type,
        };
        assert!(create_fee_payment_auth_proof(&mut rng, &key, &payment, &g).is_err());
    }
}
