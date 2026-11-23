use ark_std::string::ToString;
use ark_std::{format, vec::Vec};
use rand_core::{CryptoRng, RngCore};
use zeroize::{Zeroize, ZeroizeOnDrop};

use polymesh_dart_bp::auth_proofs::account::registration_account_commitment;
use polymesh_dart_bp::auth_proofs::account_comm_key::NUM_GENERATORS;
use polymesh_dart_bp::auth_proofs::fee_account::{
    PALLAS_FR_SMOOTH_ORDER, fee_registration_account_commitment,
};
use polymesh_dart_bp::auth_proofs::keys::{
    MasterSeed as BPMasterSeed, keygen_enc_given_sk, keygen_sig_given_sk,
};
use polymesh_dart_bp::auth_proofs::{
    account::AuthProofAffirmation as BPAuthProofAffirmation,
    fee_account::AuthProofFeePayment as BPAuthProofFeePayment,
};
use polymesh_dart_bp::poseidon_impls::poseidon_2::params::pallas::new_poseidon2_params_for_2_1_hashing;
use polymesh_dart_common::{AssetId, Balance, SkGenCounter};

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
    ) -> Result<Self, Error> {
        let (sk_aff, sk_enc) = seed.derive_secret_keys::<PallasScalar>(path, counter)?;
        Ok(Self { sk_aff, sk_enc })
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

fn asset_id_balance_for_fee_reg_txn(txn_type: DeviceTxnType) -> Result<(AssetId, Balance), Error> {
    let DeviceTxnType::FeeAccountRegistration { asset_id, balance } = txn_type else {
        return Err(Error::ProofGenerationError(
            "Expected a fee account registration txn type".to_string(),
        ));
    };
    Ok((asset_id, balance))
}

/// Create `AuthProofOnlySk` for fee account registration, bound to the commitment to a new fee
/// account with the `(initial_rho, initial_randomness)` of `derive_fee_account_randomness` for
/// `seed`, `path`, `counter_s` and the request's asset id and counter. Rejects either of small order.
pub fn create_fee_account_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    seed: &BPMasterSeed,
    path: &[u8],
    counter_s: SkGenCounter,
    request: &FeeAccountRegistrationDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<FeeAccountRegistrationDeviceResponse, Error> {
    let (asset_id, _) = asset_id_balance_for_fee_reg_txn(request.txn_type)?;
    let (initial_rho, initial_randomness) =
        seed.derive_fee_account_randomness::<PallasA>(path, counter_s, asset_id, request.counter)?;
    fee_account_registration_auth_proof(rng, key, initial_rho, initial_randomness, request, gens)
}

/// `create_fee_account_registration_auth_proof` for a fee account opened with `initial_rho` and
/// `initial_randomness` instead of the master seed's.
#[cfg(feature = "host_proofs")]
pub fn create_fee_account_registration_auth_proof_given_randomness<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    initial_rho: PallasScalar,
    initial_randomness: PallasScalar,
    request: &FeeAccountRegistrationDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<FeeAccountRegistrationDeviceResponse, Error> {
    fee_account_registration_auth_proof(rng, key, initial_rho, initial_randomness, request, gens)
}

fn fee_account_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    key: &AuthSigningKey,
    initial_rho: PallasScalar,
    initial_randomness: PallasScalar,
    request: &FeeAccountRegistrationDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<FeeAccountRegistrationDeviceResponse, Error> {
    let (asset_id, balance) = asset_id_balance_for_fee_reg_txn(request.txn_type)?;
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let pk = PallasA::try_from(&request.pk)?;
    let account_commitment = fee_registration_account_commitment(
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
        &account_commitment.0,
        &nonce,
        &request.txn_type.into(),
        &gens.sig_key_gen(),
    )?;

    Ok(FeeAccountRegistrationDeviceResponse(
        SingleSkDeviceResponse(WrappedCanonical::wrap(&proof)?),
    ))
}

fn registration_txn_type(txn_type: DeviceTxnType) -> Result<AssetId, Error> {
    let DeviceTxnType::AccountRegistration { asset_id } = txn_type else {
        return Err(Error::ProofGenerationError(
            "Expected an account registration txn type".to_string(),
        ));
    };
    Ok(asset_id)
}

/// Create `AuthProofOnlySks` for account registration (2 keys), bound to the commitment to a new
/// account with the `(randomness, rho_randomness)` of `derive_account_randomness` for `seed`, `path`,
/// `counter_s` and the request's asset id and counter. Rejects a `randomness` of small order.
pub fn create_registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    seed: &BPMasterSeed,
    path: &[u8],
    counter_s: SkGenCounter,
    request: &RegistrationDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<AccountRegistrationDeviceResponse, Error> {
    let asset_id = registration_txn_type(request.txn_type)?;
    let (randomness, rho_randomness) =
        seed.derive_account_randomness::<PallasA>(path, counter_s, asset_id, request.counter)?;
    registration_auth_proof(rng, keys, randomness, rho_randomness, request, gens)
}

/// `create_registration_auth_proof` for an account opened with `randomness` and `rho_randomness`
/// instead of the master seed's.
#[cfg(feature = "host_proofs")]
pub fn create_registration_auth_proof_given_randomness<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    randomness: PallasScalar,
    rho_randomness: PallasScalar,
    request: &RegistrationDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<AccountRegistrationDeviceResponse, Error> {
    registration_auth_proof(rng, keys, randomness, rho_randomness, request, gens)
}

fn registration_auth_proof<R: RngCore + CryptoRng>(
    rng: &mut R,
    keys: &AuthSigningKeys,
    randomness: PallasScalar,
    rho_randomness: PallasScalar,
    request: &RegistrationDeviceRequest,
    gens: &DeviceGenerators,
) -> Result<AccountRegistrationDeviceResponse, Error> {
    let asset_id = registration_txn_type(request.txn_type)?;
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let pk_aff = PallasA::try_from(&request.pk_aff)?;
    let pk_enc = PallasA::try_from(&request.pk_enc)?;
    let account_commitment = registration_account_commitment(
        hash_identity::<PallasScalar>(&request.nonce),
        pk_aff,
        pk_enc,
        asset_id,
        request.counter,
        randomness,
        rho_randomness,
        &new_poseidon2_params_for_2_1_hashing()?,
        &PALLAS_FR_SMOOTH_ORDER,
        gens.account_comm_key,
    )?;

    let proof = BPAuthProofOnlySks::new_with_account_commitment(
        rng,
        keys.sk_aff,
        keys.sk_enc,
        pk_aff,
        pk_enc,
        &account_commitment.0,
        &nonce,
        &request.txn_type.into(),
        &gens.sig_key_gen(),
        &gens.enc_key_gen(),
    )?;

    Ok(AccountRegistrationDeviceResponse(TwoSksDeviceResponse(
        WrappedCanonical::wrap(&proof)?,
    )))
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
    let nonce = ledger_nonce(&request.challenge_h_bytes, &request.nonce);
    let pk_aff = PallasA::try_from(&request.pk_aff)?;
    let pk_enc = PallasA::try_from(&request.pk_enc)?;

    let proof = BPAuthProofOnlySks::new(
        rng,
        keys.sk_aff,
        keys.sk_enc,
        pk_aff,
        pk_enc,
        &nonce,
        &request.txn_type.into(),
        &gens.sig_key_gen(),
        &gens.enc_key_gen(),
    )?;

    Ok(AssetMintingDeviceResponse(TwoSksDeviceResponse(
        WrappedCanonical::wrap(&proof)?,
    )))
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
        let keys = AuthSigningKeys::from_master_seed(&seed, b"", 0).unwrap();
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
        let seed_hex = "0x0707070707070707070707070707070707070707070707070707070707070707";
        let host = MasterSeed::from_seed(seed_hex)
            .unwrap()
            .derive_account_keys("m/0")
            .unwrap();
        let seed = BPMasterSeed::new(vec![7u8; 32]);
        let device = AuthSigningKeys::from_master_seed(&seed, b"m/0", 0).unwrap();
        assert_eq!(device.sk_aff, host.acct.secret.0.0);
        assert_eq!(device.sk_enc, host.enc.secret.0.0);
    }

    #[test]
    fn two_sks_proofs_reject_wrong_txn_type() {
        let mut rng = rng_from_seed([0u8; 32]);
        let g = DeviceGenerators::new().unwrap();
        let seed = BPMasterSeed::new(b"txn-type".repeat(4));
        let keys = AuthSigningKeys::from_master_seed(&seed, b"", 0).unwrap();
        let pk = CompressedAffine::try_from(g.sig_key_gen()).unwrap();

        let registration = RegistrationDeviceRequest {
            challenge_h_bytes: Vec::new(),
            nonce: Vec::new(),
            pk_aff: pk.clone(),
            pk_enc: pk.clone(),
            counter: 0,
            txn_type: DeviceTxnType::Mint {
                asset_id: 1,
                amount: 1,
            },
        };
        assert!(
            create_registration_auth_proof(&mut rng, &keys, &seed, b"", 0, &registration, &g)
                .is_err()
        );

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

    #[cfg(feature = "host_proofs")]
    mod registration {
        use super::*;
        use ark_std::UniformRand;
        use polymesh_dart_bp::account::state::AccountState as BPAccountState;
        use polymesh_dart_bp::fee_account::FeeAccountState as BPFeeAccountState;
        use polymesh_dart_bp::poseidon_impls::poseidon_2::params::pallas::get_poseidon2_params_for_2_1_hashing;
        use polymesh_dart_common::NullifierSkGenCounter;

        const SEED_PATH: &[u8] = b"m/0";
        const IDENTITY: &[u8] = b"identity";
        const ASSET_ID: AssetId = 5;
        const COUNTER: NullifierSkGenCounter = 3;
        const FEE_BALANCE: Balance = 1000;

        fn seed_and_keys() -> (BPMasterSeed, AuthSigningKeys) {
            let seed = BPMasterSeed::new(b"registration-seed-check".repeat(2));
            let keys = AuthSigningKeys::from_master_seed(&seed, SEED_PATH, 0).unwrap();
            (seed, keys)
        }

        fn public_keys(keys: &AuthSigningKeys, g: &DeviceGenerators) -> (PallasA, PallasA) {
            let (_, pk_aff) = keygen_sig_given_sk(keys.sk_aff, g.sig_key_gen());
            let (_, pk_enc) = keygen_enc_given_sk(keys.sk_enc, g.enc_key_gen());
            (pk_aff.0, pk_enc.0)
        }

        /// Registration request for a new account of `keys` at `COUNTER`.
        fn registration_request(
            keys: &AuthSigningKeys,
            g: &DeviceGenerators,
        ) -> RegistrationDeviceRequest {
            let (pk_aff, pk_enc) = public_keys(keys, g);
            RegistrationDeviceRequest {
                challenge_h_bytes: vec![1u8; 32],
                nonce: IDENTITY.to_vec(),
                pk_aff: CompressedAffine::try_from(pk_aff).unwrap(),
                pk_enc: CompressedAffine::try_from(pk_enc).unwrap(),
                counter: COUNTER,
                txn_type: DeviceTxnType::AccountRegistration { asset_id: ASSET_ID },
            }
        }

        /// Commitment to a new account of `keys` at `COUNTER` opened with `randomness` and
        /// `rho_randomness`.
        fn account_commitment(
            keys: &AuthSigningKeys,
            randomness: PallasScalar,
            rho_randomness: PallasScalar,
            g: &DeviceGenerators,
        ) -> PallasA {
            let (pk_aff, pk_enc) = public_keys(keys, g);
            BPAccountState::new_given_randomness(
                hash_identity::<PallasScalar>(IDENTITY),
                pk_aff,
                pk_enc,
                ASSET_ID,
                COUNTER,
                randomness,
                rho_randomness,
                get_poseidon2_params_for_2_1_hashing().unwrap(),
            )
            .unwrap()
            .commit(g.account_comm_key)
            .unwrap()
            .0
        }

        /// Whether `response` to `request` verifies against the registered `commitment`.
        fn verifies(
            response: &AccountRegistrationDeviceResponse,
            request: &RegistrationDeviceRequest,
            commitment: &PallasA,
            g: &DeviceGenerators,
        ) -> bool {
            let proof: BPAuthProofOnlySks = response.0.0.decode().unwrap();
            proof
                .verify_with_account_commitment(
                    PallasA::try_from(&request.pk_aff).unwrap(),
                    PallasA::try_from(&request.pk_enc).unwrap(),
                    commitment,
                    &ledger_nonce(&request.challenge_h_bytes, &request.nonce),
                    &request.txn_type.into(),
                    &g.sig_key_gen(),
                    &g.enc_key_gen(),
                    None,
                )
                .is_ok()
        }

        #[test]
        fn registration_proof_binds_seed_account() {
            let mut rng = rng_from_seed([0u8; 32]);
            let g = DeviceGenerators::new().unwrap();
            let (seed, keys) = seed_and_keys();
            let request = registration_request(&keys, &g);
            let response =
                create_registration_auth_proof(&mut rng, &keys, &seed, SEED_PATH, 0, &request, &g)
                    .unwrap();
            let (s, rr) = seed
                .derive_account_randomness::<PallasA>(SEED_PATH, 0, ASSET_ID, COUNTER)
                .unwrap();
            let seed_account = account_commitment(&keys, s, rr, &g);
            assert!(verifies(&response, &request, &seed_account, &g));

            // A registered commitment with host-chosen randomness, or with the seed's for another
            // counter, path or seed counter.
            let host_chosen = account_commitment(
                &keys,
                PallasScalar::rand(&mut rng),
                PallasScalar::rand(&mut rng),
                &g,
            );
            assert!(!verifies(&response, &request, &host_chosen, &g));
            let host_chosen_rho = account_commitment(&keys, s, PallasScalar::rand(&mut rng), &g);
            assert!(!verifies(&response, &request, &host_chosen_rho, &g));
            for (path, counter_s, counter) in [
                (SEED_PATH, 0, COUNTER + 1),
                (b"m/1".as_slice(), 0, COUNTER),
                (SEED_PATH, 1, COUNTER),
            ] {
                let (s, rr) = seed
                    .derive_account_randomness::<PallasA>(path, counter_s, ASSET_ID, counter)
                    .unwrap();
                assert!(!verifies(
                    &response,
                    &request,
                    &account_commitment(&keys, s, rr, &g),
                    &g
                ));
            }

            // The device shown another counter computes another account.
            let mut wrong_counter = request.clone();
            wrong_counter.counter = COUNTER + 1;
            let response = create_registration_auth_proof(
                &mut rng,
                &keys,
                &seed,
                SEED_PATH,
                0,
                &wrong_counter,
                &g,
            )
            .unwrap();
            assert!(!verifies(&response, &request, &seed_account, &g));
        }

        #[test]
        fn registration_rejects_small_order_randomness() {
            use ark_ff::FftField;
            let mut rng = rng_from_seed([0u8; 32]);
            let g = DeviceGenerators::new().unwrap();
            let (_, keys) = seed_and_keys();
            let request = registration_request(&keys, &g);
            let rho_randomness = PallasScalar::rand(&mut rng);
            let prove = |rng: &mut _, randomness| {
                create_registration_auth_proof_given_randomness(
                    rng,
                    &keys,
                    randomness,
                    rho_randomness,
                    &request,
                    &g,
                )
            };

            let randomness = PallasScalar::rand(&mut rng);
            prove(&mut rng, randomness).unwrap();
            for randomness in [
                PallasScalar::from(0u8),
                PallasScalar::from(1u8),
                -PallasScalar::from(1u8),
                PallasScalar::TWO_ADIC_ROOT_OF_UNITY,
            ] {
                assert!(prove(&mut rng, randomness).is_err());
            }
        }

        /// Fee registration request for a fee account of `key` at `COUNTER`.
        fn fee_registration_request(
            key: &AuthSigningKey,
            g: &DeviceGenerators,
        ) -> FeeAccountRegistrationDeviceRequest {
            let (_, pk) = keygen_sig_given_sk(key.sk, g.sig_key_gen());
            FeeAccountRegistrationDeviceRequest {
                challenge_h_bytes: vec![1u8; 32],
                nonce: IDENTITY.to_vec(),
                pk: CompressedAffine::try_from(pk.0).unwrap(),
                counter: COUNTER,
                txn_type: DeviceTxnType::FeeAccountRegistration {
                    asset_id: ASSET_ID,
                    balance: FEE_BALANCE,
                },
            }
        }

        /// Commitment to a new fee account of `key` opened with `initial_rho` and
        /// `initial_randomness`.
        fn fee_account_commitment(
            key: &AuthSigningKey,
            initial_rho: PallasScalar,
            initial_randomness: PallasScalar,
            g: &DeviceGenerators,
        ) -> PallasA {
            let (_, pk) = keygen_sig_given_sk(key.sk, g.sig_key_gen());
            BPFeeAccountState::new_given_randomness(
                pk.0,
                FEE_BALANCE,
                ASSET_ID,
                initial_rho,
                initial_randomness,
            )
            .unwrap()
            .commit(&g.account_comm_key)
            .unwrap()
            .0
        }

        /// Whether `response` to `request` verifies against the registered `commitment`.
        fn fee_verifies(
            response: &FeeAccountRegistrationDeviceResponse,
            request: &FeeAccountRegistrationDeviceRequest,
            commitment: &PallasA,
            g: &DeviceGenerators,
        ) -> bool {
            let proof: BPAuthProofOnlySk = response.0.0.decode().unwrap();
            proof
                .verify_with_account_commitment(
                    PallasA::try_from(&request.pk).unwrap(),
                    commitment,
                    &ledger_nonce(&request.challenge_h_bytes, &request.nonce),
                    &request.txn_type.into(),
                    &g.sig_key_gen(),
                    None,
                )
                .is_ok()
        }

        #[test]
        fn fee_registration_proof_binds_seed_account() {
            let mut rng = rng_from_seed([0u8; 32]);
            let g = DeviceGenerators::new().unwrap();
            let (seed, keys) = seed_and_keys();
            let key = AuthSigningKey { sk: keys.sk_aff };
            let request = fee_registration_request(&key, &g);
            let response = create_fee_account_registration_auth_proof(
                &mut rng, &key, &seed, SEED_PATH, 0, &request, &g,
            )
            .unwrap();
            let (initial_rho, initial_randomness) = seed
                .derive_fee_account_randomness::<PallasA>(SEED_PATH, 0, ASSET_ID, COUNTER)
                .unwrap();
            let seed_account = fee_account_commitment(&key, initial_rho, initial_randomness, &g);
            assert!(fee_verifies(&response, &request, &seed_account, &g));

            // A registered commitment with host-chosen randomness, or with the non-fee randomness
            // for the same input.
            let host_chosen = fee_account_commitment(
                &key,
                PallasScalar::rand(&mut rng),
                PallasScalar::rand(&mut rng),
                &g,
            );
            assert!(!fee_verifies(&response, &request, &host_chosen, &g));
            let (s, rr) = seed
                .derive_account_randomness::<PallasA>(SEED_PATH, 0, ASSET_ID, COUNTER)
                .unwrap();
            assert!(!fee_verifies(
                &response,
                &request,
                &fee_account_commitment(&key, s, rr, &g),
                &g
            ));

            // The device shown another counter computes another account.
            let mut wrong_counter = request.clone();
            wrong_counter.counter = COUNTER + 1;
            let response = create_fee_account_registration_auth_proof(
                &mut rng,
                &key,
                &seed,
                SEED_PATH,
                0,
                &wrong_counter,
                &g,
            )
            .unwrap();
            assert!(!fee_verifies(&response, &request, &seed_account, &g));
        }

        #[test]
        fn fee_registration_rejects_small_order_randomness() {
            use ark_ff::FftField;
            let mut rng = rng_from_seed([0u8; 32]);
            let g = DeviceGenerators::new().unwrap();
            let key = AuthSigningKey {
                sk: seed_and_keys().1.sk_aff,
            };
            let request = fee_registration_request(&key, &g);
            let prove = |rng: &mut _, initial_rho, initial_randomness| {
                create_fee_account_registration_auth_proof_given_randomness(
                    rng,
                    &key,
                    initial_rho,
                    initial_randomness,
                    &request,
                    &g,
                )
            };

            let (rho, s) = (PallasScalar::rand(&mut rng), PallasScalar::rand(&mut rng));
            prove(&mut rng, rho, s).unwrap();
            for small in [
                PallasScalar::from(0u8),
                PallasScalar::from(1u8),
                -PallasScalar::from(1u8),
                PallasScalar::TWO_ADIC_ROOT_OF_UNITY,
            ] {
                assert!(prove(&mut rng, small, s).is_err());
                assert!(prove(&mut rng, rho, small).is_err());
            }
        }
    }
}
