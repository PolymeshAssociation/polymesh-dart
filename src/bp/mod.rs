use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_ff::{
    PrimeField,
    field_hashers::{DefaultFieldHasher, HashToField},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;

use blake2::Blake2b512;
use bounded_collections::Get;
use bulletproofs::hash_to_curve_pasta::hash_to_pallas;
use digest::Digest;
use polymesh_dart_bp::poseidon_impls::poseidon_2::{
    Poseidon2Params, params::pallas::get_poseidon2_params_for_2_1_hashing,
};
use polymesh_dart_common::{
    MAX_ACCOUNT_ASSET_REG_PROOFS, MAX_ASSET_AUDITORS, MAX_ASSET_ENC_KEYS, MAX_ASSET_MEDIATORS,
    MAX_BATCHED_PROOFS, MAX_FEE_ACCOUNT_REG_PROOFS, MAX_FEE_ACCOUNT_TOPUP_PROOFS,
    MAX_INNER_PROOF_SIZE, MAX_KEYS_PER_REG_PROOF, MEMO_MAX_LENGTH, SETTLEMENT_MAX_LEGS,
};

#[cfg(feature = "sqlx")]
pub mod sqlx_impl;

pub mod encode;
pub use encode::{BoundedCanonical, CompressedAffine, WrappedCanonical};

mod account;
pub use account::*;

mod asset;
pub use asset::*;

mod batched;
pub use batched::*;

mod leg;
pub use leg::*;

mod keys;
pub use keys::*;

mod fee;
pub mod key_distribution_proof;

pub mod account_reg_split;
pub mod affirmation_proofs;
pub use affirmation_proofs::*;
pub mod auth_proofs;
pub mod fee_split;
pub use fee_split::*;
pub mod mint_split;
pub mod split_types;

use crate::curve_tree::{
    AccountTreeConfig, AssetTreeConfig, CompressedLeafValue, CurveTreeConfig, CurveTreeLookup,
    CurveTreeParameters, CurveTreePath, FeeAccountTreeConfig, ValidateCurveTreeRoot,
    get_asset_commitment_parameters, get_asset_curve_tree_parameters,
};
use crate::*;
pub use fee::*;
use polymesh_dart_bp::account::state::AccountCommitmentKeyTrait;

/// Use `GetExtra` as the trait bounds for pallet `Config` parameters
/// that will be used for bounded collections.
pub trait GetExtra<T>:
    Get<T> + Clone + core::fmt::Debug + Default + PartialEq + Eq + Send + Sync + 'static
{
}

/// ConstSize type wrapper.
///
/// This allows the use of Bounded collections in extrinsic parameters.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct ConstSize<const T: u32>;

impl<const T: u32> Get<u32> for ConstSize<T> {
    fn get() -> u32 {
        T
    }
}

impl<const T: u32> GetExtra<u32> for ConstSize<T> {}

pub trait DartLimits: Clone + core::fmt::Debug + PartialEq + Eq + Send + Sync + 'static {
    /// The maximum number of keys in an account registration proof.
    type MaxKeysPerRegProof: GetExtra<u32>;

    /// The maximum number of proofs in a single batched proof.
    type MaxBatchedProofs: GetExtra<u32>;

    /// The maximum number of fee account registration proofs in a single transaction.
    type MaxFeeAccountRegProofs: GetExtra<u32>;

    /// The maximum number of fee account topup proofs in a single transaction.
    type MaxFeeAccountTopupProofs: GetExtra<u32>;

    /// The maximum number of account asset registration proofs in a single transaction.
    type MaxAccountAssetRegProofs: GetExtra<u32>;

    /// The maximum number of legs in a settlement.
    type MaxSettlementLegs: GetExtra<u32>;

    /// The maximum settlement memo length.
    type MaxSettlementMemoLength: GetExtra<u32>;

    /// The maximum number of asset auditors.
    type MaxAssetAuditors: GetExtra<u32>;

    /// The maximum number of asset mediators.
    type MaxAssetMediators: GetExtra<u32>;

    /// The maximum number of asset encryption keys (for both auditors and mediators) in the asset state.
    type MaxAssetEncryptionKeys: GetExtra<u32>;

    /// The maximum inner proof size.
    type MaxInnerProofSize: GetExtra<u32>;
}

impl DartLimits for () {
    type MaxKeysPerRegProof = ConstSize<500>;
    type MaxBatchedProofs = ConstSize<MAX_BATCHED_PROOFS>;
    type MaxFeeAccountRegProofs = ConstSize<MAX_FEE_ACCOUNT_REG_PROOFS>;
    type MaxFeeAccountTopupProofs = ConstSize<MAX_FEE_ACCOUNT_TOPUP_PROOFS>;
    type MaxAccountAssetRegProofs = ConstSize<200>;
    type MaxSettlementLegs = ConstSize<SETTLEMENT_MAX_LEGS>;
    type MaxSettlementMemoLength = ConstSize<MEMO_MAX_LENGTH>;
    type MaxAssetAuditors = ConstSize<MAX_ASSET_AUDITORS>;
    type MaxAssetMediators = ConstSize<MAX_ASSET_MEDIATORS>;
    type MaxAssetEncryptionKeys = ConstSize<MAX_ASSET_ENC_KEYS>;
    type MaxInnerProofSize = ConstSize<MAX_INNER_PROOF_SIZE>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolymeshLimits;

impl DartLimits for PolymeshLimits {
    type MaxKeysPerRegProof = ConstSize<MAX_KEYS_PER_REG_PROOF>;
    type MaxBatchedProofs = ConstSize<MAX_BATCHED_PROOFS>;
    type MaxFeeAccountRegProofs = ConstSize<MAX_FEE_ACCOUNT_REG_PROOFS>;
    type MaxFeeAccountTopupProofs = ConstSize<MAX_FEE_ACCOUNT_TOPUP_PROOFS>;
    type MaxAccountAssetRegProofs = ConstSize<MAX_ACCOUNT_ASSET_REG_PROOFS>;
    type MaxSettlementLegs = ConstSize<SETTLEMENT_MAX_LEGS>;
    type MaxSettlementMemoLength = ConstSize<MEMO_MAX_LENGTH>;
    type MaxAssetAuditors = ConstSize<MAX_ASSET_AUDITORS>;
    type MaxAssetMediators = ConstSize<MAX_ASSET_MEDIATORS>;
    type MaxAssetEncryptionKeys = ConstSize<MAX_ASSET_ENC_KEYS>;
    type MaxInnerProofSize = ConstSize<MAX_INNER_PROOF_SIZE>;
}

pub type LeafIndex = u64;
pub type TreeIndex = u8;
pub type NodeLevel = u8;
pub type NodeIndex = LeafIndex;
pub type ChildIndex = LeafIndex;

pub type PallasParameters = ark_pallas::PallasConfig;
pub type VestaParameters = ark_vesta::VestaConfig;
pub type PallasA = ark_pallas::Affine;
pub type PallasScalar = <PallasA as AffineRepr>::ScalarField;
pub type VestaA = ark_vesta::Affine;
pub type VestaScalar = <VestaA as AffineRepr>::ScalarField;

pub const ACCOUNT_IDENTITY_LABEL: &[u8; 16] = b"account-identity";
pub(crate) fn hash_identity<F: PrimeField>(did: &[u8]) -> F {
    let hasher = <DefaultFieldHasher<Blake2b512> as HashToField<F>>::new(ACCOUNT_IDENTITY_LABEL);
    let r = hasher.hash_to_field::<1>(&did);
    r[0]
}

/// Constants that are hashed to generate the generators for the Dart BP protocol.
pub const DART_GEN_DOMAIN: &'static [u8] = b"polymesh-dart-generators";
pub const DART_GEN_ACCOUNT_KEY: &'static [u8] = b"polymesh-dart-account-key";
pub const DART_GEN_ASSET_KEY: &'static [u8] = b"polymesh-dart-asset-key";
pub const DART_GEN_ENC_KEY: &'static [u8] = b"polymesh-dart-pk-enc";

#[cfg(feature = "std")]
lazy_static::lazy_static! {
    pub static ref DART_GENS: DartBPGenerators = DartBPGenerators::new(DART_GEN_DOMAIN);

    pub static ref POSEIDON_PARAMS: PoseidonParameters = PoseidonParameters::new().expect("Failed to create Poseidon parameters");
}

#[cfg(feature = "std")]
pub fn set_dart_gens(_gens: DartBPGenerators) {}

#[cfg(feature = "std")]
pub fn dart_gens() -> &'static DartBPGenerators {
    &DART_GENS
}

#[cfg(not(feature = "std"))]
static mut DART_GENS: Option<DartBPGenerators> = None;

#[cfg(not(feature = "std"))]
#[allow(static_mut_refs)]
pub fn set_dart_gens(gens: DartBPGenerators) {
    unsafe {
        DART_GENS = Some(gens);
    }
}

#[cfg(not(feature = "std"))]
#[allow(static_mut_refs)]
pub fn dart_gens() -> &'static DartBPGenerators {
    unsafe {
        if DART_GENS.is_none() {
            set_dart_gens(DartBPGenerators::new(DART_GEN_DOMAIN));
        }
        DART_GENS.as_ref().unwrap()
    }
}

#[cfg(feature = "std")]
pub fn set_poseidon_params(_params: PoseidonParameters) {}

#[cfg(feature = "std")]
pub fn poseidon_params() -> &'static PoseidonParameters {
    &POSEIDON_PARAMS
}

#[cfg(not(feature = "std"))]
static mut POSEIDON_PARAMS: Option<PoseidonParameters> = None;

#[cfg(not(feature = "std"))]
#[allow(static_mut_refs)]
pub fn set_poseidon_params(params: PoseidonParameters) {
    unsafe {
        POSEIDON_PARAMS = Some(params);
    }
}

#[cfg(not(feature = "std"))]
#[allow(static_mut_refs)]
pub fn poseidon_params() -> &'static PoseidonParameters {
    unsafe {
        if POSEIDON_PARAMS.is_none() {
            set_poseidon_params(
                PoseidonParameters::new().expect("Failed to create Poseidon parameters"),
            );
        }
        POSEIDON_PARAMS.as_ref().unwrap()
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PoseidonParameters {
    pub params: Poseidon2Params<PallasScalar>,
}

impl PoseidonParameters {
    pub fn new() -> Result<Self, Error> {
        Ok(Self {
            params: get_poseidon2_params_for_2_1_hashing()?,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountCommitmentKey {
    pub sk_gen: PallasA,
    pub balance_gen: PallasA,
    pub counter_gen: PallasA,
    pub asset_id_gen: PallasA,
    pub rho_gen: PallasA,
    pub current_rho_gen: PallasA,
    pub randomness_gen: PallasA,
    pub current_randomness_gen: PallasA,
    pub identity_gen: PallasA,
    pub sk_enc_gen: PallasA,
}

impl AccountCommitmentKey {
    /// Create a new account commitment key
    pub fn new<D: Digest>(label: &[u8], sk_gen: PallasA, enc_key_gen: PallasA) -> Self {
        let balance_gen = hash_to_pallas(label, b" : balance_gen").into_affine();
        let counter_gen = hash_to_pallas(label, b" : counter_gen").into_affine();
        let asset_id_gen = hash_to_pallas(label, b" : asset_id_gen").into_affine();
        let rho_gen = hash_to_pallas(label, b" : rho_gen").into_affine();
        let current_rho_gen = hash_to_pallas(label, b" : current_rho_gen").into_affine();
        let randomness_gen = hash_to_pallas(label, b" : randomness_gen").into_affine();
        let current_randomness_gen =
            hash_to_pallas(label, b" : current_randomness_gen").into_affine();
        let identity_gen = hash_to_pallas(label, b" : identity_gen").into_affine();
        let sk_enc_gen = enc_key_gen;

        Self {
            sk_gen,
            balance_gen,
            counter_gen,
            asset_id_gen,
            rho_gen,
            current_rho_gen,
            randomness_gen,
            current_randomness_gen,
            identity_gen,
            sk_enc_gen,
        }
    }
}

impl AccountCommitmentKeyTrait<PallasA> for AccountCommitmentKey {
    fn sk_gen(&self) -> PallasA {
        self.sk_gen
    }

    fn balance_gen(&self) -> PallasA {
        self.balance_gen
    }

    fn counter_gen(&self) -> PallasA {
        self.counter_gen
    }

    fn asset_id_gen(&self) -> PallasA {
        self.asset_id_gen
    }

    fn rho_gen(&self) -> PallasA {
        self.rho_gen
    }

    fn current_rho_gen(&self) -> PallasA {
        self.current_rho_gen
    }

    fn randomness_gen(&self) -> PallasA {
        self.randomness_gen
    }

    fn current_randomness_gen(&self) -> PallasA {
        self.current_randomness_gen
    }

    fn id_gen(&self) -> PallasA {
        self.identity_gen
    }

    fn sk_enc_gen(&self) -> PallasA {
        self.sk_enc_gen
    }
}

/// The generators for the Dart BP protocol.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct DartBPGenerators {
    sig_key_gen: PallasA,
    enc_key_gen: PallasA,
    account_comm_key: AccountCommitmentKey,
    leg_asset_value_gen: PallasA,
}

impl DartBPGenerators {
    /// Creates a new instance of `DartBPGenerators` by generating the necessary generators.
    pub fn new(label: &[u8]) -> Self {
        let sig_key_gen = hash_to_pallas(label, b" : sig_key_gen").into_affine();
        let enc_key_gen = hash_to_pallas(label, b" : enc_key_gen").into_affine();

        let account_comm_key =
            AccountCommitmentKey::new::<Blake2b512>(DART_GEN_ACCOUNT_KEY, sig_key_gen, enc_key_gen);

        let leg_asset_value_gen = hash_to_pallas(label, b" : leg_asset_value_gen").into_affine();

        Self {
            sig_key_gen,
            enc_key_gen,
            account_comm_key,
            leg_asset_value_gen,
        }
    }

    /// Returns the generators for account state commitments.
    pub fn account_comm_key(&self) -> AccountCommitmentKey {
        self.account_comm_key
    }

    pub fn sig_key_gen(&self) -> PallasA {
        self.sig_key_gen
    }

    pub fn enc_key_gen(&self) -> PallasA {
        self.enc_key_gen
    }

    pub fn leg_asset_value_gen(&self) -> PallasA {
        self.leg_asset_value_gen
    }
}

pub(crate) fn try_block_number<T: TryInto<BlockNumber>>(
    block_number: T,
) -> Result<BlockNumber, Error> {
    block_number
        .try_into()
        .map_err(|_| Error::CurveTreeBlockNumberNotFound)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account_reg_split::AccountRegHostProtocol;
    use crate::affirmation_proofs::{
        ClaimReceivedHostProtocol, InstantReceiverAffirmationHostProtocol,
        InstantSenderAffirmationHostProtocol, ReceiverAffirmationHostProtocol,
        ReceiverCounterUpdateHostProtocol, SenderAffirmationHostProtocol,
        SenderCounterUpdateHostProtocol, SenderReverseHostProtocol,
    };
    use crate::auth_proofs::{
        create_affirmation_auth_proof, create_fee_account_auth_proof,
        create_fee_payment_auth_proof, create_registration_auth_proof,
    };
    use crate::curve_tree::ProverCurveTree;
    use crate::fee_split::{FeePaymentHostProtocol, FeeRegHostProtocol, FeeTopupHostProtocol};
    use crate::mint_split::MintHostProtocol;
    use crate::split_types::{AffirmationDeviceRequest, AffirmationDeviceResponse};
    use ark_ec::short_weierstrass::Affine;
    use bounded_collections::BoundedVec;
    use polymesh_dart_common::NullifierSkGenCounter;
    use rand_core::SeedableRng;

    #[test]
    fn test_dart_bp_generators_encode_decode() {
        let gens = dart_gens().clone();

        let mut encoded = Vec::new();
        gens.serialize_uncompressed(&mut encoded).unwrap();
        let decoded: DartBPGenerators =
            CanonicalDeserialize::deserialize_uncompressed(&encoded[..]).unwrap();
        assert_eq!(gens, decoded);
    }

    #[test]
    fn test_fee_reg_split() {
        let mut rng = rand::thread_rng();
        let ctx = b"test-fee-reg-split";

        let keys = AccountKeys::rand(&mut rng).unwrap();
        let asset_id: AssetId = 0;
        let balance: Balance = 1000;

        let account_state =
            FeeAccountAssetState::new(&mut rng, &keys.acct.public, asset_id, balance).unwrap();

        let (protocol, device_request) =
            FeeRegHostProtocol::init(&mut rng, &keys.acct.public, &account_state, ctx).unwrap();

        let device_response = create_fee_account_auth_proof(
            &mut rng,
            &keys.acct,
            &device_request,
            dart_gens().account_comm_key().sk_gen(),
        )
        .unwrap();

        let proof = protocol.finish::<()>(&device_response).unwrap();

        proof.verify(ctx).unwrap();
    }

    #[test]
    fn test_fee_topup_split() {
        let mut rng = rand::thread_rng();
        let ctx = b"test-fee-topup-split";

        let keys = AccountKeys::rand(&mut rng).unwrap();
        let asset_id: AssetId = 0;
        let initial_balance: Balance = 1000;
        let topup_amount: Balance = 500;

        let mut account_state =
            FeeAccountAssetState::new(&mut rng, &keys.acct.public, asset_id, initial_balance)
                .unwrap();

        let mut fee_tree =
            ProverCurveTree::<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>::new(
                FEE_ACCOUNT_TREE_HEIGHT,
            )
            .unwrap();
        let leaf = account_state
            .current_commitment()
            .unwrap()
            .as_leaf_value()
            .unwrap();
        fee_tree.insert(leaf).unwrap();
        fee_tree.store_root().unwrap();

        let (protocol, device_request) = FeeTopupHostProtocol::<FeeAccountTreeConfig>::init(
            &mut rng,
            &keys.acct.public,
            &mut account_state,
            topup_amount,
            ctx,
            &fee_tree,
        )
        .unwrap();

        let device_response = create_fee_account_auth_proof(
            &mut rng,
            &keys.acct,
            &device_request,
            dart_gens().account_comm_key().sk_gen(),
        )
        .unwrap();

        let tree_params = FeeAccountTreeConfig::parameters();
        let proof = protocol
            .finish::<_, ()>(&mut rng, &device_response, tree_params)
            .unwrap();

        let root = fee_tree.root().unwrap().root_node().unwrap();
        proof.verify(&mut rng, ctx, &root).unwrap();
    }

    #[test]
    fn test_fee_payment_split() {
        let mut rng = rand::thread_rng();
        let ctx = b"test-fee-payment-split";

        let keys = AccountKeys::rand(&mut rng).unwrap();
        let asset_id: AssetId = 0;
        let initial_balance: Balance = 1000;
        let topup_amount: Balance = 500;
        let payment_amount: Balance = 100;

        let mut fee_state =
            FeeAccountAssetState::new(&mut rng, &keys.acct.public, asset_id, initial_balance)
                .unwrap();

        let mut fee_tree =
            ProverCurveTree::<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>::new(
                FEE_ACCOUNT_TREE_HEIGHT,
            )
            .unwrap();
        let leaf = fee_state
            .current_commitment()
            .unwrap()
            .as_leaf_value()
            .unwrap();
        fee_tree.insert(leaf).unwrap();
        fee_tree.store_root().unwrap();

        let topup_proof = FeeAccountTopupProof::<()>::new(
            &mut rng,
            &keys.acct,
            &mut fee_state,
            topup_amount,
            ctx,
            &fee_tree,
        )
        .unwrap();
        fee_state.commit_pending_state().unwrap();

        let leaf = topup_proof
            .updated_account_state_commitment
            .as_leaf_value()
            .unwrap();
        fee_tree.insert(leaf).unwrap();
        fee_tree.store_root().unwrap();

        let (protocol, device_request) = FeePaymentHostProtocol::<FeeAccountTreeConfig>::init(
            &mut rng,
            &mut fee_state,
            payment_amount,
            ctx,
            &fee_tree,
        )
        .unwrap();

        let gens = dart_gens();
        let tree_params_for_gens = FeeAccountTreeConfig::parameters();
        let comm_re_rand_gen = tree_params_for_gens
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;
        let device_response = create_fee_payment_auth_proof(
            &mut rng,
            &keys.acct,
            &device_request,
            gens.account_comm_key().sk_gen(),
            gens.account_comm_key().randomness_gen(),
            comm_re_rand_gen,
        )
        .unwrap();

        let root = fee_tree.root().unwrap();
        let root_block = fee_tree.get_block_number().unwrap();
        let tree_params = FeeAccountTreeConfig::parameters();
        let proof = protocol
            .finish::<_, ()>(&mut rng, &device_response, root_block, tree_params)
            .unwrap();

        proof.verify(&mut rng, ctx, root).unwrap();
    }

    #[test]
    fn test_account_reg_split() {
        let mut rng = rand::thread_rng();
        let ctx = b"test-account-reg-split";
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;

        let tree_params = AccountTreeConfig::parameters();

        let keys = AccountKeys::rand(&mut rng).unwrap();

        let (account_state, rho_randomness) =
            keys.init_asset_state(asset_id, counter, ctx).unwrap();

        let (protocol, device_request) =
            AccountRegHostProtocol::init(&mut rng, &account_state, rho_randomness, counter, ctx)
                .unwrap();

        let gens = dart_gens();
        let device_response = create_registration_auth_proof(
            &mut rng,
            &keys,
            &device_request,
            gens.account_comm_key().sk_gen(),
            gens.account_comm_key().sk_enc_gen(),
        )
        .unwrap();

        let proof: AccountAssetRegistrationProof<()> = protocol
            .finish(&mut rng, &device_response, counter, tree_params)
            .unwrap();

        proof.verify(ctx, tree_params, &mut rng).unwrap();
    }

    #[test]
    fn test_batched_account_reg_split() {
        let mut rng = rand::rngs::StdRng::from_entropy();
        let ctx = b"test-batched-account-reg-split";
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;

        let tree_params = AccountTreeConfig::parameters();

        let keys1 = AccountKeys::rand(&mut rng).unwrap();
        let keys2 = AccountKeys::rand(&mut rng).unwrap();

        let (account_state1, rho_randomness1) =
            keys1.init_asset_state(asset_id, counter, ctx).unwrap();
        let (account_state2, rho_randomness2) =
            keys2.init_asset_state(asset_id, counter, ctx).unwrap();

        let (protocol1, device_request1) =
            AccountRegHostProtocol::init(&mut rng, &account_state1, rho_randomness1, counter, ctx)
                .unwrap();
        let (protocol2, device_request2) =
            AccountRegHostProtocol::init(&mut rng, &account_state2, rho_randomness2, counter, ctx)
                .unwrap();

        let gens = dart_gens();
        let device_response1 = create_registration_auth_proof(
            &mut rng,
            &keys1,
            &device_request1,
            gens.account_comm_key().sk_gen(),
            gens.account_comm_key().sk_enc_gen(),
        )
        .unwrap();
        let device_response2 = create_registration_auth_proof(
            &mut rng,
            &keys2,
            &device_request2,
            gens.account_comm_key().sk_gen(),
            gens.account_comm_key().sk_enc_gen(),
        )
        .unwrap();

        let proof1 = protocol1
            .finish(&mut rng, &device_response1, counter, tree_params)
            .unwrap();
        let proof2 = protocol2
            .finish(&mut rng, &device_response2, counter, tree_params)
            .unwrap();

        let batched: BatchedAccountAssetRegistrationProof = BatchedAccountAssetRegistrationProof {
            proofs: {
                let mut proofs = BoundedVec::new();
                proofs.try_push(proof1).unwrap();
                proofs.try_push(proof2).unwrap();
                proofs
            },
        };

        batched.verify(ctx, tree_params, &mut rng).unwrap();
    }

    #[test]
    fn test_mint_split() {
        let mut rng = rand::thread_rng();
        let ctx = b"test-mint-split";
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;
        let mint_amount: Balance = 500;

        let keys = AccountKeys::rand(&mut rng).unwrap();
        let pk = keys.public_keys();

        let (mut account_state, _) = keys.init_asset_state(asset_id, counter, ctx).unwrap();

        let mut account_tree =
            ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
                ACCOUNT_TREE_HEIGHT,
            )
            .unwrap();
        let leaf = account_state
            .current_commitment()
            .unwrap()
            .as_leaf_value()
            .unwrap();
        account_tree.insert(leaf).unwrap();
        account_tree.store_root().unwrap();

        let (protocol, device_request) = MintHostProtocol::<AccountTreeConfig>::init(
            &mut rng,
            &pk,
            &mut account_state,
            mint_amount,
            ctx,
            &account_tree,
        )
        .unwrap();

        let gens = dart_gens();
        let device_response = create_registration_auth_proof(
            &mut rng,
            &keys,
            &device_request,
            gens.account_comm_key().sk_gen(),
            gens.account_comm_key().sk_enc_gen(),
        )
        .unwrap();

        let root = account_tree.root().unwrap();
        let root_block = account_tree.get_block_number().unwrap();
        let tree_params = AccountTreeConfig::parameters();
        let proof: AssetMintingProof<()> = protocol
            .finish(&mut rng, &device_response, root_block, tree_params)
            .unwrap();

        proof.verify(ctx, root, &mut rng).unwrap();
    }

    fn make_affirmation_device_response<R: rand_core::RngCore + rand_core::CryptoRng>(
        rng: &mut R,
        keys: &AccountKeys,
        request: &AffirmationDeviceRequest,
        comm_re_rand_gen: Affine<PallasParameters>,
    ) -> AffirmationDeviceResponse {
        let gens = dart_gens();
        create_affirmation_auth_proof(
            rng,
            keys,
            request,
            gens.account_comm_key().sk_gen(),
            gens.enc_key_gen(),
            comm_re_rand_gen,
            gens.leg_asset_value_gen(),
        )
        .unwrap()
    }

    fn make_leg_and_tree_with_config<R: rand_core::RngCore + rand_core::CryptoRng>(
        rng: &mut R,
        sender_enc: EncryptionPublicKey,
        receiver_enc: EncryptionPublicKey,
        asset_id: AssetId,
        amount: Balance,
        reveal_asset_id: bool,
        state_leaf: AccountStateCommitment,
    ) -> (
        LegEncrypted,
        LegRef,
        ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
    ) {
        let leg = Leg::new(sender_enc, receiver_enc, asset_id, amount).unwrap();
        let mut leg_config = LegConfig::default();
        leg_config.reveal_asset_id = reveal_asset_id;
        let (_, leg_enc, _) = leg
            .encrypt(rng, leg_config.into(), vec![], vec![], vec![])
            .unwrap();
        let leg_ref = LegRef::new(SettlementRef([1; 32]), 0);
        let mut tree = ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
            ACCOUNT_TREE_HEIGHT,
        )
        .unwrap();
        let leaf = state_leaf.as_leaf_value().unwrap();
        tree.insert(leaf).unwrap();
        tree.store_root().unwrap();
        (leg_enc, leg_ref, tree)
    }

    fn make_leg_and_tree<R: rand_core::RngCore + rand_core::CryptoRng>(
        rng: &mut R,
        sender_enc: EncryptionPublicKey,
        receiver_enc: EncryptionPublicKey,
        asset_id: AssetId,
        amount: Balance,
        state_leaf: AccountStateCommitment,
    ) -> (
        LegEncrypted,
        LegRef,
        ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
    ) {
        make_leg_and_tree_with_config(
            rng,
            sender_enc,
            receiver_enc,
            asset_id,
            amount,
            false,
            state_leaf,
        )
    }

    #[test]
    fn test_sender_affirmation_split() {
        let test_with_config = |reveal_asset_id: bool| {
            let mut rng = rand::thread_rng();
            let asset_id: AssetId = 1;
            let counter: NullifierSkGenCounter = 0;
            let ctx: &[u8] = if reveal_asset_id {
                b"test-sender-affirm-split-revealed"
            } else {
                b"test-sender-affirm-split"
            };
            let mint_amount: Balance = 1000;
            let send_amount: Balance = 300;

            let sender_keys = AccountKeys::rand(&mut rng).unwrap();
            let receiver_keys = AccountKeys::rand(&mut rng).unwrap();

            let (mut sender_state, _) = sender_keys
                .init_asset_state(asset_id, counter, ctx)
                .unwrap();
            sender_state.current_state.balance = mint_amount;

            let leaf = sender_state.current_commitment().unwrap();
            let (leg_enc, leg_ref, account_tree) = make_leg_and_tree_with_config(
                &mut rng,
                sender_keys.enc.public,
                receiver_keys.enc.public,
                asset_id,
                send_amount,
                reveal_asset_id,
                leaf,
            );

            let (protocol, device_request) =
                SenderAffirmationHostProtocol::<AccountTreeConfig>::init(
                    &mut rng,
                    &mut sender_state,
                    &leg_ref,
                    &leg_enc,
                    send_amount,
                    &account_tree,
                )
                .unwrap();

            if reveal_asset_id {
                assert!(device_request.k_asset_ids.is_empty());
            } else {
                assert_eq!(device_request.k_asset_ids.len(), 1);
            }

            let tree_params = AccountTreeConfig::parameters();
            let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;
            let device_response = make_affirmation_device_response(
                &mut rng,
                &sender_keys,
                &device_request,
                comm_re_rand_gen,
            );

            let proof = protocol
                .finish::<_, ()>(&mut rng, &device_response)
                .unwrap();

            let root = account_tree.root().unwrap();
            proof.verify(&leg_enc, &root, &mut rng).unwrap();
        };

        test_with_config(false);
        test_with_config(true);
    }

    #[test]
    fn test_receiver_affirmation_split() {
        let test_with_config = |reveal_asset_id: bool| {
            let mut rng = rand::thread_rng();
            let asset_id: AssetId = 1;
            let counter: NullifierSkGenCounter = 0;
            let ctx: &[u8] = if reveal_asset_id {
                b"test-receiver-affirm-split-revealed"
            } else {
                b"test-receiver-affirm-split"
            };
            let receive_amount: Balance = 300;

            let sender_keys = AccountKeys::rand(&mut rng).unwrap();
            let receiver_keys = AccountKeys::rand(&mut rng).unwrap();

            let (mut receiver_state, _) = receiver_keys
                .init_asset_state(asset_id, counter, ctx)
                .unwrap();

            let leaf = receiver_state.current_commitment().unwrap();
            let (leg_enc, leg_ref, account_tree) = make_leg_and_tree_with_config(
                &mut rng,
                sender_keys.enc.public,
                receiver_keys.enc.public,
                asset_id,
                receive_amount,
                reveal_asset_id,
                leaf,
            );

            let (protocol, device_request) =
                ReceiverAffirmationHostProtocol::<AccountTreeConfig>::init(
                    &mut rng,
                    &mut receiver_state,
                    &leg_ref,
                    &leg_enc,
                    &account_tree,
                )
                .unwrap();

            if reveal_asset_id {
                assert!(device_request.k_asset_ids.is_empty());
            } else {
                assert_eq!(device_request.k_asset_ids.len(), 1);
            }

            let tree_params = AccountTreeConfig::parameters();
            let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;
            let device_response = make_affirmation_device_response(
                &mut rng,
                &receiver_keys,
                &device_request,
                comm_re_rand_gen,
            );

            let proof = protocol
                .finish::<_, ()>(&mut rng, &device_response)
                .unwrap();

            let root = account_tree.root().unwrap();
            proof.verify(&leg_enc, &root, &mut rng).unwrap();
        };

        test_with_config(false);
        test_with_config(true);
    }

    #[test]
    fn test_claim_received_split() {
        let mut rng = rand::thread_rng();
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;
        let ctx = b"test-claim-received-split";
        let claim_amount: Balance = 300;

        let sender_keys = AccountKeys::rand(&mut rng).unwrap();
        let receiver_keys = AccountKeys::rand(&mut rng).unwrap();

        let (mut receiver_state, _) = receiver_keys
            .init_asset_state(asset_id, counter, ctx)
            .unwrap();
        receiver_state.current_state.counter = 1;

        let leaf = receiver_state.current_commitment().unwrap();
        let (leg_enc, leg_ref, account_tree) = make_leg_and_tree(
            &mut rng,
            sender_keys.enc.public,
            receiver_keys.enc.public,
            asset_id,
            claim_amount,
            leaf,
        );

        let (protocol, device_request) = ClaimReceivedHostProtocol::<AccountTreeConfig>::init(
            &mut rng,
            &mut receiver_state,
            &leg_ref,
            &leg_enc,
            claim_amount,
            &account_tree,
        )
        .unwrap();

        let tree_params = AccountTreeConfig::parameters();
        let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;

        let device_response = make_affirmation_device_response(
            &mut rng,
            &receiver_keys,
            &device_request,
            comm_re_rand_gen,
        );
        let proof = protocol
            .finish::<_, ()>(&mut rng, &device_response)
            .unwrap();

        let root = account_tree.root().unwrap();
        proof.verify(&leg_enc, &root, &mut rng).unwrap();
    }

    #[test]
    fn test_sender_reverse_split() {
        let mut rng = rand::thread_rng();
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;
        let ctx = b"test-sender-reverse-split";
        let reverse_amount: Balance = 300;

        let sender_keys = AccountKeys::rand(&mut rng).unwrap();
        let receiver_keys = AccountKeys::rand(&mut rng).unwrap();

        let (mut sender_state, _) = sender_keys
            .init_asset_state(asset_id, counter, ctx)
            .unwrap();
        sender_state.current_state.counter = 1;

        let leaf = sender_state.current_commitment().unwrap();
        let (leg_enc, leg_ref, account_tree) = make_leg_and_tree(
            &mut rng,
            sender_keys.enc.public,
            receiver_keys.enc.public,
            asset_id,
            reverse_amount,
            leaf,
        );

        let (protocol, device_request) = SenderReverseHostProtocol::<AccountTreeConfig>::init(
            &mut rng,
            &mut sender_state,
            &leg_ref,
            &leg_enc,
            reverse_amount,
            &account_tree,
        )
        .unwrap();

        let tree_params = AccountTreeConfig::parameters();
        let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;

        let device_response = make_affirmation_device_response(
            &mut rng,
            &sender_keys,
            &device_request,
            comm_re_rand_gen,
        );
        let proof = protocol
            .finish::<_, ()>(&mut rng, &device_response)
            .unwrap();

        let root = account_tree.root().unwrap();
        proof.verify(&leg_enc, &root, &mut rng).unwrap();
    }

    #[test]
    fn test_sender_counter_update_split() {
        let mut rng = rand::thread_rng();
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;
        let ctx = b"test-sender-counter-update";

        let sender_keys = AccountKeys::rand(&mut rng).unwrap();
        let receiver_keys = AccountKeys::rand(&mut rng).unwrap();

        let (mut sender_state, _) = sender_keys
            .init_asset_state(asset_id, counter, ctx)
            .unwrap();
        sender_state.current_state.counter = 1;

        let leaf = sender_state.current_commitment().unwrap();

        let (leg_enc, leg_ref, account_tree) = make_leg_and_tree(
            &mut rng,
            sender_keys.enc.public,
            receiver_keys.enc.public,
            asset_id,
            0,
            leaf,
        );

        let (protocol, device_request) =
            SenderCounterUpdateHostProtocol::<AccountTreeConfig>::init(
                &mut rng,
                &mut sender_state,
                &leg_ref,
                &leg_enc,
                &account_tree,
            )
            .unwrap();

        let tree_params = AccountTreeConfig::parameters();
        let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;

        let device_response = make_affirmation_device_response(
            &mut rng,
            &sender_keys,
            &device_request,
            comm_re_rand_gen,
        );
        let proof = protocol
            .finish::<_, ()>(&mut rng, &device_response)
            .unwrap();

        let root = account_tree.root().unwrap();
        proof.verify(&leg_enc, &root, &mut rng).unwrap();
    }

    #[test]
    fn test_receiver_counter_update_split() {
        let mut rng = rand::thread_rng();
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;
        let ctx = b"test-receiver-counter-update";

        let sender_keys = AccountKeys::rand(&mut rng).unwrap();
        let receiver_keys = AccountKeys::rand(&mut rng).unwrap();

        let (mut receiver_state, _) = receiver_keys
            .init_asset_state(asset_id, counter, ctx)
            .unwrap();
        receiver_state.current_state.counter = 1;

        let leg = Leg::new(
            sender_keys.enc.public,
            receiver_keys.enc.public,
            asset_id,
            0,
        )
        .unwrap();
        let (_, leg_enc, _) = leg
            .encrypt(
                &mut rng,
                LegConfig::default().into(),
                vec![],
                vec![],
                vec![],
            )
            .unwrap();
        let leg_ref = LegRef::new(SettlementRef([8u8; 32]), 0);

        let mut account_tree =
            ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
                ACCOUNT_TREE_HEIGHT,
            )
            .unwrap();
        let leaf = receiver_state
            .current_commitment()
            .unwrap()
            .as_leaf_value()
            .unwrap();
        account_tree.insert(leaf).unwrap();
        account_tree.store_root().unwrap();

        let (protocol, device_request) =
            ReceiverCounterUpdateHostProtocol::<AccountTreeConfig>::init(
                &mut rng,
                &mut receiver_state,
                &leg_ref,
                &leg_enc,
                &account_tree,
            )
            .unwrap();

        let tree_params = AccountTreeConfig::parameters();
        let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;

        let device_response = make_affirmation_device_response(
            &mut rng,
            &receiver_keys,
            &device_request,
            comm_re_rand_gen,
        );
        let proof = protocol
            .finish::<_, ()>(&mut rng, &device_response)
            .unwrap();

        let root = account_tree.root().unwrap();
        proof.verify(&leg_enc, &root, &mut rng).unwrap();
    }

    #[test]
    fn test_instant_sender_affirmation_split() {
        let mut rng = rand::thread_rng();
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;
        let ctx = b"test-instant-sender-affirm";
        let send_amount: Balance = 300;

        let sender_keys = AccountKeys::rand(&mut rng).unwrap();
        let receiver_keys = AccountKeys::rand(&mut rng).unwrap();

        let (mut sender_state, _) = sender_keys
            .init_asset_state(asset_id, counter, ctx)
            .unwrap();
        sender_state.current_state.balance = 1000;

        let leaf = sender_state.current_commitment().unwrap();
        let (leg_enc, leg_ref, account_tree) = make_leg_and_tree(
            &mut rng,
            sender_keys.enc.public,
            receiver_keys.enc.public,
            asset_id,
            send_amount,
            leaf,
        );

        let (protocol, device_request) =
            InstantSenderAffirmationHostProtocol::<AccountTreeConfig>::init(
                &mut rng,
                &mut sender_state,
                &leg_ref,
                &leg_enc,
                send_amount,
                &account_tree,
            )
            .unwrap();

        let tree_params = AccountTreeConfig::parameters();
        let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;

        let device_response = make_affirmation_device_response(
            &mut rng,
            &sender_keys,
            &device_request,
            comm_re_rand_gen,
        );
        let proof = protocol
            .finish::<_, ()>(&mut rng, &device_response)
            .unwrap();

        let root = account_tree.root().unwrap();
        proof.verify(&leg_enc, &root, &mut rng).unwrap();
    }

    #[test]
    fn test_instant_receiver_affirmation_split() {
        let mut rng = rand::thread_rng();
        let asset_id: AssetId = 1;
        let counter: NullifierSkGenCounter = 0;
        let ctx = b"test-instant-receiver-affirm";
        let receive_amount: Balance = 300;

        let sender_keys = AccountKeys::rand(&mut rng).unwrap();
        let receiver_keys = AccountKeys::rand(&mut rng).unwrap();

        let (mut receiver_state, _) = receiver_keys
            .init_asset_state(asset_id, counter, ctx)
            .unwrap();

        let leaf = receiver_state.current_commitment().unwrap();
        let (leg_enc, leg_ref, account_tree) = make_leg_and_tree(
            &mut rng,
            sender_keys.enc.public,
            receiver_keys.enc.public,
            asset_id,
            receive_amount,
            leaf,
        );

        let (protocol, device_request) =
            InstantReceiverAffirmationHostProtocol::<AccountTreeConfig>::init(
                &mut rng,
                &mut receiver_state,
                &leg_ref,
                &leg_enc,
                receive_amount,
                &account_tree,
            )
            .unwrap();

        let tree_params = AccountTreeConfig::parameters();
        let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;

        let device_response = make_affirmation_device_response(
            &mut rng,
            &receiver_keys,
            &device_request,
            comm_re_rand_gen,
        );
        let proof = protocol
            .finish::<_, ()>(&mut rng, &device_response)
            .unwrap();

        let root = account_tree.root().unwrap();
        proof.verify(&leg_enc, &root, &mut rng).unwrap();
    }
}
