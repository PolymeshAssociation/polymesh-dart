use std::{collections::HashMap, hash::Hash};

use ark_ec::{AffineRepr, CurveConfig, CurveGroup};
use ark_ff::UniformRand as _;
use blake2::{Blake2b512, Blake2s256};

use bounded_collections::{BoundedVec, ConstU32};
use codec::Encode;

use dart_bp::{account as bp_account, keys as bp_keys, leg as bp_leg};
use dart_common::{LegId, MEMO_MAX_LENGTH, SETTLEMENT_MAX_LEGS, SettlementId};
use digest::Digest as _;
use dock_crypto_utils::commitment::PedersenCommitmentKey;
use indexmap::IndexMap;
use rand::{RngCore, SeedableRng as _};

use crate::*;

pub mod curve_tree;
use curve_tree::*;

pub(crate) type PallasParameters = ark_pallas::PallasConfig;
pub(crate) type VestaParameters = ark_vesta::VestaConfig;
pub(crate) type PallasA = ark_pallas::Affine;
pub(crate) type PallasScalar = <PallasA as AffineRepr>::ScalarField;

type BPAccountState = bp_account::AccountState<PallasA>;
type BPAccountStateCommitment = bp_account::AccountStateCommitment<PallasA>;

lazy_static::lazy_static! {
    pub static ref DART_GENS: DartBPGenerators = DartBPGenerators::new();
}

/// Constants that are hashed to generate the generators for the Dart BP protocol.
pub const DART_GEN_DOMAIN: &'static str = "polymesh-dart-generators";
pub const DART_GEN_ACCOUNT_KEY: &'static str = "polymesh-dart-pk-acct";
pub const DART_GEN_ENC_KEY: &'static str = "polymesh-dart-pk-enc";

/// The generators for the Dart BP protocol.
#[derive(Clone, Debug)]
pub struct DartBPGenerators {
    pub pk_acct_g: PallasA,
    pub pk_enc_g: PallasA,
    pub account_comm_g: [PallasA; 6],
    pub asset_comm_g: [PallasA; 2],
    pub leg_g: PallasA,
    pub leg_h: PallasA,
    pub ped_comm_key: PedersenCommitmentKey<PallasA>,
}

impl DartBPGenerators {
    /// Creates a new instance of `DartBPGenerators` by generating the necessary generators.
    pub fn new() -> Self {
        // TODO: we should the standard HashToCurve algorithm to generate the generators.

        // Use a seeded rng to generate the generators.  Usse `DART_GEN_DOMAIN` to seed the RNG.
        let mut rng = rand_chacha::ChaCha20Rng::from_seed(
            Blake2s256::digest(DART_GEN_DOMAIN.as_bytes()).into(),
        );

        let pk_acct_g = PallasA::rand(&mut rng);
        // HACK: The sender affirmation fails if this isn't the same.
        //let pk_enc_g = PallasA::rand(&mut rng);
        let pk_enc_g = pk_acct_g;

        let account_comm_g = [
            PallasA::rand(&mut rng), // field: sk -- TODO: Change this generator be the same `pk_acct_g`.
            PallasA::rand(&mut rng), // field: finalized balance.
            PallasA::rand(&mut rng), // field: counter
            PallasA::rand(&mut rng), // field: asset_id
            PallasA::rand(&mut rng), // field: random value rho
            PallasA::rand(&mut rng), // field: random value s
        ];

        let asset_comm_g = [
            PallasA::rand(&mut rng), // field: is_mediator (1 for true, 0 for false)
            PallasA::rand(&mut rng), // field: asset_id
        ];

        // HACK: The sender affirmation fails if this isn't the same.
        //let leg_g = PallasA::rand(&mut rng);
        let leg_g = pk_enc_g;
        let leg_h = PallasA::rand(&mut rng);

        let ped_comm_key =
            PedersenCommitmentKey::<PallasA>::new::<Blake2b512>(b"polymesh-dart-comm-key");

        Self {
            pk_acct_g,
            pk_enc_g,
            account_comm_g,
            asset_comm_g,
            leg_g,
            leg_h,
            ped_comm_key,
        }
    }

    /// Returns the generators for account state commitments.
    pub fn account_comm_g(&self) -> &[PallasA] {
        &self.account_comm_g
    }

    /// Returns the generators for asset state commitments.
    pub fn asset_comm_g(&self) -> &[PallasA] {
        &self.asset_comm_g
    }
}

pub trait AccountLookup {
    /// Get the encryption public key for the account.
    fn get_account_enc_pk(&self, account: &AccountPublicKey) -> Option<EncryptionPublicKey>;

    /// Get the account public key for the given encryption public key.
    fn get_account(&self, enc_pk: &EncryptionPublicKey) -> Option<AccountPublicKey>;
}

#[derive(Clone, Debug, Default)]
pub struct AccountLookupMap {
    enc_to_acct: HashMap<EncryptionPublicKey, AccountPublicKey>,
    acct_to_enc: HashMap<AccountPublicKey, EncryptionPublicKey>,
}

impl AccountLookup for AccountLookupMap {
    fn get_account_enc_pk(&self, account: &AccountPublicKey) -> Option<EncryptionPublicKey> {
        self.acct_to_enc.get(account).copied()
    }

    fn get_account(&self, enc_pk: &EncryptionPublicKey) -> Option<AccountPublicKey> {
        self.enc_to_acct.get(enc_pk).copied()
    }
}

impl AccountLookupMap {
    pub fn new() -> Self {
        Self {
            enc_to_acct: HashMap::new(),
            acct_to_enc: HashMap::new(),
        }
    }

    pub fn ensure_unregistered(&self, keys: &AccountPublicKeys) -> Result<()> {
        if self.enc_to_acct.contains_key(&keys.enc) {
            return Err(Error::AccountPublicKeyExists);
        }
        if self.acct_to_enc.contains_key(&keys.acct) {
            return Err(Error::AccountPublicKeyExists);
        }
        Ok(())
    }

    /// Register an account's encryption public key and account public key in the lookup map.
    pub fn register_account_keys(&mut self, account_pk_keys: &AccountPublicKeys) {
        self.enc_to_acct
            .insert(account_pk_keys.enc, account_pk_keys.acct);
        self.acct_to_enc
            .insert(account_pk_keys.acct, account_pk_keys.enc);
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct EncryptionPublicKey(bp_keys::EncKey<PallasA>);

impl From<AccountPublicKey> for EncryptionPublicKey {
    fn from(account_pk: AccountPublicKey) -> Self {
        EncryptionPublicKey(bp_keys::EncKey(account_pk.0.0))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EncryptionSecretKey(bp_keys::DecKey<PallasA>);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct EncryptionKeyPair {
    pub public: EncryptionPublicKey,
    secret: EncryptionSecretKey,
}

impl EncryptionKeyPair {
    /// Generates a new set of encryption keys using the provided RNG.
    pub fn rand<R: RngCore>(rng: &mut R) -> Self {
        let (enc, enc_pk) = bp_keys::keygen_enc(rng, DART_GENS.pk_enc_g);
        Self {
            public: EncryptionPublicKey(enc_pk),
            secret: EncryptionSecretKey(enc),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct AccountPublicKey(bp_keys::VerKey<PallasA>);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AccountSecretKey(bp_keys::SigKey<PallasA>);

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AccountKeyPair {
    pub public: AccountPublicKey,
    secret: AccountSecretKey,
}

impl AccountKeyPair {
    /// Generates a new set of account keys using the provided RNG.
    pub fn rand<R: RngCore>(rng: &mut R) -> Self {
        let (account, account_pk) = bp_keys::keygen_sig(rng, DART_GENS.pk_acct_g);
        Self {
            public: AccountPublicKey(account_pk),
            secret: AccountSecretKey(account),
        }
    }

    pub fn account_state<R: RngCore>(&self, rng: &mut R, asset_id: AssetId) -> AccountState {
        AccountState(BPAccountState::new(rng, self.secret.0.0, asset_id))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct AccountPublicKeys {
    pub enc: EncryptionPublicKey,
    pub acct: AccountPublicKey,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AccountKeys {
    pub enc: EncryptionKeyPair,
    pub acct: AccountKeyPair,
}

impl AccountKeys {
    /// Generates a new set of account keys using the provided RNG.
    pub fn rand<R: RngCore>(rng: &mut R) -> Self {
        let enc = EncryptionKeyPair::rand(rng);
        let acct = AccountKeyPair::rand(rng);
        Self { enc, acct }
    }

    /// Genreates a new set of account keys using the provided string as a seed.
    pub fn from_seed(seed: &str) -> Self {
        let mut rng =
            rand_chacha::ChaCha20Rng::from_seed(Blake2s256::digest(seed.as_bytes()).into());
        Self::rand(&mut rng)
    }

    /// Initializes a new asset state for the account.
    pub fn init_asset_state<R: RngCore>(
        &self,
        rng: &mut R,
        asset_id: AssetId,
    ) -> AccountAssetState {
        AccountAssetState::new(rng, self, asset_id)
    }

    /// Returns the public keys for the account.
    pub fn public_keys(&self) -> AccountPublicKeys {
        AccountPublicKeys {
            enc: self.enc.public,
            acct: self.acct.public,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccountState(BPAccountState);

impl AccountState {
    pub fn commitment(&self) -> AccountStateCommitment {
        AccountStateCommitment(self.0.commit(&DART_GENS.account_comm_g()))
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct AccountStateNullifier(pub PallasA);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AccountStateCommitment(pub BPAccountStateCommitment);

pub struct AccountAssetState {
    pub account: AccountKeys,
    pub asset_id: AssetId,
    pub current_state: AccountState,
    pub current_state_commitment: AccountStateCommitment,
    pub current_tx_id: u64,
    pub pending_state: Option<AccountState>,
}

impl AccountAssetState {
    pub fn new<R: RngCore>(rng: &mut R, account: &AccountKeys, asset_id: AssetId) -> Self {
        let current_state = account.acct.account_state(rng, asset_id);
        let current_state_commitment = current_state.commitment();
        Self {
            account: *account,
            asset_id,
            current_state,
            current_state_commitment,
            current_tx_id: 0,
            pending_state: None,
        }
    }

    pub fn mint<R: RngCore>(&mut self, rng: &mut R, amount: Balance) -> AccountState {
        let state = AccountState(self.current_state.0.get_state_for_mint(rng, amount));
        self._set_pending_state(state.clone());
        state
    }

    pub fn get_sender_affirm_state<R: RngCore>(
        &mut self,
        rng: &mut R,
        amount: Balance,
    ) -> AccountState {
        let state = AccountState(self.current_state.0.get_state_for_send(rng, amount));
        self._set_pending_state(state.clone());
        state
    }

    pub fn get_receiver_affirm_state<R: RngCore>(&mut self, rng: &mut R) -> AccountState {
        let state = AccountState(self.current_state.0.get_state_for_receive(rng));
        self._set_pending_state(state.clone());
        state
    }

    pub fn get_state_for_claiming_received<R: RngCore>(
        &mut self,
        rng: &mut R,
        amount: Balance,
    ) -> AccountState {
        let state = AccountState(
            self.current_state
                .0
                .get_state_for_claiming_received(rng, amount),
        );
        self._set_pending_state(state.clone());
        state
    }

    pub fn get_state_for_reversing_send<R: RngCore>(
        &mut self,
        rng: &mut R,
        amount: Balance,
    ) -> AccountState {
        let state = AccountState(
            self.current_state
                .0
                .get_state_for_reversing_send(rng, amount),
        );
        self._set_pending_state(state.clone());
        state
    }

    pub fn get_state_for_decreasing_counter<R: RngCore>(&mut self, rng: &mut R) -> AccountState {
        let state = AccountState(
            self.current_state
                .0
                .get_state_for_decreasing_counter(rng, None),
        );
        self._set_pending_state(state.clone());
        state
    }

    fn _set_pending_state(&mut self, state: AccountState) {
        self.pending_state = Some(state);
    }

    pub fn commit_pending_state(&mut self) -> bool {
        match self.pending_state.take() {
            Some(pending_state) => {
                self.current_state = pending_state;
                self.current_state_commitment = self.current_state.commitment();
                self.current_tx_id += 1;
                true
            }
            None => false,
        }
    }
}

/// Represents the state of an asset in the Dart BP protocol.
#[derive(Clone, Debug)]
pub struct AssetState {
    asset_id: AssetId,
    is_mediator: bool,
    pk: EncryptionPublicKey,
}

impl AssetState {
    /// Creates a new asset state with the given asset ID, mediator status, and public key.
    pub fn new(asset_id: AssetId, is_mediator: bool, pk: EncryptionPublicKey) -> Self {
        Self {
            asset_id,
            is_mediator,
            pk,
        }
    }

    /// Changes the auditor or mediator for the asset.
    pub fn change_auditor(&mut self, is_mediator: bool, pk: EncryptionPublicKey) {
        self.is_mediator = is_mediator;
        self.pk = pk;
    }

    /// Given commitment key `leaf_comm_key`, the leaf is `leaf_comm_key[0] * role + leaf_comm_key[1] * asset_id + pk`
    /// where `role` equals 1 if `pk` is the public key of mediator else its 0.A
    pub fn commitment(&self) -> AssetStateCommitment {
        let leaf_comm_key = DART_GENS.asset_comm_g();
        let comm = if self.is_mediator {
            leaf_comm_key[0]
        } else {
            <PallasA as AffineRepr>::zero()
        };
        AssetStateCommitment(
            (comm + (leaf_comm_key[1] * PallasScalar::from(self.asset_id)) + self.pk.0.0)
                .into_affine(),
        )
    }
}

/// Represents the commitment of an asset state in the Dart BP protocol.
#[derive(Clone, Debug, Default)]
pub struct AssetStateCommitment(pub PallasA);

/// Represents a tree of asset states in the Dart BP protocol.
pub struct AssetCurveTree {
    tree: FullCurveTree<ASSET_TREE_L>,
    assets: IndexMap<AssetId, AssetState>,
}

impl AssetCurveTree {
    /// Creates a new instance of `AssetCurveTree` with the specified parameters.
    pub fn new() -> Result<Self> {
        Ok(Self {
            tree: FullCurveTree::new_with_capacity(
                ASSET_TREE_L,
                ASSET_TREE_HEIGHT as usize,
                ACCOUNT_TREE_GENS,
            ),
            assets: IndexMap::new(),
        })
    }

    /// Returns the asset state for the given asset ID, if it exists.
    pub fn get_asset_state(&self, asset_id: AssetId) -> Option<AssetState> {
        self.assets.get(&asset_id).cloned()
    }

    /// Sets the asset state in the tree and returns the index of the asset state.
    pub fn set_asset_state(&mut self, state: AssetState) -> Result<usize> {
        let asset_id = state.asset_id;
        // Get the new asset state commitment.
        let leaf = state.commitment();

        // Update or insert the asset state.
        let entry = self.assets.entry(asset_id);
        let index = entry.index();
        entry.insert_entry(state);

        // Update the leaf in the curve tree.
        self.tree.update(leaf.0, index)?;
        Ok(index)
    }

    pub fn get_asset_state_path(&self, asset_id: AssetId) -> Option<CurveTreePath<ASSET_TREE_L>> {
        let leaf_index = self.assets.get_index_of(&asset_id)?;
        self.tree.get_path_to_leaf_index(leaf_index).ok()
    }

    pub fn params(&self) -> &CurveTreeParameters {
        self.tree.params()
    }

    pub fn root_node(&self) -> CurveTreeRoot<ASSET_TREE_L> {
        self.tree.root_node()
    }
}

/// Account asset registration proof.  Report section 5.1.3 "Account Registration".
pub struct AccountAssetRegistrationProof {
    pub account: AccountPublicKey,
    pub account_state_commitment: AccountStateCommitment,
    pub asset_id: AssetId,

    proof: bp_account::RegTxnProof<PallasA>,
    challenge: PallasScalar,
}

impl AccountAssetRegistrationProof {
    /// Generate a new account state for an asset and a registration proof for it.
    pub fn new(
        rng: &mut impl RngCore,
        account: &AccountKeys,
        asset_id: AssetId,
        ctx: &[u8],
    ) -> (Self, AccountAssetState) {
        let account_state = account.init_asset_state(rng, asset_id);
        let account_state_commitment = account_state.current_state_commitment.clone();
        let (proof, challenge) = bp_account::RegTxnProof::new(
            rng,
            account.acct.public.0.0,
            &account_state.current_state.0,
            account_state_commitment.0.clone(),
            ctx,
            &DART_GENS.account_comm_g(),
            DART_GENS.pk_acct_g,
        );
        (
            Self {
                account: account.acct.public,
                account_state_commitment,
                asset_id,
                proof,
                challenge,
            },
            account_state,
        )
    }

    /// Verifies the account asset registration proof against the provided public key, asset ID, and account state commitment.
    pub fn verify(&self, ctx: &[u8]) -> Result<()> {
        self.proof.verify(
            &self.account.0.0,
            self.asset_id,
            &self.account_state_commitment.0,
            self.challenge,
            ctx,
            &DART_GENS.account_comm_g(),
            DART_GENS.pk_acct_g,
        )?;
        Ok(())
    }
}

/// Asset minting proof.  Report section 5.1.4 "Increase Asset Supply".
pub struct AssetMintingProof {
    // Public inputs.
    pub pk: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,

    // proof
    proof: bp_account::MintTxnProof<
        ACCOUNT_TREE_L,
        <PallasParameters as CurveConfig>::ScalarField,
        <VestaParameters as CurveConfig>::ScalarField,
        PallasParameters,
        VestaParameters,
    >,
    challenge: PallasScalar,
}

impl AssetMintingProof {
    /// Generate a new asset minting proof.
    pub fn new(
        rng: &mut impl RngCore,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
        amount: Balance,
    ) -> Result<Self> {
        // Generate a new minting state for the account asset.
        let mint_account_state = account_asset.mint(rng, amount);
        let mint_account_commitment = mint_account_state.commitment();

        let pk = account_asset.account.acct.public;
        let current_account_state = &account_asset.current_state.0;
        let current_account_path =
            tree_lookup.get_path_to_leaf(account_asset.current_state_commitment.0.0)?;

        let root = tree_lookup.root_node();

        let (proof, challenge) = bp_account::MintTxnProof::new(
            rng,
            pk.0.0,
            amount,
            current_account_state,
            &mint_account_state.0,
            mint_account_commitment.0.clone(),
            current_account_path,
            b"",
            tree_lookup.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.pk_acct_g,
        );
        Ok(Self {
            pk,
            asset_id: account_asset.asset_id,
            amount,
            root,

            proof,
            challenge,
        })
    }

    pub fn account_state_commitment(&self) -> AccountStateCommitment {
        AccountStateCommitment(self.proof.updated_account_commitment.clone())
    }

    pub fn nullifier(&self) -> AccountStateNullifier {
        AccountStateNullifier(self.proof.nullifier)
    }

    pub fn verify(&self, tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>) -> Result<()> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for asset minting proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        self.proof.verify(
            self.pk.0.0,
            self.asset_id,
            self.amount,
            &self.root,
            self.challenge,
            b"",
            tree_roots.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.pk_acct_g,
        )?;
        Ok(())
    }
}

/// Represents the auditor or mediator in a leg of the Dart BP protocol.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AuditorOrMediator {
    Mediator(AccountPublicKeys),
    Auditor(EncryptionPublicKey),
}

impl AuditorOrMediator {
    pub fn mediator(pk: &AccountPublicKeys) -> Self {
        Self::Mediator(*pk)
    }

    pub fn auditor(pk: &EncryptionPublicKey) -> Self {
        Self::Auditor(*pk)
    }

    pub fn get_keys(&self) -> (EncryptionPublicKey, Option<AccountPublicKey>) {
        match self {
            AuditorOrMediator::Mediator(pk) => (pk.enc, Some(pk.acct)),
            AuditorOrMediator::Auditor(pk) => (*pk, None),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SettlementRef {
    /// ID based reference.
    ID(SettlementId),
    /// Hash based reference.
    Hash([u8; 32]),
}

impl From<SettlementId> for SettlementRef {
    fn from(id: SettlementId) -> Self {
        SettlementRef::ID(id)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LegRef {
    /// The settlement reference.
    pub settlement: SettlementRef,
    /// The leg ID within the settlement.
    pub leg_id: LegId,
}

impl LegRef {
    pub fn new(settlement: SettlementRef, leg_id: LegId) -> Self {
        Self { settlement, leg_id }
    }

    /// Returns the leg ID.
    pub fn leg_id(&self) -> LegId {
        self.leg_id
    }

    /// Returns the settlement ID if the settlement reference is an ID.
    pub fn settlement_id(&self) -> Option<SettlementId> {
        if let SettlementRef::ID(id) = &self.settlement {
            Some(*id)
        } else {
            None
        }
    }

    /// The settlement/leg context to tie proofs to a leg.
    pub fn context(&self) -> String {
        format!("{:?}-{}", self.settlement, self.leg_id)
    }
}

pub enum LegRole {
    Sender,
    Receiver,
    Auditor,
    Mediator,
}

/// The decrypted leg details in the Dart BP protocol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Leg(bp_leg::Leg<PallasA>);

impl Leg {
    pub fn new(
        sender: AccountPublicKey,
        receiver: AccountPublicKey,
        mediator: Option<AccountPublicKey>,
        asset_id: AssetId,
        amount: Balance,
    ) -> Self {
        let leg = bp_leg::Leg::new(
            sender.0.0,
            receiver.0.0,
            mediator.map(|m| m.0.0),
            amount,
            asset_id,
        );
        Self(leg)
    }

    pub fn encrypt<R: RngCore>(
        &self,
        rng: &mut R,
        ephemeral_key: EphemeralSkEncryption,
        pk_e: &EncryptionPublicKey,
    ) -> (LegEncrypted, LegEncryptionRandomness) {
        let (leg_enc, leg_enc_rand) =
            self.0
                .encrypt(rng, &pk_e.0.0, DART_GENS.leg_g, DART_GENS.leg_h);
        (
            LegEncrypted {
                leg_enc,
                ephemeral_key,
            },
            LegEncryptionRandomness(leg_enc_rand),
        )
    }

    pub fn sender(&self) -> AccountPublicKey {
        AccountPublicKey(bp_keys::VerKey(self.0.pk_s))
    }

    pub fn receiver(&self) -> AccountPublicKey {
        AccountPublicKey(bp_keys::VerKey(self.0.pk_r))
    }

    pub fn mediator(&self) -> Option<AccountPublicKey> {
        self.0.pk_m.map(|m| AccountPublicKey(bp_keys::VerKey(m)))
    }

    pub fn asset_id(&self) -> AssetId {
        self.0.asset_id
    }

    pub fn amount(&self) -> Balance {
        self.0.amount
    }
}

/// A helper type to build the encrypted leg and its proof in the Dart BP protocol.
pub struct LegBuilder {
    pub sender: AccountPublicKeys,
    pub receiver: AccountPublicKeys,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub mediator: AuditorOrMediator,
}

impl LegBuilder {
    /// Creates a new leg with the given sender, receiver, asset ID, amount, and optional mediator.
    pub fn new(
        sender: AccountPublicKeys,
        receiver: AccountPublicKeys,
        asset_id: AssetId,
        amount: Balance,
        mediator: AuditorOrMediator,
    ) -> Self {
        Self {
            sender,
            receiver,
            asset_id,
            amount,
            mediator,
        }
    }

    pub fn encryt_and_prove<R: RngCore>(
        self,
        rng: &mut R,
        ctx: &[u8],
        asset_tree: &AssetCurveTree,
    ) -> SettlementLegProof {
        let (mediator_enc, mediator_acct) = self.mediator.get_keys();
        let leg = Leg::new(
            self.sender.acct,
            self.receiver.acct,
            mediator_acct,
            self.asset_id,
            self.amount,
        );
        let (ephemeral_key, eph_rand, pk_e) =
            EphemeralSkEncryption::new(rng, self.sender.enc, self.receiver.enc, mediator_enc);
        let (leg_enc, leg_enc_rand) = leg.encrypt(rng, ephemeral_key, &pk_e);

        let leg_proof = SettlementLegProof::new(
            rng,
            leg,
            leg_enc,
            &leg_enc_rand,
            eph_rand,
            pk_e,
            mediator_acct,
            ctx,
            asset_tree,
        );

        leg_proof
    }
}

pub struct SettlementBuilder {
    memo: Vec<u8>,
    legs: Vec<LegBuilder>,
}

impl SettlementBuilder {
    pub fn new(memo: &[u8]) -> Self {
        Self {
            memo: memo.to_vec(),
            legs: Vec::new(),
        }
    }

    pub fn leg(mut self, leg: LegBuilder) -> Self {
        self.legs.push(leg);
        self
    }

    pub fn encryt_and_prove<R: RngCore>(
        self,
        rng: &mut R,
        asset_tree: &AssetCurveTree,
    ) -> Result<SettlementProof> {
        let memo = BoundedVec::try_from(self.memo)
            .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        let root = asset_tree.root_node();

        let mut legs = Vec::with_capacity(self.legs.len());

        for (idx, leg_builder) in self.legs.into_iter().enumerate() {
            let ctx = (&memo, idx as u8).encode();
            let leg_proof = leg_builder.encryt_and_prove(rng, &ctx, asset_tree);
            legs.push(leg_proof);
        }

        let legs =
            BoundedVec::try_from(legs).map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        Ok(SettlementProof { memo, root, legs })
    }
}

#[derive(Clone)]
pub struct SettlementProof {
    memo: BoundedVec<u8, ConstU32<MEMO_MAX_LENGTH>>,
    root: CurveTreeRoot<ASSET_TREE_L>,

    pub legs: BoundedVec<SettlementLegProof, ConstU32<SETTLEMENT_MAX_LEGS>>,
}

impl SettlementProof {
    pub fn verify(&self, asset_tree: impl ValidateCurveTreeRoot<ASSET_TREE_L>) -> Result<()> {
        // Validate the root of the curve tree.
        if !asset_tree.validate_root(&self.root) {
            log::error!("Invalid root for settlement proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let params = asset_tree.params();
        for (idx, leg) in self.legs.iter().enumerate() {
            let ctx = (&self.memo, idx as u8).encode();
            leg.verify(&ctx, &self.root, params)?;
        }
        Ok(())
    }
}

/// The proof for a settlement leg in the Dart BP protocol.
///
/// This is to prove that the leg includes the correct encryption of the leg details and
/// that the correct auditor/mediator for the asset is included in the leg.
#[derive(Clone)]
pub struct SettlementLegProof {
    pub leg_enc: LegEncrypted,
    pub has_mediator: bool,

    proof: bp_leg::SettlementTxnProof<
        ASSET_TREE_L,
        <PallasParameters as CurveConfig>::ScalarField,
        <VestaParameters as CurveConfig>::ScalarField,
        PallasParameters,
        VestaParameters,
    >,
    challenge: PallasScalar,
}

impl SettlementLegProof {
    pub(crate) fn new(
        rng: &mut impl RngCore,
        leg: Leg,
        leg_enc: LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        eph_rand: PallasScalar,
        pk_e: EncryptionPublicKey,
        mediator: Option<AccountPublicKey>,
        ctx: &[u8],
        asset_tree: &AssetCurveTree,
    ) -> Self {
        let asset_path = asset_tree
            .get_asset_state_path(leg.asset_id())
            .expect("Missing asset state");

        let (proof, challenge) = bp_leg::SettlementTxnProof::new(
            rng,
            leg.0,
            leg_enc.leg_enc.clone(),
            leg_enc_rand.0.clone(),
            leg_enc.ephemeral_key.enc.clone(),
            eph_rand,
            pk_e.0.0,
            mediator.map(|m| m.0.0),
            asset_path,
            ctx,
            asset_tree.params(),
            &DART_GENS.asset_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
            &DART_GENS.ped_comm_key,
        );

        Self {
            leg_enc,
            has_mediator: mediator.is_some(),

            proof,
            challenge,
        }
    }

    pub fn verify(
        &self,
        ctx: &[u8],
        root: &CurveTreeRoot<ASSET_TREE_L>,
        params: &CurveTreeParameters,
    ) -> Result<()> {
        let pk_e = self.leg_enc.ephemeral_key.pk_e;
        log::debug!("Verify leg: {:?}", self.leg_enc.leg_enc);
        self.proof.verify(
            self.leg_enc.leg_enc.clone(),
            self.leg_enc.ephemeral_key.enc.clone(),
            pk_e.0.0,
            &root,
            self.challenge,
            ctx,
            params,
            &DART_GENS.asset_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
            &DART_GENS.ped_comm_key,
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EphemeralSkEncryption {
    enc: bp_leg::EphemeralSkEncryption<PallasA>,
    pk_e: EncryptionPublicKey,
}

impl EphemeralSkEncryption {
    pub(crate) fn new<R: RngCore>(
        rng: &mut R,
        sender: EncryptionPublicKey,
        receiver: EncryptionPublicKey,
        mediator: EncryptionPublicKey,
    ) -> (Self, PallasScalar, EncryptionPublicKey) {
        let (ephemeral_key, eph_key_rand, _sk_e, pk_e) =
            bp_leg::EphemeralSkEncryption::new::<_, Blake2b512>(
                rng,
                sender.0.0,
                receiver.0.0,
                mediator.0.0,
                DART_GENS.leg_g,
                DART_GENS.leg_h,
            );
        log::debug!("Ephemeral key: sk_e={:?}", _sk_e);
        let pk_e = EncryptionPublicKey(pk_e);
        (
            Self {
                enc: ephemeral_key,
                pk_e,
            },
            eph_key_rand,
            pk_e,
        )
    }
}

pub struct LegEncryptionRandomness(bp_leg::LegEncryptionRandomness<PallasA>);

/// Represents an encrypted leg in the Dart BP protocol.  Stored onchain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LegEncrypted {
    leg_enc: bp_leg::LegEncryption<PallasA>,
    ephemeral_key: EphemeralSkEncryption,
}

impl LegEncrypted {
    pub fn decrypt_sk_e(&self, role: LegRole, keys: &EncryptionKeyPair) -> EncryptionSecretKey {
        let sk = keys.secret.0.0;
        let sk_e = match role {
            LegRole::Sender => self.ephemeral_key.enc.decrypt_for_sender::<Blake2b512>(sk),
            LegRole::Receiver => self
                .ephemeral_key
                .enc
                .decrypt_for_receiver::<Blake2b512>(sk),
            LegRole::Auditor | LegRole::Mediator => self
                .ephemeral_key
                .enc
                .decrypt_for_mediator_or_auditor::<Blake2b512>(sk),
        };
        EncryptionSecretKey(bp_keys::DecKey(sk_e))
    }

    /// Decrypts the leg using the provided secret key and role.
    pub fn decrypt(&self, role: LegRole, keys: &EncryptionKeyPair) -> Leg {
        let sk_e = self.decrypt_sk_e(role, keys);
        log::debug!("Decrypted sk_e: {:?}", sk_e.0.0);
        let leg = self.leg_enc.decrypt(&sk_e.0.0, DART_GENS.leg_h);
        Leg(leg)
    }
}

/// The sender affirmation proof in the Dart BP protocol.
pub struct SenderAffirmationProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,

    proof: bp_account::AffirmAsSenderTxnProof<
        ACCOUNT_TREE_L,
        <PallasParameters as CurveConfig>::ScalarField,
        <VestaParameters as CurveConfig>::ScalarField,
        PallasParameters,
        VestaParameters,
    >,
    challenge: PallasScalar,
}

impl SenderAffirmationProof {
    pub fn new<R: RngCore>(
        rng: &mut R,
        leg_ref: LegRef,
        amount: Balance,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Self {
        // Generate a new account state for the sender affirmation.
        let new_account_state = account_asset.get_sender_affirm_state(rng, amount);
        let new_account_commitment = new_account_state.commitment();

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.0.0)
            .expect("Failed to get path to current account state commitment");

        let root = tree_lookup.root_node();

        let ctx = leg_ref.context();
        let (proof, challenge) = bp_account::AffirmAsSenderTxnProof::new(
            rng,
            amount,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.0,
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        );

        Self {
            leg_ref,
            root,

            proof,
            challenge,
        }
    }

    pub fn account_state_commitment(&self) -> AccountStateCommitment {
        AccountStateCommitment(self.proof.updated_account_commitment.clone())
    }

    pub fn nullifier(&self) -> AccountStateNullifier {
        AccountStateNullifier(self.proof.nullifier)
    }

    pub fn verify(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
    ) -> Result<()> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for sender affirmation proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let ctx = self.leg_ref.context();
        self.proof.verify(
            leg_enc.leg_enc.clone(),
            &self.root,
            self.challenge,
            ctx.as_bytes(),
            tree_roots.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        )?;
        Ok(())
    }
}

/// The receiver affirmation proof in the Dart BP protocol.
pub struct ReceiverAffirmationProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub account_state_commitment: AccountStateCommitment,

    proof: bp_account::AffirmAsReceiverTxnProof<
        ACCOUNT_TREE_L,
        <PallasParameters as CurveConfig>::ScalarField,
        <VestaParameters as CurveConfig>::ScalarField,
        PallasParameters,
        VestaParameters,
    >,
    challenge: PallasScalar,
}

impl ReceiverAffirmationProof {
    pub fn new<R: RngCore>(
        rng: &mut R,
        leg_ref: LegRef,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Self {
        // Generate a new account state for the receiver affirmation.
        let new_account_state = account_asset.get_receiver_affirm_state(rng);
        let new_account_commitment = new_account_state.commitment();

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.0.0)
            .expect("Failed to get path to current account state commitment");

        let root = tree_lookup.root_node();

        let ctx = leg_ref.context();
        let (proof, challenge) = bp_account::AffirmAsReceiverTxnProof::new(
            rng,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.0.clone(),
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        );

        Self {
            leg_ref,
            root,
            account_state_commitment: new_account_commitment,

            proof,
            challenge,
        }
    }

    pub fn account_state_commitment(&self) -> AccountStateCommitment {
        AccountStateCommitment(self.proof.updated_account_commitment.clone())
    }

    pub fn nullifier(&self) -> AccountStateNullifier {
        AccountStateNullifier(self.proof.nullifier)
    }

    pub fn verify(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
    ) -> Result<()> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for receiver affirmation proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let ctx = self.leg_ref.context();
        self.proof.verify(
            leg_enc.leg_enc.clone(),
            &self.root,
            self.challenge,
            ctx.as_bytes(),
            tree_roots.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        )?;
        Ok(())
    }
}

/// The proof for claiming received assets in the Dart BP protocol.
pub struct ReceiverClaimProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub account_state_commitment: AccountStateCommitment,

    proof: bp_account::ClaimReceivedTxnProof<
        ACCOUNT_TREE_L,
        <PallasParameters as CurveConfig>::ScalarField,
        <VestaParameters as CurveConfig>::ScalarField,
        PallasParameters,
        VestaParameters,
    >,
    challenge: PallasScalar,
}

impl ReceiverClaimProof {
    pub fn new<R: RngCore>(
        rng: &mut R,
        leg_ref: LegRef,
        amount: Balance,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Self {
        // Generate a new account state for claiming received assets.
        let new_account_state = account_asset.get_state_for_claiming_received(rng, amount);
        let new_account_commitment = new_account_state.commitment();

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.0.0)
            .expect("Failed to get path to current account state commitment");

        let root = tree_lookup.root_node();

        let ctx = leg_ref.context();
        let (proof, challenge) = bp_account::ClaimReceivedTxnProof::new(
            rng,
            amount,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.0.clone(),
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        );

        Self {
            leg_ref,
            root,
            account_state_commitment: new_account_commitment,

            proof,
            challenge,
        }
    }

    pub fn account_state_commitment(&self) -> AccountStateCommitment {
        AccountStateCommitment(self.proof.updated_account_commitment.clone())
    }

    pub fn nullifier(&self) -> AccountStateNullifier {
        AccountStateNullifier(self.proof.nullifier)
    }

    pub fn verify(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
    ) -> Result<()> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for receiver claim proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let ctx = self.leg_ref.context();
        self.proof.verify(
            leg_enc.leg_enc.clone(),
            &self.root,
            self.challenge,
            ctx.as_bytes(),
            tree_roots.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        )?;
        Ok(())
    }
}

/// Sender counter update proof in the Dart BP protocol.
pub struct SenderCounterUpdateProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub account_state_commitment: AccountStateCommitment,

    proof: bp_account::SenderCounterUpdateTxnProof<
        ACCOUNT_TREE_L,
        <PallasParameters as CurveConfig>::ScalarField,
        <VestaParameters as CurveConfig>::ScalarField,
        PallasParameters,
        VestaParameters,
    >,
    challenge: PallasScalar,
}

impl SenderCounterUpdateProof {
    pub fn new<R: RngCore>(
        rng: &mut R,
        leg_ref: LegRef,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Self {
        // Generate a new account state for decreasing the counter.
        let new_account_state = account_asset.get_state_for_decreasing_counter(rng);
        let new_account_commitment = new_account_state.commitment();

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.0.0)
            .expect("Failed to get path to current account state commitment");

        let root = tree_lookup.root_node();

        let ctx = leg_ref.context();
        let (proof, challenge) = bp_account::SenderCounterUpdateTxnProof::new(
            rng,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.0.clone(),
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        );

        Self {
            leg_ref,
            root,
            account_state_commitment: new_account_commitment,

            proof,
            challenge,
        }
    }

    pub fn account_state_commitment(&self) -> AccountStateCommitment {
        AccountStateCommitment(self.proof.updated_account_commitment.clone())
    }

    pub fn nullifier(&self) -> AccountStateNullifier {
        AccountStateNullifier(self.proof.nullifier)
    }

    pub fn verify(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
    ) -> Result<()> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for sender counter update proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let ctx = self.leg_ref.context();
        self.proof.verify(
            leg_enc.leg_enc.clone(),
            &self.root,
            self.challenge,
            ctx.as_bytes(),
            tree_roots.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        )?;
        Ok(())
    }
}

/// Sender reversal proof in the Dart BP protocol.
pub struct SenderReversalProof {
    pub leg_ref: LegRef,
    pub root: CurveTreeRoot<ACCOUNT_TREE_L>,
    pub account_state_commitment: AccountStateCommitment,

    proof: bp_account::SenderReverseTxnProof<
        ACCOUNT_TREE_L,
        <PallasParameters as CurveConfig>::ScalarField,
        <VestaParameters as CurveConfig>::ScalarField,
        PallasParameters,
        VestaParameters,
    >,
    challenge: PallasScalar,
}

impl SenderReversalProof {
    pub fn new<R: RngCore>(
        rng: &mut R,
        leg_ref: LegRef,
        amount: Balance,
        sk_e: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L>,
    ) -> Self {
        // Generate a new account state for reversing the send.
        let new_account_state = account_asset.get_state_for_reversing_send(rng, amount);
        let new_account_commitment = new_account_state.commitment();

        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.0.0)
            .expect("Failed to get path to current account state commitment");

        let root = tree_lookup.root_node();

        let ctx = leg_ref.context();
        let (proof, challenge) = bp_account::SenderReverseTxnProof::new(
            rng,
            amount,
            sk_e.0.0,
            leg_enc.leg_enc.clone(),
            &current_account_state,
            &new_account_state.0,
            new_account_commitment.0.clone(),
            current_account_path,
            ctx.as_bytes(),
            tree_lookup.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        );

        Self {
            leg_ref,
            root,
            account_state_commitment: new_account_commitment,

            proof,
            challenge,
        }
    }

    pub fn account_state_commitment(&self) -> AccountStateCommitment {
        AccountStateCommitment(self.proof.updated_account_commitment.clone())
    }

    pub fn nullifier(&self) -> AccountStateNullifier {
        AccountStateNullifier(self.proof.nullifier)
    }

    pub fn verify(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L>,
    ) -> Result<()> {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root) {
            log::error!("Invalid root for sender reversal proof");
            return Err(Error::CurveTreeRootNotFound);
        }
        let ctx = self.leg_ref.context();
        self.proof.verify(
            leg_enc.leg_enc.clone(),
            &self.root,
            self.challenge,
            ctx.as_bytes(),
            tree_roots.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.leg_g,
            DART_GENS.leg_h,
        )?;
        Ok(())
    }
}

/// Mediator affirmation proof in the Dart BP protocol.
pub struct MediatorAffirmationProof {
    pub leg_ref: LegRef,
    pub accept: bool,

    proof: bp_leg::MediatorTxnProof<PallasA>,
    challenge: PallasScalar,
}

impl MediatorAffirmationProof {
    pub fn new<R: RngCore>(
        rng: &mut R,
        leg_ref: LegRef,
        eph_sk: EncryptionSecretKey,
        leg_enc: &LegEncrypted,
        mediator_sk: &AccountKeyPair,
        accept: bool,
    ) -> Self {
        let ctx = leg_ref.context();
        let eph_pk = leg_enc.ephemeral_key.pk_e;
        let (proof, challenge) = bp_leg::MediatorTxnProof::new(
            rng,
            leg_enc.leg_enc.clone(),
            eph_sk.0.0,
            eph_pk.0.0,
            mediator_sk.secret.0.0,
            accept,
            ctx.as_bytes(),
            DART_GENS.leg_g,
        );

        Self {
            leg_ref,
            accept,

            proof,
            challenge,
        }
    }

    pub fn verify(&self, leg_enc: &LegEncrypted) -> Result<()> {
        let ctx = self.leg_ref.context();
        let eph_pk = leg_enc.ephemeral_key.pk_e;
        self.proof.verify(
            leg_enc.leg_enc.clone(),
            eph_pk.0.0,
            self.accept,
            self.challenge,
            ctx.as_bytes(),
            DART_GENS.leg_g,
        )?;
        Ok(())
    }
}
