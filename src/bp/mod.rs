use std::collections::HashMap;

use ark_ec::{AffineRepr, CurveConfig};
use ark_ff::UniformRand as _;
use blake2::{Blake2b512, Blake2s256};

use dart_bp::{
    account as bp_account,
    leg as bp_leg,
    keys as bp_keys,
};
use digest::Digest as _;
use rand::{RngCore, SeedableRng as _};

use crate::*;

pub mod curve_tree;
use curve_tree::*;

pub type PallasParameters = ark_pallas::PallasConfig;
pub type VestaParameters = ark_vesta::VestaConfig;
pub type PallasA = ark_pallas::Affine;

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
    pub leg_g: PallasA,
    pub leg_h: PallasA,
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
        let pk_enc_g = PallasA::rand(&mut rng);

        let account_comm_g = [
            PallasA::rand(&mut rng), // field: sk -- TODO: Change this generator be the same `pk_acct_g`?
            PallasA::rand(&mut rng), // field: finalized balance.
            PallasA::rand(&mut rng), // field: counter
            PallasA::rand(&mut rng), // field: asset_id
            PallasA::rand(&mut rng), // field: random value rho
            PallasA::rand(&mut rng), // field: random value s
        ];

        let leg_g = PallasA::rand(&mut rng);
        let leg_h = PallasA::rand(&mut rng);
        Self { pk_acct_g, pk_enc_g, account_comm_g, leg_g, leg_h }
    }

    /// Returns the generators for account state commitments.
    pub fn account_comm_g(&self) -> &[PallasA] {
        &self.account_comm_g
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
        Self { public: EncryptionPublicKey(enc_pk), secret: EncryptionSecretKey(enc) }
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
        Self { public: AccountPublicKey(account_pk), secret: AccountSecretKey(account) }
    }

    pub fn account_state<R: RngCore>(
        &self,
        rng: &mut R,
        asset_id: AssetId,
    ) -> AccountState {
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
        let mut rng = rand_chacha::ChaCha20Rng::from_seed(
            Blake2s256::digest(seed.as_bytes()).into(),
        );
        Self::rand(&mut rng)
    }

    /// Initializes a new asset state for the account.
    pub fn init_asset_state(
        &self,
        asset_id: AssetId,
    ) -> AccountAssetState {
        AccountAssetState::new(&mut rand::thread_rng(), self, asset_id)
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

pub struct AccountStateCommitment(BPAccountStateCommitment);

pub struct AccountAssetState {
    pub account: AccountKeys,
    pub asset_id: AssetId,
    pub current_state: AccountState,
    pub current_state_commitment: AccountStateCommitment,
    pub current_tx_id: u64,
    pub pending_state: Option<AccountState>,
}

impl AccountAssetState {
    pub fn new<R: RngCore>(
        rng: &mut R,
        account: &AccountKeys,
        asset_id: AssetId,
    ) -> Self {
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

    pub fn mint<R: RngCore>(
        &mut self,
        rng: &mut R,
        amount: Balance,
    ) -> AccountState {
        let state = AccountState(self.current_state.0.get_state_for_mint(rng, amount));
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

/// Account asset registration proof.  Report section 5.1.3 "Account Registration".
pub struct AccountAssetRegistrationProof {
    proof: bp_account::RegTxnProof<PallasA>,
    challenge: <PallasA as AffineRepr>::ScalarField,
}

impl AccountAssetRegistrationProof {
    /// Generate a new account state for an asset and a registration proof for it.
    pub fn new(
        rng: &mut impl RngCore,
        account: &AccountKeys,
        asset_id: AssetId,
    ) -> (Self, AccountAssetState) {
        let account_state = account.init_asset_state(asset_id);
        let (proof, challenge) = bp_account::RegTxnProof::new(
            rng,
            account.acct.public.0.0,
            &account_state.current_state.0,
            account_state.current_state_commitment.0.clone(),
            b"test-nonce-0",
            &DART_GENS.account_comm_g(),
            DART_GENS.pk_acct_g,
        );
        (Self { proof, challenge }, account_state)
    }

    /// Verifies the account asset registration proof against the provided public key, asset ID, and account state commitment.
    pub fn verify(
        &self,
        pk: &AccountPublicKey,
        asset_id: AssetId,
        account_commitment: &AccountStateCommitment,
    ) -> bool {
        self.proof.verify(
            &pk.0.0,
            asset_id,
            &account_commitment.0,
            self.challenge,
            b"test-nonce-0",
            &DART_GENS.account_comm_g(),
            DART_GENS.pk_acct_g,
        ).is_ok()
    }
}

/// Asset minting proof.  Report section 5.1.4 "Increase Asset Supply".
pub struct AssetMintingProof<const L: usize> {
    // Public inputs.
    pk: AccountPublicKey,
    asset_id: AssetId,
    amount: Balance,
    root: CurveTreeRoot<L>,

    // proof
    proof: bp_account::MintTxnProof<L, <PallasParameters as CurveConfig>::ScalarField, <VestaParameters as CurveConfig>::ScalarField, PallasParameters, VestaParameters>,
    challenge: <PallasA as AffineRepr>::ScalarField,
}

impl<const L: usize> AssetMintingProof<L> {
    /// Generate a new asset minting proof.
    pub fn new(
        rng: &mut impl RngCore,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<L>,
        amount: Balance,
    ) -> Self {
        // Generate a new minting state for the account asset.
        let mint_account_state = account_asset.mint(rng, amount);
        let mint_account_commitment = mint_account_state.commitment();

        let pk = account_asset.account.acct.public;
        let current_account_state = &account_asset.current_state.0;
        let current_account_path = tree_lookup
            .get_path_to_leaf(account_asset.current_state_commitment.0.0)
            .expect("Failed to get path to current account state commitment");

        let root = tree_lookup.root_node();

        let (proof, challenge) = bp_account::MintTxnProof::new(
            rng,
            pk.0.0,
            amount,
            current_account_state,
            &mint_account_state.0,
            mint_account_commitment.0,
            current_account_path,
            b"test-nonce-0",
            tree_lookup.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.pk_acct_g,
        );
        Self {
            pk,
            asset_id: account_asset.asset_id,
            amount,
            proof, challenge, root
        }
    }

    pub fn verify(&self, tree_roots: impl ValidateCurveTreeRoot<L>) -> bool {
        // Validate the root of the curve tree.
        if !tree_roots.validate_root(&self.root).is_ok() {
            return false;
        }
        self.proof.verify(
            self.pk.0.0,
            self.asset_id,
            self.amount,
            &self.root,
            self.challenge,
            b"test-nonce-0",
            tree_roots.params(),
            &DART_GENS.account_comm_g(),
            DART_GENS.pk_acct_g,
        ).is_ok()
    }
}

/// Represents the auditor or mediator in a leg of the Dart BP protocol.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AuditorOrMediator {
    Mediator(AccountPublicKeys),
    Auditor(EncryptionPublicKey),
}

impl AuditorOrMediator {
    pub fn get_keys(&self) -> (EncryptionPublicKey, Option<AccountPublicKey>) {
        match self {
            AuditorOrMediator::Mediator(pk) => (pk.enc, Some(pk.acct)),
            AuditorOrMediator::Auditor(pk) => (*pk, None),
        }
    }
}

pub enum LegRole {
    Sender,
    Receiver,
    Auditor,
    Mediator,
}

pub struct Leg(bp_leg::Leg<PallasA>);

impl Leg {
    pub fn new(
        sender: AccountPublicKey,
        receiver: AccountPublicKey,
        mediator: Option<AccountPublicKey>,
        asset_id: AssetId,
        amount: Balance
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
        ephemeral_key: bp_leg::EphemeralSkEncryption<PallasA>,
        pk_e: &PallasA,
    ) -> LegEncrypted {
        let (leg_enc, _) = self.0.encrypt(rng, pk_e, DART_GENS.leg_g, DART_GENS.leg_h);
        LegEncrypted { leg_enc, ephemeral_key }
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

pub struct LegBuilder {
    sender: AccountPublicKeys,
    receiver: AccountPublicKeys,
    asset_id: AssetId,
    amount: Balance,
    mediator: AuditorOrMediator,
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

    pub fn encryt<R: RngCore>(
        &self,
        rng: &mut R,
    ) -> LegEncrypted {
        let (mediator_enc, mediator_acct) = self.mediator.get_keys();
        let leg = Leg::new(
            self.sender.acct,
            self.receiver.acct,
            mediator_acct,
            self.asset_id,
            self.amount,
        );
        let (ephemeral_key, _eph_ek_enc_r, _sk_e, pk_e) =
            bp_leg::EphemeralSkEncryption::new::<_, Blake2b512>(rng, self.sender.enc.0.0, self.receiver.enc.0.0, mediator_enc.0.0, DART_GENS.leg_g, DART_GENS.leg_h);
        leg.encrypt(rng, ephemeral_key, &pk_e.0)
    }
}

pub struct LegEncrypted {
    leg_enc: bp_leg::LegEncryption<PallasA>,
    ephemeral_key: bp_leg::EphemeralSkEncryption<PallasA>,
}

impl LegEncrypted {
    pub fn decrypt(&self, role: LegRole, sk: &EncryptionSecretKey) -> Leg {
        let sk_e = match role {
            LegRole::Sender => self.ephemeral_key.decrypt_for_sender::<Blake2b512>(sk.0.0),
            LegRole::Receiver => self.ephemeral_key.decrypt_for_receiver::<Blake2b512>(sk.0.0),
            LegRole::Auditor | LegRole::Mediator => self.ephemeral_key.decrypt_for_mediator_or_auditor::<Blake2b512>(sk.0.0),
        };
        let leg = self.leg_enc.decrypt(&sk_e, DART_GENS.leg_h);
        Leg(leg)
    }
}
