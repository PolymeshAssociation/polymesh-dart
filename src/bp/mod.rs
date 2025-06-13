use ark_ec::{AffineRepr, CurveConfig};
use ark_ff::UniformRand as _;
use blake2::Blake2s256;

use dart_bp::{
    account_new as bp_account,
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
            PallasA::rand(&mut rng), // field: sk -- TODO: Shouldn't this generator be the same `pk_acct_g`?
            PallasA::rand(&mut rng), // field: finalized balance.
            PallasA::rand(&mut rng), // field: counter
            PallasA::rand(&mut rng), // field: asset_id
            PallasA::rand(&mut rng), // field: random value rho
            PallasA::rand(&mut rng), // field: random value s
        ];
        Self { pk_acct_g, pk_enc_g, account_comm_g }
    }

    /// Returns the generators for account state commitments.
    pub fn account_comm_g(&self) -> &[PallasA] {
        &self.account_comm_g
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
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