use dock_crypto_utils::transcript::Transcript as _;
#[cfg(feature = "parallel")]
use rayon::prelude::*;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use ark_ec::short_weierstrass::Affine;
use ark_std::vec::Vec;
use bulletproofs::r1cs::{ConstraintSystem as _, VerificationTuple};
use curve_tree_relations::curve_tree::Root;

use bounded_collections::BoundedVec;
use codec::{Decode, DecodeWithMemTracking, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use rand_core::{CryptoRng, RngCore, SeedableRng as _};

use super::encode::*;
use super::*;
use crate::auth_proofs::{create_fee_account_auth_proof, create_fee_payment_auth_proof};
use crate::fee_split::{FeeRegHostProtocol, FeeTopupHostProtocol};
use crate::*;
use dock_crypto_utils::randomized_mult_checker::PairRandomizedMultCheckerGuard;
use polymesh_dart_bp::util::{batch_verify_bp_with_rng, serialize_challenge};
use polymesh_dart_bp::{AUTH_PROOF_LABEL, TXN_CHALLENGE_LABEL, fee_account as bp_fee_account};

type BPFeeAccountState = bp_fee_account::FeeAccountState<PallasA>;
type BPFeeAccountStateCommitment = bp_fee_account::FeeAccountStateCommitment<PallasA>;

pub trait FeeAccountStateUpdate {
    fn account_state_commitment(&self) -> FeeAccountStateCommitment;
    fn nullifier(&self) -> FeeAccountStateNullifier;
    fn root_block(&self) -> BlockNumber;
}

#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "sqlx", derive(sqlx::FromRow))]
pub struct FeeAccountState {
    pub pk: AccountPublicKey,
    pub balance: Balance,
    pub asset_id: AssetId,
    pub initial_rho: WrappedCanonical<PallasScalar>,
    pub initial_randomness: WrappedCanonical<PallasScalar>,
    pub rho: WrappedCanonical<PallasScalar>,
    pub randomness: WrappedCanonical<PallasScalar>,
}

impl FeeAccountState {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountPublicKey,
        asset_id: AssetId,
        balance: Balance,
    ) -> Result<Self, Error> {
        let bp_state = BPFeeAccountState::new(rng, account.get_affine()?, balance, asset_id);
        bp_state.try_into()
    }

    pub fn bp_state(&self) -> Result<(BPFeeAccountState, BPFeeAccountStateCommitment), Error> {
        let state = BPFeeAccountState {
            pk: self.pk.get_affine()?,
            balance: self.balance,
            asset_id: self.asset_id,
            initial_rho: self.initial_rho.decode()?,
            initial_randomness: self.initial_randomness.decode()?,
            rho: self.rho.decode()?,
            randomness: self.randomness.decode()?,
        };
        let commitment = state.commit(dart_gens().account_comm_key())?;
        Ok((state, commitment))
    }

    pub fn commitment(&self) -> Result<FeeAccountStateCommitment, Error> {
        let (_state, commitment) = self.bp_state()?;
        FeeAccountStateCommitment::from_affine(commitment.0)
    }

    pub fn nullifier(&self) -> Result<FeeAccountStateNullifier, Error> {
        let account_comm_key = dart_gens().account_comm_key();
        let rho = self.rho.decode()?;
        let nullifier = (account_comm_key.rho_gen() * rho).into();
        FeeAccountStateNullifier::from_affine(nullifier)
    }
}

impl TryFrom<BPFeeAccountState> for FeeAccountState {
    type Error = Error;

    fn try_from(state: BPFeeAccountState) -> Result<Self, Self::Error> {
        Ok(Self {
            pk: AccountPublicKey::from_affine(state.pk)?,
            balance: state.balance,
            asset_id: state.asset_id,
            initial_rho: WrappedCanonical::wrap(&state.initial_rho)?,
            initial_randomness: WrappedCanonical::wrap(&state.initial_randomness)?,
            rho: WrappedCanonical::wrap(&state.rho)?,
            randomness: WrappedCanonical::wrap(&state.randomness)?,
        })
    }
}

#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct FeeAccountStateNullifier(CompressedAffine);

impl FeeAccountStateNullifier {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }
}

#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub struct FeeAccountStateCommitment(CompressedAffine);

impl FeeAccountStateCommitment {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    pub fn as_leaf_value(&self) -> Result<CompressedLeafValue<FeeAccountTreeConfig>, Error> {
        Ok(self.0.into())
    }

    pub fn as_commitment(&self) -> Result<BPFeeAccountStateCommitment, Error> {
        Ok(bp_fee_account::FeeAccountStateCommitment(
            self.get_affine()?,
        ))
    }
}

impl From<CompressedLeafValue<FeeAccountTreeConfig>> for FeeAccountStateCommitment {
    fn from(ca: CompressedLeafValue<FeeAccountTreeConfig>) -> Self {
        Self(ca.into())
    }
}

impl From<CompressedAffine> for FeeAccountStateCommitment {
    fn from(ca: CompressedAffine) -> Self {
        Self(ca)
    }
}

impl From<FeeAccountStateCommitment> for CompressedAffine {
    fn from(asc: FeeAccountStateCommitment) -> Self {
        asc.0
    }
}

#[derive(Clone, Debug)]
pub struct FeeAccountAssetStateChange {
    pub current_state: BPFeeAccountState,
    pub current_commitment: BPFeeAccountStateCommitment,
    pub new_state: BPFeeAccountState,
    pub new_commitment: BPFeeAccountStateCommitment,
}

impl FeeAccountAssetStateChange {
    pub fn commitment(&self) -> Result<FeeAccountStateCommitment, Error> {
        FeeAccountStateCommitment::from_affine(self.new_commitment.0)
    }

    pub fn get_path<
        C: CurveTreeConfig<
                F0 = <PallasParameters as CurveConfig>::ScalarField,
                F1 = <VestaParameters as CurveConfig>::ScalarField,
                P0 = PallasParameters,
                P1 = VestaParameters,
            >,
    >(
        &self,
        tree_lookup: &impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<CurveTreePath<FEE_ACCOUNT_TREE_L, C>, Error> {
        tree_lookup.get_path_to_leaf(CompressedLeafValue::from_affine(self.current_commitment.0)?)
    }
}

#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct FeeAccountAssetState {
    pub current_state: FeeAccountState,
    pub pending_state: Option<FeeAccountState>,
}

impl FeeAccountAssetState {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountPublicKey,
        asset_id: AssetId,
        balance: Balance,
    ) -> Result<Self, Error> {
        let current_state = FeeAccountState::new(rng, account, asset_id, balance)?;
        Ok(Self {
            current_state,
            pending_state: None,
        })
    }

    pub fn current_commitment(&self) -> Result<FeeAccountStateCommitment, Error> {
        self.current_state.commitment()
    }

    pub fn asset_id(&self) -> AssetId {
        self.current_state.asset_id
    }

    pub fn pk(&self) -> AccountPublicKey {
        self.current_state.pk
    }

    pub fn bp_current_state(
        &self,
    ) -> Result<(BPFeeAccountState, BPFeeAccountStateCommitment), Error> {
        self.current_state.bp_state()
    }

    fn state_change(
        &mut self,
        update: impl FnOnce(&BPFeeAccountState) -> Result<BPFeeAccountState, Error>,
    ) -> Result<FeeAccountAssetStateChange, Error> {
        let (current_state, current_commitment) = self.bp_current_state()?;

        // Update the state.
        let new_state = update(&current_state)?;
        let new_commitment = new_state.commit(dart_gens().account_comm_key())?;

        // Set the pending state.
        self.pending_state = Some(new_state.clone().try_into()?);

        Ok(FeeAccountAssetStateChange {
            current_state,
            current_commitment,
            new_state,
            new_commitment,
        })
    }

    pub fn topup(&mut self, amount: Balance) -> Result<FeeAccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_topup(amount)?))
    }

    pub fn get_payment_state(
        &mut self,
        amount: Balance,
    ) -> Result<FeeAccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_payment(amount)?))
    }

    pub fn commit_pending_state(&mut self) -> Result<bool, Error> {
        match self.pending_state.take() {
            Some(pending_state) => {
                self.current_state = pending_state;
                Ok(true)
            }
            None => Ok(false),
        }
    }
}

/// Fee account registration proof to initialize an account for an fee payment asset.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct FeeAccountRegistrationProof<T: DartLimits = ()> {
    pub account: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub account_state_commitment: FeeAccountStateCommitment,

    pub(crate) inner: BoundedCanonical<bp_fee_account::RegTxnProof<PallasA>, T::MaxInnerProofSize>,
}

impl<T: DartLimits> FeeAccountRegistrationProof<T> {
    /// Generate a new account state for an asset and a registration proof for it.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        key: &AccountKeyPair,
        asset_id: AssetId,
        balance: Balance,
        identity: &[u8],
    ) -> Result<(Self, FeeAccountAssetState), Error> {
        let gens = dart_gens();
        let account_state = FeeAccountAssetState::new(rng, &key.public, asset_id, balance)?;

        let (protocol, device_request) =
            FeeRegHostProtocol::init(rng, &key.public, &account_state, identity)?;

        let device_response = create_fee_account_auth_proof(
            rng,
            key,
            &device_request,
            gens.account_comm_key().sk_gen(),
        )?;

        let proof = protocol.finish(&device_response)?;
        Ok((proof, account_state))
    }

    /// Verifies the account asset registration proof against the provided public key, asset ID, and account state commitment.
    pub fn verify(&self, identity: &[u8]) -> Result<(), Error> {
        let proof = self.inner.decode()?;
        proof.verify_split(
            &self.account.get_affine()?,
            self.amount,
            self.asset_id,
            &self.account_state_commitment.as_commitment()?,
            identity,
            dart_gens().account_comm_key(),
        )?;
        Ok(())
    }
}

/// A batch of Fee account registration proofs.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct BatchedFeeAccountRegistrationProof<T: DartLimits = ()> {
    pub proofs: BoundedVec<FeeAccountRegistrationProof<T>, T::MaxFeeAccountRegProofs>,
}

impl<T: DartLimits> BatchedFeeAccountRegistrationProof<T> {
    /// Generate a new batched fee account registration proof.
    #[cfg(feature = "parallel")]
    pub fn new<R: RngCore + CryptoRng + Send + Sync + Clone>(
        rng: &mut R,
        registrations: &[(&AccountKeyPair, AssetId, Balance)],
        identity: &[u8],
    ) -> Result<(Self, Vec<FeeAccountAssetState>), Error> {
        // Generate random seeds for each proof generation.
        let seeds = (0..registrations.len())
            .map(|_| {
                let mut seed = [0u8; 32];
                rng.fill_bytes(&mut seed);
                seed
            })
            .collect::<Vec<_>>();

        let proofs_and_states = registrations
            .into_par_iter()
            .zip(seeds)
            .map(|((account, asset_id, balance), seed)| {
                let mut rng = rand_chacha::ChaCha20Rng::from_seed(seed);
                FeeAccountRegistrationProof::new(&mut rng, account, *asset_id, *balance, identity)
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let mut proofs = BoundedVec::with_bounded_capacity(registrations.len());
        let mut states = Vec::with_capacity(registrations.len());

        for (proof, state) in proofs_and_states {
            proofs
                .try_push(proof)
                .map_err(|_| Error::TooManyBatchedProofs)?;
            states.push(state);
        }

        Ok((Self { proofs }, states))
    }

    /// Generate a new batched fee account registration proof.
    #[cfg(not(feature = "parallel"))]
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        registrations: &[(&AccountKeyPair, AssetId, Balance)],
        identity: &[u8],
    ) -> Result<(Self, Vec<FeeAccountAssetState>), Error> {
        let mut proofs = BoundedVec::with_bounded_capacity(registrations.len());
        let mut states = Vec::with_capacity(registrations.len());

        for (account, asset_id, balance) in registrations {
            let mut seed = [0u8; 32];
            rng.fill_bytes(&mut seed);
            let mut rng = rand_chacha::ChaCha20Rng::from_seed(seed);
            let (proof, state) =
                FeeAccountRegistrationProof::new(&mut rng, account, *asset_id, *balance, identity)?;
            proofs
                .try_push(proof)
                .map_err(|_| Error::TooManyAccountAssetRegProofs)?;
            states.push(state);
        }

        Ok((Self { proofs }, states))
    }

    /// Verify the batched fee account registration proofs.
    #[cfg(feature = "parallel")]
    pub fn verify(&self, identity: &[u8]) -> Result<(), Error> {
        self.proofs
            .par_iter()
            .try_for_each(|proof| proof.verify(identity))?;
        Ok(())
    }

    /// Verify the batched fee account registration proofs.
    #[cfg(not(feature = "parallel"))]
    pub fn verify(&self, identity: &[u8]) -> Result<(), Error> {
        for proof in &self.proofs {
            proof.verify(identity)?;
        }
        Ok(())
    }

    /// Get the number of proofs in the batch.
    pub fn len(&self) -> usize {
        self.proofs.len()
    }

    /// Get the total amount of all proofs in the batch.
    pub fn total_amount(&self, asset_id: AssetId) -> Balance {
        let mut total: Balance = 0;
        for proof in &self.proofs {
            if proof.asset_id == asset_id {
                total = total.saturating_add(proof.amount);
            }
        }
        total
    }
}

type BPFeeAccountTopupTxnProof<C> = bp_fee_account::FeeAccountTopupTxnProof<
    FEE_ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// Fee payment account topup proof.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T, C))]
pub struct FeeAccountTopupProof<T: DartLimits = (), C: CurveTreeConfig = FeeAccountTreeConfig> {
    pub account: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub updated_account_state_commitment: FeeAccountStateCommitment,
    pub nullifier: FeeAccountStateNullifier,

    pub(crate) inner: BoundedCanonical<BPFeeAccountTopupTxnProof<C>, T::MaxInnerProofSize>,
}

impl<
    T: DartLimits,
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> FeeAccountTopupProof<T, C>
{
    /// Generate a new topup proof for the given state change.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        key: &AccountKeyPair,
        account_state: &mut FeeAccountAssetState,
        amount: Balance,
        ctx: &[u8],
        tree_lookup: &impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        let (protocol, device_request) = FeeTopupHostProtocol::<C>::init(
            rng,
            &key.public,
            account_state,
            amount,
            ctx,
            tree_lookup,
        )?;

        let device_response = create_fee_account_auth_proof(
            rng,
            key,
            &device_request,
            dart_gens().account_comm_key().sk_gen(),
        )?;

        let proof = protocol.finish(rng, &device_response, tree_lookup.params())?;

        Ok(proof)
    }

    /// Verifies the topup proof against the provided public key, asset ID, amount, and account state commitment.
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        root: &Root<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C::P0, C::P1>,
    ) -> Result<(), Error> {
        PairRandomizedMultCheckerGuard::new_using_rng(rng).with(
            |even_rmc, odd_rmc| -> Result<(), Error> {
                let proof = self.inner.decode()?;
                proof.verify_split(
                    self.account.get_affine()?,
                    self.asset_id,
                    self.amount,
                    self.updated_account_state_commitment.as_commitment()?,
                    self.nullifier.get_affine()?,
                    &root,
                    ctx,
                    C::parameters(),
                    dart_gens().account_comm_key(),
                    rng,
                    Some((even_rmc, odd_rmc)),
                )?;
                Ok(())
            },
        )?;

        Ok(())
    }

    /// Verify this fee account topup proof inside a batch of proofs.
    pub(crate) fn batched_verify<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        root: &Root<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C::P0, C::P1>,
    ) -> Result<
        (
            VerificationTuple<Affine<C::P0>>,
            VerificationTuple<Affine<C::P1>>,
        ),
        Error,
    > {
        let proof = self.inner.decode()?;
        let tuples = proof.verify_split_and_return_tuples(
            self.account.get_affine()?,
            self.asset_id,
            self.amount,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            &root,
            ctx,
            C::parameters(),
            dart_gens().account_comm_key(),
            rng,
            None,
        )?;
        Ok(tuples)
    }
}

/// A batch of Fee account topup proofs.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T, C))]
pub struct BatchedFeeAccountTopupProof<
    T: DartLimits = (),
    C: CurveTreeConfig = FeeAccountTreeConfig,
> {
    pub root_block: BlockNumber,

    pub proofs: BoundedVec<FeeAccountTopupProof<T, C>, T::MaxFeeAccountTopupProofs>,
}

impl<
    T: DartLimits,
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> BatchedFeeAccountTopupProof<T, C>
{
    /// Generate a new batched fee account topups proof.
    #[cfg(feature = "parallel")]
    pub fn new<R: RngCore + CryptoRng + Send + Sync + Clone>(
        rng: &mut R,
        topups: &mut [(&AccountKeyPair, Balance, FeeAccountAssetState)],
        ctx: &[u8],
        tree_lookup: impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C> + Send + Sync,
    ) -> Result<Self, Error> {
        // Generate random seeds for each proof generation.
        let seeds = (0..topups.len())
            .map(|_| {
                let mut seed = [0u8; 32];
                rng.fill_bytes(&mut seed);
                seed
            })
            .collect::<Vec<_>>();

        let root_block = tree_lookup.get_block_number()?;

        let proofs_vec = topups
            .par_iter_mut()
            .zip(seeds)
            .map(|((key, amount, account_state), seed)| {
                let mut rng = rand_chacha::ChaCha20Rng::from_seed(seed);
                FeeAccountTopupProof::new(&mut rng, key, account_state, *amount, ctx, &tree_lookup)
            })
            .collect::<Result<Vec<_>, Error>>()?;

        let mut proofs = BoundedVec::with_bounded_capacity(topups.len());
        for proof in proofs_vec {
            proofs
                .try_push(proof)
                .map_err(|_| Error::TooManyBatchedProofs)?;
        }

        Ok(Self {
            root_block: try_block_number(root_block)?,
            proofs,
        })
    }

    /// Generate a new batched fee account topups proof.
    #[cfg(not(feature = "parallel"))]
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        topups: &mut [(&AccountKeyPair, Balance, FeeAccountAssetState)],
        ctx: &[u8],
        tree_lookup: &impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        let root_block = tree_lookup.get_block_number()?;

        let mut proofs = BoundedVec::with_bounded_capacity(topups.len());
        for (key, amount, account_state) in topups.iter_mut() {
            let proof =
                FeeAccountTopupProof::new(rng, key, account_state, *amount, ctx, tree_lookup)?;
            proofs
                .try_push(proof)
                .map_err(|_| Error::TooManyBatchedProofs)?;
        }
        Ok(Self {
            root_block: try_block_number(root_block)?,
            proofs,
        })
    }

    /// Verify the batched fee account topup proofs.
    #[cfg(feature = "parallel")]
    pub fn verify<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        tree_roots: &(
             impl ValidateCurveTreeRoot<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C> + Send + Sync
         ),
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for fee account topup proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        // NOTE: This could single pair of RMC if allowed to pass the pair in proof.verify
        self.proofs
            .par_iter()
            .try_for_each_init(|| rng.clone(), |rng, proof| proof.verify(rng, ctx, &root))?;
        Ok(())
    }

    /// Verify the batched fee account topup proofs.
    #[cfg(not(feature = "parallel"))]
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        tree_roots: &impl ValidateCurveTreeRoot<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for fee account topup proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        for proof in &self.proofs {
            proof.verify(rng, ctx, &root)?;
        }
        Ok(())
    }

    /// Verify the batched fee account topup proofs.
    #[cfg(feature = "parallel")]
    pub fn batched_verify<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        tree_roots: &(
             impl ValidateCurveTreeRoot<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C> + Send + Sync
         ),
    ) -> Result<(), Error> {
        let batch_size = self.proofs.len();
        if batch_size < 2 {
            return self.verify(rng, ctx, tree_roots);
        }

        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for fee account topup proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let tuples = self
            .proofs
            .par_iter()
            .map_init(
                || rng.clone(),
                |rng, proof| proof.batched_verify(rng, ctx, &root),
            )
            .collect::<Result<Vec<_>, Error>>()?;

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);
        for (even, odd) in tuples {
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        let params = C::parameters();
        batch_verify_bp_with_rng(
            even_tuples,
            odd_tuples,
            params.even_parameters.pc_gens(),
            params.odd_parameters.pc_gens(),
            params.even_parameters.bp_gens(),
            params.odd_parameters.bp_gens(),
            rng,
        )?;

        Ok(())
    }

    /// Verify the batched fee account topup proofs.
    #[cfg(not(feature = "parallel"))]
    pub fn batched_verify<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        tree_roots: &impl ValidateCurveTreeRoot<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<(), Error> {
        let batch_size = self.proofs.len();
        if batch_size < 2 {
            return self.verify(rng, ctx, tree_roots);
        }

        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for fee account topup proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);
        for proof in &self.proofs {
            let (even, odd) = proof.batched_verify(rng, ctx, &root)?;
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        let params = C::parameters();
        batch_verify_bp_with_rng(
            even_tuples,
            odd_tuples,
            params.even_parameters.pc_gens(),
            params.odd_parameters.pc_gens(),
            params.even_parameters.bp_gens(),
            params.odd_parameters.bp_gens(),
            rng,
        )?;

        Ok(())
    }

    /// Get the number of proofs in the batch.
    pub fn len(&self) -> usize {
        self.proofs.len()
    }

    /// Get the total amount of all proofs in the batch.
    pub fn total_amount(&self, asset_id: AssetId) -> Balance {
        let mut total: Balance = 0;
        for proof in &self.proofs {
            if proof.asset_id == asset_id {
                total = total.saturating_add(proof.amount);
            }
        }
        total
    }
}

#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T, C))]
pub struct FeeAccountPaymentProof<T: DartLimits = (), C: CurveTreeConfig = FeeAccountTreeConfig> {
    pub asset_id: AssetId,
    pub amount: Balance,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: FeeAccountStateCommitment,
    pub nullifier: FeeAccountStateNullifier,

    pub(crate) inner: BoundedCanonical<BPFeePaymentSplitProof<C>, T::MaxInnerProofSize>,
}

impl<
    T: DartLimits,
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> FeeAccountPaymentProof<T, C>
{
    /// Generate a new payment proof for the given fee payment account.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        key: &AccountKeyPair,
        ctx: &[u8],
        account_state: &mut FeeAccountAssetState,
        amount: Balance,
        tree_lookup: impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        let root_block = tree_lookup.get_block_number()?;

        let (protocol, device_request) =
            FeePaymentHostProtocol::<C>::init(rng, account_state, amount, ctx, &tree_lookup)?;

        let gens = dart_gens();
        let tree_params = tree_lookup.params();
        let comm_re_rand_gen = tree_params.even_parameters.sl_params.pc_gens().B_blinding;
        let device_response = create_fee_payment_auth_proof(
            rng,
            key,
            &device_request,
            gens.account_comm_key().sk_gen(),
            gens.account_comm_key().randomness_gen(),
            comm_re_rand_gen,
        )?;

        let proof = protocol.finish(rng, &device_response, root_block, tree_params)?;
        Ok(proof)
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        tree_roots: impl ValidateCurveTreeRoot<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<(), Error> {
        PairRandomizedMultCheckerGuard::new_using_rng(rng).with(
            |even_rmc, odd_rmc| -> Result<(), Error> {
                let root = tree_roots
                    .get_block_root(self.root_block.into())
                    .ok_or(Error::CurveTreeRootNotFound)?;
                let root = root.root_node()?;
                let proof = self.inner.decode()?;
                let account_comm_key = dart_gens().account_comm_key();
                let updated_account_commitment =
                    self.updated_account_state_commitment.as_commitment()?;
                let nullifier = self.nullifier.get_affine()?;

                // Phase 1: derive challenge_h from host transcript
                let (mut even_verifier, odd_verifier, challenge_h) = proof
                    .challenge_contribution::<C::DLogParams0, C::DLogParams1>(
                        self.asset_id,
                        self.amount,
                        updated_account_commitment,
                        nullifier,
                        &root,
                        ctx,
                        tree_roots.params(),
                        account_comm_key.clone(),
                    )?;

                // Phase 2: reconstruct ledger_nonce and verify auth proof
                let challenge_h_bytes = serialize_challenge(&challenge_h)?;
                let ledger_nonce: Vec<u8> = challenge_h_bytes
                    .iter()
                    .chain(ctx.iter())
                    .copied()
                    .collect();

                let sk_gen = account_comm_key.sk_gen();
                let randomness_gen = account_comm_key.randomness_gen();
                let b_blinding = tree_roots
                    .params()
                    .even_parameters
                    .sl_params
                    .pc_gens()
                    .B_blinding;

                let rerandomized_leaf = proof.partial.rerandomized_leaf();
                proof.commitment_proof.auth_proof.verify(
                    &rerandomized_leaf,
                    &updated_account_commitment.0,
                    nullifier,
                    &ledger_nonce,
                    sk_gen,
                    randomness_gen,
                    b_blinding,
                    Some(even_rmc),
                )?;

                // Phase 3: hash auth_proof into transcript, derive final challenge, verify host
                let mut auth_proof_bytes = Vec::new();
                proof
                    .commitment_proof
                    .auth_proof
                    .serialize_compressed(&mut auth_proof_bytes)?;
                even_verifier
                    .transcript()
                    .append_message(AUTH_PROOF_LABEL, &auth_proof_bytes);
                let challenge_h_final = even_verifier
                    .transcript()
                    .challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);

                let (even_tuple, odd_tuple) =
                proof.verify_host_and_return_tuples_with_given_challenge::<
                    _,
                    C::DLogParams0,
                    C::DLogParams1,
                >(
                    &challenge_h_final,
                    even_verifier,
                    odd_verifier,
                    self.asset_id,
                    self.amount,
                    updated_account_commitment,
                    nullifier,
                    tree_roots.params(),
                    account_comm_key,
                    rng,
                    Some(even_rmc),
                )?;

                polymesh_dart_bp::util::handle_verification_tuples(
                    even_tuple,
                    odd_tuple,
                    tree_roots.params(),
                    Some((even_rmc, odd_rmc)),
                )?;

                Ok(())
            },
        )?;

        Ok(())
    }
}

/// Fee payment + batch of proofs.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T, C))]
pub struct FeePaymentWithBatchedProofs<
    T: DartLimits = (),
    C: CurveTreeConfig = FeeAccountTreeConfig,
> {
    pub fee_payment: FeeAccountPaymentProof<T, C>,
    pub batched_proofs: BatchedProofs<T>,
}

pub const FEE_PAYMENT_BATCH_CTX: &[u8] = b"FeePaymentBatch";

impl<
    T: DartLimits,
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> FeePaymentWithBatchedProofs<T, C>
{
    /// Generate a new fee payment for a batch of proofs.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        key: &AccountKeyPair,
        batched_proofs: BatchedProofs<T>,
        account_state: &mut FeeAccountAssetState,
        amount: Balance,
        tree_lookup: impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        let ctx = batched_proofs.ctx(FEE_PAYMENT_BATCH_CTX);
        let fee_payment =
            FeeAccountPaymentProof::new(rng, key, &ctx.0, account_state, amount, tree_lookup)?;

        Ok(Self {
            fee_payment,
            batched_proofs,
        })
    }

    /// Verifies only the fee payment for this batch of proofs.
    pub fn verify_fee_payment<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        tree_roots: impl ValidateCurveTreeRoot<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<(), Error> {
        let ctx = self.batched_proofs.ctx(FEE_PAYMENT_BATCH_CTX);
        self.fee_payment.verify(rng, &ctx.0, tree_roots)
    }

    /// Get the fee payment ctx for this batch of proofs.
    pub fn fee_payment_ctx(&self) -> ProofHash {
        self.batched_proofs.ctx(FEE_PAYMENT_BATCH_CTX)
    }
}
