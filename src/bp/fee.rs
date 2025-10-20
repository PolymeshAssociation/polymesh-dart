#[cfg(feature = "parallel")]
use rayon::prelude::*;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use ark_std::vec::Vec;
use curve_tree_relations::curve_tree::Root;

use bounded_collections::BoundedVec;
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use rand_core::{CryptoRng, RngCore};

use polymesh_dart_bp::fee_account as bp_fee_account;

use super::encode::*;
use super::*;
use crate::*;

type BPFeeAccountState = bp_fee_account::FeeAccountState<PallasA>;
type BPFeeAccountStateCommitment = bp_fee_account::FeeAccountStateCommitment<PallasA>;

pub trait FeeAccountStateUpdate {
    fn account_state_commitment(&self) -> FeeAccountStateCommitment;
    fn nullifier(&self) -> FeeAccountStateNullifier;
    fn root_block(&self) -> BlockNumber;
}

#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "sqlx", derive(sqlx::FromRow))]
pub struct FeeAccountState {
    pub balance: Balance,
    pub asset_id: AssetId,
    pub rho: WrappedCanonical<PallasScalar>,
    pub randomness: WrappedCanonical<PallasScalar>,
}

impl FeeAccountState {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        asset_id: AssetId,
        balance: Balance,
    ) -> Result<Self, Error> {
        let bp_state = BPFeeAccountState::new(rng, account.secret.0.0, balance, asset_id)?;
        bp_state.try_into()
    }

    pub fn bp_state(
        &self,
        account: &AccountKeyPair,
    ) -> Result<(BPFeeAccountState, BPFeeAccountStateCommitment), Error> {
        let state = BPFeeAccountState {
            sk: account.secret.0.0,
            balance: self.balance,
            asset_id: self.asset_id,
            rho: self.rho.decode()?,
            randomness: self.randomness.decode()?,
        };
        let commitment = state.commit(dart_gens().account_comm_key())?;
        Ok((state, commitment))
    }

    pub fn commitment(&self, account: &AccountKeyPair) -> Result<FeeAccountStateCommitment, Error> {
        let (_state, commitment) = self.bp_state(account)?;
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
            balance: state.balance,
            asset_id: state.asset_id,
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

#[derive(Copy, Clone, MaxEncodedLen, Encode, Decode, TypeInfo, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
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

#[derive(Clone, Debug, Encode, Decode)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct FeeAccountAssetState {
    pub current_state: FeeAccountState,
    pub pending_state: Option<FeeAccountState>,
}

impl FeeAccountAssetState {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        asset_id: AssetId,
        balance: Balance,
    ) -> Result<Self, Error> {
        let current_state = FeeAccountState::new(rng, account, asset_id, balance)?;
        Ok(Self {
            current_state,
            pending_state: None,
        })
    }

    pub fn current_commitment(
        &self,
        account: &AccountKeyPair,
    ) -> Result<FeeAccountStateCommitment, Error> {
        self.current_state.commitment(account)
    }

    pub fn asset_id(&self) -> AssetId {
        self.current_state.asset_id
    }

    pub fn bp_current_state(
        &self,
        account: &AccountKeyPair,
    ) -> Result<(BPFeeAccountState, BPFeeAccountStateCommitment), Error> {
        self.current_state.bp_state(account)
    }

    fn state_change(
        &mut self,
        account: &AccountKeyPair,
        update: impl FnOnce(&BPFeeAccountState) -> Result<BPFeeAccountState, Error>,
    ) -> Result<FeeAccountAssetStateChange, Error> {
        let (current_state, current_commitment) = self.bp_current_state(account)?;

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

    pub fn topup<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        account: &AccountKeyPair,
        amount: Balance,
    ) -> Result<FeeAccountAssetStateChange, Error> {
        self.state_change(account, |state| Ok(state.get_state_for_topup(rng, amount)?))
    }

    pub fn get_payment_state<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        account: &AccountKeyPair,
        amount: Balance,
    ) -> Result<FeeAccountAssetStateChange, Error> {
        self.state_change(account, |state| {
            Ok(state.get_state_for_payment(rng, amount)?)
        })
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
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct FeeAccountRegistrationProof {
    pub account: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub account_state_commitment: FeeAccountStateCommitment,
    pub nullifier: FeeAccountStateNullifier,

    proof: WrappedCanonical<bp_fee_account::RegTxnProof<PallasA>>,
}

impl FeeAccountRegistrationProof {
    /// Generate a new account state for an asset and a registration proof for it.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        asset_id: AssetId,
        balance: Balance,
        identity: &[u8],
    ) -> Result<(Self, FeeAccountAssetState), Error> {
        let pk = account.public;
        let account_state = FeeAccountAssetState::new(rng, account, asset_id, balance)?;
        let (bp_state, commitment) = account_state.bp_current_state(account)?;
        let nullifier = account_state.current_state.nullifier()?;
        let gens = dart_gens();
        let proof = bp_fee_account::RegTxnProof::new(
            rng,
            pk.get_affine()?,
            &bp_state,
            commitment,
            identity,
            gens.account_comm_key(),
        )?;
        Ok((
            Self {
                account: pk,
                asset_id,
                amount: balance,
                account_state_commitment: FeeAccountStateCommitment::from_affine(commitment.0)?,
                nullifier,

                proof: WrappedCanonical::wrap(&proof)?,
            },
            account_state,
        ))
    }

    /// Verifies the account asset registration proof against the provided public key, asset ID, and account state commitment.
    pub fn verify(&self, identity: &[u8]) -> Result<(), Error> {
        let proof = self.proof.decode()?;
        proof.verify(
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
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct BatchedFeeAccountRegistrationProof<T: DartLimits = ()> {
    pub proofs: BoundedVec<FeeAccountRegistrationProof, T::MaxFeeAccountRegProofs>,
}

impl<T: DartLimits> BatchedFeeAccountRegistrationProof<T> {
    /// Generate a new batched fee account registration proof.
    #[cfg(feature = "parallel")]
    pub fn new<R: RngCore + CryptoRng + Send + Sync + Clone>(
        rng: &mut R,
        registrations: &[(&AccountKeyPair, AssetId, Balance)],
        identity: &[u8],
    ) -> Result<(Self, Vec<FeeAccountAssetState>), Error> {
        let proofs_and_states = registrations
            .par_iter()
            .map_init(
                || rng.clone(),
                |rng, (account, asset_id, balance)| {
                    FeeAccountRegistrationProof::new(rng, account, *asset_id, *balance, identity)
                },
            )
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
            let (proof, state) =
                FeeAccountRegistrationProof::new(rng, account, *asset_id, *balance, identity)?;
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
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct FeeAccountTopupProof<C: CurveTreeConfig = FeeAccountTreeConfig> {
    pub account: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub updated_account_state_commitment: FeeAccountStateCommitment,
    pub nullifier: FeeAccountStateNullifier,

    proof: WrappedCanonical<BPFeeAccountTopupTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> FeeAccountTopupProof<C>
{
    /// Generate a new topup proof for the given state change.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        account_state: &mut FeeAccountAssetState,
        amount: Balance,
        ctx: &[u8],
        tree_lookup: &impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        let pk = account.public;
        let state_change = account_state.topup(rng, account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(tree_lookup)?;

        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let (proof, nullifier) = bp_fee_account::FeeAccountTopupTxnProof::new(
            rng,
            &pk.get_affine()?,
            amount,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx,
            tree_lookup.params(),
            dart_gens().account_comm_key(),
        )?;
        Ok(Self {
            account: pk,
            asset_id: state_change.new_state.asset_id,
            amount,
            updated_account_state_commitment,
            nullifier: FeeAccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    /// Verifies the topup proof against the provided public key, asset ID, amount, and account state commitment.
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        root: &Root<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C::P0, C::P1>,
    ) -> Result<(), Error> {
        let proof = self.proof.decode()?;
        proof.verify(
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
        Ok(())
    }
}

/// A batch of Fee account topup proofs.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T, C))]
pub struct BatchedFeeAccountTopupProof<
    T: DartLimits = (),
    C: CurveTreeConfig = FeeAccountTreeConfig,
> {
    pub root_block: BlockNumber,

    pub proofs: BoundedVec<FeeAccountTopupProof<C>, T::MaxFeeAccountTopupProofs>,
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
    /// Generate a new batched fee account topup proof.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        topups: &mut [(&AccountKeyPair, Balance, FeeAccountAssetState)],
        ctx: &[u8],
        tree_lookup: &impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        let root_block = tree_lookup.get_block_number()?;

        let mut proofs = BoundedVec::with_bounded_capacity(topups.len());
        let mut account_states = Vec::with_capacity(topups.len());
        for (account, amount, account_state) in topups.iter_mut() {
            let proof =
                FeeAccountTopupProof::new(rng, account, account_state, *amount, ctx, tree_lookup)?;
            account_states.push(account_state.clone());
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

type BPFeePaymentProof<C> = bp_fee_account::FeePaymentProof<
    FEE_ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// Fee payment proof.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct FeeAccountPaymentProof<C: CurveTreeConfig = FeeAccountTreeConfig> {
    pub asset_id: AssetId,
    pub amount: Balance,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: FeeAccountStateCommitment,
    pub nullifier: FeeAccountStateNullifier,

    proof: WrappedCanonical<BPFeePaymentProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> FeeAccountPaymentProof<C>
{
    /// Generate a new payment proof for the given fee payment account.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        ctx: &[u8],
        account_state: &mut FeeAccountAssetState,
        amount: Balance,
        tree_lookup: impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        let state_change = account_state.get_payment_state(rng, account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let (proof, nullifier) = bp_fee_account::FeePaymentProof::new(
            rng,
            amount,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx,
            tree_lookup.params(),
            dart_gens().account_comm_key(),
        )?;
        Ok(Self {
            asset_id: state_change.new_state.asset_id,
            amount,
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: FeeAccountStateNullifier::from_affine(nullifier)?,
            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    /// Verifies the payment proof against the provided asset ID, amount, and account state commitment.
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        ctx: &[u8],
        tree_roots: impl ValidateCurveTreeRoot<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for fee payment proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        let proof = self.proof.decode()?;
        proof.verify(
            self.asset_id,
            self.amount,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            &root,
            ctx,
            tree_roots.params(),
            dart_gens().account_comm_key(),
            rng,
            None,
        )?;
        Ok(())
    }
}

/// Fee payment + batch of proofs.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T, C))]
pub struct FeePaymentWithBatchedProofs<
    T: DartLimits = (),
    C: CurveTreeConfig = FeeAccountTreeConfig,
> {
    pub fee_payment: FeeAccountPaymentProof<C>,
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
        account: &AccountKeyPair,
        batched_proofs: BatchedProofs<T>,
        account_state: &mut FeeAccountAssetState,
        amount: Balance,
        tree_lookup: impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        let ctx = batched_proofs.ctx(FEE_PAYMENT_BATCH_CTX);
        let fee_payment =
            FeeAccountPaymentProof::new(rng, account, &ctx.0, account_state, amount, tree_lookup)?;

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
