use bulletproofs::{BulletproofGens, PedersenGens};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

#[cfg(feature = "ledger_device_sdk")]
use ledger_device_sdk::log;

use codec::{Decode, DecodeWithMemTracking, Encode, MaxEncodedLen};

use ark_ec::CurveConfig;
use ark_ff::Field;
use ark_std::UniformRand;
use ark_std::vec::Vec;

use bounded_collections::BoundedVec;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use rand_core::{CryptoRng, RngCore};

use polymesh_dart_bp::account::state::AccountCommitmentKeyTrait;
use polymesh_dart_bp::{account as bp_account, account_registration, auth_proofs, leg as bp_leg};
use polymesh_dart_common::NullifierSkGenCounter;

use super::*;
use crate::*;

pub type PallasParameters = ark_pallas::PallasConfig;

pub fn get_pc_gens() -> PedersenGens<PallasA> {
    PedersenGens::<PallasA>::new().expect("Failed to create Pedersen generators")
}

pub fn get_bp_gens() -> BulletproofGens<PallasA> {
    BulletproofGens::<PallasA>::new(MAX_CURVE_TREE_GENS as u32, 1)
}

pub(crate) type BPAccountState = bp_account::AccountState<PallasA>;
pub(crate) type BPAccountStateCommitment = bp_account::AccountStateCommitment<PallasA>;

pub type AssetCommitmentData =
    bp_leg::AssetData<PallasScalar, VestaScalar, PallasParameters, VestaParameters>;

pub trait AccountStateUpdate {
    fn account_state_commitment(&self) -> AccountStateCommitment;
    fn nullifier(&self) -> AccountStateNullifier;
    fn root_block(&self) -> BlockNumber;
}

#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "sqlx", derive(sqlx::FromRow))]
pub struct AccountState {
    pub balance: Balance,
    pub counter: PendingTxnCounter,
    pub identity: WrappedCanonical<PallasScalar>,
    pub asset_id: AssetId,
    pub rho: WrappedCanonical<PallasScalar>,
    pub current_rho: WrappedCanonical<PallasScalar>,
    pub randomness: WrappedCanonical<PallasScalar>,
    pub current_randomness: WrappedCanonical<PallasScalar>,
}

impl AccountState {
    pub fn bp_state(
        &self,
        account: &AccountKeyPair,
        enc_key: &EncryptionSecretKey,
    ) -> Result<(BPAccountState, BPAccountStateCommitment), Error> {
        log::debug!("-- bp_state: sk_enc_inv");
        let sk_enc_inv = enc_key
            .0
            .0
            .inverse()
            .ok_or(Error::CryptoError("Encryption key inversion failed".into()))?;
        log::debug!("-- bp_state: sk_enc_inv computed");
        let state = BPAccountState {
            sk: account.secret.0.0,
            id: self.identity.decode()?,
            balance: self.balance,
            counter: self.counter,
            asset_id: self.asset_id,
            rho: self.rho.decode()?,
            current_rho: self.current_rho.decode()?,
            randomness: self.randomness.decode()?,
            current_randomness: self.current_randomness.decode()?,
            sk_enc_inv,
        };
        log::debug!("-- bp_state: BPAccountState constructed");
        let commitment = state.commit(dart_gens().account_comm_key())?;
        log::debug!("-- bp_state: commitment computed");
        Ok((state, commitment))
    }

    pub fn commitment(
        &self,
        account: &AccountKeyPair,
        enc_key: &EncryptionSecretKey,
    ) -> Result<AccountStateCommitment, Error> {
        let (_state, commitment) = self.bp_state(account, enc_key)?;
        AccountStateCommitment::from_affine(commitment.0)
    }

    pub fn nullifier(&self) -> Result<AccountStateNullifier, Error> {
        let account_comm_key = dart_gens().account_comm_key();
        let current_rho = self.current_rho.decode()?;
        let nullifier = (account_comm_key.current_rho_gen() * current_rho).into();
        AccountStateNullifier::from_affine(nullifier)
    }
}

impl TryFrom<BPAccountState> for AccountState {
    type Error = Error;

    fn try_from(state: BPAccountState) -> Result<Self, Self::Error> {
        Ok(Self {
            balance: state.balance,
            counter: state.counter,
            asset_id: state.asset_id,
            identity: WrappedCanonical::wrap(&state.id)?,
            rho: WrappedCanonical::wrap(&state.rho)?,
            current_rho: WrappedCanonical::wrap(&state.current_rho)?,
            randomness: WrappedCanonical::wrap(&state.randomness)?,
            current_randomness: WrappedCanonical::wrap(&state.current_randomness)?,
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
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "scale-info", derive(scale_info::TypeInfo))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AccountStateNullifier(CompressedAffine);

impl AccountStateNullifier {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }
}

#[derive(
    Copy, Clone, MaxEncodedLen, Encode, Decode, DecodeWithMemTracking, Debug, PartialEq, Eq,
)]
#[cfg_attr(feature = "scale-info", derive(scale_info::TypeInfo))]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub struct AccountStateCommitment(CompressedAffine);

impl AccountStateCommitment {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    pub fn as_leaf_value(&self) -> Result<CompressedLeafValue<AccountTreeConfig>, Error> {
        Ok(self.0.into())
    }

    pub fn as_commitment(&self) -> Result<BPAccountStateCommitment, Error> {
        Ok(bp_account::AccountStateCommitment(self.get_affine()?))
    }
}

impl From<CompressedLeafValue<AccountTreeConfig>> for AccountStateCommitment {
    fn from(ca: CompressedLeafValue<AccountTreeConfig>) -> Self {
        Self(ca.into())
    }
}

impl From<CompressedAffine> for AccountStateCommitment {
    fn from(ca: CompressedAffine) -> Self {
        Self(ca)
    }
}

impl From<AccountStateCommitment> for CompressedAffine {
    fn from(asc: AccountStateCommitment) -> Self {
        asc.0
    }
}

#[derive(Clone, Debug)]
pub struct AccountAssetStateChange {
    pub current_state: BPAccountState,
    pub current_commitment: BPAccountStateCommitment,
    pub new_state: BPAccountState,
    pub new_commitment: BPAccountStateCommitment,
}

impl AccountAssetStateChange {
    pub fn commitment(&self) -> Result<AccountStateCommitment, Error> {
        AccountStateCommitment::from_affine(self.new_commitment.0)
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
        tree_lookup: &impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<CurveTreePath<ACCOUNT_TREE_L, C>, Error> {
        tree_lookup.get_path_to_leaf(CompressedLeafValue::from_affine(self.current_commitment.0)?)
    }
}

#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AccountAssetState {
    pub current_state: AccountState,
    pub pending_state: Option<AccountState>,
}

impl AccountAssetState {
    pub fn new(
        keys: &AccountKeys,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<Self, Error> {
        let current_state = keys.account_state(asset_id, counter, identity)?;
        Ok(Self {
            current_state,
            pending_state: None,
        })
    }

    pub fn current_commitment(&self, keys: &AccountKeys) -> Result<AccountStateCommitment, Error> {
        self.current_state.commitment(&keys.acct, &keys.enc.secret)
    }

    pub fn asset_id(&self) -> AssetId {
        self.current_state.asset_id
    }

    pub fn bp_current_state(
        &self,
        keys: &AccountKeys,
    ) -> Result<(BPAccountState, BPAccountStateCommitment), Error> {
        self.current_state.bp_state(&keys.acct, &keys.enc.secret)
    }

    fn state_change(
        &mut self,
        keys: &AccountKeys,
        update: impl FnOnce(&BPAccountState) -> Result<BPAccountState, Error>,
    ) -> Result<AccountAssetStateChange, Error> {
        log::debug!("-- state_change: bp_current_state");
        let (current_state, current_commitment) = self.bp_current_state(keys)?;
        log::debug!("-- state_change: bp_current_state computed");

        // Update the state.
        log::debug!("-- state_change: update");
        let new_state = update(&current_state)?;
        log::debug!("-- state_change: update computed");
        let new_commitment = new_state.commit(dart_gens().account_comm_key())?;
        log::debug!("-- state_change: new commitment computed");

        // Set the pending state.
        log::debug!("-- state_change: set pending state");
        self.pending_state = Some(new_state.clone().try_into()?);
        log::debug!("-- state_change: pending state set");

        Ok(AccountAssetStateChange {
            current_state,
            current_commitment,
            new_state,
            new_commitment,
        })
    }

    pub fn mint(
        &mut self,
        keys: &AccountKeys,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(keys, |state| Ok(state.get_state_for_mint(amount)?))
    }

    pub fn get_sender_affirm_state(
        &mut self,
        keys: &AccountKeys,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(keys, |state| Ok(state.get_state_for_send(amount)?))
    }

    pub fn get_receiver_affirm_state(
        &mut self,
        keys: &AccountKeys,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(keys, |state| Ok(state.get_state_for_receive()))
    }

    pub fn get_instant_sender_affirm_state(
        &mut self,
        keys: &AccountKeys,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(keys, |state| {
            Ok(state.get_state_for_irreversible_send(amount)?)
        })
    }

    pub fn get_instant_receiver_affirm_state(
        &mut self,
        keys: &AccountKeys,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(keys, |state| {
            Ok(state.get_state_for_irreversible_receive(amount)?)
        })
    }

    pub fn get_state_for_claiming_received(
        &mut self,
        keys: &AccountKeys,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(keys, |state| {
            Ok(state.get_state_for_claiming_received(amount)?)
        })
    }

    pub fn get_state_for_reversing_send(
        &mut self,
        keys: &AccountKeys,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(
            keys,
            |state| Ok(state.get_state_for_reversing_send(amount)?),
        )
    }

    pub fn get_state_for_decreasing_counter(
        &mut self,
        keys: &AccountKeys,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(keys, |state| {
            Ok(state.get_state_for_decreasing_counter(None)?)
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

/// Batched account asset registration proof.
///
/// This is used to register multiple account/asset pairs in a single proof.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "scale-info", derive(scale_info::TypeInfo))]
#[cfg_attr(feature = "scale-info", scale_info(skip_type_params(T)))]
pub struct BatchedAccountAssetRegistrationProof<T: DartLimits = ()> {
    pub proofs: BoundedVec<AccountAssetRegistrationProof, T::MaxAccountAssetRegProofs>,
}

impl<T: DartLimits> BatchedAccountAssetRegistrationProof<T> {
    /// Generate a new batched account asset registration proof.
    #[cfg(feature = "parallel")]
    pub fn new<R: RngCore + CryptoRng + Sync + Send + Clone>(
        rng: &mut R,
        account_assets: &[(AccountKeys, AssetId, NullifierSkGenCounter)],
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
    ) -> Result<(Self, Vec<AccountAssetState>), Error> {
        let proofs_and_states = account_assets
            .par_iter()
            .map_init(
                || rng.clone(),
                |rng, (account, asset_id, counter)| {
                    AccountAssetRegistrationProof::new(
                        rng,
                        account,
                        *asset_id,
                        *counter,
                        identity,
                        tree_params,
                    )
                },
            )
            .collect::<Result<Vec<_>, Error>>()?;

        let mut proofs = BoundedVec::with_bounded_capacity(account_assets.len());
        let mut states = Vec::with_capacity(account_assets.len());

        for (proof, state) in proofs_and_states {
            proofs
                .try_push(proof)
                .map_err(|_| Error::TooManyAccountAssetRegProofs)?;
            states.push(state);
        }

        Ok((Self { proofs }, states))
    }

    /// Generate a new batched account asset registration proof.
    #[cfg(not(feature = "parallel"))]
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account_assets: &[(AccountKeys, AssetId, NullifierSkGenCounter)],
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
    ) -> Result<(Self, Vec<AccountAssetState>), Error> {
        let mut proofs = BoundedVec::with_bounded_capacity(account_assets.len());
        let mut states = Vec::with_capacity(account_assets.len());

        for (account, asset_id, counter) in account_assets {
            let (proof, state) = AccountAssetRegistrationProof::new(
                rng,
                account,
                *asset_id,
                *counter,
                identity,
                tree_params,
            )?;
            proofs
                .try_push(proof)
                .map_err(|_| Error::TooManyAccountAssetRegProofs)?;
            states.push(state);
        }

        Ok((Self { proofs }, states))
    }

    /// Verify the batched account asset registration proof.
    #[cfg(feature = "parallel")]
    pub fn verify<R: RngCore + CryptoRng + Sync + Send + Clone>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        if self.proofs.len() == 0 {
            return Ok(());
        }
        self.proofs
            .par_iter()
            .map_init(
                || rng.clone(),
                |rng, proof| proof.verify(identity, tree_params, rng),
            )
            .collect::<Result<(), Error>>()?;
        Ok(())
    }

    /// Verify the batched account asset registration proof.
    #[cfg(not(feature = "parallel"))]
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        for proof in &self.proofs {
            proof.verify(identity, tree_params, rng)?;
        }
        Ok(())
    }

    /// Verify the batched account asset registration proof.
    #[cfg(feature = "parallel")]
    pub fn batched_verify<R: RngCore + CryptoRng + Sync + Send + Clone>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        if self.proofs.len() < 2 {
            return self.verify(identity, tree_params, rng);
        }

        // NOTE: This could use single RMC if allowed to pass in batched_verify
        let tuples = self
            .proofs
            .par_iter()
            .map_init(
                || rng.clone(),
                |rng, proof| proof.batched_verify(identity, tree_params, rng),
            )
            .collect::<Result<Vec<_>, Error>>()?;

        bulletproofs::r1cs::batch_verify_with_rng(
            tuples,
            tree_params.even_parameters.pc_gens(),
            tree_params.even_parameters.bp_gens(),
            rng,
        )?;

        Ok(())
    }

    /// Verify the batched account asset registration proof.
    #[cfg(not(feature = "parallel"))]
    pub fn batched_verify<R: RngCore + CryptoRng + Sync + Send + Clone>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        if self.proofs.len() < 2 {
            return self.verify(identity, tree_params, rng);
        }
        let mut tuples = Vec::with_capacity(self.proofs.len());

        for proof in &self.proofs {
            let tuple = proof.batched_verify(identity, tree_params, rng)?;
            tuples.push(tuple);
        }

        bulletproofs::r1cs::batch_verify_with_rng(
            tuples,
            tree_params.even_parameters.pc_gens(),
            tree_params.even_parameters.bp_gens(),
            rng,
        )?;

        Ok(())
    }

    /// Get the number of proofs in the batch.
    pub fn len(&self) -> usize {
        self.proofs.len()
    }
}

/// Authorization of account asset registration.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "scale-info", derive(scale_info::TypeInfo))]
pub struct AuthorizedAccountAssetRegistrationProof {
    pub account: AccountPublicKeys,
    pub asset_id: AssetId,
    pub counter: NullifierSkGenCounter,
    pub account_state_commitment: AccountStateCommitment,

    inner: WrappedCanonical<auth_proofs::AuthProofRegOnlyAffSk<PallasA>>,
}

impl AuthorizedAccountAssetRegistrationProof {
    /// Generate a new authorization proof for account asset registration.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        keys: &AccountKeys,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<(Self, AccountAssetState), Error> {
        let account_state = keys.init_asset_state(asset_id, counter, identity)?;
        let (_bp_state, commitment) = account_state.bp_current_state(keys)?;
        let pk_aff = keys.acct.public.get_affine()?;
        let rand_1 = PallasScalar::rand(rng);
        let gens = dart_gens();
        let nonce = (asset_id, counter, identity).encode();
        let proof = auth_proofs::AuthProofRegOnlyAffSk::new(
            rng,
            keys.acct.secret.0.0,
            rand_1,
            pk_aff,
            &commitment,
            &nonce,
            gens.account_comm_key(),
        )?;
        Ok((
            Self {
                account: keys.public_keys(),
                asset_id,
                counter,
                account_state_commitment: AccountStateCommitment::from_affine(commitment.0)?,

                inner: WrappedCanonical::wrap(&proof)?,
            },
            account_state,
        ))
    }

    /// Verify the authorization proof for account asset registration.
    pub fn verify(&self, identity: &[u8]) -> Result<(), Error> {
        let proof = self.inner.decode()?;
        let nonce = (self.asset_id, self.counter, identity).encode();
        let gens = dart_gens();
        proof.verify(
            self.account.acct.get_affine()?,
            &self.account_state_commitment.as_commitment()?,
            &nonce,
            gens.account_comm_key(),
        )?;
        Ok(())
    }
}

/// Account asset registration proof.  Report section 5.1.3 "Account Registration".
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, PartialEq, Eq)]
#[cfg_attr(feature = "scale-info", derive(scale_info::TypeInfo))]
pub struct AccountAssetRegistrationProof {
    pub account: AccountPublicKeys,
    pub asset_id: AssetId,
    pub counter: NullifierSkGenCounter,
    pub account_state_commitment: AccountStateCommitment,

    inner: WrappedCanonical<account_registration::RegTxnProof<PallasA>>,
}

impl AccountAssetRegistrationProof {
    /// Generate a new account state for an asset and a registration proof for it.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        keys: &AccountKeys,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
    ) -> Result<(Self, AccountAssetState), Error> {
        let account_state = keys.init_asset_state(asset_id, counter, identity)?;
        let (bp_state, commitment) = account_state.bp_current_state(keys)?;
        let params = PoseidonParameters::new()?;
        let gens = DartBPGenerators::new(DART_GEN_DOMAIN);
        let proof = account_registration::RegTxnProof::new(
            rng,
            keys.acct.public.get_affine()?,
            keys.enc.public.get_affine()?,
            &bp_state,
            commitment,
            counter,
            identity,
            gens.account_comm_key(),
            tree_params.even_parameters.pc_gens(),
            tree_params.even_parameters.bp_gens(),
            &params.params,
            None,
        )?;
        Ok((
            Self {
                account: keys.public_keys(),
                asset_id,
                counter,
                account_state_commitment: AccountStateCommitment::from_affine(commitment.0)?,

                inner: WrappedCanonical::wrap(&proof)?,
            },
            account_state,
        ))
    }

    /// Verifies the account asset registration proof against the provided public key, asset ID, and account state commitment.
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let proof = self.inner.decode()?;
        let params = poseidon_params();
        let id = hash_identity::<PallasScalar>(identity);

        let mut rmc = RandomizedMultChecker::new(PallasScalar::rand(rng));

        proof.verify(
            rng,
            id,
            &self.account.acct.get_affine()?,
            self.account.enc.get_affine()?,
            self.asset_id,
            &self.account_state_commitment.as_commitment()?,
            self.counter,
            identity,
            dart_gens().account_comm_key(),
            tree_params.even_parameters.pc_gens(),
            tree_params.even_parameters.bp_gens(),
            &params.params,
            None,
            Some(&mut rmc),
        )?;
        if !rmc.verify() {
            return Err(Error::RMCVerifyError);
        }
        Ok(())
    }

    /// Verify this registration proof inside a batch of proofs.
    pub(crate) fn batched_verify<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<bulletproofs::r1cs::VerificationTuple<PallasA>, Error> {
        let proof = self.inner.decode()?;
        let params = poseidon_params();
        let id = hash_identity::<PallasScalar>(identity);

        // A better approach is to not create RandomizedMultChecker here but outside and pass in
        let mut rmc = RandomizedMultChecker::new(PallasScalar::rand(rng));

        let tuple = proof.verify_and_return_tuples(
            id,
            &self.account.acct.get_affine()?,
            self.account.enc.get_affine()?,
            self.asset_id,
            &self.account_state_commitment.as_commitment()?,
            self.counter,
            identity,
            dart_gens().account_comm_key(),
            tree_params.even_parameters.pc_gens(),
            tree_params.even_parameters.bp_gens(),
            &params.params,
            None,
            rng,
            Some(&mut rmc),
        )?;

        if !rmc.verify() {
            return Err(Error::RMCVerifyError);
        }
        Ok(tuple)
    }
}
