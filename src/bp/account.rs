#[cfg(feature = "parallel")]
use rayon::prelude::*;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, DecodeWithMemTracking, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use ark_ec::CurveConfig;
use ark_std::UniformRand;
use ark_std::vec::Vec;

use bounded_collections::BoundedVec;
use bulletproofs::r1cs::{ConstraintSystem, VerificationTuple};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::Transcript;
use rand_core::{CryptoRng, RngCore};

use polymesh_dart_bp::account::state::AccountCommitmentKeyTrait;
use polymesh_dart_bp::{
    TXN_CHALLENGE_LABEL, account as bp_account, account_registration, leg as bp_leg,
};
use polymesh_dart_common::NullifierSkGenCounter;

use super::*;
use crate::*;

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
    pub keys: AccountPublicKeys,
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
    pub fn bp_state(&self) -> Result<(BPAccountState, BPAccountStateCommitment), Error> {
        let state = BPAccountState {
            pk_aff: self.keys.acct.get_affine()?,
            pk_enc: self.keys.enc.get_affine()?,
            id: self.identity.decode()?,
            balance: self.balance,
            counter: self.counter,
            asset_id: self.asset_id,
            rho: self.rho.decode()?,
            current_rho: self.current_rho.decode()?,
            randomness: self.randomness.decode()?,
            current_randomness: self.current_randomness.decode()?,
        };
        let commitment = state.commit(dart_gens().account_comm_key())?;
        Ok((state, commitment))
    }

    pub fn commitment(&self) -> Result<AccountStateCommitment, Error> {
        let (_state, commitment) = self.bp_state()?;
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
            keys: AccountPublicKeys {
                acct: AccountPublicKey::from_affine(state.pk_aff)?,
                enc: EncryptionPublicKey::from_affine(state.pk_enc)?,
            },
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
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
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
    ) -> Result<(Self, PallasScalar), Error> {
        let (current_state, rho_randomness) = keys.account_state(asset_id, counter, identity)?;
        Ok((
            Self {
                current_state,
                pending_state: None,
            },
            rho_randomness,
        ))
    }

    pub fn current_commitment(&self) -> Result<AccountStateCommitment, Error> {
        self.current_state.commitment()
    }

    pub fn asset_id(&self) -> AssetId {
        self.current_state.asset_id
    }

    pub fn pk_aff(&self) -> AccountPublicKey {
        self.current_state.keys.acct
    }

    pub fn pk_enc(&self) -> EncryptionPublicKey {
        self.current_state.keys.enc
    }

    pub fn bp_current_state(&self) -> Result<(BPAccountState, BPAccountStateCommitment), Error> {
        self.current_state.bp_state()
    }

    fn state_change(
        &mut self,
        update: impl FnOnce(&BPAccountState) -> Result<BPAccountState, Error>,
    ) -> Result<AccountAssetStateChange, Error> {
        let (current_state, current_commitment) = self.bp_current_state()?;

        // Update the state.
        let new_state = update(&current_state)?;
        let new_commitment = new_state.commit(dart_gens().account_comm_key())?;

        // Set the pending state.
        self.pending_state = Some(new_state.clone().try_into()?);

        Ok(AccountAssetStateChange {
            current_state,
            current_commitment,
            new_state,
            new_commitment,
        })
    }

    pub fn mint(&mut self, amount: Balance) -> Result<AccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_mint(amount)?))
    }

    pub fn get_sender_affirm_state(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_send(amount)?))
    }

    pub fn get_receiver_affirm_state(&mut self) -> Result<AccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_receive()))
    }

    pub fn get_instant_sender_affirm_state(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_irreversible_send(amount)?))
    }

    pub fn get_instant_receiver_affirm_state(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_irreversible_receive(amount)?))
    }

    pub fn get_state_for_claiming_received(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_claiming_received(amount)?))
    }

    pub fn get_state_for_reversing_send(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_reversing_send(amount)?))
    }

    pub fn get_state_for_decreasing_counter(&mut self) -> Result<AccountAssetStateChange, Error> {
        self.state_change(|state| Ok(state.get_state_for_decreasing_counter(None)?))
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
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
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

    #[cfg(feature = "parallel")]
    pub fn verify_split<R: RngCore + CryptoRng + Sync + Send + Clone>(
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
                |rng, proof| proof.verify_split(identity, tree_params, rng),
            )
            .collect::<Result<(), Error>>()?;
        Ok(())
    }

    #[cfg(not(feature = "parallel"))]
    pub fn verify_split<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        for proof in &self.proofs {
            proof.verify_split(identity, tree_params, rng)?;
        }
        Ok(())
    }
}

/// Account asset registration proof.  Report section 5.1.3 "Account Registration".
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
pub struct AccountAssetRegistrationProof {
    pub account: AccountPublicKeys,
    pub asset_id: AssetId,
    pub counter: NullifierSkGenCounter,
    pub account_state_commitment: AccountStateCommitment,

    pub(crate) inner: WrappedCanonical<account_registration::RegTxnProof<PallasA>>,
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
        let (account_state, rho_randomness) = keys.init_asset_state(asset_id, counter, identity)?;
        let (bp_state, commitment) = account_state.bp_current_state()?;
        let params = poseidon_params();
        let gens = dart_gens();
        let proof = account_registration::RegTxnProof::new(
            rng,
            keys.acct.secret.0.0,
            keys.enc.secret.0.0,
            &bp_state,
            commitment,
            rho_randomness,
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

        let result = proof.verify(
            rng,
            id,
            self.account.acct.get_affine()?,
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
        );

        process_result_and_rmc(result, rmc)
    }

    pub fn verify_split<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let proof = self.inner.decode()?;
        let params = poseidon_params();
        let id = hash_identity::<PallasScalar>(identity);
        let pk_aff = self.account.acct.get_affine()?;
        let pk_enc = self.account.enc.get_affine()?;
        let commitment = self.account_state_commitment.as_commitment()?;
        let gens = dart_gens();
        let comm_key = gens.account_comm_key();
        let sk_gen = comm_key.sk_gen();
        let sk_enc_gen = comm_key.sk_enc_gen();
        let pc_gens = tree_params.even_parameters.pc_gens();
        let bp_gens = tree_params.even_parameters.bp_gens();

        let mut rmc = RandomizedMultChecker::new(PallasScalar::rand(rng));
        let result = (|| -> Result<(), Error> {
            let mut verifier = proof.partial.challenge_contribution(
                id,
                pk_aff,
                pk_enc,
                self.asset_id,
                &commitment,
                self.counter,
                identity,
                &comm_key,
                &params.params,
                None,
            )?;

            let challenge_h_v = verifier
                .transcript()
                .challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);

            let mut challenge_h_v_bytes = Vec::new();
            challenge_h_v.serialize_compressed(&mut challenge_h_v_bytes)?;
            let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
                .iter()
                .chain(identity.iter())
                .copied()
                .collect();

            proof
                .auth_proof
                .verify(pk_aff, pk_enc, &ledger_nonce_v, &sk_gen, &sk_enc_gen, None)?;

            let mut auth_proof_bytes = Vec::new();
            proof
                .auth_proof
                .serialize_compressed(&mut auth_proof_bytes)?;
            verifier
                .transcript()
                .append_message(AUTH_PROOF_LABEL, &auth_proof_bytes);
            let challenge_h_final_v = verifier
                .transcript()
                .challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);

            proof.partial.verify_with_challenge(
                &challenge_h_final_v,
                &comm_key,
                pk_aff,
                pk_enc,
                id,
                self.asset_id,
                &commitment,
                pc_gens,
                bp_gens,
                None,
                Some(&mut rmc),
            )?;

            let bp_proof = proof.partial.proof.as_ref().ok_or(Error::RMCVerifyError)?;
            let tuple = verifier.verification_scalars_and_points_with_rng(bp_proof, rng)?;
            bulletproofs::r1cs::verify_given_verification_tuple(tuple, pc_gens, bp_gens)?;
            Ok(())
        })();

        process_result_and_rmc(result, rmc)
    }

    /// Verify this registration proof inside a batch of proofs.
    pub(crate) fn batched_verify<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_params: &CurveTreeParameters<AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<VerificationTuple<PallasA>, Error> {
        let proof = self.inner.decode()?;
        let params = poseidon_params();
        let id = hash_identity::<PallasScalar>(identity);

        // A better approach is to not create RandomizedMultChecker here but outside and pass in
        let mut rmc = RandomizedMultChecker::new(PallasScalar::rand(rng));

        let result = proof.verify_and_return_tuples(
            id,
            self.account.acct.get_affine()?,
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
        );

        process_result_and_rmc(result, rmc)
    }
}
