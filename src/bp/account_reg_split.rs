use ark_ec::CurveGroup;
use bulletproofs::r1cs::ConstraintSystem;
use codec::{Decode, Encode};
use rand_core::{CryptoRng, RngCore};

use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_bp::TXN_CHALLENGE_LABEL;
use polymesh_dart_bp::account as bp_account;
use polymesh_dart_bp::account::state::AccountStateWithoutSk as BPAccountStateWithoutSk;
use polymesh_dart_bp::account_registration;
use polymesh_dart_common::NullifierSkGenCounter;

use super::encode::*;
use super::split_types::*;
use super::*;
use crate::*;

type BPRegTxnProof = account_registration::RegTxnProof<PallasA>;
type BPRegTxnWithoutSkProtocol = account_registration::RegTxnWithoutSkProtocol<PallasA>;

#[derive(Clone, Debug, Encode, Decode)]
pub struct AccountAssetStateWithPk {
    pub current_state: AccountState,
    pub pending_state: Option<AccountState>,
    /// Sum of affirmation and encryption public keys.
    pub pk_contribution: CompressedAffine,
}

impl AccountAssetStateWithPk {
    pub fn from_asset_state(
        asset_state: &AccountAssetState,
        pk: &AccountPublicKeys,
    ) -> Result<Self, Error> {
        let pk_aff = pk.acct.get_affine()?;
        let pk_enc_aff = pk.enc.get_affine()?;
        let pk_contribution = (pk_aff.into_group() + pk_enc_aff).into_affine();
        Ok(Self {
            current_state: asset_state.current_state.clone(),
            pending_state: asset_state.pending_state.clone(),
            pk_contribution: CompressedAffine::try_from(pk_contribution)?,
        })
    }

    pub fn asset_id(&self) -> AssetId {
        self.current_state.asset_id
    }

    fn pk_contribution_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.pk_contribution)?)
    }

    pub fn current_full_commitment(&self) -> Result<AccountStateCommitment, Error> {
        let without_sk_comm = self
            .bp_current_state_without_sk()?
            .commit(dart_gens().account_comm_key())?;
        let pk = self.pk_contribution_affine()?;
        let full = (without_sk_comm.0.into_group() + pk).into_affine();
        AccountStateCommitment::from_affine(full)
    }

    pub(crate) fn bp_current_state_without_sk(
        &self,
    ) -> Result<BPAccountStateWithoutSk<PallasA>, Error> {
        Ok(BPAccountStateWithoutSk {
            id: self.current_state.identity.decode()?,
            balance: self.current_state.balance,
            counter: self.current_state.counter,
            asset_id: self.current_state.asset_id,
            rho: self.current_state.rho.decode()?,
            current_rho: self.current_state.current_rho.decode()?,
            randomness: self.current_state.randomness.decode()?,
            current_randomness: self.current_state.current_randomness.decode()?,
        })
    }

    pub(crate) fn full_commitment_from_without_sk(
        &self,
        without_sk_comm: PallasA,
    ) -> Result<BPAccountStateCommitment, Error> {
        let pk = self.pk_contribution_affine()?;
        Ok(bp_account::AccountStateCommitment(
            (without_sk_comm.into_group() + pk).into_affine(),
        ))
    }
}

impl TryFrom<BPAccountStateWithoutSk<PallasA>> for AccountState {
    type Error = Error;

    fn try_from(state: BPAccountStateWithoutSk<PallasA>) -> Result<Self, Self::Error> {
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

// Account Registration — W3 split

pub struct AccountRegHostProtocol {
    protocol: BPRegTxnWithoutSkProtocol,
    prover: bulletproofs::r1cs::Prover<'static, MerlinTranscript, PallasA>,
}

impl AccountRegHostProtocol {
    pub fn init<R: RngCore + CryptoRng>(
        rng: &mut R,
        pk: &AccountPublicKeys,
        account_state: &AccountAssetStateWithPk,
        rho_randomness: PallasScalar,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
    ) -> Result<(Self, RegistrationDeviceRequest), Error> {
        let pk_aff = pk.acct.get_affine()?;
        let pk_enc = pk.enc.get_affine()?;
        let without_sk = account_state.bp_current_state_without_sk()?;
        let commitment = account_state.current_full_commitment()?.as_commitment()?;
        let params = poseidon_params();
        let tree_params = AccountTreeConfig::parameters();

        let (protocol, mut prover) = BPRegTxnWithoutSkProtocol::init(
            rng,
            pk_aff,
            pk_enc,
            &without_sk,
            commitment,
            rho_randomness,
            counter,
            nonce,
            &dart_gens().account_comm_key(),
            tree_params.even_parameters.pc_gens(),
            tree_params.even_parameters.bp_gens(),
            &params.params,
            None,
        )?;

        let challenge_h = prover
            .transcript()
            .challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);
        let challenge_h_bytes = serialize_challenge(&challenge_h)?;

        let device_request = RegistrationDeviceRequest {
            challenge_h_bytes,
            nonce: nonce.to_vec(),
            pk_aff: CompressedAffine::try_from(pk_aff)?,
            pk_enc: CompressedAffine::try_from(pk_enc)?,
        };

        Ok((Self { protocol, prover }, device_request))
    }

    pub fn finish<R: RngCore + CryptoRng>(
        mut self,
        rng: &mut R,
        device_response: &TwoSksDeviceResponse,
        pk: &AccountPublicKeys,
        account_state: &AccountAssetStateWithPk,
        counter: NullifierSkGenCounter,
    ) -> Result<AccountAssetRegistrationProof, Error> {
        let auth_proof = device_response.0.decode()?;

        let challenge_h_final =
            append_auth_proof_and_get_challenge(&auth_proof, self.prover.transcript())?;

        let mut partial = self.protocol.gen_proof(&challenge_h_final)?;

        let tree_params = AccountTreeConfig::parameters();
        let r1cs_proof = self
            .prover
            .prove_with_rng(tree_params.even_parameters.bp_gens(), rng)?;
        partial.proof = Some(r1cs_proof);

        let bp_proof = BPRegTxnProof {
            partial,
            auth_proof,
        };

        Ok(AccountAssetRegistrationProof {
            account: *pk,
            asset_id: account_state.asset_id(),
            counter,
            account_state_commitment: account_state.current_full_commitment()?,
            inner: WrappedCanonical::wrap(&bp_proof)?,
        })
    }
}
