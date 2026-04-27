use bulletproofs::r1cs::ConstraintSystem;
use rand_core::{CryptoRng, RngCore};

use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_bp::TXN_CHALLENGE_LABEL;
use polymesh_dart_bp::fee_account as bp_fee_account;
use polymesh_dart_bp::util::{
    BPProof, append_auth_proof_and_get_challenge, prove_with_rng, serialize_challenge,
};

use super::encode::*;
use super::split_types::*;
use super::*;
use crate::*;

type BPRegTxnProof = bp_fee_account::RegTxnProof<PallasA>;
type BPRegTxnProofWithoutSkProtocol = bp_fee_account::RegTxnProofWithoutSkProtocol<PallasA>;

type BPFeeAccountTopupTxnWithoutSkProtocol = bp_fee_account::FeeAccountTopupTxnWithoutSkProtocol<
    <PallasParameters as CurveConfig>::ScalarField,
    <VestaParameters as CurveConfig>::ScalarField,
    PallasParameters,
    VestaParameters,
    FEE_ACCOUNT_TREE_L,
>;
type BPFeeAccountTopupTxnWithoutSkProof = bp_fee_account::FeeAccountTopupTxnWithoutSkProof<
    FEE_ACCOUNT_TREE_L,
    <PallasParameters as CurveConfig>::ScalarField,
    <VestaParameters as CurveConfig>::ScalarField,
    PallasParameters,
    VestaParameters,
>;
type BPFeeAccountTopupTxnProof = bp_fee_account::FeeAccountTopupTxnProof<
    FEE_ACCOUNT_TREE_L,
    <PallasParameters as CurveConfig>::ScalarField,
    <VestaParameters as CurveConfig>::ScalarField,
    PallasParameters,
    VestaParameters,
>;

type BPFeePaymentSplitProtocol = bp_fee_account::FeePaymentSplitProtocol<
    FEE_ACCOUNT_TREE_L,
    <PallasParameters as CurveConfig>::ScalarField,
    <VestaParameters as CurveConfig>::ScalarField,
    PallasParameters,
    VestaParameters,
>;
type BPAccountCommitmentsSplitProof =
    bp_fee_account::AccountCommitmentsSplitProof<PallasParameters>;
pub(crate) type BPFeePaymentSplitProof<C> = bp_fee_account::FeePaymentSplitProof<
    FEE_ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

// Fee Registration — W3 split

pub struct FeeRegHostProtocol {
    account_state: FeeAccountState,
    protocol: BPRegTxnProofWithoutSkProtocol,
    transcript: MerlinTranscript,
}

impl FeeRegHostProtocol {
    pub fn init<R: RngCore + CryptoRng>(
        rng: &mut R,
        pk: &AccountPublicKey,
        account_state: &FeeAccountAssetState,
        nonce: &[u8],
    ) -> Result<(Self, FeeAccountDeviceRequest), Error> {
        let pk_affine = pk.get_affine()?;
        let account_state = account_state.current_state.clone();
        let (account, commitment) = account_state.bp_state()?;
        let gens = dart_gens();

        let mut transcript = MerlinTranscript::new(bp_fee_account::FEE_REG_TXN_LABEL);
        let protocol = BPRegTxnProofWithoutSkProtocol::init_with_given_transcript(
            rng,
            pk_affine,
            &account,
            commitment,
            nonce,
            gens.account_comm_key(),
            &mut transcript,
        )?;

        let challenge_h = transcript.challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);
        let challenge_h_bytes = serialize_challenge(&challenge_h)?;

        let device_request = FeeAccountDeviceRequest {
            challenge_h_bytes,
            nonce: nonce.to_vec(),
            pk: CompressedAffine::try_from(pk_affine)?,
        };

        Ok((
            Self {
                protocol,
                transcript,
                account_state,
            },
            device_request,
        ))
    }

    pub fn finish(
        mut self,
        device_response: &SingleSkDeviceResponse,
    ) -> Result<FeeAccountRegistrationProof, Error> {
        let auth_proof = device_response.0.decode()?;

        let challenge_h_final =
            append_auth_proof_and_get_challenge(&auth_proof, &mut self.transcript)?;

        let partial = self.protocol.gen_proof(&challenge_h_final);
        let bp_proof = BPRegTxnProof {
            partial,
            auth_proof,
        };

        Ok(FeeAccountRegistrationProof {
            account: self.account_state.pk,
            asset_id: self.account_state.asset_id,
            amount: self.account_state.balance,
            account_state_commitment: self.account_state.commitment()?,
            inner: WrappedCanonical::wrap(&bp_proof)?,
        })
    }
}

// Fee Topup — W3 split

pub struct FeeTopupHostProtocol<C: CurveTreeConfig = FeeAccountTreeConfig> {
    protocol: BPFeeAccountTopupTxnWithoutSkProtocol,
    even_prover: bulletproofs::r1cs::Prover<'static, MerlinTranscript, PallasA>,
    odd_prover: bulletproofs::r1cs::Prover<'static, MerlinTranscript, VestaA>,
    nullifier: PallasA,
    updated_commitment: FeeAccountStateCommitment,
    asset_id: AssetId,
    amount: Balance,
    pk: AccountPublicKey,
    _marker: core::marker::PhantomData<C>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> FeeTopupHostProtocol<C>
{
    pub fn init<R: RngCore + CryptoRng>(
        rng: &mut R,
        pk: &AccountPublicKey,
        account_state: &mut FeeAccountAssetState,
        amount: Balance,
        nonce: &[u8],
        tree_lookup: &impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<(Self, FeeAccountDeviceRequest), Error> {
        let pk_affine = pk.get_affine()?;
        let state_change = account_state.topup(amount)?;
        let updated_commitment = state_change.commitment()?;
        let leaf_path = state_change.get_path(tree_lookup)?;

        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let (protocol, mut even_prover, odd_prover, nullifier) =
            BPFeeAccountTopupTxnWithoutSkProtocol::init::<_, C::DLogParams0, C::DLogParams1>(
                rng,
                &pk_affine,
                amount,
                state_change.current_state,
                state_change.new_state,
                state_change.new_commitment,
                leaf_path,
                &root,
                nonce,
                C::parameters(),
                dart_gens().account_comm_key(),
            )?;

        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);
        let challenge_h_bytes = serialize_challenge(&challenge_h)?;

        let device_request = FeeAccountDeviceRequest {
            challenge_h_bytes,
            nonce: nonce.to_vec(),
            pk: CompressedAffine::try_from(pk_affine)?,
        };

        Ok((
            Self {
                protocol,
                even_prover,
                odd_prover,
                nullifier,
                updated_commitment,
                asset_id: account_state.asset_id(),
                amount,
                pk: *pk,
                _marker: core::marker::PhantomData,
            },
            device_request,
        ))
    }

    pub fn finish<R: RngCore + CryptoRng>(
        mut self,
        rng: &mut R,
        device_response: &SingleSkDeviceResponse,
        tree_params: &CurveTreeParameters<C>,
    ) -> Result<FeeAccountTopupProof<C>, Error> {
        let auth_proof = device_response.0.decode()?;

        let challenge_h_final =
            append_auth_proof_and_get_challenge(&auth_proof, self.even_prover.transcript())?;

        let mut partial: BPFeeAccountTopupTxnWithoutSkProof =
            self.protocol.gen_proof(&challenge_h_final)?;

        let (even_proof, odd_proof) = prove_with_rng(
            self.even_prover,
            self.odd_prover,
            &tree_params.even_parameters.bp_gens(),
            &tree_params.odd_parameters.bp_gens(),
            rng,
        )?;
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        let bp_proof = BPFeeAccountTopupTxnProof {
            auth_proof,
            partial,
        };

        Ok(FeeAccountTopupProof {
            account: self.pk,
            asset_id: self.asset_id,
            amount: self.amount,
            updated_account_state_commitment: self.updated_commitment,
            nullifier: FeeAccountStateNullifier::from_affine(self.nullifier)?,
            inner: WrappedCanonical::wrap(&bp_proof)?,
        })
    }
}

// Fee Payment — W3 split

pub struct FeePaymentHostProtocol<C: CurveTreeConfig = FeeAccountTreeConfig> {
    split_protocol: BPFeePaymentSplitProtocol,
    even_prover: bulletproofs::r1cs::Prover<'static, MerlinTranscript, PallasA>,
    odd_prover: bulletproofs::r1cs::Prover<'static, MerlinTranscript, VestaA>,
    nullifier: PallasA,
    updated_commitment: FeeAccountStateCommitment,
    asset_id: AssetId,
    amount: Balance,
    _marker: core::marker::PhantomData<C>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> FeePaymentHostProtocol<C>
{
    pub fn init<R: RngCore + CryptoRng>(
        rng: &mut R,
        account_state: &mut FeeAccountAssetState,
        amount: Balance,
        nonce: &[u8],
        tree_lookup: &impl CurveTreeLookup<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, C>,
    ) -> Result<(Self, FeePaymentDeviceRequest), Error> {
        let state_change = account_state.get_payment_state(amount)?;
        let updated_commitment = state_change.commitment()?;
        let leaf_path = state_change.get_path(tree_lookup)?;

        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let (protocol, even_prover, odd_prover, nullifier) =
            BPFeePaymentSplitProtocol::init::<_, C::DLogParams0, C::DLogParams1>(
                rng,
                amount,
                &state_change.current_state,
                &state_change.new_state,
                state_change.new_commitment,
                leaf_path,
                &root,
                nonce,
                C::parameters(),
                dart_gens().account_comm_key(),
            )?;

        let challenge_h_bytes = serialize_challenge(&protocol.challenge_h)?;
        let rerandomized_leaf = protocol.rerandomized_leaf();
        let updated_comm_affine = updated_commitment.get_affine()?;

        let device_request = FeePaymentDeviceRequest {
            challenge_h_bytes,
            nonce: nonce.to_vec(),
            auth_rerandomization: WrappedCanonical::wrap(&protocol.auth_rerandomization)?,
            auth_new_randomness: WrappedCanonical::wrap(&protocol.auth_new_randomness)?,
            rerandomized_leaf: CompressedAffine::try_from(rerandomized_leaf)?,
            updated_account_commitment: CompressedAffine::try_from(updated_comm_affine)?,
            nullifier: CompressedAffine::try_from(nullifier)?,
        };

        Ok((
            Self {
                split_protocol: protocol,
                even_prover,
                odd_prover,
                nullifier,
                updated_commitment,
                asset_id: account_state.asset_id(),
                amount,
                _marker: core::marker::PhantomData,
            },
            device_request,
        ))
    }

    pub fn finish<R: RngCore + CryptoRng>(
        mut self,
        rng: &mut R,
        device_response: &FeePaymentDeviceResponse,
        root_block: BlockNumber,
        tree_params: &CurveTreeParameters<C>,
    ) -> Result<FeeAccountPaymentProof<C>, Error> {
        let auth_proof = device_response.0.decode()?;

        let challenge_h_final =
            append_auth_proof_and_get_challenge(&auth_proof, self.even_prover.transcript())?;

        let (partial, host_commitment_proof) = self
            .split_protocol
            .gen_proof::<_, C::DLogParams0, C::DLogParams1>(
                &challenge_h_final,
                self.even_prover,
                self.odd_prover,
                tree_params,
                rng,
            )?;

        let commitment_proof = BPAccountCommitmentsSplitProof {
            auth_proof,
            host_proof: host_commitment_proof,
        };

        let bp_proof = BPFeePaymentSplitProof::<C> {
            partial,
            commitment_proof,
        };

        Ok(FeeAccountPaymentProof {
            asset_id: self.asset_id,
            amount: self.amount,
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment: self.updated_commitment,
            nullifier: FeeAccountStateNullifier::from_affine(self.nullifier)?,
            inner: WrappedCanonical::wrap(&bp_proof)?,
        })
    }
}
