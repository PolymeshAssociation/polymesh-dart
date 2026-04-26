use bulletproofs::r1cs::ConstraintSystem;
use rand_core::{CryptoRng, RngCore};

use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_bp::TXN_CHALLENGE_LABEL;
use polymesh_dart_bp::account_registration;
use polymesh_dart_common::NullifierSkGenCounter;

use super::encode::*;
use super::split_types::*;
use super::*;
use crate::*;

type BPRegTxnProof = account_registration::RegTxnProof<PallasA>;
type BPRegTxnWithoutSkProtocol = account_registration::RegTxnWithoutSkProtocol<PallasA>;

// Account Registration — W3 split

pub struct AccountRegHostProtocol {
    protocol: BPRegTxnWithoutSkProtocol,
    prover: bulletproofs::r1cs::Prover<'static, MerlinTranscript, PallasA>,
}

impl AccountRegHostProtocol {
    pub fn init<R: RngCore + CryptoRng>(
        rng: &mut R,
        account_state: &AccountAssetState,
        rho_randomness: PallasScalar,
        counter: NullifierSkGenCounter,
        nonce: &[u8],
    ) -> Result<(Self, RegistrationDeviceRequest), Error> {
        let pk_aff = account_state.pk_aff().get_affine()?;
        let pk_enc = account_state.pk_enc().get_affine()?;
        let (account, commitment) = account_state.bp_current_state()?;
        let params = poseidon_params();
        let tree_params = AccountTreeConfig::parameters();

        let (protocol, mut prover) = BPRegTxnWithoutSkProtocol::init(
            rng,
            pk_aff,
            pk_enc,
            &account,
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
        account_state: &AccountAssetState,
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
            account_state_commitment: account_state.current_commitment()?,
            inner: WrappedCanonical::wrap(&bp_proof)?,
        })
    }
}
