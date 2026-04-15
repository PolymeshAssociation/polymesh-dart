use bulletproofs::r1cs::ConstraintSystem;
use rand_core::{CryptoRng, RngCore};

use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_bp::TXN_CHALLENGE_LABEL;
use polymesh_dart_bp::account::mint::{MintTxnProof, MintTxnProofPartialProtocol};
use polymesh_dart_bp::util::{BPProof, prove_with_rng};

use super::account_reg_split::AccountAssetStateWithPk;
use super::encode::*;
use super::split_types::*;
use super::*;
use crate::*;

type BPMintTxnProof = MintTxnProof<
    ACCOUNT_TREE_L,
    <PallasParameters as CurveConfig>::ScalarField,
    <VestaParameters as CurveConfig>::ScalarField,
    PallasParameters,
    VestaParameters,
>;

type BPMintTxnProofPartialProtocol = MintTxnProofPartialProtocol<
    <PallasParameters as CurveConfig>::ScalarField,
    <VestaParameters as CurveConfig>::ScalarField,
    PallasParameters,
    VestaParameters,
    ACCOUNT_TREE_L,
>;

// AccountAssetStateChangeWithoutSk

#[derive(Clone, Debug)]
pub struct AccountAssetStateChangeWithoutSk {
    pub current_state: BPAccountStateWithoutSk,
    pub current_commitment: BPAccountStateCommitment,
    pub new_state: BPAccountStateWithoutSk,
    pub new_commitment: BPAccountStateCommitment,
}

impl AccountAssetStateChangeWithoutSk {
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

impl AccountAssetStateWithPk {
    /// Compute the current and updated state commitments using a closure, exactly
    /// like `AccountAssetState::state_change` but without needing sk.
    fn state_change(
        &mut self,
        update: impl FnOnce(&BPAccountStateWithoutSk) -> Result<BPAccountStateWithoutSk, Error>,
    ) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        let current = self.bp_current_state_without_sk()?;
        let current_without_sk_comm = current.commit(dart_gens().account_comm_key())?;
        let current_commitment = self.full_commitment_from_without_sk(current_without_sk_comm.0)?;

        let new = update(&current)?;
        let new_without_sk_comm = new.commit(dart_gens().account_comm_key())?;
        let new_commitment = self.full_commitment_from_without_sk(new_without_sk_comm.0)?;

        self.pending_state = Some(new.clone().try_into()?);

        Ok(AccountAssetStateChangeWithoutSk {
            current_state: current,
            current_commitment,
            new_state: new,
            new_commitment,
        })
    }

    pub fn mint(&mut self, amount: Balance) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        self.state_change(|state| Ok(state.get_state_for_mint(amount)?))
    }

    pub fn get_sender_affirm_state(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        self.state_change(|state| Ok(state.get_state_for_send(amount)?))
    }

    pub fn get_receiver_affirm_state(&mut self) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        self.state_change(|state| Ok(state.get_state_for_receive()))
    }

    pub fn get_instant_sender_affirm_state(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        self.state_change(|state| Ok(state.get_state_for_irreversible_send(amount)?))
    }

    pub fn get_instant_receiver_affirm_state(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        self.state_change(|state| Ok(state.get_state_for_irreversible_receive(amount)?))
    }

    pub fn get_state_for_claiming_received(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        self.state_change(|state| Ok(state.get_state_for_claiming_received(amount)?))
    }

    pub fn get_state_for_reversing_send(
        &mut self,
        amount: Balance,
    ) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        self.state_change(|state| Ok(state.get_state_for_reversing_send(amount)?))
    }

    pub fn get_state_for_decreasing_counter(
        &mut self,
        amount_to_decrease: Option<Balance>,
    ) -> Result<AccountAssetStateChangeWithoutSk, Error> {
        self.state_change(|state| Ok(state.get_state_for_decreasing_counter(amount_to_decrease)?))
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

// Mint — W3 split

pub struct MintHostProtocol<C: CurveTreeConfig = AccountTreeConfig> {
    protocol: BPMintTxnProofPartialProtocol,
    even_prover: bulletproofs::r1cs::Prover<'static, MerlinTranscript, PallasA>,
    odd_prover: bulletproofs::r1cs::Prover<'static, MerlinTranscript, VestaA>,
    nullifier: PallasA,
    updated_commitment: AccountStateCommitment,
    pk: AccountPublicKey,
    pk_enc: EncryptionPublicKey,
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
> MintHostProtocol<C>
{
    pub fn init<R: RngCore + CryptoRng>(
        rng: &mut R,
        pk: &AccountPublicKeys,
        account_state: &mut AccountAssetStateWithPk,
        amount: Balance,
        nonce: &[u8],
        tree_lookup: &impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<(Self, RegistrationDeviceRequest), Error> {
        let pk_aff = pk.acct.get_affine()?;
        let pk_enc = pk.enc.get_affine()?;

        let state_change = account_state.mint(amount)?;
        let updated_commitment = state_change.commitment()?;
        let leaf_path = state_change.get_path(tree_lookup)?;

        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let (protocol, mut even_prover, odd_prover, nullifier) =
            BPMintTxnProofPartialProtocol::init::<_, C::DLogParams0, C::DLogParams1>(
                rng,
                pk_aff,
                pk_enc,
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

        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);
        let challenge_h_bytes = serialize_challenge(&challenge_h)?;

        let device_request = RegistrationDeviceRequest {
            challenge_h_bytes,
            nonce: nonce.to_vec(),
            pk_aff: CompressedAffine::try_from(pk_aff)?,
            pk_enc: CompressedAffine::try_from(pk_enc)?,
        };

        Ok((
            Self {
                protocol,
                even_prover,
                odd_prover,
                nullifier,
                updated_commitment,
                pk: pk.acct,
                pk_enc: pk.enc,
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
        device_response: &TwoSksDeviceResponse,
        root_block: u64,
        tree_params: &CurveTreeParameters<C>,
    ) -> Result<AssetMintingProof<C>, Error> {
        let auth_proof = device_response.0.decode()?;

        let challenge_h_final =
            append_auth_proof_and_get_challenge(&auth_proof, self.even_prover.transcript())?;

        let mut partial = self.protocol.gen_proof(&challenge_h_final)?;
        let auth_proof_final = auth_proof;

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

        let bp_proof = BPMintTxnProof {
            partial,
            auth_proof: auth_proof_final,
        };

        Ok(AssetMintingProof {
            pk: self.pk,
            pk_enc: self.pk_enc,
            asset_id: self.asset_id,
            amount: self.amount,
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment: self.updated_commitment,
            nullifier: AccountStateNullifier::from_affine(self.nullifier)?,
            inner: WrappedCanonical::wrap(&bp_proof)?,
        })
    }
}
