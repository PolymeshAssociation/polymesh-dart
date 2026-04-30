//! Implements the host protocols and proof types for all affirmation operations. The host holds account
//! state without sk; the device holds sk and creates the auth proofs.

use bulletproofs::r1cs::{ConstraintSystem, Prover};
use codec::{Decode, DecodeWithMemTracking, Encode};
use dock_crypto_utils::randomized_mult_checker::PairRandomizedMultCheckerGuard;
use dock_crypto_utils::transcript::Transcript;
use rand_core::{CryptoRng, RngCore};
use scale_info::TypeInfo;

use ark_ff::UniformRand;
use ark_std::{string::ToString, vec};
use dock_crypto_utils::transcript::MerlinTranscript;
use polymesh_dart_bp::TXN_CHALLENGE_LABEL;
use polymesh_dart_bp::account as bp_account;
use polymesh_dart_bp::util::{
    append_auth_proof_and_get_challenge, handle_verification_tuples, make_ledger_nonce,
    serialize_challenge,
};

use super::split_types::*;
use super::*;
use crate::Error;
use crate::curve_tree::CurveTreeLookup;

macro_rules! bp_types {
    ($proto:ident, $proof:ident) => {
        type $proto = bp_account::$proto<
            ACCOUNT_TREE_L,
            PallasScalar,
            VestaScalar,
            PallasParameters,
            VestaParameters,
        >;
        type $proof = bp_account::$proof<
            ACCOUNT_TREE_L,
            PallasScalar,
            VestaScalar,
            PallasParameters,
            VestaParameters,
        >;
    };
}

bp_types!(AffirmAsSenderSplitProtocol, AffirmAsSenderSplitProof);
bp_types!(AffirmAsReceiverSplitProtocol, AffirmAsReceiverSplitProof);
bp_types!(
    IrreversibleAffirmAsSenderSplitProtocol,
    IrreversibleAffirmAsSenderSplitProof
);
bp_types!(
    IrreversibleAffirmAsReceiverSplitProtocol,
    IrreversibleAffirmAsReceiverSplitProof
);
bp_types!(ClaimReceivedSplitProtocol, ClaimReceivedSplitProof);
bp_types!(SenderReverseSplitProtocol, SenderReverseSplitProof);
bp_types!(
    SenderCounterUpdateSplitProtocol,
    SenderCounterUpdateSplitProof
);
bp_types!(
    ReceiverCounterUpdateSplitProtocol,
    ReceiverCounterUpdateSplitProof
);

// `has_balance: true` — init takes (amount, k_amount); gen_proof returns tuple.

macro_rules! with_balance {
    (
        host_protocol: $HostProto:ident,
        split_proof: $SplitProof:ident,
        bp_protocol: $BPProto:ident,
        bp_proof: $BPProof:ident,
        eph_pk_extractor: $EphPkExtractor:ident,
        eph_pk_variant: $EphPkVariant:ident,
        verifier_has_balance_decreased: $hbd:expr,
        verifier_has_counter_decreased: $hcd:expr,
        state_method: $state_method:ident,
    ) => {
        pub struct $HostProto<C: CurveTreeConfig = AccountTreeConfig> {
            protocol: $BPProto,
            even_prover: Prover<'static, MerlinTranscript, PallasA>,
            odd_prover: Prover<'static, MerlinTranscript, VestaA>,
            nullifier: PallasA,
            updated_commitment: AccountStateCommitment,
            leg_ref: LegRef,
            amount: Balance,
            root_block: BlockNumber,
            _marker: core::marker::PhantomData<C>,
        }

        impl<
            C: CurveTreeConfig<
                    F0 = <PallasParameters as CurveConfig>::ScalarField,
                    F1 = <VestaParameters as CurveConfig>::ScalarField,
                    P0 = PallasParameters,
                    P1 = VestaParameters,
                >,
        > $HostProto<C>
        {
            pub fn init<R: RngCore + CryptoRng>(
                rng: &mut R,
                account_state: &mut AccountAssetState,
                leg_ref: &LegRef,
                leg_enc: &LegEncrypted,
                amount: Balance,
                tree_lookup: &impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
            ) -> Result<(Self, AffirmationDeviceRequest), Error> {
                let state_change = account_state.$state_method(amount)?;
                let updated_commitment = state_change.commitment()?;
                let leaf_path = state_change.get_path(tree_lookup)?;

                let root_block = tree_lookup.get_block_number()?;
                let root = tree_lookup.root()?;
                let root = root.root_node()?;

                let nonce = leg_ref.context();
                let leg_enc_inner = leg_enc.decode()?;
                let (leg_enc_core, eph_pk) = leg_enc_inner.$EphPkExtractor();

                let k_amount = PallasScalar::rand(rng);
                // k_asset_id is needed only when asset-id is hidden in the leg.
                let k_asset_id = if leg_enc_core.is_asset_id_revealed() {
                    None
                } else {
                    Some(PallasScalar::rand(rng))
                };

                let (protocol, mut even_prover, odd_prover, nullifier) =
                    $BPProto::init::<_, C::DLogParams0, C::DLogParams1>(
                        rng,
                        amount,
                        (leg_enc_core.clone(), eph_pk.clone()),
                        &state_change.current_state,
                        &state_change.new_state,
                        state_change.new_commitment,
                        leaf_path,
                        &root,
                        nonce.as_bytes(),
                        C::parameters(),
                        dart_gens().account_comm_key(),
                        dart_gens().leg_asset_value_gen(),
                        k_amount,
                        k_asset_id,
                    )?;

                let challenge_h = even_prover
                    .transcript()
                    .challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);
                let challenge_h_bytes = serialize_challenge(&challenge_h)?;

                let leg_prover_config =
                    polymesh_dart_bp::account::common::leg_link::LegProverConfig {
                        encryption: leg_enc_core,
                        party_eph_pk: polymesh_dart_bp::leg::PartyEphemeralPublicKey::$EphPkVariant(
                            eph_pk.clone(),
                        ),
                        has_balance_changed: true,
                    };

                let device_request = AffirmationDeviceRequest {
                    challenge_h_bytes,
                    nonce: nonce.as_bytes().to_vec(),
                    auth_rerandomization: WrappedCanonical::wrap(&protocol.auth_rerandomization())?,
                    auth_rand_new_comm: WrappedCanonical::wrap(&protocol.auth_rand_new_comm())?,
                    rerandomized_leaf: CompressedAffine::try_from(protocol.rerandomized_leaf())?,
                    updated_account_commitment: updated_commitment.into(),
                    nullifier: CompressedAffine::try_from(nullifier)?,
                    k_amounts: vec![WrappedCanonical::wrap(&k_amount)?],
                    k_asset_ids: match k_asset_id {
                        Some(k) => vec![WrappedCanonical::wrap(&k)?],
                        None => vec![],
                    },
                    leg_prover_configs: vec![LegProverConfig::wrap(&leg_prover_config)?],
                };

                Ok((
                    Self {
                        protocol,
                        even_prover,
                        odd_prover,
                        nullifier,
                        updated_commitment,
                        leg_ref: leg_ref.clone(),
                        amount,
                        root_block,
                        _marker: core::marker::PhantomData,
                    },
                    device_request,
                ))
            }

            pub fn finish<R: RngCore + CryptoRng, T: DartLimits>(
                mut self,
                rng: &mut R,
                device_response: &AffirmationDeviceResponse,
            ) -> Result<$SplitProof<T, C>, Error> {
                let auth_proof = device_response.0.decode()?;

                let challenge_h_final = append_auth_proof_and_get_challenge(
                    &auth_proof,
                    self.even_prover.transcript(),
                )?;

                let (host_data, balance_proof) = self
                    .protocol
                    .gen_proof::<_, C::DLogParams0, C::DLogParams1>(
                        &challenge_h_final,
                        self.even_prover,
                        self.odd_prover,
                        C::parameters(),
                        rng,
                    )?;

                let bp_proof = $BPProof::assemble(host_data, balance_proof, auth_proof);

                Ok($SplitProof {
                    leg_ref: self.leg_ref,
                    root_block: self.root_block,
                    updated_account_state_commitment: self.updated_commitment,
                    nullifier: AccountStateNullifier::from_affine(self.nullifier)?,
                    amount: self.amount,
                    inner: BoundedCanonical::wrap(&bp_proof)?,
                })
            }
        }

        #[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
        #[scale_info(skip_type_params(C))]
        pub struct $SplitProof<T: DartLimits = (), C: CurveTreeConfig = AccountTreeConfig> {
            pub leg_ref: LegRef,
            pub root_block: BlockNumber,
            pub updated_account_state_commitment: AccountStateCommitment,
            pub nullifier: AccountStateNullifier,
            pub amount: Balance,
            pub(crate) inner: BoundedCanonical<
                bp_account::$BPProof<
                    ACCOUNT_TREE_L,
                    <C as CurveTreeConfig>::F0,
                    <C as CurveTreeConfig>::F1,
                    <C as CurveTreeConfig>::P0,
                    <C as CurveTreeConfig>::P1,
                >,
                T::MaxInnerProofSize,
            >,
        }

        impl<
            T: DartLimits,
            C: CurveTreeConfig<
                    F0 = <PallasParameters as CurveConfig>::ScalarField,
                    F1 = <VestaParameters as CurveConfig>::ScalarField,
                    P0 = PallasParameters,
                    P1 = VestaParameters,
                >,
        > $SplitProof<T, C>
        {
            pub fn new<R: RngCore + CryptoRng>(
                rng: &mut R,
                keys: &AccountKeys,
                leg_ref: &LegRef,
                amount: Balance,
                leg_enc: &LegEncrypted,
                account_asset: &mut AccountAssetState,
                tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
            ) -> Result<Self, Error> {
                let gens = dart_gens();
                let comm_re_rand_gen = tree_lookup.params().even_parameters.pc_gens().B_blinding;

                let (protocol, device_request) =
                    $HostProto::init(rng, account_asset, leg_ref, leg_enc, amount, &tree_lookup)?;

                let device_response = $crate::bp::auth_proofs::create_affirmation_auth_proof(
                    rng,
                    keys.acct.secret.0.0,
                    keys.enc.secret.0.0,
                    &device_request,
                    gens.account_comm_key().sk_gen(),
                    gens.enc_key_gen(),
                    comm_re_rand_gen,
                    gens.leg_asset_value_gen(),
                )?;

                protocol.finish(rng, &device_response)
            }

            pub fn verify<R: RngCore + CryptoRng>(
                &self,
                leg_enc: &LegEncrypted,
                tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
                rng: &mut R,
            ) -> Result<(), Error> {
                // Get the curve tree root.
                let root = tree_roots
                    .get_block_root(self.root_block.into())
                    .ok_or_else(|| {
                        log::error!("Invalid root for sender affirmation proof");
                        Error::CurveTreeRootNotFound
                    })?;
                let root = root.root_node()?;

                let proof = self.inner.decode()?;
                let updated_comm = self.updated_account_state_commitment.as_commitment()?;
                let nullifier = self.nullifier.get_affine()?;
                let ctx = self.leg_ref.context();
                let gens = dart_gens();
                let comm_key = gens.account_comm_key();
                let sk_gen = comm_key.sk_gen();
                let sk_enc_gen = comm_key.sk_enc_gen();
                let enc_gen = gens.leg_asset_value_gen();

                PairRandomizedMultCheckerGuard::new_using_rng(rng).with(
                    |even_rmc, odd_rmc| -> Result<(), Error> {
                        let leg_enc_inner = leg_enc.decode()?;
                        let (leg_enc_core, eph_pk) = leg_enc_inner.$EphPkExtractor();

                        let mut verifier = proof
                            .challenge_contribution::<C::DLogParams0, C::DLogParams1>(
                                updated_comm,
                                nullifier,
                                &root,
                                ctx.as_bytes(),
                                C::parameters(),
                                &comm_key,
                                enc_gen,
                                &leg_enc_core,
                                &eph_pk,
                            )?;

                        let challenge_h_v = verifier
                            .even_verifier
                            .as_mut()
                            .ok_or_else(|| {
                                Error::ProofGenerationError("Missing even_verifier".to_string())
                            })?
                            .transcript()
                            .challenge_scalar::<C::F0>(TXN_CHALLENGE_LABEL);

                        let ledger_nonce_v = make_ledger_nonce(&challenge_h_v, ctx.as_bytes())?;

                        let re_randomized_leaf_v = proof
                            .common
                            .partial
                            .re_randomized_path
                            .as_ref()
                            .ok_or_else(|| {
                                Error::ProofGenerationError(
                                    "Missing re_randomized_path".to_string(),
                                )
                            })?
                            .path
                            .get_rerandomized_leaf();

                        proof.common.auth_proof.verify(
                            vec![bp_account::LegVerifierConfig {
                                encryption: leg_enc_core,
                                party_eph_pk:
                                    polymesh_dart_bp::leg::PartyEphemeralPublicKey::$EphPkVariant(
                                        eph_pk,
                                    ),
                                has_balance_decreased: $hbd,
                                has_counter_decreased: $hcd,
                            }],
                            &re_randomized_leaf_v,
                            &updated_comm.0,
                            nullifier,
                            &ledger_nonce_v,
                            sk_gen,
                            sk_enc_gen,
                            C::parameters().even_parameters.pc_gens().B_blinding,
                            enc_gen,
                            None,
                        )?;

                        let challenge_h_final_v: C::F0 = append_auth_proof_and_get_challenge(
                            &proof.common.auth_proof,
                            verifier
                                .even_verifier
                                .as_mut()
                                .ok_or_else(|| {
                                    Error::ProofGenerationError("Missing even_verifier".to_string())
                                })?
                                .transcript(),
                        )?;

                        let (even_tuple, odd_tuple) = proof
                            .verify_and_return_tuples::<_, C::DLogParams0, C::DLogParams1>(
                                verifier,
                                &challenge_h_final_v,
                                updated_comm,
                                nullifier,
                                C::parameters(),
                                &comm_key,
                                enc_gen,
                                rng,
                                Some(even_rmc),
                            )?;

                        handle_verification_tuples(
                            even_tuple,
                            odd_tuple,
                            C::parameters(),
                            Some((even_rmc, odd_rmc)),
                        )?;
                        Ok(())
                    },
                )?;

                Ok(())
            }
        }

        impl<T: DartLimits, C: CurveTreeConfig> AccountStateUpdate for $SplitProof<T, C> {
            fn account_state_commitment(&self) -> AccountStateCommitment {
                self.updated_account_state_commitment
            }
            fn nullifier(&self) -> AccountStateNullifier {
                self.nullifier
            }
            fn root_block(&self) -> BlockNumber {
                self.root_block
            }
        }
    };
}

// `has_balance: false` — init does NOT take amount/k_amount; gen_proof returns
// a single host_data; assemble takes 2 args.

macro_rules! no_balance {
    (
        host_protocol: $HostProto:ident,
        split_proof: $SplitProof:ident,
        bp_protocol: $BPProto:ident,
        bp_proof: $BPProof:ident,
        eph_pk_extractor: $EphPkExtractor:ident,
        eph_pk_variant: $EphPkVariant:ident,
        verifier_has_counter_decreased: $hcd:expr,
        state_method: $state_method:ident,
    ) => {
        pub struct $HostProto<C: CurveTreeConfig = AccountTreeConfig> {
            protocol: $BPProto,
            even_prover: Prover<'static, MerlinTranscript, PallasA>,
            odd_prover: Prover<'static, MerlinTranscript, VestaA>,
            nullifier: PallasA,
            updated_commitment: AccountStateCommitment,
            leg_ref: LegRef,
            root_block: BlockNumber,
            _marker: core::marker::PhantomData<C>,
        }

        impl<
            C: CurveTreeConfig<
                    F0 = <PallasParameters as CurveConfig>::ScalarField,
                    F1 = <VestaParameters as CurveConfig>::ScalarField,
                    P0 = PallasParameters,
                    P1 = VestaParameters,
                >,
        > $HostProto<C>
        {
            pub fn init<R: RngCore + CryptoRng>(
                rng: &mut R,
                account_state: &mut AccountAssetState,
                leg_ref: &LegRef,
                leg_enc: &LegEncrypted,
                tree_lookup: &impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
            ) -> Result<(Self, AffirmationDeviceRequest), Error> {
                let state_change = account_state.$state_method()?;
                let updated_commitment = state_change.commitment()?;
                let leaf_path = state_change.get_path(tree_lookup)?;

                let root_block = tree_lookup.get_block_number()?;
                let root = tree_lookup.root()?;
                let root = root.root_node()?;

                let nonce = leg_ref.context();
                let leg_enc_inner = leg_enc.decode()?;
                let (leg_enc_core, eph_pk) = leg_enc_inner.$EphPkExtractor();

                // k_asset_id is needed only when asset-id is hidden in the leg.
                let k_asset_id = if leg_enc_core.is_asset_id_revealed() {
                    None
                } else {
                    Some(PallasScalar::rand(rng))
                };

                let (protocol, mut even_prover, odd_prover, nullifier) =
                    $BPProto::init::<_, C::DLogParams0, C::DLogParams1>(
                        rng,
                        (leg_enc_core.clone(), eph_pk.clone()),
                        &state_change.current_state,
                        &state_change.new_state,
                        state_change.new_commitment,
                        leaf_path,
                        &root,
                        nonce.as_bytes(),
                        C::parameters(),
                        dart_gens().account_comm_key(),
                        dart_gens().leg_asset_value_gen(),
                        k_asset_id,
                    )?;

                let challenge_h = even_prover
                    .transcript()
                    .challenge_scalar::<PallasScalar>(TXN_CHALLENGE_LABEL);
                let challenge_h_bytes = serialize_challenge(&challenge_h)?;

                let leg_prover_config =
                    polymesh_dart_bp::account::common::leg_link::LegProverConfig {
                        encryption: leg_enc_core,
                        party_eph_pk: polymesh_dart_bp::leg::PartyEphemeralPublicKey::$EphPkVariant(
                            eph_pk.clone(),
                        ),
                        has_balance_changed: false,
                    };

                let device_request = AffirmationDeviceRequest {
                    challenge_h_bytes,
                    nonce: nonce.as_bytes().to_vec(),
                    auth_rerandomization: WrappedCanonical::wrap(&protocol.auth_rerandomization())?,
                    auth_rand_new_comm: WrappedCanonical::wrap(&protocol.auth_rand_new_comm())?,
                    rerandomized_leaf: CompressedAffine::try_from(protocol.rerandomized_leaf())?,
                    updated_account_commitment: updated_commitment.into(),
                    nullifier: CompressedAffine::try_from(nullifier)?,
                    k_amounts: vec![],
                    k_asset_ids: match k_asset_id {
                        Some(k) => vec![WrappedCanonical::wrap(&k)?],
                        None => vec![],
                    },
                    leg_prover_configs: vec![LegProverConfig::wrap(&leg_prover_config)?],
                };

                Ok((
                    Self {
                        protocol,
                        even_prover,
                        odd_prover,
                        nullifier,
                        updated_commitment,
                        leg_ref: leg_ref.clone(),
                        root_block,
                        _marker: core::marker::PhantomData,
                    },
                    device_request,
                ))
            }

            pub fn finish<R: RngCore + CryptoRng, T: DartLimits>(
                mut self,
                rng: &mut R,
                device_response: &AffirmationDeviceResponse,
            ) -> Result<$SplitProof<T, C>, Error> {
                let auth_proof = device_response.0.decode()?;

                let challenge_h_final = append_auth_proof_and_get_challenge(
                    &auth_proof,
                    self.even_prover.transcript(),
                )?;

                let host_data = self
                    .protocol
                    .gen_proof::<_, C::DLogParams0, C::DLogParams1>(
                        &challenge_h_final,
                        self.even_prover,
                        self.odd_prover,
                        C::parameters(),
                        rng,
                    )?;

                let bp_proof = $BPProof::assemble(host_data, auth_proof);

                Ok($SplitProof {
                    leg_ref: self.leg_ref,
                    root_block: self.root_block,
                    updated_account_state_commitment: self.updated_commitment,
                    nullifier: AccountStateNullifier::from_affine(self.nullifier)?,
                    inner: BoundedCanonical::wrap(&bp_proof)?,
                })
            }
        }

        #[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
        #[scale_info(skip_type_params(C))]
        pub struct $SplitProof<T: DartLimits = (), C: CurveTreeConfig = AccountTreeConfig> {
            pub leg_ref: LegRef,
            pub root_block: BlockNumber,
            pub updated_account_state_commitment: AccountStateCommitment,
            pub nullifier: AccountStateNullifier,
            pub(crate) inner: BoundedCanonical<
                bp_account::$BPProof<
                    ACCOUNT_TREE_L,
                    <C as CurveTreeConfig>::F0,
                    <C as CurveTreeConfig>::F1,
                    <C as CurveTreeConfig>::P0,
                    <C as CurveTreeConfig>::P1,
                >,
                T::MaxInnerProofSize,
            >,
        }

        impl<
            T: DartLimits,
            C: CurveTreeConfig<
                    F0 = <PallasParameters as CurveConfig>::ScalarField,
                    F1 = <VestaParameters as CurveConfig>::ScalarField,
                    P0 = PallasParameters,
                    P1 = VestaParameters,
                >,
        > $SplitProof<T, C>
        {
            pub fn new<R: RngCore + CryptoRng>(
                rng: &mut R,
                keys: &AccountKeys,
                leg_ref: &LegRef,
                leg_enc: &LegEncrypted,
                account_asset: &mut AccountAssetState,
                tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
            ) -> Result<Self, Error> {
                let gens = dart_gens();
                let comm_re_rand_gen = tree_lookup.params().even_parameters.pc_gens().B_blinding;

                let (protocol, device_request) =
                    $HostProto::init(rng, account_asset, leg_ref, leg_enc, &tree_lookup)?;

                let device_response = $crate::bp::auth_proofs::create_affirmation_auth_proof(
                    rng,
                    keys.acct.secret.0.0,
                    keys.enc.secret.0.0,
                    &device_request,
                    gens.account_comm_key().sk_gen(),
                    gens.enc_key_gen(),
                    comm_re_rand_gen,
                    gens.leg_asset_value_gen(),
                )?;

                protocol.finish(rng, &device_response)
            }

            pub fn verify<R: RngCore + CryptoRng>(
                &self,
                leg_enc: &LegEncrypted,
                tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
                rng: &mut R,
            ) -> Result<(), Error> {
                // Get the curve tree root.
                let root = tree_roots
                    .get_block_root(self.root_block.into())
                    .ok_or_else(|| {
                        log::error!("Invalid root for sender affirmation proof");
                        Error::CurveTreeRootNotFound
                    })?;
                let root = root.root_node()?;

                let proof = self.inner.decode()?;
                let updated_comm = self.updated_account_state_commitment.as_commitment()?;
                let nullifier = self.nullifier.get_affine()?;
                let ctx = self.leg_ref.context();
                let gens = dart_gens();
                let comm_key = gens.account_comm_key();
                let sk_gen = comm_key.sk_gen();
                let sk_enc_gen = comm_key.sk_enc_gen();
                let enc_gen = gens.leg_asset_value_gen();

                PairRandomizedMultCheckerGuard::new_using_rng(rng).with(
                    |even_rmc, odd_rmc| -> Result<(), Error> {
                        let leg_enc_inner = leg_enc.decode()?;
                        let (leg_enc_core, eph_pk) = leg_enc_inner.$EphPkExtractor();

                        let mut verifier = proof
                            .challenge_contribution::<C::DLogParams0, C::DLogParams1>(
                                updated_comm,
                                nullifier,
                                &root,
                                ctx.as_bytes(),
                                C::parameters(),
                                &comm_key,
                                enc_gen,
                                &leg_enc_core,
                                &eph_pk,
                            )?;

                        let challenge_h_v = verifier
                            .even_verifier
                            .as_mut()
                            .ok_or_else(|| {
                                Error::ProofGenerationError("Missing even_verifier".to_string())
                            })?
                            .transcript()
                            .challenge_scalar::<C::F0>(TXN_CHALLENGE_LABEL);

                        let ledger_nonce_v = make_ledger_nonce(&challenge_h_v, ctx.as_bytes())?;

                        let re_randomized_leaf_v = proof
                            .common
                            .partial
                            .re_randomized_path
                            .as_ref()
                            .ok_or_else(|| {
                                Error::ProofGenerationError(
                                    "Missing re_randomized_path".to_string(),
                                )
                            })?
                            .path
                            .get_rerandomized_leaf();

                        proof.common.auth_proof.verify(
                            vec![bp_account::LegVerifierConfig {
                                encryption: leg_enc_core,
                                party_eph_pk:
                                    polymesh_dart_bp::leg::PartyEphemeralPublicKey::$EphPkVariant(
                                        eph_pk,
                                    ),
                                has_balance_decreased: None,
                                has_counter_decreased: $hcd,
                            }],
                            &re_randomized_leaf_v,
                            &updated_comm.0,
                            nullifier,
                            &ledger_nonce_v,
                            sk_gen,
                            sk_enc_gen,
                            C::parameters().even_parameters.pc_gens().B_blinding,
                            enc_gen,
                            None,
                        )?;

                        let challenge_h_final_v: C::F0 = append_auth_proof_and_get_challenge(
                            &proof.common.auth_proof,
                            verifier
                                .even_verifier
                                .as_mut()
                                .ok_or_else(|| {
                                    Error::ProofGenerationError("Missing even_verifier".to_string())
                                })?
                                .transcript(),
                        )?;

                        let (even_tuple, odd_tuple) = proof
                            .verify_and_return_tuples::<_, C::DLogParams0, C::DLogParams1>(
                                verifier,
                                &challenge_h_final_v,
                                updated_comm,
                                nullifier,
                                C::parameters(),
                                &comm_key,
                                enc_gen,
                                rng,
                                Some(even_rmc),
                            )?;

                        handle_verification_tuples(
                            even_tuple,
                            odd_tuple,
                            C::parameters(),
                            Some((even_rmc, odd_rmc)),
                        )?;
                        Ok(())
                    },
                )?;

                Ok(())
            }
        }

        impl<T: DartLimits, C: CurveTreeConfig> AccountStateUpdate for $SplitProof<T, C> {
            fn account_state_commitment(&self) -> AccountStateCommitment {
                self.updated_account_state_commitment
            }
            fn nullifier(&self) -> AccountStateNullifier {
                self.nullifier
            }
            fn root_block(&self) -> BlockNumber {
                self.root_block
            }
        }
    };
}

with_balance! {
    host_protocol: SenderAffirmationHostProtocol,
    split_proof: SenderAffirmationProof,
    bp_protocol: AffirmAsSenderSplitProtocol,
    bp_proof: AffirmAsSenderSplitProof,
    eph_pk_extractor: core_and_eph_keys_for_sender,
    eph_pk_variant: Sender,
    verifier_has_balance_decreased: Some(true),
    verifier_has_counter_decreased: Some(false),
    state_method: get_sender_affirm_state,
}

no_balance! {
    host_protocol: ReceiverAffirmationHostProtocol,
    split_proof: ReceiverAffirmationProof,
    bp_protocol: AffirmAsReceiverSplitProtocol,
    bp_proof: AffirmAsReceiverSplitProof,
    eph_pk_extractor: core_and_eph_keys_for_receiver,
    eph_pk_variant: Receiver,
    verifier_has_counter_decreased: Some(false),
    state_method: get_receiver_affirm_state,
}

with_balance! {
    host_protocol: ClaimReceivedHostProtocol,
    split_proof: ReceiverClaimProof,
    bp_protocol: ClaimReceivedSplitProtocol,
    bp_proof: ClaimReceivedSplitProof,
    eph_pk_extractor: core_and_eph_keys_for_receiver,
    eph_pk_variant: Receiver,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: Some(true),
    state_method: get_state_for_claiming_received,
}

with_balance! {
    host_protocol: SenderReverseHostProtocol,
    split_proof: SenderReversalProof,
    bp_protocol: SenderReverseSplitProtocol,
    bp_proof: SenderReverseSplitProof,
    eph_pk_extractor: core_and_eph_keys_for_sender,
    eph_pk_variant: Sender,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: Some(true),
    state_method: get_state_for_reversing_send,
}

no_balance! {
    host_protocol: SenderCounterUpdateHostProtocol,
    split_proof: SenderCounterUpdateProof,
    bp_protocol: SenderCounterUpdateSplitProtocol,
    bp_proof: SenderCounterUpdateSplitProof,
    eph_pk_extractor: core_and_eph_keys_for_sender,
    eph_pk_variant: Sender,
    verifier_has_counter_decreased: Some(true),
    state_method: get_state_for_decreasing_counter,
}

no_balance! {
    host_protocol: ReceiverCounterUpdateHostProtocol,
    split_proof: ReceiverCounterUpdateProof,
    bp_protocol: ReceiverCounterUpdateSplitProtocol,
    bp_proof: ReceiverCounterUpdateSplitProof,
    eph_pk_extractor: core_and_eph_keys_for_receiver,
    eph_pk_variant: Receiver,
    verifier_has_counter_decreased: Some(true),
    state_method: get_state_for_decreasing_counter,
}

with_balance! {
    host_protocol: InstantSenderAffirmationHostProtocol,
    split_proof: InstantSenderAffirmationProof,
    bp_protocol: IrreversibleAffirmAsSenderSplitProtocol,
    bp_proof: IrreversibleAffirmAsSenderSplitProof,
    eph_pk_extractor: core_and_eph_keys_for_sender,
    eph_pk_variant: Sender,
    verifier_has_balance_decreased: Some(true),
    verifier_has_counter_decreased: None,
    state_method: get_instant_sender_affirm_state,
}

with_balance! {
    host_protocol: InstantReceiverAffirmationHostProtocol,
    split_proof: InstantReceiverAffirmationProof,
    bp_protocol: IrreversibleAffirmAsReceiverSplitProtocol,
    bp_proof: IrreversibleAffirmAsReceiverSplitProof,
    eph_pk_extractor: core_and_eph_keys_for_receiver,
    eph_pk_variant: Receiver,
    verifier_has_balance_decreased: Some(false),
    verifier_has_counter_decreased: None,
    state_method: get_instant_receiver_affirm_state,
}
