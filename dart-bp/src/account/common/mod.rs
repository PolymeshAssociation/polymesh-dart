pub mod balance;
pub mod leg_link;
pub mod verifier;

use crate::account::state::NUM_GENERATORS;
use crate::account::{AccountCommitmentKeyTrait, AccountState, AccountStateCommitment};
use crate::auth_proofs::account::AuthProofAffirmation;
use crate::dst;
use crate::leg::{LegEncryptionCore, PartyEphemeralPublicKey};
use crate::util::{
    BPProof, generate_sigma_responses_for_common_state_change,
    generate_sigma_t_values_for_common_state_change, prove_with_rng,
};
use crate::util::{
    create_account_commitment_t_values, create_bp_and_null_t_values,
    generate_account_commitment_responses, generate_null_bp_responses,
};
use crate::{
    Error, LEG_ENC_LABEL, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL, TXN_EVEN_LABEL,
    TXN_ODD_LABEL, UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript, error::Result,
};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;

use ark_serialize::{
    CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::io::{Read, Write};
use ark_std::{UniformRand, format, string::ToString, vec, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use dock_crypto_utils::transcript::MerlinTranscript;
use dock_crypto_utils::transcript::Transcript;
use leg_link::{LegAccountLink, LegAccountLinkProtocol, LegProverConfig};
use polymesh_dart_common::{AssetId, Balance};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialPokPedersenCommitment,
    PartialSchnorrResponse,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::{Zeroize, ZeroizeOnDrop};

// Aiming for 3 possible workflows:
// W1 - Solo. Single prover has all witnesses including secret key(s)
//
// W2 - Parallel. Two provers, device (ledger) has the secret key(s) and host (computer) has everything else and they run in parallel, independently.
//
// W3 - Sequential. Two provers, device (ledger) has the secret key(s) and host (computer) has everything else and they run sequentially.
//    1. host does the pre-challenge phase (commits to randomness, writes all instance in transcript), generates challenge and sends it to device.
//    2. device creates the full proof using the challenge as its instance data
//    3. device sends the proof to host.
//    4. Host does its post challenge phase where it generates the proof. Host might decide to generate new challenge based on device's proof.
//
// Following allows all 3 workflows by orchestrating functions in the appropriate order and allowing args (gen_proof takes challenge where host could give any challenge of its choice)
//
// I don't see any technical reason to have W3 but still allowing it.

/// Proof for everything except account commitments and leg links
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommonStateChangeProofPartial<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    const L: usize,
> {
    /// When this is None, external [`R1CSProof`] will be used and [`CommonStateChangeProof`] only
    /// contains proof for the sigma protocols and enforces the Bulletproof constraints.
    pub r1cs_proof: Option<BPProof<G0, G1>>,
    /// When using batched proving (multi-asset state transitions),
    /// this will be None as the path is computed externally.
    pub re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G0, G1>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PartialPokDiscreteLog<Affine<G0>>,
    /// Commitment to initial rho, old and current rho, old and current randomness
    pub comm_bp_randomness_relations: Affine<G0>,
    /// Response for proving knowledge of rho and commitment randomness (step 3 of Schnorr).
    /// Carries the commitment to randomness `t` from step 1.
    pub resp_bp_randomness_relations: PartialSchnorrResponse<Affine<G0>>,
}

/// Proof for variables that change during each account state transition
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommonStateChangeProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub partial: CommonStateChangeProofPartial<F0, F1, G0, G1, { L }>,
    /// Response for proving knowledge of re-randomized account commitment (leaf) using Schnorr
    /// protocol (step 3 of Schnorr). Carries the commitment to randomness `t` from step 1.
    pub resp_acc_old: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3
    /// of Schnorr). Carries the commitment to randomness `t` from step 1.
    pub resp_acc_new: PartialSchnorrResponse<Affine<G0>>,
    pub resp_leg_link: Vec<LegAccountLink<G0>>,
}

#[derive(Zeroize, ZeroizeOnDrop)]
pub struct CommonStateChangeProver<
    'a,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    #[zeroize(skip)]
    pub even_prover: Option<Prover<'a, MerlinTranscript, Affine<G0>>>,
    #[zeroize(skip)]
    pub odd_prover: Option<Prover<'a, MerlinTranscript, Affine<G1>>>,
    #[zeroize(skip)]
    pub re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G0, G1>>,
    pub leaf_rerandomization: F0,
    #[zeroize(skip)]
    pub nullifier: Affine<G0>,
    pub t_acc_old: SchnorrCommitment<Affine<G0>>,
    pub t_acc_new: SchnorrCommitment<Affine<G0>>,
    pub t_null: PokDiscreteLogProtocol<Affine<G0>>,
    pub t_leg_link: Vec<LegAccountLinkProtocol<G0>>,
    #[zeroize(skip)]
    pub comm_bp_randomness_relations: Affine<G0>,
    pub t_bp_randomness_relations: SchnorrCommitment<Affine<G0>>,
    pub comm_bp_blinding: F0,
    pub sk_enc_inv_blinding: F0,
    pub old_balance_blinding: F0,
    pub new_balance_blinding: F0,
    /// Amount blindings of the balance-changed legs, shared with `BalanceChangeProver` so the
    /// balance BP and the leg-link `ct_amount` use the same blinding for `v`
    pub balance_amount_blindings: Vec<F0>,
    pub is_asset_id_revealed: bool,
}

impl<
    'a,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonStateChangeProver<'a, L, F0, F1, G0, G1>
{
    pub fn init<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<Affine<G0>>>,
        sk_enc: G0::ScalarField,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        account_tree_root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let transcript_even = MerlinTranscript::new(TXN_EVEN_LABEL);
        let transcript_odd = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.sl_params.pc_gens(),
            transcript_even,
        );
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.sl_params.pc_gens(),
            transcript_odd,
        );

        let mut prover = Self::init_with_given_prover::<_, Parameters0, Parameters1>(
            rng,
            legs_with_conf,
            sk_enc,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            account_tree_root,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )?;
        prover.even_prover = Some(even_prover);
        prover.odd_prover = Some(odd_prover);
        Ok(prover)
    }

    pub fn init_with_given_prover<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<Affine<G0>>>,
        sk_enc: G0::ScalarField,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        account_tree_root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<Self> {
        let (re_randomized_path, leaf_rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget_new::<_, Parameters0, Parameters1>(
                even_prover,
                odd_prover,
                account_tree_params,
                rng,
                None,
            )?;

        add_to_transcript!(
            even_prover.transcript(),
            ROOT_LABEL,
            account_tree_root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
        );

        Self::init_with_given_prover_inner(
            rng,
            legs_with_conf,
            sk_enc,
            account,
            updated_account,
            updated_account_commitment,
            leaf_rerandomization,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            even_prover,
            Some(re_randomized_path),
        )
    }

    /// Creates a new prover when the leaf has already been re-randomized externally.
    /// This is useful for batched proving when proving multiple paths at once.
    /// `rerandomized_leaf_and_blinding` - Tuple of (rerandomized_leaf, re_randomization_of_leaf)
    pub fn init_with_given_prover_with_rerandomized_leaf<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<Affine<G0>>>,
        sk_enc: G0::ScalarField,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_rerandomization: F0,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
    ) -> Result<Self> {
        // Note: No re_randomized_path to add to transcript since it was computed externally (batch proof)
        // The caller is responsible for adding it to the transcript
        Self::init_with_given_prover_inner(
            rng,
            legs_with_conf,
            sk_enc,
            account,
            updated_account,
            updated_account_commitment,
            leaf_rerandomization,
            nonce,
            account_tree_params,
            account_comm_key,
            enc_gen,
            even_prover,
            None, // No path since it was computed externally
        )
    }

    /// Initialize various sigma protocols and enforce BP constraints for various
    fn init_with_given_prover_inner<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<Affine<G0>>>,
        sk_enc: G0::ScalarField,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_rerandomization: F0,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G0, G1>>,
    ) -> Result<Self> {
        let _enc_key_gen = account_comm_key.sk_enc_gen();
        // has_balance_changed denotes whether the balance changed for any leg. This flag is known to verifier as well
        let has_balance_changed = legs_with_conf.iter().any(|l| l.has_balance_changed);
        ensure_same_accounts(account, updated_account, has_balance_changed)?;

        add_to_transcript!(
            even_prover.transcript(),
            NONCE_LABEL,
            nonce,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let asset_id = account.asset_id();

        // For legs that have asset-id ciphertext, prove that asset-id ciphertext is correctly formed when is_asset_id_revealed = true
        let (is_asset_id_revealed, legs, amounts, legs_balance_changed) =
            legs_for_proof(legs_with_conf, asset_id)?;

        for (leg_core, eph_pk) in &legs {
            add_to_transcript!(
                even_prover.transcript(),
                LEG_ENC_LABEL,
                leg_core,
                LEG_ENC_LABEL,
                eph_pk
            );
        }

        let mut id_blinding = F0::rand(rng);
        let mut old_counter_blinding = F0::rand(rng);
        let mut asset_id_blinding = (!is_asset_id_revealed).then(|| F0::rand(rng));
        let mut initial_rho_blinding = F0::rand(rng);
        let mut old_rho_blinding = F0::rand(rng);
        let mut new_rho_blinding = F0::rand(rng);
        let mut old_randomness_blinding = F0::rand(rng);
        let mut new_randomness_blinding = F0::rand(rng);
        let mut initial_randomness_blinding = F0::rand(rng);

        let mut sk_blinding = F0::rand(rng);
        let mut sk_enc_blinding = F0::rand(rng);
        let sk_enc_inv_blinding = F0::rand(rng);

        let (old_balance_blinding, new_balance_blinding) = if has_balance_changed {
            (F0::rand(rng), F0::rand(rng))
        } else {
            let b = F0::rand(rng);
            (b, b)
        };

        // One amount blinding per ct_amount leg (revealed or balance-changed), owned by the leg-link.
        // The balance-changed subset is shared with the balance BP in the same commit order.
        let num_ct_amounts = (0..legs.len())
            .filter(|&i| legs[i].0.is_asset_id_revealed() || legs_balance_changed[i])
            .count();
        let amount_blindings: Vec<F0> = (0..num_ct_amounts).map(|_| F0::rand(rng)).collect();
        let mut balance_amount_blindings = Vec::with_capacity(amount_blindings.len());
        let mut amount_idx = 0;
        for i in 0..legs.len() {
            if legs[i].0.is_asset_id_revealed() || legs_balance_changed[i] {
                if legs_balance_changed[i] {
                    balance_amount_blindings.push(amount_blindings[amount_idx]);
                }
                amount_idx += 1;
            }
        }

        let (
            nullifier,
            comm_bp_randomness_relations,
            comm_bp_blinding,
            t_acc_old,
            t_acc_new,
            t_null,
            t_leg_link,
            t_bp_randomness_relations,
        ) = generate_sigma_t_values_for_common_state_change(
            rng,
            legs,
            amounts,
            legs_balance_changed,
            sk_enc,
            account,
            updated_account,
            id_blinding,
            sk_blinding,
            old_balance_blinding,
            new_balance_blinding,
            old_counter_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            initial_randomness_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
            asset_id_blinding,
            sk_enc_blinding,
            sk_enc_inv_blinding,
            amount_blindings,
            even_prover,
            &account_comm_key,
            account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
            enc_gen,
        )?;

        Zeroize::zeroize(&mut id_blinding);
        Zeroize::zeroize(&mut sk_blinding);
        // sk_enc_inv_blinding is needed for later and must NOT be zeroized here
        Zeroize::zeroize(&mut sk_enc_blinding);
        Zeroize::zeroize(&mut old_counter_blinding);
        Zeroize::zeroize(&mut asset_id_blinding);
        Zeroize::zeroize(&mut initial_rho_blinding);
        Zeroize::zeroize(&mut old_rho_blinding);
        Zeroize::zeroize(&mut new_rho_blinding);
        Zeroize::zeroize(&mut old_randomness_blinding);
        Zeroize::zeroize(&mut new_randomness_blinding);
        Zeroize::zeroize(&mut initial_randomness_blinding);

        Ok(Self {
            even_prover: None,
            odd_prover: None,
            re_randomized_path,
            leaf_rerandomization,
            nullifier,
            t_acc_old,
            t_acc_new,
            t_null,
            t_leg_link,
            comm_bp_randomness_relations,
            t_bp_randomness_relations,
            comm_bp_blinding,
            sk_enc_inv_blinding,
            old_balance_blinding,
            new_balance_blinding,
            balance_amount_blindings,
            is_asset_id_revealed,
        })
    }

    pub fn gen_proof<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        mut self,
        rng: &mut R,
        sk_aff: G0::ScalarField,
        sk_enc: G0::ScalarField,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        challenge: &F0,
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters0>,
    ) -> Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
        let even_prover = self.even_prover.take().ok_or_else(|| {
            Error::ProofGenerationError(
                "even_prover is missing or already consumed; use init() or avoid reusing the prover"
                    .to_string(),
            )
        })?;
        let odd_prover = self.odd_prover.take().ok_or_else(|| {
            Error::ProofGenerationError(
                "odd_prover is missing or already consumed; use init() or avoid reusing the prover"
                    .to_string(),
            )
        })?;

        let mut proof =
            self.generate_sigma_responses(sk_aff, sk_enc, account, updated_account, challenge)?;

        let bp_gens = account_tree_params.bp_gens();
        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, bp_gens.0, bp_gens.1, rng)?;

        proof.partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });
        Ok(proof)
    }

    pub fn generate_sigma_responses(
        mut self,
        sk_aff: G0::ScalarField,
        sk_enc: G0::ScalarField,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        challenge: &F0,
    ) -> Result<CommonStateChangeProof<L, F0, F1, G0, G1>> {
        let (resp_acc_old, resp_acc_new, resp_null, resp_leg_link, resp_bp_randomness_relations) =
            generate_sigma_responses_for_common_state_change(
                sk_aff,
                sk_enc,
                account,
                updated_account,
                self.leaf_rerandomization,
                self.comm_bp_blinding,
                &self.t_acc_old,
                &self.t_acc_new,
                self.t_null.clone(),
                self.t_leg_link.clone(),
                &self.t_bp_randomness_relations,
                self.is_asset_id_revealed,
                challenge,
            )?;

        Zeroize::zeroize(&mut self.leaf_rerandomization);
        Zeroize::zeroize(&mut self.comm_bp_blinding);

        Ok(CommonStateChangeProof {
            partial: CommonStateChangeProofPartial {
                r1cs_proof: None,
                re_randomized_path: self.re_randomized_path.clone(),
                resp_null,
                comm_bp_randomness_relations: self.comm_bp_randomness_relations,
                resp_bp_randomness_relations,
            },
            resp_acc_old,
            resp_acc_new,
            resp_leg_link,
        })
    }
}

/// Host portion of the split account commitment proof for account state transition.
/// Does NOT include sk or sk_enc.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountCommitmentsHostProof<G: SWCurveConfig + Clone + Copy> {
    /// Full response for old re-randomized account (carries its commitment `t`)
    pub resp_acc_old: SchnorrResponse<Affine<G>>,
    /// Partial response for new account (carries its commitment `t`)
    pub resp_acc_new: PartialSchnorrResponse<Affine<G>>,
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsHostProof<G> {
    pub fn challenge_contribution(&self, transcript: &mut MerlinTranscript) -> Result<()> {
        self.resp_acc_old
            .challenge_contribution(dst::ACCOUNT_COMM_OLD, transcript)?;
        self.resp_acc_new
            .challenge_contribution(dst::ACCOUNT_COMM_NEW, transcript)?;
        Ok(())
    }
}

/// Prover-side protocol state for host's affirmation account commitment Schnorr proofs (without sk, sk_enc).
#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct AccountCommitmentsHostProtocol<G: SWCurveConfig + Clone + Copy> {
    pub t_acc_old: SchnorrCommitment<Affine<G>>,
    pub t_acc_new: SchnorrCommitment<Affine<G>>,
    /// Whether asset_id is revealed in this transaction
    pub is_asset_id_revealed: bool,
    // Blindings shared with BP and auth proof
    pub old_balance_blinding: G::ScalarField,
    pub new_balance_blinding: G::ScalarField,
    pub old_counter_blinding: G::ScalarField,
    pub initial_rho_blinding: G::ScalarField,
    pub old_rho_blinding: G::ScalarField,
    pub new_rho_blinding: G::ScalarField,
    pub initial_randomness_blinding: G::ScalarField,
    pub old_randomness_blinding: G::ScalarField,
    pub new_randomness_blinding: G::ScalarField,
    pub id_blinding: G::ScalarField,
    /// Random value for splitting the new commitment with auth proof.
    /// Auth proves `B_blinding * rand_new_comm` in its new commitment part.
    /// Host proves `B_blinding * (-rand_new_comm)` in its new commitment part.
    pub rand_new_comm: G::ScalarField,
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsHostProtocol<G> {
    /// Returns `(Self, asset_id_blinding)` where `asset_id_blinding` is `Some` when
    /// asset-id is hidden and is shared with the ct_asset_id_2 split proofs.
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
        b_blinding: Affine<G>,
        is_asset_id_revealed: bool,
        has_balance_changed: bool,
    ) -> (Self, Option<G::ScalarField>) {
        let (old_balance_blinding, new_balance_blinding) = if has_balance_changed {
            (G::ScalarField::rand(rng), G::ScalarField::rand(rng))
        } else {
            let b = G::ScalarField::rand(rng);
            (b, b)
        };
        let old_counter_blinding = G::ScalarField::rand(rng);
        let initial_rho_blinding = G::ScalarField::rand(rng);
        let old_rho_blinding = G::ScalarField::rand(rng);
        let new_rho_blinding = G::ScalarField::rand(rng);
        let initial_randomness_blinding = G::ScalarField::rand(rng);
        let old_randomness_blinding = G::ScalarField::rand(rng);
        let new_randomness_blinding = G::ScalarField::rand(rng);
        let id_blinding = G::ScalarField::rand(rng);
        let asset_id_blinding = (!is_asset_id_revealed).then(|| G::ScalarField::rand(rng));
        let rand_new_comm = G::ScalarField::rand(rng);

        let (t_acc_old, t_acc_new) = create_account_commitment_t_values(
            rng,
            false, // include_sk: host mode
            &account_comm_key,
            b_blinding,
            is_asset_id_revealed,
            None, // sk_blinding — not used in host mode
            old_balance_blinding,
            new_balance_blinding,
            old_counter_blinding,
            asset_id_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            initial_randomness_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
            id_blinding,
            None, // sk_enc_blinding — not used in host mode
        );

        (
            Self {
                t_acc_old,
                t_acc_new,
                is_asset_id_revealed,
                old_balance_blinding,
                new_balance_blinding,
                old_counter_blinding,
                initial_rho_blinding,
                old_rho_blinding,
                new_rho_blinding,
                initial_randomness_blinding,
                old_randomness_blinding,
                new_randomness_blinding,
                id_blinding,
                rand_new_comm,
            },
            asset_id_blinding,
        )
    }

    pub fn challenge_contribution(&self, transcript: &mut MerlinTranscript) -> Result<()> {
        self.t_acc_old
            .challenge_contribution(dst::ACCOUNT_COMM_OLD, transcript)?;
        self.t_acc_new
            .challenge_contribution(dst::ACCOUNT_COMM_NEW, transcript)?;
        Ok(())
    }

    /// Generate the host's Schnorr proofs for account commitments.
    /// `host_rerandomization` is the host's share of the leaf rerandomization scalar.
    pub fn gen_proof(
        self,
        challenge: &G::ScalarField,
        account: &AccountState<Affine<G>>,
        updated_account: &AccountState<Affine<G>>,
        host_rerandomization: G::ScalarField,
    ) -> Result<AccountCommitmentsHostProof<G>> {
        let (resp_acc_old, resp_acc_new) = generate_account_commitment_responses(
            account,
            updated_account,
            &self.t_acc_old,
            &self.t_acc_new,
            self.is_asset_id_revealed,
            false, // include_sk: host mode
            None,
            None,
            None,
            Some(host_rerandomization),
            Some(-self.rand_new_comm), // B_blinding witness for new commitment
            challenge,
        )?;

        Ok(AccountCommitmentsHostProof {
            resp_acc_old,
            resp_acc_new,
        })
    }
}

/// Prover-side protocol state for host's partial affirmation proof (BP, nullifier, transcript).
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct CommonStateChangePartialProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub t_null: PokDiscreteLogProtocol<Affine<G0>>,
    pub t_bp: SchnorrCommitment<Affine<G0>>,
    #[zeroize(skip)]
    pub re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G0, G1>>,
    pub rerandomization: F0,
    #[zeroize(skip)]
    pub comm_bp: Affine<G0>,
    pub comm_bp_blinding: F0,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonStateChangePartialProtocol<L, F0, F1, G0, G1>
{
    /// Initialize the host's partial protocol: curve-tree re-randomization, transcript setup,
    /// nullifier T-value, BP commit + constraints (6 values, no sk_enc/sk_enc_inv), BP T-value.
    ///
    /// This does NOT create leg-link or leg-amount proofs (those are in the auth proof).
    ///
    /// Returns (protocol, nullifier).
    pub fn init_with_given_prover<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<Affine<G0>>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        account_tree_root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        // Shared blindings from AffirmationCommitmentsHostProtocol
        initial_rho_blinding: F0,
        old_rho_blinding: F0,
        new_rho_blinding: F0,
        initial_randomness_blinding: F0,
        old_randomness_blinding: F0,
        new_randomness_blinding: F0,
        even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        let (re_randomized_path, rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget_new::<_, Parameters0, Parameters1>(
                even_prover,
                odd_prover,
                account_tree_params,
                rng,
                None,
            )?;

        add_to_transcript!(
            even_prover.transcript(),
            ROOT_LABEL,
            account_tree_root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
        );

        let (mut p, nullifier) = Self::init_with_given_prover_with_rerandomized_leaf(
            rng,
            legs_with_conf,
            account,
            updated_account,
            updated_account_commitment,
            rerandomization,
            nonce,
            account_tree_params,
            account_comm_key,
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            initial_randomness_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
            even_prover,
        )?;
        p.re_randomized_path = Some(re_randomized_path);
        Ok((p, nullifier))
    }

    /// Initialize the host's partial protocol when the leaf has already been re-randomized externally.
    /// Used for batched (multi-asset) proving.
    pub fn init_with_given_prover_with_rerandomized_leaf<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<Affine<G0>>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_rerandomization: F0,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        initial_rho_blinding: F0,
        old_rho_blinding: F0,
        new_rho_blinding: F0,
        initial_randomness_blinding: F0,
        old_randomness_blinding: F0,
        new_randomness_blinding: F0,
        even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    ) -> Result<(Self, Affine<G0>)> {
        let asset_id = account.asset_id();
        let (_, legs, _, _) = legs_for_proof(legs_with_conf, asset_id)?;

        add_to_transcript!(
            even_prover.transcript(),
            NONCE_LABEL,
            nonce,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        for (leg_core, eph_pk) in &legs {
            add_to_transcript!(
                even_prover.transcript(),
                LEG_ENC_LABEL,
                leg_core,
                LEG_ENC_LABEL,
                eph_pk
            );
        }

        let (nullifier, comm_bp, comm_bp_blinding, t_null, t_bp, _) = create_bp_and_null_t_values(
            rng,
            false, // include_sk: host mode
            account.rho(),
            account.current_rho(),
            updated_account.current_rho(),
            account.randomness(),
            account.current_randomness(),
            updated_account.current_randomness(),
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            initial_randomness_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
            None, // sk_enc — not used in host mode
            None, // sk_enc_blinding — not used in host mode
            None, // sk_enc_inv_blinding — not used in host mode
            even_prover,
            &account_comm_key,
            &account_tree_params.even_parameters.pc_gens(),
            &account_tree_params.even_parameters.bp_gens(),
        )?;

        // NOTE: Challenge contributions for t_null and t_bp are NOT written here.
        // The caller writes all challenge contributions in the correct order
        // matching solo transcript ordering.

        Ok((
            Self {
                t_null,
                t_bp,
                re_randomized_path: None,
                rerandomization: leaf_rerandomization,
                comm_bp,
                comm_bp_blinding,
            },
            nullifier,
        ))
    }

    /// Generate the partial proof given the host challenge.
    pub fn gen_proof(mut self, challenge: &F0) -> CommonStateChangeProofPartial<F0, F1, G0, G1, L> {
        // `Self` is `ZeroizeOnDrop` (no move-out), so `take()` the `Option` path rather than
        // cloning it; `self` still drops at the end, zeroizing its secret fields.
        let (resp_null, resp_bp) = generate_null_bp_responses(
            self.comm_bp_blinding,
            self.t_null.clone(),
            &self.t_bp,
            None, // include_sk: host mode
            challenge,
        )
        .unwrap();

        CommonStateChangeProofPartial {
            r1cs_proof: None,
            re_randomized_path: self.re_randomized_path.take(),
            resp_null,
            comm_bp_randomness_relations: self.comm_bp,
            resp_bp_randomness_relations: resp_bp,
        }
    }
}

/// Data produced by the host in the split (W2/W3) affirmation flow.
/// Contains all host-side proof components + auth shares.
pub struct CommonAffirmationHostProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub partial: CommonStateChangeProofPartial<F0, F1, G0, G1, L>,
    pub host_commitment_proof: AccountCommitmentsHostProof<G0>,
    /// Host's PokPedersenCommitment proofs for ct_asset_id part (one per leg with hidden asset-id).
    /// `ct_asset_id = enc_gen * asset_id + B_blinding * (-k_2)`.
    /// The asset-id is shared with the account commitments
    pub resp_ct_asset_id: Vec<Partial2PokPedersenCommitment<Affine<G0>>>,
    /// Host's proofs for `ct_amount_2 = enc_gen * amount + B_blinding * (-k)`, one per
    /// `needs_ct_amount` leg. Full proof: amount is owned here and consumed by the balance BP.
    pub resp_ct_amount: Vec<PokPedersenCommitment<Affine<G0>>>,
    /// Auth's share of the leaf rerandomization scalar
    pub auth_rerandomization: F0,
    /// Commitment randomness for auth's new commitment part (B_blinding * rand_new_comm)
    pub auth_rand_new_comm: F0,
}

/// Prover-side protocol state for the host in the split (W2/W3) affirmation flow.
/// Analogous to `CommonTransparentSplitProtocol` for transparent transactions.
///
/// `init()` returns `(Self, Prover, Prover, nullifier)`.
/// `init_with_given_prover()` returns `(Self, nullifier)` for batched proving.
/// `gen_proof()` / `gen_proof_partial()` consume `Self` and produce `AffirmationSplitHostProof`.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct CommonAffirmationSplitProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    acc_host_proto: AccountCommitmentsHostProtocol<G0>,
    // Partial protocol state (stored inline to avoid lifetime from Prover)
    t_null: PokDiscreteLogProtocol<Affine<G0>>,
    t_bp: SchnorrCommitment<Affine<G0>>,
    #[zeroize(skip)]
    re_randomized_path: Option<SelectAndRerandomizePathWithDivisorComms<L, G0, G1>>,
    #[zeroize(skip)]
    comm_bp: Affine<G0>,
    comm_bp_blinding: F0,
    old_account: AccountState<Affine<G0>>,
    updated_account: AccountState<Affine<G0>>,
    ct_asset_id: Vec<(Affine<G0>, PokPedersenCommitmentProtocol<Affine<G0>>)>,
    /// Host `ct_amount_2 = enc_gen * amount + B_blinding * (-k)`, one per `needs_ct_amount` leg.
    ct_amount: Vec<(Affine<G0>, PokPedersenCommitmentProtocol<Affine<G0>>)>,
    /// Witness-1 blindings of the balance-changed legs' `ct_amount_2`, in leg order, handed to the
    /// `BalanceSplitProver` so its balance BP amount slots use the same amounts as those `ct_amount_2`.
    balance_amount_blindings: Vec<F0>,
    host_rerandomization: F0,
    /// Auth's share of the leaf rerandomization scalar
    pub auth_rerandomization: F0,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonAffirmationSplitProtocol<L, F0, F1, G0, G1>
{
    /// Initialize the split protocol: creates provers, host commitment protocol, partial protocol,
    /// writes all challenge contributions, derives challenge.
    /// Returns `(protocol, even_prover, odd_prover, nullifier)`.
    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<Affine<G0>>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        account_tree_root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        k_asset_ids: &[F0],
        k_amounts: &[F0],
    ) -> Result<(
        Self,
        Prover<'a, MerlinTranscript, Affine<G0>>,
        Prover<'a, MerlinTranscript, Affine<G1>>,
        Affine<G0>,
    )> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens(),
            even_transcript,
        );
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.pc_gens(),
            odd_transcript,
        );

        let (acc_host_proto, asset_id_blinding, b_blinding) =
            Self::validate_and_init_comm_protocol(
                rng,
                &legs_with_conf,
                k_asset_ids.len(),
                account_comm_key.clone(),
                account_tree_params,
            )?;

        let (partial_proto, nullifier) = CommonStateChangePartialProtocol::init_with_given_prover::<
            _,
            Parameters0,
            Parameters1,
        >(
            rng,
            legs_with_conf.clone(),
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            account_tree_root,
            nonce,
            account_tree_params,
            account_comm_key.clone(),
            acc_host_proto.initial_rho_blinding,
            acc_host_proto.old_rho_blinding,
            acc_host_proto.new_rho_blinding,
            acc_host_proto.initial_randomness_blinding,
            acc_host_proto.old_randomness_blinding,
            acc_host_proto.new_randomness_blinding,
            &mut even_prover,
            &mut odd_prover,
        )?;

        let protocol = Self::init_inner(
            rng,
            account,
            updated_account,
            acc_host_proto,
            asset_id_blinding,
            partial_proto,
            nullifier,
            account_comm_key,
            enc_gen,
            k_asset_ids,
            b_blinding,
            &legs_with_conf,
            k_amounts,
            &mut even_prover,
        )?;

        Ok((protocol, even_prover, odd_prover, nullifier))
    }

    /// Initialize the split protocol with an external prover and pre-rerandomized leaf.
    /// Used for batched (multi-asset) proving where the caller owns the provers.
    /// Returns `(protocol, nullifier)`.
    pub fn init_with_given_prover_with_rerandomized_leaf<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: Vec<LegProverConfig<Affine<G0>>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_rerandomization: F0,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        k_asset_ids: &[F0],
        k_amounts: &[F0],
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
    ) -> Result<(Self, Affine<G0>)> {
        let (acc_host_proto, asset_id_blinding, b_blinding) =
            Self::validate_and_init_comm_protocol(
                rng,
                &legs_with_conf,
                k_asset_ids.len(),
                account_comm_key.clone(),
                account_tree_params,
            )?;

        let (partial_proto, nullifier) =
            CommonStateChangePartialProtocol::init_with_given_prover_with_rerandomized_leaf::<
                _,
                Parameters0,
                Parameters1,
            >(
                rng,
                legs_with_conf.clone(),
                account,
                updated_account,
                updated_account_commitment,
                leaf_rerandomization,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                acc_host_proto.initial_rho_blinding,
                acc_host_proto.old_rho_blinding,
                acc_host_proto.new_rho_blinding,
                acc_host_proto.initial_randomness_blinding,
                acc_host_proto.old_randomness_blinding,
                acc_host_proto.new_randomness_blinding,
                even_prover,
            )?;

        let protocol = Self::init_inner(
            rng,
            account,
            updated_account,
            acc_host_proto,
            asset_id_blinding,
            partial_proto,
            nullifier,
            account_comm_key,
            enc_gen,
            k_asset_ids,
            b_blinding,
            &legs_with_conf,
            k_amounts,
            even_prover,
        )?;

        Ok((protocol, nullifier))
    }

    fn validate_and_init_comm_protocol<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        legs_with_conf: &[LegProverConfig<Affine<G0>>],
        expected_hidden_asset_ids: usize,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
    ) -> Result<(AccountCommitmentsHostProtocol<G0>, Option<F0>, Affine<G0>)> {
        let (asset_id, num_hidden_asset_ids) =
            LegProverConfig::asset_id_and_hidden_count(legs_with_conf)?;
        // Asset id revealed in at-least one leg
        let is_asset_id_revealed = asset_id.is_some();
        // If asset-id is revealed in at least one leg, the prover does not treat it as witness in
        // any leg and this no blindings are needed
        let expected_blindings_asset_ids = if is_asset_id_revealed {
            0
        } else {
            num_hidden_asset_ids
        };
        if expected_hidden_asset_ids != expected_blindings_asset_ids {
            return Err(Error::ProofGenerationError(format!(
                "k_asset_ids length {} does not match expected {}",
                expected_hidden_asset_ids, expected_blindings_asset_ids
            )));
        }

        let has_balance_changed = LegProverConfig::has_balance_changed(legs_with_conf);
        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        let (acc_host_proto, asset_id_blinding) = AccountCommitmentsHostProtocol::init(
            rng,
            account_comm_key,
            b_blinding,
            is_asset_id_revealed,
            has_balance_changed,
        );
        Ok((acc_host_proto, asset_id_blinding, b_blinding))
    }

    /// challenge contributions, ct_asset_id, split secrets.
    fn init_inner<'a, R: CryptoRngCore>(
        rng: &mut R,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        acc_host_proto: AccountCommitmentsHostProtocol<G0>,
        asset_id_blinding: Option<F0>,
        mut partial_proto: CommonStateChangePartialProtocol<L, F0, F1, G0, G1>,
        nullifier: Affine<G0>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_gen: Affine<G0>,
        k_asset_ids: &[F0],
        b_blinding: Affine<G0>,
        legs_with_conf: &[LegProverConfig<Affine<G0>>],
        k_amounts: &[F0],
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
    ) -> Result<Self> {
        // `partial_proto` is `ZeroizeOnDrop` (no move-out): clone the non-`Default` protocol
        // structs, `take()` the `Option` path to avoid cloning it, and copy the `Copy` scalars/
        // points. `partial_proto` then drops at the end, zeroizing its secret fields.
        let t_null = partial_proto.t_null.clone();
        let t_bp = partial_proto.t_bp.clone();
        let re_randomized_path = partial_proto.re_randomized_path.take();
        let comm_bp = partial_proto.comm_bp;
        let comm_bp_blinding = partial_proto.comm_bp_blinding;
        let rerandomization = partial_proto.rerandomization;

        {
            let mut transcript = even_prover.transcript();
            acc_host_proto
                .t_acc_old
                .challenge_contribution(dst::ACCOUNT_COMM_OLD, &mut transcript)?;
            acc_host_proto
                .t_acc_new
                .challenge_contribution(dst::ACCOUNT_COMM_NEW, &mut transcript)?;
            t_bp.challenge_contribution(dst::BP_RANDOMNESS_RELATIONS, &mut transcript)?;
            let null_gen = account_comm_key.current_rho_gen();
            t_null.challenge_contribution(
                &null_gen,
                &nullifier,
                dst::NULLIFIER,
                &mut transcript,
            )?;
        }

        let mut ct_asset_id_2_protos = Vec::new();
        if let Some(asset_id_blinding) = asset_id_blinding {
            ct_asset_id_2_protos = Self::asset_id_proto(
                rng,
                F0::from(account.asset_id()),
                asset_id_blinding,
                k_asset_ids,
                enc_gen,
                b_blinding,
            );

            {
                let mut transcript = even_prover.transcript();
                for (ct_asset_id_2, proto) in &ct_asset_id_2_protos {
                    proto.challenge_contribution(
                        &enc_gen,
                        &b_blinding,
                        ct_asset_id_2,
                        dst::HOST_CT_ASSET_ID_2,
                        &mut transcript,
                    )?;
                }
            }
        }

        // ct_amount_2 = enc_gen * amount + B_blinding * (-k), one per needs_ct_amount leg. The
        // witness-1 (amount) blindings of the balance-changed legs are handed to the balance BP so
        // its amount slots use the same amount as these ct_amount_2, which equals the amount in ct_amount.
        let amount_blindings: Vec<F0> = (0..k_amounts.len()).map(|_| F0::rand(rng)).collect();
        let ct_amount_2_protos = Self::amount_proto(
            rng,
            legs_with_conf,
            &amount_blindings,
            k_amounts,
            enc_gen,
            b_blinding,
        );
        {
            let mut transcript = even_prover.transcript();
            for (ct_amount_2, proto) in &ct_amount_2_protos {
                proto.challenge_contribution(
                    &enc_gen,
                    &b_blinding,
                    ct_amount_2,
                    dst::HOST_CT_AMOUNT_2,
                    &mut transcript,
                )?;
            }
        }
        let mut balance_amount_blindings = Vec::new();
        let mut amount_idx = 0;
        for conf in legs_with_conf {
            if conf.needs_ct_amount() {
                if conf.has_balance_changed {
                    balance_amount_blindings.push(amount_blindings[amount_idx]);
                }
                amount_idx += 1;
            }
        }

        // Split rerandomization
        let host_rerandomization = F0::rand(rng);
        let auth_rerandomization = rerandomization - host_rerandomization;

        {
            let is_asset_id_revealed = acc_host_proto.is_asset_id_revealed;
            let balance: F0 = account.balance().into();
            let counter: F0 = account.counter().into();
            let mut old_wits = Vec::with_capacity(NUM_GENERATORS);
            old_wits.push(balance);
            old_wits.push(counter);
            if !is_asset_id_revealed {
                old_wits.push(account.asset_id().into());
            }
            old_wits.push(account.rho());
            old_wits.push(account.current_rho());
            old_wits.push(account.randomness());
            old_wits.push(account.current_randomness());
            old_wits.push(account.id());
            old_wits.push(host_rerandomization);

            let gens_old: Vec<Affine<G0>> = if is_asset_id_revealed {
                account_comm_key
                    .as_gens_with_blinding_without_sk_and_asset_id(b_blinding)
                    .to_vec()
            } else {
                account_comm_key
                    .as_gens_with_blinding_without_sk(b_blinding)
                    .to_vec()
            };

            let reduced_acc_old =
                <Projective<G0> as VariableBaseMSM>::msm_unchecked(&gens_old, &old_wits)
                    .into_affine();

            let mut new_wits = old_wits;
            let last = new_wits.len() - 1;
            new_wits[last] = -acc_host_proto.rand_new_comm;
            let has_balance_changed = account.balance() != updated_account.balance();
            if has_balance_changed {
                new_wits[0] = updated_account.balance().into();
            }
            let current_rho_idx = if is_asset_id_revealed { 3 } else { 4 };
            let current_randomness_idx = if is_asset_id_revealed { 5 } else { 6 };
            new_wits[current_rho_idx] = updated_account.current_rho();
            new_wits[current_randomness_idx] = updated_account.current_randomness();

            let mut gens_new = gens_old;
            gens_new[last] = b_blinding;
            let reduced_acc_new =
                <Projective<G0> as VariableBaseMSM>::msm_unchecked(&gens_new, &new_wits)
                    .into_affine();

            #[cfg(not(feature = "ignore_prover_input_sanitation"))]
            if cfg!(debug_assertions) {
                // y_old - y_new should equal the contribution of the
                // fields that differ (balance if changed, current_rho, current_randomness,
                // B_blinding term).
                let mut diff_wits = vec![F0::zero(); gens_new.len()];
                if has_balance_changed {
                    diff_wits[0] = balance - F0::from(updated_account.balance());
                }
                diff_wits[current_rho_idx] = account.current_rho() - updated_account.current_rho();
                diff_wits[current_randomness_idx] =
                    account.current_randomness() - updated_account.current_randomness();
                diff_wits[last] = host_rerandomization + acc_host_proto.rand_new_comm;
                debug_assert_eq!(
                    (reduced_acc_old.into_group() - reduced_acc_new.into_group()).into_affine(),
                    <Projective<G0> as VariableBaseMSM>::msm_unchecked(&gens_new, &diff_wits)
                        .into_affine()
                );
            }

            let transcript = even_prover.transcript();
            transcript.append(b"acc_comm_old", &reduced_acc_old);
            transcript.append(b"acc_comm_new", &reduced_acc_new);
        }

        Ok(Self {
            acc_host_proto,
            t_null,
            t_bp,
            re_randomized_path,
            comm_bp,
            comm_bp_blinding,
            old_account: account.clone(),
            updated_account: updated_account.clone(),
            ct_asset_id: ct_asset_id_2_protos,
            ct_amount: ct_amount_2_protos,
            balance_amount_blindings,
            host_rerandomization,
            auth_rerandomization,
        })
    }

    /// Returns the rerandomized leaf point (needed by the auth proof).
    pub fn rerandomized_leaf(&self) -> Affine<G0> {
        self.re_randomized_path
            .as_ref()
            .expect("re_randomized_path must be set for non-batched proving")
            .path
            .get_rerandomized_leaf()
            .expect("rerandomized leaf must be set")
    }

    /// Returns the old balance blinding from the host commitment protocol.
    pub fn old_balance_blinding(&self) -> F0 {
        self.acc_host_proto.old_balance_blinding
    }

    /// Returns the new balance blinding from the host commitment protocol.
    pub fn new_balance_blinding(&self) -> F0 {
        self.acc_host_proto.new_balance_blinding
    }

    /// Witness-1 (amount) blindings of the balance-changed legs' `ct_amount_2`, in leg order, to be
    /// consumed by the `BalanceSplitProver` so its balance BP amount slots use the same amounts as those `ct_amount_2`.
    pub fn balance_amount_blindings(&self) -> Vec<F0> {
        self.balance_amount_blindings.clone()
    }

    /// Returns the commitment randomness for auth's new commitment part.
    pub fn auth_rand_new_comm(&self) -> F0 {
        self.acc_host_proto.rand_new_comm
    }

    /// Generate the host's proofs, consuming the protocol. Finalizes the Bulletproof.
    /// Returns `AffirmationSplitHostProof`.
    pub fn gen_proof<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        challenge: &F0,
        even_prover: Prover<'_, MerlinTranscript, Affine<G0>>,
        odd_prover: Prover<'_, MerlinTranscript, Affine<G1>>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        rng: &mut R,
    ) -> Result<CommonAffirmationHostProof<L, F0, F1, G0, G1>> {
        let mut host_proof = self.gen_proof_partial(challenge)?;

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;
        host_proof.partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok(host_proof)
    }

    /// Generate the host's proofs without finalizing the Bulletproof.
    /// Used for batched proving where the caller finalizes BP externally.
    /// The returned `partial.r1cs_proof` is `None`.
    pub fn gen_proof_partial(
        mut self,
        challenge: &F0,
    ) -> Result<CommonAffirmationHostProof<L, F0, F1, G0, G1>> {
        // `Self` is `ZeroizeOnDrop`, so it cannot be destructured by move. Pull the owned
        // fields out without moving out of `self`: `take()` the `Default`-able fields (the
        // `Option` path and the `Vec`s, avoiding a clone of the large rerandomized path),
        // `clone()` the small protocol structs, and copy the `Copy` scalars. `self` then
        // drops at the end of the function, zeroizing the secret fields it still holds.
        let acc_host_proto = self.acc_host_proto.clone();
        let t_null = self.t_null.clone();
        let t_bp = self.t_bp.clone();
        let re_randomized_path = self.re_randomized_path.take();
        let comm_bp = self.comm_bp;
        let comm_bp_blinding = self.comm_bp_blinding;
        let ct_asset_id_2_protos = core::mem::take(&mut self.ct_asset_id);
        let ct_amount_2_protos = core::mem::take(&mut self.ct_amount);
        let host_rerandomization = self.host_rerandomization;
        let auth_rerandomization = self.auth_rerandomization;

        // Save rand_new_comm before consuming acc_host_proto
        let auth_rand_new_comm = acc_host_proto.rand_new_comm;

        // Generate host commitment proof
        let host_commitment_proof = acc_host_proto.gen_proof(
            challenge,
            &self.old_account,
            &self.updated_account,
            host_rerandomization,
        )?;

        // Generate partial proof (nullifier + BP Schnorr)
        let (resp_null, resp_bp) = generate_null_bp_responses(
            comm_bp_blinding,
            t_null,
            &t_bp,
            None, // include_sk: host mode
            challenge,
        )?;

        let partial = CommonStateChangeProofPartial {
            r1cs_proof: None,
            re_randomized_path,
            resp_null,
            comm_bp_randomness_relations: comm_bp,
            resp_bp_randomness_relations: resp_bp,
        };

        // Generate ct_asset_id_2 proofs
        let resp_ct_asset_id_2: Vec<_> = ct_asset_id_2_protos
            .into_iter()
            .map(|(_, proto)| proto.gen_partial2_proof(challenge))
            .collect();

        // Generate ct_amount_2 proofs (full: amount owned here, consumed by the balance BP)
        let resp_ct_amount: Vec<_> = ct_amount_2_protos
            .into_iter()
            .map(|(_, proto)| proto.gen_proof(challenge))
            .collect();

        Ok(CommonAffirmationHostProof {
            partial,
            host_commitment_proof,
            resp_ct_asset_id: resp_ct_asset_id_2,
            resp_ct_amount,
            auth_rerandomization,
            auth_rand_new_comm,
        })
    }
}

/// Separate impl block so `#[mockable]` covers only `asset_id_proto`.
/// Tests mock this to inject a forged asset-id and verify the cross-binding rejects it.
#[cfg_attr(
    all(test, feature = "nightly_mocking_tests"),
    mocktopus::macros::mockable
)]
impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonAffirmationSplitProtocol<L, F0, F1, G0, G1>
{
    pub(crate) fn asset_id_proto<R: CryptoRngCore>(
        rng: &mut R,
        asset_id: F0,
        asset_id_blinding: F0,
        k_asset_ids: &[F0],
        enc_gen: Affine<G0>,
        b_blinding: Affine<G0>,
    ) -> Vec<(Affine<G0>, PokPedersenCommitmentProtocol<Affine<G0>>)> {
        k_asset_ids
            .iter()
            .map(|&k_asset_id| {
                let ct_asset_id_2 = (enc_gen * asset_id + b_blinding * (-k_asset_id)).into_affine();
                let proto = PokPedersenCommitmentProtocol::init(
                    asset_id,
                    asset_id_blinding,
                    &enc_gen,
                    -k_asset_id,
                    F0::rand(rng),
                    &b_blinding,
                );
                (ct_asset_id_2, proto)
            })
            .collect()
    }

    pub(crate) fn amount_proto<R: CryptoRngCore>(
        rng: &mut R,
        legs_with_conf: &[LegProverConfig<Affine<G0>>],
        amount_blindings: &[F0],
        k_amounts: &[F0],
        enc_gen: Affine<G0>,
        b_blinding: Affine<G0>,
    ) -> Vec<(Affine<G0>, PokPedersenCommitmentProtocol<Affine<G0>>)> {
        let mut protos = Vec::with_capacity(k_amounts.len());
        let mut idx = 0;
        for conf in legs_with_conf {
            if conf.needs_ct_amount() {
                let amount = F0::from(conf.amount);
                let ct_amount_2 = (enc_gen * amount + b_blinding * (-k_amounts[idx])).into_affine();
                let proto = PokPedersenCommitmentProtocol::init(
                    amount,
                    amount_blindings[idx],
                    &enc_gen,
                    -k_amounts[idx],
                    F0::rand(rng),
                    &b_blinding,
                );
                protos.push((ct_amount_2, proto));
                idx += 1;
            }
        }
        protos
    }
}

/// The full split proof: partial (host BP/nullifier) + host + auth
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommonAffirmationSplitProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub partial: CommonStateChangeProofPartial<F0, F1, G0, G1, L>,
    pub host_commitment_proof: AccountCommitmentsHostProof<G0>,
    pub resp_ct_asset_id: Vec<Partial2PokPedersenCommitment<Affine<G0>>>,
    pub resp_ct_amount: Vec<PokPedersenCommitment<Affine<G0>>>,
    pub auth_proof: AuthProofAffirmation<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> CommonAffirmationSplitProof<L, F0, F1, G0, G1>
{
    pub fn assemble(
        host_data: CommonAffirmationHostProof<L, F0, F1, G0, G1>,
        auth_proof: AuthProofAffirmation<Affine<G0>>,
    ) -> Self {
        Self {
            partial: host_data.partial,
            host_commitment_proof: host_data.host_commitment_proof,
            resp_ct_asset_id: host_data.resp_ct_asset_id,
            resp_ct_amount: host_data.resp_ct_amount,
            auth_proof,
        }
    }
}

pub fn ensure_same_accounts<G: AffineRepr>(
    old_state: &AccountState<G>,
    new_state: &AccountState<G>,
    has_balance_changed: bool,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if old_state.pk_aff() != new_state.pk_aff() {
            return Err(Error::ProofGenerationError(
                "Affirmation public key mismatch between old and new account states".to_string(),
            ));
        }
        if old_state.pk_enc() != new_state.pk_enc() {
            return Err(Error::ProofGenerationError(
                "Encryption public key mismatch between old and new account states".to_string(),
            ));
        }
        if old_state.id != new_state.id {
            return Err(Error::ProofGenerationError(
                "Identity mismatch between old and new account states".to_string(),
            ));
        }
        if old_state.asset_id != new_state.asset_id {
            return Err(Error::ProofGenerationError(format!(
                "Asset ID mismatch between old and new account states: old = {}, new = {}",
                old_state.asset_id, new_state.asset_id
            )));
        }
        if old_state.rho != new_state.rho {
            return Err(Error::ProofGenerationError(
                "Initial rho mismatch between old and new account states".to_string(),
            ));
        }
        if has_balance_changed {
            if old_state.balance == new_state.balance {
                return Err(Error::ProofGenerationError(
                    "Balance should have changed but it hasn't".to_string(),
                ));
            }
        } else {
            if old_state.balance != new_state.balance {
                return Err(Error::ProofGenerationError(
                    "Balance shouldn't have changed but it has".to_string(),
                ));
            }
        }
        if old_state.current_rho * old_state.rho != new_state.current_rho {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly constructed".to_string(),
            ));
        }
        if old_state.randomness != new_state.randomness {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly constructed".to_string(),
            ));
        }
        if old_state.current_randomness * old_state.randomness != new_state.current_randomness {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly constructed".to_string(),
            ));
        }
        Ok(())
    }
}

pub(crate) fn legs_for_proof<G: AffineRepr>(
    legs_with_conf: Vec<LegProverConfig<G>>,
    asset_id: AssetId,
) -> Result<
    (
        bool,
        Vec<(LegEncryptionCore<G>, PartyEphemeralPublicKey<G>)>,
        Vec<Balance>,
        Vec<bool>,
    ),
    Error,
> {
    let mut legs = Vec::with_capacity(legs_with_conf.len());
    let mut amounts = Vec::with_capacity(legs_with_conf.len());
    let mut has_balance_changed = Vec::with_capacity(legs_with_conf.len());
    let mut is_asset_id_revealed = false;
    // If asset-id is revealed in any of the leg encryptions, then its assumed that its revealed and the proof
    // is done accordingly
    for leg_conf in legs_with_conf {
        if let Some(a) = leg_conf.encryption.asset_id() {
            if a != asset_id {
                return Err(Error::ProofGenerationError(format!(
                    "Asset-id mismatch between leg config and account state: leg config = {a}, account = {}",
                    asset_id
                )));
            }
            is_asset_id_revealed = true;
        }
        amounts.push(leg_conf.amount);
        has_balance_changed.push(leg_conf.has_balance_changed);
        legs.push((leg_conf.encryption, leg_conf.party_eph_pk));
    }
    Ok((is_asset_id_revealed, legs, amounts, has_balance_changed))
}
