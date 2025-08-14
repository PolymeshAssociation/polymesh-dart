use std::iter::Copied;
use ark_ec::AffineRepr;
use crate::error::*;
use crate::{AMOUNT_BITS, AssetId, Balance};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::{Field, PrimeField};
use ark_serialize::CanonicalSerialize;
use ark_std::vec;
use bulletproofs::{BulletproofGens, PedersenGens};
use bulletproofs::r1cs::{ConstraintSystem, Prover, R1CSProof, Variable, Verifier};
use curve_tree_relations::curve_tree::{Root, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::range_proof::{difference, range_proof};
use dock_crypto_utils::transcript::MerlinTranscript;
use rand_core::{CryptoRng, RngCore};
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use crate::account::{AccountCommitmentKeyTrait, AccountState};
use crate::leg::LegEncryption;

/// Creates two new transcripts and two new provers, one for even level and one for odd.
/// Also re-randomizes the path and enforces the corresponding constraints. Returns the even prover,
/// odd prover, re-randomize path and blinding used to re-randomize the leaf
pub fn initialize_curve_tree_prover<
    'g,
    R: RngCore,
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    rng: &mut R,
    even_label: &'static [u8],
    odd_label: &'static [u8],
    leaf_path: CurveTreeWitnessPath<L, G0, G1>,
    tree_parameters: &'g SelRerandParameters<G0, G1>,
) -> (
    Prover<'g, MerlinTranscript, Affine<G0>>,
    Prover<'g, MerlinTranscript, Affine<G1>>,
    SelectAndRerandomizePath<L, G0, G1>,
    F0,
) {
    let even_transcript = MerlinTranscript::new(even_label);
    let mut even_prover = Prover::new(&tree_parameters.even_parameters.pc_gens, even_transcript);

    let odd_transcript = MerlinTranscript::new(odd_label);
    let mut odd_prover = Prover::new(&tree_parameters.odd_parameters.pc_gens, odd_transcript);

    let (re_randomized_path, rerandomization) = leaf_path.select_and_rerandomize_prover_gadget(
        &mut even_prover,
        &mut odd_prover,
        tree_parameters,
        rng,
    );

    (even_prover, odd_prover, re_randomized_path, rerandomization)
}

/// Creates two new transcripts and two new verifiers, one for even level and one for odd.
/// Adds the path commitments and enforces the corresponding constraints.
/// Returns the even verifier and odd verifier,
pub fn initialize_curve_tree_verifier<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_label: &'static [u8],
    odd_label: &'static [u8],
    mut re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    tree_root: &Root<L, 1, G0, G1>,
    tree_parameters: &SelRerandParameters<G0, G1>,
) -> (
    Verifier<MerlinTranscript, Affine<G0>>,
    Verifier<MerlinTranscript, Affine<G1>>,
) {
    let even_transcript = MerlinTranscript::new(even_label);
    let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
    let odd_transcript = MerlinTranscript::new(odd_label);
    let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

    re_randomized_path.add_root(tree_root);

    #[cfg(feature = "parallel")]
    rayon::join(
        || {
            // Enforce constraints for odd level
            re_randomized_path.odd_verifier_gadget(tree_root, &mut odd_verifier, &tree_parameters);
        },
        || {
            // Enforce constraints for even level
            re_randomized_path.even_verifier_gadget(
                tree_root,
                &mut even_verifier,
                &tree_parameters,
            );
        },
    );

    #[cfg(not(feature = "parallel"))]
    {
        // Enforce constraints for odd level
        re_randomized_path.odd_verifier_gadget(tree_root, &mut odd_verifier, &tree_parameters);

        // Enforce constraints for even level
        re_randomized_path.even_verifier_gadget(tree_root, &mut even_verifier, &tree_parameters);
    }

    (even_verifier, odd_verifier)
}

/// Enforce that balance has correctly changed. If `has_balance_decreased` is true, then `old_bal - new_bal = amount` else `new_bal - old_bal = amount`
pub fn enforce_balance_change_prover<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    old_bal: Balance,
    new_bal: Balance,
    amount: Balance,
    has_balance_decreased: bool,
    even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
) -> Result<((F0, Affine<G0>), (F0, Affine<G0>), (F0, Affine<G0>))> {
    // Commit to amount, old and new balance
    // TODO: It makes sense to commit to all these in a single vector commitment
    let r_bal_old = F0::rand(rng);
    let (comm_bal_old, var_bal_old) = even_prover.commit(F0::from(old_bal), r_bal_old);

    let r_bal_new = F0::rand(rng);
    let (comm_bal_new, var_bal_new) = even_prover.commit(F0::from(new_bal), r_bal_new);

    let r_amount = F0::rand(rng);
    let (comm_amount, var_amount) = even_prover.commit(F0::from(amount), r_amount);

    // TODO: Combined the following 2 gadgets reduce 1 constraint
    if has_balance_decreased {
        // old - new balance is correct
        difference(
            even_prover,
            var_bal_old.into(),
            var_bal_new.into(),
            var_amount.into(),
        )?;
    } else {
        // new - old balance is correct
        difference(
            even_prover,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )?;
    }
    // new balance does not overflow
    range_proof(
        even_prover,
        var_bal_new.into(),
        Some(new_bal),
        AMOUNT_BITS.into(),
    )?;
    Ok((
        (r_bal_old, comm_bal_old),
        (r_bal_new, comm_bal_new),
        (r_amount, comm_amount),
    ))
}

/// Enforce that balance has correctly changed. If `has_balance_decreased` is true, then `old_bal - new_bal = amount` else `new_bal - old_bal = amount`
pub fn enforce_balance_change_verifier<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0>>(
    comm_bal_old: Affine<G0>,
    comm_bal_new: Affine<G0>,
    comm_amount: Affine<G0>,
    has_balance_decreased: bool,
    even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
) -> Result<()> {
    let var_bal_old = even_verifier.commit(comm_bal_old);
    let var_bal_new = even_verifier.commit(comm_bal_new);
    let var_amount = even_verifier.commit(comm_amount);

    if has_balance_decreased {
        difference(
            even_verifier,
            var_bal_old.into(),
            var_bal_new.into(),
            var_amount.into(),
        )?;
    } else {
        difference(
            even_verifier,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )?;
    }

    range_proof(even_verifier, var_bal_new.into(), None, AMOUNT_BITS.into())?;

    Ok(())
}

/// Generate responses (Schnorr step 3) for state change just related to amount and balances
pub fn generate_schnorr_responses_for_balance_change<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    t_old_bal: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_new_bal: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_amount: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_leg_amount: PokPedersenCommitmentProtocol<Affine<G0>>,
    prover_challenge: &F0,
) -> (
    PokPedersenCommitment<Affine<G0>>,
    PokPedersenCommitment<Affine<G0>>,
    PokPedersenCommitment<Affine<G0>>,
    PokPedersenCommitment<Affine<G0>>,
) {
    let resp_old_bal = t_old_bal.gen_proof(prover_challenge);
    let resp_new_bal = t_new_bal.gen_proof(prover_challenge);
    let resp_amount = t_amount.clone().gen_proof(prover_challenge);
    let resp_leg_amount = t_leg_amount.clone().gen_proof(prover_challenge);
    (resp_old_bal, resp_new_bal, resp_amount, resp_leg_amount)
}

#[cfg(feature = "std")]
pub fn prove<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_prover: Prover<MerlinTranscript, Affine<G0>>,
    odd_prover: Prover<MerlinTranscript, Affine<G1>>,
    tree_params: &SelRerandParameters<G0, G1>,
) -> Result<(R1CSProof<Affine<G0>>, R1CSProof<Affine<G1>>)> {
    let mut rng = rand::thread_rng();
    prove_with_rng(even_prover, odd_prover, tree_params, &mut rng)
}

#[allow(unused_variables)]
pub fn prove_with_rng<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    R: RngCore + CryptoRng,
>(
    even_prover: Prover<MerlinTranscript, Affine<G0>>,
    odd_prover: Prover<MerlinTranscript, Affine<G1>>,
    tree_params: &SelRerandParameters<G0, G1>,
    rng: &mut R,
) -> Result<(R1CSProof<Affine<G0>>, R1CSProof<Affine<G1>>)> {
    #[cfg(feature = "parallel")]
    let (even_proof, odd_proof) = rayon::join(
        || even_prover.prove(&tree_params.even_parameters.bp_gens),
        || odd_prover.prove(&tree_params.odd_parameters.bp_gens),
    );

    #[cfg(not(feature = "parallel"))]
    let (even_proof, odd_proof) = (
        even_prover.prove_with_rng(&tree_params.even_parameters.bp_gens, rng),
        odd_prover.prove_with_rng(&tree_params.odd_parameters.bp_gens, rng),
    );

    let (even_proof, odd_proof) = (even_proof?, odd_proof?);
    Ok((even_proof, odd_proof))
}

#[cfg(feature = "std")]
pub fn verify<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
>(
    even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
    odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
    even_proof: &R1CSProof<Affine<G0>>,
    odd_proof: &R1CSProof<Affine<G1>>,
    tree_params: &SelRerandParameters<G0, G1>,
) -> Result<()> {
    let mut rng = rand::thread_rng();
    verify_with_rng(
        even_verifier,
        odd_verifier,
        even_proof,
        odd_proof,
        tree_params,
        &mut rng,
    )
}

#[allow(unused_variables)]
pub fn verify_with_rng<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    R: RngCore + CryptoRng,
>(
    even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
    odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
    even_proof: &R1CSProof<Affine<G0>>,
    odd_proof: &R1CSProof<Affine<G1>>,
    tree_params: &SelRerandParameters<G0, G1>,
    rng: &mut R,
) -> Result<()> {
    #[cfg(feature = "parallel")]
    let (even_res, odd_res) = rayon::join(
        || {
            even_verifier.verify(
                even_proof,
                &tree_params.even_parameters.pc_gens,
                &tree_params.even_parameters.bp_gens,
            )
        },
        || {
            odd_verifier.verify(
                odd_proof,
                &tree_params.odd_parameters.pc_gens,
                &tree_params.odd_parameters.bp_gens,
            )
        },
    );

    #[cfg(not(feature = "parallel"))]
    let (even_res, odd_res) = (
        even_verifier.verify_with_rng(
            even_proof,
            &tree_params.even_parameters.pc_gens,
            &tree_params.even_parameters.bp_gens,
            rng,
        ),
        odd_verifier.verify_with_rng(
            odd_proof,
            &tree_params.odd_parameters.pc_gens,
            &tree_params.odd_parameters.bp_gens,
            rng,
        ),
    );

    even_res?;
    odd_res?;

    Ok(())
}


/// Generate commitment to randomness (Schnorr step 1) for state change excluding changes related to amount and balances
pub fn generate_schnorr_t_values_for_common_state_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Copy,
>(
    rng: &mut R,
    asset_id: AssetId,
    leg_enc: &LegEncryption<Affine<G0>>,
    old_account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    is_sender: bool,
    sk_blinding: F0,
    old_balance_blinding: F0,
    new_balance_blinding: F0,
    new_counter_blinding: F0,
    initial_rho_blinding: F0,
    old_rho_blinding: F0,
    new_rho_blinding: F0,
    old_randomness_blinding: F0,
    new_randomness_blinding: F0,
    asset_id_blinding: F0,
    r_pk: F0, // r_1 or r_2 depending on sender or receiver
    r_4: F0,
    prover: &mut Prover<MerlinTranscript, Affine<G0>>,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
) -> Result<(
    Affine<G0>,
    Affine<G0>,
    F0,
    SchnorrCommitment<Affine<G0>>,
    SchnorrCommitment<Affine<G0>>,
    PokDiscreteLogProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
    SchnorrCommitment<Affine<G0>>,
)> {
    let nullifier = old_account.nullifier(account_comm_key);

    let comm_bp_blinding = F0::rand(rng);
    let (comm_bp_randomness_relations, vars) = prover.commit_vec(
        &[
            old_account.rho,
            old_account.current_rho,
            updated_account.current_rho,
            old_account.randomness,
            updated_account.randomness,
        ],
        comm_bp_blinding,
        bp_gens,
    );

    enforce_constraints_for_randomness_relations(prover, vars);

    // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
    let t_r_leaf = SchnorrCommitment::new(
        &account_comm_key.as_gens_with_blinding(pc_gens.B_blinding),
        vec![
            sk_blinding,
            old_balance_blinding,
            new_counter_blinding,
            asset_id_blinding,
            initial_rho_blinding,
            old_rho_blinding,
            old_randomness_blinding,
            F0::rand(rng),
        ],
    );

    // Schnorr commitment for proving correctness of new account state which will become new leaf
    let t_acc_new = SchnorrCommitment::new(
        &account_comm_key.as_gens(),
        vec![
            sk_blinding,
            new_balance_blinding,
            new_counter_blinding,
            asset_id_blinding,
            initial_rho_blinding,
            new_rho_blinding,
            new_randomness_blinding,
        ],
    );

    let pk_gen = account_comm_key.sk_gen();
    let null_gen = account_comm_key.current_rho_gen();

    // Schnorr commitment for proving correctness of nullifier
    let t_null = PokDiscreteLogProtocol::init(
        old_account.current_rho,
        old_rho_blinding,
        &null_gen,
    );

    // Schnorr commitment for proving correctness of asset-id used in leg
    let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
        r_4,
        F0::rand(rng),
        &enc_key_gen,
        F0::from(asset_id),
        asset_id_blinding,
        &enc_gen,
    );

    // Schnorr commitment for proving knowledge of secret key of the corresponding party's public key used in leg
    let t_leg_pk = PokPedersenCommitmentProtocol::init(
        r_pk,
        F0::rand(rng),
        &enc_key_gen,
        old_account.sk,
        sk_blinding,
        &pk_gen,
    );

    // Schnorr commitment for proving correctness of Bulletproof commitment
    let t_bp_randomness_relations = SchnorrCommitment::new(
        &bp_gens_vec_for_randomness_relations(pc_gens, bp_gens),
        vec![
            F0::rand(rng),
            initial_rho_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_randomness_blinding,
            new_randomness_blinding,
        ],
    );

    let mut transcript = prover.transcript();

    // Add challenge contribution of each of the above commitments to the transcript
    t_r_leaf.challenge_contribution(&mut transcript)?;
    t_acc_new.challenge_contribution(&mut transcript)?;
    t_null.challenge_contribution(
        &null_gen,
        &nullifier,
        &mut transcript,
    )?;
    t_leg_asset_id.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        &leg_enc.ct_asset_id,
        &mut transcript,
    )?;
    t_leg_pk.challenge_contribution(
        &enc_key_gen,
        &pk_gen,
        if is_sender {
            &leg_enc.ct_s
        } else {
            &leg_enc.ct_r
        },
        &mut transcript,
    )?;
    t_bp_randomness_relations.challenge_contribution(&mut transcript)?;
    comm_bp_randomness_relations.serialize_compressed(&mut transcript)?;

    Ok((
        nullifier,
        comm_bp_randomness_relations,
        comm_bp_blinding,
        t_r_leaf,
        t_acc_new,
        t_null,
        t_leg_asset_id,
        t_leg_pk,
        t_bp_randomness_relations,
    ))
}

/// Generate commitment to randomness (Schnorr step 1) for state change just related to amount and balances
pub fn generate_schnorr_t_values_for_balance_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    amount: Balance,
    ct_amount: &Affine<G0>,
    account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    old_balance_blinding: F0,
    new_balance_blinding: F0,
    amount_blinding: F0,
    r_bal_old: F0,
    r_bal_new: F0,
    r_amount: F0,
    r_3: F0,
    comm_bal_old: &Affine<G0>,
    comm_bal_new: &Affine<G0>,
    comm_amount: &Affine<G0>,
    pc_gens: &PedersenGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
    mut prover_transcript: &mut MerlinTranscript,
) -> Result<(
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
)> {
    // The following 3 are for Bulletproof commitment and will likely be combined in one
    // Schnorr commitment for proving knowledge of old account balance
    let t_old_bal = PokPedersenCommitmentProtocol::init(
        account.balance.into(),
        old_balance_blinding,
        &pc_gens.B,
        r_bal_old,
        F0::rand(rng),
        &pc_gens.B_blinding,
    );

    // Schnorr commitment for proving knowledge of new account balance
    let t_new_bal = PokPedersenCommitmentProtocol::init(
        updated_account.balance.into(),
        new_balance_blinding,
        &pc_gens.B,
        r_bal_new,
        F0::rand(rng),
        &pc_gens.B_blinding,
    );

    // Schnorr commitment for proving knowledge of amount (used in Bulletproof)
    let t_amount = PokPedersenCommitmentProtocol::init(
        F0::from(amount),
        amount_blinding,
        &pc_gens.B,
        r_amount,
        F0::rand(rng),
        &pc_gens.B_blinding,
    );

    // Schnorr commitment for proving knowledge of amount used in the leg
    let t_leg_amount = PokPedersenCommitmentProtocol::init(
        r_3,
        F0::rand(rng),
        &enc_key_gen,
        F0::from(amount),
        amount_blinding,
        &enc_gen,
    );

    // Add challenge contribution of each of the above commitments to the transcript
    t_old_bal.challenge_contribution(
        &pc_gens.B,
        &pc_gens.B_blinding,
        comm_bal_old,
        &mut prover_transcript,
    )?;
    t_new_bal.challenge_contribution(
        &pc_gens.B,
        &pc_gens.B_blinding,
        comm_bal_new,
        &mut prover_transcript,
    )?;
    t_amount.challenge_contribution(
        &pc_gens.B,
        &pc_gens.B_blinding,
        comm_amount,
        &mut prover_transcript,
    )?;
    t_leg_amount.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        ct_amount,
        &mut prover_transcript,
    )?;
    Ok((t_old_bal, t_new_bal, t_amount, t_leg_amount))
}

/// Generate responses (Schnorr step 3) for state change excluding changes related to amount and balances
pub fn generate_schnorr_responses_for_common_state_change<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    leaf_rerandomization: F0,
    comm_bp_blinding: F0,
    t_r_leaf: &SchnorrCommitment<Affine<G0>>,
    t_acc_new: &SchnorrCommitment<Affine<G0>>,
    t_null: PokDiscreteLogProtocol<Affine<G0>>,
    t_leg_asset_id: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_leg_pk: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_bp_randomness_relations: &SchnorrCommitment<Affine<G0>>,
    prover_challenge: &F0,
) -> Result<(
    SchnorrResponse<Affine<G0>>,
    SchnorrResponse<Affine<G0>>,
    PokDiscreteLog<Affine<G0>>,
    PokPedersenCommitment<Affine<G0>>,
    PokPedersenCommitment<Affine<G0>>,
    SchnorrResponse<Affine<G0>>,
)> {
    // TODO: Eliminate duplicate responses
    let resp_leaf = t_r_leaf.response(
        &[
            account.sk,
            account.balance.into(),
            account.counter.into(),
            account.asset_id.into(),
            account.rho,
            account.current_rho,
            account.randomness,
            leaf_rerandomization,
        ],
        prover_challenge,
    )?;
    let resp_acc_new = t_acc_new.response(
        &[
            updated_account.sk,
            updated_account.balance.into(),
            updated_account.counter.into(),
            updated_account.asset_id.into(),
            updated_account.rho,
            updated_account.current_rho,
            updated_account.randomness,
        ],
        prover_challenge,
    )?;
    let resp_null = t_null.gen_proof(prover_challenge);
    let resp_leg_asset_id = t_leg_asset_id.clone().gen_proof(prover_challenge);
    let resp_leg_pk = t_leg_pk.clone().gen_proof(prover_challenge);
    let resp_bp = t_bp_randomness_relations.response(
        &[
            comm_bp_blinding,
            updated_account.rho,
            account.current_rho,
            updated_account.current_rho,
            account.randomness,
            updated_account.randomness,
        ],
        &prover_challenge,
    )?;
    Ok((
        resp_leaf,
        resp_acc_new,
        resp_null,
        resp_leg_asset_id,
        resp_leg_pk,
        resp_bp,
    ))
}

pub fn take_challenge_contrib_of_schnorr_t_values_for_common_state_change<
    G0: SWCurveConfig + Copy,
>(
    leg_enc: &LegEncryption<Affine<G0>>,
    is_sender: bool,
    nullifier: &Affine<G0>,
    comm_bp_randomness_relations: Affine<G0>,
    t_r_leaf: &Affine<G0>,
    t_acc_new: &Affine<G0>,
    t_randomness_relations: &Affine<G0>,
    resp_null: &PokDiscreteLog<Affine<G0>>,
    resp_leg_asset_id: &PokPedersenCommitment<Affine<G0>>,
    resp_leg_pk: &PokPedersenCommitment<Affine<G0>>,
    verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
) -> Result<()> {

    let vars = verifier.commit_vec(5, comm_bp_randomness_relations);
    enforce_constraints_for_randomness_relations(verifier, vars);

    let mut transcript = verifier.transcript();


    t_r_leaf.serialize_compressed(&mut transcript)?;
    t_acc_new.serialize_compressed(&mut transcript)?;
    resp_null.challenge_contribution(
        &account_comm_key.current_rho_gen(),
        nullifier,
        &mut transcript,
    )?;
    resp_leg_asset_id.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        &leg_enc.ct_asset_id,
        &mut transcript,
    )?;
    resp_leg_pk.challenge_contribution(
        &enc_key_gen,
        &account_comm_key.sk_gen(),
        if is_sender {
            &leg_enc.ct_s
        } else {
            &leg_enc.ct_r
        },
        &mut transcript,
    )?;

    t_randomness_relations.serialize_compressed(&mut transcript)?;
    comm_bp_randomness_relations.serialize_compressed(&mut transcript)?;

    Ok(())
}

pub fn take_challenge_contrib_of_schnorr_t_values_for_balance_change<G0: SWCurveConfig + Copy>(
    ct_amount: &Affine<G0>,
    comm_bal_old: &Affine<G0>,
    comm_bal_new: &Affine<G0>,
    comm_amount: &Affine<G0>,
    resp_old_bal: &PokPedersenCommitment<Affine<G0>>,
    resp_new_bal: &PokPedersenCommitment<Affine<G0>>,
    resp_amount: &PokPedersenCommitment<Affine<G0>>,
    resp_leg_amount: &PokPedersenCommitment<Affine<G0>>,
    pc_gens: &PedersenGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
    mut verifier_transcript: &mut MerlinTranscript,
) -> Result<()> {
    resp_old_bal.challenge_contribution(
        &pc_gens.B,
        &pc_gens.B_blinding,
        comm_bal_old,
        &mut verifier_transcript,
    )?;
    resp_new_bal.challenge_contribution(
        &pc_gens.B,
        &pc_gens.B_blinding,
        &comm_bal_new,
        &mut verifier_transcript,
    )?;
    resp_amount.challenge_contribution(
        &pc_gens.B,
        &pc_gens.B_blinding,
        &comm_amount,
        &mut verifier_transcript,
    )?;
    resp_leg_amount.challenge_contribution(
        &enc_key_gen,
        &enc_gen,
        ct_amount,
        &mut verifier_transcript,
    )?;
    Ok(())
}

pub fn verify_schnorr_for_common_state_change<G0: SWCurveConfig + Copy>(
    leg_enc: &LegEncryption<Affine<G0>>,
    is_sender: bool,
    nullifier: &Affine<G0>,
    re_randomized_leaf: &Affine<G0>,
    updated_account_commitment: &Affine<G0>,
    comm_bp: &Affine<G0>,
    t_r_leaf: &Affine<G0>,
    t_acc_new: &Affine<G0>,
    t_bp: &Affine<G0>,
    resp_leaf: &SchnorrResponse<Affine<G0>>,
    resp_acc_new: &SchnorrResponse<Affine<G0>>,
    resp_null: &PokDiscreteLog<Affine<G0>>,
    resp_leg_asset_id: &PokPedersenCommitment<Affine<G0>>,
    resp_leg_pk: &PokPedersenCommitment<Affine<G0>>,
    resp_bp: &SchnorrResponse<Affine<G0>>,
    verifier_challenge: &G0::ScalarField,
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
) -> Result<()> {
    resp_leaf.is_valid(
        &account_comm_key.as_gens_with_blinding(pc_gens.B_blinding),
        re_randomized_leaf,
        t_r_leaf,
        verifier_challenge,
    )?;
    resp_acc_new.is_valid(
        &account_comm_key.as_gens(),
        updated_account_commitment,
        t_acc_new,
        verifier_challenge,
    )?;
    if !resp_null.verify(
        nullifier,
        &account_comm_key.current_rho_gen(),
        verifier_challenge,
    ) {
        return Err(Error::ProofVerificationError(
            "Nullifier verification failed".to_string(),
        ));
    }
    if !resp_leg_asset_id.verify(
        &leg_enc.ct_asset_id,
        &enc_key_gen,
        &enc_gen,
        verifier_challenge,
    ) {
        return Err(Error::ProofVerificationError(
            "Leg asset ID verification failed".to_string(),
        ));
    }
    if !resp_leg_pk.verify(
        if is_sender {
            &leg_enc.ct_s
        } else {
            &leg_enc.ct_r
        },
        &enc_key_gen,
        &account_comm_key.sk_gen(),
        verifier_challenge,
    ) {
        return Err(Error::ProofVerificationError(
            "Leg public key verification failed".to_string(),
        ));
    }
    resp_bp.is_valid(
        &bp_gens_vec_for_randomness_relations(pc_gens, bp_gens),
        comm_bp,
        t_bp,
        verifier_challenge,
    )?;

    // Sk asset id, initial rho in leaf match the ones in updated account commitment
    if resp_leaf.0[0] != resp_acc_new.0[0] {
        return Err(Error::ProofVerificationError(
            "Secret key in leaf does not match the one in updated account commitment".to_string(),
        ));
    }
    if resp_leaf.0[3] != resp_acc_new.0[3] {
        return Err(Error::ProofVerificationError(
            "Asset ID in leaf does not match the one in updated account commitment".to_string(),
        ));
    }

    if resp_leaf.0[4] != resp_acc_new.0[4] {
        return Err(Error::ProofVerificationError(
            "Initial rho in leaf does not match the one in updated account commitment".to_string(),
        ));
    }

    // rho matches the one in nullifier
    if resp_leaf.0[5] != resp_null.response {
        return Err(Error::ProofVerificationError(
            "Rho in leaf does not match the one in nullifier".to_string(),
        ));
    }

    // Asset id in leg is same as in account commitment
    if resp_leg_asset_id.response2 != resp_acc_new.0[3] {
        return Err(Error::ProofVerificationError(
            "Asset ID in leg does not match the one in account commitment".to_string(),
        ));
    }

    // sk in account comm matches the one in pk
    if resp_leg_pk.response2 != resp_leaf.0[0] {
        return Err(Error::ProofVerificationError(
            "Secret key in leg public key does not match the one in leaf".to_string(),
        ));
    }

    if resp_bp.0[1] != resp_leaf.0[4] {
        return Err(Error::ProofVerificationError(
            "Initial rho mismatch between the leaf and the one in BP commitment".to_string(),
        ));
    }

    if resp_bp.0[2] != resp_null.response {
        return Err(Error::ProofVerificationError(
            "Old rho mismatch between the nullifier and the one in BP commitment".to_string(),
        ));
    }

    if resp_bp.0[3] != resp_acc_new.0[5] {
        return Err(Error::ProofVerificationError(
            "New rho mismatch between the new account commitment and the one in BP commitment".to_string(),
        ));
    }

    if resp_bp.0[4] != resp_leaf.0[6] {
        return Err(Error::ProofVerificationError(
            "Old randomness mismatch between the leaf and the one in BP commitment".to_string(),
        ));
    }

    if resp_bp.0[5] != resp_acc_new.0[6] {
        return Err(Error::ProofVerificationError(
            "New randomness mismatch between the account commitment and the one in BP commitment".to_string(),
        ));
    }

    Ok(())
}

pub fn verify_schnorr_for_balance_change<G0: SWCurveConfig + Copy>(
    leg_enc: &LegEncryption<Affine<G0>>,
    comm_bal_old: &Affine<G0>,
    comm_bal_new: &Affine<G0>,
    comm_amount: &Affine<G0>,
    resp_old_bal: &PokPedersenCommitment<Affine<G0>>,
    resp_new_bal: &PokPedersenCommitment<Affine<G0>>,
    resp_amount: &PokPedersenCommitment<Affine<G0>>,
    resp_leg_amount: &PokPedersenCommitment<Affine<G0>>,
    verifier_challenge: &G0::ScalarField,
    pc_gens: &PedersenGens<Affine<G0>>,
    enc_key_gen: Affine<G0>,
    enc_gen: Affine<G0>,
)   -> Result<()> {
    if !resp_old_bal.verify(
        comm_bal_old,
        &pc_gens.B,
        &pc_gens.B_blinding,
        verifier_challenge,
    ) {
        return Err(Error::ProofVerificationError(
            "Old balance verification failed".to_string(),
        ));
    }
    if !resp_new_bal.verify(
        comm_bal_new,
        &pc_gens.B,
        &pc_gens.B_blinding,
        verifier_challenge,
    ) {
        return Err(Error::ProofVerificationError(
            "New balance verification failed".to_string(),
        ));
    }
    if !resp_amount.verify(
        comm_amount,
        &pc_gens.B,
        &pc_gens.B_blinding,
        verifier_challenge,
    ) {
        return Err(Error::ProofVerificationError(
            "Amount verification failed".to_string(),
        ));
    }

    if !resp_leg_amount.verify(
        &leg_enc.ct_amount,
        &enc_key_gen,
        &enc_gen,
        verifier_challenge,
    ) {
        return Err(Error::ProofVerificationError(
            "Leg amount verification failed".to_string(),
        ));
    }

    Ok(())
}

/// Enforces the constraints for relations between initial rho, current rho, old and new randomness
/// `committed_variables` are variables for committed values `[rho, rho^i, rho^{i+1}, s^j, s^{2*j}]`
pub fn enforce_constraints_for_randomness_relations<F: Field, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    mut committed_variables: Vec<Variable<F>>,
) {
    let var_rho = committed_variables.remove(0);
    let var_rho_i = committed_variables.remove(0);
    let var_rho_i_plus_1 = committed_variables.remove(0);
    let var_s_i = committed_variables.remove(0);
    let var_s_i_plus_1 = committed_variables.remove(0);
    let (_, _, var_rho_i_plus_1_) = cs.multiply(var_rho.into(), var_rho_i.into());
    let (_, _, var_s_i_plus_1_) = cs.multiply(var_s_i.into(), var_s_i.into());
    cs.constrain(var_rho_i_plus_1 - var_rho_i_plus_1_);
    cs.constrain(var_s_i_plus_1 - var_s_i_plus_1_);
}

fn bp_gens_vec_for_randomness_relations<G0: SWCurveConfig + Copy>(
    pc_gens: &PedersenGens<Affine<G0>>,
    bp_gens: &BulletproofGens<Affine<G0>>,
) -> [Affine<G0>; 6] {
    let mut gens = bp_gens_for_vec_commitment(5, bp_gens);
    [
        pc_gens.B_blinding,
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
        gens.next().unwrap(),
    ]
}

/// Generators used by Bulletproofs to construct vector commitment, i.e. when `commit_vec` is called. The resulting commitment
/// has the first generator as the blinding generator and then these generators follow.
pub fn bp_gens_for_vec_commitment<G: AffineRepr>(size: usize, bp_gens: &BulletproofGens<G>) -> Copied<impl Iterator<Item=&G>> {
    bp_gens.share(0).G(size).copied()
}