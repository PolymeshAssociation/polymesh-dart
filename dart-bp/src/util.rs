use crate::account_new::AccountState;
use crate::leg::LegEncryption;
use crate::{AMOUNT_BITS, AssetId, Balance};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use bulletproofs::PedersenGens;
use bulletproofs::r1cs::{ConstraintSystem, Prover, Variable, Verifier};
use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::range_proof::{difference, range_proof};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand::RngCore;
use schnorr_pok::discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use std::borrow::BorrowMut;

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
    let mut even_prover: Prover<_, Affine<G0>> =
        Prover::new(&tree_parameters.even_parameters.pc_gens, even_transcript);

    let odd_transcript = MerlinTranscript::new(odd_label);
    let mut odd_prover: Prover<_, Affine<G1>> =
        Prover::new(&tree_parameters.odd_parameters.pc_gens, odd_transcript);

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
    tree_root: &CurveTree<L, 1, G0, G1>,
    tree_parameters: &SelRerandParameters<G0, G1>,
) -> (
    Verifier<MerlinTranscript, Affine<G0>>,
    Verifier<MerlinTranscript, Affine<G1>>,
) {
    let even_transcript = MerlinTranscript::new(even_label);
    let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
    let odd_transcript = MerlinTranscript::new(odd_label);
    let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

    tree_root.add_root_to_randomized_path(&mut re_randomized_path);

    // Enforce constraints for odd level
    re_randomized_path.odd_verifier_gadget(&mut odd_verifier, &tree_parameters, &tree_root);

    // Enforce constraints for even level
    re_randomized_path.even_verifier_gadget(&mut even_verifier, &tree_parameters, &tree_root);

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
) -> (
    (F0, Affine<G0>),
    (F0, Affine<G0>),
    (F0, Affine<G0>),
) {
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
        )
        .unwrap();
    } else {
        // new - odl balance is correct
        difference(
            even_prover,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )
        .unwrap();
    }
    // new balance does not overflow
    range_proof(
        even_prover,
        var_bal_new.into(),
        Some(new_bal),
        AMOUNT_BITS.into(),
    )
    .unwrap();
    (
        (r_bal_old, comm_bal_old),
        (r_bal_new, comm_bal_new),
        (r_amount, comm_amount),
    )
}

/// Enforce that balance has correctly changed. If `has_balance_decreased` is true, then `old_bal - new_bal = amount` else `new_bal - old_bal = amount`
pub fn enforce_balance_change_verifier<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0>>(
    comm_bal_old: Affine<G0>,
    comm_bal_new: Affine<G0>,
    comm_amount: Affine<G0>,
    has_balance_decreased: bool,
    even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
) {
    let var_bal_old = even_verifier.commit(comm_bal_old);
    let var_bal_new = even_verifier.commit(comm_bal_new);
    let var_amount = even_verifier.commit(comm_amount);

    if has_balance_decreased {
        difference(
            even_verifier,
            var_bal_old.into(),
            var_bal_new.into(),
            var_amount.into(),
        )
        .unwrap();
    } else {
        difference(
            even_verifier,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )
        .unwrap();
    }

    range_proof(even_verifier, var_bal_new.into(), None, AMOUNT_BITS.into()).unwrap();
}

/// Generate commitment to randomness (Schnorr step 1) for state change excluding changes related to amount and balances
pub fn generate_schnorr_t_values_for_common_state_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    asset_id: AssetId,
    leg_enc: &LegEncryption<Affine<G0>>,
    account: &AccountState<Affine<G0>>,
    sk_e: F0,
    is_sender: bool,
    sk_blinding: F0,
    sk_e_blinding: F0,
    old_balance_blinding: F0,
    new_balance_blinding: F0,
    new_counter_blinding: F0,
    old_rho_blinding: F0,
    asset_id_blinding: F0,
    account_comm_key: &[Affine<G0>],
    pc_gens: &PedersenGens<Affine<G0>>,
    g: Affine<G0>,
    h: Affine<G0>,
    mut prover_transcript: &mut MerlinTranscript,
) -> (
    Affine<G0>,
    SchnorrCommitment<Affine<G0>>,
    SchnorrCommitment<Affine<G0>>,
    PokDiscreteLogProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
) {
    let nullifier = account.nullifier(g);

    // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
    let t_r_leaf = SchnorrCommitment::new(
        &[
            account_comm_key[0],
            account_comm_key[1],
            account_comm_key[2],
            account_comm_key[3],
            account_comm_key[4],
            account_comm_key[5],
            pc_gens.B_blinding,
        ],
        vec![
            sk_blinding,
            old_balance_blinding,
            new_counter_blinding,
            asset_id_blinding,
            old_rho_blinding,
            F0::rand(rng),
            F0::rand(rng),
        ],
    );

    // Schnorr commitment for proving correctness of new account state which will become new leaf
    let t_acc_new = SchnorrCommitment::new(
        &[
            account_comm_key[0],
            account_comm_key[1],
            account_comm_key[2],
            account_comm_key[3],
            account_comm_key[4],
            account_comm_key[5],
        ],
        vec![
            sk_blinding,
            new_balance_blinding,
            new_counter_blinding,
            asset_id_blinding,
            F0::rand(rng),
            F0::rand(rng),
        ],
    );

    // Schnorr commitment for proving correctness of nullifier
    let t_null = PokDiscreteLogProtocol::init(account.rho, old_rho_blinding, &g);

    // Schnorr commitment for proving correctness of asset-id used in leg
    let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
        sk_e,
        sk_e_blinding,
        &leg_enc.ct_asset_id.eph_pk,
        F0::from(asset_id),
        asset_id_blinding,
        &h,
    );

    // Schnorr commitment for proving knowledge of secret key of the corresponding party's public key used in leg
    let t_leg_pk = PokPedersenCommitmentProtocol::init(
        sk_e,
        sk_e_blinding,
        &(if is_sender {
            leg_enc.ct_s.eph_pk
        } else {
            leg_enc.ct_r.eph_pk
        }),
        account.sk,
        sk_blinding,
        &g,
    );

    // Add challenge contribution of each of the above commitments to the transcript
    t_r_leaf
        .challenge_contribution(&mut prover_transcript)
        .unwrap();
    t_acc_new
        .challenge_contribution(&mut prover_transcript)
        .unwrap();
    t_null
        .challenge_contribution(&g, &nullifier, &mut prover_transcript)
        .unwrap();
    t_leg_asset_id
        .challenge_contribution(
            &leg_enc.ct_asset_id.eph_pk,
            &h,
            &leg_enc.ct_asset_id.encrypted,
            &mut prover_transcript,
        )
        .unwrap();
    t_leg_pk
        .challenge_contribution(
            if is_sender { &leg_enc.ct_s.eph_pk } else { &leg_enc.ct_r.eph_pk },
            &g,
            if is_sender { &leg_enc.ct_s.encrypted } else { &leg_enc.ct_r.encrypted },
            &mut prover_transcript,
        )
        .unwrap();

    (
        nullifier,
        t_r_leaf,
        t_acc_new,
        t_null,
        t_leg_asset_id,
        t_leg_pk,
    )
}

/// Generate commitment to randomness (Schnorr step 1) for state change just related to amount and balances
pub fn generate_schnorr_t_values_for_balance_change<
    R: RngCore,
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0>,
>(
    rng: &mut R,
    amount: Balance,
    leg_enc: &LegEncryption<Affine<G0>>,
    account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    sk_e: F0,
    sk_e_blinding: F0,
    old_balance_blinding: F0,
    new_balance_blinding: F0,
    amount_blinding: F0,
    r_bal_old: F0,
    r_bal_new: F0,
    r_amount: F0,
    comm_bal_old: &Affine<G0>,
    comm_bal_new: &Affine<G0>,
    comm_amount: &Affine<G0>,
    pc_gens: &PedersenGens<Affine<G0>>,
    h: Affine<G0>,
    mut prover_transcript: &mut MerlinTranscript,
) -> (
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
    PokPedersenCommitmentProtocol<Affine<G0>>,
) {

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
        sk_e,
        sk_e_blinding,
        &leg_enc.ct_amount.eph_pk,
        F0::from(amount),
        amount_blinding,
        &h,
    );

    // Add challenge contribution of each of the above commitments to the transcript
    t_old_bal
        .challenge_contribution(
            &pc_gens.B,
            &pc_gens.B_blinding,
            comm_bal_old,
            &mut prover_transcript,
        )
        .unwrap();
    t_new_bal
        .challenge_contribution(
            &pc_gens.B,
            &pc_gens.B_blinding,
            comm_bal_new,
            &mut prover_transcript,
        )
        .unwrap();
    t_amount
        .challenge_contribution(
            &pc_gens.B,
            &pc_gens.B_blinding,
            comm_amount,
            &mut prover_transcript,
        )
        .unwrap();
    t_leg_amount
        .challenge_contribution(
            &leg_enc.ct_amount.eph_pk,
            &h,
            &leg_enc.ct_amount.encrypted,
            &mut prover_transcript,
        )
        .unwrap();
    (t_old_bal, t_new_bal, t_amount, t_leg_amount)
}

/// Generate responses (Schnorr step 3) for state change excluding changes related to amount and balances
pub fn generate_schnorr_responses_for_common_state_change<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0>>(
    account: &AccountState<Affine<G0>>,
    updated_account: &AccountState<Affine<G0>>,
    leaf_rerandomization: F0,
    t_r_leaf: &SchnorrCommitment<Affine<G0>>,
    t_acc_new: &SchnorrCommitment<Affine<G0>>,
    t_null: PokDiscreteLogProtocol<Affine<G0>>,
    t_leg_asset_id: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_leg_pk: PokPedersenCommitmentProtocol<Affine<G0>>,
    prover_challenge: &F0,
) -> (SchnorrResponse<Affine<G0>>, SchnorrResponse<Affine<G0>>, PokDiscreteLog<Affine<G0>>, PokPedersenCommitment<Affine<G0>>, PokPedersenCommitment<Affine<G0>>) {
    // TODO: Eliminate duplicate responses
    let resp_leaf = t_r_leaf
        .response(
            &[
                account.sk,
                account.balance.into(),
                account.counter.into(),
                account.asset_id.into(),
                account.rho,
                account.randomness,
                leaf_rerandomization,
            ],
            prover_challenge,
        )
        .unwrap();
    let resp_acc_new = t_acc_new
        .response(
            &[
                updated_account.sk,
                updated_account.balance.into(),
                updated_account.counter.into(),
                updated_account.asset_id.into(),
                updated_account.rho,
                updated_account.randomness,
            ],
            prover_challenge,
        )
        .unwrap();
    let resp_null = t_null.gen_proof(prover_challenge);
    let resp_leg_asset_id = t_leg_asset_id.clone().gen_proof(prover_challenge);
    let resp_leg_pk = t_leg_pk.clone().gen_proof(prover_challenge);
    (resp_leaf, resp_acc_new, resp_null, resp_leg_asset_id, resp_leg_pk)
}

/// Generate responses (Schnorr step 3) for state change just related to amount and balances
pub fn generate_schnorr_responses_for_balance_change<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0>>(
    t_old_bal: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_new_bal: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_amount: PokPedersenCommitmentProtocol<Affine<G0>>,
    t_leg_amount: PokPedersenCommitmentProtocol<Affine<G0>>,
    prover_challenge: &F0,
) -> (PokPedersenCommitment<Affine<G0>>, PokPedersenCommitment<Affine<G0>>, PokPedersenCommitment<Affine<G0>>, PokPedersenCommitment<Affine<G0>>) {
    let resp_old_bal = t_old_bal.gen_proof(prover_challenge);
    let resp_new_bal = t_new_bal.gen_proof(prover_challenge);
    let resp_amount = t_amount.clone().gen_proof(prover_challenge);
    let resp_leg_amount = t_leg_amount.clone().gen_proof(prover_challenge);
    (resp_old_bal, resp_new_bal, resp_amount, resp_leg_amount)
}
