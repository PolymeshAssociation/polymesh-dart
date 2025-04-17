use crate::leg::{Leg, LegEncryption, LegEncryptionRandomness, SETTLE_TXN_EVEN_LABEL, SETTLE_TXN_ODD_LABEL};
use crate::{AMOUNT_BITS, AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID, PendingTxnCounter};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use bulletproofs::r1cs::{ConstraintSystem, R1CSError, R1CSProof};
use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters, SelectAndRerandomizePath};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::range_proof::{difference, range_proof};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand::RngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLog, PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Neg;
use crate::util::{initialize_curve_tree_prover, initialize_curve_tree_verifier};

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountState<G: AffineRepr> {
    pub sk: G::ScalarField,
    pub balance: Balance,
    pub counter: PendingTxnCounter,
    pub asset_id: AssetId,
    pub rho: G::ScalarField,
    pub randomness: G::ScalarField,
    // TODO: Add version
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountStateCommitment<G: AffineRepr>(pub G);

// TODO: Convert asserts to errors

impl<G: AffineRepr> AccountState<G> {
    pub fn new<R: RngCore>(rng: &mut R, sk: G::ScalarField, asset_id: AssetId) -> Self {
        assert!(asset_id <= MAX_ASSET_ID);
        let rho = Self::gen_new_rho(rng, &sk);
        let randomness = G::ScalarField::rand(rng);
        Self {
            sk,
            balance: 0,
            counter: 0,
            asset_id,
            rho,
            randomness,
        }
    }

    pub fn commit(&self, comm_key: &[G]) -> AccountStateCommitment<G> {
        assert!(comm_key.len() >= 6);
        let comm = G::Group::msm(
            &comm_key[..6],
            &[
                self.sk,
                G::ScalarField::from(self.balance),
                G::ScalarField::from(self.counter),
                G::ScalarField::from(self.asset_id),
                self.rho,
                self.randomness,
            ],
        )
        .unwrap();
        AccountStateCommitment(comm.into_affine())
    }

    pub fn get_state_for_mint<R: RngCore>(&self, rng: &mut R, amount: u64) -> Self {
        assert!(amount + self.balance <= MAX_AMOUNT);
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.rho = new_state.get_new_rho(rng);
        new_state.randomness = G::ScalarField::rand(rng);
        new_state
    }

    pub fn get_state_for_send<R: RngCore>(&self, rng: &mut R, amount: u64) -> Self {
        assert!(amount <= self.balance);
        let mut new_state = self.clone();
        new_state.balance -= amount;
        new_state.counter += 1;
        new_state.rho = new_state.get_new_rho(rng);
        new_state.randomness = G::ScalarField::rand(rng);
        new_state
    }

    pub fn get_state_for_receive<R: RngCore>(&self, rng: &mut R) -> Self {
        let mut new_state = self.clone();
        new_state.counter += 1;
        new_state.rho = new_state.get_new_rho(rng);
        new_state.randomness = G::ScalarField::rand(rng);
        new_state
    }

    pub fn get_state_for_claiming_received<R: RngCore>(&self, rng: &mut R, amount: u64) -> Self {
        assert!(self.counter > 0);
        assert!(amount + self.balance <= MAX_AMOUNT);
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.counter -= 1;
        new_state.rho = new_state.get_new_rho(rng);
        new_state.randomness = G::ScalarField::rand(rng);
        new_state
    }

    pub fn get_state_for_reversing_send<R: RngCore>(&self, rng: &mut R, amount: u64) -> Self {
        assert!(self.counter > 0);
        assert!(amount + self.balance <= MAX_AMOUNT);
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.counter -= 1;
        new_state.rho = new_state.get_new_rho(rng);
        new_state.randomness = G::ScalarField::rand(rng);
        new_state
    }

    pub fn get_state_for_decreasing_counter<R: RngCore>(
        &self,
        rng: &mut R,
        decrease_counter_by: Option<PendingTxnCounter>,
    ) -> Self {
        let decrease_counter_by = decrease_counter_by.unwrap_or(1);
        assert!(self.counter >= decrease_counter_by);
        let mut new_state = self.clone();
        new_state.counter -= decrease_counter_by;
        new_state.rho = new_state.get_new_rho(rng);
        new_state.randomness = G::ScalarField::rand(rng);
        new_state
    }

    pub fn get_new_rho<R: RngCore>(&self, rng: &mut R) -> G::ScalarField {
        Self::gen_new_rho(rng, &self.sk)
    }

    pub fn nullifier(&self, g: &G) -> G {
        let exp = (self.sk + self.rho).inverse().unwrap();
        (*g * exp).into()
    }

    fn gen_new_rho<R: RngCore>(rng: &mut R, sk: &G::ScalarField) -> G::ScalarField {
        let mut rho = G::ScalarField::rand(rng);
        let minus_sk = sk.neg();
        while minus_sk == rho {
            rho = G::ScalarField::rand(rng);
        }
        rho
    }
}

// In practice, these will be different for different txns
pub const TXN_ODD_LABEL: &[u8; 13] = b"txn-odd-level";
pub const TXN_EVEN_LABEL: &[u8; 14] = b"txn-even-level";
pub const TXN_CHALLENGE_LABEL: &[u8; 13] = b"txn-challenge";
pub const TXN_INSTANCE_LABEL: &[u8; 18] = b"txn-extra-instance";

// TODO: A refactoring idea is to create partial Schnorr proofs for generic state. With each state, we have same variables which
// almost always change and some which always have to be proven equal (unless revelaed).

/// This is the proof for issuer minting asset into account. Report section 5.1.4, called "Increase Asset Supply"
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MintTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    /// This contains the old account state, but re-randomized (as re-randomized leaf)
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    /// This is the commitment to the new account state which will become new leaf
    pub updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    pub nullifier: Affine<G0>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of issuer secret key using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_pk: PokDiscreteLog<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MintTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: RngCore>(
        rng: &mut R,
        issuer_pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
    ) -> (Self, F0) {
        let (mut even_prover, mut odd_prover, re_randomized_path, rerandomization) = initialize_curve_tree_prover(rng, TXN_EVEN_LABEL, TXN_ODD_LABEL, leaf_path, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        issuer_pk.serialize_compressed(&mut extra_instance).unwrap();
        asset_id.serialize_compressed(&mut extra_instance).unwrap();
        increase_bal_by
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();

        even_prover
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&g);

        // We don't need to check if the new balance overflows or not as the chain tracks the total supply
        // (total minted value) and ensures that it is bounded (can be stored in AMOUNT_BITS)

        // Need to prove that:
        // 1. sk, asset-id, counter are same in both old and new account commitment
        // 2. nullifier is correctly formed
        // 3. sk in account commitment is same as in the issuer's public key

        let sk_blinding = F0::rand(rng);
        let counter_blinding = F0::rand(rng);
        let new_balance_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);

        // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
        let t_r_leaf = SchnorrCommitment::new(
            &[
                account_comm_key[0],
                account_comm_key[1],
                account_comm_key[2],
                account_comm_key[4],
                account_comm_key[5],
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![
                sk_blinding,
                new_balance_blinding,
                counter_blinding,
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
                account_comm_key[4],
                account_comm_key[5],
            ],
            vec![
                sk_blinding,
                new_balance_blinding,
                counter_blinding,
                F0::rand(rng),
                F0::rand(rng),
            ],
        );
        // Schnorr commitment for proving correctness of nullifier
        let t_null = PokPedersenCommitmentProtocol::init(
            account.sk,
            sk_blinding,
            &nullifier,
            account.rho,
            old_rho_blinding,
            &nullifier,
        );
        // Schnorr commitment for knowledge of secret key in public key
        let t_pk = PokDiscreteLogProtocol::init(account.sk, sk_blinding, &g);

        let mut prover_transcript = even_prover.transcript();

        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_acc_new
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_null
            .challenge_contribution(&nullifier, &nullifier, &g, &mut prover_transcript)
            .unwrap();
        t_pk.challenge_contribution(&g, &issuer_pk, &mut prover_transcript)
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // TODO: Eliminate duplicate responses
        let resp_leaf = t_r_leaf
            .response(
                &[
                    account.sk,
                    account.balance.into(),
                    account.counter.into(),
                    account.rho,
                    account.randomness,
                    rerandomization,
                ],
                &prover_challenge,
            )
            .unwrap();
        let resp_acc_new = t_acc_new
            .response(
                &[
                    updated_account.sk,
                    updated_account.balance.into(),
                    updated_account.counter.into(),
                    updated_account.rho,
                    updated_account.randomness,
                ],
                &prover_challenge,
            )
            .unwrap();
        let resp_null = t_null.gen_proof(&prover_challenge);
        let resp_pk = t_pk.gen_proof(&prover_challenge);

        let even_proof = even_prover
            .prove(&account_tree_params.even_parameters.bp_gens)
            .unwrap();
        let odd_proof = odd_prover
            .prove(&account_tree_params.odd_parameters.bp_gens)
            .unwrap();
        (
            Self {
                odd_proof,
                even_proof,
                re_randomized_path,
                updated_account_commitment,
                nullifier,
                t_r_leaf: t_r_leaf.t,
                t_acc_new: t_acc_new.t,
                resp_leaf,
                resp_acc_new,
                resp_null,
                resp_pk,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        issuer_pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        account_tree: &CurveTree<L, 1, G0, G1>,
        prover_challenge: F0,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
    ) -> Result<(), R1CSError> {
        let (mut even_verifier, mut odd_verifier) = initialize_curve_tree_verifier(TXN_EVEN_LABEL, TXN_ODD_LABEL, self.re_randomized_path.clone(), account_tree, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        issuer_pk.serialize_compressed(&mut extra_instance).unwrap();
        asset_id.serialize_compressed(&mut extra_instance).unwrap();
        increase_bal_by
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        self.updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();

        even_verifier
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let mut verifier_transcript = even_verifier.transcript();

        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.t_acc_new
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_null
            .challenge_contribution(
                &self.nullifier,
                &self.nullifier,
                &g,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_pk
            .challenge_contribution(&g, &issuer_pk, &mut verifier_transcript)
            .unwrap();

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        let asset_id_comm = (account_comm_key[3] * F0::from(asset_id)).into_affine();

        let y = self.re_randomized_path.re_randomized_leaf - asset_id_comm;
        self.resp_leaf
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[4],
                    account_comm_key[5],
                    account_tree_params.even_parameters.pc_gens.B_blinding,
                ],
                &y.into_affine(),
                &self.t_r_leaf,
                &verifier_challenge,
            )
            .unwrap();

        let y = self.updated_account_commitment.0 - asset_id_comm;
        self.resp_acc_new
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[4],
                    account_comm_key[5],
                ],
                &y.into_affine(),
                &self.t_acc_new,
                &verifier_challenge,
            )
            .unwrap();

        assert!(
            self.resp_null
                .verify(&g, &self.nullifier, &self.nullifier, &verifier_challenge,)
        );
        assert!(self.resp_pk.verify(&issuer_pk, &g, &verifier_challenge));

        // Sk and counter in leaf match the ones in updated account commitment
        assert_eq!(self.resp_leaf.0[0], self.resp_acc_new.0[0]);
        assert_eq!(self.resp_leaf.0[2], self.resp_acc_new.0[2]);
        // Balance in leaf is less than the one in the new account commitment by `increase_bal_by`
        assert_eq!(
            self.resp_leaf.0[1] + (verifier_challenge * F0::from(increase_bal_by)),
            self.resp_acc_new.0[1]
        );

        // Sk and rho match the ones in nullifier
        assert_eq!(self.resp_leaf.0[0], self.resp_null.response1);
        assert_eq!(self.resp_leaf.0[3], self.resp_null.response2);
        // Sk in leaf matches the one in public key
        assert_eq!(self.resp_leaf.0[0], self.resp_pk.response);

        even_verifier.verify(
            &self.even_proof,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
        )?;
        odd_verifier.verify(
            &self.odd_proof,
            &account_tree_params.odd_parameters.pc_gens,
            &account_tree_params.odd_parameters.bp_gens,
        )?;
        Ok(())
    }
}

/// This is the proof for send txn. Report section 5.1.7
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SendTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    /// This is the commitment to the new account state which will become new leaf
    pub updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    pub comm_bal_old: Affine<G0>,
    pub comm_bal_new: Affine<G0>,
    pub comm_amount: Affine<G0>,
    pub nullifier: Affine<G0>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of old balance using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to old balance is created for using with Bulletproofs
    pub resp_old_bal: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of old balance using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to new balance is created for using with Bulletproofs
    pub resp_new_bal: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_amount: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of asset-id in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_asset_id: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of secret key of the party's public key in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_pk: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to amount is created for using with Bulletproofs
    pub resp_amount: PokPedersenCommitment<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SendTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: RngCore>(
        rng: &mut R,
        asset_id: AssetId,
        amount: Balance,
        sk_e: G0::ScalarField,
        leg_enc: LegEncryption<Affine<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> (Self, F0) {
        let (mut even_prover, mut odd_prover, re_randomized_path, rerandomization) = initialize_curve_tree_prover(rng, TXN_EVEN_LABEL, TXN_ODD_LABEL, leaf_path, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_prover
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&g);

        // Commit to amount, old and new balance
        // TODO: It makes sense to commit to all these in a single vector commitment
        let r_bal_old = F0::rand(rng);
        let (comm_bal_old, var_bal_old) = even_prover.commit(F0::from(account.balance), r_bal_old);

        let r_bal_new = F0::rand(rng);
        let (comm_bal_new, var_bal_new) =
            even_prover.commit(F0::from(updated_account.balance), r_bal_new);

        let r_amount = F0::rand(rng);
        let (comm_amount, var_amount) = even_prover.commit(F0::from(amount), r_amount);

        // TODO: Combined the following 2 gadgets reduce 1 constraint
        // old - new balance is correct
        difference(
            &mut even_prover,
            var_bal_old.into(),
            var_bal_new.into(),
            var_amount.into(),
        )
        .unwrap();
        // new balance does not overflow
        range_proof(
            &mut even_prover,
            var_bal_new.into(),
            Some(updated_account.balance),
            AMOUNT_BITS.into(),
        )
        .unwrap();

        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. old balance - new balance = amount. Question: Do i need to show old balance > amount as amount is under 48 bit in leg and new balance is being proven under 48-bits
        // 4. amount and asset id are the same as the ones committed in leg
        // 5. new counter - old counter = 1
        // 6. nullifier is created from rho and sk in old account commitment so this sk and rho should be proven equal with other usages of these 2.
        // 7. pk in leg has the sk in account commitment

        let sk_blinding = F0::rand(rng);
        let new_counter_blinding = F0::rand(rng);
        let old_balance_blinding = F0::rand(rng);
        let new_balance_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let amount_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let sk_e_blinding = F0::rand(rng);

        let t_r_leaf = SchnorrCommitment::new(
            &[
                account_comm_key[0],
                account_comm_key[1],
                account_comm_key[2],
                account_comm_key[3],
                account_comm_key[4],
                account_comm_key[5],
                account_tree_params.even_parameters.pc_gens.B_blinding,
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
        let t_old_bal = PokPedersenCommitmentProtocol::init(
            account.balance.into(),
            old_balance_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_bal_old,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );
        let t_new_bal = PokPedersenCommitmentProtocol::init(
            updated_account.balance.into(),
            new_balance_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_bal_new,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );

        let t_null = PokPedersenCommitmentProtocol::init(
            account.sk,
            sk_blinding,
            &nullifier,
            account.rho,
            old_rho_blinding,
            &nullifier,
        );

        let t_leg_amount = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_amount.eph_pk,
            F0::from(amount),
            amount_blinding,
            &h,
        );
        let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_asset_id.eph_pk,
            F0::from(asset_id),
            asset_id_blinding,
            &h,
        );
        let t_leg_pk = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_s.eph_pk,
            account.sk,
            sk_blinding,
            &g,
        );
        let t_amount = PokPedersenCommitmentProtocol::init(
            F0::from(amount),
            amount_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_amount,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );

        let mut prover_transcript = even_prover.transcript();

        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_acc_new
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_old_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_bal_old,
                &mut prover_transcript,
            )
            .unwrap();
        t_new_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_bal_new,
                &mut prover_transcript,
            )
            .unwrap();
        t_null
            .challenge_contribution(&nullifier, &nullifier, &g, &mut prover_transcript)
            .unwrap();

        t_leg_amount
            .challenge_contribution(
                &leg_enc.ct_amount.eph_pk,
                &h,
                &leg_enc.ct_amount.encrypted,
                &mut prover_transcript,
            )
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
                &leg_enc.ct_s.eph_pk,
                &g,
                &leg_enc.ct_s.encrypted,
                &mut prover_transcript,
            )
            .unwrap();
        t_amount
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_amount,
                &mut prover_transcript,
            )
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

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
                    rerandomization,
                ],
                &prover_challenge,
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
                &prover_challenge,
            )
            .unwrap();
        let resp_old_bal = t_old_bal.gen_proof(&prover_challenge);
        let resp_new_bal = t_new_bal.gen_proof(&prover_challenge);
        let resp_null = t_null.gen_proof(&prover_challenge);

        let resp_leg_amount = t_leg_amount.clone().gen_proof(&prover_challenge);
        let resp_leg_asset_id = t_leg_asset_id.clone().gen_proof(&prover_challenge);
        let resp_leg_pk = t_leg_pk.clone().gen_proof(&prover_challenge);
        let resp_amount = t_amount.clone().gen_proof(&prover_challenge);

        let even_proof = even_prover
            .prove(&account_tree_params.even_parameters.bp_gens)
            .unwrap();
        let odd_proof = odd_prover
            .prove(&account_tree_params.odd_parameters.bp_gens)
            .unwrap();

        (
            Self {
                odd_proof,
                even_proof,
                updated_account_commitment,
                re_randomized_path,
                comm_bal_old,
                comm_bal_new,
                comm_amount,
                resp_leaf,
                resp_acc_new,
                resp_old_bal,
                resp_new_bal,
                resp_null,
                resp_leg_amount,
                resp_leg_asset_id,
                resp_leg_pk,
                resp_amount,
                nullifier,
                t_r_leaf: t_r_leaf.t,
                t_acc_new: t_acc_new.t,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        account_tree: &CurveTree<L, 1, G0, G1>,
        prover_challenge: F0,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> Result<(), R1CSError> {
        let (mut even_verifier, mut odd_verifier) = initialize_curve_tree_verifier(TXN_EVEN_LABEL, TXN_ODD_LABEL, self.re_randomized_path.clone(), account_tree, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        self.updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_verifier
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let var_bal_old = even_verifier.commit(self.comm_bal_old);
        let var_bal_new = even_verifier.commit(self.comm_bal_new);
        let var_amount = even_verifier.commit(self.comm_amount);

        difference(
            &mut even_verifier,
            var_bal_old.into(),
            var_bal_new.into(),
            var_amount.into(),
        )
        .unwrap();

        range_proof(
            &mut even_verifier,
            var_bal_new.into(),
            None,
            AMOUNT_BITS.into(),
        )
        .unwrap();

        let mut verifier_transcript = even_verifier.transcript();

        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.t_acc_new
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_old_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_bal_old,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_new_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_bal_new,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_null
            .challenge_contribution(
                &self.nullifier,
                &self.nullifier,
                &g,
                &mut verifier_transcript,
            )
            .unwrap();

        self.resp_leg_amount
            .challenge_contribution(
                &leg_enc.ct_amount.eph_pk,
                &h,
                &leg_enc.ct_amount.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_leg_asset_id
            .challenge_contribution(
                &leg_enc.ct_asset_id.eph_pk,
                &h,
                &leg_enc.ct_asset_id.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_leg_pk
            .challenge_contribution(
                &leg_enc.ct_s.eph_pk,
                &g,
                &leg_enc.ct_s.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_amount
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_amount,
                &mut verifier_transcript,
            )
            .unwrap();

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        self.resp_leaf
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                    account_tree_params.even_parameters.pc_gens.B_blinding,
                ],
                &self.re_randomized_path.re_randomized_leaf,
                &self.t_r_leaf,
                &verifier_challenge,
            )
            .unwrap();
        self.resp_acc_new
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                ],
                &self.updated_account_commitment.0,
                &self.t_acc_new,
                &verifier_challenge,
            )
            .unwrap();
        assert!(self.resp_old_bal.verify(
            &self.comm_bal_old,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ));
        assert!(self.resp_new_bal.verify(
            &self.comm_bal_new,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ));
        assert!(
            self.resp_null
                .verify(&g, &self.nullifier, &self.nullifier, &verifier_challenge,)
        );

        assert!(self.resp_leg_amount.verify(
            &leg_enc.ct_amount.encrypted,
            &leg_enc.ct_amount.eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_leg_asset_id.verify(
            &leg_enc.ct_asset_id.encrypted,
            &leg_enc.ct_asset_id.eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_leg_pk.verify(
            &leg_enc.ct_s.encrypted,
            &leg_enc.ct_s.eph_pk,
            &g,
            &verifier_challenge
        ));
        assert!(self.resp_amount.verify(
            &self.comm_amount,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge
        ));

        // Sk and asset id in leaf match the ones in updated account commitment
        assert_eq!(self.resp_leaf.0[0], self.resp_acc_new.0[0]);
        assert_eq!(self.resp_leaf.0[3], self.resp_acc_new.0[3]);
        // Balance in leaf (old account) is same as in the old balance commitment
        assert_eq!(self.resp_leaf.0[1], self.resp_old_bal.response1);
        // Balance in new account commitment is same as in the new balance commitment
        assert_eq!(self.resp_acc_new.0[1], self.resp_new_bal.response1);
        // Counter in new account commitment is 1 more than the one in the leaf commitment
        assert_eq!(
            self.resp_acc_new.0[2],
            self.resp_leaf.0[2] + verifier_challenge
        );

        // Sk and rho match the ones in nullifier
        assert_eq!(self.resp_leaf.0[0], self.resp_null.response1);
        assert_eq!(self.resp_leaf.0[4], self.resp_null.response2);

        // Amount in leg is same as amount in commitment
        assert_eq!(self.resp_leg_amount.response2, self.resp_amount.response1);

        // Asset id in leg is same as in account commitment
        assert_eq!(self.resp_leg_asset_id.response2, self.resp_acc_new.0[3]);

        // sk in account comm matches the one in pk
        assert_eq!(self.resp_leg_pk.response2, self.resp_leaf.0[0]);

        // sk_e matches in all 3 encryptions
        assert_eq!(
            self.resp_leg_amount.response1,
            self.resp_leg_asset_id.response1
        );
        assert_eq!(self.resp_leg_amount.response1, self.resp_leg_pk.response1);

        odd_verifier.verify(
            &self.odd_proof,
            &account_tree_params.odd_parameters.pc_gens,
            &account_tree_params.odd_parameters.bp_gens,
        )?;
        even_verifier.verify(
            &self.even_proof,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
        )?;
        Ok(())
    }
}

/// This is the proof for receive txn. Report section 5.1.8
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReceiveTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    /// This is the commitment to the new account state which will become new leaf
    pub updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    pub nullifier: Affine<G0>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokPedersenCommitment<Affine<G0>>,
    pub resp_leg_asset_id: PokPedersenCommitment<Affine<G0>>,
    pub resp_leg_pk: PokPedersenCommitment<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> ReceiveTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: RngCore>(
        rng: &mut R,
        asset_id: AssetId,
        sk_e: G0::ScalarField,
        leg_enc: LegEncryption<Affine<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> (Self, F0) {
        let (mut even_prover, mut odd_prover, re_randomized_path, rerandomization) = initialize_curve_tree_prover(rng, TXN_EVEN_LABEL, TXN_ODD_LABEL, leaf_path, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_prover
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&g);

        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. new counter - old counter = 1
        // 5. nullifier is created from rho and sk in old account commitment so this sk and rho should be proven equal with other usages of these 2.
        // 6. pk in leg has the sk in account commitment

        let sk_blinding = F0::rand(rng);
        let new_counter_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let balance_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let sk_e_blinding = F0::rand(rng);

        let t_r_leaf = SchnorrCommitment::new(
            &[
                account_comm_key[0],
                account_comm_key[1],
                account_comm_key[2],
                account_comm_key[3],
                account_comm_key[4],
                account_comm_key[5],
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![
                sk_blinding,
                balance_blinding,
                new_counter_blinding,
                asset_id_blinding,
                old_rho_blinding,
                F0::rand(rng),
                F0::rand(rng),
            ],
        );
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
                balance_blinding,
                new_counter_blinding,
                asset_id_blinding,
                F0::rand(rng),
                F0::rand(rng),
            ],
        );
        let t_null = PokPedersenCommitmentProtocol::init(
            account.sk,
            sk_blinding,
            &nullifier,
            account.rho,
            old_rho_blinding,
            &nullifier,
        );

        let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_asset_id.eph_pk,
            F0::from(asset_id),
            asset_id_blinding,
            &h,
        );
        let t_leg_pk = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_r.eph_pk,
            account.sk,
            sk_blinding,
            &g,
        );

        let mut prover_transcript = even_prover.transcript();

        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_acc_new
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_null
            .challenge_contribution(&nullifier, &nullifier, &g, &mut prover_transcript)
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
                &leg_enc.ct_r.eph_pk,
                &g,
                &leg_enc.ct_r.encrypted,
                &mut prover_transcript,
            )
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

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
                    rerandomization,
                ],
                &prover_challenge,
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
                &prover_challenge,
            )
            .unwrap();
        let resp_null = t_null.gen_proof(&prover_challenge);

        let resp_leg_asset_id = t_leg_asset_id.clone().gen_proof(&prover_challenge);
        let resp_leg_pk = t_leg_pk.clone().gen_proof(&prover_challenge);

        let even_proof = even_prover
            .prove(&account_tree_params.even_parameters.bp_gens)
            .unwrap();
        let odd_proof = odd_prover
            .prove(&account_tree_params.odd_parameters.bp_gens)
            .unwrap();
        (
            Self {
                odd_proof,
                even_proof,
                re_randomized_path,
                nullifier,
                updated_account_commitment,
                t_r_leaf: t_r_leaf.t,
                t_acc_new: t_acc_new.t,
                resp_leaf,
                resp_acc_new,
                resp_null,
                resp_leg_pk,
                resp_leg_asset_id,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        account_tree: &CurveTree<L, 1, G0, G1>,
        prover_challenge: F0,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> Result<(), R1CSError> {
        let (mut even_verifier, mut odd_verifier) = initialize_curve_tree_verifier(TXN_EVEN_LABEL, TXN_ODD_LABEL, self.re_randomized_path.clone(), account_tree, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        self.updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_verifier
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let mut verifier_transcript = even_verifier.transcript();

        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.t_acc_new
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_null
            .challenge_contribution(
                &self.nullifier,
                &self.nullifier,
                &g,
                &mut verifier_transcript,
            )
            .unwrap();

        self.resp_leg_asset_id
            .challenge_contribution(
                &leg_enc.ct_asset_id.eph_pk,
                &h,
                &leg_enc.ct_asset_id.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_leg_pk
            .challenge_contribution(
                &leg_enc.ct_r.eph_pk,
                &g,
                &leg_enc.ct_r.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        self.resp_leaf
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                    account_tree_params.even_parameters.pc_gens.B_blinding,
                ],
                &self.re_randomized_path.re_randomized_leaf,
                &self.t_r_leaf,
                &verifier_challenge,
            )
            .unwrap();
        self.resp_acc_new
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                ],
                &self.updated_account_commitment.0,
                &self.t_acc_new,
                &verifier_challenge,
            )
            .unwrap();
        assert!(
            self.resp_null
                .verify(&g, &self.nullifier, &self.nullifier, &verifier_challenge,)
        );

        assert!(self.resp_leg_asset_id.verify(
            &leg_enc.ct_asset_id.encrypted,
            &leg_enc.ct_asset_id.eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_leg_pk.verify(
            &leg_enc.ct_r.encrypted,
            &leg_enc.ct_r.eph_pk,
            &g,
            &verifier_challenge
        ));

        // Sk and asset id in leaf match the ones in updated account commitment
        assert_eq!(self.resp_leaf.0[0], self.resp_acc_new.0[0]);
        assert_eq!(self.resp_leaf.0[3], self.resp_acc_new.0[3]);
        // Balance in leaf (old account) is same as in the updated account commitment
        assert_eq!(self.resp_leaf.0[1], self.resp_acc_new.0[1]);

        // Counter in new account commitment is 1 more than the one in the leaf commitment
        assert_eq!(
            self.resp_acc_new.0[2],
            self.resp_leaf.0[2] + verifier_challenge
        );

        // Sk and rho match the ones in nullifier
        assert_eq!(self.resp_leaf.0[0], self.resp_null.response1);
        assert_eq!(self.resp_leaf.0[4], self.resp_null.response2);

        // Asset id in leg is same as in account commitment
        assert_eq!(self.resp_leg_asset_id.response2, self.resp_acc_new.0[3]);

        // sk in account comm matches the one in pk
        assert_eq!(self.resp_leg_pk.response2, self.resp_leaf.0[0]);

        // sk_e matches in both encryptions
        assert_eq!(self.resp_leg_pk.response1, self.resp_leg_asset_id.response1);

        odd_verifier.verify(
            &self.odd_proof,
            &account_tree_params.odd_parameters.pc_gens,
            &account_tree_params.odd_parameters.bp_gens,
        )?;
        even_verifier.verify(
            &self.even_proof,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
        )?;
        Ok(())
    }
}

/// This is the proof for receiver claiming funds from a receive txn. Not present in report
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ClaimReceivedTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    /// This is the commitment to the new account state which will become new leaf
    pub updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    pub comm_bal_old: Affine<G0>,
    pub comm_bal_new: Affine<G0>,
    pub comm_amount: Affine<G0>,
    pub nullifier: Affine<G0>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of old balance using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to old balance is created for using with Bulletproofs
    pub resp_old_bal: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of old balance using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to new balance is created for using with Bulletproofs
    pub resp_new_bal: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_amount: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of asset-id in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_asset_id: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of secret key of the party's public key in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_pk: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to amount is created for using with Bulletproofs
    pub resp_amount: PokPedersenCommitment<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> ClaimReceivedTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: RngCore>(
        rng: &mut R,
        asset_id: AssetId,
        amount: Balance,
        sk_e: G0::ScalarField,
        sk_r: G0::ScalarField,
        leg_enc: LegEncryption<Affine<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> (Self, F0) {
        let (mut even_prover, mut odd_prover, re_randomized_path, rerandomization) = initialize_curve_tree_prover(rng, TXN_EVEN_LABEL, TXN_ODD_LABEL, leaf_path, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_prover
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&g);

        // TODO: It makes sense to commit to all these in a single vector commitment
        let r_bal_old = F0::rand(rng);
        let (comm_bal_old, var_bal_old) = even_prover.commit(F0::from(account.balance), r_bal_old);

        let r_bal_new = F0::rand(rng);
        let (comm_bal_new, var_bal_new) =
            even_prover.commit(F0::from(updated_account.balance), r_bal_new);

        let r_amount = F0::rand(rng);
        let (comm_amount, var_amount) = even_prover.commit(F0::from(amount), r_amount);

        // TODO: Combine the following 2 gadgets to reduce 1 constraint
        // new - old balance is correct
        difference(
            &mut even_prover,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )
        .unwrap();
        // new balance does not overflow
        range_proof(
            &mut even_prover,
            var_bal_new.into(),
            Some(updated_account.balance),
            AMOUNT_BITS.into(),
        )
        .unwrap();

        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. new balance - old balance = amount.
        // 4. amount and asset id are the same as the ones committed in leg
        // 5. old counter - new counter = 1
        // 6. nullifier is created from rho and sk in old account commitment so this sk and rho should be proven equal with other usages of these 2.
        // 7. pk in leg has the sk in account commitment

        let sk_blinding = F0::rand(rng);
        let new_counter_blinding = F0::rand(rng);
        let old_balance_blinding = F0::rand(rng);
        let new_balance_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let amount_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let sk_e_blinding = F0::rand(rng);

        let t_r_leaf = SchnorrCommitment::new(
            &[
                account_comm_key[0],
                account_comm_key[1],
                account_comm_key[2],
                account_comm_key[3],
                account_comm_key[4],
                account_comm_key[5],
                account_tree_params.even_parameters.pc_gens.B_blinding,
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
        let t_old_bal = PokPedersenCommitmentProtocol::init(
            account.balance.into(),
            old_balance_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_bal_old,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );
        let t_new_bal = PokPedersenCommitmentProtocol::init(
            updated_account.balance.into(),
            new_balance_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_bal_new,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );
        let t_null = PokPedersenCommitmentProtocol::init(
            account.sk,
            sk_blinding,
            &nullifier,
            account.rho,
            old_rho_blinding,
            &nullifier,
        );

        let t_leg_amount = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_amount.eph_pk,
            F0::from(amount),
            amount_blinding,
            &h,
        );
        let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_asset_id.eph_pk,
            F0::from(asset_id),
            asset_id_blinding,
            &h,
        );
        let t_leg_pk = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_r.eph_pk,
            sk_r,
            sk_blinding,
            &g,
        );
        let t_amount = PokPedersenCommitmentProtocol::init(
            F0::from(amount),
            amount_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_amount,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );

        let mut prover_transcript = even_prover.transcript();

        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_acc_new
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_old_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_bal_old,
                &mut prover_transcript,
            )
            .unwrap();
        t_new_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_bal_new,
                &mut prover_transcript,
            )
            .unwrap();
        t_null
            .challenge_contribution(&nullifier, &nullifier, &g, &mut prover_transcript)
            .unwrap();

        t_leg_amount
            .challenge_contribution(
                &leg_enc.ct_amount.eph_pk,
                &h,
                &leg_enc.ct_amount.encrypted,
                &mut prover_transcript,
            )
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
                &leg_enc.ct_r.eph_pk,
                &g,
                &leg_enc.ct_r.encrypted,
                &mut prover_transcript,
            )
            .unwrap();
        t_amount
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_amount,
                &mut prover_transcript,
            )
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

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
                    rerandomization,
                ],
                &prover_challenge,
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
                &prover_challenge,
            )
            .unwrap();
        let resp_old_bal = t_old_bal.gen_proof(&prover_challenge);
        let resp_new_bal = t_new_bal.gen_proof(&prover_challenge);
        let resp_null = t_null.gen_proof(&prover_challenge);

        let resp_leg_amount = t_leg_amount.clone().gen_proof(&prover_challenge);
        let resp_leg_asset_id = t_leg_asset_id.clone().gen_proof(&prover_challenge);
        let resp_leg_pk = t_leg_pk.clone().gen_proof(&prover_challenge);
        let resp_amount = t_amount.clone().gen_proof(&prover_challenge);

        let even_proof = even_prover
            .prove(&account_tree_params.even_parameters.bp_gens)
            .unwrap();
        let odd_proof = odd_prover
            .prove(&account_tree_params.odd_parameters.bp_gens)
            .unwrap();
        (
            Self {
                odd_proof,
                even_proof,
                updated_account_commitment,
                re_randomized_path,
                comm_bal_old,
                comm_bal_new,
                comm_amount,
                resp_leaf,
                resp_acc_new,
                resp_old_bal,
                resp_new_bal,
                resp_null,
                resp_leg_amount,
                resp_leg_asset_id,
                resp_leg_pk,
                resp_amount,
                nullifier,
                t_r_leaf: t_r_leaf.t,
                t_acc_new: t_acc_new.t,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        account_tree: &CurveTree<L, 1, G0, G1>,
        prover_challenge: F0,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> Result<(), R1CSError> {
        let (mut even_verifier, mut odd_verifier) = initialize_curve_tree_verifier(TXN_EVEN_LABEL, TXN_ODD_LABEL, self.re_randomized_path.clone(), account_tree, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        self.updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_verifier
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let var_bal_old = even_verifier.commit(self.comm_bal_old);
        let var_bal_new = even_verifier.commit(self.comm_bal_new);
        let var_amount = even_verifier.commit(self.comm_amount);

        difference(
            &mut even_verifier,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )
        .unwrap();

        range_proof(
            &mut even_verifier,
            var_bal_new.into(),
            None,
            AMOUNT_BITS.into(),
        )
        .unwrap();

        let mut verifier_transcript = even_verifier.transcript();

        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.t_acc_new
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_old_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_bal_old,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_new_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_bal_new,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_null
            .challenge_contribution(
                &self.nullifier,
                &self.nullifier,
                &g,
                &mut verifier_transcript,
            )
            .unwrap();

        self.resp_leg_amount
            .challenge_contribution(
                &leg_enc.ct_amount.eph_pk,
                &h,
                &leg_enc.ct_amount.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_leg_asset_id
            .challenge_contribution(
                &leg_enc.ct_asset_id.eph_pk,
                &h,
                &leg_enc.ct_asset_id.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_leg_pk
            .challenge_contribution(
                &leg_enc.ct_r.eph_pk,
                &g,
                &leg_enc.ct_r.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_amount
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_amount,
                &mut verifier_transcript,
            )
            .unwrap();

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        self.resp_leaf
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                    account_tree_params.even_parameters.pc_gens.B_blinding,
                ],
                &self.re_randomized_path.re_randomized_leaf,
                &self.t_r_leaf,
                &verifier_challenge,
            )
            .unwrap();
        self.resp_acc_new
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                ],
                &self.updated_account_commitment.0,
                &self.t_acc_new,
                &verifier_challenge,
            )
            .unwrap();
        assert!(self.resp_old_bal.verify(
            &self.comm_bal_old,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ));
        assert!(self.resp_new_bal.verify(
            &self.comm_bal_new,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ));
        assert!(
            self.resp_null
                .verify(&g, &self.nullifier, &self.nullifier, &verifier_challenge,)
        );

        assert!(self.resp_leg_amount.verify(
            &leg_enc.ct_amount.encrypted,
            &leg_enc.ct_amount.eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_leg_asset_id.verify(
            &leg_enc.ct_asset_id.encrypted,
            &leg_enc.ct_asset_id.eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_leg_pk.verify(
            &leg_enc.ct_r.encrypted,
            &leg_enc.ct_r.eph_pk,
            &g,
            &verifier_challenge
        ));
        assert!(self.resp_amount.verify(
            &self.comm_amount,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge
        ));

        // Sk and asset id in leaf match the ones in updated account commitment
        assert_eq!(self.resp_leaf.0[0], self.resp_acc_new.0[0]);
        assert_eq!(self.resp_leaf.0[3], self.resp_acc_new.0[3]);
        // Balance in leaf (old account) is same as in the old balance commitment
        assert_eq!(self.resp_leaf.0[1], self.resp_old_bal.response1);
        // Balance in new account commitment is same as in the new balance commitment
        assert_eq!(self.resp_acc_new.0[1], self.resp_new_bal.response1);
        // Counter in new account commitment is 1 less than the one in the leaf commitment
        assert_eq!(
            self.resp_acc_new.0[2] + verifier_challenge,
            self.resp_leaf.0[2]
        );

        // Sk and rho match the ones in nullifier
        assert_eq!(self.resp_leaf.0[0], self.resp_null.response1);
        assert_eq!(self.resp_leaf.0[4], self.resp_null.response2);

        // Amount in leg is same as amount in commitment
        assert_eq!(self.resp_leg_amount.response2, self.resp_amount.response1);

        // Asset id in leg is same as in account commitment
        assert_eq!(self.resp_leg_asset_id.response2, self.resp_acc_new.0[3]);

        // sk in account comm matches the one in pk
        assert_eq!(self.resp_leg_pk.response2, self.resp_leaf.0[0]);

        // sk_e matches in all 3 encryptions
        assert_eq!(
            self.resp_leg_amount.response1,
            self.resp_leg_asset_id.response1
        );
        assert_eq!(self.resp_leg_amount.response1, self.resp_leg_pk.response1);

        odd_verifier.verify(
            &self.odd_proof,
            &account_tree_params.odd_parameters.pc_gens,
            &account_tree_params.odd_parameters.bp_gens,
        )?;
        even_verifier.verify(
            &self.even_proof,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SenderReverseTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    /// This is the commitment to the new account state which will become new leaf
    pub updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    pub comm_bal_old: Affine<G0>,
    pub comm_bal_new: Affine<G0>,
    pub comm_amount: Affine<G0>,
    pub nullifier: Affine<G0>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of old balance using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to old balance is created for using with Bulletproofs
    pub resp_old_bal: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of old balance using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to new balance is created for using with Bulletproofs
    pub resp_new_bal: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_amount: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of asset-id in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_asset_id: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of secret key of the party's public key in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_pk: PokPedersenCommitment<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount using Schnorr protocol (step 1 and 3 of Schnorr).
    /// The commitment to amount is created for using with Bulletproofs
    pub resp_amount: PokPedersenCommitment<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SenderReverseTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: RngCore>(
        rng: &mut R,
        amount: Balance,
        sk_e: G0::ScalarField,
        leg_enc: LegEncryption<Affine<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> (Self, F0) {
        let (mut even_prover, mut odd_prover, re_randomized_path, rerandomization) = initialize_curve_tree_prover(rng, TXN_EVEN_LABEL, TXN_ODD_LABEL, leaf_path, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_prover
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&g);

        // TODO: It makes sense to commit to all these in a single vector commitment
        let r_bal_old = F0::rand(rng);
        let (comm_bal_old, var_bal_old) = even_prover.commit(F0::from(account.balance), r_bal_old);

        let r_bal_new = F0::rand(rng);
        let (comm_bal_new, var_bal_new) =
            even_prover.commit(F0::from(updated_account.balance), r_bal_new);

        let r_amount = F0::rand(rng);
        let (comm_amount, var_amount) = even_prover.commit(F0::from(amount), r_amount);

        // TODO: Combine the following 2 gadgets to reduce 1 constraint
        // new - old balance is correct
        difference(
            &mut even_prover,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )
        .unwrap();
        // new balance does not overflow
        range_proof(
            &mut even_prover,
            var_bal_new.into(),
            Some(updated_account.balance),
            AMOUNT_BITS.into(),
        )
        .unwrap();

        let sk_blinding = F0::rand(rng);
        let new_counter_blinding = F0::rand(rng);
        let old_balance_blinding = F0::rand(rng);
        let new_balance_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let amount_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let sk_e_blinding = F0::rand(rng);

        let t_r_leaf = SchnorrCommitment::new(
            &[
                account_comm_key[0],
                account_comm_key[1],
                account_comm_key[2],
                account_comm_key[3],
                account_comm_key[4],
                account_comm_key[5],
                account_tree_params.even_parameters.pc_gens.B_blinding,
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
        let t_old_bal = PokPedersenCommitmentProtocol::init(
            account.balance.into(),
            old_balance_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_bal_old,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );
        let t_new_bal = PokPedersenCommitmentProtocol::init(
            updated_account.balance.into(),
            new_balance_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_bal_new,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );
        let t_null = PokPedersenCommitmentProtocol::init(
            account.sk,
            sk_blinding,
            &nullifier,
            account.rho,
            old_rho_blinding,
            &nullifier,
        );

        let t_leg_amount = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_amount.eph_pk,
            F0::from(amount),
            amount_blinding,
            &h,
        );
        let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_asset_id.eph_pk,
            F0::from(account.asset_id),
            asset_id_blinding,
            &h,
        );
        let t_leg_pk = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_s.eph_pk,
            account.sk,
            sk_blinding,
            &g,
        );
        let t_amount = PokPedersenCommitmentProtocol::init(
            F0::from(amount),
            amount_blinding,
            &account_tree_params.even_parameters.pc_gens.B,
            r_amount,
            F0::rand(rng),
            &account_tree_params.even_parameters.pc_gens.B_blinding,
        );

        let mut prover_transcript = even_prover.transcript();

        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_acc_new
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_old_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_bal_old,
                &mut prover_transcript,
            )
            .unwrap();
        t_new_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_bal_new,
                &mut prover_transcript,
            )
            .unwrap();
        t_null
            .challenge_contribution(&nullifier, &nullifier, &g, &mut prover_transcript)
            .unwrap();

        t_leg_amount
            .challenge_contribution(
                &leg_enc.ct_amount.eph_pk,
                &h,
                &leg_enc.ct_amount.encrypted,
                &mut prover_transcript,
            )
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
                &leg_enc.ct_s.eph_pk,
                &g,
                &leg_enc.ct_s.encrypted,
                &mut prover_transcript,
            )
            .unwrap();
        t_amount
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &comm_amount,
                &mut prover_transcript,
            )
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

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
                    rerandomization,
                ],
                &prover_challenge,
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
                &prover_challenge,
            )
            .unwrap();
        let resp_old_bal = t_old_bal.gen_proof(&prover_challenge);
        let resp_new_bal = t_new_bal.gen_proof(&prover_challenge);
        let resp_null = t_null.gen_proof(&prover_challenge);

        let resp_leg_amount = t_leg_amount.clone().gen_proof(&prover_challenge);
        let resp_leg_asset_id = t_leg_asset_id.clone().gen_proof(&prover_challenge);
        let resp_leg_pk = t_leg_pk.clone().gen_proof(&prover_challenge);
        let resp_amount = t_amount.clone().gen_proof(&prover_challenge);

        let even_proof = even_prover
            .prove(&account_tree_params.even_parameters.bp_gens)
            .unwrap();
        let odd_proof = odd_prover
            .prove(&account_tree_params.odd_parameters.bp_gens)
            .unwrap();
        (
            Self {
                even_proof,
                odd_proof,
                re_randomized_path,
                updated_account_commitment,
                nullifier,
                comm_bal_old,
                comm_bal_new,
                comm_amount,
                resp_leaf,
                resp_acc_new,
                resp_old_bal,
                resp_new_bal,
                resp_null,
                resp_leg_amount,
                resp_leg_asset_id,
                resp_leg_pk,
                resp_amount,
                t_r_leaf: t_r_leaf.t,
                t_acc_new: t_acc_new.t,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        account_tree: &CurveTree<L, 1, G0, G1>,
        prover_challenge: F0,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> Result<(), R1CSError> {
        let (mut even_verifier, mut odd_verifier) = initialize_curve_tree_verifier(TXN_EVEN_LABEL, TXN_ODD_LABEL, self.re_randomized_path.clone(), account_tree, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        self.updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_verifier
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let var_bal_old = even_verifier.commit(self.comm_bal_old);
        let var_bal_new = even_verifier.commit(self.comm_bal_new);
        let var_amount = even_verifier.commit(self.comm_amount);

        difference(
            &mut even_verifier,
            var_bal_new.into(),
            var_bal_old.into(),
            var_amount.into(),
        )
        .unwrap();

        range_proof(
            &mut even_verifier,
            var_bal_new.into(),
            None,
            AMOUNT_BITS.into(),
        )
        .unwrap();

        let mut verifier_transcript = even_verifier.transcript();

        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.t_acc_new
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_old_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_bal_old,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_new_bal
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_bal_new,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_null
            .challenge_contribution(
                &self.nullifier,
                &self.nullifier,
                &g,
                &mut verifier_transcript,
            )
            .unwrap();

        self.resp_leg_amount
            .challenge_contribution(
                &leg_enc.ct_amount.eph_pk,
                &h,
                &leg_enc.ct_amount.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_leg_asset_id
            .challenge_contribution(
                &leg_enc.ct_asset_id.eph_pk,
                &h,
                &leg_enc.ct_asset_id.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_leg_pk
            .challenge_contribution(
                &leg_enc.ct_s.eph_pk,
                &g,
                &leg_enc.ct_s.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_amount
            .challenge_contribution(
                &account_tree_params.even_parameters.pc_gens.B,
                &account_tree_params.even_parameters.pc_gens.B_blinding,
                &self.comm_amount,
                &mut verifier_transcript,
            )
            .unwrap();

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        self.resp_leaf
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                    account_tree_params.even_parameters.pc_gens.B_blinding,
                ],
                &self.re_randomized_path.re_randomized_leaf,
                &self.t_r_leaf,
                &verifier_challenge,
            )
            .unwrap();
        self.resp_acc_new
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                ],
                &self.updated_account_commitment.0,
                &self.t_acc_new,
                &verifier_challenge,
            )
            .unwrap();
        assert!(self.resp_old_bal.verify(
            &self.comm_bal_old,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ));
        assert!(self.resp_new_bal.verify(
            &self.comm_bal_new,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge,
        ));
        assert!(
            self.resp_null
                .verify(&g, &self.nullifier, &self.nullifier, &verifier_challenge,)
        );

        assert!(self.resp_leg_amount.verify(
            &leg_enc.ct_amount.encrypted,
            &leg_enc.ct_amount.eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_leg_asset_id.verify(
            &leg_enc.ct_asset_id.encrypted,
            &leg_enc.ct_asset_id.eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_leg_pk.verify(
            &leg_enc.ct_s.encrypted,
            &leg_enc.ct_s.eph_pk,
            &g,
            &verifier_challenge
        ));
        assert!(self.resp_amount.verify(
            &self.comm_amount,
            &account_tree_params.even_parameters.pc_gens.B,
            &account_tree_params.even_parameters.pc_gens.B_blinding,
            &verifier_challenge
        ));

        // Sk and asset id in leaf match the ones in updated account commitment
        assert_eq!(self.resp_leaf.0[0], self.resp_acc_new.0[0]);
        assert_eq!(self.resp_leaf.0[3], self.resp_acc_new.0[3]);
        // Balance in leaf (old account) is same as in the old balance commitment
        assert_eq!(self.resp_leaf.0[1], self.resp_old_bal.response1);
        // Balance in new account commitment is same as in the new balance commitment
        assert_eq!(self.resp_acc_new.0[1], self.resp_new_bal.response1);
        // Counter in new account commitment is 1 less than the one in the leaf commitment
        assert_eq!(
            self.resp_acc_new.0[2] + verifier_challenge,
            self.resp_leaf.0[2]
        );

        // Sk and rho match the ones in nullifier
        assert_eq!(self.resp_leaf.0[0], self.resp_null.response1);
        assert_eq!(self.resp_leaf.0[4], self.resp_null.response2);

        // Amount in leg is same as amount in commitment
        assert_eq!(self.resp_leg_amount.response2, self.resp_amount.response1);

        // Asset id in leg is same as in account commitment
        assert_eq!(self.resp_leg_asset_id.response2, self.resp_acc_new.0[3]);

        // sk in account comm matches the one in pk
        assert_eq!(self.resp_leg_pk.response2, self.resp_leaf.0[0]);

        // sk_e matches in all 3 encryptions
        assert_eq!(
            self.resp_leg_amount.response1,
            self.resp_leg_asset_id.response1
        );
        assert_eq!(self.resp_leg_amount.response1, self.resp_leg_pk.response1);

        odd_verifier.verify(
            &self.odd_proof,
            &account_tree_params.odd_parameters.pc_gens,
            &account_tree_params.odd_parameters.bp_gens,
        )?;
        even_verifier.verify(
            &self.even_proof,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
        )?;
        Ok(())
    }
}

/// This is the proof for sender sending counter update txn. Report calls it txn_cu and describes in section 5.1.11, fig. 9
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SenderCounterUpdateTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub even_proof: R1CSProof<Affine<G0>>,
    pub odd_proof: R1CSProof<Affine<G1>>,
    pub re_randomized_path: SelectAndRerandomizePath<L, G0, G1>,
    /// This is the commitment to the new account state which will become new leaf
    pub updated_account_commitment: AccountStateCommitment<Affine<G0>>,
    pub nullifier: Affine<G0>,
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_r_leaf: Affine<G0>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G0>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: SchnorrResponse<Affine<G0>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: SchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokPedersenCommitment<Affine<G0>>,
    pub resp_leg_asset_id: PokPedersenCommitment<Affine<G0>>,
    pub resp_leg_pk: PokPedersenCommitment<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> SenderCounterUpdateTxnProof<L, F0, F1, G0, G1>
{
    pub fn new<R: RngCore>(
        rng: &mut R,
        asset_id: AssetId,
        sk_e: G0::ScalarField,
        leg_enc: LegEncryption<Affine<G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        updated_account_commitment: AccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> (Self, F0) {
        let (mut even_prover, mut odd_prover, re_randomized_path, rerandomization) = initialize_curve_tree_prover(rng, TXN_EVEN_LABEL, TXN_ODD_LABEL, leaf_path, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_prover
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&g);

        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. old counter - new counter = 1
        // 5. nullifier is created from rho and sk in old account commitment so this sk and rho should be proven equal with other usages of these 2.
        // 6. pk in leg has the sk in account commitment

        let sk_blinding = F0::rand(rng);
        let counter_blinding = F0::rand(rng);
        let asset_id_blinding = F0::rand(rng);
        let balance_blinding = F0::rand(rng);
        let old_rho_blinding = F0::rand(rng);
        let sk_e_blinding = F0::rand(rng);

        let t_r_leaf = SchnorrCommitment::new(
            &[
                account_comm_key[0],
                account_comm_key[1],
                account_comm_key[2],
                account_comm_key[3],
                account_comm_key[4],
                account_comm_key[5],
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![
                sk_blinding,
                balance_blinding,
                counter_blinding,
                asset_id_blinding,
                old_rho_blinding,
                F0::rand(rng),
                F0::rand(rng),
            ],
        );
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
                balance_blinding,
                counter_blinding,
                asset_id_blinding,
                F0::rand(rng),
                F0::rand(rng),
            ],
        );
        let t_null = PokPedersenCommitmentProtocol::init(
            account.sk,
            sk_blinding,
            &nullifier,
            account.rho,
            old_rho_blinding,
            &nullifier,
        );

        let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_asset_id.eph_pk,
            F0::from(asset_id),
            asset_id_blinding,
            &h,
        );
        let t_leg_pk = PokPedersenCommitmentProtocol::init(
            sk_e,
            sk_e_blinding,
            &leg_enc.ct_s.eph_pk,
            account.sk,
            sk_blinding,
            &g,
        );

        let mut prover_transcript = even_prover.transcript();

        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_acc_new
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_null
            .challenge_contribution(&nullifier, &nullifier, &g, &mut prover_transcript)
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
                &leg_enc.ct_s.eph_pk,
                &g,
                &leg_enc.ct_s.encrypted,
                &mut prover_transcript,
            )
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

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
                    rerandomization,
                ],
                &prover_challenge,
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
                &prover_challenge,
            )
            .unwrap();
        let resp_null = t_null.gen_proof(&prover_challenge);

        let resp_leg_asset_id = t_leg_asset_id.clone().gen_proof(&prover_challenge);
        let resp_leg_pk = t_leg_pk.clone().gen_proof(&prover_challenge);

        let even_proof = even_prover
            .prove(&account_tree_params.even_parameters.bp_gens)
            .unwrap();
        let odd_proof = odd_prover
            .prove(&account_tree_params.odd_parameters.bp_gens)
            .unwrap();
        (
            Self {
                even_proof,
                odd_proof,
                re_randomized_path,
                updated_account_commitment,
                nullifier,
                t_r_leaf: t_r_leaf.t,
                t_acc_new: t_acc_new.t,
                resp_leaf,
                resp_acc_new,
                resp_null,
                resp_leg_asset_id,
                resp_leg_pk,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<Affine<G0>>,
        account_tree: &CurveTree<L, 1, G0, G1>,
        prover_challenge: F0,
        nonce: &[u8],
        account_tree_params: &SelRerandParameters<G0, G1>,
        account_comm_key: &[Affine<G0>],
        g: Affine<G0>,
        h: Affine<G0>,
    ) -> Result<(), R1CSError> {
        let (mut even_verifier, mut odd_verifier) = initialize_curve_tree_verifier(TXN_EVEN_LABEL, TXN_ODD_LABEL, self.re_randomized_path.clone(), account_tree, account_tree_params);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        leg_enc.serialize_compressed(&mut extra_instance).unwrap();
        self.updated_account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        // TODO: Uncomment
        // account_tree_params.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        even_verifier
            .transcript()
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let mut verifier_transcript = even_verifier.transcript();

        self.t_r_leaf
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.t_acc_new
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_null
            .challenge_contribution(
                &self.nullifier,
                &self.nullifier,
                &g,
                &mut verifier_transcript,
            )
            .unwrap();

        self.resp_leg_asset_id
            .challenge_contribution(
                &leg_enc.ct_asset_id.eph_pk,
                &h,
                &leg_enc.ct_asset_id.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_leg_pk
            .challenge_contribution(
                &leg_enc.ct_s.eph_pk,
                &g,
                &leg_enc.ct_s.encrypted,
                &mut verifier_transcript,
            )
            .unwrap();

        let verifier_challenge = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        self.resp_leaf
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                    account_tree_params.even_parameters.pc_gens.B_blinding,
                ],
                &self.re_randomized_path.re_randomized_leaf,
                &self.t_r_leaf,
                &verifier_challenge,
            )
            .unwrap();
        self.resp_acc_new
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[1],
                    account_comm_key[2],
                    account_comm_key[3],
                    account_comm_key[4],
                    account_comm_key[5],
                ],
                &self.updated_account_commitment.0,
                &self.t_acc_new,
                &verifier_challenge,
            )
            .unwrap();
        assert!(
            self.resp_null
                .verify(&g, &self.nullifier, &self.nullifier, &verifier_challenge,)
        );

        assert!(self.resp_leg_asset_id.verify(
            &leg_enc.ct_asset_id.encrypted,
            &leg_enc.ct_asset_id.eph_pk,
            &h,
            &verifier_challenge
        ));
        assert!(self.resp_leg_pk.verify(
            &leg_enc.ct_s.encrypted,
            &leg_enc.ct_s.eph_pk,
            &g,
            &verifier_challenge
        ));

        // Sk and asset id in leaf match the ones in updated account commitment
        assert_eq!(self.resp_leaf.0[0], self.resp_acc_new.0[0]);
        assert_eq!(self.resp_leaf.0[3], self.resp_acc_new.0[3]);
        // Balance in leaf (old account) is same as in the updated account commitment
        assert_eq!(self.resp_leaf.0[1], self.resp_acc_new.0[1]);

        // Counter in new account commitment is 1 less than the one in the leaf commitment
        assert_eq!(
            self.resp_acc_new.0[2] + verifier_challenge,
            self.resp_leaf.0[2]
        );

        // Sk and rho match the ones in nullifier
        assert_eq!(self.resp_leaf.0[0], self.resp_null.response1);
        assert_eq!(self.resp_leaf.0[4], self.resp_null.response2);

        // Asset id in leg is same as in account commitment
        assert_eq!(self.resp_leg_asset_id.response2, self.resp_acc_new.0[3]);

        // sk in account comm matches the one in pk
        assert_eq!(self.resp_leg_pk.response2, self.resp_leaf.0[0]);

        // sk_e matches in both encryptions
        assert_eq!(self.resp_leg_pk.response1, self.resp_leg_asset_id.response1);

        odd_verifier.verify(
            &self.odd_proof,
            &account_tree_params.odd_parameters.pc_gens,
            &account_tree_params.odd_parameters.bp_gens,
        )?;
        even_verifier.verify(
            &self.even_proof,
            &account_tree_params.even_parameters.pc_gens,
            &account_tree_params.even_parameters.bp_gens,
        )?;
        Ok(())
    }
}

/// This is the proof for doing proof of balance with an auditor. Report section 5.1.10, fig 8
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PobWithAuditorProof<G: AffineRepr> {
    nullifier: G,
    t_acc: G,
    pub resp_acc: SchnorrResponse<G>,
    pub resp_null: PokPedersenCommitment<G>,
    pub resp_pk: PokDiscreteLog<G>,
}

impl<G: AffineRepr> PobWithAuditorProof<G> {
    pub fn new<R: RngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: &[G],
        g: G,
    ) -> (Self, G::ScalarField) {
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. nullifier is created from rho and sk in account commitment
        //
        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. If its not possible then do a membership proof

        let mut prover_transcript = MerlinTranscript::new(b"test");

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        pk.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();

        prover_transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&g);

        let sk_blinding = G::ScalarField::rand(rng);
        let rho_blinding = G::ScalarField::rand(rng);

        let t_acc = SchnorrCommitment::new(
            &[
                account_comm_key[0],
                account_comm_key[4],
                account_comm_key[5],
            ],
            vec![sk_blinding, rho_blinding, G::ScalarField::rand(rng)],
        );
        let t_null = PokPedersenCommitmentProtocol::init(
            account.sk,
            sk_blinding,
            &nullifier,
            account.rho,
            rho_blinding,
            &nullifier,
        );
        let t_pk = PokDiscreteLogProtocol::init(account.sk, sk_blinding, &g);

        t_acc
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_null
            .challenge_contribution(&nullifier, &nullifier, &g, &mut prover_transcript)
            .unwrap();
        t_pk.challenge_contribution(&g, &pk, &mut prover_transcript)
            .unwrap();

        let prover_challenge =
            prover_transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let resp_acc = t_acc
            .response(
                &[account.sk, account.rho, account.randomness],
                &prover_challenge,
            )
            .unwrap();
        let resp_null = t_null.gen_proof(&prover_challenge);
        let resp_pk = t_pk.gen_proof(&prover_challenge);
        (
            Self {
                nullifier,
                t_acc: t_acc.t,
                resp_acc,
                resp_null,
                resp_pk,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        prover_challenge: G::ScalarField,
        nonce: &[u8],
        account_comm_key: &[G],
        g: G,
    ) -> Result<(), R1CSError> {
        let mut verifier_transcript = MerlinTranscript::new(b"test");

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        pk.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();

        verifier_transcript
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        self.t_acc
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_null
            .challenge_contribution(
                &self.nullifier,
                &self.nullifier,
                &g,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_pk
            .challenge_contribution(&g, &pk, &mut verifier_transcript)
            .unwrap();

        let verifier_challenge =
            verifier_transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        let y = account_commitment.0.into_group()
            - (account_comm_key[1] * G::ScalarField::from(balance)
                + account_comm_key[2] * G::ScalarField::from(counter)
                + account_comm_key[3] * G::ScalarField::from(asset_id));
        self.resp_acc
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[4],
                    account_comm_key[5],
                ],
                &y.into_affine(),
                &self.t_acc,
                &verifier_challenge,
            )
            .unwrap();
        assert!(
            self.resp_null
                .verify(&g, &self.nullifier, &self.nullifier, &verifier_challenge,)
        );
        assert!(self.resp_pk.verify(&pk, &g, &verifier_challenge));

        // Sk and rho match the ones in nullifier
        assert_eq!(self.resp_acc.0[0], self.resp_null.response1);
        assert_eq!(self.resp_acc.0[1], self.resp_null.response2);
        // Sk in account matches the one in public key
        assert_eq!(self.resp_acc.0[0], self.resp_pk.response);
        Ok(())
    }
}

/// This is the proof for doing proof of balance with an arbitrary party. Report section 5.1.11, fig 10
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PobWithAnyoneProof<G: AffineRepr> {
    nullifier: G,
    t_acc: G,
    pub resp_acc: SchnorrResponse<G>,
    pub resp_null: PokPedersenCommitment<G>,
    pub resp_pk: PokDiscreteLog<G>,
    pub t_sent_amount: G,
    pub t_recv_amount: G,
    pub resp_asset_id: Vec<PokDiscreteLog<G>>,
    pub resp_pk_send: BTreeMap<usize, PokPedersenCommitment<G>>,
    pub resp_pk_recv: BTreeMap<usize, PokPedersenCommitment<G>>,
    pub resp_recv_amount: SchnorrResponse<G>,
    pub resp_sent_amount: SchnorrResponse<G>,
}

impl<G: AffineRepr> PobWithAnyoneProof<G> {
    pub fn new<R: RngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        // Next few fields args can be abstracted in a single argument. Like a map with key as index and value as legs, keys, etc for that index
        legs: Vec<(Leg<G>, LegEncryption<G>, LegEncryptionRandomness<G>)>,
        eph_keys: Vec<(G::ScalarField, G)>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: &[G],
        g: G,
        h: G,
    ) -> (Self, G::ScalarField) {
        assert_eq!(legs.len(), eph_keys.len());
        assert_eq!(
            legs.len(),
            sender_in_leg_indices.len() + receiver_in_leg_indices.len()
        );

        let num_pending_txns = legs.len();
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. counter equals number of leg encryptions
        // 3. pk has the respective role in each leg
        // 4. asset is the given one in all legs
        // 5. sum of amounts in pending send txns equals the given public value
        // 6. sum of amounts in pending receive txns equals the given public value
        // 7. nullifier is created from rho and sk in account commitment

        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. If its not possible then do a membership proof

        let h_at = h * G::ScalarField::from(account.asset_id);

        let mut prover_transcript = MerlinTranscript::new(b"test");

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        pending_sent_amount
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        pending_recv_amount
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        account
            .asset_id
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        account
            .balance
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        account
            .counter
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        h_at.serialize_compressed(&mut extra_instance).unwrap();
        for l in &legs {
            l.1.serialize_compressed(&mut extra_instance).unwrap();
        }
        pk.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        prover_transcript.append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier = account.nullifier(&g);

        let sk_blinding = G::ScalarField::rand(rng);
        let rho_blinding = G::ScalarField::rand(rng);

        let mut sk_e_blindings = vec![];
        // TODO: Check if batching asset-id checks in single equation (as asset-id is same and public) is any faster than doing the randomized check over the complete protocol

        // For proving correctness of Elgamal ciphertext of asset-id
        let mut t_asset_id = vec![];

        // For proving correctness of Elgamal ciphertext of sender public key. Used when prover is sender.
        let mut t_pk_send = BTreeMap::new();
        // For proving correctness of Elgamal ciphertext of sender public key. Used when prover is receiver.
        let mut t_pk_recv = BTreeMap::new();

        // For proving correctness of Elgamal ciphertext of amount where prover is sender. Will be used in MSM later.
        let mut t_sent_points = vec![];
        let mut t_sent_scalars = vec![];

        // For proving correctness of Elgamal ciphertext of amount where prover is receiver. Will be used in MSM later.
        let mut t_recv_points = vec![];
        let mut t_recv_scalars = vec![];

        // Ephmeral keys where prover is sender
        let mut send_sk_e = vec![];
        // Ephmeral keys where prover is receiver
        let mut recv_sk_e = vec![];

        let t_acc = SchnorrCommitment::new(
            &[
                account_comm_key[0],
                account_comm_key[4],
                account_comm_key[5],
            ],
            vec![sk_blinding, rho_blinding, G::ScalarField::rand(rng)],
        );
        let t_null = PokPedersenCommitmentProtocol::init(
            account.sk,
            sk_blinding,
            &nullifier,
            account.rho,
            rho_blinding,
            &nullifier,
        );
        // To prove secret key in account state is same as in public key
        let t_pk = PokDiscreteLogProtocol::init(account.sk, sk_blinding, &g);

        for i in 0..num_pending_txns as usize {
            let sk_e_blinding = G::ScalarField::rand(rng);

            let t_leg_asset_id = PokDiscreteLogProtocol::init(
                eph_keys[i].0,
                sk_e_blinding,
                &legs[i].1.ct_asset_id.eph_pk,
            );

            if receiver_in_leg_indices.contains(&i) {
                let t_leg_pk = PokPedersenCommitmentProtocol::init(
                    eph_keys[i].0,
                    sk_e_blinding,
                    &legs[i].1.ct_r.eph_pk,
                    account.sk,
                    sk_blinding,
                    &g,
                );
                t_pk_recv.insert(i, t_leg_pk);
                t_recv_points.push(legs[i].1.ct_amount.eph_pk);
                t_recv_scalars.push(sk_e_blinding);
                recv_sk_e.push(eph_keys[i].0);
            } else if sender_in_leg_indices.contains(&i) {
                let t_leg_pk = PokPedersenCommitmentProtocol::init(
                    eph_keys[i].0,
                    sk_e_blinding,
                    &legs[i].1.ct_s.eph_pk,
                    account.sk,
                    sk_blinding,
                    &g,
                );
                t_pk_send.insert(i, t_leg_pk);
                t_sent_points.push(legs[i].1.ct_amount.eph_pk);
                t_sent_scalars.push(sk_e_blinding);
                send_sk_e.push(eph_keys[i].0);
            } else {
                panic!("Could not find index {i} in sent or recv")
            }

            t_asset_id.push(t_leg_asset_id);
            sk_e_blindings.push(sk_e_blinding);
        }

        let t_sent_amount = SchnorrCommitment::new(&t_sent_points, t_sent_scalars);
        let t_recv_amount = SchnorrCommitment::new(&t_recv_points, t_recv_scalars);

        t_acc
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_null
            .challenge_contribution(&nullifier, &nullifier, &g, &mut prover_transcript)
            .unwrap();
        t_pk.challenge_contribution(&g, &pk, &mut prover_transcript)
            .unwrap();

        for i in 0..num_pending_txns as usize {
            let y = legs[i].1.ct_asset_id.encrypted.into_group() - h_at;
            t_asset_id[i]
                .challenge_contribution(
                    &legs[i].1.ct_asset_id.eph_pk,
                    &y.into_affine(),
                    &mut prover_transcript,
                )
                .unwrap();
            if receiver_in_leg_indices.contains(&i) {
                t_pk_recv
                    .get(&i)
                    .unwrap()
                    .challenge_contribution(
                        &legs[i].1.ct_r.eph_pk,
                        &g,
                        &legs[i].1.ct_r.encrypted,
                        &mut prover_transcript,
                    )
                    .unwrap();
            } else if sender_in_leg_indices.contains(&i) {
                t_pk_send
                    .get(&i)
                    .unwrap()
                    .challenge_contribution(
                        &legs[i].1.ct_s.eph_pk,
                        &g,
                        &legs[i].1.ct_s.encrypted,
                        &mut prover_transcript,
                    )
                    .unwrap();
            } else {
                panic!("Could not find index {i} in sent or recv")
            }
        }

        t_sent_amount
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_recv_amount
            .challenge_contribution(&mut prover_transcript)
            .unwrap();

        let prover_challenge =
            prover_transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let mut resp_pk_send = BTreeMap::new();
        let mut resp_pk_recv = BTreeMap::new();
        let mut resp_asset_id = vec![];

        // TODO: Eliminate duplicate responses
        let resp_acc = t_acc
            .response(
                &[account.sk, account.rho, account.randomness],
                &prover_challenge,
            )
            .unwrap();
        let resp_null = t_null.gen_proof(&prover_challenge);
        let resp_pk = t_pk.gen_proof(&prover_challenge);

        for i in 0..num_pending_txns {
            resp_asset_id.push(t_asset_id[i].clone().gen_proof(&prover_challenge));
            if receiver_in_leg_indices.contains(&i) {
                resp_pk_recv.insert(
                    i,
                    t_pk_recv
                        .get(&i)
                        .unwrap()
                        .clone()
                        .gen_proof(&prover_challenge),
                );
            } else if sender_in_leg_indices.contains(&i) {
                resp_pk_send.insert(
                    i,
                    t_pk_send
                        .get(&i)
                        .unwrap()
                        .clone()
                        .gen_proof(&prover_challenge),
                );
            } else {
                panic!("Could not find index {i} in sent or recv")
            }
        }

        let resp_sent_amount = t_sent_amount
            .response(&send_sk_e, &prover_challenge)
            .unwrap();
        let resp_recv_amount = t_recv_amount
            .response(&recv_sk_e, &prover_challenge)
            .unwrap();
        (
            Self {
                nullifier,
                t_acc: t_acc.t,
                resp_acc,
                resp_null,
                resp_pk,
                t_sent_amount: t_sent_amount.t,
                t_recv_amount: t_recv_amount.t,
                resp_asset_id,
                resp_pk_recv,
                resp_pk_send,
                resp_recv_amount,
                resp_sent_amount,
            },
            prover_challenge,
        )
    }

    pub fn verify(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        legs: Vec<LegEncryption<G>>,
        prover_challenge: G::ScalarField,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: &[G],
        g: G,
        h: G,
    ) -> Result<(), R1CSError> {
        assert_eq!(legs.len(), self.resp_asset_id.len());
        assert_eq!(sender_in_leg_indices.len(), self.resp_pk_send.len());
        assert_eq!(receiver_in_leg_indices.len(), self.resp_pk_recv.len());
        assert_eq!(sender_in_leg_indices.len(), self.resp_sent_amount.0.len());
        assert_eq!(receiver_in_leg_indices.len(), self.resp_recv_amount.0.len());

        let num_pending_txns = legs.len();

        let mut verifier_transcript = MerlinTranscript::new(b"test");

        let h_at = h * G::ScalarField::from(asset_id);

        let mut extra_instance = vec![];
        nonce.serialize_compressed(&mut extra_instance).unwrap();
        account_commitment
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        pending_sent_amount
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        pending_recv_amount
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        asset_id.serialize_compressed(&mut extra_instance).unwrap();
        balance.serialize_compressed(&mut extra_instance).unwrap();
        counter.serialize_compressed(&mut extra_instance).unwrap();
        h_at.serialize_compressed(&mut extra_instance).unwrap();
        for l in &legs {
            l.serialize_compressed(&mut extra_instance).unwrap();
        }
        pk.serialize_compressed(&mut extra_instance).unwrap();
        account_comm_key
            .serialize_compressed(&mut extra_instance)
            .unwrap();
        g.serialize_compressed(&mut extra_instance).unwrap();
        h.serialize_compressed(&mut extra_instance).unwrap();

        verifier_transcript
            .append_message_without_static_label(TXN_INSTANCE_LABEL, &extra_instance);

        // For proving correctness of Elgamal ciphertext of amount where prover is sender. Will be used in MSM later.
        let mut t_sent_points = vec![];

        // For proving correctness of Elgamal ciphertext of amount where prover is receiver. Will be used in MSM later.
        let mut t_recv_points = vec![];

        self.t_acc
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.resp_null
            .challenge_contribution(
                &self.nullifier,
                &self.nullifier,
                &g,
                &mut verifier_transcript,
            )
            .unwrap();
        self.resp_pk
            .challenge_contribution(&g, &pk, &mut verifier_transcript)
            .unwrap();

        for i in 0..num_pending_txns {
            let y = legs[i].ct_asset_id.encrypted.into_group() - h_at;
            self.resp_asset_id[i]
                .challenge_contribution(
                    &legs[i].ct_asset_id.eph_pk,
                    &y.into_affine(),
                    &mut verifier_transcript,
                )
                .unwrap();

            if receiver_in_leg_indices.contains(&i) {
                t_recv_points.push(legs[i].ct_amount.eph_pk);

                self.resp_pk_recv
                    .get(&i)
                    .unwrap()
                    .challenge_contribution(
                        &legs[i].ct_r.eph_pk,
                        &g,
                        &legs[i].ct_r.encrypted,
                        &mut verifier_transcript,
                    )
                    .unwrap();
            } else if sender_in_leg_indices.contains(&i) {
                t_sent_points.push(legs[i].ct_amount.eph_pk);

                self.resp_pk_send
                    .get(&i)
                    .unwrap()
                    .challenge_contribution(
                        &legs[i].ct_s.eph_pk,
                        &g,
                        &legs[i].ct_s.encrypted,
                        &mut verifier_transcript,
                    )
                    .unwrap();
            } else {
                panic!("Could not find index {i} in sent or recv")
            }
        }

        self.t_sent_amount
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();
        self.t_recv_amount
            .serialize_compressed(&mut verifier_transcript)
            .unwrap();

        let verifier_challenge =
            verifier_transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        assert_eq!(verifier_challenge, prover_challenge);

        let y = account_commitment.0.into_group()
            - (account_comm_key[1] * G::ScalarField::from(balance)
                + account_comm_key[2] * G::ScalarField::from(counter)
                + account_comm_key[3] * G::ScalarField::from(asset_id));
        self.resp_acc
            .is_valid(
                &[
                    account_comm_key[0],
                    account_comm_key[4],
                    account_comm_key[5],
                ],
                &y.into_affine(),
                &self.t_acc,
                &verifier_challenge,
            )
            .unwrap();
        assert!(
            self.resp_null
                .verify(&g, &self.nullifier, &self.nullifier, &verifier_challenge,)
        );
        assert!(self.resp_pk.verify(&pk, &g, &verifier_challenge));

        let mut y_recv = G::Group::zero();
        let mut y_sent = G::Group::zero();
        for i in 0..num_pending_txns as usize {
            // TODO: This `y` is already computed above so avoid
            let y = legs[i].ct_asset_id.encrypted.into_group() - h_at;
            assert!(self.resp_asset_id[i].verify(
                &y.into_affine(),
                &legs[i].ct_asset_id.eph_pk,
                &verifier_challenge
            ));

            if receiver_in_leg_indices.contains(&i) {
                assert!(self.resp_pk_recv.get(&i).unwrap().verify(
                    &legs[i].ct_r.encrypted,
                    &legs[i].ct_r.eph_pk,
                    &g,
                    &verifier_challenge
                ));
                y_recv += &legs[i].ct_amount.encrypted;
            } else if sender_in_leg_indices.contains(&i) {
                assert!(self.resp_pk_send.get(&i).unwrap().verify(
                    &legs[i].ct_s.encrypted,
                    &legs[i].ct_s.eph_pk,
                    &g,
                    &verifier_challenge
                ));
                y_sent += &legs[i].ct_amount.encrypted;
            } else {
                panic!("Could not find index {i} in sent or recv")
            }
        }

        y_sent -= h * G::ScalarField::from(pending_sent_amount);
        self.resp_sent_amount
            .is_valid(
                &t_sent_points,
                &y_sent.into_affine(),
                &self.t_sent_amount,
                &verifier_challenge,
            )
            .unwrap();

        y_recv -= h * G::ScalarField::from(pending_recv_amount);
        self.resp_recv_amount
            .is_valid(
                &t_recv_points,
                &y_recv.into_affine(),
                &self.t_recv_amount,
                &verifier_challenge,
            )
            .unwrap();

        // Sk and rho match the ones in nullifier
        assert_eq!(self.resp_acc.0[0], self.resp_null.response1);
        assert_eq!(self.resp_acc.0[1], self.resp_null.response2);
        // Sk in account matches the one in public key
        assert_eq!(self.resp_acc.0[0], self.resp_pk.response);

        let mut resp_recv_amount_offset = 0;
        let mut resp_send_amount_offset = 0;
        for i in 0..num_pending_txns as usize {
            // TODO: Question: Do i need these checks since if a leg is on chain, its assumed to be valid.
            if receiver_in_leg_indices.contains(&i) {
                // sk_e is same
                assert_eq!(
                    self.resp_pk_recv.get(&i).unwrap().response1,
                    self.resp_asset_id[i].response
                );
                assert_eq!(
                    self.resp_pk_recv.get(&i).unwrap().response1,
                    self.resp_recv_amount.0[resp_recv_amount_offset]
                );
                resp_recv_amount_offset += 1;
                // sk is same
                assert_eq!(
                    self.resp_pk_recv.get(&i).unwrap().response2,
                    self.resp_acc.0[0]
                );
            } else if sender_in_leg_indices.contains(&i) {
                // sk_e is same
                assert_eq!(
                    self.resp_pk_send.get(&i).unwrap().response1,
                    self.resp_asset_id[i].response
                );
                assert_eq!(
                    self.resp_pk_send.get(&i).unwrap().response1,
                    self.resp_sent_amount.0[resp_send_amount_offset]
                );
                resp_send_amount_offset += 1;
                // sk is same
                assert_eq!(
                    self.resp_pk_send.get(&i).unwrap().response2,
                    self.resp_acc.0[0]
                );
            } else {
                panic!("Could not find index {i} in sent or recv")
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::leg::tests::setup_keys;
    use crate::leg::{Leg, initialize_leg_for_settlement};
    use crate::old::keys::{keygen_enc, keygen_sig};
    use ark_ec::CurveGroup;
    use ark_serialize::CanonicalSerialize;
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use curve_tree_relations::curve_tree::{CurveTree, SelRerandParameters};
    use std::collections::BTreeSet;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type VestaA = ark_vesta::Affine;

    /// Create a new tree and add the given account's commitment to the tree and return the tree
    /// In future, allow to generate tree many given number of leaves and add the account commitment to a
    /// random position in tree.
    fn get_tree_with_account_comm<const L: usize>(account: &AccountState<PallasA>, account_comm_key: &[PallasA], account_tree_params: &SelRerandParameters<PallasParameters, VestaParameters>) -> CurveTree<L, 1, PallasParameters, VestaParameters> {
        let account_comm = account.commit(&account_comm_key);

        // Add account commitment in curve tree
        let set = vec![account_comm.0];
        CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            account_tree_params,
            Some(4),
        )
    }

    #[test]
    fn register_and_increase_supply_txns() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_p = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();

        let asset_id = 1;

        // Issuer creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, gen_p);
        // Issuer creates account to mint to
        // Knowledge and correctness (both balance and counter 0, sk-pk relation) can be proven using Schnorr protocol
        let account = AccountState::new(&mut rng, sk_i.0, asset_id);

        let account_tree = get_tree_with_account_comm::<L>(&account, &account_comm_key, &account_tree_params);

        // Setup ends. Issuer and verifier interaction begins below

        let increase_bal_by = 10;

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_mint(&mut rng, increase_bal_by);
        let updated_account_comm = updated_account.commit(&account_comm_key);

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let (proof, prover_challenge) = MintTxnProof::new(
            &mut rng,
            pk_i.0,
            asset_id,
            increase_bal_by,
            &account,
            &updated_account,
            updated_account_comm,
            path,
            nonce,
            &account_tree_params,
            &account_comm_key,
            gen_p,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                pk_i.0,
                asset_id,
                increase_bal_by,
                &account_tree,
                prover_challenge,
                nonce,
                &account_tree_params,
                &account_comm_key,
                gen_p,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

    #[test]
    fn send_txn() {
        let mut rng = rand::thread_rng();

        // Setup begins

        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;

        // Create public params (generators, etc)
        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let leaf_comm_key = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;
        let amount = 100;

        // Venue has successfully created the settlement and leg commitment has been stored on chain
        let (leg, leg_enc, leg_enc_rand, eph_sk_enc, eph_sk_enc_rand, sk_e, pk_e) =
            initialize_leg_for_settlement::<_, _, Blake2b512>(
                &mut rng,
                asset_id,
                amount,
                (pk_s.0, pk_s_e.0),
                (pk_r.0, pk_r_e.0),
                (pk_a.0, pk_a_e.0),
                gen_p_1,
                gen_p_2,
            );

        // Sender account
        let mut account = AccountState::new(&mut rng, sk_s.0, asset_id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;
        let account_tree = get_tree_with_account_comm::<L>(&account, &account_comm_key, &account_tree_params);

        // Setup ends. Sender and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_send(&mut rng, amount);
        let updated_account_comm = updated_account.commit(&account_comm_key);

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let (proof, prover_challenge) = SendTxnProof::new(
            &mut rng,
            asset_id,
            amount,
            sk_e.0,
            leg_enc.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            nonce,
            &account_tree_params,
            &account_comm_key,
            gen_p_1,
            gen_p_2,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                leg_enc,
                &account_tree,
                prover_challenge,
                nonce,
                &account_tree_params,
                &account_comm_key,
                gen_p_1,
                gen_p_2,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

    #[test]
    fn receive_txn() {
        let mut rng = rand::thread_rng();

        // Setup beings

        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;

        // Create public params (generators, etc)

        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let leaf_comm_key = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();

        // All parties generate their keys
        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;
        let amount = 100;

        // Venue has successfully created the settlement and leg commitment has been stored on chain
        let (leg, leg_enc, leg_enc_rand, eph_sk_enc, eph_sk_enc_rand, sk_e, pk_e) =
            initialize_leg_for_settlement::<_, _, Blake2b512>(
                &mut rng,
                asset_id,
                amount,
                (pk_s.0, pk_s_e.0),
                (pk_r.0, pk_r_e.0),
                (pk_a.0, pk_a_e.0),
                gen_p_1,
                gen_p_2,
            );

        // Receiver account
        let mut account = AccountState::new(&mut rng, sk_r.0, asset_id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;
        let account_tree = get_tree_with_account_comm::<L>(&account, &account_comm_key, &account_tree_params);

        // Setup ends. Receiver and verifier interaction begins below

        let nonce = b"test-nonce";

        let clock = Instant::now();
        let updated_account = account.get_state_for_receive(&mut rng);
        let updated_account_comm = updated_account.commit(&account_comm_key);

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let (proof, prover_challenge) = ReceiveTxnProof::new(
            &mut rng,
            asset_id,
            sk_e.0,
            leg_enc.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            nonce,
            &account_tree_params,
            &account_comm_key,
            gen_p_1,
            gen_p_2,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                leg_enc,
                &account_tree,
                prover_challenge,
                nonce,
                &account_tree_params,
                &account_comm_key,
                gen_p_1,
                gen_p_2,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

    #[test]
    fn claim_received_funds() {
        // This is what report calls txn_cu (counter update) done by receiver
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;

        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let leaf_comm_key = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();

        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;
        let amount = 100;

        // Venue has successfully created the settlement and leg commitment has been stored on chain
        let (leg, leg_enc, _, _, _, sk_e, pk_e) = initialize_leg_for_settlement::<_, _, Blake2b512>(
            &mut rng,
            asset_id,
            amount,
            (pk_s.0, pk_s_e.0),
            (pk_r.0, pk_r_e.0),
            (pk_a.0, pk_a_e.0),
            gen_p_1,
            gen_p_2,
        );

        // Receiver account
        let mut account = AccountState::new(&mut rng, sk_r.0, asset_id);
        // Assume that account had some balance and it had sent the receive transaction to increase its counter
        account.balance = 200;
        account.counter += 1;

        let account_tree = get_tree_with_account_comm::<L>(&account, &account_comm_key, &account_tree_params);

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_claiming_received(&mut rng, amount);
        let updated_account_comm = updated_account.commit(&account_comm_key);

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let (proof, prover_challenge) = ClaimReceivedTxnProof::new(
            &mut rng,
            asset_id,
            amount,
            sk_e.0,
            sk_r.0,
            leg_enc.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            nonce,
            &account_tree_params,
            &account_comm_key,
            gen_p_1,
            gen_p_2,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                leg_enc,
                &account_tree,
                prover_challenge,
                nonce,
                &account_tree_params,
                &account_comm_key,
                gen_p_1,
                gen_p_2,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

    #[test]
    fn reverse_send_txn() {
        let mut rng = rand::thread_rng();


        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;

        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();

        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;
        let amount = 100;

        // Venue has successfully created the settlement and leg commitment has been stored on chain
        let (leg, leg_enc, _, _, _, sk_e, pk_e) = initialize_leg_for_settlement::<_, _, Blake2b512>(
            &mut rng,
            asset_id,
            amount,
            (pk_s.0, pk_s_e.0),
            (pk_r.0, pk_r_e.0),
            (pk_a.0, pk_a_e.0),
            gen_p_1,
            gen_p_2,
        );

        // Sender account
        let mut account = AccountState::new(&mut rng, sk_s.0, asset_id);
        // Assume that account had some balance and it had sent the send transaction to increase its counter
        account.balance = 200;
        account.counter += 1;

        let account_tree = get_tree_with_account_comm::<L>(&account, &account_comm_key, &account_tree_params);

        let nonce = b"test-nonce";

        let clock = Instant::now();
        let updated_account = account.get_state_for_reversing_send(&mut rng, amount);
        let updated_account_comm = updated_account.commit(&account_comm_key);

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let (proof, prover_challenge) = SenderReverseTxnProof::new(
            &mut rng,
            amount,
            sk_e.0,
            leg_enc.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            nonce,
            &account_tree_params,
            &account_comm_key,
            gen_p_1,
            gen_p_2,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                leg_enc,
                &account_tree,
                prover_challenge,
                nonce,
                &account_tree_params,
                &account_comm_key,
                gen_p_1,
                gen_p_2,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

    #[test]
    fn counter_update_txn_by_sender() {
        // This is similar to receive txn as only account's counter is decreased, balance remains same.

        let mut rng = rand::thread_rng();


        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;

        let account_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let leaf_comm_key = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();

        let (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        ) = setup_keys(&mut rng, gen_p_1);

        let asset_id = 1;
        let amount = 100;

        // The txn with this leg has been executed by the chain and now sender wants to decrease its counter for this
        let (_, leg_enc, _, _, _, sk_e, _) = initialize_leg_for_settlement::<_, _, Blake2b512>(
            &mut rng,
            asset_id,
            amount,
            (pk_s.0, pk_s_e.0),
            (pk_r.0, pk_r_e.0),
            (pk_a.0, pk_a_e.0),
            gen_p_1,
            gen_p_2,
        );

        // Sender account with non-zero counter
        let mut account = AccountState::new(&mut rng, sk_s.0, asset_id);
        account.balance = 50;
        account.counter = 1;

        let account_tree = get_tree_with_account_comm::<L>(&account, &account_comm_key, &account_tree_params);

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_decreasing_counter(&mut rng, None);
        let updated_account_comm = updated_account.commit(&account_comm_key);
        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let (proof, prover_challenge) = SenderCounterUpdateTxnProof::new(
            &mut rng,
            asset_id,
            sk_e.0,
            leg_enc.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            nonce,
            &account_tree_params,
            &account_comm_key,
            gen_p_1,
            gen_p_2,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                leg_enc,
                &account_tree,
                prover_challenge,
                nonce,
                &account_tree_params,
                &account_comm_key,
                gen_p_1,
                gen_p_2,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

    #[test]
    fn pob_with_auditor_as_verifier() {
        let mut rng = rand::thread_rng();

        // TODO: Generate by hashing public string
        let gen_p = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();

        let asset_id = 1;

        let (sk, pk) = keygen_sig(&mut rng, gen_p);
        // Account exists with some balance and pending txns
        let mut account = AccountState::new(&mut rng, sk.0, asset_id);
        account.balance = 1000;
        account.counter = 7;
        let account_comm = account.commit(&account_comm_key);

        let nonce = b"test-nonce";

        let (proof, prover_challenge) = PobWithAuditorProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            nonce,
            &account_comm_key,
            gen_p,
        );
        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                &pk.0,
                account_comm,
                prover_challenge,
                nonce,
                &account_comm_key,
                gen_p,
            )
            .unwrap();
    }

    #[test]
    fn pob_with_anyone() {
        let mut rng = rand::thread_rng();

        // TODO: Generate by hashing public string
        let gen_p_1 = PallasA::rand(&mut rng);
        let gen_p_2 = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();

        let asset_id = 1;

        let num_pending_txns = 10;

        let (sk, pk) = keygen_sig(&mut rng, gen_p_1);
        // Account exists with some balance and pending txns
        let mut account = AccountState::new(&mut rng, sk.0, asset_id);
        account.balance = 1000000;
        account.counter = num_pending_txns;
        let account_comm = account.commit(&account_comm_key);

        let (sk_other, pk_other) = keygen_sig(&mut rng, gen_p_1);
        let (sk_a, pk_a) = keygen_sig(&mut rng, gen_p_1);

        // Create some legs as pending transfers
        let mut legs = vec![];
        let mut eph_keys = vec![];
        // Set this amount in each leg. Just for testing, in practice it could be different
        let amount = 10;
        let mut pending_sent_amount = 0;
        let mut pending_recv_amount = 0;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();
        for i in 0..num_pending_txns as usize {
            // for odd i, account is sender, for even i, its receiver
            let (sk_e, pk_e) = keygen_enc(&mut rng, gen_p_1);
            let leg = if i % 2 == 0 {
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                Leg::new(pk_other.0, pk.0, pk_a.0, amount, asset_id)
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                Leg::new(pk.0, pk_other.0, pk_a.0, amount, asset_id)
            };
            let (leg_enc, enc_rands) = leg.encrypt(&mut rng, &pk_e.0, gen_p_1, gen_p_2);
            legs.push((leg, leg_enc, enc_rands));
            eph_keys.push((sk_e.0, pk_e.0));
        }

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let (proof, prover_challenge) = PobWithAnyoneProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            legs.clone(),
            eph_keys.clone(),
            sender_in_leg_indices.clone(),
            receiver_in_leg_indices.clone(),
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            &account_comm_key,
            gen_p_1,
            gen_p_2,
        );

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                &pk.0,
                account_comm,
                legs.into_iter().map(|l| l.1).collect(),
                prover_challenge,
                sender_in_leg_indices.clone(),
                receiver_in_leg_indices.clone(),
                pending_sent_amount,
                pending_recv_amount,
                nonce,
                &account_comm_key,
                gen_p_1,
                gen_p_2,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For {num_pending_txns} pending txns");
        println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }
}
