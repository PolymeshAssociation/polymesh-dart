use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{format, string::ToString, vec, vec::Vec};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizeMultiPathWithDivisorComms};
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use crate::account::state_transition::{AccountStateTransitionProof, AccountStateTransitionProofBuilder, AccountStateTransitionProofVerifier};
use crate::util::{get_verification_tuples_with_rng, handle_verification_tuples, prove_with_rng, BPProof};
use crate::{add_to_transcript, error::Result, Error, TXN_EVEN_LABEL, TXN_ODD_LABEL};
use crate::{RE_RANDOMIZED_PATH_LABEL, ROOT_LABEL};
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use crate::account::AccountCommitmentKeyTrait;
use ark_ec_divisors::DivisorCurve;
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;

/// Combined proof for state transitions across multiple accounts (multiple assets).
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct MultiAssetStateTransitionProof<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// Individual account state transition proofs
    pub account_proofs: Vec<AccountStateTransitionProof<L, F0, F1, G0, G1>>,
    /// Collection of re-randomized paths for all accounts in batches of size at most M
    pub re_randomized_paths: Vec<SelectAndRerandomizeMultiPathWithDivisorComms<L, M, G0, G1>>,
    /// When this is None, external [`R1CSProof`] will be used
    pub r1cs_proof: Option<BPProof<G0, G1>>,
}

impl<
    const L: usize,
    const M: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> MultiAssetStateTransitionProof<L, M, F0, F1, G0, G1>
{
    pub fn new<
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
        D1: DivisorCurve<BaseField = F0, ScalarField = F1> + From<Projective<G1>>,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        account_builders: Vec<AccountStateTransitionProofBuilder<L, F0, F1, G0, G1>>,
        leaf_paths: Vec<CurveTreeWitnessMultiPath<L, M, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, Vec<Affine<G0>>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens(),
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens(), odd_transcript);

        let (mut proof, nullifiers) = Self::new_with_given_prover::<_, D0, D1, Parameters0, Parameters1>(
            rng,
            account_builders,
            leaf_paths,
            tree_root,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            &mut even_prover,
            &mut odd_prover,
        )?;

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params.even_parameters.bp_gens(), &account_tree_params.odd_parameters.bp_gens(), rng)?;

        proof.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });
        Ok((proof, nullifiers))
    }

    pub fn new_with_given_prover<
        'a,
        R: CryptoRngCore,
        D0: DivisorCurve<BaseField = F1, ScalarField = F0> + From<Projective<G0>>,
        D1: DivisorCurve<BaseField = F0, ScalarField = F1> + From<Projective<G1>>,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        account_builders: Vec<AccountStateTransitionProofBuilder<L, F0, F1, G0, G1>>,
        leaf_paths: Vec<CurveTreeWitnessMultiPath<L, M, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_prover: &mut Prover<'a, MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<'a, MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Vec<Affine<G0>>)> {
        let num_accounts = account_builders.len();
        if num_accounts == 0 {
            return Err(Error::ProofGenerationError(
                "At least one account is required to create a multi-asset state transition proof"
                    .to_string(),
            ));
        }

        if leaf_paths
            .iter()
            .fold(0, |acc, path| acc + path.num_indices())
            != num_accounts as u32
        {
            return Err(Error::ProofGenerationError(
                "Total number of paths in leaf_paths does not match number of accounts".to_string(),
            ));
        }

        add_to_transcript!(even_prover.transcript(), ROOT_LABEL, tree_root);

        // Batch the curve tree operations for all accounts
        let mut re_randomized_paths = Vec::with_capacity(leaf_paths.len());
        let mut rerandomized_leaves_and_randomizers = Vec::with_capacity(num_accounts);

        for leaf_path in leaf_paths.iter() {
            let (re_randomized_path, randomizers_of_leaves) = leaf_path
                .batched_select_and_rerandomize_prover_gadget_new::<R, D0, D1, Parameters0, Parameters1>(
                    even_prover,
                    odd_prover,
                    account_tree_params,
                    rng,
                )?;

            add_to_transcript!(
                even_prover.transcript(),
                RE_RANDOMIZED_PATH_LABEL,
                re_randomized_path
            );

            let rerandomized_leaves = re_randomized_path.path.get_rerandomized_leaves();
            rerandomized_leaves_and_randomizers.append(
                &mut (rerandomized_leaves
                    .into_iter()
                    .zip(randomizers_of_leaves)
                    .map(|(l, r)| (l, r))
                    .collect::<Vec<_>>()),
            );
            re_randomized_paths.push(re_randomized_path);
        }

        debug_assert!(rerandomized_leaves_and_randomizers.len() == num_accounts);

        // Create individual account state transition proofs using the pre-computed rerandomized leaves
        let mut account_proofs = Vec::with_capacity(num_accounts);
        let mut nullifiers = Vec::with_capacity(num_accounts);

        for (i, builder) in account_builders.into_iter().enumerate() {
            // Finalize with pre-computed rerandomized leaf
            // Note: nonce and updated_account_commitment are added to transcript inside finalize_with_given_prover_with_rerandomized_leaf
            let (proof, nullifier) = builder.finalize_with_given_prover_with_rerandomized_leaf_new::<_, D0, D1, Parameters0, Parameters1>(
                rng,
                rerandomized_leaves_and_randomizers[i].1, // Extract just the scalar randomization
                account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                even_prover,
            )?;

            account_proofs.push(proof);
            nullifiers.push(nullifier);
        }

        Ok((
            Self {
                account_proofs,
                re_randomized_paths,
                r1cs_proof: None,
            },
            nullifiers,
        ))
    }

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        rng: &mut R,
        account_verifiers: Vec<AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple) = self.verify_and_return_tuples::<_, Parameters0, Parameters1>(
            account_verifiers,
            tree_root,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            rng,
            rmc_0,
        )?;

        handle_verification_tuples(
            even_tuple, odd_tuple, account_tree_params, rmc
        )
    }

    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        account_verifiers: Vec<AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(even_transcript);
        let mut odd_verifier = Verifier::new(odd_transcript);

        self.enforce_constraints_and_verify_only_sigma_protocols::<Parameters0, Parameters1>(
            account_verifiers,
            tree_root,
            account_tree_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            &mut even_verifier,
            &mut odd_verifier,
            rmc,
        )?;

        let r1cs_proof = self
            .r1cs_proof
            .as_ref()
            .ok_or_else(|| Error::ProofVerificationError("R1CS proof is missing".to_string()))?;

        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )
    }

    pub fn enforce_constraints_and_verify_only_sigma_protocols<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        account_verifiers: Vec<AccountStateTransitionProofVerifier<L, F0, F1, G0, G1>>,
        tree_root: &Root<L, M, G0, G1>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        if self.account_proofs.len() != account_verifiers.len() {
            return Err(Error::ProofVerificationError(format!(
                "Number of proofs ({}) does not match number of verifiers ({})",
                self.account_proofs.len(),
                account_verifiers.len()
            )));
        }

        add_to_transcript!(even_verifier.transcript(), ROOT_LABEL, tree_root,);

        // Verify batched curve tree operations
        let mut rerandomized_leaves = Vec::with_capacity(self.account_proofs.len());
        for re_randomized_path in &self.re_randomized_paths {
            re_randomized_path.batched_select_and_rerandomize_verifier_gadget::<Parameters0, Parameters1>(
                tree_root,
                even_verifier,
                odd_verifier,
                account_tree_params,
            )?;

            add_to_transcript!(
                even_verifier.transcript(),
                RE_RANDOMIZED_PATH_LABEL,
                re_randomized_path
            );

            rerandomized_leaves.extend(re_randomized_path.path.get_rerandomized_leaves());
        }

        debug_assert!(rerandomized_leaves.len() == self.account_proofs.len());

        // Verify each account state transition proof
        for (i, verifier) in account_verifiers.into_iter().enumerate() {
            let proof = &self.account_proofs[i];

            // Reborrow rmc for each iteration
            let rmc_for_this_iteration = match rmc.as_mut() {
                Some(rmc_ref) => Some(&mut **rmc_ref),
                None => None,
            };

            // Verify with pre-computed rerandomized leaf
            verifier.enforce_constraints_and_verify_only_sigma_protocols_with_rerandomized_leaf_new(
                proof,
                rerandomized_leaves[i],
                account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                even_verifier,
                rmc_for_this_iteration,
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::account::AccountCommitmentKeyTrait;
    use crate::account::state::AccountStateBuilder;
    use crate::account_registration::tests::new_account;
    use crate::leg::tests::setup_keys;
    use ark_std::UniformRand;
    use rand::thread_rng;
    use std::time::Instant;
    use ark_ec_divisors::curves::{
        pallas::PallasParams, pallas::Point as PallasPoint, vesta::Point as VestaPoint,
        vesta::VestaParams,
    };
    use ark_pallas::{Fr as PallasFr, PallasConfig as PallasParameters};
    use ark_vesta::VestaConfig as VestaParameters;
    use crate::account::state_transition::{AccountStateTransitionProofBuilder, AccountStateTransitionProofVerifier};
    use crate::account::tests::{get_batched_tree_with_account_comms, setup_gens_new, setup_leg};

    #[test]
    fn test_multi_asset_state_transition_two_accounts() {
        // Alice and Bob both have 2 accounts, 1 per asset. In one leg, Alice is sending Bob asset 1 and in other leg Bob is sending Alice asset 2.
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 14;
        const L: usize = 64;
        const M: usize = 2;

        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"test");

        // Setup keys for Alice and Bob
        let (
            ((sk_alice, pk_alice), (_, pk_alice_e)),
            ((sk_bob, pk_bob), (_, pk_bob_e)),
            (_, (_, pk_auditor_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id_1 = 1u32;
        let asset_id_2 = 2u32;

        let alice_send_amount = 100u64; // Alice sends 100 of asset 1 to Bob
        let bob_send_amount = 200u64; // Bob sends 200 of asset 2 to Alice

        // Leg 1: Alice -> Bob (asset 1)
        let (_, leg_enc_1, leg_enc_rand_1) = setup_leg(
            &mut rng,
            pk_alice.0,
            pk_bob.0,
            pk_auditor_e.0,
            true,
            alice_send_amount,
            asset_id_1,
            pk_alice_e.0,
            pk_bob_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Leg 2: Bob -> Alice (asset 2)
        let (_, leg_enc_2, leg_enc_rand_2) = setup_leg(
            &mut rng,
            pk_bob.0,
            pk_alice.0,
            pk_auditor_e.0,
            true,
            bob_send_amount,
            asset_id_2,
            pk_bob_e.0,
            pk_alice_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Here the same keys are used but in practice, different accounts use different keys
        // Alice's account for asset 1
        let alice_id_1 = PallasFr::rand(&mut rng);
        let (mut alice_account_1, _, _) =
            new_account(&mut rng, asset_id_1, sk_alice.clone(), alice_id_1);
        alice_account_1.balance = 500;

        // Alice's account for asset 2
        let alice_id_2 = PallasFr::rand(&mut rng);
        let (mut alice_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_alice, alice_id_2);
        alice_account_2.balance = 300;

        // Bob's account for asset 1
        let bob_id_1 = PallasFr::rand(&mut rng);
        let (mut bob_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_bob.clone(), bob_id_1);
        bob_account_1.balance = 400;

        // Bob's account for asset 2
        let bob_id_2 = PallasFr::rand(&mut rng);
        let (mut bob_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_bob, bob_id_2);
        bob_account_2.balance = 800;

        let account_tree = get_batched_tree_with_account_comms::<L, M, _>(
            vec![
                &alice_account_1,
                &alice_account_2,
                &bob_account_1,
                &bob_account_2,
            ],
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let account_tree_root = account_tree.root_node();

        // Paths for Alice accounts
        let path_1 = account_tree.get_paths_to_leaves(&[0, 1]).unwrap();

        // Paths for Bob accounts
        let path_2 = account_tree.get_paths_to_leaves(&[2, 3]).unwrap();

        // Alice's asset 1 account after sending 100 to Bob
        let alice_account_1_updated = alice_account_1
            .get_state_for_send(alice_send_amount)
            .unwrap();
        let alice_account_1_updated_comm = alice_account_1_updated
            .commit(account_comm_key.clone())
            .unwrap();

        // Alice's asset 2 account after receiving affirmation from Bob
        let alice_account_2_updated = alice_account_2.get_state_for_receive();
        let alice_account_2_after_comm = alice_account_2_updated
            .commit(account_comm_key.clone())
            .unwrap();

        // Bob's asset 1 account after receiving affirmation from Alice
        let bob_account_1_updated = bob_account_1.get_state_for_receive();
        let bob_account_1_updated_comm = bob_account_1_updated
            .commit(account_comm_key.clone())
            .unwrap();

        // Bob's asset 2 account after sending 200 to Alice
        let bob_account_2_updated = bob_account_2.get_state_for_send(bob_send_amount).unwrap();
        let bob_account_2_updated_comm = bob_account_2_updated
            .commit(account_comm_key.clone())
            .unwrap();

        let alice_nonce = b"alice_nonce";
        let bob_nonce = b"bob_nonce";

        // Alice's builder for asset 1 account
        let mut alice_builder_1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_1.clone(),
                alice_account_1_updated.clone(),
                alice_account_1_updated_comm,
                alice_nonce,
            );
        alice_builder_1.add_send_affirmation(
            alice_send_amount,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
        );

        // Alice's builder for asset 2 account
        let mut alice_builder_2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_2.clone(),
                alice_account_2_updated.clone(),
                alice_account_2_after_comm,
                alice_nonce,
            );
        alice_builder_2.add_receive_affirmation(leg_enc_2.clone(), leg_enc_rand_2.clone());

        // Bob's builder for asset 1 account
        let mut bob_builder_1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_1.clone(),
                bob_account_1_updated.clone(),
                bob_account_1_updated_comm,
                bob_nonce,
            );
        bob_builder_1.add_receive_affirmation(leg_enc_1.clone(), leg_enc_rand_1.clone());

        // Bob's builder for asset 2 account
        let mut bob_builder_2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_2.clone(),
                bob_account_2_updated.clone(),
                bob_account_2_updated_comm,
                bob_nonce,
            );
        bob_builder_2.add_send_affirmation(
            bob_send_amount,
            leg_enc_2.clone(),
            leg_enc_rand_2.clone(),
        );

        // Alice create multi-asset proof
        let start = Instant::now();
        let (multi_asset_proof, nullifiers) =
            MultiAssetStateTransitionProof::<L, M, _, _, PallasParameters, VestaParameters>::new::<
                _,
                PallasPoint,
                VestaPoint,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                vec![alice_builder_1, alice_builder_2],
                vec![path_1],
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time = start.elapsed();

        assert_eq!(nullifiers.len(), 2);
        let alice_nullifier_1 = nullifiers[0];
        let alice_nullifier_2 = nullifiers[1];

        // Create Alice verifiers
        let mut alice_verifier_1 = AccountStateTransitionProofVerifier::init(
            alice_account_1_updated_comm,
            alice_nullifier_1,
            alice_nonce,
        );
        alice_verifier_1.add_send_affirmation(leg_enc_1.clone());

        let mut alice_verifier_2 = AccountStateTransitionProofVerifier::init(
            alice_account_2_after_comm,
            alice_nullifier_2,
            alice_nonce,
        );
        alice_verifier_2.add_receive_affirmation(leg_enc_2.clone());

        let start = Instant::now();
        multi_asset_proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![alice_verifier_1, alice_verifier_2],
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time = start.elapsed();

        let proof_size = multi_asset_proof.compressed_size();
        println!(
            "Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            proving_time, verification_time, proof_size
        );

        // Bob create multi-asset proof
        let start = Instant::now();
        let (multi_asset_proof, nullifiers) =
            MultiAssetStateTransitionProof::<L, M, _, _, PallasParameters, VestaParameters>::new::<
                _,
                PallasPoint,
                VestaPoint,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                vec![bob_builder_1, bob_builder_2],
                vec![path_2],
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let proving_time = start.elapsed();

        assert_eq!(nullifiers.len(), 2);
        let bob_nullifier_1 = nullifiers[0];
        let bob_nullifier_2 = nullifiers[1];

        // Create Bob verifiers
        let mut bob_verifier_1 = AccountStateTransitionProofVerifier::init(
            bob_account_1_updated_comm,
            bob_nullifier_1,
            bob_nonce,
        );
        bob_verifier_1.add_receive_affirmation(leg_enc_1.clone());

        let mut bob_verifier_2 = AccountStateTransitionProofVerifier::init(
            bob_account_2_updated_comm,
            bob_nullifier_2,
            bob_nonce,
        );
        bob_verifier_2.add_send_affirmation(leg_enc_2.clone());

        let start = Instant::now();
        multi_asset_proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![bob_verifier_1, bob_verifier_2],
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let verification_time = start.elapsed();

        let proof_size = multi_asset_proof.compressed_size();
        println!(
            "Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            proving_time, verification_time, proof_size
        );
    }

    #[test]
    fn test_multi_asset_six_legs() {
        // 6 legs, all different assets and thus both Alice and Bob will have 6 accounts. Alice acts as sender and Bob as receiver in first leg,
        // opposite in other leg, and in next 2 legs, Alice and Bob both reverse and in next 2 legs, both alice and bob claim and update counter

        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 15; // Increased for 12 accounts with multiple operations
        const L: usize = 64;
        const M: usize = 2;

        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"test");

        // Setup keys for Alice and Bob
        let (
            ((sk_alice, pk_alice), (_, pk_alice_e)),
            ((sk_bob, pk_bob), (_, pk_bob_e)),
            (_, (_, pk_auditor_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        // 6 different assets
        let asset_ids: Vec<u32> = (1..=6).collect();

        // Leg amounts
        let leg_1_amount = 100u64; // Alice -> Bob on asset 1
        let leg_2_amount = 200u64; // Bob -> Alice on asset 2
        let leg_3_amount = 50u64; // Alice -> Bob (sender reverse) on asset 3
        let leg_4_amount = 75u64; // Bob -> Alice (receiver reverse) on asset 4
        let leg_5_amount = 150u64; // Alice -> Bob (both claim, Alice counter update) on asset 5
        let leg_6_amount = 125u64; // Bob -> Alice (both claim, Bob counter update) on asset 6

        // Create all 6 legs
        let (_, leg_enc_1, leg_enc_rand_1) = setup_leg(
            &mut rng,
            pk_alice.0,
            pk_bob.0,
            pk_auditor_e.0,
            true,
            leg_1_amount,
            asset_ids[0],
            pk_alice_e.0,
            pk_bob_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_2, leg_enc_rand_2) = setup_leg(
            &mut rng,
            pk_bob.0,
            pk_alice.0,
            pk_auditor_e.0,
            true,
            leg_2_amount,
            asset_ids[1],
            pk_bob_e.0,
            pk_alice_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_3, leg_enc_rand_3) = setup_leg(
            &mut rng,
            pk_alice.0,
            pk_bob.0,
            pk_auditor_e.0,
            true,
            leg_3_amount,
            asset_ids[2],
            pk_alice_e.0,
            pk_bob_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_4, leg_enc_rand_4) = setup_leg(
            &mut rng,
            pk_bob.0,
            pk_alice.0,
            pk_auditor_e.0,
            true,
            leg_4_amount,
            asset_ids[3],
            pk_bob_e.0,
            pk_alice_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_5, leg_enc_rand_5) = setup_leg(
            &mut rng,
            pk_alice.0,
            pk_bob.0,
            pk_auditor_e.0,
            true,
            leg_5_amount,
            asset_ids[4],
            pk_alice_e.0,
            pk_bob_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_6, leg_enc_rand_6) = setup_leg(
            &mut rng,
            pk_bob.0,
            pk_alice.0,
            pk_auditor_e.0,
            true,
            leg_6_amount,
            asset_ids[5],
            pk_bob_e.0,
            pk_alice_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Create Alice's 6 accounts (one per asset)
        let alice_id_1 = PallasFr::rand(&mut rng);
        let (mut alice_account_1, _, _) =
            new_account(&mut rng, asset_ids[0], sk_alice.clone(), alice_id_1);
        alice_account_1.balance = 1000;

        let alice_id_2 = PallasFr::rand(&mut rng);
        let (mut alice_account_2, _, _) =
            new_account(&mut rng, asset_ids[1], sk_alice.clone(), alice_id_2);
        alice_account_2.balance = 1000;

        let alice_id_3 = PallasFr::rand(&mut rng);
        let (mut alice_account_3, _, _) =
            new_account(&mut rng, asset_ids[2], sk_alice.clone(), alice_id_3);
        alice_account_3.balance = 1000;
        alice_account_3.counter = 1;

        let alice_id_4 = PallasFr::rand(&mut rng);
        let (mut alice_account_4, _, _) =
            new_account(&mut rng, asset_ids[3], sk_alice.clone(), alice_id_4);
        alice_account_4.balance = 1000;
        alice_account_4.counter = 1;

        let alice_id_5 = PallasFr::rand(&mut rng);
        let (mut alice_account_5, _, _) =
            new_account(&mut rng, asset_ids[4], sk_alice.clone(), alice_id_5);
        alice_account_5.balance = 1000;
        alice_account_5.counter = 1;

        let alice_id_6 = PallasFr::rand(&mut rng);
        let (mut alice_account_6, _, _) =
            new_account(&mut rng, asset_ids[5], sk_alice.clone(), alice_id_6);
        alice_account_6.balance = 1000;
        alice_account_6.counter = 1;

        // Create Bob's 6 accounts (one per asset)
        let bob_id_1 = PallasFr::rand(&mut rng);
        let (mut bob_account_1, _, _) =
            new_account(&mut rng, asset_ids[0], sk_bob.clone(), bob_id_1);
        bob_account_1.balance = 1000;

        let bob_id_2 = PallasFr::rand(&mut rng);
        let (mut bob_account_2, _, _) =
            new_account(&mut rng, asset_ids[1], sk_bob.clone(), bob_id_2);
        bob_account_2.balance = 1000;

        let bob_id_3 = PallasFr::rand(&mut rng);
        let (mut bob_account_3, _, _) =
            new_account(&mut rng, asset_ids[2], sk_bob.clone(), bob_id_3);
        bob_account_3.balance = 1000;
        bob_account_3.counter = 1;

        let bob_id_4 = PallasFr::rand(&mut rng);
        let (mut bob_account_4, _, _) =
            new_account(&mut rng, asset_ids[3], sk_bob.clone(), bob_id_4);
        bob_account_4.balance = 1000;
        bob_account_4.counter = 1;

        let bob_id_5 = PallasFr::rand(&mut rng);
        let (mut bob_account_5, _, _) =
            new_account(&mut rng, asset_ids[4], sk_bob.clone(), bob_id_5);
        bob_account_5.balance = 1000;
        bob_account_5.counter = 1;

        let bob_id_6 = PallasFr::rand(&mut rng);
        let (mut bob_account_6, _, _) =
            new_account(&mut rng, asset_ids[5], sk_bob.clone(), bob_id_6);
        bob_account_6.balance = 1000;
        bob_account_6.counter = 1;

        // Alice's account state transitions
        let alice_account_1_updated = alice_account_1.get_state_for_send(leg_1_amount).unwrap();
        let alice_account_2_updated = alice_account_2.get_state_for_receive();
        let alice_account_3_updated = alice_account_3
            .get_state_for_reversing_send(leg_3_amount)
            .unwrap();
        let alice_account_4_updated = alice_account_4
            .get_state_for_decreasing_counter(None)
            .unwrap();
        let alice_account_5_updated = alice_account_5
            .get_state_for_decreasing_counter(None)
            .unwrap();
        let alice_account_6_updated = alice_account_6
            .get_state_for_claiming_received(leg_6_amount)
            .unwrap();

        // Bob's account state transitions
        let bob_account_1_updated = bob_account_1.get_state_for_receive();
        let bob_account_2_updated = bob_account_2.get_state_for_send(leg_2_amount).unwrap();
        let bob_account_3_updated = bob_account_3
            .get_state_for_decreasing_counter(None)
            .unwrap();
        let bob_account_4_updated = bob_account_4
            .get_state_for_reversing_send(leg_4_amount)
            .unwrap();
        let bob_account_5_updated = bob_account_5
            .get_state_for_claiming_received(leg_5_amount)
            .unwrap();
        let bob_account_6_updated = bob_account_6
            .get_state_for_decreasing_counter(None)
            .unwrap();

        // Compute updated commitments
        let alice_account_1_updated_comm = alice_account_1_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_account_2_updated_comm = alice_account_2_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_account_3_updated_comm = alice_account_3_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_account_4_updated_comm = alice_account_4_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_account_5_updated_comm = alice_account_5_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_account_6_updated_comm = alice_account_6_updated
            .commit(account_comm_key.clone())
            .unwrap();

        let bob_account_1_updated_comm = bob_account_1_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_account_2_updated_comm = bob_account_2_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_account_3_updated_comm = bob_account_3_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_account_4_updated_comm = bob_account_4_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_account_5_updated_comm = bob_account_5_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_account_6_updated_comm = bob_account_6_updated
            .commit(account_comm_key.clone())
            .unwrap();

        // Create batched account tree
        let account_tree = get_batched_tree_with_account_comms::<L, M, _>(
            vec![
                &alice_account_1,
                &alice_account_2,
                &alice_account_3,
                &alice_account_4,
                &alice_account_5,
                &alice_account_6,
                &bob_account_1,
                &bob_account_2,
                &bob_account_3,
                &bob_account_4,
                &bob_account_5,
                &bob_account_6,
            ],
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let account_tree_root = account_tree.root_node();

        // Alice's accounts are at indices 0-5, Bob's at 6-11
        let paths_alice = vec![
            account_tree.get_paths_to_leaves(&[0, 1]).unwrap(),
            account_tree.get_paths_to_leaves(&[2, 3]).unwrap(),
            account_tree.get_paths_to_leaves(&[4, 5]).unwrap(),
        ];
        let paths_bob = vec![
            account_tree.get_paths_to_leaves(&[6, 7]).unwrap(),
            account_tree.get_paths_to_leaves(&[8, 9]).unwrap(),
            account_tree.get_paths_to_leaves(&[10, 11]).unwrap(),
        ];

        let nonce_alice = b"alice_nonce";
        let nonce_bob = b"bob_nonce";

        // Alice creates builders for all 6 accounts
        let mut alice_builder_1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_1.clone(),
                alice_account_1_updated.clone(),
                alice_account_1_updated_comm,
                nonce_alice,
            );
        alice_builder_1.add_send_affirmation(
            leg_1_amount,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
        );

        let mut alice_builder_2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_2.clone(),
                alice_account_2_updated.clone(),
                alice_account_2_updated_comm,
                nonce_alice,
            );
        alice_builder_2.add_receive_affirmation(leg_enc_2.clone(), leg_enc_rand_2.clone());

        let mut alice_builder_3 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_3.clone(),
                alice_account_3_updated.clone(),
                alice_account_3_updated_comm,
                nonce_alice,
            );
        alice_builder_3.add_sender_reverse(leg_3_amount, leg_enc_3.clone(), leg_enc_rand_3.clone());

        let mut alice_builder_4 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_4.clone(),
                alice_account_4_updated.clone(),
                alice_account_4_updated_comm,
                nonce_alice,
            );
        alice_builder_4.add_receiver_reverse(leg_enc_4.clone(), leg_enc_rand_4.clone());

        let mut alice_builder_5 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_5.clone(),
                alice_account_5_updated.clone(),
                alice_account_5_updated_comm,
                nonce_alice,
            );
        alice_builder_5.add_sender_counter_update(leg_enc_5.clone(), leg_enc_rand_5.clone());

        let mut alice_builder_6 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_6.clone(),
                alice_account_6_updated.clone(),
                alice_account_6_updated_comm,
                nonce_alice,
            );
        alice_builder_6.add_claim_received(leg_6_amount, leg_enc_6.clone(), leg_enc_rand_6.clone());

        // Alice creates multi-asset proof with all 6 accounts
        let start = Instant::now();
        let (alice_proof, alice_nullifiers) =
            MultiAssetStateTransitionProof::<L, M, _, _, PallasParameters, VestaParameters>::new::<
                _,
                PallasPoint,
                VestaPoint,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                vec![
                    alice_builder_1,
                    alice_builder_2,
                    alice_builder_3,
                    alice_builder_4,
                    alice_builder_5,
                    alice_builder_6,
                ],
                paths_alice,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let alice_proving_time = start.elapsed();

        assert_eq!(alice_nullifiers.len(), 6);

        let mut alice_verifier_1 = AccountStateTransitionProofVerifier::init(
            alice_account_1_updated_comm,
            alice_nullifiers[0],
            nonce_alice,
        );
        alice_verifier_1.add_send_affirmation(leg_enc_1.clone());

        let mut alice_verifier_2 = AccountStateTransitionProofVerifier::init(
            alice_account_2_updated_comm,
            alice_nullifiers[1],
            nonce_alice,
        );
        alice_verifier_2.add_receive_affirmation(leg_enc_2.clone());

        let mut alice_verifier_3 = AccountStateTransitionProofVerifier::init(
            alice_account_3_updated_comm,
            alice_nullifiers[2],
            nonce_alice,
        );
        alice_verifier_3.add_sender_reverse(leg_enc_3.clone());

        let mut alice_verifier_4 = AccountStateTransitionProofVerifier::init(
            alice_account_4_updated_comm,
            alice_nullifiers[3],
            nonce_alice,
        );
        alice_verifier_4.add_receiver_reverse(leg_enc_4.clone());

        let mut alice_verifier_5 = AccountStateTransitionProofVerifier::init(
            alice_account_5_updated_comm,
            alice_nullifiers[4],
            nonce_alice,
        );
        alice_verifier_5.add_sender_counter_update(leg_enc_5.clone());

        let mut alice_verifier_6 = AccountStateTransitionProofVerifier::init(
            alice_account_6_updated_comm,
            alice_nullifiers[5],
            nonce_alice,
        );
        alice_verifier_6.add_claim_received(leg_enc_6.clone());

        // Verify Alice's proof
        let start = Instant::now();
        alice_proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![
                    alice_verifier_1,
                    alice_verifier_2,
                    alice_verifier_3,
                    alice_verifier_4,
                    alice_verifier_5,
                    alice_verifier_6,
                ],
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let alice_verification_time = start.elapsed();

        let alice_proof_size = alice_proof.compressed_size();
        println!(
            "Alice: Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            alice_proving_time, alice_verification_time, alice_proof_size
        );

        // Bob creates builders for all 6 accounts
        let mut bob_builder_1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_1.clone(),
                bob_account_1_updated.clone(),
                bob_account_1_updated_comm,
                nonce_bob,
            );
        bob_builder_1.add_receive_affirmation(leg_enc_1.clone(), leg_enc_rand_1.clone());

        let mut bob_builder_2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_2.clone(),
                bob_account_2_updated.clone(),
                bob_account_2_updated_comm,
                nonce_bob,
            );
        bob_builder_2.add_send_affirmation(leg_2_amount, leg_enc_2.clone(), leg_enc_rand_2.clone());

        let mut bob_builder_3 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_3.clone(),
                bob_account_3_updated.clone(),
                bob_account_3_updated_comm,
                nonce_bob,
            );
        bob_builder_3.add_receiver_reverse(leg_enc_3.clone(), leg_enc_rand_3.clone());

        let mut bob_builder_4 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_4.clone(),
                bob_account_4_updated.clone(),
                bob_account_4_updated_comm,
                nonce_bob,
            );
        bob_builder_4.add_sender_reverse(leg_4_amount, leg_enc_4.clone(), leg_enc_rand_4.clone());

        let mut bob_builder_5 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_5.clone(),
                bob_account_5_updated.clone(),
                bob_account_5_updated_comm,
                nonce_bob,
            );
        bob_builder_5.add_claim_received(leg_5_amount, leg_enc_5.clone(), leg_enc_rand_5.clone());

        let mut bob_builder_6 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_6.clone(),
                bob_account_6_updated.clone(),
                bob_account_6_updated_comm,
                nonce_bob,
            );
        bob_builder_6.add_sender_counter_update(leg_enc_6.clone(), leg_enc_rand_6.clone());

        // Bob creates multi-asset proof with all 6 accounts
        let start = Instant::now();
        let (bob_proof, bob_nullifiers) =
            MultiAssetStateTransitionProof::<L, M, _, _, PallasParameters, VestaParameters>::new::<
                _,
                PallasPoint,
                VestaPoint,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                vec![
                    bob_builder_1,
                    bob_builder_2,
                    bob_builder_3,
                    bob_builder_4,
                    bob_builder_5,
                    bob_builder_6,
                ],
                paths_bob,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let bob_proving_time = start.elapsed();

        assert_eq!(bob_nullifiers.len(), 6);

        // Bob creates verifiers
        let mut bob_verifier_1 = AccountStateTransitionProofVerifier::init(
            bob_account_1_updated_comm,
            bob_nullifiers[0],
            nonce_bob,
        );
        bob_verifier_1.add_receive_affirmation(leg_enc_1.clone());

        let mut bob_verifier_2 = AccountStateTransitionProofVerifier::init(
            bob_account_2_updated_comm,
            bob_nullifiers[1],
            nonce_bob,
        );
        bob_verifier_2.add_send_affirmation(leg_enc_2.clone());

        let mut bob_verifier_3 = AccountStateTransitionProofVerifier::init(
            bob_account_3_updated_comm,
            bob_nullifiers[2],
            nonce_bob,
        );
        bob_verifier_3.add_receiver_reverse(leg_enc_3.clone());

        let mut bob_verifier_4 = AccountStateTransitionProofVerifier::init(
            bob_account_4_updated_comm,
            bob_nullifiers[3],
            nonce_bob,
        );
        bob_verifier_4.add_sender_reverse(leg_enc_4.clone());

        let mut bob_verifier_5 = AccountStateTransitionProofVerifier::init(
            bob_account_5_updated_comm,
            bob_nullifiers[4],
            nonce_bob,
        );
        bob_verifier_5.add_claim_received(leg_enc_5.clone());

        let mut bob_verifier_6 = AccountStateTransitionProofVerifier::init(
            bob_account_6_updated_comm,
            bob_nullifiers[5],
            nonce_bob,
        );
        bob_verifier_6.add_sender_counter_update(leg_enc_6.clone());

        // Verify Bob's proof
        let start = Instant::now();
        bob_proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![
                    bob_verifier_1,
                    bob_verifier_2,
                    bob_verifier_3,
                    bob_verifier_4,
                    bob_verifier_5,
                    bob_verifier_6,
                ],
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let bob_verification_time = start.elapsed();

        let bob_proof_size = bob_proof.compressed_size();
        println!(
            "Bob: Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            bob_proving_time, bob_verification_time, bob_proof_size
        );
    }

    #[test]
    fn test_multi_asset_six_legs_two_assets() {
        // 6 legs with 2 assets. Alice and Bob each have 2 accounts (one per asset).
        // First 4 legs use asset 1:
        //   Leg 1: Alice sends to Bob
        //   Leg 2: Bob sends to Alice
        //   Leg 3: Alice sends to Bob
        //   Leg 4: Bob sends to Alice
        // Last 2 legs use asset 2 with irreversible operations:
        //   Leg 5: Alice irreversible send to Bob
        //   Leg 6: Bob irreversible send to Alice

        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 14;
        const L: usize = 64;
        const M: usize = 2;

        let (account_tree_params, account_comm_key, enc_key_gen, enc_gen) =
            setup_gens_new::<NUM_GENS>(b"test");

        // Setup keys for Alice and Bob
        let (
            ((sk_alice, pk_alice), (_, pk_alice_e)),
            ((sk_bob, pk_bob), (_, pk_bob_e)),
            (_, (_, pk_auditor_e)),
        ) = setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        // 2 different assets
        let asset_id_1 = 1u32;
        let asset_id_2 = 2u32;

        // Leg amounts
        let leg_1_amount = 100u64; // Alice -> Bob on asset 1
        let leg_2_amount = 150u64; // Bob -> Alice on asset 1
        let leg_3_amount = 80u64; // Alice -> Bob on asset 1
        let leg_4_amount = 120u64; // Bob -> Alice on asset 1
        let leg_5_amount = 200u64; // Alice -> Bob irreversible on asset 2
        let leg_6_amount = 250u64; // Bob -> Alice irreversible on asset 2

        // Create all 6 legs
        let (_, leg_enc_1, leg_enc_rand_1) = setup_leg(
            &mut rng,
            pk_alice.0,
            pk_bob.0,
            pk_auditor_e.0,
            true,
            leg_1_amount,
            asset_id_1,
            pk_alice_e.0,
            pk_bob_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_2, leg_enc_rand_2) = setup_leg(
            &mut rng,
            pk_bob.0,
            pk_alice.0,
            pk_auditor_e.0,
            true,
            leg_2_amount,
            asset_id_1,
            pk_bob_e.0,
            pk_alice_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_3, leg_enc_rand_3) = setup_leg(
            &mut rng,
            pk_alice.0,
            pk_bob.0,
            pk_auditor_e.0,
            true,
            leg_3_amount,
            asset_id_1,
            pk_alice_e.0,
            pk_bob_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_4, leg_enc_rand_4) = setup_leg(
            &mut rng,
            pk_bob.0,
            pk_alice.0,
            pk_auditor_e.0,
            true,
            leg_4_amount,
            asset_id_1,
            pk_bob_e.0,
            pk_alice_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_5, leg_enc_rand_5) = setup_leg(
            &mut rng,
            pk_alice.0,
            pk_bob.0,
            pk_auditor_e.0,
            true,
            leg_5_amount,
            asset_id_2,
            pk_alice_e.0,
            pk_bob_e.0,
            enc_key_gen,
            enc_gen,
        );

        let (_, leg_enc_6, leg_enc_rand_6) = setup_leg(
            &mut rng,
            pk_bob.0,
            pk_alice.0,
            pk_auditor_e.0,
            true,
            leg_6_amount,
            asset_id_2,
            pk_bob_e.0,
            pk_alice_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Create Alice's 2 accounts (one per asset)
        let alice_id_1 = PallasFr::rand(&mut rng);
        let (mut alice_account_1, _, _) =
            new_account(&mut rng, asset_id_1, sk_alice.clone(), alice_id_1);
        alice_account_1.balance = 1000;

        let alice_id_2 = PallasFr::rand(&mut rng);
        let (mut alice_account_2, _, _) =
            new_account(&mut rng, asset_id_2, sk_alice.clone(), alice_id_2);
        alice_account_2.balance = 1000;

        // Create Bob's 2 accounts (one per asset)
        let bob_id_1 = PallasFr::rand(&mut rng);
        let (mut bob_account_1, _, _) = new_account(&mut rng, asset_id_1, sk_bob.clone(), bob_id_1);
        bob_account_1.balance = 1000;

        let bob_id_2 = PallasFr::rand(&mut rng);
        let (mut bob_account_2, _, _) = new_account(&mut rng, asset_id_2, sk_bob.clone(), bob_id_2);
        bob_account_2.balance = 1000;

        let mut builder1 = AccountStateBuilder::init(alice_account_1.clone());
        builder1.update_for_send(leg_1_amount).unwrap();
        builder1.update_for_claiming_received(leg_2_amount).unwrap();
        builder1.update_for_send(leg_3_amount).unwrap();
        builder1.update_for_claiming_received(leg_4_amount).unwrap();
        let alice_account_1_updated = builder1.finalize();

        let mut builder2 = AccountStateBuilder::init(alice_account_2.clone());
        builder2.update_for_irreversible_send(leg_5_amount).unwrap();
        builder2
            .update_for_irreversible_receive(leg_6_amount)
            .unwrap();
        let alice_account_2_updated = builder2.finalize();

        let mut builder3 = AccountStateBuilder::init(bob_account_1.clone());
        builder3.update_for_send(leg_2_amount).unwrap();
        builder3.update_for_claiming_received(leg_1_amount).unwrap();
        builder3.update_for_send(leg_4_amount).unwrap();
        builder3.update_for_claiming_received(leg_3_amount).unwrap();
        let bob_account_1_updated = builder3.finalize();

        let mut builder4 = AccountStateBuilder::init(bob_account_2.clone());
        builder4
            .update_for_irreversible_receive(leg_5_amount)
            .unwrap();
        builder4.update_for_irreversible_send(leg_6_amount).unwrap();
        let bob_account_2_updated = builder4.finalize();

        let alice_account_1_updated_comm = alice_account_1_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let alice_account_2_updated_comm = alice_account_2_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_account_1_updated_comm = bob_account_1_updated
            .commit(account_comm_key.clone())
            .unwrap();
        let bob_account_2_updated_comm = bob_account_2_updated
            .commit(account_comm_key.clone())
            .unwrap();

        let account_tree = get_batched_tree_with_account_comms::<L, M, _>(
            vec![
                &alice_account_1,
                &alice_account_2,
                &bob_account_1,
                &bob_account_2,
            ],
            account_comm_key.clone(),
            &account_tree_params,
            6,
        )
        .unwrap();

        let account_tree_root = account_tree.root_node();

        // Alice's accounts are at indices 0-1, Bob's at 2-3
        let paths_alice = vec![account_tree.get_paths_to_leaves(&[0, 1]).unwrap()];
        let paths_bob = vec![account_tree.get_paths_to_leaves(&[2, 3]).unwrap()];

        let nonce_alice = b"alice_nonce";
        let nonce_bob = b"bob_nonce";

        // Alice creates builders for her 2 accounts
        let mut alice_builder_1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_1.clone(),
                alice_account_1_updated.clone(),
                alice_account_1_updated_comm,
                nonce_alice,
            );
        // Add all 4 operations for asset 1
        alice_builder_1.add_send_affirmation(
            leg_1_amount,
            leg_enc_1.clone(),
            leg_enc_rand_1.clone(),
        );
        alice_builder_1.add_claim_received(leg_2_amount, leg_enc_2.clone(), leg_enc_rand_2.clone());
        alice_builder_1.add_send_affirmation(
            leg_3_amount,
            leg_enc_3.clone(),
            leg_enc_rand_3.clone(),
        );
        alice_builder_1.add_claim_received(leg_4_amount, leg_enc_4.clone(), leg_enc_rand_4.clone());

        let mut alice_builder_2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                alice_account_2.clone(),
                alice_account_2_updated.clone(),
                alice_account_2_updated_comm,
                nonce_alice,
            );
        alice_builder_2.add_irreversible_send(
            leg_5_amount,
            leg_enc_5.clone(),
            leg_enc_rand_5.clone(),
        );
        alice_builder_2.add_irreversible_receive(
            leg_6_amount,
            leg_enc_6.clone(),
            leg_enc_rand_6.clone(),
        );

        // Alice creates multi-asset proof with both accounts
        let start = Instant::now();
        let (alice_proof, alice_nullifiers) =
            MultiAssetStateTransitionProof::<L, M, _, _, PallasParameters, VestaParameters>::new::<
                _,
                PallasPoint,
                VestaPoint,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                vec![alice_builder_1, alice_builder_2],
                paths_alice,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let alice_proving_time = start.elapsed();

        assert_eq!(alice_nullifiers.len(), 2);

        // Alice creates verifiers
        let mut bob_builder_1 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_1.clone(),
                bob_account_1_updated.clone(),
                bob_account_1_updated_comm,
                nonce_bob,
            );
        bob_builder_1.add_claim_received(leg_1_amount, leg_enc_1.clone(), leg_enc_rand_1.clone());
        bob_builder_1.add_send_affirmation(leg_2_amount, leg_enc_2.clone(), leg_enc_rand_2.clone());
        bob_builder_1.add_claim_received(leg_3_amount, leg_enc_3.clone(), leg_enc_rand_3.clone());
        bob_builder_1.add_send_affirmation(leg_4_amount, leg_enc_4.clone(), leg_enc_rand_4.clone());

        let mut bob_builder_2 =
            AccountStateTransitionProofBuilder::<L, _, _, PallasParameters, VestaParameters>::init(
                bob_account_2.clone(),
                bob_account_2_updated.clone(),
                bob_account_2_updated_comm,
                nonce_bob,
            );
        bob_builder_2.add_irreversible_receive(
            leg_5_amount,
            leg_enc_5.clone(),
            leg_enc_rand_5.clone(),
        );
        bob_builder_2.add_irreversible_send(
            leg_6_amount,
            leg_enc_6.clone(),
            leg_enc_rand_6.clone(),
        );

        let start = Instant::now();
        let (bob_proof, bob_nullifiers) =
            MultiAssetStateTransitionProof::<L, M, _, _, PallasParameters, VestaParameters>::new::<
                _,
                PallasPoint,
                VestaPoint,
                PallasParams,
                VestaParams,
            >(
                &mut rng,
                vec![bob_builder_1, bob_builder_2],
                paths_bob,
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
            )
            .unwrap();
        let bob_proving_time = start.elapsed();

        let mut alice_verifier_1 = AccountStateTransitionProofVerifier::init(
            alice_account_1_updated_comm,
            alice_nullifiers[0],
            nonce_alice,
        );
        alice_verifier_1.add_send_affirmation(leg_enc_1.clone());
        alice_verifier_1.add_claim_received(leg_enc_2.clone());
        alice_verifier_1.add_send_affirmation(leg_enc_3.clone());
        alice_verifier_1.add_claim_received(leg_enc_4.clone());

        let mut alice_verifier_2 = AccountStateTransitionProofVerifier::init(
            alice_account_2_updated_comm,
            alice_nullifiers[1],
            nonce_alice,
        );
        alice_verifier_2.add_irreversible_send(leg_enc_5.clone());
        alice_verifier_2.add_irreversible_receive(leg_enc_6.clone());

        let start = Instant::now();
        alice_proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![alice_verifier_1, alice_verifier_2],
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let alice_verification_time = start.elapsed();

        // Verify Bob
        let mut bob_verifier_1 = AccountStateTransitionProofVerifier::init(
            bob_account_1_updated_comm,
            bob_nullifiers[0],
            nonce_bob,
        );
        bob_verifier_1.add_claim_received(leg_enc_1.clone());
        bob_verifier_1.add_send_affirmation(leg_enc_2.clone());
        bob_verifier_1.add_claim_received(leg_enc_3.clone());
        bob_verifier_1.add_send_affirmation(leg_enc_4.clone());

        let mut bob_verifier_2 = AccountStateTransitionProofVerifier::init(
            bob_account_2_updated_comm,
            bob_nullifiers[1],
            nonce_bob,
        );
        bob_verifier_2.add_irreversible_receive(leg_enc_5.clone());
        bob_verifier_2.add_irreversible_send(leg_enc_6.clone());

        let start = Instant::now();
        bob_proof
            .verify::<_, PallasParams, VestaParams>(
                &mut rng,
                vec![bob_verifier_1, bob_verifier_2],
                &account_tree_root,
                &account_tree_params,
                account_comm_key.clone(),
                enc_key_gen,
                enc_gen,
                None,
            )
            .unwrap();
        let bob_verification_time = start.elapsed();

        let alice_proof_size = alice_proof.compressed_size();
        let bob_proof_size = bob_proof.compressed_size();

        println!("For L={L}, height={}", account_tree.height());
        println!(
            "Alice: Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            alice_proving_time, alice_verification_time, alice_proof_size
        );
        println!(
            "Bob: Proving time = {:?}, verification time = {:?}, proof size = {} bytes",
            bob_proving_time, bob_verification_time, bob_proof_size
        );
    }
}