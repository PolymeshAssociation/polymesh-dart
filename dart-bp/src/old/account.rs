use crate::dart::{AssetId, Balance, PendingTxnCounter};
use ark_ec::short_weierstrass::Affine;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_std::UniformRand;
use equality_across_groups::ec::commitments::SWPoint;
use rand::RngCore;
use std::ops::Neg;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Account<PK: SWPoint> {
    pub sk: PK::ScalarField,
    pub balance: Balance,
    pub counter: PendingTxnCounter,
    pub asset_id: AssetId,
    pub rho: PK::ScalarField,
    pub randomness: PK::ScalarField,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AccountCommitment<PK: SWPoint>(pub Affine<PK>);

impl<PK: SWPoint> Account<PK> {
    pub fn new<R: RngCore>(rng: &mut R, sk: PK::ScalarField, asset_id: AssetId) -> Self {
        let mut rho = PK::ScalarField::rand(rng);
        let minus_sk = sk.neg();
        while minus_sk == rho {
            rho = PK::ScalarField::rand(rng);
        }
        let randomness = PK::ScalarField::rand(rng);
        Self {
            sk,
            balance: 0,
            counter: 0,
            asset_id,
            rho,
            randomness,
        }
    }

    pub fn commit(&self, comm_key: &[Affine<PK>]) -> AccountCommitment<PK> {
        assert!(comm_key.len() >= 6);
        let comm = PK::msm(
            &comm_key[..6],
            &[
                self.sk,
                PK::ScalarField::from(self.balance),
                PK::ScalarField::from(self.counter),
                PK::ScalarField::from(self.asset_id),
                self.rho,
                self.randomness,
            ],
        )
        .unwrap();
        AccountCommitment(comm.into_affine())
    }

    pub fn nullifier(&self, gen: &Affine<PK>) -> Affine<PK> {
        let exp = (self.sk + self.rho).inverse().unwrap();
        (*gen * exp).into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve_tree::{CurveTree, SelRerandParameters};
    use crate::dart::old::keys::{keygen_enc, keygen_sig};
    use crate::dart::old::leg::Leg;
    use crate::dart::AMOUNT_BITS;
    use crate::range_proof::{difference, public_difference, range_proof};
    use ark_ec::{CurveGroup, VariableBaseMSM};
    use ark_pallas::PallasConfig;
    use ark_serialize::CanonicalSerialize;
    use ark_std::{
        rand::{prelude::StdRng, SeedableRng},
        UniformRand,
    };
    use ark_vesta::VestaConfig;
    use blake2::Blake2b512;
    use bulletproofs::r1cs::{Prover, Verifier};
    use digest::{Digest, ExtendableOutput, Update};
    use dock_crypto_utils::commitment::PedersenCommitmentKey;
    use dock_crypto_utils::transcript::{new_merlin_transcript, Transcript};
    use equality_across_groups::ec::commitments::{
        CommitmentWithOpening, PointCommitmentWithOpening,
    };
    use equality_across_groups::ec::sw_scalar_mult::ScalarMultiplicationProtocol;
    use merlin::Transcript as MTranscript;
    use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment};
    use sha3::Shake256;
    use std::time::{Duration, Instant};

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasP = ark_pallas::Projective;
    type PallasA = ark_pallas::Affine;
    type VestaA = ark_vesta::Affine;
    type PallasFr = ark_pallas::Fr;
    type VestaFr = ark_vesta::Fr;

    #[test]
    fn register_and_increase_supply_txns() {
        let mut rng = rand::thread_rng();

        // TODO: Find the optimum gen length for any circuit
        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;

        let account_tree_params =
            SelRerandParameters::<VestaParameters, PallasParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_v = VestaA::rand(&mut rng);
        let gen_p = PallasA::rand(&mut rng);
        let account_comm_key = (0..6).map(|_| VestaA::rand(&mut rng)).collect::<Vec<_>>();

        let asset_id = 1;

        let (sk_i, pk_i) = keygen_sig(&mut rng, gen_v);
        let account = Account::<VestaConfig>::new(&mut rng, sk_i.0, asset_id);
        // Knowledge and correctness (both balance and counter 0, sk-pk relation) can be proven using Schnoor protocol
        let account_comm = account.commit(&account_comm_key);

        // Add account commitment in curve tree
        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(4),
        );

        let increase_bal_by = 10;
        let mut updated_account = account.clone();
        updated_account.balance += increase_bal_by;
        updated_account.rho = VestaFr::rand(&mut rng);
        updated_account.randomness = VestaFr::rand(&mut rng);
        let updated_account_comm = updated_account.commit(&account_comm_key);

        let vesta_transcript = MTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<VestaParameters>> = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            vesta_transcript,
        );

        let pallas_transcript = MTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<PallasParameters>> = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            pallas_transcript,
        );

        // TODO: Don't use new transcript but a common one across all protocols. Also add other instance variables like commitment, key, etc to transcript
        let mut prover_transcript = new_merlin_transcript(b"test");

        let nullifier = account.nullifier(&gen_v);

        let (mut path, rerandomization) = account_tree.select_and_rerandomize_prover_gadget(
            0,
            0,
            &mut vesta_prover,
            &mut pallas_prover,
            &account_tree_params,
            &mut rng,
        );
        // re_randomized_leaf is the commitment to the account state
        let re_randomized_leaf_comm = path.selected_commitment;

        let r_bal_old = VestaFr::rand(&mut rng);
        let (comm_bal_old, var_bal_old) =
            vesta_prover.commit(VestaFr::from(account.balance), r_bal_old);

        let r_bal_new = VestaFr::rand(&mut rng);
        let (comm_bal_new, var_bal_new) =
            vesta_prover.commit(VestaFr::from(updated_account.balance), r_bal_new);

        // TODO: Can the following 2 gadgets be combined to reduce 1 constraint?
        // new - old balance is correct
        public_difference(
            &mut vesta_prover,
            var_bal_new.into(),
            var_bal_old.into(),
            increase_bal_by,
        )
        .unwrap();
        // new balance does not overflow
        range_proof(
            &mut vesta_prover,
            var_bal_new.into(),
            Some(updated_account.balance),
            AMOUNT_BITS.into(),
        )
        .unwrap();

        let sk_blinding = VestaFr::rand(&mut rng);
        let counter_blinding = VestaFr::rand(&mut rng);
        let old_balance_blinding = VestaFr::rand(&mut rng);
        let new_balance_blinding = VestaFr::rand(&mut rng);
        let old_rho_blinding = VestaFr::rand(&mut rng);

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
                old_balance_blinding,
                counter_blinding,
                old_rho_blinding,
                VestaFr::rand(&mut rng),
                VestaFr::rand(&mut rng),
            ],
        );
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
                VestaFr::rand(&mut rng),
                VestaFr::rand(&mut rng),
            ],
        );
        // TODO: Use PokPedersenCommitmentProtocol
        let t_old_bal = SchnorrCommitment::new(
            &[
                account_tree_params.even_parameters.pc_gens.B,
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![old_balance_blinding, VestaFr::rand(&mut rng)],
        );
        let t_new_bal = SchnorrCommitment::new(
            &[
                account_tree_params.even_parameters.pc_gens.B,
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![new_balance_blinding, VestaFr::rand(&mut rng)],
        );
        let t_null =
            SchnorrCommitment::new(&[nullifier, nullifier], vec![sk_blinding, old_rho_blinding]);
        let t_pk = SchnorrCommitment::new(&[gen_v], vec![sk_blinding]);

        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_acc_new
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_old_bal
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_new_bal
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_null
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_pk.challenge_contribution(&mut prover_transcript).unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<VestaFr>(b"challenge");

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
        let resp_old_bal = t_old_bal
            .response(&[account.balance.into(), r_bal_old], &prover_challenge)
            .unwrap();
        let resp_new_bal = t_new_bal
            .response(
                &[updated_account.balance.into(), r_bal_new],
                &prover_challenge,
            )
            .unwrap();
        let resp_null = t_null
            .response(&[account.sk, account.rho], &prover_challenge)
            .unwrap();
        let resp_pk = t_pk.response(&[account.sk], &prover_challenge).unwrap();

        let pallas_proof = pallas_prover
            .prove(&account_tree_params.odd_parameters.bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&account_tree_params.even_parameters.bp_gens)
            .unwrap();

        {
            let mut verifier_transcript = new_merlin_transcript(b"test");

            let pallas_transcript = MTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::<_, Affine<PallasConfig>>::new(pallas_transcript);
            let vesta_transcript = MTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::<_, Affine<VestaConfig>>::new(vesta_transcript);

            account_tree.select_and_rerandomize_verification_commitments(&mut path);
            let commitments = path;

            // Enforce constraints for odd level
            commitments.odd_verifier_gadget(
                &mut pallas_verifier,
                &account_tree_params,
                &account_tree,
            );

            // Enforce constraints for even level
            commitments.even_verifier_gadget(
                &mut vesta_verifier,
                &account_tree_params,
                &account_tree,
            );

            let var_bal_old = vesta_verifier.commit(comm_bal_old);
            let var_bal_new = vesta_verifier.commit(comm_bal_new);

            public_difference(
                &mut vesta_verifier,
                var_bal_new.into(),
                var_bal_old.into(),
                increase_bal_by,
            )
            .unwrap();

            range_proof(
                &mut vesta_verifier,
                var_bal_new.into(),
                None,
                AMOUNT_BITS.into(),
            )
            .unwrap();

            t_r_leaf
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_acc_new
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_old_bal
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_new_bal
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_null
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_pk.t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();

            let verifier_challenge = verifier_transcript.challenge_scalar::<VestaFr>(b"challenge");
            assert_eq!(verifier_challenge, prover_challenge);

            let asset_id_comm = (account_comm_key[3] * VestaFr::from(asset_id)).into_affine();

            let y = re_randomized_leaf_comm - asset_id_comm;
            resp_leaf
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
                    &t_r_leaf.t,
                    &verifier_challenge,
                )
                .unwrap();

            let y = updated_account_comm.0 - asset_id_comm;
            resp_acc_new
                .is_valid(
                    &[
                        account_comm_key[0],
                        account_comm_key[1],
                        account_comm_key[2],
                        account_comm_key[4],
                        account_comm_key[5],
                    ],
                    &y.into_affine(),
                    &t_acc_new.t,
                    &verifier_challenge,
                )
                .unwrap();

            resp_old_bal
                .is_valid(
                    &[
                        account_tree_params.even_parameters.pc_gens.B,
                        account_tree_params.even_parameters.pc_gens.B_blinding,
                    ],
                    &comm_bal_old,
                    &t_old_bal.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_new_bal
                .is_valid(
                    &[
                        account_tree_params.even_parameters.pc_gens.B,
                        account_tree_params.even_parameters.pc_gens.B_blinding,
                    ],
                    &comm_bal_new,
                    &t_new_bal.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_null
                .is_valid(
                    &[nullifier, nullifier],
                    &gen_v,
                    &t_null.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_pk
                .is_valid(&[gen_v], &pk_i.0, &t_pk.t, &verifier_challenge)
                .unwrap();

            // Sk and counter in leaf match the ones in updated account commitment
            assert_eq!(resp_leaf.0[0], resp_acc_new.0[0]);
            assert_eq!(resp_leaf.0[2], resp_acc_new.0[2]);
            // Balance in leaf is same as in the old balance commitment
            assert_eq!(resp_leaf.0[1], resp_old_bal.0[0]);
            // Balance in new account commitment is same as in the new balance commitment
            assert_eq!(resp_acc_new.0[1], resp_new_bal.0[0]);

            // Sk and rho match the ones in nullifier
            assert_eq!(resp_leaf.0[0], resp_null.0[0]);
            assert_eq!(resp_leaf.0[3], resp_null.0[1]);
            // Sk in leaf matches the one in public key
            assert_eq!(resp_leaf.0[0], resp_pk.0[0]);

            vesta_verifier
                .verify(
                    &vesta_proof,
                    &account_tree_params.even_parameters.pc_gens,
                    &account_tree_params.even_parameters.bp_gens,
                )
                .unwrap();
            pallas_verifier
                .verify(
                    &pallas_proof,
                    &account_tree_params.odd_parameters.pc_gens,
                    &account_tree_params.odd_parameters.bp_gens,
                )
                .unwrap();
        }
    }

    #[test]
    fn send_txn() {
        let mut rng = rand::thread_rng();

        // TODO: Find the optimum gen length for any circuit
        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;
        const NUM_REPS: usize = 128;

        let account_tree_params =
            SelRerandParameters::<VestaParameters, PallasParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_v = VestaA::rand(&mut rng);
        let gen_p = PallasA::rand(&mut rng);
        let leg_comm_key = (0..9).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();
        // Using same generators as used in Leg for auditor key and asset id. Not mandatory but doing it for efficiency.
        let leaf_comm_key = vec![leg_comm_key[4], leg_comm_key[5], leg_comm_key[7]];
        let account_comm_key = (0..6).map(|_| VestaA::rand(&mut rng)).collect::<Vec<_>>();

        let comm_key_p = PedersenCommitmentKey::<PallasA>::new::<Blake2b512>(b"test1");
        let comm_key_v = PedersenCommitmentKey::<VestaA>::new::<Blake2b512>(b"test2");

        let (sk_a, pk_a) = keygen_sig(&mut rng, gen_v);
        let (sk_s, pk_s) = keygen_sig(&mut rng, gen_v);
        let (sk_r, pk_r) = keygen_sig(&mut rng, gen_v);

        let asset_id = 1;
        let amount = 100;

        // Venue has successfully created the settlement and leg commitment has been stored on chain
        let leg = Leg::<PallasConfig, VestaConfig>::new(
            &mut rng, &pk_s.0, &pk_r.0, &pk_a.0, amount, asset_id,
        );
        let leg_comm = leg.commit(&leg_comm_key);

        let mut account = Account::<VestaConfig>::new(&mut rng, sk_s.0, asset_id);
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;
        let account_comm = account.commit(&account_comm_key);

        // Add account commitment in curve tree
        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, VestaParameters, PallasParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(4),
        );

        let mut updated_account = account.clone();
        updated_account.balance -= amount;
        updated_account.counter += 1;
        updated_account.rho = VestaFr::rand(&mut rng);
        updated_account.randomness = VestaFr::rand(&mut rng);
        let updated_account_comm = updated_account.commit(&account_comm_key);

        let vesta_transcript = MTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<VestaParameters>> = Prover::new(
            &account_tree_params.even_parameters.pc_gens,
            vesta_transcript,
        );

        let pallas_transcript = MTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<PallasParameters>> = Prover::new(
            &account_tree_params.odd_parameters.pc_gens,
            pallas_transcript,
        );

        // TODO: Don't use new transcript but a common one across all protocols. Also add other instance variables like commitment, key, etc to transcript
        let mut prover_transcript = new_merlin_transcript(b"test");

        let nullifier = account.nullifier(&gen_v);

        let (mut path, rerandomization) = account_tree.select_and_rerandomize_prover_gadget(
            0,
            0,
            &mut vesta_prover,
            &mut pallas_prover,
            &account_tree_params,
            &mut rng,
        );
        // re_randomized_leaf is the commitment to the account state
        let re_randomized_leaf_comm = path.selected_commitment;

        // TODO: It makes sense to commit to all these in a single vector commitment
        let r_bal_old = VestaFr::rand(&mut rng);
        let (comm_bal_old, var_bal_old) =
            vesta_prover.commit(VestaFr::from(account.balance), r_bal_old);

        let r_bal_new = VestaFr::rand(&mut rng);
        let (comm_bal_new, var_bal_new) =
            vesta_prover.commit(VestaFr::from(updated_account.balance), r_bal_new);

        let r_amount = VestaFr::rand(&mut rng);
        let (comm_amount, var_amount) = vesta_prover.commit(VestaFr::from(amount), r_amount);

        let r_counter_old = VestaFr::rand(&mut rng);
        let (comm_counter_old, var_counter_old) =
            vesta_prover.commit(VestaFr::from(account.counter), r_counter_old);

        let r_counter_new = VestaFr::rand(&mut rng);
        let (comm_counter_new, var_counter_new) =
            vesta_prover.commit(VestaFr::from(updated_account.counter), r_counter_new);

        // TODO: Can the following 2 gadgets be combined to reduce 1 constraint?
        // old - new balance is correct
        difference(
            &mut vesta_prover,
            var_bal_old.into(),
            var_bal_new.into(),
            var_amount.into(),
        )
        .unwrap();
        // new balance does not overflow
        range_proof(
            &mut vesta_prover,
            var_bal_new.into(),
            Some(updated_account.balance),
            AMOUNT_BITS.into(),
        )
        .unwrap();
        // amount does not overflow. Question: Don't need that as leg already stores valid amounts.
        range_proof(
            &mut vesta_prover,
            var_amount.into(),
            Some(amount),
            AMOUNT_BITS.into(),
        )
        .unwrap();
        // new - old counter is correct
        public_difference(
            &mut vesta_prover,
            var_counter_new.into(),
            var_counter_old.into(),
            1,
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

        let sk_blinding = VestaFr::rand(&mut rng);
        let old_counter_blinding = VestaFr::rand(&mut rng);
        let new_counter_blinding = VestaFr::rand(&mut rng);
        let old_balance_blinding = VestaFr::rand(&mut rng);
        let new_balance_blinding = VestaFr::rand(&mut rng);
        let asset_id_blinding = VestaFr::rand(&mut rng);
        let old_rho_blinding = VestaFr::rand(&mut rng);

        let pk_x_blinding = PallasFr::rand(&mut rng);
        let pk_y_blinding = PallasFr::rand(&mut rng);

        let comm_sk = CommitmentWithOpening::new(&mut rng, account.sk, &comm_key_v);
        let comm_pk = PointCommitmentWithOpening::new(&mut rng, &pk_s.0, &comm_key_p).unwrap();

        let cdls_protocol =
            ScalarMultiplicationProtocol::<VestaConfig, PallasConfig, NUM_REPS>::init(
                &mut rng,
                comm_sk.clone(),
                comm_pk.clone(),
                pk_s.0,
                gen_v,
                &comm_key_v,
                &comm_key_p,
            )
            .unwrap();

        let t_sk = SchnorrCommitment::new(
            &[comm_key_v.g, comm_key_v.h],
            vec![sk_blinding, VestaFr::rand(&mut rng)],
        );
        let t_pk_x = SchnorrCommitment::new(
            &[comm_key_p.g, comm_key_p.h],
            vec![pk_x_blinding, PallasFr::rand(&mut rng)],
        );
        let t_pk_y = SchnorrCommitment::new(
            &[comm_key_p.g, comm_key_p.h],
            vec![pk_y_blinding, PallasFr::rand(&mut rng)],
        );
        // TODO: Uncomment. Need to pick blindings for amount and asset-id such that they are same and valid members of both fields.
        // Cant I just pick random BigInts and cast them to each field. Would it require range proofs to prove that blinding is smaller than the order of the smaller field.
        // Likely no as amounts are 48-bit and asset ids are public so ensured that are under 32-bit. But this approach is problematic if amounts are > 250-bit which won't be the case.
        // let t_leg = SchnorrCommitment::new(&leg_comm_key, vec![pk_x_blinding, pk_y_blinding, PallasFr::rand(&mut rng), PallasFr::rand(&mut rng), PallasFr::rand(&mut rng), PallasFr::rand(&mut rng), amount_blinding, asset_id_blinding]);

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
                old_counter_blinding,
                asset_id_blinding,
                old_rho_blinding,
                VestaFr::rand(&mut rng),
                VestaFr::rand(&mut rng),
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
                VestaFr::rand(&mut rng),
                VestaFr::rand(&mut rng),
            ],
        );
        // TODO: Use PokPedersenCommitmentProtocol
        let t_old_bal = SchnorrCommitment::new(
            &[
                account_tree_params.even_parameters.pc_gens.B,
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![old_balance_blinding, VestaFr::rand(&mut rng)],
        );
        let t_new_bal = SchnorrCommitment::new(
            &[
                account_tree_params.even_parameters.pc_gens.B,
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![new_balance_blinding, VestaFr::rand(&mut rng)],
        );
        let t_null =
            SchnorrCommitment::new(&[nullifier, nullifier], vec![sk_blinding, old_rho_blinding]);
        let t_old_cnt = SchnorrCommitment::new(
            &[
                account_tree_params.even_parameters.pc_gens.B,
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![old_counter_blinding, VestaFr::rand(&mut rng)],
        );
        let t_new_cnt = SchnorrCommitment::new(
            &[
                account_tree_params.even_parameters.pc_gens.B,
                account_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![new_counter_blinding, VestaFr::rand(&mut rng)],
        );

        cdls_protocol
            .challenge_contribution(&mut prover_transcript)
            .unwrap();

        // t_leg.challenge_contribution(&mut prover_transcript).unwrap();
        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_acc_new
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_old_bal
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_new_bal
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_null
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_old_cnt
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_new_cnt
            .challenge_contribution(&mut prover_transcript)
            .unwrap();

        let mut prover_challenge_cdls = [0_u8; NUM_REPS / 8];
        prover_transcript.challenge_bytes(b"challenge", &mut prover_challenge_cdls);
        let cdls_proof = cdls_protocol.gen_proof(&prover_challenge_cdls);

        // TODO: Need to call challenge_bytes and get create scalar in both fields
        let prover_challenge = prover_transcript.challenge_scalar::<VestaFr>(b"challenge");

        // TODO: Eliminate duplicate responses
        // let resp_leg = t_leg.response(&[leg.pk_s_x, leg.pk_s_y, leg.pk_r_x, leg.pk_r_y, leg.pk_a_x, leg.pk_a_y, leg.amount.into(), leg.asset_id.into(), leg.randomness], &prover_challenge).unwrap();
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
        let resp_old_bal = t_old_bal
            .response(&[account.balance.into(), r_bal_old], &prover_challenge)
            .unwrap();
        let resp_new_bal = t_new_bal
            .response(
                &[updated_account.balance.into(), r_bal_new],
                &prover_challenge,
            )
            .unwrap();
        let resp_null = t_null
            .response(&[account.sk, account.rho], &prover_challenge)
            .unwrap();
        let resp_old_cnt = t_old_cnt
            .response(&[account.counter.into(), r_counter_old], &prover_challenge)
            .unwrap();
        let resp_new_cnt = t_new_cnt
            .response(
                &[updated_account.counter.into(), r_counter_new],
                &prover_challenge,
            )
            .unwrap();

        let pallas_proof = pallas_prover
            .prove(&account_tree_params.odd_parameters.bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&account_tree_params.even_parameters.bp_gens)
            .unwrap();

        {
            let mut verifier_transcript = new_merlin_transcript(b"test");

            let pallas_transcript = MTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::<_, Affine<PallasConfig>>::new(pallas_transcript);
            let vesta_transcript = MTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::<_, Affine<VestaConfig>>::new(vesta_transcript);

            account_tree.select_and_rerandomize_verification_commitments(&mut path);
            let commitments = path;

            // Enforce constraints for odd level
            commitments.odd_verifier_gadget(
                &mut pallas_verifier,
                &account_tree_params,
                &account_tree,
            );

            // Enforce constraints for even level
            commitments.even_verifier_gadget(
                &mut vesta_verifier,
                &account_tree_params,
                &account_tree,
            );

            let var_bal_old = vesta_verifier.commit(comm_bal_old);
            let var_bal_new = vesta_verifier.commit(comm_bal_new);
            let var_amount = vesta_verifier.commit(comm_amount);
            let var_counter_old = vesta_verifier.commit(comm_counter_old);
            let var_counter_new = vesta_verifier.commit(comm_counter_new);

            difference(
                &mut vesta_verifier,
                var_bal_old.into(),
                var_bal_new.into(),
                var_amount.into(),
            )
            .unwrap();

            range_proof(
                &mut vesta_verifier,
                var_bal_new.into(),
                None,
                AMOUNT_BITS.into(),
            )
            .unwrap();

            range_proof(
                &mut vesta_verifier,
                var_amount.into(),
                None,
                AMOUNT_BITS.into(),
            )
            .unwrap();

            public_difference(
                &mut vesta_verifier,
                var_counter_new.into(),
                var_counter_old.into(),
                1,
            )
            .unwrap();

            cdls_proof
                .challenge_contribution(&mut verifier_transcript)
                .unwrap();

            t_r_leaf
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_acc_new
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_old_bal
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_new_bal
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_null
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_old_cnt
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_new_cnt
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();

            let mut verifier_challenge_cdls = [0_u8; NUM_REPS / 8];
            verifier_transcript.challenge_bytes(b"challenge", &mut verifier_challenge_cdls);
            assert_eq!(prover_challenge_cdls, verifier_challenge_cdls);

            let verifier_challenge = verifier_transcript.challenge_scalar::<VestaFr>(b"challenge");
            assert_eq!(verifier_challenge, prover_challenge);

            cdls_proof
                .verify(
                    &comm_sk.comm,
                    &comm_pk.comm,
                    &gen_v,
                    &verifier_challenge_cdls,
                    &comm_key_v,
                    &comm_key_p,
                )
                .unwrap();

            resp_leaf
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
                    &re_randomized_leaf_comm,
                    &t_r_leaf.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_acc_new
                .is_valid(
                    &[
                        account_comm_key[0],
                        account_comm_key[1],
                        account_comm_key[2],
                        account_comm_key[3],
                        account_comm_key[4],
                        account_comm_key[5],
                    ],
                    &updated_account_comm.0,
                    &t_acc_new.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_old_bal
                .is_valid(
                    &[
                        account_tree_params.even_parameters.pc_gens.B,
                        account_tree_params.even_parameters.pc_gens.B_blinding,
                    ],
                    &comm_bal_old,
                    &t_old_bal.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_new_bal
                .is_valid(
                    &[
                        account_tree_params.even_parameters.pc_gens.B,
                        account_tree_params.even_parameters.pc_gens.B_blinding,
                    ],
                    &comm_bal_new,
                    &t_new_bal.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_null
                .is_valid(
                    &[nullifier, nullifier],
                    &gen_v,
                    &t_null.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_old_cnt
                .is_valid(
                    &[
                        account_tree_params.even_parameters.pc_gens.B,
                        account_tree_params.even_parameters.pc_gens.B_blinding,
                    ],
                    &comm_counter_old,
                    &t_old_cnt.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_new_cnt
                .is_valid(
                    &[
                        account_tree_params.even_parameters.pc_gens.B,
                        account_tree_params.even_parameters.pc_gens.B_blinding,
                    ],
                    &comm_counter_new,
                    &t_new_cnt.t,
                    &verifier_challenge,
                )
                .unwrap();

            // Sk and asset id in leaf match the ones in updated account commitment
            assert_eq!(resp_leaf.0[0], resp_acc_new.0[0]);
            assert_eq!(resp_leaf.0[3], resp_acc_new.0[3]);
            // Balance in leaf is same as in the old balance commitment
            assert_eq!(resp_leaf.0[1], resp_old_bal.0[0]);
            // Balance in new account commitment is same as in the new balance commitment
            assert_eq!(resp_acc_new.0[1], resp_new_bal.0[0]);
            // Counter in leaf is same as in the old counter commitment
            assert_eq!(resp_leaf.0[2], resp_old_cnt.0[0]);
            // Counter in new account commitment is same as in the new counter commitment
            assert_eq!(resp_acc_new.0[2], resp_new_cnt.0[0]);

            // Sk and rho match the ones in nullifier
            assert_eq!(resp_leaf.0[0], resp_null.0[0]);
            assert_eq!(resp_leaf.0[4], resp_null.0[1]);

            vesta_verifier
                .verify(
                    &vesta_proof,
                    &account_tree_params.even_parameters.pc_gens,
                    &account_tree_params.even_parameters.bp_gens,
                )
                .unwrap();
            pallas_verifier
                .verify(
                    &pallas_proof,
                    &account_tree_params.odd_parameters.pc_gens,
                    &account_tree_params.odd_parameters.bp_gens,
                )
                .unwrap();
        }
    }
}
