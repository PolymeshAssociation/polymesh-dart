use crate::dart::{AssetId, Balance};
use ark_ec::short_weierstrass::{Affine, Projective};
use ark_ec::CurveGroup;
use ark_std::UniformRand;
use equality_across_groups::ec::commitments::{point_coords_as_scalar_field_elements, SWPoint};
use rand::RngCore;
use std::marker::PhantomData;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Leg<OTHER: SWPoint, PK: SWPoint> {
    pub pk_s_x: OTHER::ScalarField,
    pub pk_s_y: OTHER::ScalarField,
    pub pk_r_x: OTHER::ScalarField,
    pub pk_r_y: OTHER::ScalarField,
    pub pk_a_x: OTHER::ScalarField,
    pub pk_a_y: OTHER::ScalarField,
    pub amount: Balance,
    pub asset_id: AssetId,
    pub randomness: OTHER::ScalarField,
    pub phantom_data: PhantomData<PK>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LegCommitment<OTHER: SWPoint>(pub Affine<OTHER>);

impl<OTHER: SWPoint, PK: SWPoint> Leg<OTHER, PK> {
    pub fn new<R: RngCore>(
        rng: &mut R,
        pk_s: &Affine<PK>,
        pk_r: &Affine<PK>,
        pk_a: &Affine<PK>,
        amount: Balance,
        asset_id: AssetId,
    ) -> Self {
        let randomness = OTHER::ScalarField::rand(rng);
        let (pk_s_x, pk_s_y) = point_coords_as_scalar_field_elements::<PK, OTHER>(pk_s).unwrap();
        let (pk_r_x, pk_r_y) = point_coords_as_scalar_field_elements::<PK, OTHER>(pk_r).unwrap();
        let (pk_a_x, pk_a_y) = point_coords_as_scalar_field_elements::<PK, OTHER>(pk_a).unwrap();
        Self {
            pk_s_x,
            pk_s_y,
            pk_r_x,
            pk_r_y,
            pk_a_x,
            pk_a_y,
            amount,
            asset_id,
            randomness,
            phantom_data: PhantomData::default(),
        }
    }

    pub fn commit(&self, comm_key: &[Affine<OTHER>]) -> LegCommitment<OTHER> {
        assert!(comm_key.len() >= 9);
        let comm = OTHER::msm(
            &comm_key[..9],
            &[
                self.pk_s_x,
                self.pk_s_y,
                self.pk_r_x,
                self.pk_r_y,
                self.pk_a_x,
                self.pk_a_y,
                OTHER::ScalarField::from(self.amount),
                OTHER::ScalarField::from(self.asset_id),
                self.randomness,
            ],
        )
        .unwrap();
        LegCommitment(comm.into_affine())
    }

    pub fn encrypt(&self) {
        todo!()
    }
}

/// Commit to auditor public key coordinates and asset-id
pub fn create_leaf_for_auditor_tree<PK: SWPoint, OTHER: SWPoint>(
    pk_a: &Affine<PK>,
    asset_id: AssetId,
    comm_key: &[Affine<OTHER>],
) -> Affine<OTHER> {
    assert!(comm_key.len() >= 3);
    let (x, y) = point_coords_as_scalar_field_elements::<PK, OTHER>(pk_a).unwrap();
    let comm = OTHER::msm(&comm_key[..3], &[x, y, OTHER::ScalarField::from(asset_id)]).unwrap();
    comm.into_affine()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::curve_tree::{CurveTree, SelRerandParameters};
    use crate::dart::old::keys::{keygen_enc, keygen_sig};
    use crate::dart::AMOUNT_BITS;
    use crate::range_proof::range_proof;
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
    use dock_crypto_utils::transcript::Transcript;
    use dock_crypto_utils::{
        elgamal::BatchedHashedElgamalCiphertext, transcript::new_merlin_transcript,
    };
    use merlin::Transcript as MTranscript;
    use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment};
    use sha3::Shake256;
    use std::time::{Duration, Instant};
    use verifiable_encryption::tz_21::dkgith::DkgithProof;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasP = ark_pallas::Projective;
    type PallasA = ark_pallas::Affine;
    type VestaA = ark_vesta::Affine;
    type PallasFr = ark_pallas::Fr;
    type VestaFr = ark_vesta::Fr;

    #[test]
    fn leg_verification() {
        let mut rng = rand::thread_rng();
        // TODO: Find the optimum gen length for any circuit
        const NUM_GENS: usize = 1 << 11; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 8;
        const SEED_SIZE: usize = 16;
        const SALT_SIZE: usize = 32;
        const NUM_PARTIES: usize = 64;
        const NUM_REPS: usize = 48;
        const SUBSET_SIZE: usize = 15;

        let auditor_tree_params =
            SelRerandParameters::<PallasParameters, VestaParameters>::new(NUM_GENS, NUM_GENS);

        // TODO: Generate by hashing public string
        let gen_v = VestaA::rand(&mut rng);
        let gen_p = PallasA::rand(&mut rng);
        let leg_comm_key = (0..9).map(|_| PallasA::rand(&mut rng)).collect::<Vec<_>>();
        // Using same generators as used in Leg for auditor key and asset id. Not mandatory but doing it for efficiency.
        let leaf_comm_key = vec![leg_comm_key[4], leg_comm_key[5], leg_comm_key[7]];

        let (sk_a, pk_a) = keygen_sig(&mut rng, gen_v);
        let (sk_s, pk_s) = keygen_sig(&mut rng, gen_v);
        let (sk_r, pk_r) = keygen_sig(&mut rng, gen_v);

        let asset_id = 1;

        let leaf_comm = create_leaf_for_auditor_tree(&pk_a.0, asset_id, &leaf_comm_key);

        let set = vec![leaf_comm];
        let auditor_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &auditor_tree_params,
            Some(4),
        );

        let mut total_prover_time = Duration::default();
        let mut total_verifier_time = Duration::default();

        let amount = 100;
        let clock = Instant::now();
        let leg = Leg::<PallasConfig, VestaConfig>::new(
            &mut rng, &pk_s.0, &pk_r.0, &pk_a.0, amount, asset_id,
        );
        let leg_comm = leg.commit(&leg_comm_key);

        let (sk_e, pk_e) = keygen_enc(&mut rng, gen_p);
        total_prover_time += clock.elapsed();

        // TODO: Don't use new transcript but a common one across all protocols. Also add other instance variables like commitment, key, etc to transcript
        let mut prover_transcript = new_merlin_transcript(b"test");

        let clock = Instant::now();
        let ve_proof = DkgithProof::<
            _,
            BatchedHashedElgamalCiphertext<Affine<PallasConfig>>,
            NUM_PARTIES,
            NUM_REPS,
            SEED_SIZE,
            SALT_SIZE,
        >::new::<_, Blake2b512, Shake256>(
            &mut rng,
            vec![
                leg.pk_s_x,
                leg.pk_s_y,
                leg.pk_r_x,
                leg.pk_r_y,
                leg.pk_a_x,
                leg.pk_a_y,
                leg.amount.into(),
                leg.asset_id.into(),
                leg.randomness,
            ],
            &leg_comm_key,
            &pk_e.0,
            &gen_p,
            &mut prover_transcript,
        )
        .unwrap();
        let ve_prover_time = clock.elapsed();
        total_prover_time += ve_prover_time;

        let clock = Instant::now();
        let pallas_transcript = MTranscript::new(b"select_and_rerandomize");
        let mut pallas_prover: Prover<_, Affine<PallasParameters>> = Prover::new(
            &auditor_tree_params.even_parameters.pc_gens,
            pallas_transcript,
        );

        let vesta_transcript = MTranscript::new(b"select_and_rerandomize");
        let mut vesta_prover: Prover<_, Affine<VestaParameters>> = Prover::new(
            &auditor_tree_params.odd_parameters.pc_gens,
            vesta_transcript,
        );

        let (mut path, rerandomization) = auditor_tree.select_and_rerandomize_prover_gadget(
            0,
            0,
            &mut pallas_prover,
            &mut vesta_prover,
            &auditor_tree_params,
            &mut rng,
        );
        // path.selected_commitment is the commitment to the coordinates of pk
        let re_randomized_leaf_comm = path.selected_commitment;

        let r_amount = PallasFr::rand(&mut rng);
        // TODO: Can I avoid this new commitment?
        let (comm_amount, var_amount) = pallas_prover.commit(PallasFr::from(leg.amount), r_amount);

        range_proof(
            &mut pallas_prover,
            var_amount.into(),
            Some(leg.amount),
            AMOUNT_BITS.into(),
        )
        .unwrap();

        // Proving knowledge and equality of values in re_randomized_leaf_comm and leg_comm
        let x_blinding = PallasFr::rand(&mut rng);
        let y_blinding = PallasFr::rand(&mut rng);
        let asset_id_blinding = PallasFr::rand(&mut rng);
        let amount_blinding = PallasFr::rand(&mut rng);

        let t_r_leaf = SchnorrCommitment::new(
            &[
                leaf_comm_key[0],
                leaf_comm_key[1],
                leaf_comm_key[2],
                auditor_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![
                x_blinding,
                y_blinding,
                asset_id_blinding,
                PallasFr::rand(&mut rng),
            ],
        );
        let t_leg = SchnorrCommitment::new(
            &leg_comm_key,
            vec![
                PallasFr::rand(&mut rng),
                PallasFr::rand(&mut rng),
                PallasFr::rand(&mut rng),
                PallasFr::rand(&mut rng),
                x_blinding,
                y_blinding,
                amount_blinding,
                asset_id_blinding,
                PallasFr::rand(&mut rng),
            ],
        );
        // TODO: Use PokPedersenCommitmentProtocol
        let t_amount = SchnorrCommitment::new(
            &[
                auditor_tree_params.even_parameters.pc_gens.B,
                auditor_tree_params.even_parameters.pc_gens.B_blinding,
            ],
            vec![amount_blinding, PallasFr::rand(&mut rng)],
        );

        t_r_leaf
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_leg
            .challenge_contribution(&mut prover_transcript)
            .unwrap();
        t_amount
            .challenge_contribution(&mut prover_transcript)
            .unwrap();

        let prover_challenge = prover_transcript.challenge_scalar::<PallasFr>(b"challenge");

        // TODO: Eliminate duplicate responses
        let resp_leaf = t_r_leaf
            .response(
                &[leg.pk_a_x, leg.pk_a_y, leg.asset_id.into(), rerandomization],
                &prover_challenge,
            )
            .unwrap();
        let resp_leg = t_leg
            .response(
                &[
                    leg.pk_s_x,
                    leg.pk_s_y,
                    leg.pk_r_x,
                    leg.pk_r_y,
                    leg.pk_a_x,
                    leg.pk_a_y,
                    leg.amount.into(),
                    leg.asset_id.into(),
                    leg.randomness,
                ],
                &prover_challenge,
            )
            .unwrap();
        let resp_amount = t_amount
            .response(&[leg.amount.into(), r_amount], &prover_challenge)
            .unwrap();

        let pallas_proof = pallas_prover
            .prove(&auditor_tree_params.even_parameters.bp_gens)
            .unwrap();
        let vesta_proof = vesta_prover
            .prove(&auditor_tree_params.odd_parameters.bp_gens)
            .unwrap();

        total_prover_time += clock.elapsed();

        let mut proof_size = ve_proof.compressed_size()
            + resp_leaf.compressed_size()
            + resp_leg.compressed_size()
            + resp_amount.compressed_size()
            + pallas_proof.compressed_size()
            + vesta_proof.compressed_size();
        println!(
            "total proof size = {proof_size}, ve proof size={}",
            ve_proof.compressed_size()
        );

        let mut ve_verifier_time = Duration::default();
        {
            let clock = Instant::now();
            let mut verifier_transcript = new_merlin_transcript(b"test");
            ve_proof
                .verify::<Blake2b512, Shake256>(
                    &leg_comm.0,
                    &leg_comm_key,
                    &pk_e.0,
                    &gen_p,
                    &mut verifier_transcript,
                )
                .unwrap();
            ve_verifier_time = clock.elapsed();
            total_verifier_time += ve_verifier_time;

            let clock = Instant::now();
            let pallas_transcript = MTranscript::new(b"select_and_rerandomize");
            let mut pallas_verifier = Verifier::<_, Affine<PallasConfig>>::new(pallas_transcript);
            let vesta_transcript = MTranscript::new(b"select_and_rerandomize");
            let mut vesta_verifier = Verifier::<_, Affine<VestaConfig>>::new(vesta_transcript);

            auditor_tree.select_and_rerandomize_verification_commitments(&mut path);
            let commitments = path;

            // Enforce constraints for odd level
            commitments.odd_verifier_gadget(
                &mut vesta_verifier,
                &auditor_tree_params,
                &auditor_tree,
            );

            // Enforce constraints for even level
            commitments.even_verifier_gadget(
                &mut pallas_verifier,
                &auditor_tree_params,
                &auditor_tree,
            );

            let var_amount = pallas_verifier.commit(comm_amount);
            // Value is of 48-bit
            range_proof(
                &mut pallas_verifier,
                var_amount.into(),
                None,
                AMOUNT_BITS.into(),
            )
            .unwrap();

            t_r_leaf
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_leg
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();
            t_amount
                .t
                .serialize_compressed(&mut verifier_transcript)
                .unwrap();

            let verifier_challenge = verifier_transcript.challenge_scalar::<PallasFr>(b"challenge");
            assert_eq!(verifier_challenge, prover_challenge);

            // Verify proof of knowledge of leaf commitment and leg commitment
            resp_leaf
                .is_valid(
                    &[
                        leaf_comm_key[0],
                        leaf_comm_key[1],
                        leaf_comm_key[2],
                        auditor_tree_params.even_parameters.pc_gens.B_blinding,
                    ],
                    &re_randomized_leaf_comm,
                    &t_r_leaf.t,
                    &verifier_challenge,
                )
                .unwrap();
            resp_leg
                .is_valid(&leg_comm_key, &leg_comm.0, &t_leg.t, &verifier_challenge)
                .unwrap();
            resp_amount
                .is_valid(
                    &[
                        auditor_tree_params.even_parameters.pc_gens.B,
                        auditor_tree_params.even_parameters.pc_gens.B_blinding,
                    ],
                    &comm_amount,
                    &t_amount.t,
                    &verifier_challenge,
                )
                .unwrap();

            // Auditor pk co-ordinates are same
            assert_eq!(resp_leaf.0[0], resp_leg.0[4]);
            assert_eq!(resp_leaf.0[1], resp_leg.0[5]);
            // Asset id is same
            assert_eq!(resp_leaf.0[2], resp_leg.0[7]);
            // Amount is same
            assert_eq!(resp_amount.0[0], resp_leg.0[6]);

            vesta_verifier
                .verify(
                    &vesta_proof,
                    &auditor_tree_params.odd_parameters.pc_gens,
                    &auditor_tree_params.odd_parameters.bp_gens,
                )
                .unwrap();
            pallas_verifier
                .verify(
                    &pallas_proof,
                    &auditor_tree_params.even_parameters.pc_gens,
                    &auditor_tree_params.even_parameters.bp_gens,
                )
                .unwrap();
            total_verifier_time += clock.elapsed();
        }

        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            total_prover_time, total_verifier_time
        );
        println!(
            "ve prover time = {:?}, ve verifier time = {:?}",
            ve_prover_time, ve_verifier_time
        );

        let clock = Instant::now();
        let ct = ve_proof
            .compress::<SUBSET_SIZE, Blake2b512, Shake256>()
            .unwrap();
        println!("Ciphertext compressed in: {:?}", clock.elapsed());

        // Decrypt use ephemeral secret key
        let clock = Instant::now();
        let decrypted = ct
            .decrypt::<Blake2b512>(&sk_e.0, &leg_comm.0, &leg_comm_key)
            .unwrap();
        println!("Ciphertext decrypted in: {:?}", clock.elapsed());
        assert_eq!(
            decrypted,
            vec![
                leg.pk_s_x,
                leg.pk_s_y,
                leg.pk_r_x,
                leg.pk_r_y,
                leg.pk_a_x,
                leg.pk_a_y,
                leg.amount.into(),
                leg.asset_id.into(),
                leg.randomness
            ]
        );
    }
}
