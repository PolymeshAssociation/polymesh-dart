use ct_halo2::ec_chip::Ec;
use ct_halo2::multi_layer::{MultiLayerChip, MultiLayerConfig, SingleLayerWitness};
use ff::PrimeField;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Error, Precommitted, Selector};
use halo2_proofs::poly::Rotation;
use crate::AffineSerializable;

// Precommitted column indices for randomness relation circuit
pub const PRECOMMITTED_INITIAL_RHO_IDX: usize = 0;
pub const PRECOMMITTED_OLD_CURRENT_RHO_IDX: usize = 1;
pub const PRECOMMITTED_NEW_CURRENT_RHO_IDX: usize = 2;
pub const PRECOMMITTED_OLD_RANDOMNESS_IDX: usize = 3;
pub const PRECOMMITTED_NEW_RANDOMNESS_IDX: usize = 4;

#[derive(Clone, Debug)]
pub struct StateTransitionCircuit<
    P: AffineSerializable,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    const ARITY: usize
> {
    pub initial_rho: Value<P::Scalar>,
    pub old_current_rho: Value<P::Scalar>,
    pub new_current_rho: Value<P::Scalar>,
    pub old_randomness: Value<P::Scalar>,
    pub new_randomness: Value<P::Scalar>,
    pub tree_witness: Vec<SingleLayerWitness<E, ARITY>>,
}

impl<
    P: AffineSerializable,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    const ARITY: usize
> StateTransitionCircuit<P, E, ARITY> {
    pub fn new(
        initial_rho: Value<P::Scalar>,
        old_current_rho: Value<P::Scalar>,
        new_current_rho: Value<P::Scalar>,
        old_randomness: Value<P::Scalar>,
        new_randomness: Value<P::Scalar>,
        tree_witness: Vec<SingleLayerWitness<E, ARITY>>,
    ) -> Self {
        Self {
            initial_rho,
            old_current_rho,
            new_current_rho,
            old_randomness,
            new_randomness,
            tree_witness
        }
    }
}

#[derive(Clone, Debug)]
pub struct StateTransitionConfig<E: Ec> {
    pub precommitted: Column<Precommitted>,
    pub product: Selector,
    pub square: Selector,
    pub ct_config: MultiLayerConfig<E>,
}

impl<
    F: PrimeField,
    P: AffineSerializable<ScalarExt = F>,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    const ARITY: usize
> Circuit<F> for StateTransitionCircuit<P, E, ARITY> {
    type Config = StateTransitionConfig<E>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        // Self::new(
        //     self.initial_rho,
        //     self.old_current_rho,
        //     self.new_current_rho,
        //     self.old_randomness,
        //     self.new_randomness,
        // )
        // TODO: Needed for V1
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let precommitted = meta.precommitted_column();
        let product = meta.selector();
        let square = meta.selector();

        meta.create_gate("product", |meta| {
            let s = meta.query_selector(product);
            let initial_row = meta.query_precommitted(precommitted, Rotation::cur());
            let old_rho = meta.query_precommitted(precommitted, Rotation::next());
            let new_rho = meta.query_precommitted(precommitted, Rotation(2));
            // Enforce new_rho = initial_row * old_rho
            vec![s * (new_rho - (initial_row * old_rho))]
        });

        meta.create_gate("square", |meta| {
            let s = meta.query_selector(square);
            let old_randomness = meta.query_precommitted(precommitted, Rotation::cur());
            let new_randomness = meta.query_precommitted(precommitted, Rotation::next());
            // Enforce new_randomness = old_randomness^2
            vec![s * (new_randomness - old_randomness.square())]
        });

        let ct_config = MultiLayerChip::<E, ARITY>::configure(meta);

        Self::Config {
            precommitted,
            product,
            square,
            ct_config
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "randomness-refresh",
            |mut region| {

                config.product.enable(&mut region, 0)?;
                region.assign_precommitted(|| "initial_rho", config.precommitted, 0, || self.initial_rho)?;
                region.assign_precommitted(|| "old_current_rho", config.precommitted, 1, || self.old_current_rho)?;
                region.assign_precommitted(|| "new_current_rho", config.precommitted, 2, || self.new_current_rho)?;

                config.square.enable(&mut region, 3)?;
                region.assign_precommitted(|| "old_randomness", config.precommitted, 3, || self.old_randomness)?;
                region.assign_precommitted(|| "new_randomness", config.precommitted, 4, || self.new_randomness)?;

                Ok(())
            },
        )?;

        let multi_layer_chip = MultiLayerChip::construct(config.ct_config);
        multi_layer_chip.assign_layers(
            layouter.namespace(|| "ct"),
            &self.tree_witness,
        )?;

        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::time::Instant;
    use ct_halo2::ec_chip::{PallasEc, VestaEc};
    use ct_halo2::fixed_points_pallas::{FixedPointsPallas, FullWidthPallas};
    use ct_halo2::fixed_points_vesta::{FixedPointsVesta, FullWidthVesta};
    use ct_halo2::multi_layer::{MultiLayerCircuit, SingleLayerWitness};
    use ct_halo2::tree::params::{CTCircuitParams, CTProvingKey, CTVerifyingKey};
    use ct_halo2::tree::sel_re_rand::{SelRerandParameters, SelRerandProvingParams, SelRerandVerifyingParams};
    use ct_halo2::tree::tree::CurveTree;
    use ff::Field;
    use group::{Curve, Group};
    use halo2_gadgets::ecc::chip::FixedPoint;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::plonk::{keygen_vk, keygen_pk, create_proof_with_given_column_blindings, create_proof, get_the_only_precommitted_col_comm};
    use halo2_proofs::poly::commitment::Params;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use lazy_static::lazy_static;
    use pasta_curves::{pallas, vesta};
    use rand_core::OsRng;

    type PallasAffine = pallas::Affine;
    type VestaAffine = vesta::Affine;

    #[derive(Clone)]
    pub struct BlindingGenParams<P0, P1, T0, T1> {
        pub blinding_gen_even: P1,
        pub blinding_gen_odd: P0,
        pub blinding_gen_tables_even: T1,
        pub blinding_gen_tables_odd: T0,
    }

    /// For tree with leaf in Pallas curve
    pub type PallasLeafBlindingGen = BlindingGenParams<PallasAffine, VestaAffine, FixedPointsPallas, FixedPointsVesta>;

    pub const LARGEST_K_PALLAS: u32 = 12;
    pub const LARGEST_K_VESTA: u32 = 12;

    lazy_static! {
        pub static ref PALLAS_BLINDING_PARAMS: PallasLeafBlindingGen = PallasLeafBlindingGen {
            blinding_gen_even: FullWidthVesta::generator(&FullWidthVesta),
            blinding_gen_odd: FullWidthPallas::generator(&FullWidthPallas),
            blinding_gen_tables_even: FixedPointsVesta,
            blinding_gen_tables_odd: FixedPointsPallas,
        };

        // TODO: Create them once but keygen has to be tweaked to accept a limited set of gens or we adapt params to be smaller without extra allocations
        // pub static ref PALLAS_COMM_KEY: Params<PallasAffine> = Params::<PallasAffine>::new(LARGEST_K_PALLAS);
        // pub static ref VESTA_COMM_KEY: Params<VestaAffine> = Params::<VestaAffine>::new(LARGEST_K_VESTA);
    }

    /// Generate circuit parameters and keys for curve tree and state transition i.e, updating rho and commitment randomness
    pub fn setup_curve_tree_params_for_state_transition<const L: usize>(
        k: u32,
        height: usize,
    ) -> (
        CTCircuitParams<PallasAffine, VestaAffine>,
        CTProvingKey<PallasAffine, VestaAffine>,
        CTVerifyingKey<PallasAffine, VestaAffine>,
    ) {
        let params_odd = Params::<PallasAffine>::new(k-1);
        let params_even = Params::<VestaAffine>::new(k);

        let empty_even = SingleLayerWitness::<PallasEc, L>::default();
        let empty_odd = SingleLayerWitness::<VestaEc, L>::default();

        let mut empty_odd_layer_witnesses = vec![];
        let mut empty_even_layer_witnesses = vec![];

        for i in 0..height {
            if i % 2 == 0 {
                empty_even_layer_witnesses.push(empty_even.clone());
            } else {
                empty_odd_layer_witnesses.push(empty_odd.clone());
            }
        }

        let empty_odd_circuit = StateTransitionCircuit::<PallasAffine, VestaEc, L> {
            initial_rho: Value::unknown(),
            old_current_rho: Value::unknown(),
            new_current_rho: Value::unknown(),
            old_randomness: Value::unknown(),
            new_randomness: Value::unknown(),
            tree_witness: empty_odd_layer_witnesses
        };

        let empty_even_circuit = MultiLayerCircuit::<PallasEc, L> {
            layers: empty_even_layer_witnesses,
        };

        let vk_odd = keygen_vk(&params_odd, &empty_odd_circuit).unwrap();
        let pk_odd = keygen_pk(&params_odd, vk_odd.clone(), &empty_odd_circuit).unwrap();

        let vk_even = keygen_vk(&params_even, &empty_even_circuit).unwrap();
        let pk_even = keygen_pk(&params_even, vk_even.clone(), &empty_even_circuit).unwrap();

        let circuit_params = CTCircuitParams {
            even: params_odd,
            odd: params_even
        };

        let ct_pk = CTProvingKey {
            even: pk_odd,
            odd: pk_even,
        };

        let ct_vk = CTVerifyingKey {
            even: vk_odd,
            odd: vk_even,
        };

        (circuit_params, ct_pk, ct_vk)
    }

    /// Generate SelRerand parameters using PALLAS_BLINDING_PARAMS
    pub fn generate_pallas_sel_rerand_params<const L: usize>() -> (
        SelRerandParameters<PallasAffine, VestaAffine, FixedPointsPallas, FixedPointsVesta>,
        SelRerandProvingParams<PallasAffine, VestaAffine>,
        SelRerandVerifyingParams<PallasAffine, VestaAffine>
    ) {
        let blinding_gen_even = PALLAS_BLINDING_PARAMS.blinding_gen_even;
        let blinding_gen_odd = PALLAS_BLINDING_PARAMS.blinding_gen_odd;

        let sr_params = SelRerandParameters::<PallasAffine, VestaAffine, _, _>::new(
            1,
            L,
            b"test",
            blinding_gen_even,
            blinding_gen_odd,
            PALLAS_BLINDING_PARAMS.blinding_gen_tables_even.clone(),
            PALLAS_BLINDING_PARAMS.blinding_gen_tables_odd.clone(),
        );

        let sr_proving_params = sr_params.proving_params();
        let sr_verifying_params = sr_params.verifying_params();

        (sr_params, sr_proving_params, sr_verifying_params)
    }

    /// Create a curve tree with provided leaves
    /// Generates curve tree params internally and returns the tree and params
    pub fn setup_account_tree_with_leaves<const L: usize>(
        leaves: &[PallasAffine],
        height: Option<u8>,
    ) -> (
        CurveTree<PallasAffine, VestaAffine, L>, 
        SelRerandProvingParams<PallasAffine, VestaAffine>,
        SelRerandVerifyingParams<PallasAffine, VestaAffine>
    ) {
        let (sr_params, sr_proving_params, sr_verifying_params) = generate_pallas_sel_rerand_params::<L>();

        let curve_tree = CurveTree::<PallasAffine, VestaAffine, L>::from_leaves(leaves, &sr_params, height);

        (curve_tree, sr_proving_params, sr_verifying_params)
    }

    #[test]
    fn mint() {
        let mut rng = OsRng;

        let k = 13;
        const L: usize = 1024;
        let height = 3;
        let num_leaves = 1 << height;

        // Use helper functions for setup
        let (circuit_params, pk, vk) = setup_curve_tree_params_for_state_transition::<L>(k, height);
        
        // Generate random leaves
        let leaves: Vec<_> = (0..num_leaves)
            .map(|_| pallas::Point::random(&mut rng).to_affine())
            .collect();
            
        let (curve_tree, sr_proving_params, sr_verifying_params) = setup_account_tree_with_leaves::<L>(&leaves, Some(height as u8));

        assert_eq!(curve_tree.height(), height as u8);
        let root = curve_tree.root_node();

        let leaf_index = 0;

        let initial_rho = pallas::Scalar::random(&mut rng);
        let old_current_rho = pallas::Scalar::random(&mut rng);
        let new_current_rho = initial_rho * old_current_rho;
        let old_randomness = pallas::Scalar::random(&mut rng);
        let new_randomness = old_randomness.square();

        let path = curve_tree.get_path_to_leaf_for_proof(leaf_index, 0);

        let (
            even_layer_witnesses,
            odd_layer_witnesses,
            even_layer_public_inputs,
            odd_layer_public_inputs,
            mut re_randomized_path,
            _
        ) = path.prepare_witness::<_, PallasEc, VestaEc>(&mut rng, &sr_proving_params);

        let odd_layer_circuit = StateTransitionCircuit::<PallasAffine, VestaEc, L>::new(
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            odd_layer_witnesses
        );

        let even_layer_circuit = MultiLayerCircuit::<PallasEc, L> {
            layers: even_layer_witnesses,
        };

        let prover_even = MockProver::run(circuit_params.odd.k, &even_layer_circuit, vec![even_layer_public_inputs.clone()]).unwrap();
        prover_even.assert_satisfied();
        let prover_odd = MockProver::run(circuit_params.even.k, &odd_layer_circuit, vec![odd_layer_public_inputs.clone()]).unwrap();
        prover_odd.assert_satisfied();

        let start = Instant::now();
        // TODO: Check if this is always correct since we consider only queries to advice columns but some circuits might
        // have no advice columns.
        let num_blindings = pk.even.get_vk().blinding_factors() + 2;
        let blinding_rows = (0..num_blindings)
            .map(|_| pallas::Scalar::random(&mut rng))
            .collect::<Vec<_>>();

        let mut transcript_even = Blake2bWrite::<_, PallasAffine, Challenge255<_>>::init(vec![]);

        create_proof_with_given_column_blindings(
            &circuit_params.even,
            &pk.even,
            &[odd_layer_circuit],
            &[&[&odd_layer_public_inputs]],
            vec![Some(vec![blinding_rows.clone()])],
            &mut rng,
            &mut transcript_even,
        )
            .unwrap();
        let proof_odd = transcript_even.finalize();

        let mut transcript_odd = Blake2bWrite::<_, VestaAffine, Challenge255<_>>::init(vec![]);
        create_proof(
            &circuit_params.odd,
            &pk.odd,
            &[even_layer_circuit],
            &[&[&even_layer_public_inputs]],
            &mut rng,
            &mut transcript_odd,
        )
            .unwrap();
        let proof_even = transcript_odd.finalize();

        println!("For tree height={height} and L={L}");
        println!("Proving time: {:?}", start.elapsed());
        println!("Proof size: {} bytes", proof_odd.len() + proof_even.len());

        let start = Instant::now();

        let mut transcript_even = Blake2bRead::<_, _, Challenge255<_>>::init(proof_odd.as_slice());
        let mut transcript_odd = Blake2bRead::<_, _, Challenge255<_>>::init(proof_even.as_slice());
        let rerandomized_leaf = re_randomized_path.select_and_rerandomize_verifier_gadget::<
            _, _, _, _
        >(
            &root, &sr_verifying_params,
            &circuit_params,
            &vk,
            &mut transcript_even, &mut transcript_odd
        ).unwrap();

        println!("Verification time: {:?}", start.elapsed());

        // Verify commitment
        let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(proof_odd.as_slice());
        let precommitted_commitment = get_the_only_precommitted_col_comm(&vk.even, &mut transcript).unwrap();

        let domain = vk.even.get_domain();

        let mut precommitted = domain.empty_lagrange();
        precommitted[PRECOMMITTED_INITIAL_RHO_IDX] = initial_rho;
        precommitted[PRECOMMITTED_OLD_CURRENT_RHO_IDX] = old_current_rho;
        precommitted[PRECOMMITTED_NEW_CURRENT_RHO_IDX] = new_current_rho;
        precommitted[PRECOMMITTED_OLD_RANDOMNESS_IDX] = old_randomness;
        precommitted[PRECOMMITTED_NEW_RANDOMNESS_IDX] = new_randomness;

        let usable_rows = circuit_params.even.n as usize - (num_blindings - 1);
        for (i, v) in precommitted[usable_rows..].iter_mut().enumerate() {
            *v = blinding_rows[i];
        }
        let comm = circuit_params.even
            .commit_lagrange(&precommitted, (*blinding_rows.last().unwrap()).into())
            .into();
        assert_eq!(precommitted_commitment, comm);
    }
}