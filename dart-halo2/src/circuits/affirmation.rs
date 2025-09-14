use core::marker::PhantomData;
use ct_halo2::ec_chip::Ec;
use ct_halo2::multi_layer::{MultiLayerChip, MultiLayerConfig, SingleLayerWitness};
use ff::PrimeField;
use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheck;
use halo2_proofs::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2_proofs::plonk::{Circuit, Column, ConstraintSystem, Error, Expression, Instance, Precommitted, Selector, TableColumn};
use halo2_proofs::poly::Rotation;
use crate::AffineSerializable;

pub const PRECOMMITTED_INITIAL_RHO_IDX: usize = 0;
pub const PRECOMMITTED_OLD_CURRENT_RHO_IDX: usize = 1;
pub const PRECOMMITTED_NEW_CURRENT_RHO_IDX: usize = 2;
pub const PRECOMMITTED_OLD_RANDOMNESS_IDX: usize = 3;
pub const PRECOMMITTED_NEW_RANDOMNESS_IDX: usize = 4;
pub const PRECOMMITTED_FLAG_IDX: usize = 5;
pub const PRECOMMITTED_OLD_BALANCE_IDX: usize = 6;
pub const PRECOMMITTED_AMOUNT_IDX: usize = 7;
pub const PRECOMMITTED_NEW_BALANCE_IDX: usize = 8;

#[derive(Clone, Debug)]
pub struct StateTransitionWithBalanceChangeCircuit<
    P: AffineSerializable,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    Lookup: LookupRangeCheck<P::Scalar, LIMB_BITS>,
    const LIMB_BITS: usize,
    const ARITY: usize
> {
    num_words: usize,
    initial_rho: Value<P::Scalar>,
    old_current_rho: Value<P::Scalar>,
    new_current_rho: Value<P::Scalar>,
    old_randomness: Value<P::Scalar>,
    new_randomness: Value<P::Scalar>,
    amount: Value<P::Scalar>,
    old_balance: Value<P::Scalar>,
    new_balance: Value<P::Scalar>,
    pub tree_witness: Vec<SingleLayerWitness<E, ARITY>>,
    _marker: PhantomData<Lookup>,
}

impl<
    P: AffineSerializable,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    Lookup: LookupRangeCheck<P::Scalar, LIMB_BITS>,
    const LIMB_BITS: usize,
    const ARITY: usize
> StateTransitionWithBalanceChangeCircuit<P, E, Lookup, LIMB_BITS, ARITY> {
    pub fn new(
        num_words: usize,
        initial_rho: Value<P::Scalar>,
        old_current_rho: Value<P::Scalar>,
        new_current_rho: Value<P::Scalar>,
        old_randomness: Value<P::Scalar>,
        new_randomness: Value<P::Scalar>,
        amount: Value<P::Scalar>,
        old_balance: Value<P::Scalar>,
        new_balance: Value<P::Scalar>,
        tree_witness: Vec<SingleLayerWitness<E, ARITY>>,
    ) -> Self {
        Self {
            num_words,
            initial_rho,
            old_current_rho,
            new_current_rho,
            old_randomness,
            new_randomness,
            amount,
            old_balance,
            new_balance,
            tree_witness,
            _marker: PhantomData,
        }
    }
}

#[derive(Clone)]
pub struct StateTransitionWithBalanceChangeConfig<
    E: Ec,
    Lookup: LookupRangeCheck<E::Base, LIMB_BITS> + Clone,
    const LIMB_BITS: usize,
> {
    pub precommitted: Column<Precommitted>,
    pub product: Selector,
    pub square: Selector,
    pub balance_change: Selector,
    pub instance: Column<Instance>,
    pub lookup_config: Lookup,
    pub table_idx: TableColumn,
    pub ct_config: MultiLayerConfig<E>,
}

impl<
    F: PrimeField,
    P: AffineSerializable<ScalarExt = F>,
    E: Ec<Base = P::ScalarExt, Scalar = P::Base>,
    Lookup: LookupRangeCheck<F, LIMB_BITS> + Clone,
    const LIMB_BITS: usize,
    const ARITY: usize
> Circuit<F> for StateTransitionWithBalanceChangeCircuit<P, E, Lookup, LIMB_BITS, ARITY> where {

    type Config = StateTransitionWithBalanceChangeConfig<E, Lookup, LIMB_BITS>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        // TODO: Needed for V1
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let precommitted = meta.precommitted_column();
        let product = meta.selector();
        let square = meta.selector();
        let balance_change = meta.selector();
        // TODO: This column can be merged with MultiLayerChip's instance column (which hold re-randomized points)
        let instance = meta.instance_column();
        meta.enable_equality(precommitted);
        meta.enable_equality(instance);

        meta.create_gate("product", |meta| {
            let s = meta.query_selector(product);
            let initial_row = meta.query_precommitted(precommitted, Rotation::cur());
            let old_rho = meta.query_precommitted(precommitted, Rotation::next());
            let new_rho = meta.query_precommitted(precommitted, Rotation(2));
            vec![s * (new_rho - (initial_row * old_rho))]
        });

        meta.create_gate("square", |meta| {
            let s = meta.query_selector(square);
            let old_randomness = meta.query_precommitted(precommitted, Rotation::cur());
            let new_randomness = meta.query_precommitted(precommitted, Rotation::next());
            vec![s * (new_randomness - old_randomness.square())]
        });

        // Enforce new_balance = old_balance + (b - 1) * amount
        meta.create_gate("balance_change", |meta| {
            let s = meta.query_selector(balance_change);
            // Not enforcing if flag is an acceptable value since its instance and verifier should set it correctly
            let flag = meta.query_precommitted(precommitted, Rotation::cur());
            let old_balance = meta.query_precommitted(precommitted, Rotation::next());
            let amount = meta.query_precommitted(precommitted, Rotation(2));
            let new_balance = meta.query_precommitted(precommitted, Rotation(3));

            vec![s * (new_balance - old_balance - ((flag - Expression::Constant(F::ONE)) * amount))]
        });

        let running_sum = meta.advice_column();
        let table_idx = meta.lookup_table_column();
        let constants = meta.fixed_column();
        meta.enable_constant(constants);

        let lookup_config = Lookup::configure(meta, running_sum, table_idx);

        let ct_config = MultiLayerChip::<E, ARITY>::configure(meta);

        StateTransitionWithBalanceChangeConfig {
            precommitted,
            product,
            square,
            balance_change,
            instance,
            lookup_config,
            table_idx,
            ct_config
        }
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        // Load table values for range check
        layouter.assign_table(
            || "table_idx",
            |mut table| {
                for index in 0..(1 << LIMB_BITS) {
                    table.assign_cell(
                        || "table_idx",
                        config.table_idx,
                        index,
                        || Value::known(F::from(index as u64)),
                    )?;
                }
                Ok(())
            },
        )?;

        let new_balance_cell = layouter.assign_region(
            || "affirmation-with-balance-change",
            |mut region| {
                // flag value will be read directly in the constraint through the instance column

                config.product.enable(&mut region, 0)?;
                region.assign_precommitted(|| "initial_rho", config.precommitted, 0, || self.initial_rho)?;
                region.assign_precommitted(|| "old_current_rho", config.precommitted, 1, || self.old_current_rho)?;
                region.assign_precommitted(|| "new_current_rho", config.precommitted, 2, || self.new_current_rho)?;

                config.square.enable(&mut region, 3)?;
                region.assign_precommitted(|| "old_randomness", config.precommitted, 3, || self.old_randomness)?;
                region.assign_precommitted(|| "new_randomness", config.precommitted, 4, || self.new_randomness)?;

                config.balance_change.enable(&mut region, 5)?;
                region.assign_precommitted_from_instance(
                    || "load flag",
                    config.instance,
                    0,
                    config.precommitted,
                    5,
                )?;
                region.assign_precommitted(|| "old_balance", config.precommitted, 6, || self.old_balance)?;
                region.assign_precommitted(|| "amount", config.precommitted, 7, || self.amount)?;
                region.assign_precommitted(|| "new_balance", config.precommitted, 8, || self.new_balance)
            },
        )?;

        // Apply range proof over new_balance
        let new_balance_rs = config.lookup_config.witness_check(
            layouter.namespace(|| "range check new_balance"),
            self.new_balance,
            self.num_words, // num_words parameter, so range proof covers [0, 2^{LIMB_BITS*num_words})
            true,
        )?;

        layouter.assign_region(
            || "constraint new_balance",
            |mut region| {
                region.constrain_equal(new_balance_rs[0].cell(), new_balance_cell.cell())?;
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
    use ct_halo2::multi_layer::{MultiLayerCircuit, SingleLayerWitness};
    use ct_halo2::tree::params::{CTCircuitParams, CTProvingKey, CTVerifyingKey};
    use ff::Field;
    use group::{Curve, Group};
    use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::plonk::{keygen_vk, keygen_pk, create_proof_with_given_column_blindings, create_proof, get_the_only_precommitted_col_comm};
    use halo2_proofs::poly::commitment::Params;
    use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use pasta_curves::{pallas, vesta};
    use rand_core::OsRng;
    use crate::circuits::mint::tests::setup_account_tree_with_leaves;

    type PallasAffine = pallas::Affine;
    type VestaAffine = vesta::Affine;

    // TODO: Remove hardcoding
    const LIMB_BITS: usize = 6;
    const NUM_WORDS: usize = 8;

    /// Generate circuit parameters and keys for curve tree operations with affirmation circuit
    pub fn setup_curve_tree_params_for_affirm<const L: usize>(
        k: u32,
        height: usize,
    ) -> (
        CTCircuitParams<PallasAffine, VestaAffine>,
        CTProvingKey<PallasAffine, VestaAffine>,
        CTVerifyingKey<PallasAffine, VestaAffine>,
    ) {
        let params_odd = Params::<PallasAffine>::new(k);
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

        let empty_odd_circuit = StateTransitionWithBalanceChangeCircuit::<PallasAffine, VestaEc, LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>, LIMB_BITS, L>::new(
            NUM_WORDS,
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            Value::unknown(),
            empty_odd_layer_witnesses
        );

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

        println!("6");
        (circuit_params, ct_pk, ct_vk)
    }

    #[test]
    fn affirmation_with_balance_change() {
        let mut rng = OsRng;

        let k = 11;
        const L: usize = 1024;
        let height = 2;
        let num_leaves = 1 << height;

        let (circuit_params, pk, vk) = setup_curve_tree_params_for_affirm::<L>(k, height);
        
        let leaves: Vec<_> = (0..num_leaves)
            .map(|_| pallas::Point::random(&mut rng).to_affine())
            .collect();
            
        let (curve_tree, sr_proving_params, _) = setup_account_tree_with_leaves::<L>(&leaves, Some(height as u8));

        assert_eq!(curve_tree.height(), height as u8);
        let root = curve_tree.root_node();

        let leaf_index = 0;

        let initial_rho = pallas::Scalar::random(&mut rng);
        let old_current_rho = pallas::Scalar::random(&mut rng);
        let new_current_rho = initial_rho * old_current_rho;
        let old_randomness = pallas::Scalar::random(&mut rng);
        let new_randomness = old_randomness.square();

        let amount = pallas::Scalar::from(100u64);
        let old_balance = pallas::Scalar::from(500u64);
        let new_balance = old_balance + amount;

        // flag = 2 for when new_balance > old_balance, flag = 0 when new_balance < old_balance
        let flag = pallas::Scalar::from(2u64);

        assert_eq!(new_balance, old_balance + (flag - pallas::Scalar::ONE) * amount);

        let path = curve_tree.get_path_to_leaf_for_proof(leaf_index, 0);

        let (
            even_layer_witnesses,
            odd_layer_witnesses,
            even_layer_public_inputs,
            odd_layer_public_inputs,
            re_randomized_path,
            _
        ) = path.prepare_witness::<_, PallasEc, VestaEc>(&mut rng, &sr_proving_params);

        let odd_layer_circuit = StateTransitionWithBalanceChangeCircuit::<PallasAffine, VestaEc, LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>, LIMB_BITS, L>::new(
            NUM_WORDS,
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            Value::known(amount),
            Value::known(old_balance),
            Value::known(new_balance),
            odd_layer_witnesses
        );

        let even_layer_circuit = MultiLayerCircuit::<PallasEc, L> {
            layers: even_layer_witnesses,
        };

        let prover_even = MockProver::run(circuit_params.odd.k, &even_layer_circuit, vec![even_layer_public_inputs.clone()]).unwrap();
        prover_even.assert_satisfied();
        let prover_odd = MockProver::run(circuit_params.even.k, &odd_layer_circuit, vec![vec![flag], odd_layer_public_inputs.clone()]).unwrap();
        prover_odd.assert_satisfied();

        let start = Instant::now();
        let num_blindings = pk.even.get_vk().blinding_factors() + 2;
        let blinding_rows = (0..num_blindings)
            .map(|_| pallas::Scalar::random(&mut rng))
            .collect::<Vec<_>>();

        let mut transcript_even = Blake2bWrite::<_, PallasAffine, Challenge255<_>>::init(vec![]);

        create_proof_with_given_column_blindings(
            &circuit_params.even,
            &pk.even,
            &[odd_layer_circuit],
            &[&[&[flag], &odd_layer_public_inputs]],
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
        let (even_layer_public_inputs, odd_layer_public_inputs) = re_randomized_path.prepare_inputs(&root, &sr_proving_params.verifying_params());
        let odd_inputs = vec![vec![flag], odd_layer_public_inputs];
        re_randomized_path.verify(
            &circuit_params,
            &vk,
            &[&[&even_layer_public_inputs]],
            &[odd_inputs.iter().map(|v| v.as_slice()).collect::<Vec<_>>().as_slice()],
            &mut transcript_even,
            &mut transcript_odd,
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
        precommitted[PRECOMMITTED_FLAG_IDX] = flag;
        precommitted[PRECOMMITTED_OLD_BALANCE_IDX] = old_balance;
        precommitted[PRECOMMITTED_AMOUNT_IDX] = amount;
        precommitted[PRECOMMITTED_NEW_BALANCE_IDX] = new_balance;

        let usable_rows = circuit_params.even.n as usize - (num_blindings - 1);
        for (i, v) in precommitted[usable_rows..].iter_mut().enumerate() {
            *v = blinding_rows[i];
        }
        let comm = circuit_params.even
            .commit_lagrange(&precommitted, (*blinding_rows.last().unwrap()).into())
            .into();
        assert_eq!(precommitted_commitment, comm);

        // Test with flag = 0 (balance decrease)
        let amount = pallas::Scalar::from(200u64);
        let old_balance = pallas::Scalar::from(1000u64);
        let new_balance = old_balance - amount;
        let flag = pallas::Scalar::from(0u64);

        let (
            even_layer_witnesses,
            odd_layer_witnesses,
            even_layer_public_inputs,
            odd_layer_public_inputs,
            re_randomized_path,
            _
        ) = path.prepare_witness::<_, PallasEc, VestaEc>(&mut rng, &sr_proving_params);

        let odd_layer_circuit = StateTransitionWithBalanceChangeCircuit::<PallasAffine, VestaEc, LookupRangeCheckConfig<pallas::Scalar, LIMB_BITS>, LIMB_BITS, L>::new(
            NUM_WORDS, // num_words = 4
            Value::known(initial_rho),
            Value::known(old_current_rho),
            Value::known(new_current_rho),
            Value::known(old_randomness),
            Value::known(new_randomness),
            Value::known(amount),
            Value::known(old_balance),
            Value::known(new_balance),
            odd_layer_witnesses
        );

        let even_layer_circuit = MultiLayerCircuit::<PallasEc, L> {
            layers: even_layer_witnesses,
        };

        let prover_even = MockProver::run(circuit_params.odd.k, &even_layer_circuit, vec![even_layer_public_inputs.clone()]).unwrap();
        prover_even.assert_satisfied();
        let prover_odd = MockProver::run(circuit_params.even.k, &odd_layer_circuit, vec![vec![flag], odd_layer_public_inputs.clone()]).unwrap();
        prover_odd.assert_satisfied();

        let blinding_rows = (0..num_blindings)
            .map(|_| pallas::Scalar::random(&mut rng))
            .collect::<Vec<_>>();

        let mut transcript_even = Blake2bWrite::<_, PallasAffine, Challenge255<_>>::init(vec![]);
        create_proof_with_given_column_blindings(
            &circuit_params.even,
            &pk.even,
            &[odd_layer_circuit],
            &[&[&[flag], &odd_layer_public_inputs]],
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

        let mut transcript_even = Blake2bRead::<_, _, Challenge255<_>>::init(proof_odd.as_slice());
        let mut transcript_odd = Blake2bRead::<_, _, Challenge255<_>>::init(proof_even.as_slice());
        let (even_layer_public_inputs, odd_layer_public_inputs) = re_randomized_path.prepare_inputs(&root, &sr_proving_params.verifying_params());
        let odd_inputs = vec![vec![flag], odd_layer_public_inputs];
        re_randomized_path.verify(
            &circuit_params,
            &vk,
            &[&[&even_layer_public_inputs]],
            &[odd_inputs.iter().map(|v| v.as_slice()).collect::<Vec<_>>().as_slice()],
            &mut transcript_even,
            &mut transcript_odd,
        ).unwrap();
    }
}