use std::marker::PhantomData;
use ff::Field;
use halo2_poseidon::{Mds, Spec};

#[derive(Debug)]
pub struct PoseidonParams<F: Field>(PhantomData<F>);

impl<F: Field> Spec<F, 3, 2> for PoseidonParams<F> {
    fn full_rounds() -> usize {
        8
    }

    fn partial_rounds() -> usize {
        56
    }

    fn sbox(val: F) -> F {
        val.pow([5])
    }

    fn secure_mds() -> usize {
        unimplemented!()
    }

    fn constants() -> (Vec<[F; 3]>, Mds<F, 3>, Mds<F, 3>) {
        // This is wrong and not possible without atm
        // (
        //     halo2_poseidon::fp::ROUND_CONSTANTS[..].to_vec(),
        //     halo2_poseidon::fp::MDS,
        //     halo2_poseidon::fp::MDS_INV,
        // )
        todo!()
    }
}