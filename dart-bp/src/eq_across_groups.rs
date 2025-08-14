// This is a temporary file. The crate isn't compiling currently so copying the file for just now

//! Sigma protocol for proving that two values committed in different groups are equal. As described in Figure 1 and its
//! extension in section 5 of the paper [Proofs of discrete logarithm equality across groups](https://eprint.iacr.org/2022/1593).
//!
//! Support proving with and without range proofs. For range proofs, Bulletproofs++ is used. The current Bulletproofs++ works over
//! 64-bit integers and can aggregate number of range proofs if that number is a power of 2. So the tests work with 64-bit, 4-chunks.
//!
//! Following is the map of symbols in the code to those in the paper
//! `WITNESS_BIT_SIZE` -> `b_x`
//! `CHALLENGE_BIT_SIZE` -> `b_c`
//! `ABORT_PARAM` -> `b_f`
//! `NUM_REPS` -> `tau`
//!
//! `RESPONSE_BYTE_SIZE` is the number of bytes need to represent `z` which lies in `[2^{WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE}, 2^{WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE + ABORT_PARAM} - 1]`
//!
//! The groups are assumed to be elliptic curve groups.

use ark_ec::{AffineRepr, VariableBaseMSM};
use ark_ff::{BigInt, BigInteger, PrimeField, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use ark_std::{rand::RngCore, vec, vec::Vec, UniformRand};
use crypto_bigint::{BoxedUint, RandomBits};
use dock_crypto_utils::{commitment::PedersenCommitmentKey, transcript::Transcript};
use schnorr_pok::error::SchnorrError;

/// The proof described in Figure 1 can have many repetitions of a sigma protocol. This is one repetition.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default, CanonicalSerialize, CanonicalDeserialize)]
pub struct ProofSingleRep<
    G1: AffineRepr,
    G2: AffineRepr,
    const WITNESS_BIT_SIZE: usize,
    const CHALLENGE_BIT_SIZE: usize,
    const ABORT_PARAM: usize,
    const RESPONSE_BYTE_SIZE: usize,
> {
    /// Commitment to the randomness in group G1, called `K_p` in the paper
    pub k1_com: G1,
    /// Response in group G1, called `s_p` in the paper
    pub s1: G1::ScalarField,
    /// Commitment to the randomness in group G2, called `K_p` in the paper
    pub k2_com: G2,
    /// Response in group G2, called `s_q` in the paper
    pub s2: G2::ScalarField,
    pub z: BigInt<RESPONSE_BYTE_SIZE>,
}

/// Sigma protocol described in Figure 1. Optionally can contain a range proof if the verifier is not convinced
/// of the range of witness. Expects the witness to be in `[0, 2^WITNESS_BIT_SIZE)`
/// By convention, G1 is the group for range proof
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct Proof<
    G1: AffineRepr,
    G2: AffineRepr,
    const WITNESS_BIT_SIZE: usize,
    const CHALLENGE_BIT_SIZE: usize,
    const ABORT_PARAM: usize,
    const RESPONSE_BYTE_SIZE: usize,
    const NUM_REPS: usize,
> {
    pub eq: [ProofSingleRep<
        G1,
        G2,
        WITNESS_BIT_SIZE,
        CHALLENGE_BIT_SIZE,
        ABORT_PARAM,
        RESPONSE_BYTE_SIZE,
    >; NUM_REPS],
}

impl<
    G1: AffineRepr,
    G2: AffineRepr,
    const WITNESS_BIT_SIZE: usize,
    const CHALLENGE_BIT_SIZE: usize,
    const ABORT_PARAM: usize,
    const RESPONSE_BYTE_SIZE: usize,
    const NUM_REPS: usize,
>
Proof<G1, G2, WITNESS_BIT_SIZE, CHALLENGE_BIT_SIZE, ABORT_PARAM, RESPONSE_BYTE_SIZE, NUM_REPS>
{
    // ceil((WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE + ABORT_PARAM)/8) == RESPONSE_BYTE_SIZE
    const CHECK_RESP_SIZE: () = assert!(
        (WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE + ABORT_PARAM + 7) / 8 == RESPONSE_BYTE_SIZE
    );
    const CHECK_REP_COUNT: () = assert!((NUM_REPS * CHALLENGE_BIT_SIZE) >= 128,);
    const CHECK_GROUP_SIZE: () = assert!(
        // 2^(WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE + ABORT_PARAM) < min(g1_modulus_bitsize, g2_modulus_bitsize)
        ((WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE + ABORT_PARAM) as u32)
            < if G1::ScalarField::MODULUS_BIT_SIZE > G2::ScalarField::MODULUS_BIT_SIZE {
                G2::ScalarField::MODULUS_BIT_SIZE
            } else {
                G1::ScalarField::MODULUS_BIT_SIZE
            },
    );

    /// `r1` and `r2` are the randomness used in commitment to `witness` in groups G1 and G2 respectively
    /// This does not include the commitments, commitment key or any public parameters into the transcript.
    /// The caller should ensure that they have been added before
    pub fn new<R: RngCore>(
        rng: &mut R,
        witness: &G1::ScalarField,
        r1: G1::ScalarField,
        r2: G2::ScalarField,
        comm_key_g1: &PedersenCommitmentKey<G1>,
        comm_key_g2: &PedersenCommitmentKey<G2>,
        transcript: &mut (impl Transcript + Clone),
    ) -> Result<Self, Error> {
        Ok(Self {
            eq: Self::new_equality_proof_only(
                rng,
                witness,
                r1,
                r2,
                comm_key_g1,
                comm_key_g2,
                transcript,
            )?,
        })
    }

    /// Verifies the proof of equality without checking for range proof.
    /// `comm_g1` and `comm_g2` are the commitments to `witness` in groups G1 and G2 respectively.
    /// This does not include the commitments, commitment key or any public parameters into the transcript.
    /// The caller should ensure that they have been added before
    pub fn verify(
        &self,
        comm_g1: &G1,
        comm_g2: &G2,
        comm_key_g1: &PedersenCommitmentKey<G1>,
        comm_key_g2: &PedersenCommitmentKey<G2>,
        transcript: &mut impl Transcript,
    ) -> Result<(), Error> {
        Self::verify_equality_proof_only(
            &self.eq,
            comm_g1,
            comm_g2,
            comm_key_g1,
            comm_key_g2,
            transcript,
        )
    }

    pub fn new_equality_proof_only<R: RngCore>(
        rng: &mut R,
        witness: &G1::ScalarField,
        r1: G1::ScalarField,
        r2: G2::ScalarField,
        comm_key_g1: &PedersenCommitmentKey<G1>,
        comm_key_g2: &PedersenCommitmentKey<G2>,
        transcript: &mut (impl Transcript + Clone),
    ) -> Result<
        [ProofSingleRep<
            G1,
            G2,
            WITNESS_BIT_SIZE,
            CHALLENGE_BIT_SIZE,
            ABORT_PARAM,
            RESPONSE_BYTE_SIZE,
        >; NUM_REPS],
        Error,
    > {
        Self::static_asserts();
        let mut proofs = [ProofSingleRep::<
            G1,
            G2,
            WITNESS_BIT_SIZE,
            CHALLENGE_BIT_SIZE,
            ABORT_PARAM,
            RESPONSE_BYTE_SIZE,
        >::default(); NUM_REPS];

        let (min_resp, max_resp) = Self::max_min_resp();

        let x = witness.into_bigint();
        for (i, b) in x.to_bits_le().into_iter().enumerate() {
            if i >= WITNESS_BIT_SIZE {
                if b {
                    return Err(Error::WitnessBiggerThanExpected);
                }
            }
        }

        let wit_byte_size = Self::witness_byte_size();
        let mut x_bytes = x.to_bytes_le();
        x_bytes.drain(wit_byte_size..);

        let mut proof_count = 0;
        while proof_count < NUM_REPS {
            // clone the transcript and make changes to the cloned one as in case of abort the changes made to
            // the transcript need to be reverted and there is no function to revert an addition to the transcript.
            // In case of no abort, transcript will be set to this cloned one.
            let mut curr_trans = transcript.clone();

            let k = BoxedUint::try_random_bits(
                rng,
                (WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE + ABORT_PARAM) as u32,
            )
                .unwrap();

            let k_bytes = k.to_le_bytes();

            let k1 = G1::ScalarField::from_le_bytes_mod_order(&k_bytes);
            let k2 = G2::ScalarField::from_le_bytes_mod_order(&k_bytes);
            let t1 = G1::ScalarField::rand(rng);
            let t2 = G2::ScalarField::rand(rng);

            let k1_com = comm_key_g1.commit(&k1, &t1);
            let k2_com = comm_key_g2.commit(&k2, &t2);

            let c_bytes = Self::challenge_bytes(&k1_com, &k2_com, &mut curr_trans);

            let c = BoxedUint::from_le_slice(&c_bytes, c_bytes.len() as u32 * 8).unwrap();
            let x = BoxedUint::from_le_slice(&x_bytes, wit_byte_size as u32 * 8).unwrap();
            let z = k + (c * x);
            let z = from_bytes_le::<RESPONSE_BYTE_SIZE>(&z.to_le_bytes());

            if z < min_resp || z > max_resp {
                // Abort and restart this repetition
                continue;
            }

            *transcript = curr_trans;

            let c1 = G1::ScalarField::from_le_bytes_mod_order(&c_bytes);
            let c2 = G2::ScalarField::from_le_bytes_mod_order(&c_bytes);
            let s1 = t1 + c1 * r1;
            let s2 = t2 + c2 * r2;
            proofs[proof_count] = ProofSingleRep {
                k1_com,
                s1,
                k2_com,
                s2,
                z,
            };
            proof_count += 1;
        }
        Ok(proofs)
    }

    pub fn verify_equality_proof_only(
        eq: &[ProofSingleRep<
            G1,
            G2,
            WITNESS_BIT_SIZE,
            CHALLENGE_BIT_SIZE,
            ABORT_PARAM,
            RESPONSE_BYTE_SIZE,
        >; NUM_REPS],
        comm_g1: &G1,
        comm_g2: &G2,
        comm_key_g1: &PedersenCommitmentKey<G1>,
        comm_key_g2: &PedersenCommitmentKey<G2>,
        transcript: &mut impl Transcript,
    ) -> Result<(), Error> {
        Self::static_asserts();
        let (min_resp, max_resp) = Self::max_min_resp();
        for i in 0..NUM_REPS {
            if eq[i].z < min_resp || eq[i].z > max_resp {
                return Err(Error::ZOutOfRangeForRep(i));
            }
            let z_bytes = eq[i].z.to_bytes_le();
            let z1 = G1::ScalarField::from_le_bytes_mod_order(&z_bytes);
            let z2 = G2::ScalarField::from_le_bytes_mod_order(&z_bytes);

            let c_bytes = Self::challenge_bytes(&eq[i].k1_com, &eq[i].k2_com, transcript);

            let c1 = G1::ScalarField::from_le_bytes_mod_order(&c_bytes);
            let c2 = G2::ScalarField::from_le_bytes_mod_order(&c_bytes);

            if comm_key_g1.commit_as_projective(&z1, &eq[i].s1) != (eq[i].k1_com + comm_g1.mul(&c1))
            {
                return Err(Error::SchnorrCheckFailedForRep(i));
            }
            if comm_key_g2.commit_as_projective(&z2, &eq[i].s2) != (eq[i].k2_com + comm_g2.mul(&c2))
            {
                return Err(Error::SchnorrCheckFailedForRep(i));
            }
        }
        Ok(())
    }

    /// Minimum and maximum values of the response `z`
    fn max_min_resp() -> (BigInt<RESPONSE_BYTE_SIZE>, BigInt<RESPONSE_BYTE_SIZE>) {
        let mut max_resp = BigInt::<RESPONSE_BYTE_SIZE>::one();
        let mut min_resp = BigInt::<RESPONSE_BYTE_SIZE>::one();
        for i in 0..WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE + ABORT_PARAM {
            max_resp.mul2();
            if i < WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE {
                min_resp.mul2();
            }
        }
        max_resp.sub_with_borrow(&BigInt::one());
        (min_resp, max_resp)
    }

    /// Generate challenge from transcript by adding `k1_com`, `k2_com` and ensuring that the challenge
    /// is of `CHALLENGE_BIT_SIZE` bits max.
    fn challenge_bytes(k1_com: &G1, k2_com: &G2, transcript: &mut impl Transcript) -> Vec<u8> {
        transcript.append(b"K1", k1_com);
        transcript.append(b"K2", k2_com);

        let chal_byte_size = Self::challenge_byte_size();
        let mut c_bytes = vec![0; chal_byte_size];
        transcript.challenge_bytes(b"challenge", &mut c_bytes);

        // if CHALLENGE_BIT_SIZE is not multiple of 8, then unset MSBs beyond CHALLENGE_BIT_SIZE
        c_bytes[chal_byte_size - 1] = c_bytes[chal_byte_size - 1] & Self::challenge_mask();
        c_bytes
    }

    /// ceil(WITNESS_BIT_SIZE/8)
    const fn witness_byte_size() -> usize {
        (WITNESS_BIT_SIZE + 7) / 8
    }

    /// ceil(CHALLENGE_BIT_SIZE/8)
    const fn challenge_byte_size() -> usize {
        (CHALLENGE_BIT_SIZE + 7) / 8
    }

    /// if CHALLENGE_BIT_SIZE is not multiple of 8, then the mask used to unset MSBs beyond CHALLENGE_BIT_SIZE
    const fn challenge_mask() -> u8 {
        u8::MAX << (Self::challenge_byte_size() * 8 - CHALLENGE_BIT_SIZE)
    }

    const fn static_asserts() {
        let _ = Self::CHECK_RESP_SIZE;
        let _ = Self::CHECK_REP_COUNT;
        let _ = Self::CHECK_GROUP_SIZE;
    }
}

fn from_bytes_le<const LIMBS: usize>(bytes: &[u8]) -> BigInt<LIMBS> {
    let mut res = BigInt::zero();
    for (i, bytes_8) in bytes.chunks(8).enumerate() {
        let mut b_8 = [0; 8];
        for j in 0..bytes_8.len() {
            b_8[j] = bytes_8[j];
        }
        res.0[i] = u64::from_le_bytes(b_8);
    }
    res
}

#[derive(Debug)]
pub enum Error {
    WitnessBiggerThanExpected,
    ZOutOfRangeForRep(usize),
    SchnorrCheckFailedForRep(usize),
    Schnorr(SchnorrError),
    Serialization(SerializationError),
}

impl From<SchnorrError> for Error {
    fn from(e: SchnorrError) -> Self {
        Self::Schnorr(e)
    }
}

impl From<SerializationError> for Error {
    fn from(e: SerializationError) -> Self {
        Self::Serialization(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blake2::Blake2b512;
    use dock_crypto_utils::{transcript::new_merlin_transcript};
    use rand_core::OsRng;

    type PallasA = ark_pallas::Affine;
    type VestaA = ark_vesta::Affine;

    #[test]
    fn check_without_range_proof() {
        macro_rules! check {
            ($fn_name: ident, $wit_size: expr, $chal_bit_size: expr, $abort_p: expr, $resp_size: expr, $num_reps: expr, $g1: ident, $g2: ident) => {
                fn $fn_name() {
                    let mut rng = OsRng::default();
                    const WITNESS_BIT_SIZE: usize = $wit_size;
                    const CHALLENGE_BIT_SIZE: usize = $chal_bit_size;
                    const ABORT_PARAM: usize = $abort_p;
                    const RESPONSE_BYTE_SIZE: usize = $resp_size;
                    const NUM_REPS: usize = $num_reps;
                    assert_eq!(
                        (WITNESS_BIT_SIZE + CHALLENGE_BIT_SIZE + ABORT_PARAM + 7) / 8
                            , RESPONSE_BYTE_SIZE
                    );

                    let comm_key1 = PedersenCommitmentKey::<$g1>::new::<Blake2b512>(b"test");
                    let comm_key2 = PedersenCommitmentKey::<$g2>::new::<Blake2b512>(b"test");

                    // Since testing with WITNESS_BIT_SIZE > 32
                    let x = <$g1 as AffineRepr>::ScalarField::from(u32::rand(&mut rng));
                    let mut x_bytes = vec![];
                    x.serialize_compressed(&mut x_bytes).unwrap();

                    let x1 = <$g1 as AffineRepr>::ScalarField::from_le_bytes_mod_order(&x_bytes);
                    let x2 = <$g2 as AffineRepr>::ScalarField::from_le_bytes_mod_order(&x_bytes);
                    let r1 = <$g1 as AffineRepr>::ScalarField::rand(&mut rng);
                    let r2 = <$g2 as AffineRepr>::ScalarField::rand(&mut rng);

                    let comm_g1 = comm_key1.commit(&x1, &r1);
                    let comm_g2 = comm_key2.commit(&x2, &r2);

                    let nonce = b"123";

                    let mut prover_transcript = new_merlin_transcript(b"test");
                    prover_transcript.append_message_without_static_label(b"nonce", nonce);
                    prover_transcript.append(b"comm_key1", &comm_key1);
                    prover_transcript.append(b"comm_key2", &comm_key2);
                    prover_transcript.append(b"comm_g1", &comm_g1);
                    prover_transcript.append(b"comm_g2", &comm_g2);
                    let proof = Proof::<
                        $g1,
                        $g2,
                        WITNESS_BIT_SIZE,
                        CHALLENGE_BIT_SIZE,
                        ABORT_PARAM,
                        RESPONSE_BYTE_SIZE,
                        NUM_REPS,
                    >::new(
                        &mut rng,
                        &x1,
                        r1,
                        r2,
                        &comm_key1,
                        &comm_key2,
                        &mut prover_transcript,
                    )
                    .unwrap();

                    let mut verifier_transcript = new_merlin_transcript(b"test");
                    verifier_transcript.append_message_without_static_label(b"nonce", nonce);
                    verifier_transcript.append(b"comm_key1", &comm_key1);
                    verifier_transcript.append(b"comm_key2", &comm_key2);
                    verifier_transcript.append(b"comm_g1", &comm_g1);
                    verifier_transcript.append(b"comm_g2", &comm_g2);
                    proof
                        .verify(
                            &comm_g1,
                            &comm_g2,
                            &comm_key1,
                            &comm_key2,
                            &mut verifier_transcript,
                        )
                        .unwrap();
                }
                $fn_name();
            };
        }

        check!(check1, 32, 192, 8, 29, 1, PallasA, VestaA);
    }
}