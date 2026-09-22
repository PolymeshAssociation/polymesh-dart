//! Client signature scheme `DS`, generic over the group and independent of the pairing curve.
//!
//! A Schnorr proof of knowledge of the discrete log of `pk = base*sk`, Fiat-Shamir'd over the
//! message. Not RFC 8032: same group arithmetic, different challenge derivation, no clamping, no
//! cofactor handling. `schnorr_pok::discrete_log` is used rather than
//! `dock_crypto_utils::schnorr_signature` because only the former exposes the randomized
//! multiplication checker path, which is what makes batch verification one MSM.

use ark_ec::{AffineRepr, CurveGroup, scalar_mul::BatchMulPreprocessing};
use ark_ff::PrimeField;
use ark_std::{
    UniformRand,
    rand::{CryptoRng, RngCore},
    vec::Vec,
};
use dock_crypto_utils::{
    error::UtilsError,
    randomized_mult_checker::{RandomizedMultChecker, RandomizedMultCheckerGuard},
};
use schnorr_pok::{
    compute_random_oracle_challenge,
    discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol},
};
use sha2::Sha256;

pub type Sig<D> = PokDiscreteLog<D>;

#[derive(Clone, Debug)]
pub struct Keypair<D: AffineRepr> {
    pub sk: D::ScalarField,
    pub pk: D,
}

pub fn generator<D: AffineRepr>() -> D {
    D::generator()
}

pub fn keygen<D: AffineRepr, R: RngCore>(rng: &mut R, base: &D) -> Keypair<D> {
    let sk = D::ScalarField::rand(rng);
    let pk = base.mul_bigint(sk.into_bigint()).into_affine();
    Keypair { sk, pk }
}

/// One windowed table over the shared `base`, reused for all `num_keys` public keys. A client
/// generates one ephemeral key per token, so this is the issuance-side form.
pub fn keygen_batch<D: AffineRepr, R: RngCore>(
    rng: &mut R,
    base: &D,
    num_keys: usize,
) -> Vec<Keypair<D>> {
    let sk: Vec<D::ScalarField> = (0..num_keys).map(|_| D::ScalarField::rand(rng)).collect();
    let table = BatchMulPreprocessing::new(base.into_group(), num_keys.max(1));
    table
        .batch_mul(&sk)
        .into_iter()
        .zip(sk)
        .map(|(pk, sk)| Keypair { sk, pk })
        .collect()
}

fn challenge<D: AffineRepr>(t: &D, pk: &D, msg: &[u8]) -> D::ScalarField {
    let mut bytes = Vec::with_capacity(t.compressed_size() + pk.compressed_size() + msg.len());
    t.serialize_compressed(&mut bytes).unwrap();
    pk.serialize_compressed(&mut bytes).unwrap();
    bytes.extend_from_slice(msg);
    compute_random_oracle_challenge::<D::ScalarField, Sha256>(&bytes)
}

pub fn sign<D: AffineRepr, R: RngCore>(
    rng: &mut R,
    kp: &Keypair<D>,
    msg: &[u8],
    base: &D,
) -> Sig<D> {
    let protocol = PokDiscreteLogProtocol::init(kp.sk, D::ScalarField::rand(rng), base);
    let c = challenge(&protocol.t, &kp.pk, msg);
    protocol.gen_proof(&c)
}

pub fn verify<D: AffineRepr>(sig: &Sig<D>, pk: &D, msg: &[u8], base: &D) -> bool {
    let c = challenge(&sig.t, pk, msg);
    sig.verify(pk, base, &c).is_ok()
}

/// Folds one verification into the checker. `n` of these collapse to a single MSM over the distinct
/// points, so the shared `base` contributes one term for the whole batch rather than `n`.
pub fn add_to_checker<D: AffineRepr>(
    sig: &Sig<D>,
    pk: &D,
    msg: &[u8],
    base: &D,
    rmc: &mut RandomizedMultChecker<D>,
) {
    let c = challenge(&sig.t, pk, msg);
    sig.verify_using_randomized_mult_checker(*pk, *base, &c, rmc);
}

/// `deserialize_compressed` validates on-curve and subgroup membership. Identity is rejected here.
pub fn decode_pk<D: AffineRepr>(bytes: &[u8]) -> Option<D> {
    let pk = D::deserialize_compressed(bytes).ok()?;
    (!pk.is_zero()).then_some(pk)
}

/// Verifies `n` signatures over a shared message as one MSM.
pub fn batch_verify<D: AffineRepr, R: RngCore + CryptoRng>(
    rng: &mut R,
    sigs: &[Sig<D>],
    pks: &[D],
    msg: &[u8],
    base: &D,
) -> bool {
    RandomizedMultCheckerGuard::<D>::new_using_rng(rng)
        .with(|rmc| {
            for (sig, pk) in sigs.iter().zip(pks) {
                add_to_checker(sig, pk, msg, base, rmc);
            }
            Ok::<(), UtilsError>(())
        })
        .is_ok()
}
