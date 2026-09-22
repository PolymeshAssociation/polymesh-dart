//! Hash to `G1`.
//!
//! One strategy, `Standard`. It resolves per curve to whatever standard hash-to-curve arkworks
//! provides, and falls back to hash-to-field plus try-and-increment on `x` only where arkworks
//! provides nothing. Callers never pick.
//!
//! BLS12-381 gets the RFC 9380 WB construction. BN254 gets the fallback, and not by preference:
//! its `G1` is `y^2 = x^3 + 3` with `COEFF_A = 0`, arkworks' `SWUConfig::map_to_curve` requires
//! `COEFF_A != 0`, no WB isogeny is shipped for it, and arkworks 0.5 has no SVDW at all. The
//! fallback is variable time in the number of increments, so a BN254 deployment needs a
//! constant-time map written before it ships. Adding one means a new impl here and nothing else.

use ark_ec::{
    AffineRepr, CurveGroup,
    hashing::{
        HashToCurve,
        curve_maps::wb::{WBConfig, WBMap},
        map_to_curve_hasher::MapToCurveBasedHasher,
    },
    pairing::Pairing,
    short_weierstrass::{Affine, Projective, SWCurveConfig},
};
use ark_ff::{
    One,
    field_hashers::{DefaultFieldHasher, HashToField},
};
use sha2::Sha256;

pub const DST: &[u8] = b"POLYMESH-DART-BAT-POC-H2C-V1";

/// Maps the token message to `G1`. `NAME` says which construction the curve resolved to, so a
/// results table reports it rather than leaving the reader to assume.
pub trait HashToG1<E: Pairing> {
    const NAME: &'static str;

    fn hash(msg: &[u8]) -> E::G1Affine;
}

/// RFC 9380 hash-to-curve. Available only for curves carrying a `WBConfig`.
fn wb<P: WBConfig>(msg: &[u8]) -> Affine<P> {
    MapToCurveBasedHasher::<Projective<P>, DefaultFieldHasher<Sha256, 128>, WBMap<P>>::new(DST)
        .expect("valid WB parameters")
        .hash(msg)
        .expect("hash to curve")
}

/// Fallback for curves with no standard map. Hashes to one base field element, increments `x` until
/// it lands on the curve, then clears the cofactor. Variable time in the number of increments.
fn try_and_incr<P: SWCurveConfig>(msg: &[u8]) -> Affine<P> {
    let hasher = <DefaultFieldHasher<Sha256, 128> as HashToField<P::BaseField>>::new(DST);
    let [mut x] = hasher.hash_to_field::<1>(msg);
    loop {
        if let Some(p) = Affine::<P>::get_point_from_x_unchecked(x, true) {
            return p.mul_by_cofactor_to_group().into_affine();
        }
        x += P::BaseField::one();
    }
}

pub struct Standard;

impl HashToG1<ark_bls12_381::Bls12_381> for Standard {
    const NAME: &'static str = "WB/SWU, RFC 9380";

    fn hash(msg: &[u8]) -> ark_bls12_381::G1Affine {
        wb::<ark_bls12_381::g1::Config>(msg)
    }
}

impl HashToG1<ark_bn254::Bn254> for Standard {
    const NAME: &'static str = "try-and-increment, no standard map in arkworks";

    fn hash(msg: &[u8]) -> ark_bn254::G1Affine {
        try_and_incr::<ark_bn254::g1::Config>(msg)
    }
}
