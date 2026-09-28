//! Hash to `G1`.
//!
//! Each pairing has one standard hash-to-curve, so the map is fixed by the curve. BLS12-381 gets
//! the [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380.html) WB construction over SWU. BN254 gets
//! the RFC 9380 Shallue-van de Woestijne map, which applies where SWU does not because it has
//! `a.b = 0` and BN254's `G1` is `y^2 = x^3 + 3`.

#[cfg(feature = "bn254")]
use ark_ec::hashing::curve_maps::svdw::{SVDWConfig, SVDWMap};
#[cfg(feature = "bls12-381")]
use ark_ec::hashing::curve_maps::wb::{WBConfig, WBMap};
use ark_ec::pairing::Pairing;
#[cfg(any(feature = "bls12-381", feature = "bn254"))]
use {
    ark_ec::{
        hashing::{HashToCurve, map_to_curve_hasher::MapToCurveBasedHasher},
        short_weierstrass::{Affine, Projective},
    },
    ark_ff::field_hashers::DefaultFieldHasher,
    sha2::Sha256,
};

/// Tags follow RFC 9380 section 3.1, application tag then suite ID. RFC 9380 has no BN254 suite,
/// so its ID is the one gnark-crypto uses.
#[cfg(feature = "bls12-381")]
const BLS12_381_DST: &[u8] = b"POLYMESH-BAT-V01-CS01-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
#[cfg(feature = "bn254")]
const BN254_DST: &[u8] = b"POLYMESH-BAT-V01-CS01-with-BN254G1_XMD:SHA-256_SVDW_RO_";

/// A pairing whose `G1` has a standard hash-to-curve.
pub trait HashToG1: Pairing {
    const DST: &'static [u8];

    fn hash_to_g1(msg: &[u8]) -> Self::G1Affine;
}

/// RFC 9380 hash-to-curve over the WB isogeny. Available only for curves carrying a `WBConfig`.
#[cfg(feature = "bls12-381")]
fn wb<P: WBConfig>(dst: &[u8], msg: &[u8]) -> Affine<P> {
    MapToCurveBasedHasher::<Projective<P>, DefaultFieldHasher<Sha256, 128>, WBMap<P>>::new(dst)
        .expect("valid WB parameters")
        .hash(msg)
        .expect("hash to curve")
}

/// RFC 9380 hash-to-curve over the Shallue-van de Woestijne map.
#[cfg(feature = "bn254")]
fn svdw<P: SVDWConfig>(dst: &[u8], msg: &[u8]) -> Affine<P> {
    MapToCurveBasedHasher::<Projective<P>, DefaultFieldHasher<Sha256, 128>, SVDWMap<P>>::new(dst)
        .expect("valid SVDW parameters")
        .hash(msg)
        .expect("hash to curve")
}

#[cfg(feature = "bls12-381")]
impl HashToG1 for ark_bls12_381::Bls12_381 {
    const DST: &'static [u8] = BLS12_381_DST;

    fn hash_to_g1(msg: &[u8]) -> ark_bls12_381::G1Affine {
        wb::<ark_bls12_381::g1::Config>(BLS12_381_DST, msg)
    }
}

#[cfg(feature = "bn254")]
impl HashToG1 for ark_bn254::Bn254 {
    const DST: &'static [u8] = BN254_DST;

    fn hash_to_g1(msg: &[u8]) -> ark_bn254::G1Affine {
        svdw::<ark_bn254::g1::Config>(BN254_DST, msg)
    }
}
