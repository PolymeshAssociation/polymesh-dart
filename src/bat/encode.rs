use codec::{Decode, DecodeWithMemTracking, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use ark_ec::{
    AffineRepr,
    short_weierstrass::{Affine, SWCurveConfig},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use polymesh_bat::signature::BatchSig;

use super::*;

pub type CompressedG2Point = [u8; BAT_G2_SIZE];

#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct CompressedG2Affine(
    #[cfg_attr(feature = "serde", serde(with = "human_hex"))] CompressedG2Point,
);

impl core::fmt::Debug for CompressedG2Affine {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", hex::encode(&self.0[..]))
    }
}

impl CompressedG2Affine {
    /// Returns the underlying byte array.
    pub fn as_bytes(&self) -> &CompressedG2Point {
        &self.0
    }
}

impl<P: SWCurveConfig> TryFrom<Affine<P>> for CompressedG2Affine {
    type Error = Error;

    fn try_from(affine: Affine<P>) -> Result<Self, Self::Error> {
        let mut buf = [0u8; BAT_G2_SIZE];
        affine.serialize_compressed(&mut buf[..])?;
        Ok(Self(buf))
    }
}

impl<P: SWCurveConfig> TryFrom<&CompressedG2Affine> for Affine<P> {
    type Error = Error;

    fn try_from(affine: &CompressedG2Affine) -> Result<Self, Self::Error> {
        Ok(Self::deserialize_compressed(&affine.0[..])?)
    }
}

/// `pk_iss`.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatIssuerPublicKey(CompressedG2Affine);

impl BatIssuerPublicKey {
    pub fn from_affine(affine: BatG2) -> Result<Self, Error> {
        Ok(Self(CompressedG2Affine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<BatG2, Error> {
        BatG2::try_from(&self.0)
    }

    /// The check to run before registering a key.
    pub fn validate(&self) -> Result<(), Error> {
        if self.get_affine()?.is_zero() {
            return Err(polymesh_bat::Error::IdentityPoint.into());
        }
        Ok(())
    }
}

/// `com_k`, the issuer's commitment to the session's signature mask.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatCommitmentToSigMask(CompressedG2Affine);

impl BatCommitmentToSigMask {
    pub fn from_affine(affine: BatG2) -> Result<Self, Error> {
        Ok(Self(CompressedG2Affine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<BatG2, Error> {
        BatG2::try_from(&self.0)
    }
}

/// `alpha`, the unblinded issuer signature on a token.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatTokenSignature(CompressedAffine);

impl BatTokenSignature {
    pub fn from_affine(affine: BatG1) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<BatG1, Error> {
        BatG1::try_from(&self.0)
    }
}

/// `pk_e`. A token's one-time key is its nullifier.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatNullifier(CompressedAffine);

impl BatNullifier {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        PallasA::try_from(&self.0)
    }
}

/// `pk_ref`, the key a session's refund is signed with.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatRefundPublicKey(CompressedAffine);

impl BatRefundPublicKey {
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    pub fn get_affine(&self) -> Result<PallasA, Error> {
        PallasA::try_from(&self.0)
    }
}

/// `k`, the session's signature mask.
pub type BatSignatureMask = WrappedCanonical<BatScalar>;

/// Client signature over a set of keys.
pub type BatSignature = WrappedCanonical<BatchSig<PallasA>>;
