#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::string::String;
use ark_std::vec::Vec;
use codec::{
    Decode, DecodeWithMemTracking, Encode, EncodeLike, Error as CodecError, Input, MaxEncodedLen,
    Output,
};
use scale_info::{Path, Type, TypeInfo, build::Fields};
use zeroize::{Zeroize, ZeroizeOnDrop};

use super::error::Error;
use super::{CompressedAffine, PallasA};
use crate::keys::{DecKey, EncKey, SigKey, VerKey};

/// The encryption public key, which can be shared freely.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    Default,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary, examples("0xceae8587b3e968b9669df8eb715f73bcf3f7a9cd3c61c515a4d80f2ca59c8114")))]
pub struct EncryptionPublicKey(CompressedAffine);

/// FromStr for EncryptionPublicKey
impl core::str::FromStr for EncryptionPublicKey {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(CompressedAffine::from_str(s)?))
    }
}

impl EncryptionPublicKey {
    /// Creates a `EncryptionPublicKey` from a hex string.
    pub fn from_str(s: &str) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::from_str(s)?))
    }

    /// Converts a `AccountPublicKey` to a hex string.
    pub fn to_string(&self) -> String {
        self.0.to_string()
    }

    /// Creates a `EncryptionPublicKey` from an affine point.
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    /// Gets the affine point corresponding to the `EncryptionPublicKey`.
    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    /// Creates an `EncryptionPublicKey` from a BP encryption key.
    pub fn from_bp_key(pk: EncKey<PallasA>) -> Result<Self, Error> {
        Self::from_affine(pk.0)
    }

    /// Gets the BP encryption key corresponding to the `EncryptionPublicKey`.
    pub fn get_bp_key(&self) -> Result<EncKey<PallasA>, Error> {
        Ok(EncKey(self.get_affine()?))
    }
}

/// The encryption secret key, which should be kept private.
#[derive(
    Clone,
    Debug,
    Default,
    CanonicalSerialize,
    CanonicalDeserialize,
    PartialEq,
    Eq,
    Zeroize,
    ZeroizeOnDrop,
)]
pub struct EncryptionSecretKey(pub DecKey<PallasA>);

impl EncryptionSecretKey {
    /// Gets the inner decryption key.
    pub fn inner(&self) -> &DecKey<PallasA> {
        &self.0
    }
}

/// The account public key, which can be shared freely.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    Default,
    TypeInfo,
    Debug,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary, examples("0xceae8587b3e968b9669df8eb715f73bcf3f7a9cd3c61c515a4d80f2ca59c8114")))]
pub struct AccountPublicKey(pub(crate) CompressedAffine);

/// FromStr for AccountPublicKey
impl core::str::FromStr for AccountPublicKey {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Self(CompressedAffine::from_str(s)?))
    }
}

impl AccountPublicKey {
    /// Creates a `AccountPublicKey` from a hex string.
    pub fn from_str(s: &str) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::from_str(s)?))
    }

    /// Converts a `AccountPublicKey` to a hex string.
    pub fn to_string(&self) -> String {
        self.0.to_string()
    }

    /// Creates a `AccountPublicKey` from an affine point.
    pub fn from_affine(affine: PallasA) -> Result<Self, Error> {
        Ok(Self(CompressedAffine::try_from(affine)?))
    }

    /// Gets the affine point corresponding to the `AccountPublicKey`.
    pub fn get_affine(&self) -> Result<PallasA, Error> {
        Ok(PallasA::try_from(&self.0)?)
    }

    /// Creates an `AccountPublicKey` from a BP verification key.
    pub fn from_bp_key(pk: VerKey<PallasA>) -> Result<Self, Error> {
        Self::from_affine(pk.0)
    }

    /// Gets the BP verification key corresponding to the `AccountPublicKey`.
    pub fn get_bp_key(&self) -> Result<VerKey<PallasA>, Error> {
        Ok(VerKey(self.get_affine()?))
    }
}

/// The account secret key, which should be kept private.
#[derive(
    Clone,
    Debug,
    Default,
    CanonicalSerialize,
    CanonicalDeserialize,
    PartialEq,
    Eq,
    Zeroize,
    ZeroizeOnDrop,
)]
pub struct AccountSecretKey(pub SigKey<PallasA>);

// SCALE encoding for the secret-key newtypes: the underlying scalar is `serialize_compressed`d to a
// fixed 32-byte array.
macro_rules! impl_scale_as_array32 {
    ($type:ident) => {
        impl TypeInfo for $type {
            type Identity = Self;
            fn type_info() -> Type {
                Type::builder()
                    .path(Path::new(stringify!($type), module_path!()))
                    .composite(Fields::unnamed().field(|f| f.ty::<[u8; 32]>()))
            }
        }

        impl EncodeLike for $type {}

        impl Encode for $type {
            #[inline]
            fn size_hint(&self) -> usize {
                self.compressed_size()
            }

            fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
                let mut buf = [0u8; 32];
                self.serialize_compressed(&mut buf[..])
                    .expect("Failed to serialize");
                dest.write(&buf[..]);
            }
        }

        impl DecodeWithMemTracking for $type {}

        impl Decode for $type {
            fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
                let buf: [u8; 32] = Decode::decode(input)?;
                Ok(Self::deserialize_compressed(&buf[..])
                    .map_err(|_| CodecError::from("Failed to deserialize"))?)
            }
        }
    };
}

impl_scale_as_array32!(AccountSecretKey);
impl_scale_as_array32!(EncryptionSecretKey);

/// The pair of public keys for an account: the encryption public key and the account public key.
#[derive(
    Copy,
    Clone,
    Debug,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    TypeInfo,
    PartialEq,
    Eq,
    Hash,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AccountPublicKeys {
    pub enc: EncryptionPublicKey,
    pub acct: AccountPublicKey,
}
