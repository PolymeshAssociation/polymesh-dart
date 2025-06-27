use std::mem;

use codec::{Decode, Encode, EncodeAsRef, Error as CodecError, Input, Output};
#[cfg(feature = "std")]
use scale_info::{Path, Type, TypeInfo, build::Fields};

use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use crate::{
    curve_tree::{CurveTreeRoot, Inner, LeafValue},
    *,
};

pub const ARK_EC_POINT_SIZE: usize = 33;

pub type CompressedPoint = [u8; ARK_EC_POINT_SIZE];

#[derive(Copy, Clone, Debug, Encode, Decode)]
#[cfg_attr(feature = "std", derive(TypeInfo))]
pub struct CompressedAffine(CompressedPoint);

impl<P: SWCurveConfig> TryFrom<Affine<P>> for CompressedAffine {
    type Error = ();

    /// Converts an `Affine<P>` to a `CompressedAffine<P>`.
    fn try_from(affine: Affine<P>) -> Result<Self, Self::Error> {
        let mut buf = [0u8; ARK_EC_POINT_SIZE];
        affine.serialize_compressed(&mut buf[..]).map_err(|err| {
            log::error!("Failed to serialize CompressedAffine: {:?}", err);
            ()
        })?;
        Ok(Self(buf))
    }
}

/// Convert from `Affine<P>` to `CompressedAffine`.
impl<P: SWCurveConfig> From<&Affine<P>> for CompressedAffine {
    fn from(affine: &Affine<P>) -> Self {
        CompressedAffine::try_from(affine).expect("Failed to convert Affine to CompressedAffine")
    }
}

impl<P: SWCurveConfig> From<CompressedAffine> for Affine<P> {
    fn from(compressed: CompressedAffine) -> Self {
        compressed
            .try_into()
            .expect("Failed to convert CompressedAffine to Affine")
    }
}

impl<'a, P: SWCurveConfig> EncodeAsRef<'a, Affine<P>> for CompressedAffine {
    type RefType = CompressedAffine;
}

#[cfg(feature = "std")]
impl TypeInfo for DartBPGenerators {
    type Identity = Self;

    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("DartBPGenerators", module_path!()))
            .composite(
                Fields::named()
                    .field(|f| f.name("sig_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("enc_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("account_comm_key").ty::<AccountCommitmentKey>())
                    .field(|f| f.name("asset_comm_key").ty::<AssetCommitmentKey>())
                    .field(|f| f.name("enc_sig_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("leg_asset_value_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("ped_comm_key_g").ty::<CompressedAffine>())
                    .field(|f| f.name("ped_comm_key_h").ty::<CompressedAffine>()),
            )
    }
}

#[cfg(feature = "std")]
impl TypeInfo for AccountCommitmentKey {
    type Identity = Self;

    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("AccountCommitmentKey", module_path!()))
            .composite(
                Fields::named()
                    .field(|f| f.name("sk_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("balance_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("counter_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("asset_id_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("rho_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("randomness_gen").ty::<CompressedAffine>()),
            )
    }
}

#[cfg(feature = "std")]
impl TypeInfo for AssetCommitmentKey {
    type Identity = Self;

    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("AssetCommitmentKey", module_path!()))
            .composite(
                Fields::named()
                    .field(|f| f.name("is_mediator_gen").ty::<CompressedAffine>())
                    .field(|f| f.name("asset_id_gen").ty::<CompressedAffine>()),
            )
    }
}

/// TypeInfo, SCALE encoding and decoding for `EncryptionPublicKey`.

#[cfg(feature = "std")]
impl TypeInfo for EncryptionPublicKey {
    type Identity = Self;
    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("EncryptionPublicKey", module_path!()))
            .composite(Fields::unnamed().field(|f| {
                f.ty::<CompressedPoint>()
                    .type_name("EncodedEncryptionPublicKey")
            }))
    }
}

impl Encode for EncryptionPublicKey {
    #[inline]
    fn size_hint(&self) -> usize {
        self.compressed_size()
    }

    /// Encodes as a `Vec<u8>`.
    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        let mut buf = Vec::new();
        self.serialize_compressed(&mut buf)
            .expect("Failed to serialize EncryptionPublicKey");
        dest.write(&*buf);
    }
}

impl Decode for EncryptionPublicKey {
    /// Decode a `EncryptionPublicKey` .
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        let buf = <CompressedPoint>::decode(input)?;
        Ok(Self::deserialize_compressed(&buf[..])
            .map_err(|_| CodecError::from("Failed to deserialize EncryptionPublicKey"))?)
    }
}

/// TypeInfo, SCALE encoding and decoding for `AccountPublicKey`.

#[cfg(feature = "std")]
impl TypeInfo for AccountPublicKey {
    type Identity = Self;
    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("AccountPublicKey", module_path!()))
            .composite(Fields::unnamed().field(|f| {
                f.ty::<CompressedPoint>()
                    .type_name("EncodedAccountPublicKey")
            }))
    }
}

impl Encode for AccountPublicKey {
    #[inline]
    fn size_hint(&self) -> usize {
        self.compressed_size()
    }

    /// Encodes as a `Vec<u8>`.
    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        let mut buf = Vec::new();
        self.serialize_compressed(&mut buf)
            .expect("Failed to serialize AccountPublicKey");
        dest.write(&*buf);
    }
}

impl Decode for AccountPublicKey {
    /// Decode a `AccountPublicKey` .
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        let buf = <CompressedPoint>::decode(input)?;
        Ok(Self::deserialize_compressed(&buf[..])
            .map_err(|_| CodecError::from("Failed to deserialize AccountPublicKey"))?)
    }
}

/// TypeInfo, SCALE encoding and decoding for `LegEncrypted`.

#[cfg(feature = "std")]
impl TypeInfo for LegEncrypted {
    type Identity = Self;
    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("LegEncrypted", module_path!()))
            .composite(
                Fields::unnamed().field(|f| f.ty::<Vec<u8>>().type_name("EncodedLegEncrypted")),
            )
    }
}

impl Encode for LegEncrypted {
    #[inline]
    fn size_hint(&self) -> usize {
        self.compressed_size()
    }

    /// Encodes as a `Vec<u8>`.
    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        let mut buf = Vec::new();
        self.serialize_compressed(&mut buf)
            .expect("Failed to serialize LegEncrypted");
        buf.encode_to(dest);
    }
}

impl Decode for LegEncrypted {
    /// Decode a `LegEncrypted` .
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        let buf = <Vec<u8>>::decode(input)?;
        Ok(Self::deserialize_compressed(&*buf)
            .map_err(|_| CodecError::from("Failed to deserialize LegEncrypted"))?)
    }
}

/// TypeInfo, SCALE encoding and decoding for `AccountStateCommitment`.

#[cfg(feature = "std")]
impl TypeInfo for AccountStateCommitment {
    type Identity = Self;
    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("AccountStateCommitment", module_path!()))
            .composite(Fields::unnamed().field(|f| {
                f.ty::<CompressedPoint>()
                    .type_name("EncodedAccountStateCommitment")
            }))
    }
}

impl Encode for AccountStateCommitment {
    #[inline]
    fn size_hint(&self) -> usize {
        self.compressed_size()
    }

    /// Encodes as a `Vec<u8>`.
    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        let mut buf = Vec::new();
        self.serialize_compressed(&mut buf)
            .expect("Failed to serialize AccountStateCommitment");
        dest.write(&*buf);
    }
}

impl Decode for AccountStateCommitment {
    /// Decode a `AccountStateCommitment` .
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        let buf = <CompressedPoint>::decode(input)?;
        Ok(Self::deserialize_compressed(&buf[..])
            .map_err(|_| CodecError::from("Failed to deserialize AccountStateCommitment"))?)
    }
}

/// TypeInfo for `AssetStateCommitment`.
#[cfg(feature = "std")]
impl TypeInfo for AssetStateCommitment {
    type Identity = Self;
    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("AssetStateCommitment", module_path!()))
            .composite(Fields::unnamed().field(|f| {
                f.ty::<CompressedPoint>()
                    .type_name("EncodedAssetStateCommitment")
            }))
    }
}

/// TypeInfo, SCALE encoding and decoding for `CurveTreeRoot<L>`.

#[cfg(feature = "std")]
impl<const L: usize> TypeInfo for CurveTreeRoot<L> {
    type Identity = Self;
    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("CurveTreeRoot", module_path!()))
            .composite(
                Fields::unnamed().field(|f| f.ty::<Vec<u8>>().type_name("EncodedCurveTreeRoot")),
            )
    }
}

impl<const L: usize> Encode for CurveTreeRoot<L> {
    #[inline]
    fn size_hint(&self) -> usize {
        mem::size_of::<u32>() + self.compressed_size()
    }

    /// Encodes as a `Vec<u8>`.
    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        let mut buf = Vec::new();
        self.serialize_compressed(&mut buf)
            .expect("Failed to serialize CurveTreeRoot");
        buf.encode_to(dest);
    }
}

impl<const L: usize> Decode for CurveTreeRoot<L> {
    /// Decode a `CurveTreeRoot<L>` .
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        let buf = <Vec<u8>>::decode(input)?;
        Ok(Self::deserialize_compressed(&*buf)
            .map_err(|_| CodecError::from("Failed to deserialize CurveTreeRoot"))?)
    }
}

/// TypeInfo, SCALE encoding and decoding for `Inner<M, P0, P1>`.

#[cfg(feature = "std")]
impl<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> TypeInfo for Inner<M, P0, P1> {
    type Identity = Self;
    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("Inner", module_path!()))
            .composite(Fields::unnamed().field(|f| f.ty::<Vec<u8>>().type_name("EncodedInner")))
    }
}

impl<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> Encode for Inner<M, P0, P1> {
    #[inline]
    fn size_hint(&self) -> usize {
        mem::size_of::<u32>() + self.compressed_size()
    }

    /// Encodes as a `Vec<u8>`.
    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        let mut buf = Vec::new();
        self.serialize_compressed(&mut buf)
            .expect("Failed to serialize Inner");
        buf.encode_to(dest);
    }
}

impl<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig> Decode for Inner<M, P0, P1> {
    /// Decode a `Inner<M, P0, P1>` .
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        let buf = <Vec<u8>>::decode(input)?;
        Ok(Self::deserialize_compressed(&*buf)
            .map_err(|_| CodecError::from("Failed to deserialize Inner"))?)
    }
}

/// TypeInfo, SCALE encoding and decoding for `LeafValue<P0>`.

#[cfg(feature = "std")]
impl<P0: SWCurveConfig> TypeInfo for LeafValue<P0> {
    type Identity = Self;
    fn type_info() -> Type {
        Type::builder()
            .path(Path::new("LeafValue", module_path!()))
            .composite(
                Fields::unnamed()
                    .field(|f| f.ty::<CompressedPoint>().type_name("EncodedLeafValue")),
            )
    }
}

impl<P0: SWCurveConfig> Encode for LeafValue<P0> {
    #[inline]
    fn size_hint(&self) -> usize {
        self.compressed_size()
    }

    /// Encodes as a `Vec<u8>`.
    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        let mut buf = Vec::new();
        self.serialize_compressed(&mut buf)
            .expect("Failed to serialize LeafValue");
        dest.write(&*buf);
    }
}

impl<P0: SWCurveConfig> Decode for LeafValue<P0> {
    /// Decode a `LeafValue<P0>` .
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        let buf = <CompressedPoint>::decode(input)?;
        Ok(Self::deserialize_compressed(&buf[..])
            .map_err(|_| CodecError::from("Failed to deserialize LeafValue"))?)
    }
}

/// A wrapper type for `CanonicalSerialize` and `CanonicalDeserialize` types.
#[derive(Clone)]
pub struct WrappedCanonical<T>(pub T);

impl<T> core::ops::Deref for WrappedCanonical<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> From<T> for WrappedCanonical<T> {
    #[inline]
    fn from(value: T) -> Self {
        Self(value)
    }
}

#[cfg(feature = "std")]
impl<T: 'static> TypeInfo for WrappedCanonical<T> {
    type Identity = Self;

    fn type_info() -> Type {
        use std::any::type_name;

        Type::builder()
            .path(Path::new(type_name::<T>(), module_path!()))
            .composite(
                Fields::unnamed().field(|f| f.ty::<Vec<u8>>().type_name("EncodedLegEncrypted")),
            )
    }
}

impl<T: CanonicalSerialize> Encode for WrappedCanonical<T> {
    #[inline]
    fn size_hint(&self) -> usize {
        mem::size_of::<u32>() + self.0.compressed_size()
    }

    /// Encodes as a `Vec<u8>`.
    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        let mut buf = Vec::new();
        self.0
            .serialize_compressed(&mut buf)
            .expect("Failed to serialize LegEncrypted");
        buf.encode_to(dest);
    }
}

impl<T: CanonicalDeserialize> Decode for WrappedCanonical<T> {
    /// Decode a `LegEncrypted` .
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        let buf = <Vec<u8>>::decode(input)?;
        Ok(Self(T::deserialize_compressed(&*buf).map_err(|_| {
            CodecError::from("Failed to deserialize LegEncrypted")
        })?))
    }
}
