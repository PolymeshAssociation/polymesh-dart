#[cfg(feature = "bounded")]
use bounded_collections::{BoundedVec, Get};
use codec::{
    Decode, DecodeWithMemTracking, Encode, EncodeAsRef, EncodeLike, Error as CodecError, Input,
    MaxEncodedLen, Output,
};
use scale_info::{Path, Type, TypeInfo, build::Fields};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use super::error::Error;
#[cfg(feature = "serde")]
use super::human_hex;

use ark_ec::AffineRepr;
use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{format, string::String, vec::Vec};

pub const ARK_EC_BASE_FIELD_SIZE: usize = 32;

pub type BaseField = [u8; ARK_EC_BASE_FIELD_SIZE];

#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
    DecodeWithMemTracking,
    Default,
    TypeInfo,
    PartialEq,
    Eq,
    Hash,
    PartialOrd,
    Ord,
)]
pub struct CompressedBaseField(BaseField);

impl core::fmt::Debug for CompressedBaseField {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", hex::encode(&self.0[..]))
    }
}

impl CompressedBaseField {
    /// Creates a `CompressedBaseField` from a hex string.
    pub fn from_str(s: &str) -> Result<Self, Error> {
        let offset = if s.starts_with("0x") { 2 } else { 0 };
        let mut field = [0u8; ARK_EC_BASE_FIELD_SIZE];
        hex::decode_to_slice(&s[offset..], &mut field[..]).map_err(|_| Error::HexDecodeError)?;
        Ok(Self(field))
    }

    /// Returns the underlying byte array.
    pub fn as_bytes(&self) -> &[u8; ARK_EC_BASE_FIELD_SIZE] {
        &self.0
    }

    /// Returns the size of the compressed base field.
    pub fn size_hint() -> usize {
        ARK_EC_BASE_FIELD_SIZE
    }

    pub fn from_base_field<F: CanonicalSerialize>(field: &F) -> Result<Self, Error> {
        let mut buf = [0u8; ARK_EC_BASE_FIELD_SIZE];
        field.serialize_compressed(&mut buf[..])?;
        Ok(Self(buf))
    }

    pub fn to_base_field<F: CanonicalDeserialize>(&self) -> Result<F, Error> {
        Ok(F::deserialize_compressed(&self.0[..])?)
    }
}

pub const ARK_EC_POINT_SIZE: usize = 32;

pub type CompressedPoint = [u8; ARK_EC_POINT_SIZE];

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
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary, examples("0xceae8587b3e968b9669df8eb715f73bcf3f7a9cd3c61c515a4d80f2ca59c8114")))]
pub struct CompressedAffine(
    #[cfg_attr(feature = "serde", serde(with = "human_hex"))] CompressedPoint,
);

impl Default for CompressedAffine {
    fn default() -> Self {
        Self([0u8; ARK_EC_POINT_SIZE])
    }
}

impl core::fmt::Debug for CompressedAffine {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", hex::encode(&self.0[..]))
    }
}

/// FromStr for CompressedAffine
impl core::str::FromStr for CompressedAffine {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_str(s)
    }
}

impl CompressedAffine {
    pub fn zero<P0: SWCurveConfig>() -> Self {
        let affine = Affine::<P0>::zero();
        Self::try_from(affine).expect("Failed to convert zero Affine to CompressedAffine")
    }

    /// Creates a `CompressedAffine` from a hex string.
    pub fn from_str(s: &str) -> Result<Self, Error> {
        let offset = if s.starts_with("0x") { 2 } else { 0 };
        let mut point = [0u8; ARK_EC_POINT_SIZE];
        hex::decode_to_slice(&s[offset..], &mut point[..]).map_err(|_| Error::HexDecodeError)?;
        Ok(Self(point))
    }

    /// Converts the compressed point to a hex string.
    pub fn to_string(&self) -> String {
        format!("{}", hex::encode(&self.0[..]))
    }

    /// Returns the underlying byte array.
    pub fn as_bytes(&self) -> &[u8; ARK_EC_POINT_SIZE] {
        &self.0
    }

    /// Returns the size of the compressed point.
    pub fn size_hint() -> usize {
        ARK_EC_POINT_SIZE
    }
}

impl<P: SWCurveConfig> TryFrom<Affine<P>> for CompressedAffine {
    type Error = Error;

    /// Converts an `Affine<P>` to a `CompressedAffine<P>`.
    fn try_from(affine: Affine<P>) -> Result<Self, Self::Error> {
        let mut buf = [0u8; ARK_EC_POINT_SIZE];
        affine.serialize_compressed(&mut buf[..])?;
        Ok(Self(buf))
    }
}

/// Convert from `Affine<P>` to `CompressedAffine`.
impl<P: SWCurveConfig> From<&Affine<P>> for CompressedAffine {
    fn from(affine: &Affine<P>) -> Self {
        Self::try_from(*affine).expect("Failed to convert Affine to CompressedAffine")
    }
}

impl<P: SWCurveConfig> TryFrom<&CompressedAffine> for Affine<P> {
    type Error = Error;

    /// Converts an `Affine<P>` to a `CompressedAffine<P>`.
    fn try_from(affine: &CompressedAffine) -> Result<Self, Self::Error> {
        Ok(Self::deserialize_compressed(&affine.0[..])?)
    }
}

impl<P: SWCurveConfig> From<CompressedAffine> for Affine<P> {
    fn from(compressed: CompressedAffine) -> Self {
        Self::try_from(&compressed).expect("Failed to convert CompressedAffine to Affine")
    }
}

impl<'a, P: SWCurveConfig> EncodeAsRef<'a, Affine<P>> for CompressedAffine {
    type RefType = CompressedAffine;
}

/// A wrapper type for `CanonicalSerialize` and `CanonicalDeserialize` types.
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(bound = ""))]
pub struct WrappedCanonical<T> {
    #[cfg_attr(feature = "serde", serde(with = "human_hex"))]
    #[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary))]
    wrapped: Vec<u8>,
    #[cfg_attr(feature = "serde", serde(skip))]
    _marker: core::marker::PhantomData<T>,
}

impl<T> PartialEq for WrappedCanonical<T> {
    fn eq(&self, other: &Self) -> bool {
        self.wrapped == other.wrapped
    }
}

impl<T> Eq for WrappedCanonical<T> {}

impl<T> core::fmt::Debug for WrappedCanonical<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let len = self.wrapped.len().min(32);
        write!(
            f,
            "WrappedCanonical<{}>({})",
            core::any::type_name::<T>(),
            hex::encode(&self.wrapped[..len])
        )
    }
}

impl<T: Clone + CanonicalSerialize + CanonicalDeserialize> WrappedCanonical<T> {
    /// Wraps a `T` value into a `WrappedCanonical` by serializing it into a compressed byte vector.
    pub fn wrap(value: &T) -> Result<Self, Error> {
        let mut buf = Vec::with_capacity(value.compressed_size());
        value.serialize_compressed(&mut buf)?;
        Ok(Self {
            wrapped: buf,
            _marker: core::marker::PhantomData,
        })
    }

    /// Decodes the wrapped value back into its original type `T`.
    pub fn decode(&self) -> Result<T, Error> {
        Ok(T::deserialize_compressed(&*self.wrapped)?)
    }
}

impl<T: 'static> TypeInfo for WrappedCanonical<T> {
    type Identity = Self;

    fn type_info() -> Type {
        use core::any::type_name;

        let mut ty_name = type_name::<T>();
        // Strip any generic parameters if they exist.
        if let Some(pos) = ty_name.find('<') {
            ty_name = &ty_name[..pos];
        }
        // Strip the module path if it exists.
        let (module_path, ident) = if let Some(pos) = ty_name.rfind("::") {
            let module_path = &ty_name[..pos];
            let ident = &ty_name[pos + 2..];
            (module_path, ident)
        } else {
            ("", ty_name)
        };

        Type::builder()
            .path(Path::new(ident, module_path))
            .composite(Fields::unnamed().field(|f| f.ty::<Vec<u8>>()))
    }
}

impl<T: CanonicalSerialize> EncodeLike for WrappedCanonical<T> {}

impl<T: CanonicalSerialize> Encode for WrappedCanonical<T> {
    #[inline]
    fn size_hint(&self) -> usize {
        self.wrapped.size_hint()
    }

    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        self.wrapped.encode_to(dest);
    }
}

impl<T: CanonicalDeserialize> codec::DecodeWithMemTracking for WrappedCanonical<T> {}

impl<T: CanonicalDeserialize> Decode for WrappedCanonical<T> {
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        Ok(Self {
            wrapped: <Vec<u8>>::decode(input)?,
            _marker: core::marker::PhantomData,
        })
    }
}

/// A bounded wrapper type for `CanonicalSerialize` and `CanonicalDeserialize` types.
#[cfg(feature = "bounded")]
#[derive(Clone)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(bound = ""))]
pub struct BoundedCanonical<T, S: Get<u32>> {
    #[cfg_attr(feature = "serde", serde(with = "human_hex"))]
    #[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary))]
    wrapped: BoundedVec<u8, S>,
    #[cfg_attr(feature = "serde", serde(skip))]
    _marker: core::marker::PhantomData<T>,
}

#[cfg(feature = "bounded")]
impl<T, S: Get<u32>> PartialEq for BoundedCanonical<T, S> {
    fn eq(&self, other: &Self) -> bool {
        self.wrapped.as_slice() == other.wrapped.as_slice()
    }
}

#[cfg(feature = "bounded")]
impl<T, S: Get<u32>> Eq for BoundedCanonical<T, S> {}

#[cfg(feature = "bounded")]
impl<T, S: Get<u32>> core::fmt::Debug for BoundedCanonical<T, S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let len = self.wrapped.len().min(32);
        write!(
            f,
            "BoundedCanonical<{}>({})",
            core::any::type_name::<T>(),
            hex::encode(&self.wrapped[..len])
        )
    }
}

#[cfg(feature = "bounded")]
impl<T: Clone + CanonicalSerialize + CanonicalDeserialize, S: Get<u32>> BoundedCanonical<T, S> {
    /// Wraps a `T` value into a `BoundedCanonical` by serializing it into a compressed byte vector.
    pub fn wrap(value: &T) -> Result<Self, Error> {
        let mut buf = Vec::with_capacity(value.compressed_size());
        value.serialize_compressed(&mut buf)?;
        Ok(Self {
            wrapped: buf.try_into().map_err(|_| Error::ValueExceedsBound)?,
            _marker: core::marker::PhantomData,
        })
    }

    /// Decodes the wrapped value back into its original type `T`.
    pub fn decode(&self) -> Result<T, Error> {
        Ok(T::deserialize_compressed(self.wrapped.as_slice())?)
    }
}

#[cfg(feature = "bounded")]
impl<T: 'static, S: Get<u32> + 'static> TypeInfo for BoundedCanonical<T, S> {
    type Identity = Self;

    fn type_info() -> Type {
        use core::any::type_name;

        let mut ty_name = type_name::<T>();
        // Strip any generic parameters if they exist.
        if let Some(pos) = ty_name.find('<') {
            ty_name = &ty_name[..pos];
        }
        // Strip the module path if it exists.
        let (module_path, ident) = if let Some(pos) = ty_name.rfind("::") {
            let module_path = &ty_name[..pos];
            let ident = &ty_name[pos + 2..];
            (module_path, ident)
        } else {
            ("", ty_name)
        };

        Type::builder()
            .path(Path::new(ident, module_path))
            .composite(Fields::unnamed().field(|f| f.ty::<BoundedVec<u8, S>>()))
    }
}

#[cfg(feature = "bounded")]
impl<T: CanonicalSerialize, S: Get<u32>> EncodeLike for BoundedCanonical<T, S> {}

#[cfg(feature = "bounded")]
impl<T: CanonicalSerialize, S: Get<u32>> Encode for BoundedCanonical<T, S> {
    #[inline]
    fn size_hint(&self) -> usize {
        self.wrapped.size_hint()
    }

    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        self.wrapped.encode_to(dest);
    }
}

#[cfg(feature = "bounded")]
impl<T: CanonicalDeserialize, S: Get<u32>> codec::DecodeWithMemTracking for BoundedCanonical<T, S> {}

#[cfg(feature = "bounded")]
impl<T: CanonicalDeserialize, S: Get<u32>> Decode for BoundedCanonical<T, S> {
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        Ok(Self {
            wrapped: BoundedVec::<u8, S>::decode(input)?,
            _marker: core::marker::PhantomData,
        })
    }
}
