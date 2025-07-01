use std::mem;

use codec::{Decode, Encode, EncodeAsRef, Error as CodecError, Input, Output};
#[cfg(feature = "std")]
use scale_info::{Path, Type, TypeInfo, build::Fields};

use ark_ec::{models::short_weierstrass::SWCurveConfig, short_weierstrass::Affine};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};

use crate::{
    curve_tree::{CurveTreeRoot, Inner, LeafValue},
    *,
};

macro_rules! impl_scale_and_type_info {
     ( $type:ident as $as_type:ident $( < $($trailing:tt)* )? ) => {
        impl_scale_and_type_info!(@impl_ {
            $type as $as_type;
            $(
                impl_generics { }
                generics { }
                trailing { $( $trailing )* }
            )?
        });
    };
    // Parse const generics.
    (@impl_ {
        $type:ident as $as_type:ident;
        impl_generics { $( $impl_generics:tt )* }
        generics { $( $generics:tt )* }
        trailing { $(,)? const $lt:ident : $clt:ident $($trailing:tt)* }
    }) => {
        impl_scale_and_type_info!(@impl_ {
            $type as $as_type;
            impl_generics { $( $impl_generics )* const $lt : $clt, }
            generics { $( $generics )* $lt, }
            trailing { $( $trailing )* }
        });
    };
    // Parse non-const generics.
    (@impl_ {
        $type:ident as $as_type:ident;
        impl_generics { $( $impl_generics:tt )* }
        generics { $( $generics:tt )* }
        trailing { $(,)? $lt:ident : $clt:ident $($trailing:tt)* }
    }) => {
        impl_scale_and_type_info!(@impl_ {
            $type as $as_type;
            impl_generics { $( $impl_generics )* $lt : $clt, }
            generics { $( $generics )* $lt, }
            trailing { $( $trailing )* }
        });
    };
    (@impl_ {
        $type:ident as Vec;
        $(
            impl_generics { $( $impl_generics:tt )* }
            generics { $( $generics:tt )* }
            trailing { > }
        )?
    }) => {
        #[cfg(feature = "std")]
        impl $(< $( $impl_generics )* >)? TypeInfo for $type $(< $( $generics )* >)? {
            type Identity = Self;
            fn type_info() -> Type {
                Type::builder()
                    .path(Path::new(stringify!($type), module_path!()))
                    .composite(Fields::unnamed().field(|f| f.ty::<Vec<u8>>().type_name(concat!("Encoded", stringify!($type)))))
            }
        }

        impl $(< $( $impl_generics )* >)? Encode for $type $(< $( $generics )* >)? {
            #[inline]
            fn size_hint(&self) -> usize {
                mem::size_of::<u32>() + self.compressed_size()
            }

            fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
                let mut buf = Vec::with_capacity(self.size_hint());
                self.serialize_compressed(&mut buf)
                    .expect("Failed to serialize");
                buf.encode_to(dest);
            }
        }

        impl $(< $( $impl_generics )* >)? Decode for $type $(< $( $generics )* >)? {
            fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
                let buf = <Vec<u8>>::decode(input)?;
                Ok(Self::deserialize_compressed(&*buf)
                    .map_err(|_| CodecError::from("Failed to deserialize"))?)
            }
        }
    };
    (@impl_ {
        $type:ident as CompressedPoint;
        $(
            impl_generics { $( $impl_generics:tt )* }
            generics { $( $generics:tt )* }
            trailing { > }
        )?
    }) => {
        #[cfg(feature = "std")]
        impl $(< $( $impl_generics )* >)? TypeInfo for $type $(< $( $generics )* >)? {
            type Identity = Self;
            fn type_info() -> Type {
                Type::builder()
                    .path(Path::new(stringify!($type), module_path!()))
                    .composite(Fields::unnamed().field(|f| f.ty::<CompressedPoint>().type_name(concat!("Encoded", stringify!($type)))))
            }
        }

        impl $(< $( $impl_generics )* >)? Encode for $type $(< $( $generics )* >)? {
            #[inline]
            fn size_hint(&self) -> usize {
                self.compressed_size()
            }

            fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
                let mut buf = Vec::with_capacity(self.size_hint());
                self.serialize_compressed(&mut buf)
                    .expect("Failed to serialize");
                dest.write(&*buf);
            }
        }

        impl $(< $( $impl_generics )* >)? Decode for $type $(< $( $generics )* >)? {
            fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
                let buf = <CompressedPoint>::decode(input)?;
                Ok(Self::deserialize_compressed(&buf[..])
                    .map_err(|_| CodecError::from("Failed to deserialize"))?)
            }
        }
    };
}

pub const ARK_EC_POINT_SIZE: usize = 33;

pub type CompressedPoint = [u8; ARK_EC_POINT_SIZE];

#[derive(Copy, Clone, Debug, Encode, Decode)]
#[cfg_attr(feature = "std", derive(TypeInfo))]
pub struct CompressedAffine(CompressedPoint);

impl<P: SWCurveConfig> TryFrom<Affine<P>> for CompressedAffine {
    type Error = SerializationError;

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
    type Error = SerializationError;

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

// TypeInfo, SCALE encoding and decoding for `EncryptionPublicKey`.
impl_scale_and_type_info!(EncryptionPublicKey as CompressedPoint);

// TypeInfo, SCALE encoding and decoding for `AccountPublicKey`.
impl_scale_and_type_info!(AccountPublicKey as CompressedPoint);

// TypeInfo, SCALE encoding and decoding for `LegEncrypted`.
impl_scale_and_type_info!(LegEncrypted as Vec);

// TypeInfo, SCALE encoding and decoding for `AccountStateCommitment`.
impl_scale_and_type_info!(AccountStateCommitment as CompressedPoint);

// TypeInfo, SCALE encoding and decoding for `AccountStateNullifier`.
impl_scale_and_type_info!(AccountStateNullifier as CompressedPoint);

// TypeInfo, SCALE encoding and decoding for `AssetStateCommitment`.
impl_scale_and_type_info!(AssetStateCommitment as CompressedPoint);

// TypeInfo, SCALE encoding and decoding for `CurveTreeRoot<L>`.
impl_scale_and_type_info!(CurveTreeRoot as Vec<const L: usize>);

// TypeInfo, SCALE encoding and decoding for `Inner<M, P0, P1>`.
impl_scale_and_type_info!(Inner as Vec<const M: usize, P0: SWCurveConfig, P1: SWCurveConfig>);

// TypeInfo, SCALE encoding and decoding for `LeafValue<P0>`.
impl_scale_and_type_info!(LeafValue as CompressedPoint<P0: SWCurveConfig>);

/// A wrapper type for `CanonicalSerialize` and `CanonicalDeserialize` types.
#[derive(Clone)]
pub struct WrappedCanonical<T> {
    wrapped: Vec<u8>,
    _marker: core::marker::PhantomData<T>,
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

#[cfg(feature = "std")]
impl<T: 'static> TypeInfo for WrappedCanonical<T> {
    type Identity = Self;

    fn type_info() -> Type {
        use std::any::type_name;

        Type::builder()
            .path(Path::new(type_name::<T>(), module_path!()))
            .composite(
                Fields::unnamed()
                    .field(|f| f.ty::<Vec<u8>>().type_name("EncodedWrappedCanonical<T>")),
            )
    }
}

impl<T: CanonicalSerialize> Encode for WrappedCanonical<T> {
    #[inline]
    fn size_hint(&self) -> usize {
        self.wrapped.size_hint()
    }

    fn encode_to<W: Output + ?Sized>(&self, dest: &mut W) {
        self.wrapped.encode_to(dest);
    }
}

impl<T: CanonicalDeserialize> Decode for WrappedCanonical<T> {
    fn decode<I: Input>(input: &mut I) -> Result<Self, CodecError> {
        Ok(Self {
            wrapped: <Vec<u8>>::decode(input)?,
            _marker: core::marker::PhantomData,
        })
    }
}
