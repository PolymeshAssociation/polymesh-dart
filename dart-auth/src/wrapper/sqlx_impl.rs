use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use sqlx::{Database, Decode, Encode, Type, encode::IsNull};

use super::encode::WrappedCanonical;
use super::keys::{
    AccountPublicKey, AccountPublicKeys, AccountSecretKey, EncryptionPublicKey, EncryptionSecretKey,
};

// The public/secret-key wire types are stored as BLOBs (SCALE-encoded).

macro_rules! impl_sqlx_blob {
    ($type:ident) => {
        impl<DB: Database> Type<DB> for $type
        where
            Vec<u8>: Type<DB>,
        {
            fn type_info() -> DB::TypeInfo {
                <Vec<u8> as Type<DB>>::type_info()
            }
        }

        impl<'r, DB: Database> Decode<'r, DB> for $type
        where
            Vec<u8>: Decode<'r, DB>,
        {
            fn decode(
                value: DB::ValueRef<'r>,
            ) -> Result<$type, Box<dyn core::error::Error + 'static + Send + Sync>> {
                let value = <Vec<u8> as Decode<DB>>::decode(value)?;
                Ok(codec::Decode::decode(&mut &value[..])?)
            }
        }

        impl<'r, DB: Database> Encode<'r, DB> for $type
        where
            Vec<u8>: Encode<'r, DB>,
        {
            fn encode_by_ref(
                &self,
                buf: &mut DB::ArgumentBuffer<'r>,
            ) -> Result<IsNull, Box<dyn core::error::Error + 'static + Send + Sync>> {
                let value = codec::Encode::encode(self);
                Encode::<'r, DB>::encode(value, buf)
            }
        }
    };
}

impl_sqlx_blob!(AccountPublicKey);
impl_sqlx_blob!(AccountPublicKeys);
impl_sqlx_blob!(AccountSecretKey);
impl_sqlx_blob!(EncryptionPublicKey);
impl_sqlx_blob!(EncryptionSecretKey);

// WrappedCanonical<T> is stored as a BLOB in the database

impl<T, DB> Type<DB> for WrappedCanonical<T>
where
    DB: Database,
    // Make sure BLOBs are supported by the database
    Vec<u8>: Type<DB>,
    T: CanonicalSerialize + CanonicalDeserialize,
{
    fn type_info() -> DB::TypeInfo {
        <Vec<u8> as Type<DB>>::type_info()
    }
}

impl<'r, T, DB> Decode<'r, DB> for WrappedCanonical<T>
where
    DB: Database,
    // Make sure BLOBs are supported by the database
    Vec<u8>: Decode<'r, DB>,
    T: CanonicalDeserialize,
{
    fn decode(
        value: DB::ValueRef<'r>,
    ) -> Result<WrappedCanonical<T>, Box<dyn core::error::Error + 'static + Send + Sync>> {
        let value = <Vec<u8> as Decode<DB>>::decode(value)?;
        Ok(codec::Decode::decode(&mut &value[..])?)
    }
}

impl<'r, T, DB> Encode<'r, DB> for WrappedCanonical<T>
where
    DB: Database,
    // Make sure BLOBs are supported by the database
    Vec<u8>: Encode<'r, DB>,
    T: CanonicalSerialize,
{
    fn encode_by_ref(
        &self,
        buf: &mut DB::ArgumentBuffer<'r>,
    ) -> Result<IsNull, Box<dyn core::error::Error + 'static + Send + Sync>> {
        let value = codec::Encode::encode(self);
        Encode::<'r, DB>::encode(value, buf)
    }
}
