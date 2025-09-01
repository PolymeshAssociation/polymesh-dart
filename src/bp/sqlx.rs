use sqlx::{Database, Decode, Encode, Type, encode::IsNull};

use super::{
    AccountPublicKey, AccountSecretKey, EncryptionPublicKey, EncryptionSecretKey, SettlementRef,
};

// SettlementRef is stored as a BLOB in the database

impl<DB: Database> Type<DB> for SettlementRef
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Type<DB>,
{
    fn type_info() -> DB::TypeInfo {
        <Vec<u8> as Type<DB>>::type_info()
    }
}

impl<'r, DB: Database> Decode<'r, DB> for SettlementRef
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Decode<'r, DB>,
{
    fn decode(
        value: DB::ValueRef<'r>,
    ) -> Result<SettlementRef, Box<dyn core::error::Error + 'static + Send + Sync>> {
        let value = <Vec<u8> as Decode<DB>>::decode(value)?;
        Ok(codec::Decode::decode(&mut &value[..])?)
    }
}

impl<'r, DB: Database> Encode<'r, DB> for SettlementRef
where
    // Make sure BLOBs are supported by the database
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

// AccountPublicKey is stored as a BLOB in the database

impl<DB: Database> Type<DB> for AccountPublicKey
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Type<DB>,
{
    fn type_info() -> DB::TypeInfo {
        <Vec<u8> as Type<DB>>::type_info()
    }
}

impl<'r, DB: Database> Decode<'r, DB> for AccountPublicKey
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Decode<'r, DB>,
{
    fn decode(
        value: DB::ValueRef<'r>,
    ) -> Result<AccountPublicKey, Box<dyn core::error::Error + 'static + Send + Sync>> {
        let value = <Vec<u8> as Decode<DB>>::decode(value)?;
        Ok(codec::Decode::decode(&mut &value[..])?)
    }
}

impl<'r, DB: Database> Encode<'r, DB> for AccountPublicKey
where
    // Make sure BLOBs are supported by the database
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

// AccountSecretKey is stored as a BLOB in the database

impl<DB: Database> Type<DB> for AccountSecretKey
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Type<DB>,
{
    fn type_info() -> DB::TypeInfo {
        <Vec<u8> as Type<DB>>::type_info()
    }
}

impl<'r, DB: Database> Decode<'r, DB> for AccountSecretKey
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Decode<'r, DB>,
{
    fn decode(
        value: DB::ValueRef<'r>,
    ) -> Result<AccountSecretKey, Box<dyn core::error::Error + 'static + Send + Sync>> {
        let value = <Vec<u8> as Decode<DB>>::decode(value)?;
        Ok(codec::Decode::decode(&mut &value[..])?)
    }
}

impl<'r, DB: Database> Encode<'r, DB> for AccountSecretKey
where
    // Make sure BLOBs are supported by the database
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

// EncryptionPublicKey is stored as a BLOB in the database

impl<DB: Database> Type<DB> for EncryptionPublicKey
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Type<DB>,
{
    fn type_info() -> DB::TypeInfo {
        <Vec<u8> as Type<DB>>::type_info()
    }
}

impl<'r, DB: Database> Decode<'r, DB> for EncryptionPublicKey
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Decode<'r, DB>,
{
    fn decode(
        value: DB::ValueRef<'r>,
    ) -> Result<EncryptionPublicKey, Box<dyn core::error::Error + 'static + Send + Sync>> {
        let value = <Vec<u8> as Decode<DB>>::decode(value)?;
        Ok(codec::Decode::decode(&mut &value[..])?)
    }
}

impl<'r, DB: Database> Encode<'r, DB> for EncryptionPublicKey
where
    // Make sure BLOBs are supported by the database
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

// EncryptionSecretKey is stored as a BLOB in the database

impl<DB: Database> Type<DB> for EncryptionSecretKey
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Type<DB>,
{
    fn type_info() -> DB::TypeInfo {
        <Vec<u8> as Type<DB>>::type_info()
    }
}

impl<'r, DB: Database> Decode<'r, DB> for EncryptionSecretKey
where
    // Make sure BLOBs are supported by the database
    Vec<u8>: Decode<'r, DB>,
{
    fn decode(
        value: DB::ValueRef<'r>,
    ) -> Result<EncryptionSecretKey, Box<dyn core::error::Error + 'static + Send + Sync>> {
        let value = <Vec<u8> as Decode<DB>>::decode(value)?;
        Ok(codec::Decode::decode(&mut &value[..])?)
    }
}

impl<'r, DB: Database> Encode<'r, DB> for EncryptionSecretKey
where
    // Make sure BLOBs are supported by the database
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
