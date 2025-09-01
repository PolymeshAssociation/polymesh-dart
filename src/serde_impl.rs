pub mod human_hex {
    use serde::{de, ser};
    use std::fmt;

    pub trait SerializeHex {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: ser::Serializer;
    }

    pub fn serialize<T, S>(bytes: &T, serializer: S) -> Result<S::Ok, S::Error>
    where
        T: ?Sized + SerializeHex,
        S: ser::Serializer,
    {
        SerializeHex::serialize(bytes, serializer)
    }

    impl<const N: usize> SerializeHex for [u8; N] {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: ser::Serializer,
        {
            if serializer.is_human_readable() {
                let h = format!("0x{}", hex::encode(self));
                serializer.serialize_str(&h)
            } else {
                serde_arrays::serialize(self, serializer)
            }
        }
    }

    impl SerializeHex for Vec<u8> {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: ser::Serializer,
        {
            if serializer.is_human_readable() {
                let h = format!("0x{}", hex::encode(self));
                serializer.serialize_str(&h)
            } else {
                ser::Serialize::serialize(self, serializer)
            }
        }
    }

    pub trait DeserializeHex<'de>: Sized {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: de::Deserializer<'de>;
    }

    impl<'de, const N: usize> DeserializeHex<'de> for [u8; N] {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            if deserializer.is_human_readable() {
                struct StringVisitor<const N: usize>;

                impl<'de, const N: usize> de::Visitor<'de> for StringVisitor<N> {
                    type Value = [u8; N];

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("a hex string")
                    }

                    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
                    where
                        E: de::Error,
                    {
                        let mut bytes = [0u8; N];
                        let off = if s.starts_with("0x") { 2 } else { 0 };
                        hex::decode_to_slice(&s[off..], &mut bytes)
                            .map_err(|e| de::Error::custom(e))?;
                        Ok(bytes)
                    }
                }

                deserializer.deserialize_str(StringVisitor)
            } else {
                serde_arrays::deserialize(deserializer)
            }
        }
    }

    impl<'de> DeserializeHex<'de> for Vec<u8> {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            if deserializer.is_human_readable() {
                struct StringVisitor;

                impl<'de> de::Visitor<'de> for StringVisitor {
                    type Value = Vec<u8>;

                    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        formatter.write_str("a hex string")
                    }

                    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
                    where
                        E: de::Error,
                    {
                        let off = if s.starts_with("0x") { 2 } else { 0 };
                        hex::decode(&s[off..]).map_err(|e| de::Error::custom(e))
                    }
                }

                deserializer.deserialize_str(StringVisitor)
            } else {
                de::Deserialize::deserialize(deserializer)
            }
        }
    }

    pub fn deserialize<'de, T, D>(deserializer: D) -> Result<T, D::Error>
    where
        T: DeserializeHex<'de>,
        D: de::Deserializer<'de>,
    {
        DeserializeHex::deserialize(deserializer)
    }
}
