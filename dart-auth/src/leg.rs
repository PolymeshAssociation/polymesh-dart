use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use polymesh_dart_common::AssetId;

/// Asset-id can be encrypted or revealed by the leg creator
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum AssetIdEncryption<G: AffineRepr> {
    /// asset-id as encrypted
    Ciphertext(G),
    /// asset-id as revealed
    Revealed(AssetId),
}

impl<G: AffineRepr> AssetIdEncryption<G> {
    pub fn is_revealed(&self) -> bool {
        matches!(self, Self::Revealed(_))
    }

    /// `None` when asset-id is encrypted (not revealed to the verifier).
    pub fn asset_id(&self) -> Option<AssetId> {
        match self {
            AssetIdEncryption::Ciphertext(_) => None,
            AssetIdEncryption::Revealed(id) => Some(*id),
        }
    }

    /// `None` when asset-id is encrypted (not revealed to the verifier).
    pub fn asset_id_ciphertext(&self) -> Option<G> {
        match self {
            AssetIdEncryption::Ciphertext(ct) => Some(*ct),
            AssetIdEncryption::Revealed(_) => None,
        }
    }
}

/// Sender's ephemeral public keys. Index 1 is None when the sender cannot decrypt the receiver's pk.
/// Index 3 is None when asset-id is revealed (not encrypted).
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct SenderEphemeralPublicKey<G: AffineRepr> {
    pub r1: G,
    pub r2: Option<G>,
    pub r3: G,
    pub r4: Option<G>,
}

/// Receiver's ephemeral public keys. Index 0 is None when the receiver cannot decrypt the sender's pk.
/// Index 3 is None when asset-id is revealed (not encrypted).
#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ReceiverEphemeralPublicKey<G: AffineRepr> {
    pub r1: Option<G>,
    pub r2: G,
    pub r3: G,
    pub r4: Option<G>,
}

/// The party's ephemeral public key — either sender or receiver.
/// Used in affirmation proofs where the same code handles both roles.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PartyEphemeralPublicKey<G: AffineRepr> {
    Sender(SenderEphemeralPublicKey<G>),
    Receiver(ReceiverEphemeralPublicKey<G>),
}

impl<G: AffineRepr> PartyEphemeralPublicKey<G> {
    pub fn is_sender(&self) -> bool {
        matches!(self, Self::Sender(_))
    }

    /// Ephemeral key for amount encryption (index 2) — always present for both parties
    pub fn eph_pk_amount(&self) -> G {
        match self {
            Self::Sender(s) => s.r3,
            Self::Receiver(r) => r.r3,
        }
    }

    /// Ephemeral key for asset_id encryption (index 3) — `None` when asset ID is revealed
    pub fn eph_pk_asset_id(&self) -> Option<G> {
        match self {
            Self::Sender(s) => s.r4,
            Self::Receiver(r) => r.r4,
        }
    }

    /// Ephemeral key identifying the party (index 0 for sender, index 1 for receiver)
    pub fn eph_pk_participant(&self) -> G {
        match self {
            Self::Sender(s) => s.r1,
            Self::Receiver(r) => r.r2,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LegEncryptionCore<G: AffineRepr> {
    pub ct_s: G,
    pub ct_r: G,
    pub ct_amount: G,
    pub ct_asset_id: AssetIdEncryption<G>,
}

impl<G: AffineRepr> LegEncryptionCore<G> {
    /// Returns the ciphertext for the participant, `ct_s` for sender, `ct_r` for receiver
    pub fn ct_participant(&self, is_sender: bool) -> G {
        if is_sender { self.ct_s } else { self.ct_r }
    }

    pub fn is_asset_id_revealed(&self) -> bool {
        matches!(self.ct_asset_id, AssetIdEncryption::Revealed(_))
    }

    /// `None` when asset-id is encrypted (not revealed to the verifier).
    pub fn asset_id(&self) -> Option<AssetId> {
        self.ct_asset_id.asset_id()
    }

    /// `None` when asset-id is revealed (hidden from the verifier).
    pub fn asset_id_ciphertext(&self) -> Option<G> {
        self.ct_asset_id.asset_id_ciphertext()
    }

    pub fn ct_s(&self) -> G {
        self.ct_s
    }

    pub fn ct_r(&self) -> G {
        self.ct_r
    }

    pub fn ct_amount(&self) -> G {
        self.ct_amount
    }
}

mod serialization {
    use super::*;
    use ark_serialize::{Compress, SerializationError, Valid, Validate};
    use ark_std::io::{Read, Write};

    impl<G: AffineRepr> CanonicalSerialize for AssetIdEncryption<G> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                AssetIdEncryption::Ciphertext(ct) => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    ct.serialize_with_mode(&mut writer, compress)
                }
                AssetIdEncryption::Revealed(id) => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    id.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                AssetIdEncryption::Ciphertext(ct) => ct.serialized_size(compress),
                AssetIdEncryption::Revealed(id) => id.serialized_size(compress),
            }
        }
    }

    impl<G: AffineRepr> CanonicalDeserialize for AssetIdEncryption<G> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            let discriminant = u8::deserialize_with_mode(&mut reader, compress, validate)?;
            match discriminant {
                0 => Ok(AssetIdEncryption::Ciphertext(G::deserialize_with_mode(
                    &mut reader,
                    compress,
                    validate,
                )?)),
                1 => Ok(AssetIdEncryption::Revealed(AssetId::deserialize_with_mode(
                    &mut reader,
                    compress,
                    validate,
                )?)),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G: AffineRepr> Valid for AssetIdEncryption<G> {
        fn check(&self) -> Result<(), SerializationError> {
            match self {
                AssetIdEncryption::Ciphertext(ct) => ct.check(),
                AssetIdEncryption::Revealed(id) => id.check(),
            }
        }
    }

    impl<G: AffineRepr> CanonicalSerialize for PartyEphemeralPublicKey<G> {
        fn serialize_with_mode<W: Write>(
            &self,
            mut writer: W,
            compress: Compress,
        ) -> Result<(), SerializationError> {
            match self {
                PartyEphemeralPublicKey::Sender(eph_pk) => {
                    0u8.serialize_with_mode(&mut writer, compress)?;
                    eph_pk.serialize_with_mode(&mut writer, compress)
                }
                PartyEphemeralPublicKey::Receiver(eph_pk) => {
                    1u8.serialize_with_mode(&mut writer, compress)?;
                    eph_pk.serialize_with_mode(&mut writer, compress)
                }
            }
        }

        fn serialized_size(&self, compress: Compress) -> usize {
            1 + match self {
                PartyEphemeralPublicKey::Sender(eph_pk) => eph_pk.serialized_size(compress),
                PartyEphemeralPublicKey::Receiver(eph_pk) => eph_pk.serialized_size(compress),
            }
        }
    }

    impl<G: AffineRepr> CanonicalDeserialize for PartyEphemeralPublicKey<G> {
        fn deserialize_with_mode<R: Read>(
            mut reader: R,
            compress: Compress,
            validate: Validate,
        ) -> Result<Self, SerializationError> {
            let discriminant = u8::deserialize_with_mode(&mut reader, compress, validate)?;
            match discriminant {
                0 => Ok(PartyEphemeralPublicKey::Sender(
                    SenderEphemeralPublicKey::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                1 => Ok(PartyEphemeralPublicKey::Receiver(
                    ReceiverEphemeralPublicKey::deserialize_with_mode(
                        &mut reader,
                        compress,
                        validate,
                    )?,
                )),
                _ => Err(SerializationError::InvalidData),
            }
        }
    }

    impl<G: AffineRepr> Valid for PartyEphemeralPublicKey<G> {
        fn check(&self) -> Result<(), SerializationError> {
            match self {
                PartyEphemeralPublicKey::Sender(eph_pk) => eph_pk.check(),
                PartyEphemeralPublicKey::Receiver(eph_pk) => eph_pk.check(),
            }
        }
    }
}
