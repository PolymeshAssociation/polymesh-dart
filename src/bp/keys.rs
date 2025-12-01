#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{string::String, vec::Vec};

use blake2::Blake2s256;
use dock_crypto_utils::hashing_utils::hash_to_field;

use bounded_collections::BoundedVec;
use digest::Digest;
use rand_core::{CryptoRng, RngCore, SeedableRng as _};
use zeroize::{Zeroize, ZeroizeOnDrop};

use polymesh_dart_bp::{account_registration::MasterSeed as BPMasterSeed, keys as bp_keys};
use polymesh_dart_common::NullifierSkGenCounter;

use super::encode::*;
use super::*;
use crate::*;

pub const DERIVE_SEPARATOR: &[u8; 2] = b"//";

/// The encryption public key, which can be shared freely.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
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
    pub fn from_bp_key(pk: bp_keys::EncKey<PallasA>) -> Result<Self, Error> {
        Self::from_affine(pk.0)
    }

    /// Gets the BP encryption key corresponding to the `EncryptionPublicKey`.
    pub fn get_bp_key(&self) -> Result<bp_keys::EncKey<PallasA>, Error> {
        Ok(bp_keys::EncKey(self.get_affine()?))
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
pub struct EncryptionSecretKey(pub(crate) bp_keys::DecKey<PallasA>);

impl EncryptionSecretKey {
    /// Gets the inner decryption key.
    pub fn inner(&self) -> &bp_keys::DecKey<PallasA> {
        &self.0
    }
}

/// The encryption key pair, consisting of the public and secret keys.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct EncryptionKeyPair {
    #[zeroize(skip)]
    pub public: EncryptionPublicKey,
    pub secret: EncryptionSecretKey,
}

impl EncryptionKeyPair {
    /// Generates a new set of encryption keys using the provided RNG.
    pub fn rand<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, Error> {
        let (enc, enc_pk) = bp_keys::keygen_enc(rng, dart_gens().enc_key_gen());
        Ok(Self {
            public: EncryptionPublicKey::from_bp_key(enc_pk)?,
            secret: EncryptionSecretKey(enc),
        })
    }
}

/// The account public key, which can be shared freely.
#[derive(
    Copy,
    Clone,
    MaxEncodedLen,
    Encode,
    Decode,
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
pub struct AccountPublicKey(CompressedAffine);

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
    pub fn from_bp_key(pk: bp_keys::VerKey<PallasA>) -> Result<Self, Error> {
        Self::from_affine(pk.0)
    }

    /// Gets the BP verification key corresponding to the `AccountPublicKey`.
    pub fn get_bp_key(&self) -> Result<bp_keys::VerKey<PallasA>, Error> {
        Ok(bp_keys::VerKey(self.get_affine()?))
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
pub struct AccountSecretKey(pub(crate) bp_keys::SigKey<PallasA>);

/// The account key pair, consisting of the public and secret keys.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct AccountKeyPair {
    #[zeroize(skip)]
    pub public: AccountPublicKey,
    pub secret: AccountSecretKey,
}

impl AccountKeyPair {
    /// Generates a new set of account keys using the provided RNG.
    pub fn rand<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, Error> {
        let (account, account_pk) = bp_keys::keygen_sig(rng, dart_gens().sig_key_gen());
        Ok(Self {
            public: AccountPublicKey::from_bp_key(account_pk)?,
            secret: AccountSecretKey(account),
        })
    }

    /// Derives commitment randomness from the account secret key, identity, asset ID, and counter.
    pub fn derive_account_randomness(
        &self,
        identity: &[u8],
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> PallasScalar {
        // For creating randomness, use `secret_key//identity//asset_id//counter_n`
        let mut extended_seed = self.secret.encode();
        extended_seed.extend(DERIVE_SEPARATOR);
        extended_seed.extend(identity);
        extended_seed.extend(DERIVE_SEPARATOR);
        extended_seed.extend(asset_id.to_le_bytes().as_slice());
        extended_seed.extend(DERIVE_SEPARATOR);
        extended_seed.extend(counter.to_le_bytes());
        let randomness = hash_to_field::<_, Blake2b512>(b"Commitment randomness", &extended_seed);
        extended_seed.zeroize();
        randomness
    }

    /// Initializes a new asset state for the account.
    pub fn init_asset_state(
        &self,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<AccountAssetState, Error> {
        AccountAssetState::new(&self, asset_id, counter, identity)
    }

    pub fn account_state(
        &self,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<AccountState, Error> {
        let params = poseidon_params();
        let randomness = self.derive_account_randomness(identity, asset_id, counter);
        let id = hash_identity::<PallasScalar>(identity);
        let state = BPAccountState::new_given_randomness(
            id,
            self.secret.0.0,
            asset_id,
            counter,
            randomness,
            params.params.clone(),
        )?;
        Ok(state.try_into()?)
    }
}

/// The pair of public keys for an account: the encryption public key and the account public key.
#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AccountPublicKeys {
    pub enc: EncryptionPublicKey,
    pub acct: AccountPublicKey,
}

/// MasterSeed for generating account keys
#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct MasterSeed(BPMasterSeed);

impl MasterSeed {
    /// From seed (mnemonic phrase or hex string)
    pub fn from_seed(seed: &str) -> Self {
        // If the seed is a hex string, use it directly; otherwise, treat it as a mnemonic phrase.
        let seed_bytes = if seed.starts_with("0x") {
            hex::decode(&seed[2..]).unwrap_or_else(|_| seed.as_bytes().to_vec())
        } else {
            seed.as_bytes().to_vec()
        };
        Self(BPMasterSeed::new(seed_bytes))
    }

    /// Derives account keys from the master seed, path and index.
    pub fn derive_account_keys(&self, path: &str) -> Result<AccountKeys, Error> {
        let enc_key_gen = dart_gens().enc_key_gen();
        let sig_key_gen = dart_gens().sig_key_gen();
        let ((acct_sk, acct_pk), (enc_sk, enc_pk)) =
            self.0
                .derive_keys::<_, Blake2b512>(path.as_bytes(), 0, enc_key_gen, sig_key_gen);
        Ok(AccountKeys {
            enc: EncryptionKeyPair {
                public: EncryptionPublicKey::from_affine(enc_pk.0)?,
                secret: EncryptionSecretKey(enc_sk),
            },
            acct: AccountKeyPair {
                public: AccountPublicKey::from_affine(acct_pk.0)?,
                secret: AccountSecretKey(acct_sk),
            },
        })
    }
}

/// The pair of key pairs for an account: the encryption key pair and the account key pair.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, Zeroize, ZeroizeOnDrop)]
pub struct AccountKeys {
    pub enc: EncryptionKeyPair,
    pub acct: AccountKeyPair,
}

impl AccountKeys {
    /// Generates a new set of account keys using the provided RNG.
    pub fn rand<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, Error> {
        let enc = EncryptionKeyPair::rand(rng)?;
        let acct = AccountKeyPair::rand(rng)?;
        Ok(Self { enc, acct })
    }

    /// Genreates a new set of account keys using the provided string as a seed.
    pub fn from_seed(seed: &str) -> Result<Self, Error> {
        let mut rng =
            rand_chacha::ChaCha20Rng::from_seed(Blake2s256::digest(seed.as_bytes()).into());
        Self::rand(&mut rng)
    }

    /// Initializes a new asset state for the account.
    pub fn init_asset_state(
        &self,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        identity: &[u8],
    ) -> Result<AccountAssetState, Error> {
        self.acct.init_asset_state(asset_id, counter, identity)
    }

    /// Returns the public keys for the account.
    pub fn public_keys(&self) -> AccountPublicKeys {
        AccountPublicKeys {
            enc: self.enc.public,
            acct: self.acct.public,
        }
    }
}

/// DART account registration proof.
///
/// This is used to prove knowledge of the secret keys (account and encryption keys) for 1 or more DART accounts.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct AccountRegistrationProof<T: DartLimits = ()> {
    pub accounts: BoundedVec<AccountPublicKeys, T::MaxKeysPerRegProof>,

    inner: WrappedCanonical<bp_keys::InvestorKeyRegProof<PallasA>>,
}

impl<T: DartLimits> AccountRegistrationProof<T> {
    /// Generate a new account registration proof for the given accounts.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        accounts: &[AccountKeys],
        identity: &[u8],
    ) -> Result<Self, Error> {
        let mut bounded_accounts = BoundedVec::with_bounded_capacity(accounts.len());
        let mut keys = Vec::with_capacity(accounts.len());

        for account in accounts {
            bounded_accounts
                .try_push(account.public_keys())
                .map_err(|_| Error::TooManyKeysInRegProof)?;

            let acc_pub = account.acct.public.get_affine()?;
            let acc_sec = account.acct.secret.0.0;
            let enc_pub = account.enc.public.get_affine()?;
            let enc_sec = account.enc.secret.0.0;
            keys.push(((acc_pub, acc_sec), (enc_pub, enc_sec)));
        }

        let proof = bp_keys::InvestorKeyRegProof::new(
            rng,
            keys,
            identity,
            dart_gens().sig_key_gen(),
            dart_gens().enc_key_gen(),
        )?;

        Ok(Self {
            accounts: bounded_accounts,
            inner: WrappedCanonical::wrap(&proof)?,
        })
    }

    /// Verify the account registration proof.
    pub fn verify(&self, identity: &[u8]) -> Result<(), Error> {
        let proof = self.inner.decode()?;
        let pk_refs: Vec<_> = self
            .accounts
            .iter()
            .map(|keys| -> Result<_, Error> {
                Ok((keys.acct.get_affine()?, keys.enc.get_affine()?))
            })
            .collect::<Result<_, _>>()?;
        proof.verify(
            pk_refs,
            identity,
            dart_gens().sig_key_gen(),
            dart_gens().enc_key_gen(),
        )?;
        Ok(())
    }

    /// Get the number of accounts in the proof.
    pub fn len(&self) -> usize {
        self.accounts.len()
    }
}

/// Encryption key registration proof for auditors and mediators.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct EncryptionKeyRegistrationProof<T: DartLimits = ()> {
    pub keys: BoundedVec<EncryptionPublicKey, T::MaxKeysPerRegProof>,

    inner: WrappedCanonical<bp_keys::AudMedRegProof<PallasA>>,
}

impl<T: DartLimits> EncryptionKeyRegistrationProof<T> {
    /// Generate a new encryption key registration proof for the given keys.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        keys: &[EncryptionKeyPair],
        identity: &[u8],
    ) -> Result<Self, Error> {
        let mut bounded_keys = BoundedVec::with_bounded_capacity(keys.len());
        let mut key_pairs = Vec::with_capacity(keys.len());

        for key in keys {
            bounded_keys
                .try_push(key.public)
                .map_err(|_| Error::TooManyKeysInRegProof)?;
            let pub_key = key.public.get_affine()?;
            let sec_key = key.secret.0.0;
            key_pairs.push((pub_key, sec_key));
        }

        let proof =
            bp_keys::AudMedRegProof::new(rng, key_pairs, identity, dart_gens().enc_key_gen())?;

        Ok(Self {
            keys: bounded_keys,
            inner: WrappedCanonical::wrap(&proof)?,
        })
    }

    /// Verify the encryption key registration proof.
    pub fn verify(&self, identity: &[u8]) -> Result<(), Error> {
        let proof = self.inner.decode()?;
        let pk_refs: Vec<_> = self
            .keys
            .iter()
            .map(|key| -> Result<_, Error> { Ok(key.get_affine()?) })
            .collect::<Result<_, _>>()?;
        proof.verify(pk_refs, identity, dart_gens().enc_key_gen())?;
        Ok(())
    }

    /// Get the number of keys in the proof.
    pub fn len(&self) -> usize {
        self.keys.len()
    }
}
