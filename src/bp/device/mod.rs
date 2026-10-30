use codec::{Decode, Encode};
use rand_core::CryptoRngCore;

use polymesh_dart_bp::auth_proofs::keys::{
    MasterSeed as BPMasterSeed, keygen_enc_given_sk, keygen_sig_given_sk,
};
use polymesh_dart_common::SkGenCounter;

use super::CompressedAffine;
use super::auth_proofs::{
    AuthSigningKey, AuthSigningKeys, create_affirmation_auth_proof, create_fee_account_auth_proof,
    create_fee_account_registration_auth_proof, create_fee_payment_auth_proof,
    create_key_registration_auth_proof, create_mint_auth_proof, create_registration_auth_proof,
    derive_account_randomness, derive_fee_account_randomness,
};
use super::key_reg_split::{KeyRegistrationDeviceRequest, KeyRegistrationDeviceResponse};
use super::split_types::{
    AccountRandomnessDeviceRequest, AccountRandomnessDeviceResponse,
    AccountRegistrationDeviceResponse, AffirmationDeviceRequest, AffirmationDeviceResponse,
    AssetMintingDeviceResponse, FeeAccountDeviceRequest, FeeAccountPaymentDeviceResponse,
    FeeAccountRandomnessDeviceResponse, FeeAccountRegistrationDeviceRequest,
    FeeAccountRegistrationDeviceResponse, FeeAccountTopupDeviceResponse, FeePaymentDeviceRequest,
    MintDeviceRequest, RegistrationDeviceRequest,
};
use crate::Error;
use ark_std::string::String;
use ark_std::{vec, vec::Vec};

#[cfg(feature = "host_proofs")]
use super::{
    AccountAssetState, AccountPublicKey, AccountState, FeeAccountAssetState, PallasA, PallasScalar,
    hash_identity, poseidon_params,
};
#[cfg(feature = "host_proofs")]
use polymesh_dart_bp::account::state::AccountState as BPAccountState;
#[cfg(feature = "host_proofs")]
use polymesh_dart_common::{AssetId, Balance, NullifierSkGenCounter};

mod generators;
#[cfg(all(test, feature = "std", feature = "host_proofs"))]
mod ledger_tests;
#[cfg(feature = "std")]
mod sealing;
#[cfg(all(test, feature = "std", feature = "host_proofs"))]
mod speculos_tests;
#[cfg(all(test, feature = "host_proofs", feature = "hardcoded-key"))]
mod tests;
#[cfg(feature = "std")]
mod transport;
#[cfg(all(feature = "std", feature = "host_proofs"))]
mod workflow;

pub use generators::DeviceGenerators;
#[cfg(all(feature = "std", feature = "hardcoded-key"))]
pub use sealing::HardcodedKeyProvider;
#[cfg(feature = "std")]
pub use sealing::{DataKey, DataKeyProvider};
#[cfg(feature = "std")]
pub use transport::{MAX_FRAME_LEN, StreamDevice, read_frame, serve, write_frame};
#[cfg(all(feature = "std", feature = "host_proofs"))]
pub use workflow::{run_fee_register_topup_pay, run_register_mint_affirm};

#[derive(Clone, Debug, Encode, Decode)]
pub struct PubKeys {
    pub pk_aff: CompressedAffine,
    pub pk_enc: CompressedAffine,
}

#[derive(Clone, Encode, Decode)]
pub enum DeviceRequest {
    GenerateKeys,
    LoadKeys(Vec<u8>),
    KeyRegistration(KeyRegistrationDeviceRequest),
    RegistrationProof(RegistrationDeviceRequest),
    MintProof(MintDeviceRequest),
    Affirm(AffirmationDeviceRequest),
    FeeRegistrationProof(FeeAccountRegistrationDeviceRequest),
    FeeTopupProof(FeeAccountDeviceRequest),
    FeePaymentProof(FeePaymentDeviceRequest),
    AccountRandomness(AccountRandomnessDeviceRequest),
    FeeAccountRandomness(AccountRandomnessDeviceRequest),
}

#[derive(Clone, Encode, Decode)]
pub enum DeviceResponse {
    Ok,
    /// sealed data are the encrypted master seed
    Keys {
        pubkeys: PubKeys,
        sealed: Vec<u8>,
    },
    KeyRegistration(KeyRegistrationDeviceResponse),
    Registration(AccountRegistrationDeviceResponse),
    Mint(AssetMintingDeviceResponse),
    Affirmation(AffirmationDeviceResponse),
    Err(String),
    FeeRegistration(FeeAccountRegistrationDeviceResponse),
    FeeTopup(FeeAccountTopupDeviceResponse),
    FeePayment(FeeAccountPaymentDeviceResponse),
    AccountRandomness(AccountRandomnessDeviceResponse),
    FeeAccountRandomness(FeeAccountRandomnessDeviceResponse),
}

/// Path and counter the device derives its keys and account randomness at.
const SEED_PATH: &[u8] = b"";
const SEED_COUNTER: SkGenCounter = 0;
const MASTER_SEED_LEN: usize = 32;

/// Holds the master seed and the secret keys derived from it. This is what runs inside the enclave.
pub struct Device {
    generators: Option<DeviceGenerators>,
    seed: Option<BPMasterSeed>,
    keys: Option<AuthSigningKeys>,
    #[cfg(feature = "std")]
    provider: Box<dyn DataKeyProvider>,
}

impl Device {
    /// Builds a device that seals its master seed via `provider`.
    #[cfg(feature = "std")]
    pub fn with_provider(provider: Box<dyn DataKeyProvider>) -> Self {
        Self {
            generators: None,
            seed: None,
            keys: None,
            provider,
        }
    }

    /// Builds a device that seals with the compiled-in `hardcoded-key`.
    #[cfg(all(feature = "std", feature = "hardcoded-key"))]
    pub fn new() -> Self {
        Self::with_provider(Box::new(HardcodedKeyProvider))
    }

    #[cfg(not(feature = "std"))]
    pub fn new() -> Self {
        Self {
            generators: None,
            seed: None,
            keys: None,
        }
    }

    /// Builds a device holding `keys`, loaded by the caller from the target's own key storage.
    /// Without a master seed it rejects account randomness requests.
    #[cfg(not(feature = "std"))]
    pub fn with_keys(keys: AuthSigningKeys) -> Self {
        Self {
            generators: None,
            seed: None,
            keys: Some(keys),
        }
    }

    /// Builds a device holding `seed`, loaded by the caller from the target's own key storage.
    #[cfg(not(feature = "std"))]
    pub fn with_master_seed(seed: BPMasterSeed) -> Result<Self, Error> {
        let mut device = Self::new();
        device.set_seed(seed)?;
        Ok(device)
    }

    pub fn handle<R: CryptoRngCore>(
        &mut self,
        request: DeviceRequest,
        rng: &mut R,
    ) -> Result<DeviceResponse, Error> {
        match request {
            DeviceRequest::GenerateKeys => {
                let g = self.gens()?;
                let mut seed_bytes = vec![0u8; MASTER_SEED_LEN];
                rng.fill_bytes(&mut seed_bytes);
                let seed = BPMasterSeed::new(seed_bytes);
                let sealed = self.seal_seed(&seed, rng)?;
                let keys = self.set_seed(seed)?;
                let (_, pk_aff) = keygen_sig_given_sk(keys.sk_aff, g.sig_key_gen());
                let (_, pk_enc) = keygen_enc_given_sk(keys.sk_enc, g.enc_key_gen());
                Ok(DeviceResponse::Keys {
                    pubkeys: PubKeys {
                        pk_aff: CompressedAffine::try_from(pk_aff.0)?,
                        pk_enc: CompressedAffine::try_from(pk_enc.0)?,
                    },
                    sealed,
                })
            }
            DeviceRequest::LoadKeys(blob) => {
                let seed = self.unseal_seed(&blob)?;
                self.set_seed(seed)?;
                Ok(DeviceResponse::Ok)
            }
            DeviceRequest::AccountRandomness(request) => {
                let response = derive_account_randomness(
                    self.master_seed()?,
                    SEED_PATH,
                    SEED_COUNTER,
                    &request,
                )?;
                Ok(DeviceResponse::AccountRandomness(response))
            }
            DeviceRequest::FeeAccountRandomness(request) => {
                let response = derive_fee_account_randomness(
                    self.master_seed()?,
                    SEED_PATH,
                    SEED_COUNTER,
                    &request,
                )?;
                Ok(DeviceResponse::FeeAccountRandomness(response))
            }
            DeviceRequest::KeyRegistration(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response =
                    create_key_registration_auth_proof(rng, keys, &request.identity, &g)?;
                Ok(DeviceResponse::KeyRegistration(response))
            }
            DeviceRequest::RegistrationProof(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response = create_registration_auth_proof(rng, keys, &request, &g)?;
                Ok(DeviceResponse::Registration(response))
            }
            DeviceRequest::MintProof(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response = create_mint_auth_proof(rng, keys, &request, &g)?;
                Ok(DeviceResponse::Mint(response))
            }
            DeviceRequest::Affirm(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response = create_affirmation_auth_proof(rng, keys, &request, &g)?;
                Ok(DeviceResponse::Affirmation(response))
            }
            DeviceRequest::FeeRegistrationProof(request) => {
                let g = self.gens()?;
                let key = self.fee_signing_key()?;
                let response = create_fee_account_registration_auth_proof(rng, &key, &request, &g)?;
                Ok(DeviceResponse::FeeRegistration(response))
            }
            DeviceRequest::FeeTopupProof(request) => {
                let g = self.gens()?;
                let key = self.fee_signing_key()?;
                let response = create_fee_account_auth_proof(rng, &key, &request, &g)?;
                Ok(DeviceResponse::FeeTopup(response))
            }
            DeviceRequest::FeePaymentProof(request) => {
                let g = self.gens()?;
                let key = self.fee_signing_key()?;
                let response = create_fee_payment_auth_proof(rng, &key, &request, &g)?;
                Ok(DeviceResponse::FeePayment(response))
            }
        }
    }

    fn gens(&mut self) -> Result<DeviceGenerators, Error> {
        if let Some(g) = self.generators {
            return Ok(g);
        }
        let g = DeviceGenerators::new()?;
        self.generators = Some(g);
        Ok(g)
    }

    /// Stores `seed` and the keys derived from it.
    fn set_seed(&mut self, seed: BPMasterSeed) -> Result<&AuthSigningKeys, Error> {
        let g = self.gens()?;
        let keys = AuthSigningKeys::from_master_seed(&seed, SEED_PATH, SEED_COUNTER, &g)?;
        self.seed = Some(seed);
        Ok(self.keys.insert(keys))
    }

    fn master_seed(&self) -> Result<&BPMasterSeed, Error> {
        self.seed
            .as_ref()
            .ok_or_else(|| Error::Device("master seed not loaded".into()))
    }

    fn signing_keys(&self) -> Result<&AuthSigningKeys, Error> {
        self.keys
            .as_ref()
            .ok_or_else(|| Error::Device("keys not generated".into()))
    }

    /// Fee accounts are keyed by `sk_aff`.
    fn fee_signing_key(&self) -> Result<AuthSigningKey, Error> {
        Ok(AuthSigningKey {
            sk: self.signing_keys()?.sk_aff,
        })
    }

    // Sealing runs only under std (AEAD). The no-std stubs exist so `Device` compiles for embedded
    // (Ledger) targets, which persist keys via their secure element rather than this sealed blob.
    // TODO: Maybe add a dedicated feature or trait config for when sealing is needed
    #[cfg(feature = "std")]
    fn seal_seed<R: CryptoRngCore>(
        &mut self,
        seed: &BPMasterSeed,
        rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        sealing::seal(self.provider.as_mut(), seed, rng)
    }

    #[cfg(not(feature = "std"))]
    fn seal_seed<R: CryptoRngCore>(
        &mut self,
        _seed: &BPMasterSeed,
        _rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        Err(Error::Device("sealing requires std".into()))
    }

    #[cfg(feature = "std")]
    fn unseal_seed(&self, blob: &[u8]) -> Result<BPMasterSeed, Error> {
        sealing::unseal(self.provider.as_ref(), blob)
    }

    #[cfg(not(feature = "std"))]
    fn unseal_seed(&self, _blob: &[u8]) -> Result<BPMasterSeed, Error> {
        Err(Error::Device("sealing requires std".into()))
    }
}

#[cfg(any(not(feature = "std"), feature = "hardcoded-key"))]
impl Default for Device {
    fn default() -> Self {
        Self::new()
    }
}

/// The device's API for the host
pub trait AuthDevice {
    /// Send request to the device and block till the response
    fn send(&mut self, request: DeviceRequest) -> Result<DeviceResponse, Error>;

    fn generate_keys(&mut self) -> Result<(PubKeys, Vec<u8>), Error> {
        match self.send(DeviceRequest::GenerateKeys)? {
            DeviceResponse::Keys { pubkeys, sealed } => Ok((pubkeys, sealed)),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn load_keys(&mut self, sealed: Vec<u8>) -> Result<(), Error> {
        match self.send(DeviceRequest::LoadKeys(sealed))? {
            DeviceResponse::Ok => Ok(()),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn key_registration(
        &mut self,
        request: KeyRegistrationDeviceRequest,
    ) -> Result<KeyRegistrationDeviceResponse, Error> {
        match self.send(DeviceRequest::KeyRegistration(request))? {
            DeviceResponse::KeyRegistration(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn registration_proof(
        &mut self,
        request: RegistrationDeviceRequest,
    ) -> Result<AccountRegistrationDeviceResponse, Error> {
        match self.send(DeviceRequest::RegistrationProof(request))? {
            DeviceResponse::Registration(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn mint_proof(
        &mut self,
        request: MintDeviceRequest,
    ) -> Result<AssetMintingDeviceResponse, Error> {
        match self.send(DeviceRequest::MintProof(request))? {
            DeviceResponse::Mint(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn affirm(
        &mut self,
        request: AffirmationDeviceRequest,
    ) -> Result<AffirmationDeviceResponse, Error> {
        match self.send(DeviceRequest::Affirm(request))? {
            DeviceResponse::Affirmation(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn fee_registration_proof(
        &mut self,
        request: FeeAccountRegistrationDeviceRequest,
    ) -> Result<FeeAccountRegistrationDeviceResponse, Error> {
        match self.send(DeviceRequest::FeeRegistrationProof(request))? {
            DeviceResponse::FeeRegistration(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn fee_topup_proof(
        &mut self,
        request: FeeAccountDeviceRequest,
    ) -> Result<FeeAccountTopupDeviceResponse, Error> {
        match self.send(DeviceRequest::FeeTopupProof(request))? {
            DeviceResponse::FeeTopup(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn fee_payment_proof(
        &mut self,
        request: FeePaymentDeviceRequest,
    ) -> Result<FeeAccountPaymentDeviceResponse, Error> {
        match self.send(DeviceRequest::FeePaymentProof(request))? {
            DeviceResponse::FeePayment(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn account_randomness(
        &mut self,
        request: AccountRandomnessDeviceRequest,
    ) -> Result<AccountRandomnessDeviceResponse, Error> {
        match self.send(DeviceRequest::AccountRandomness(request))? {
            DeviceResponse::AccountRandomness(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

    fn fee_account_randomness(
        &mut self,
        request: AccountRandomnessDeviceRequest,
    ) -> Result<FeeAccountRandomnessDeviceResponse, Error> {
        match self.send(DeviceRequest::FeeAccountRandomness(request))? {
            DeviceResponse::FeeAccountRandomness(response) => Ok(response),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }
}

/// Builds an account state from the device-returned public keys, sampling fresh commitment
/// randomness.
#[cfg(feature = "host_proofs")]
pub fn account_state_from_pubkeys<R: CryptoRngCore>(
    rng: &mut R,
    pk_aff: PallasA,
    pk_enc: PallasA,
    asset_id: AssetId,
    counter: NullifierSkGenCounter,
    identity: &[u8],
) -> Result<(AccountAssetState, PallasScalar), Error> {
    let id = hash_identity::<PallasScalar>(identity);
    let (bp_state, rho_randomness) = BPAccountState::new(
        rng,
        id,
        pk_aff,
        pk_enc,
        asset_id,
        counter,
        poseidon_params().params.clone(),
    )?;
    let current_state: AccountState = bp_state.try_into()?;
    Ok((
        AccountAssetState {
            current_state,
            pending_state: None,
        },
        rho_randomness,
    ))
}

/// Builds an account state from the device-returned public keys and account randomness.
#[cfg(feature = "host_proofs")]
pub fn account_state_from_pubkeys_given_randomness(
    pk_aff: PallasA,
    pk_enc: PallasA,
    asset_id: AssetId,
    counter: NullifierSkGenCounter,
    identity: &[u8],
    randomness: &AccountRandomnessDeviceResponse,
) -> Result<(AccountAssetState, PallasScalar), Error> {
    let id = hash_identity::<PallasScalar>(identity);
    let rho_randomness = randomness.rho_randomness.decode()?;
    let bp_state = BPAccountState::new_given_randomness(
        id,
        pk_aff,
        pk_enc,
        asset_id,
        counter,
        randomness.randomness.decode()?,
        rho_randomness,
        poseidon_params().params.clone(),
    )?;
    let current_state: AccountState = bp_state.try_into()?;
    Ok((
        AccountAssetState {
            current_state,
            pending_state: None,
        },
        rho_randomness,
    ))
}

/// Builds a fee account state from the device-returned public key and fee account randomness.
#[cfg(feature = "host_proofs")]
pub fn fee_account_state_from_pubkey_given_randomness(
    pk: &AccountPublicKey,
    asset_id: AssetId,
    balance: Balance,
    randomness: &FeeAccountRandomnessDeviceResponse,
) -> Result<FeeAccountAssetState, Error> {
    FeeAccountAssetState::new_given_randomness(
        pk,
        asset_id,
        balance,
        randomness.initial_rho.decode()?,
        randomness.initial_randomness.decode()?,
    )
}
