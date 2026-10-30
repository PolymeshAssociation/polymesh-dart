use codec::{Decode, Encode};
use rand_core::CryptoRngCore;

use polymesh_dart_bp::auth_proofs::keys::{keygen_enc, keygen_sig};

use super::CompressedAffine;
use super::auth_proofs::{
    AuthSigningKeys, create_affirmation_auth_proof, create_key_registration_auth_proof,
    create_mint_auth_proof, create_registration_auth_proof,
};
use super::key_reg_split::{KeyRegistrationDeviceRequest, KeyRegistrationDeviceResponse};
use super::split_types::{
    AffirmationDeviceRequest, AffirmationDeviceResponse, AssetMintingDeviceResponse,
    MintDeviceRequest, RegistrationDeviceRequest, TwoSksDeviceResponse,
};
use crate::Error;
use ark_std::string::String;
use ark_std::vec::Vec;

#[cfg(feature = "host_proofs")]
use super::{
    AccountAssetState, AccountState, PallasA, PallasScalar, hash_identity, poseidon_params,
};
#[cfg(feature = "host_proofs")]
use polymesh_dart_bp::account::state::AccountState as BPAccountState;
#[cfg(feature = "host_proofs")]
use polymesh_dart_common::{AssetId, NullifierSkGenCounter};

mod generators;
#[cfg(all(test, feature = "host_proofs"))]
mod ledger_tests;
#[cfg(feature = "std")]
mod sealing;
#[cfg(all(test, feature = "host_proofs"))]
mod speculos_tests;
#[cfg(all(test, feature = "host_proofs"))]
mod tests;
#[cfg(feature = "std")]
mod transport;
#[cfg(feature = "host_proofs")]
mod workflow;

pub use generators::DeviceGenerators;
#[cfg(all(feature = "std", feature = "hardcoded-key"))]
pub use sealing::HardcodedKeyProvider;
#[cfg(feature = "std")]
pub use sealing::{DataKey, DataKeyProvider};
#[cfg(feature = "std")]
pub use transport::{StreamDevice, read_frame, serve, write_frame};
#[cfg(feature = "host_proofs")]
pub use workflow::run_register_mint_affirm;

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
}

#[derive(Clone, Encode, Decode)]
pub enum DeviceResponse {
    Ok,
    /// sealed data are the encrypted secret key
    Keys {
        pubkeys: PubKeys,
        sealed: Vec<u8>,
    },
    KeyRegistration(KeyRegistrationDeviceResponse),
    Registration(TwoSksDeviceResponse),
    Mint(AssetMintingDeviceResponse),
    Affirmation(AffirmationDeviceResponse),
    Err(String),
}

/// Holds the secret keys. This is what runs inside the enclave.
pub struct Device {
    keys: Option<AuthSigningKeys>,
    #[cfg(feature = "std")]
    provider: Box<dyn DataKeyProvider>,
}

impl Device {
    /// Builds a device that seals keys via `provider`.
    #[cfg(feature = "std")]
    pub fn with_provider(provider: Box<dyn DataKeyProvider>) -> Self {
        Self {
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
        Self { keys: None }
    }

    pub fn handle<R: CryptoRngCore>(
        &mut self,
        request: DeviceRequest,
        rng: &mut R,
    ) -> Result<DeviceResponse, Error> {
        match request {
            DeviceRequest::GenerateKeys => {
                let g = self.gens()?;
                let (sk_aff, pk_aff) = keygen_sig(rng, g.sig_key_gen());
                let (sk_enc, pk_enc) = keygen_enc(rng, g.enc_key_gen());
                let keys = AuthSigningKeys {
                    sk_aff: sk_aff.0,
                    sk_enc: sk_enc.0,
                };
                let sealed = self.seal_keys(&keys, rng)?;
                self.keys = Some(keys);
                Ok(DeviceResponse::Keys {
                    pubkeys: PubKeys {
                        pk_aff: CompressedAffine::try_from(pk_aff.0)?,
                        pk_enc: CompressedAffine::try_from(pk_enc.0)?,
                    },
                    sealed,
                })
            }
            DeviceRequest::LoadKeys(blob) => {
                let keys = self.unseal_keys(&blob)?;
                self.keys = Some(keys);
                Ok(DeviceResponse::Ok)
            }
            DeviceRequest::KeyRegistration(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response = create_key_registration_auth_proof(
                    rng,
                    keys,
                    &request.identity,
                    g.sig_key_gen(),
                    g.enc_key_gen(),
                )?;
                Ok(DeviceResponse::KeyRegistration(response))
            }
            DeviceRequest::RegistrationProof(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response = create_registration_auth_proof(
                    rng,
                    keys,
                    &request,
                    g.sig_key_gen(),
                    g.enc_key_gen(),
                )?;
                Ok(DeviceResponse::Registration(response))
            }
            DeviceRequest::MintProof(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response =
                    create_mint_auth_proof(rng, keys, &request, g.sig_key_gen(), g.enc_key_gen())?;
                Ok(DeviceResponse::Mint(response))
            }
            DeviceRequest::Affirm(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response = create_affirmation_auth_proof(
                    rng,
                    keys,
                    &request,
                    g.comm_re_rand_gen,
                    g.anchor_gen,
                    g.leg_asset_value_gen,
                    &g.account_comm_key,
                )?;
                Ok(DeviceResponse::Affirmation(response))
            }
        }

        // TODO: Add check if device initialized with params and keys or not
    }

    fn gens(&self) -> Result<DeviceGenerators, Error> {
        DeviceGenerators::new()
    }

    fn signing_keys(&self) -> Result<&AuthSigningKeys, Error> {
        self.keys
            .as_ref()
            .ok_or_else(|| Error::Device("keys not generated".into()))
    }

    // Sealing runs only under std (AEAD). The no-std stubs exist so `Device` compiles for embedded
    // (Ledger) targets, which persist keys via their secure element rather than this sealed blob.
    // TODO: Maybe add a dedicated feature or trait config for when sealing is needed
    #[cfg(feature = "std")]
    fn seal_keys<R: CryptoRngCore>(
        &mut self,
        keys: &AuthSigningKeys,
        rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        sealing::seal(self.provider.as_mut(), keys, rng)
    }

    #[cfg(not(feature = "std"))]
    fn seal_keys<R: CryptoRngCore>(
        &mut self,
        _keys: &AuthSigningKeys,
        _rng: &mut R,
    ) -> Result<Vec<u8>, Error> {
        Err(Error::Device("sealing requires std".into()))
    }

    #[cfg(feature = "std")]
    fn unseal_keys(&self, blob: &[u8]) -> Result<AuthSigningKeys, Error> {
        sealing::unseal(self.provider.as_ref(), blob)
    }

    #[cfg(not(feature = "std"))]
    fn unseal_keys(&self, _blob: &[u8]) -> Result<AuthSigningKeys, Error> {
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
    ) -> Result<TwoSksDeviceResponse, Error> {
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
