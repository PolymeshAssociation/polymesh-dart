use codec::{Decode, Encode};
use rand_core::CryptoRngCore;

use polymesh_dart_bp::auth_proofs::keys::{keygen_enc, keygen_sig};

use super::auth_proofs::{
    AuthSigningKeys, create_affirmation_auth_proof, create_mint_auth_proof,
    create_registration_auth_proof,
};
use super::split_types::{
    AffirmationDeviceRequest, AffirmationDeviceResponse, AssetMintingDeviceResponse,
    MintDeviceRequest, RegistrationDeviceRequest, TwoSksDeviceResponse,
};
use super::{CompressedAffine, PallasA};
use crate::Error;
use ark_std::string::String;
use ark_std::vec::Vec;

#[cfg(feature = "host_proofs")]
use super::{
    AccountAssetState, AccountState, PallasScalar, dart_gens, hash_identity, poseidon_params,
};
#[cfg(feature = "host_proofs")]
use polymesh_dart_bp::account::state::AccountState as BPAccountState;
#[cfg(feature = "host_proofs")]
use polymesh_dart_common::{AssetId, NullifierSkGenCounter};

#[cfg(feature = "std")]
mod sealing;
#[cfg(all(test, feature = "host_proofs"))]
mod tests;
#[cfg(feature = "std")]
mod transport;

#[cfg(feature = "std")]
pub use transport::{StreamDevice, read_frame, serve, write_frame};

/// The fixed generator points the device needs; it can't derive them (hash-to-curve is host-only).
#[derive(Clone, Debug, Encode, Decode)]
pub struct Generators {
    pub sig_key_gen: CompressedAffine,
    pub enc_key_gen: CompressedAffine,
    pub comm_re_rand_gen: CompressedAffine,
    pub leg_asset_value_gen: CompressedAffine,
}

impl Generators {
    fn points(&self) -> Result<DeviceGenerators, Error> {
        Ok(DeviceGenerators {
            sig_key_gen: PallasA::try_from(&self.sig_key_gen)?,
            enc_key_gen: PallasA::try_from(&self.enc_key_gen)?,
            comm_re_rand_gen: PallasA::try_from(&self.comm_re_rand_gen)?,
            leg_asset_value_gen: PallasA::try_from(&self.leg_asset_value_gen)?,
        })
    }
}

#[derive(Copy, Clone)]
struct DeviceGenerators {
    sig_key_gen: PallasA,
    enc_key_gen: PallasA,
    comm_re_rand_gen: PallasA,
    leg_asset_value_gen: PallasA,
}

#[derive(Clone, Debug, Encode, Decode)]
pub struct PubKeys {
    pub pk_aff: CompressedAffine,
    pub pk_enc: CompressedAffine,
}

#[derive(Clone, Encode, Decode)]
pub enum DeviceRequest {
    SetupParams(Generators),
    GenerateKeys,
    LoadKeys(Vec<u8>),
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
    Registration(TwoSksDeviceResponse),
    Mint(AssetMintingDeviceResponse),
    Affirmation(AffirmationDeviceResponse),
    Err(String),
}

/// Holds the secret keys and generators. This is what runs inside the enclave.
pub struct Device {
    generators: Option<DeviceGenerators>,
    keys: Option<AuthSigningKeys>,
}

impl Device {
    pub fn new() -> Self {
        Self {
            generators: None,
            keys: None,
        }
    }

    pub fn handle<R: CryptoRngCore>(
        &mut self,
        request: DeviceRequest,
        rng: &mut R,
    ) -> Result<DeviceResponse, Error> {
        match request {
            DeviceRequest::SetupParams(generators) => {
                self.generators = Some(generators.points()?);
                Ok(DeviceResponse::Ok)
            }
            DeviceRequest::GenerateKeys => {
                let g = self.gens()?;
                let (sk_aff, pk_aff) = keygen_sig(rng, g.sig_key_gen);
                let (sk_enc, pk_enc) = keygen_enc(rng, g.enc_key_gen);
                let keys = AuthSigningKeys {
                    sk_aff: sk_aff.0,
                    sk_enc: sk_enc.0,
                };
                let sealed = seal_keys(&keys, rng)?;
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
                self.keys = Some(unseal_keys(&blob)?);
                Ok(DeviceResponse::Ok)
            }
            DeviceRequest::RegistrationProof(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response = create_registration_auth_proof(
                    rng,
                    keys,
                    &request,
                    g.sig_key_gen,
                    g.enc_key_gen,
                )?;
                Ok(DeviceResponse::Registration(response))
            }
            DeviceRequest::MintProof(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response =
                    create_mint_auth_proof(rng, keys, &request, g.sig_key_gen, g.enc_key_gen)?;
                Ok(DeviceResponse::Mint(response))
            }
            DeviceRequest::Affirm(request) => {
                let g = self.gens()?;
                let keys = self.signing_keys()?;
                let response = create_affirmation_auth_proof(
                    rng,
                    keys,
                    &request,
                    g.sig_key_gen,
                    g.enc_key_gen,
                    g.comm_re_rand_gen,
                    g.leg_asset_value_gen,
                )?;
                Ok(DeviceResponse::Affirmation(response))
            }
        }

        // TODO: Add check if device initialized with params and keys or not
    }

    fn gens(&self) -> Result<DeviceGenerators, Error> {
        self.generators
            .ok_or_else(|| Error::Device("not provisioned".into()))
    }

    fn signing_keys(&self) -> Result<&AuthSigningKeys, Error> {
        self.keys
            .as_ref()
            .ok_or_else(|| Error::Device("keys not generated".into()))
    }
}

impl Default for Device {
    fn default() -> Self {
        Self::new()
    }
}

// The Nitro enclave is a `x86_64-unknown-linux-musl` std build, so the real sealing runs there.
// The no-std stubs exist only so `Device` compiles for embedded (Ledger) targets, which persist
// keys via their secure element rather than this sealed blob.
#[cfg(feature = "std")]
fn seal_keys<R: CryptoRngCore>(keys: &AuthSigningKeys, rng: &mut R) -> Result<Vec<u8>, Error> {
    sealing::seal(keys, rng)
}

#[cfg(not(feature = "std"))]
fn seal_keys<R: CryptoRngCore>(_keys: &AuthSigningKeys, _rng: &mut R) -> Result<Vec<u8>, Error> {
    Err(Error::Device("sealing requires std".into()))
}

#[cfg(feature = "std")]
fn unseal_keys(blob: &[u8]) -> Result<AuthSigningKeys, Error> {
    sealing::unseal(blob)
}

#[cfg(not(feature = "std"))]
fn unseal_keys(_blob: &[u8]) -> Result<AuthSigningKeys, Error> {
    Err(Error::Device("sealing requires std".into()))
}

/// The device's API for the host
pub trait AuthDevice {
    /// Send request to the device and block till the response
    fn send(&mut self, request: DeviceRequest) -> Result<DeviceResponse, Error>;

    /// Initialize the params, set generators only for now
    fn setup_params(&mut self, generators: Generators) -> Result<(), Error> {
        match self.send(DeviceRequest::SetupParams(generators))? {
            DeviceResponse::Ok => Ok(()),
            DeviceResponse::Err(message) => Err(Error::Device(message)),
            _ => Err(Error::Device("unexpected response".into())),
        }
    }

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

/// Builds the generator set from the host's `dart_gens()`. `comm_re_rand_gen` comes from the account
/// tree parameters.
#[cfg(feature = "host_proofs")]
pub fn host_generators(comm_re_rand_gen: PallasA) -> Result<Generators, Error> {
    let gens = dart_gens();
    Ok(Generators {
        sig_key_gen: CompressedAffine::try_from(gens.sig_key_gen())?,
        enc_key_gen: CompressedAffine::try_from(gens.enc_key_gen())?,
        comm_re_rand_gen: CompressedAffine::try_from(comm_re_rand_gen)?,
        leg_asset_value_gen: CompressedAffine::try_from(gens.leg_asset_value_gen())?,
    })
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
