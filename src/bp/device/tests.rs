use super::{
    AuthDevice, Device, DeviceRequest, DeviceResponse, StreamDevice, account_state_from_pubkeys,
    run_fee_register_topup_pay, run_register_mint_affirm, serve,
};
use crate::AssetPkTLookup;
use crate::Error;
use crate::account_reg_split::AccountRegHostProtocol;
use crate::curve_tree::{AccountTreeConfig, CurveTreeConfig};
use crate::split_types::AccountRandomnessDeviceRequest;
use crate::{AssetId, PallasA, PallasScalar, WrappedCanonical};
use codec::{Decode, Encode};
use polymesh_dart_common::NullifierSkGenCounter;
use rand::rngs::StdRng;
use rand_core::{CryptoRngCore, SeedableRng};
use std::net::{TcpListener, TcpStream};

/// A `Device` reached without a transport, but with the SCALE encode/decode roundtrip the real
/// transport performs.
struct InMemoryDevice<R> {
    device: Device,
    rng: R,
}

impl<R: CryptoRngCore> InMemoryDevice<R> {
    fn new(rng: R) -> Self {
        Self {
            device: Device::new(),
            rng,
        }
    }
}

impl<R: CryptoRngCore> AuthDevice for InMemoryDevice<R> {
    fn send(&mut self, request: DeviceRequest) -> Result<DeviceResponse, Error> {
        let bytes = request.encode();
        let request = DeviceRequest::decode(&mut &bytes[..]).map_err(|_| Error::DecodeError)?;
        let response = self.device.handle(request, &mut self.rng)?;
        let bytes = response.encode();
        DeviceResponse::decode(&mut &bytes[..]).map_err(|_| Error::DecodeError)
    }
}

fn bind_local_listener() -> TcpListener {
    TcpListener::bind(("127.0.0.1", 0)).expect("no free local port")
}

#[test]
fn register_mint_affirm_via_device() {
    let mut device = InMemoryDevice::new(StdRng::seed_from_u64(0));
    run_register_mint_affirm(&mut device);
}

#[test]
fn register_mint_affirm_over_tcp() {
    let listener = bind_local_listener();
    let addr = listener.local_addr().unwrap();
    let server = std::thread::spawn(move || {
        let mut device = Device::new();
        let mut rng = StdRng::seed_from_u64(0);
        let (stream, _) = listener.accept().unwrap();
        serve(stream, &mut device, &mut rng).unwrap();
    });

    let mut device = StreamDevice::new(TcpStream::connect(addr).unwrap());
    run_register_mint_affirm(&mut device);
    drop(device);
    server.join().unwrap();
}

#[test]
fn fee_register_topup_pay_via_device() {
    let mut device = InMemoryDevice::new(StdRng::seed_from_u64(0));
    run_fee_register_topup_pay(&mut device);
}

#[test]
fn fee_register_topup_pay_over_tcp() {
    let listener = bind_local_listener();
    let addr = listener.local_addr().unwrap();
    let server = std::thread::spawn(move || {
        let mut device = Device::new();
        let mut rng = StdRng::seed_from_u64(0);
        let (stream, _) = listener.accept().unwrap();
        serve(stream, &mut device, &mut rng).unwrap();
    });

    let mut device = StreamDevice::new(TcpStream::connect(addr).unwrap());
    run_fee_register_topup_pay(&mut device);
    drop(device);
    server.join().unwrap();
}

#[test]
fn account_randomness_persists_across_restart() {
    let request = || AccountRandomnessDeviceRequest {
        asset_id: 1,
        counter: 0,
    };
    let scalars = |a: &WrappedCanonical<PallasScalar>, b: &WrappedCanonical<PallasScalar>| {
        (a.decode().unwrap(), b.decode().unwrap())
    };

    let mut device = InMemoryDevice::new(StdRng::seed_from_u64(1));
    assert!(device.account_randomness(request()).is_err());
    let (_, sealed) = device.generate_keys().unwrap();
    let account = device.account_randomness(request()).unwrap();
    let fee = device.fee_account_randomness(request()).unwrap();

    let mut device = InMemoryDevice::new(StdRng::seed_from_u64(2));
    device.load_keys(sealed).unwrap();
    let account_again = device.account_randomness(request()).unwrap();
    let fee_again = device.fee_account_randomness(request()).unwrap();

    let account = scalars(&account.randomness, &account.rho_randomness);
    let fee = scalars(&fee.initial_rho, &fee.initial_randomness);
    assert_eq!(
        account,
        scalars(&account_again.randomness, &account_again.rho_randomness)
    );
    assert_eq!(
        fee,
        scalars(&fee_again.initial_rho, &fee_again.initial_randomness)
    );
    assert_ne!(account, fee);

    let next = device
        .account_randomness(AccountRandomnessDeviceRequest {
            asset_id: 1,
            counter: 1,
        })
        .unwrap();
    assert_ne!(account, scalars(&next.randomness, &next.rho_randomness));
}

#[test]
fn key_persists_across_restart() {
    let mut rng = StdRng::seed_from_u64(0);
    let identity: &[u8] = b"test";
    let asset_id: AssetId = 1;
    let counter: NullifierSkGenCounter = 0;

    // Enclave run 1: generate and seal the keys.
    let mut device = InMemoryDevice::new(StdRng::seed_from_u64(1));
    let (pubkeys, sealed) = device.generate_keys().unwrap();

    // Enclave run 2 (fresh device): reload the sealed keys.
    let mut device = InMemoryDevice::new(StdRng::seed_from_u64(2));
    device.load_keys(sealed).unwrap();

    // A proof from the reloaded device is valid for the same account.
    let pk_aff = PallasA::try_from(&pubkeys.pk_aff).unwrap();
    let pk_enc = PallasA::try_from(&pubkeys.pk_enc).unwrap();
    let (account_state, rho_randomness) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, asset_id, counter, identity).unwrap();
    let (protocol, request) = AccountRegHostProtocol::init(
        &mut rng,
        &account_state,
        rho_randomness,
        counter,
        identity,
        None,
    )
    .unwrap();
    let response = device.registration_proof(request).unwrap();
    let proof = protocol
        .finish::<_, ()>(
            &mut rng,
            &response,
            counter,
            AccountTreeConfig::parameters(),
        )
        .unwrap();
    proof
        .verify(
            identity,
            AccountTreeConfig::parameters(),
            &mut rng,
            &AssetPkTLookup::default(),
        )
        .unwrap();
}
