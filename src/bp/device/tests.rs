use super::{
    AuthDevice, Device, DeviceRequest, DeviceResponse, StreamDevice, account_state_from_pubkeys,
    host_generators, run_register_mint_affirm, serve,
};
use crate::Error;
use crate::account_reg_split::AccountRegHostProtocol;
use crate::curve_tree::{AccountTreeConfig, CurveTreeConfig};
use crate::{AssetId, PallasA};
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
    (7000u16..8000)
        .find_map(|port| TcpListener::bind(("127.0.0.1", port)).ok())
        .expect("no free local port")
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
fn key_persists_across_restart() {
    let mut rng = StdRng::seed_from_u64(0);
    let identity: &[u8] = b"test";
    let asset_id: AssetId = 1;
    let counter: NullifierSkGenCounter = 0;

    let tree_params = AccountTreeConfig::parameters();
    let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;
    let generators = host_generators(comm_re_rand_gen).unwrap();

    // Enclave run 1: generate and seal the keys.
    let mut device = InMemoryDevice::new(StdRng::seed_from_u64(1));
    device.setup_params(generators.clone()).unwrap();
    let (pubkeys, sealed) = device.generate_keys().unwrap();

    // Enclave run 2 (fresh device): reload the sealed keys.
    let mut device = InMemoryDevice::new(StdRng::seed_from_u64(2));
    device.setup_params(generators).unwrap();
    device.load_keys(sealed).unwrap();

    // A proof from the reloaded device is valid for the same account.
    let pk_aff = PallasA::try_from(&pubkeys.pk_aff).unwrap();
    let pk_enc = PallasA::try_from(&pubkeys.pk_enc).unwrap();
    let (account_state, rho_randomness) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, asset_id, counter, identity).unwrap();
    let (protocol, request) =
        AccountRegHostProtocol::init(&mut rng, &account_state, rho_randomness, counter, identity)
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
        .verify(identity, AccountTreeConfig::parameters(), &mut rng)
        .unwrap();
}
