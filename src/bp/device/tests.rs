use super::{
    AuthDevice, Device, DeviceRequest, DeviceResponse, StreamDevice, account_state_from_pubkeys,
    host_generators, serve,
};
use crate::Error;
use crate::account_reg_split::AccountRegHostProtocol;
use crate::affirmation_proofs::SenderAffirmationHostProtocol;
use crate::curve_tree::{AccountTreeConfig, CurveTreeConfig, CurveTreeLookup, ProverCurveTree};
use crate::mint_split::MintHostProtocol;
use crate::{
    ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountKeys, AccountPublicKey,
    AccountPublicKeys, AccountStateCommitment, AssetId, Balance, EncryptionPublicKey, Leg,
    LegConfig, LegEncrypted, LegRef, PallasA, SettlementRef,
};
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

fn make_leg_and_tree<R: CryptoRngCore>(
    rng: &mut R,
    sender_enc: EncryptionPublicKey,
    receiver_enc: EncryptionPublicKey,
    asset_id: AssetId,
    amount: Balance,
    state_leaf: AccountStateCommitment,
) -> (
    LegEncrypted,
    LegRef,
    ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
) {
    let leg = Leg::new(sender_enc, receiver_enc, asset_id, amount).unwrap();
    let (_, leg_enc, _) = leg
        .encrypt(rng, LegConfig::default().into(), vec![], vec![], vec![])
        .unwrap();
    let leg_ref = LegRef::new(SettlementRef([1; 32]), 0);
    let mut tree = ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
        ACCOUNT_TREE_HEIGHT,
    )
    .unwrap();
    tree.insert(state_leaf.as_leaf_value().unwrap()).unwrap();
    tree.store_root().unwrap();
    (leg_enc, leg_ref, tree)
}

fn run_register_mint_affirm<D: AuthDevice>(device: &mut D) {
    let mut rng = StdRng::seed_from_u64(0);
    let identity: &[u8] = b"test";
    let asset_id: AssetId = 1;
    let counter: NullifierSkGenCounter = 0;

    let tree_params = AccountTreeConfig::parameters();
    let comm_re_rand_gen = tree_params.even_parameters.pc_gens().B_blinding;

    // Provision the device and generate the account keys inside it.
    device
        .setup_params(host_generators(comm_re_rand_gen).unwrap())
        .unwrap();
    let (pubkeys, _sealed) = device.generate_keys().unwrap();
    let pk_aff = PallasA::try_from(&pubkeys.pk_aff).unwrap();
    let pk_enc = PallasA::try_from(&pubkeys.pk_enc).unwrap();

    // Registration
    let (account_state, rho_randomness) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, asset_id, counter, identity).unwrap();
    let (protocol, request) =
        AccountRegHostProtocol::init(&mut rng, &account_state, rho_randomness, counter, identity)
            .unwrap();
    let response = device.registration_proof(request).unwrap();
    let reg_proof = protocol
        .finish::<_, ()>(
            &mut rng,
            &response,
            counter,
            AccountTreeConfig::parameters(),
        )
        .unwrap();
    reg_proof
        .verify(identity, AccountTreeConfig::parameters(), &mut rng)
        .unwrap();

    // Mint
    let mut account_state = account_state;
    let mut account_tree =
        ProverCurveTree::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::new(
            ACCOUNT_TREE_HEIGHT,
        )
        .unwrap();
    account_tree
        .insert(
            account_state
                .current_commitment()
                .unwrap()
                .as_leaf_value()
                .unwrap(),
        )
        .unwrap();
    account_tree.store_root().unwrap();
    let pk = AccountPublicKeys {
        acct: AccountPublicKey::from_affine(pk_aff).unwrap(),
        enc: EncryptionPublicKey::from_affine(pk_enc).unwrap(),
    };
    let mint_amount = 1000;
    let (protocol, request) = MintHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &pk,
        &mut account_state,
        mint_amount,
        identity,
        &account_tree,
    )
    .unwrap();
    let response = device.mint_proof(request).unwrap();
    let root_block = account_tree.get_block_number().unwrap();
    let mint_proof = protocol
        .finish::<_, ()>(
            &mut rng,
            &response,
            root_block,
            AccountTreeConfig::parameters(),
        )
        .unwrap();
    mint_proof
        .verify(identity, account_tree.root().unwrap(), &mut rng)
        .unwrap();

    // Sender affirmation
    let receiver = AccountKeys::rand(&mut rng).unwrap();
    let (mut sender_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, asset_id, counter, identity).unwrap();
    sender_state.current_state.balance = mint_amount;
    let leaf = sender_state.current_commitment().unwrap();
    let send_amount = 300;
    let (leg_enc, leg_ref, account_tree) = make_leg_and_tree(
        &mut rng,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        receiver.enc.public,
        asset_id,
        send_amount,
        leaf,
    );
    let (protocol, request) = SenderAffirmationHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut sender_state,
        &leg_ref,
        &leg_enc,
        send_amount,
        &account_tree,
    )
    .unwrap();
    let response = device.affirm(request).unwrap();
    let affirm_proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    let root = account_tree.root().unwrap();
    affirm_proof.verify(&leg_enc, &root, &mut rng).unwrap();
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
