//! Live Speculos integration tests. Each drives a running Speculos over its APDU TCP port and
//! verifies the device's proof host-side — the automated form of `ledger_tests` (no copy/paste).
//! The address defaults to `127.0.0.1:9999`, override with `SPECULOS_APDU_ADDR`.
//!
//! These are `#[ignore]`d — they need Speculos running with the app loaded:
//!   speculos --apdu-port 9999 --model nanosp target/nanosplus/release/app-boilerplate-rust
//!   cargo nextest run -p polymesh-dart --features host_proofs --run-ignored all -E 'test(speculos_)'
//!
//! Speculos APDU framing: send `[len: u32 BE][apdu]`; recv `[len: u32 BE][data][sw: u16 BE]` (the
//! status word is separate from the length). Proof-handler responses carry the app's `[len: u8]`
//! prefix inside `data`; `GetPubkey` returns 64 raw bytes.

use super::account_state_from_pubkeys;
use super::ledger_tests::{
    ASSET_ID, COUNTER, IDENTITY, INS_ASSET_REG, INS_GET_RESPONSE_CHUNK, INS_KEY_REG, INS_MINT,
    affirm_apdus, affirm_leg_and_tree, apdu_data, full_apdu, getpubkey_apdu,
};
use crate::AssetPkTLookup;
use crate::account_reg_split::AccountRegHostProtocol;
use crate::affirmation_proofs::{
    ReceiverAffirmationHostProtocol, ReceiverClaimHostProtocol, SenderAffirmationHostProtocol,
    SenderCounterUpdateHostProtocol,
};
use crate::curve_tree::{AccountTreeConfig, CurveTreeConfig, CurveTreeLookup, ProverCurveTree};
use crate::key_reg_split::{KeyRegistrationDeviceRequest, KeyRegistrationDeviceResponse};
use crate::mint_split::MintHostProtocol;
use crate::split_types::{
    AccountRegistrationDeviceResponse, AffirmationDeviceRequest, AffirmationDeviceResponse,
    AssetMintingDeviceResponse,
};
use crate::{
    ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountKeys, AccountPublicKey,
    AccountPublicKeys, CompressedAffine, EncryptionPublicKey, PallasA, dart_gens,
};
use codec::{Decode, Encode};
use rand::rngs::StdRng;
use rand_core::SeedableRng;
use std::io::{Read, Write};
use std::net::TcpStream;

struct Speculos {
    stream: TcpStream,
}

impl Speculos {
    fn connect() -> Self {
        let addr =
            std::env::var("SPECULOS_APDU_ADDR").unwrap_or_else(|_| "127.0.0.1:9999".to_string());
        let stream = TcpStream::connect(&addr).unwrap_or_else(|e| {
            panic!(
                "connect to Speculos at {addr} failed: {e}; run `speculos --apdu-port 9999 <app.elf>` and make the port reachable"
            )
        });
        Self { stream }
    }

    fn exchange(&mut self, apdu: &[u8]) -> (u16, Vec<u8>) {
        self.stream
            .write_all(&(apdu.len() as u32).to_be_bytes())
            .unwrap();
        self.stream.write_all(apdu).unwrap();
        let mut len = [0u8; 4];
        self.stream.read_exact(&mut len).unwrap();
        let mut data = vec![0u8; u32::from_be_bytes(len) as usize];
        self.stream.read_exact(&mut data).unwrap();
        let mut sw = [0u8; 2];
        self.stream.read_exact(&mut sw).unwrap();
        (u16::from_be_bytes(sw), data)
    }

    /// Send an APDU (hex), assert `SW == 0x9000`, return its response data field.
    fn send(&mut self, apdu_hex: &str) -> Vec<u8> {
        let (sw, data) = self.exchange(&hex::decode(apdu_hex).expect("valid apdu hex"));
        assert_eq!(sw, 0x9000, "device returned SW {sw:04x}");
        data
    }
}

/// Strip the app's `[len: u8]` prefix from a proof-handler response.
fn payload(data: &[u8]) -> Vec<u8> {
    let len = data[0] as usize;
    assert_eq!(data.len(), 1 + len, "app length-prefix mismatch");
    data[1..].to_vec()
}

/// Query the device's real account pubkeys (INS 5). Response is 64 raw bytes, no length prefix.
fn get_pubkeys(dev: &mut Speculos) -> (PallasA, PallasA) {
    let data = dev.send(&getpubkey_apdu());
    assert_eq!(data.len(), 64, "expected pk_aff(32) || pk_enc(32)");
    let pk_aff =
        PallasA::try_from(&CompressedAffine::from_str(&hex::encode(&data[..32])).unwrap()).unwrap();
    let pk_enc =
        PallasA::try_from(&CompressedAffine::from_str(&hex::encode(&data[32..])).unwrap()).unwrap();
    (pk_aff, pk_enc)
}

/// Send the chunked affirmation request; the last chunk's reply is response slice 0. Pull the rest via
/// `GetResponseChunk` (INS 12) until a slice has len < 255, then decode.
fn affirm_exchange(
    dev: &mut Speculos,
    request: &AffirmationDeviceRequest,
) -> AffirmationDeviceResponse {
    let mut data = Vec::new();
    for apdu in affirm_apdus(&request.encode()) {
        data = dev.send(&apdu);
    }
    let mut bytes = Vec::new();
    loop {
        let len = data[0] as usize;
        assert_eq!(data.len(), 1 + len, "response slice length mismatch");
        bytes.extend_from_slice(&data[1..]);
        if len < 255 {
            break;
        }
        data = dev.send(&full_apdu(INS_GET_RESPONSE_CHUNK, &[]));
    }
    AffirmationDeviceResponse::decode(&mut &bytes[..])
        .expect("decodes as AffirmationDeviceResponse")
}

#[test]
#[ignore]
fn speculos_key_registration() {
    let mut dev = Speculos::connect();
    let request = KeyRegistrationDeviceRequest {
        identity: IDENTITY.to_vec(),
    };
    let data = dev.send(&full_apdu(INS_KEY_REG, &apdu_data(&request.encode())));
    let response = KeyRegistrationDeviceResponse::decode(&mut &payload(&data)[..]).unwrap();

    let g = dart_gens();
    let pub_keys: Vec<(PallasA, PallasA)> = response
        .accounts
        .iter()
        .map(|(a, e)| (PallasA::try_from(a).unwrap(), PallasA::try_from(e).unwrap()))
        .collect();
    response
        .inner
        .decode()
        .unwrap()
        .verify(pub_keys, IDENTITY, g.sig_key_gen(), g.enc_key_gen())
        .unwrap();
}

#[test]
#[ignore]
fn speculos_account_asset_registration() {
    let mut dev = Speculos::connect();
    let mut rng = StdRng::seed_from_u64(0);
    let (pk_aff, pk_enc) = get_pubkeys(&mut dev);

    let (account_state, rho) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    let (protocol, request) =
        AccountRegHostProtocol::init(&mut rng, &account_state, rho, COUNTER, IDENTITY, None)
            .unwrap();

    let data = dev.send(&full_apdu(INS_ASSET_REG, &apdu_data(&request.encode())));
    let response = AccountRegistrationDeviceResponse::decode(&mut &payload(&data)[..]).unwrap();

    let proof = protocol
        .finish::<_, ()>(
            &mut rng,
            &response,
            COUNTER,
            AccountTreeConfig::parameters(),
        )
        .unwrap();
    proof
        .verify(
            IDENTITY,
            AccountTreeConfig::parameters(),
            &mut rng,
            &AssetPkTLookup::default(),
        )
        .unwrap();
}

#[test]
#[ignore]
fn speculos_mint() {
    let mut dev = Speculos::connect();
    let mut rng = StdRng::seed_from_u64(0);
    let (pk_aff, pk_enc) = get_pubkeys(&mut dev);

    let (mut account_state, _rho) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
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
    let (protocol, request) = MintHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &pk,
        &mut account_state,
        1000,
        IDENTITY,
        &account_tree,
    )
    .unwrap();

    let data = dev.send(&full_apdu(INS_MINT, &apdu_data(&request.encode())));
    let response = AssetMintingDeviceResponse::decode(&mut &payload(&data)[..]).unwrap();

    let root_block = account_tree.get_block_number().unwrap();
    let proof = protocol
        .finish::<_, ()>(
            &mut rng,
            &response,
            root_block,
            AccountTreeConfig::parameters(),
        )
        .unwrap();
    proof
        .verify(IDENTITY, account_tree.root().unwrap(), &mut rng)
        .unwrap();
}

#[test]
#[ignore]
fn speculos_sender_affirmation() {
    let mut dev = Speculos::connect();
    let mut rng = StdRng::seed_from_u64(0);
    let (pk_aff, pk_enc) = get_pubkeys(&mut dev);

    let (mut sender_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    sender_state.current_state.balance = 1000;
    let leaf = sender_state.current_commitment().unwrap();
    let counterparty = AccountKeys::rand(&mut rng).unwrap();
    let (leg_enc, leg_ref, account_tree) = affirm_leg_and_tree(
        &mut rng,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        counterparty.enc.public,
        300,
        leaf,
    );

    let (protocol, request) = SenderAffirmationHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut sender_state,
        &leg_ref,
        &leg_enc,
        300,
        &account_tree,
    )
    .unwrap();

    let response = affirm_exchange(&mut dev, &request);
    let proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    proof
        .verify(&leg_enc, &account_tree.root().unwrap(), &mut rng)
        .unwrap();
}

#[test]
#[ignore]
fn speculos_receiver_affirmation() {
    let mut dev = Speculos::connect();
    let mut rng = StdRng::seed_from_u64(0);
    let (pk_aff, pk_enc) = get_pubkeys(&mut dev);

    let (mut receiver_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    let leaf = receiver_state.current_commitment().unwrap();
    let counterparty = AccountKeys::rand(&mut rng).unwrap();
    let (leg_enc, leg_ref, account_tree) = affirm_leg_and_tree(
        &mut rng,
        counterparty.enc.public,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        300,
        leaf,
    );

    let (protocol, request) = ReceiverAffirmationHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut receiver_state,
        &leg_ref,
        &leg_enc,
        300,
        &account_tree,
    )
    .unwrap();

    let response = affirm_exchange(&mut dev, &request);
    let proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    proof
        .verify(&leg_enc, &account_tree.root().unwrap(), &mut rng)
        .unwrap();
}

#[test]
#[ignore]
fn speculos_receiver_claim() {
    let mut dev = Speculos::connect();
    let mut rng = StdRng::seed_from_u64(0);
    let (pk_aff, pk_enc) = get_pubkeys(&mut dev);

    let (mut receiver_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    receiver_state.current_state.counter = 1;
    let leaf = receiver_state.current_commitment().unwrap();
    let counterparty = AccountKeys::rand(&mut rng).unwrap();
    let (leg_enc, leg_ref, account_tree) = affirm_leg_and_tree(
        &mut rng,
        counterparty.enc.public,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        300,
        leaf,
    );

    let (protocol, request) = ReceiverClaimHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut receiver_state,
        &leg_ref,
        &leg_enc,
        300,
        &account_tree,
    )
    .unwrap();

    let response = affirm_exchange(&mut dev, &request);
    let proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    proof
        .verify(&leg_enc, &account_tree.root().unwrap(), &mut rng)
        .unwrap();
}

#[test]
#[ignore]
fn speculos_sender_counter_update() {
    let mut dev = Speculos::connect();
    let mut rng = StdRng::seed_from_u64(0);
    let (pk_aff, pk_enc) = get_pubkeys(&mut dev);

    let (mut sender_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    sender_state.current_state.counter = 1;
    let leaf = sender_state.current_commitment().unwrap();
    let counterparty = AccountKeys::rand(&mut rng).unwrap();
    let (leg_enc, leg_ref, account_tree) = affirm_leg_and_tree(
        &mut rng,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        counterparty.enc.public,
        0,
        leaf,
    );

    let (protocol, request) = SenderCounterUpdateHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut sender_state,
        &leg_ref,
        &leg_enc,
        0,
        &account_tree,
    )
    .unwrap();

    let response = affirm_exchange(&mut dev, &request);
    let proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    proof
        .verify(&leg_enc, &account_tree.root().unwrap(), &mut rng)
        .unwrap();
}
