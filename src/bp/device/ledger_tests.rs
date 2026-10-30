//! Ledger-parity tests. Each runs the host protocol against a `create_*_auth_proof` call and
//! verifies the host accepts the result — the same proof-construction code the Ledger app calls.
//!
//! The device response comes from a captured fixture when the matching env var is set, else it is
//! computed in-process with a local stand-in keypair (`device_keys`, below), so the test runs green
//! without a device. This in-process keypair is NOT what a real Ledger derives for `PATH` — the
//! app's `signing_keys` derives the account keys with `AuthSigningKeys::from_master_seed` from a
//! SLIP-21 node of the device's on-chip master seed, a secret this test has no access to. It only
//! needs SOME valid keypair to exercise the host protocol's accept logic.
//!
//! To validate against a real device or emulator:
//! - Paste each printed `*_APDU_FULL` into `ledgercomm-send`. Affirmation is chunked: send each
//!   `AFFIRM_APDU_FULL[i]` in order (the last chunk returns response slice 0), then send
//!   `GET_RESPONSE_CHUNK_APDU` repeatedly until a slice has len < 255.
//! - Set the matching `LEDGER_*_RESPONSE_HEX` to the raw response(s) `ledgercomm-send` prints
//!   (`[len][payload]` with an optional trailing `9000`; comma-separate a chunked affirmation's
//!   slices in order); `device_response_bytes` unwraps them.
//! Asset-reg and mint build the host request around the device's pubkeys, so first query the real
//! `(pk_aff, pk_enc)` via `GetPubkey` (INS 5) and pass `LEDGER_PUBKEYS_HEX`. Key registration is
//! self-contained (it verifies against the pubkeys in its own response) and needs neither.

use super::{DeviceGenerators, account_state_from_pubkeys};
use crate::AssetPkTLookup;
use crate::account_reg_split::AccountRegHostProtocol;
use crate::affirmation_proofs::{
    ReceiverAffirmationHostProtocol, ReceiverClaimHostProtocol, SenderAffirmationHostProtocol,
    SenderCounterUpdateHostProtocol,
};
use crate::auth_proofs::{
    AuthSigningKeys, create_affirmation_auth_proof, create_key_registration_auth_proof,
    create_mint_auth_proof, create_registration_auth_proof,
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
    AccountPublicKeys, AccountStateCommitment, Balance, CompressedAffine, EncryptionPublicKey, Leg,
    LegConfig, LegEncrypted, LegRef, PallasA, SettlementRef, dart_gens,
};
use ark_ec::CurveGroup;
use ark_std::vec::Vec;
use codec::{Decode, Encode};
use core::ops::Mul;
use polymesh_dart_bp::auth_proofs::keys::MasterSeed as BPMasterSeed;
use polymesh_dart_common::{AssetId, NullifierSkGenCounter};
use rand::rngs::StdRng;
use rand_core::SeedableRng;

/// Account path the app derives keys at under its SLIP-21 `MasterSeed`. Opaque bytes.
const ACCOUNT_PATH: &[u8] = b"m/0";
pub(super) const IDENTITY: &[u8] = b"test";
pub(super) const ASSET_ID: AssetId = 1;
pub(super) const COUNTER: NullifierSkGenCounter = 0;

/// The account path bytes the app's handlers take.
pub(super) fn path_bytes() -> Vec<u8> {
    ACCOUNT_PATH.to_vec()
}

/// Stand-in device keypair for the in-process fallback. See the module doc: this does NOT match
/// what a real Ledger derives for `ACCOUNT_PATH`.
fn device_keys() -> AuthSigningKeys {
    AuthSigningKeys::from_master_seed(
        &BPMasterSeed::new(b"ledger-test-seed".repeat(2)),
        b"",
        0,
        &DeviceGenerators::new().unwrap(),
    )
    .unwrap()
}

fn account_pubkeys(keys: &AuthSigningKeys) -> (PallasA, PallasA) {
    let g = dart_gens();
    let pk_aff = g.sig_key_gen().mul(keys.sk_aff).into_affine();
    let pk_enc = g.enc_key_gen().mul(keys.sk_enc).into_affine();
    (pk_aff, pk_enc)
}

/// The `(pk_aff, pk_enc)` the host builds its request around: the real device's pubkeys when
/// `LEDGER_PUBKEYS_HEX` is set (64 bytes = `pk_aff.as_bytes() || pk_enc.as_bytes()`, exactly what
/// `GetPubkey`/INS 5 returns for `ACCOUNT_PATH` — send `getpubkey_apdu()`), else the in-process
/// fallback keypair. A real device's keys are not derivable from the path alone, so testing against
/// a real device or emulator needs its pubkeys queried first.
fn device_pubkeys(keys: &AuthSigningKeys) -> (PallasA, PallasA) {
    match std::env::var("LEDGER_PUBKEYS_HEX") {
        Ok(h) => {
            let mut bytes = hex::decode(strip_ws(&h)).expect("valid hex");
            if bytes.len() == 66 && bytes.ends_with(&[0x90, 0x00]) {
                bytes.truncate(64); // raw GetPubkey response APDU (64 bytes + status word)
            }
            assert_eq!(bytes.len(), 64, "expected pk_aff(32) || pk_enc(32)");
            let pk_aff_ca = CompressedAffine::from_str(&hex::encode(&bytes[..32])).unwrap();
            let pk_enc_ca = CompressedAffine::from_str(&hex::encode(&bytes[32..])).unwrap();
            let pk_aff = PallasA::try_from(&pk_aff_ca).unwrap();
            let pk_enc = PallasA::try_from(&pk_enc_ca).unwrap();
            (pk_aff, pk_enc)
        }
        Err(_) => account_pubkeys(keys),
    }
}

/// The APDU data the Ledger expects: `[path_len][path bytes][SCALE(request)]`.
pub(super) fn apdu_data(request_bytes: &[u8]) -> Vec<u8> {
    let path = path_bytes();
    let mut data = Vec::with_capacity(1 + path.len() + request_bytes.len());
    data.push(path.len() as u8);
    data.extend_from_slice(&path);
    data.extend_from_slice(request_bytes);
    data
}

const CLA: u8 = 0xE0;
pub(super) const INS_GET_PUBKEY: u8 = 5;
pub(super) const INS_KEY_REG: u8 = 7;
pub(super) const INS_ASSET_REG: u8 = 8;
pub(super) const INS_AFFIRM: u8 = 9;
pub(super) const INS_MINT: u8 = 11;
pub(super) const INS_GET_RESPONSE_CHUNK: u8 = 12;
/// P1 = 0 for a non-fee account, 1 for a fee account.
pub(super) const INS_ACCOUNT_RANDOMNESS: u8 = 13;
pub(super) const INS_FEE_REG: u8 = 14;
pub(super) const INS_FEE_TOPUP: u8 = 15;
pub(super) const INS_FEE_PAYMENT: u8 = 16;
const P2_MORE: u8 = 0x80;

/// Wrap `data` in a full short APDU: `CLA INS P1 P2 Lc <data>`.
fn full_apdu_p(ins: u8, p1: u8, p2: u8, data: &[u8]) -> Vec<u8> {
    assert!(data.len() <= 255, "data exceeds one short APDU");
    let mut apdu = Vec::with_capacity(5 + data.len());
    apdu.extend_from_slice(&[CLA, ins, p1, p2, data.len() as u8]);
    apdu.extend_from_slice(data);
    apdu
}

/// Full single-APDU (P1=P2=0) ready to paste into `ledgercomm-send`.
pub(super) fn full_apdu(ins: u8, data: &[u8]) -> String {
    hex::encode(full_apdu_p(ins, 0, 0, data))
}

/// Full single-APDU with `p1` (P2=0).
pub(super) fn full_apdu_with_p1(ins: u8, p1: u8, data: &[u8]) -> String {
    hex::encode(full_apdu_p(ins, p1, 0, data))
}

/// The `GetPubkey` (INS 5) APDU — returns the device's real `(pk_aff, pk_enc)` for the path. Its
/// data is the bare path (no `[path_len]` wrapper), unlike the proof handlers.
pub(super) fn getpubkey_apdu() -> String {
    full_apdu(INS_GET_PUBKEY, &path_bytes())
}

/// The chunked affirmation APDU sequence: chunk 0 = path (P2 MORE), chunks 1..N = the request
/// split at 255 bytes (last chunk P2 LAST). Paste each in order.
pub(super) fn affirm_apdus(request_bytes: &[u8]) -> Vec<String> {
    chunked_apdus(INS_AFFIRM, request_bytes)
}

/// The chunked APDU sequence for `ins`, laid out as in `affirm_apdus`.
pub(super) fn chunked_apdus(ins: u8, request_bytes: &[u8]) -> Vec<String> {
    let mut apdus = vec![hex::encode(full_apdu_p(ins, 0, P2_MORE, &path_bytes()))];
    let slices: Vec<&[u8]> = request_bytes.chunks(255).collect();
    for (i, s) in slices.iter().enumerate() {
        let p2 = if i + 1 < slices.len() { P2_MORE } else { 0 };
        apdus.push(hex::encode(full_apdu_p(ins, (i + 1) as u8, p2, s)));
    }
    apdus
}

/// Remove all whitespace (`ledgercomm-send` prints a space before the status word).
fn strip_ws(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

/// APDU-capture mode: real pubkeys injected but no response fixture yet. The in-process fallback
/// signs with the stand-in keys, which don't match the injected pubkeys, so the host verify would
/// fail — print the APDU and stop instead. Only affects the pubkey-dependent flows.
fn apdu_capture_mode(response_env: &str) -> bool {
    std::env::var("LEDGER_PUBKEYS_HEX").is_ok() && std::env::var(response_env).is_err()
}

/// Reassemble a device response from its response APDU(s), each framed `[len: u8][payload]` with an
/// optional trailing `9000` status word. A single-APDU response is one hex string; a chunked
/// (affirmation) response is its response APDUs comma-separated, in order. Accepts the raw string
/// printed by `ledgercomm-send` — the `[len]` prefix disambiguates whether the `9000` is present.
fn device_response_bytes(raw: &str) -> Vec<u8> {
    raw.split(',')
        .flat_map(|seg| {
            let bytes = hex::decode(strip_ws(seg)).expect("valid hex");
            assert!(!bytes.is_empty(), "empty response APDU");
            let len = bytes[0] as usize;
            let rest = &bytes[1..];
            if rest.len() == len + 2 {
                assert_eq!(&rest[len..], [0x90, 0x00], "status word not 9000");
            } else {
                assert_eq!(rest.len(), len, "length-prefix mismatch");
            }
            rest[..len].to_vec()
        })
        .collect()
}

// TODO: Refactor to make a CLI instead of tests

#[test]
fn ledger_key_registration_roundtrip() {
    let keys = device_keys();
    let g = dart_gens();

    // Key registration is self-contained on the device — no host protocol, no tree.
    let request = KeyRegistrationDeviceRequest {
        identity: IDENTITY.to_vec(),
    };
    let data = apdu_data(&request.encode());
    let response = match std::env::var("LEDGER_KEY_REG_RESPONSE_HEX") {
        Ok(h) => KeyRegistrationDeviceResponse::decode(&mut &device_response_bytes(&h)[..])
            .expect("decodes as KeyRegistrationDeviceResponse"),
        Err(_) => {
            let mut dev_rng = StdRng::seed_from_u64(1);
            create_key_registration_auth_proof(
                &mut dev_rng,
                &keys,
                IDENTITY,
                &DeviceGenerators::new().unwrap(),
            )
            .unwrap()
        }
    };

    println!("KEY_REG_APDU_HEX  = {}", hex::encode(&data));
    println!("KEY_REG_APDU_FULL = {}", full_apdu(INS_KEY_REG, &data));
    println!("KEY_REG_RESPONSE_HEX = {}", hex::encode(response.encode()));

    // Host verifies the InvestorKeyRegProof directly against the returned account pubkeys.
    let pub_keys: Vec<(PallasA, PallasA)> = response
        .accounts
        .iter()
        .map(|(a, e)| (PallasA::try_from(a).unwrap(), PallasA::try_from(e).unwrap()))
        .collect();
    let proof = response.inner.decode().unwrap();
    proof
        .verify(pub_keys, IDENTITY, g.sig_key_gen(), g.enc_key_gen())
        .unwrap();
}

#[test]
fn ledger_account_asset_registration_roundtrip() {
    let mut rng = StdRng::seed_from_u64(0);
    let keys = device_keys();
    let (pk_aff, pk_enc) = device_pubkeys(&keys);

    // Host builds the request.
    let (account_state, rho) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    let (protocol, request) =
        AccountRegHostProtocol::init(&mut rng, &account_state, rho, COUNTER, IDENTITY, None)
            .unwrap();

    let data = apdu_data(&request.encode());
    println!("GETPUBKEY_APDU_FULL = {}", getpubkey_apdu());
    println!("ASSET_REG_APDU_HEX  = {}", hex::encode(&data));
    println!("ASSET_REG_APDU_FULL = {}", full_apdu(INS_ASSET_REG, &data));
    if apdu_capture_mode("LEDGER_ASSET_REG_RESPONSE_HEX") {
        println!(
            "APDU-capture mode: send ASSET_REG_APDU_FULL, then re-run with LEDGER_ASSET_REG_RESPONSE_HEX"
        );
        return;
    }

    // Device produces the response: captured fixture if provided, else in-process.
    let response = match std::env::var("LEDGER_ASSET_REG_RESPONSE_HEX") {
        Ok(h) => AccountRegistrationDeviceResponse::decode(&mut &device_response_bytes(&h)[..])
            .expect("decodes as AccountRegistrationDeviceResponse"),
        Err(_) => {
            let mut dev_rng = StdRng::seed_from_u64(1);
            create_registration_auth_proof(
                &mut dev_rng,
                &keys,
                &request,
                &DeviceGenerators::new().unwrap(),
            )
            .unwrap()
        }
    };
    println!(
        "ASSET_REG_RESPONSE_HEX = {}",
        hex::encode(response.encode())
    );

    // Host completes and verifies.
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
fn ledger_mint_roundtrip() {
    let mut rng = StdRng::seed_from_u64(0);
    let keys = device_keys();
    let (pk_aff, pk_enc) = device_pubkeys(&keys);

    let (mut account_state, _rho) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();

    // Single-leaf account tree for the mint's host protocol.
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
        IDENTITY,
        &account_tree,
    )
    .unwrap();

    let data = apdu_data(&request.encode());
    println!("GETPUBKEY_APDU_FULL = {}", getpubkey_apdu());
    println!("MINT_APDU_HEX  = {}", hex::encode(&data));
    println!("MINT_APDU_FULL = {}", full_apdu(INS_MINT, &data));
    if apdu_capture_mode("LEDGER_MINT_RESPONSE_HEX") {
        println!(
            "APDU-capture mode: send MINT_APDU_FULL, then re-run with LEDGER_MINT_RESPONSE_HEX"
        );
        return;
    }

    let response = match std::env::var("LEDGER_MINT_RESPONSE_HEX") {
        Ok(h) => AssetMintingDeviceResponse::decode(&mut &device_response_bytes(&h)[..])
            .expect("decodes as AssetMintingDeviceResponse"),
        Err(_) => {
            let mut dev_rng = StdRng::seed_from_u64(1);
            create_mint_auth_proof(
                &mut dev_rng,
                &keys,
                &request,
                &DeviceGenerators::new().unwrap(),
            )
            .unwrap()
        }
    };
    println!("MINT_RESPONSE_HEX = {}", hex::encode(response.encode()));

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

/// Encrypted leg + single-leaf tree containing `state_leaf` (the affirming account's leaf).
pub(super) fn affirm_leg_and_tree(
    rng: &mut StdRng,
    sender_enc: EncryptionPublicKey,
    receiver_enc: EncryptionPublicKey,
    amount: Balance,
    state_leaf: AccountStateCommitment,
) -> (
    LegEncrypted,
    LegRef,
    ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
) {
    let leg = Leg::new(sender_enc, receiver_enc, ASSET_ID, amount).unwrap();
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

/// The affirmation device response — captured fixture via `env`, else in-process. Prints the
/// paste-ready request/response APDUs. Returns `None` in APDU-capture mode (caller should return).
/// The device side is identical for sender and receiver affirmation; only the host protocol differs.
fn affirm_device_response(
    request: &AffirmationDeviceRequest,
    keys: &AuthSigningKeys,
    env: &str,
) -> Option<AffirmationDeviceResponse> {
    for (i, apdu) in affirm_apdus(&request.encode()).iter().enumerate() {
        println!("AFFIRM_APDU_FULL[{i}] = {apdu}");
    }
    println!(
        "GET_RESPONSE_CHUNK_APDU = {}",
        full_apdu(INS_GET_RESPONSE_CHUNK, &[])
    );
    if apdu_capture_mode(env) {
        println!(
            "APDU-capture mode: send the AFFIRM_APDU_FULL chunks (the last chunk returns slice 0), then send GET_RESPONSE_CHUNK_APDU until a slice has len < 255; comma-join all slices into {env}"
        );
        return None;
    }

    let response = match std::env::var(env) {
        Ok(h) => AffirmationDeviceResponse::decode(&mut &device_response_bytes(&h)[..])
            .expect("decodes as AffirmationDeviceResponse"),
        Err(_) => {
            let mut dev_rng = StdRng::seed_from_u64(1);
            let g = DeviceGenerators::new().unwrap();
            create_affirmation_auth_proof(&mut dev_rng, keys, request, &g).unwrap()
        }
    };
    println!("AFFIRM_RESPONSE_HEX = {}", hex::encode(response.encode()));
    Some(response)
}

#[test]
fn ledger_affirmation_roundtrip() {
    let mut rng = StdRng::seed_from_u64(0);
    let keys = device_keys();
    let (pk_aff, pk_enc) = device_pubkeys(&keys);

    // Device is the sender: it holds a minted balance and sends `send_amount`.
    let mint_amount = 1000;
    let send_amount = 300;
    let (mut sender_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    sender_state.current_state.balance = mint_amount;
    let leaf = sender_state.current_commitment().unwrap();

    let counterparty = AccountKeys::rand(&mut rng).unwrap();
    let (leg_enc, leg_ref, account_tree) = affirm_leg_and_tree(
        &mut rng,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        counterparty.enc.public,
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

    let Some(response) = affirm_device_response(&request, &keys, "LEDGER_AFFIRM_RESPONSE_HEX")
    else {
        return;
    };

    let affirm_proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    affirm_proof
        .verify(&leg_enc, &account_tree.root().unwrap(), &mut rng)
        .unwrap();
}

#[test]
fn ledger_receiver_affirmation_roundtrip() {
    let mut rng = StdRng::seed_from_u64(0);
    let keys = device_keys();
    let (pk_aff, pk_enc) = device_pubkeys(&keys);

    // Device is the receiver: a fresh account (no balance change proven at affirm time).
    let receive_amount = 300;
    let (mut receiver_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    let leaf = receiver_state.current_commitment().unwrap();

    let counterparty = AccountKeys::rand(&mut rng).unwrap();
    let (leg_enc, leg_ref, account_tree) = affirm_leg_and_tree(
        &mut rng,
        counterparty.enc.public,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        receive_amount,
        leaf,
    );

    let (protocol, request) = ReceiverAffirmationHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut receiver_state,
        &leg_ref,
        &leg_enc,
        receive_amount,
        &account_tree,
    )
    .unwrap();

    let Some(response) = affirm_device_response(&request, &keys, "LEDGER_RECV_AFFIRM_RESPONSE_HEX")
    else {
        return;
    };

    let affirm_proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    affirm_proof
        .verify(&leg_enc, &account_tree.root().unwrap(), &mut rng)
        .unwrap();
}

#[test]
fn ledger_receiver_claim_roundtrip() {
    let mut rng = StdRng::seed_from_u64(0);
    let keys = device_keys();
    let (pk_aff, pk_enc) = device_pubkeys(&keys);

    let claim_amount = 300;
    let (mut receiver_state, _) =
        account_state_from_pubkeys(&mut rng, pk_aff, pk_enc, ASSET_ID, COUNTER, IDENTITY).unwrap();
    receiver_state.current_state.counter = 1;
    let leaf = receiver_state.current_commitment().unwrap();

    let counterparty = AccountKeys::rand(&mut rng).unwrap();
    let (leg_enc, leg_ref, account_tree) = affirm_leg_and_tree(
        &mut rng,
        counterparty.enc.public,
        EncryptionPublicKey::from_affine(pk_enc).unwrap(),
        claim_amount,
        leaf,
    );

    let (protocol, request) = ReceiverClaimHostProtocol::<AccountTreeConfig>::init(
        &mut rng,
        &mut receiver_state,
        &leg_ref,
        &leg_enc,
        claim_amount,
        &account_tree,
    )
    .unwrap();

    let Some(response) = affirm_device_response(&request, &keys, "LEDGER_CLAIM_RESPONSE_HEX")
    else {
        return;
    };

    let proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    proof
        .verify(&leg_enc, &account_tree.root().unwrap(), &mut rng)
        .unwrap();
}

#[test]
fn ledger_sender_counter_update_roundtrip() {
    let mut rng = StdRng::seed_from_u64(0);
    let keys = device_keys();
    let (pk_aff, pk_enc) = device_pubkeys(&keys);

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

    let Some(response) =
        affirm_device_response(&request, &keys, "LEDGER_SENDER_COUNTER_UPDATE_RESPONSE_HEX")
    else {
        return;
    };

    let proof = protocol.finish::<_, ()>(&mut rng, &response).unwrap();
    proof
        .verify(&leg_enc, &account_tree.root().unwrap(), &mut rng)
        .unwrap();
}
