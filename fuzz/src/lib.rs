//! Panic-freedom harnesses for the DART verifier entry points.
//!
//! The Polymesh worker host falls back to executing proof verification inside the chain runtime
//! when a backend fails, so any panic reachable from a decodable `VerifyDartAssetRequest` becomes
//! a runtime panic during block production. Everything here exists to demonstrate the opposite:
//! for any bytes, decoding + verifying returns `Ok`/`Err` and never panics.
//!
//! * [`request`] mirrors the worker protocol request enum and its verification dispatcher.
//! * [`fixtures`] builds one valid request per variant (the seed corpus).
//! * [`mutate`] has the byte mutators used by the `cargo test` property harness.
//! * `fuzz_targets/` are the `cargo fuzz` (libFuzzer) entry points.

pub mod fixtures;
pub mod mutate;
pub mod request;

pub use fixtures::{Seed, leg_encryptions, seeds};
pub use request::{VerifyDartAssetRequest, decode_and_verify};

use codec::Decode;
use polymesh_dart::curve_tree::{
    AccountTreeConfig, AssetTreeConfig, CompressedCurveTreeRoot, FeeAccountTreeConfig,
};
use polymesh_dart::{
    ACCOUNT_TREE_L, ACCOUNT_TREE_M, ASSET_TREE_L, ASSET_TREE_M, AccountKeys, FEE_ACCOUNT_TREE_L,
    FEE_ACCOUNT_TREE_M, LegEncrypted, MediatorEncryption,
};

/// Exercise every `LegEncrypted` accessor the chain/worker/clients use on bytes that
/// SCALE-decode as a `LegEncrypted`. Returns `None` if the bytes do not decode.
pub fn exercise_leg_encrypted(bytes: &[u8]) -> Option<()> {
    let leg = <LegEncrypted as Decode>::decode(&mut &bytes[..]).ok()?;
    // v0 -> v1 migration path: must return Err or Ok, never panic.
    let _ = leg.from_v0();
    let _ = leg.decode();
    let _ = leg.is_asset_id_revealed();
    let _ = leg.asset_id();
    let _ = leg.mediator_count();
    let _ = leg.get_mediator_ids();
    for i in [0u8, 1, 2, 3, 200, 255] {
        if let Ok(med) = leg.mediator_encryption(i) {
            let _ = med.decode();
        }
    }
    // Client-side decryption helpers on hostile ciphertexts. Only the variants that accept
    // explicit discrete-log bounds are exercised: the unbounded ones (`try_decrypt`, `decrypt`)
    // legitimately scan up to `MAX_BALANCE` (2^48) on a wrong key, which is a client cost by
    // design, not a verifier path.
    let keys = AccountKeys::from_seed("fuzz-decrypt").ok()?;
    const SMALL: u64 = 1 << 10;
    let _ = leg.try_decrypt_with_key(
        &keys.enc,
        None,
        Some(&keys.acct.public),
        Some(SMALL as u32),
        Some(SMALL),
    );
    let _ = leg.try_decrypt_with_key(&keys.enc, Some(0), None, Some(SMALL as u32), Some(SMALL));
    let _ = leg.is_party(
        &keys.enc,
        Some(keys.acct.public),
        Some(SMALL as u32),
        Some(|_: &u32| Some(SMALL)),
    );
    if let Ok(inner) = leg.decode() {
        let sk = &keys.enc.secret.inner().0;
        let enc_gen = polymesh_dart::dart_gens().leg_asset_value_gen();
        let _ = inner.decrypt_as_sender_with_limits(sk, enc_gen, Some(SMALL as u32), Some(SMALL));
        let _ = inner.decrypt_as_receiver_with_limits(sk, enc_gen, Some(SMALL as u32), Some(SMALL));
        for (is_public, idx) in [(false, 0usize), (false, 1), (true, 0), (false, 7)] {
            let _ = inner.decrypt_given_key_with_limits(
                sk,
                is_public,
                idx,
                enc_gen,
                Some(SMALL as u32),
                Some(SMALL),
            );
        }
        for i in 0..inner.num_mediators().min(4) {
            if let Ok(m) = inner.mediator_encryption(i) {
                let _ = m.affirmation_key(sk, 0);
                let _ = m.affirmation_key(sk, 5);
                let _ = m.find_key_index(sk, &keys.acct.public.get_affine().ok()?);
            }
        }
    }
    if let Ok(m) = <MediatorEncryption as Decode>::decode(&mut &bytes[..]) {
        let _ = m.decode();
    }
    Some(())
}

/// Exercise decompression of the three `CompressedCurveTreeRoot` types on decodable bytes.
pub fn exercise_curve_tree_root(bytes: &[u8]) {
    if let Ok(r) =
        CompressedCurveTreeRoot::<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>::decode(
            &mut &bytes[..],
        )
    {
        let _ = r.root_node();
        let _ = r.compressed_inner_node();
        let _ = (r.is_even(), r.height());
    }
    if let Ok(r) = CompressedCurveTreeRoot::<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>::decode(
        &mut &bytes[..],
    ) {
        let _ = r.root_node();
    }
    if let Ok(r) = CompressedCurveTreeRoot::<
        FEE_ACCOUNT_TREE_L,
        FEE_ACCOUNT_TREE_M,
        FeeAccountTreeConfig,
    >::decode(&mut &bytes[..])
    {
        let _ = r.root_node();
    }
}
