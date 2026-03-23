use std::time::Instant;
use test_log::test;

use polymesh_dart::*;

mod common;
use common::*;

#[test]
fn test_account_key_reg() {
    let mut rng = rand::thread_rng();

    let account_keys = AccountKeys::rand(&mut rng).unwrap();

    let _proof: AccountRegistrationProof =
        AccountRegistrationProof::new(&mut rng, &[account_keys], b"DID").unwrap();
}

#[test]
fn test_account_asset_reg() {
    let mut rng = rand::thread_rng();

    let account_keys = AccountKeys::rand(&mut rng).unwrap();

    let params = get_pallas_single_layer_params();

    let (_proof, _asset_state) =
        AccountAssetRegistrationProof::new_min(&mut rng, &account_keys, 0, 0, b"DID", &params)
            .unwrap();
}
