use test_log::test;

use polymesh_dart::*;

mod common;

#[test]
fn test_account_key_reg() {
    let mut rng = rand::thread_rng();

    let account_keys = AccountKeys::rand(&mut rng).unwrap();

    eprintln!("Public keys: {:?}", account_keys.public_keys());
    let _proof: AccountRegistrationProof =
        AccountRegistrationProof::new(&mut rng, &[account_keys], b"DID").unwrap();
}
