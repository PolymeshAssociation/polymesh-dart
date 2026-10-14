//! Batched leg scanning at the wrapper boundary.

use polymesh_dart::*;
use polymesh_dart_bp::leg::{LegEncConfig, PartyVisibility};
use rand::{CryptoRng, RngCore};

fn encrypt_leg(
    rng: &mut (impl RngCore + CryptoRng),
    sender: EncryptionPublicKey,
    receiver: EncryptionPublicKey,
    asset_id: AssetId,
    amount: Balance,
    visibility: PartyVisibility,
    reveal_asset_id: bool,
) -> LegEncrypted {
    let cfg = LegEncConfig {
        visibility,
        reveal_asset_id,
    };
    let leg = Leg::new(sender, receiver, asset_id, amount).unwrap();
    let (_leg, leg_enc, _r) = leg.encrypt(rng, cfg, vec![], vec![], vec![]).unwrap();
    leg_enc
}

#[test]
fn try_decrypt_does_not_decrypt_amount_on_foreign_legs() {
    let mut rng = rand::thread_rng();
    let a_keys = AccountKeys::rand(&mut rng).unwrap();
    let b_keys = AccountKeys::rand(&mut rng).unwrap();
    let c_keys = AccountKeys::rand(&mut rng).unwrap();
    let (a, b, c) = (
        a_keys.public_keys(),
        b_keys.public_keys(),
        c_keys.public_keys(),
    );

    let n = 16usize;
    let mut legs = Vec::with_capacity(n);
    for i in 0..n {
        // Every asset-id revealed, and A is the receiver or absent, never the sender.
        let (sender, receiver) = if i % 2 == 0 {
            (b.enc, a.enc)
        } else {
            (b.enc, c.enc)
        };
        legs.push(encrypt_leg(
            &mut rng,
            sender,
            receiver,
            7 as AssetId,
            1000 + i as Balance,
            PartyVisibility::FullVisibility,
            true,
        ));
    }

    let found = legs
        .iter()
        .filter_map(|leg| leg.try_decrypt(&a_keys))
        .count();

    assert_eq!(found, n / 2);
}

#[test]
fn is_party_identifies_sender_and_receiver() {
    let mut rng = rand::thread_rng();
    let a_keys = AccountKeys::rand(&mut rng).unwrap();
    let b_keys = AccountKeys::rand(&mut rng).unwrap();
    let c_keys = AccountKeys::rand(&mut rng).unwrap();
    let (a, b) = (a_keys.public_keys(), b_keys.public_keys());
    let no_auditor = None::<fn(&AssetId) -> Option<Balance>>;

    for reveal_asset_id in [false, true] {
        let leg = encrypt_leg(
            &mut rng,
            a.enc,
            b.enc,
            3,
            500,
            PartyVisibility::FullVisibility,
            reveal_asset_id,
        );
        for (keys, expected) in [
            (&a_keys, Some(LegRole::sender())),
            (&b_keys, Some(LegRole::receiver())),
            (&c_keys, None),
        ] {
            let role = leg.is_party(&keys.enc, true, None, no_auditor).unwrap();
            assert_eq!(role, expected);
            assert_eq!(role, leg.try_decrypt(keys).map(|(_, role)| role));
        }
    }
}
