//! Batched leg scanning at the wrapper boundary.

use polymesh_dart::*;
use polymesh_dart_bp::leg::{LegEncConfig, PartyVisibility};
use rand::{CryptoRng, RngCore};
use std::collections::BTreeMap;

const VISIBILITIES: [PartyVisibility; 4] = [
    PartyVisibility::FullVisibility,
    PartyVisibility::NoVisibility,
    PartyVisibility::OnlySenderSeesReceiver,
    PartyVisibility::OnlyReceiverSeesSender,
];

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
fn batch_scan_matches_per_leg_decrypt() {
    let mut rng = rand::thread_rng();
    let sender_keys = AccountKeys::rand(&mut rng).unwrap();
    let sender = sender_keys.public_keys();
    let receiver_keys = AccountKeys::rand(&mut rng).unwrap();
    let receiver = receiver_keys.public_keys();

    let n = 40usize;
    let mut legs = Vec::with_capacity(n);
    let mut expected = Vec::with_capacity(n);
    for i in 0..n {
        let asset_id = (i % 5) as AssetId;
        let amount = 1000 + i as Balance;
        // Alternate ciphertext (hidden) and revealed asset-ids to cover both batch branches.
        legs.push(encrypt_leg(
            &mut rng,
            sender.enc,
            receiver.enc,
            asset_id,
            amount,
            PartyVisibility::FullVisibility,
            i % 2 == 1,
        ));
        expected.push((asset_id, amount));
    }

    for (role, keys) in [
        (LegRole::receiver(), &receiver_keys),
        (LegRole::sender(), &sender_keys),
    ] {
        let per_leg: Vec<(AssetId, Balance)> = legs
            .iter()
            .map(|l| {
                let leg = l.decrypt(role, keys).unwrap();
                (leg.asset_id, leg.amount)
            })
            .collect();

        let scanned = LegEncrypted::scan_values_as_participant(&legs, role, keys).unwrap();

        assert_eq!(
            scanned, per_leg,
            "batch scan disagrees with per-leg decrypt"
        );
        assert_eq!(scanned, expected, "batch scan recovered wrong values");
    }
}

#[test]
fn scan_legs_matches_per_leg_try_decrypt() {
    let mut rng = rand::thread_rng();
    let a_keys = AccountKeys::rand(&mut rng).unwrap();
    let b_keys = AccountKeys::rand(&mut rng).unwrap();
    let c_keys = AccountKeys::rand(&mut rng).unwrap();
    let (a, b, c) = (
        a_keys.public_keys(),
        b_keys.public_keys(),
        c_keys.public_keys(),
    );

    // n legs cycling A->B, B->A, B->C, so A is sender of n/3, receiver of n/3 and absent from n/3.
    // Role identification runs 48 points, above the batch ladder's 32-point threshold.
    let n = 30;
    assert_eq!(n % 3, 0);
    let mut legs = Vec::with_capacity(n);
    let mut expected = BTreeMap::new();
    for i in 0..n {
        let (sender, receiver, role) = match i % 3 {
            0 => (a.enc, b.enc, Some(LegRole::sender())),
            1 => (b.enc, a.enc, Some(LegRole::receiver())),
            _ => (b.enc, c.enc, None),
        };
        let asset_id = (i % 5) as AssetId;
        let amount = 1000 + i as Balance;
        legs.push(encrypt_leg(
            &mut rng,
            sender,
            receiver,
            asset_id,
            amount,
            VISIBILITIES[i % VISIBILITIES.len()],
            i % 2 == 1,
        ));
        if let Some(role) = role {
            expected.insert(i as u32, (role, asset_id, amount));
        }
    }

    let scanned = LegEncrypted::scan_legs(&legs, &a_keys).unwrap();
    assert_eq!(scanned, expected, "scan_legs recovered the wrong legs");

    for (i, leg) in legs.iter().enumerate() {
        let entry = scanned.get(&(i as u32));
        match leg.try_decrypt(&a_keys) {
            Some((decrypted, role)) => {
                assert_eq!(
                    entry,
                    Some(&(role, decrypted.asset_id, decrypted.amount)),
                    "leg {i} disagrees with try_decrypt"
                );
            }
            None => {
                let visible = entry.is_some_and(|(role, ..)| {
                    let vis = VISIBILITIES[i % VISIBILITIES.len()];
                    if role.is_sender() {
                        vis.sender_sees_receiver()
                    } else {
                        vis.receiver_sees_sender()
                    }
                });
                assert!(
                    !visible,
                    "leg {i} was scanned but try_decrypt returned nothing"
                );
            }
        }
    }

    // B is a party to every leg, as sender of 2n/3 and receiver of n/3.
    let scanned_b = LegEncrypted::scan_legs(&legs, &b_keys).unwrap();
    assert_eq!(scanned_b.len(), n);
    assert_eq!(
        scanned_b
            .values()
            .filter(|(role, ..)| role.is_sender())
            .count(),
        2 * (n / 3)
    );

    // An account party to none of the legs gets an empty map, and runs no value decryption.
    let d_keys = AccountKeys::rand(&mut rng).unwrap();
    assert!(LegEncrypted::scan_legs(&legs, &d_keys).unwrap().is_empty());

    // Empty batch.
    assert!(LegEncrypted::scan_legs(&[], &a_keys).unwrap().is_empty());
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
