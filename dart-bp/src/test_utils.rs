/// Assert that a `Result` is `Err`, that the error matches a given pattern, and optionally
/// that the error message contains a given string. These are just for testing.
macro_rules! assert_err {
    ($result:expr, $pattern:pat $(,)?) => {
        match &$result {
            Err(e) => {
                assert!(
                    matches!(e, $pattern),
                    "expected error matching `{}` but got: {:?}",
                    stringify!($pattern),
                    e
                );
            }
            Ok(_) => panic!("expected Err but got Ok"),
        }
    };
    ($result:expr, $pattern:pat, $msg_substr:expr $(,)?) => {
        match &$result {
            Err(e) => {
                assert!(
                    matches!(e, $pattern),
                    "expected error matching `{}` but got: {:?}",
                    stringify!($pattern),
                    e
                );
                let msg = format!("{}", e);
                assert!(
                    msg.contains($msg_substr),
                    "error message {:?} does not contain {:?}",
                    msg,
                    $msg_substr
                );
            }
            Ok(_) => panic!("expected Err but got Ok"),
        }
    };
}

use crate::leg::{
    AssetIdEncryption, EphemeralPublicKey, Leg, LegEncCoreAndEphKeys, LegEncryption,
    LegEncryptionCore, LegEncryptionRandomness, ReceiverEphemeralPublicKey,
    SenderEphemeralPublicKey,
};
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_pallas::{Affine as PallasA, Fr as PallasFr};
use ark_std::UniformRand;
use ark_std::{vec, vec::Vec};
use polymesh_dart_common::{AssetId, Balance};
use rand_core::CryptoRngCore;

/// Leg encryption with sender point `p_s`, receiver point `p_r`, full visibility, auditor keys
/// `auditors` and no mediators. The asset-id is revealed when `rand.r4` is `None`.
pub(crate) fn leg_encryption_with_party_points(
    p_s: PallasA,
    p_r: PallasA,
    auditors: &[PallasA],
    amount: Balance,
    asset_id: AssetId,
    rand: &LegEncryptionRandomness<PallasFr>,
    enc_key_gen: PallasA,
    enc_gen: PallasA,
) -> LegEncryption<PallasA> {
    let g = enc_key_gen;
    let (r1, r2, r3, r4, r5, r6) = (rand.r1, rand.r2, rand.r3, rand.r4, rand.r5, rand.r6);
    let eph = |pk: PallasA| EphemeralPublicKey {
        r1: (pk * r1).into_affine(),
        r2: (pk * r2).into_affine(),
        r3: (pk * r3).into_affine(),
        r4: r4.map(|r| (pk * r).into_affine()),
    };
    let eph_s = eph(p_s);
    let eph_r = eph(p_r);
    LegEncryption {
        leg_enc_core_and_eph_keys: LegEncCoreAndEphKeys {
            core: LegEncryptionCore {
                ct_s: (g * r1 + p_s).into_affine(),
                ct_r: (g * r2 + p_r).into_affine(),
                ct_amount: (g * r3 + enc_gen * PallasFr::from(amount)).into_affine(),
                ct_asset_id: match r4 {
                    Some(r4) => AssetIdEncryption::Ciphertext(
                        (g * r4 + enc_gen * PallasFr::from(asset_id)).into_affine(),
                    ),
                    None => AssetIdEncryption::Revealed(asset_id),
                },
                ct_s_prime: (g * r5).into_affine(),
                ct_r_prime: (g * r6).into_affine(),
            },
            eph_pk_s: SenderEphemeralPublicKey {
                r1: eph_s.r1,
                r2: Some(eph_s.r2),
                r3: eph_s.r3,
                r4: eph_s.r4,
                r5: (p_s * r5).into_affine(),
            },
            eph_pk_r: ReceiverEphemeralPublicKey {
                r1: Some(eph_r.r1),
                r2: eph_r.r2,
                r3: eph_r.r3,
                r4: eph_r.r4,
                r6: (p_r * r6).into_affine(),
            },
        },
        eph_pk_enc_keys: auditors.iter().map(|pk| eph(*pk)).collect(),
        eph_pk_public_enc_keys: vec![],
        mediators: r4.map(|_| vec![]),
    }
}

/// Leg whose sender (resp. receiver) point is `P = ek + enc_gen * (sk_enc * delta)` with
/// `ek = enc_key_gen * sk_enc`, and whose randomness `r_1` (resp. `r_2`) is `sk_enc`. `sk_enc` opens
/// the participant ciphertext to `ek`, the amount to `opened_amount` and the asset-id to
/// `opened_asset_id`, while the leg encrypts `leg_amount` of `leg_asset_id` for every other reader.
/// `opened_asset_id` is ignored when `reveal_asset_id`. `other_point` is the other party's point.
pub(crate) fn crafted_party_point_leg<R: CryptoRngCore>(
    rng: &mut R,
    is_sender: bool,
    sk_enc: PallasFr,
    other_point: PallasA,
    auditors: Vec<PallasA>,
    leg_amount: Balance,
    leg_asset_id: AssetId,
    opened_amount: Balance,
    opened_asset_id: AssetId,
    reveal_asset_id: bool,
    enc_key_gen: PallasA,
    enc_gen: PallasA,
) -> (
    Leg<PallasA>,
    LegEncryption<PallasA>,
    LegEncryptionRandomness<PallasFr>,
) {
    let ek = enc_key_gen * sk_enc;
    let r3 = PallasFr::rand(rng);
    let delta =
        (PallasFr::from(leg_amount) - PallasFr::from(opened_amount)) * r3.inverse().unwrap();
    let r4 = (!reveal_asset_id).then(|| {
        (PallasFr::from(leg_asset_id) - PallasFr::from(opened_asset_id)) * delta.inverse().unwrap()
    });
    let (r1, r2) = if is_sender {
        (sk_enc, PallasFr::rand(rng))
    } else {
        (PallasFr::rand(rng), sk_enc)
    };
    let rand = LegEncryptionRandomness {
        r1,
        r2,
        r3,
        r4,
        r5: PallasFr::rand(rng),
        r6: PallasFr::rand(rng),
        r_meds: r4.map(|_| vec![]),
    };
    let p = (ek + enc_gen * (sk_enc * delta)).into_affine();
    let (p_s, p_r) = if is_sender {
        (p, other_point)
    } else {
        (other_point, p)
    };
    let leg_enc = leg_encryption_with_party_points(
        p_s,
        p_r,
        &auditors,
        leg_amount,
        leg_asset_id,
        &rand,
        enc_key_gen,
        enc_gen,
    );
    let leg = Leg::new(p_s, p_r, leg_amount, leg_asset_id, auditors, vec![], vec![]).unwrap();
    (leg, leg_enc, rand)
}
