use std::collections::BTreeMap;

use ark_ec::AffineRepr;
use ark_ff::One;
use ark_serialize::CanonicalSerialize;
use codec::{Decode, Encode, MaxEncodedLen};
use polymesh_bat::ark_bn254::Fq2;
use polymesh_dart::*;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;

struct Issuer {
    id: BatIssuerKeyId,
    keys: BatIssuerKeys,
}

/// A registry of `n` issuer keys.
fn registry(n: u32) -> (Vec<Issuer>, BTreeMap<BatIssuerKeyId, BatIssuerPublicKey>) {
    let issuers: Vec<Issuer> = (0..n)
        .map(|id| Issuer {
            id,
            keys: BatIssuerKeys::new_with_seed(&id.to_le_bytes()),
        })
        .collect();
    let lookup = issuers
        .iter()
        .map(|i| {
            let pk = i.keys.public_key().unwrap();
            pk.validate().unwrap();
            (i.id, pk)
        })
        .collect();
    (issuers, lookup)
}

/// Buys `count` tokens from `issuer`, checking both on-chain messages as the pallet would.
fn buy(
    rng: &mut ChaCha20Rng,
    issuer: &Issuer,
    lookup: &BTreeMap<BatIssuerKeyId, BatIssuerPublicKey>,
    count: u32,
) -> (Vec<BatPreToken>, BatRefundKey, BatOnChainIssuanceRequest) {
    let (session, request) = BatClientSession::new(rng, issuer.id, count).unwrap();
    let (issuer_session, response) = issuer.keys.sign(rng, issuer.id, &request).unwrap();
    let execute = session.on_chain_issue_request(rng, &response).unwrap();
    execute.verify::<()>().unwrap();

    let reveal = issuer_session.reveal(&execute).unwrap();
    reveal
        .verify(&lookup[&execute.issuer], &execute.commitment_to_sig_mask)
        .unwrap();

    let (tokens, refund_key) = session.unmask(&response, &reveal).unwrap();
    (tokens, refund_key, execute)
}

#[test]
fn buy_pay_refund() {
    let mut rng = ChaCha20Rng::seed_from_u64(0);
    let (issuers, lookup) = registry(3);
    let (mut a, refund_a, execute_a) = buy(&mut rng, &issuers[0], &lookup, 4);
    let (b, _, _) = buy(&mut rng, &issuers[2], &lookup, 2);

    let spent: Vec<BatPreToken> = a.drain(..2).chain(b).collect();
    let batch =
        BatFeePaymentWithBatchedProofs::<()>::new(&mut rng, &spent, BatchedProofs::new()).unwrap();
    let decoded = BatFeePaymentWithBatchedProofs::<()>::decode(&mut &batch.encode()[..]).unwrap();
    assert_eq!(decoded, batch);

    let spend = decoded.verify_fee_payment(&mut rng, &lookup).unwrap();
    assert_eq!(
        spend.nullifiers,
        spent
            .iter()
            .map(|t| t.nullifier().unwrap())
            .collect::<Vec<_>>()
    );
    assert_eq!(spend.tokens_per_issuer, BTreeMap::from([(0, 2), (2, 2)]));

    let refund = BatRefundRequest::<()>::new(&mut rng, &refund_a, &a).unwrap();
    let refund = BatRefundRequest::<()>::decode(&mut &refund.encode()[..]).unwrap();
    let nullifiers = refund
        .verify(&mut rng, &lookup[&0], &execute_a.pk_ref)
        .unwrap();
    assert_eq!(
        nullifiers,
        a.iter().map(|t| t.nullifier().unwrap()).collect::<Vec<_>>()
    );

    // Refund checked against another issuer's key.
    assert!(matches!(
        refund.verify(&mut rng, &lookup[&1], &execute_a.pk_ref),
        Err(Error::BatError(_))
    ));
}

#[test]
fn payment_rejections() {
    let mut rng = ChaCha20Rng::seed_from_u64(1);
    let (issuers, mut lookup) = registry(2);
    let (tokens, _, _) = buy(&mut rng, &issuers[1], &lookup, 2);
    let batch =
        BatFeePaymentWithBatchedProofs::<()>::new(&mut rng, &tokens, BatchedProofs::new()).unwrap();

    // Signed for one batch, submitted with another.
    let other_ctx = BatchedProofs::<()>::new().ctx(b"other");
    assert!(matches!(
        batch.fee_payment.verify(&mut rng, &other_ctx.0, &lookup),
        Err(Error::BatError(polymesh_bat::Error::InvalidSignature))
    ));

    // Tokens attributed to another issuer key.
    let mut relabelled = batch.clone();
    relabelled.fee_payment.tokens = relabelled
        .fee_payment
        .tokens
        .iter()
        .map(|(_, t)| (0, *t))
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
    assert!(matches!(
        relabelled.verify_fee_payment(&mut rng, &lookup),
        Err(Error::BatError(polymesh_bat::Error::InvalidIssuerSignature))
    ));

    lookup.remove(&1);
    assert!(matches!(
        batch.verify_fee_payment(&mut rng, &lookup),
        Err(Error::UnknownBatIssuer(1))
    ));
}

#[test]
fn payment_issuer_key_limit() {
    let mut rng = ChaCha20Rng::seed_from_u64(2);
    let n = MAX_BAT_ISSUER_KEYS_PER_PAYMENT + 1;
    let (issuers, lookup) = registry(n);
    let tokens: Vec<BatPreToken> = issuers
        .iter()
        .flat_map(|i| buy(&mut rng, i, &lookup, 1).0)
        .collect();
    let batch =
        BatFeePaymentWithBatchedProofs::<()>::new(&mut rng, &tokens, BatchedProofs::new()).unwrap();
    assert!(matches!(
        batch.verify_fee_payment(&mut rng, &lookup),
        Err(Error::TooManyBatIssuerKeys)
    ));
}

#[test]
fn issuance_rejections() {
    let mut rng = ChaCha20Rng::seed_from_u64(3);
    let (issuers, _) = registry(2);
    let (session, request) = BatClientSession::new(&mut rng, 0, 3).unwrap();
    let (issuer_session, response) = issuers[0].keys.sign(&mut rng, 0, &request).unwrap();
    let execute = session.on_chain_issue_request(&mut rng, &response).unwrap();

    // The client names another issuer key or pays for fewer tokens than were signed.
    let mut other_issuer = execute;
    other_issuer.issuer = 1;
    assert!(issuer_session.clone().reveal(&other_issuer).is_err());
    let mut underpaid = execute;
    underpaid.count = 2;
    assert!(issuer_session.clone().reveal(&underpaid).is_err());
    assert!(issuer_session.reveal(&execute).is_ok());

    let mut too_many = execute;
    too_many.count = MAX_BAT_TOKENS_PER_SESSION + 1;
    assert!(too_many.verify::<()>().is_err());

    let identity = BatIssuerPublicKey::from_affine(BatG2::zero()).unwrap();
    assert!(identity.validate().is_err());
}

#[test]
fn encodings() {
    assert_eq!(BatG1::generator().compressed_size(), BAT_G1_SIZE);
    assert_eq!(BatG2::generator().compressed_size(), BAT_G2_SIZE);
    assert_eq!(BatToken::max_encoded_len(), 32 + BAT_G1_SIZE);
    assert_eq!(
        BatOnChainIssuanceRequest::max_encoded_len(),
        32 + 4 + 32 + BAT_G2_SIZE + 4
    );

    // An `x` coordinate past the modulus, and a point outside the prime-order subgroup of `G2`.
    let mut bytes = [0xffu8; BAT_G2_SIZE];
    bytes[BAT_G2_SIZE - 1] &= 0x3f;
    let key = BatIssuerPublicKey::decode(&mut &bytes[..]).unwrap();
    assert!(key.get_affine().is_err());

    let mut x = Fq2::one();
    let off_subgroup = (0..100)
        .find_map(|_| {
            x += Fq2::one();
            BatG2::get_point_from_x_unchecked(x, false)
                .filter(|p| !p.is_in_correct_subgroup_assuming_on_curve())
        })
        .unwrap();
    let mut bytes = [0u8; BAT_G2_SIZE];
    off_subgroup.serialize_compressed(&mut bytes[..]).unwrap();
    let key = BatIssuerPublicKey::decode(&mut &bytes[..]).unwrap();
    assert!(key.get_affine().is_err());
}
