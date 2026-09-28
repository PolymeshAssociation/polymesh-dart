use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::One;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    UniformRand,
    rand::{SeedableRng, rngs::StdRng},
};
use dock_crypto_utils::{
    randomized_mult_checker::RandomizedMultCheckerGuard,
    randomized_pairing_check::RandomizedPairingCheckerGuard,
};
use polymesh_bat::{
    Error,
    protocol::{
        ClientSession, CommitmentToSigMask, IssueResponse, IssuerKeypair, IssuerSession,
        OnChainIssuanceRequest, Payment, PreToken, RefundKey, RefundRequest, Reveal, SignatureMask,
        Token,
    },
    signature::{BatchSig, Keypair},
};

type E = polymesh_bat::ark_bn254::Bn254;
type D = ark_pallas::Affine;
type Fr = <E as Pairing>::ScalarField;
type G2 = <E as Pairing>::G2Affine;

const AD: &[u8] = b"test payment";

struct Issued {
    keys: IssuerKeypair<E>,
    pre: Vec<PreToken<E, D>>,
    refund_key: RefundKey<D>,
    request: OnChainIssuanceRequest<E, D>,
    reveal: Reveal<E>,
}

fn issue(rng: &mut StdRng, count: u32) -> Issued {
    let keys = IssuerKeypair::<E>::new(rng);
    let (session, req) = ClientSession::<E, D>::new(rng, count, &D::generator()).unwrap();
    let (issuer_session, resp) = IssuerSession::new(rng, &req, &keys).unwrap();
    resp.verify(rng, &req, None).unwrap();
    let request = OnChainIssuanceRequest::new(&session, &resp);
    request.verify().unwrap();
    let reveal = issuer_session.reveal(&request).unwrap();
    let (pre, refund_key) = session.unmask(&resp, &reveal.signature_mask).unwrap();
    Issued {
        keys,
        pre,
        refund_key,
        request,
        reveal,
    }
}

fn verify_payment_with_checkers(
    rng: &mut StdRng,
    payment: &Payment<E, D>,
    pk_iss: &[G2],
) -> Result<(), Error> {
    let rpc = RandomizedPairingCheckerGuard::<E>::new_using_rng(rng, true);
    rpc.with_err(Error::InvalidIssuerSignature, |rpc| {
        let rmc = RandomizedMultCheckerGuard::<D>::new_using_rng(rng);
        rmc.with_err(Error::InvalidSignature, |rmc| {
            payment.verify(rng, pk_iss, AD, &D::generator(), Some((rpc, rmc)))
        })
    })
}

fn verify_refund_with_checkers(
    rng: &mut StdRng,
    refund: &RefundRequest<E, D>,
    pk_iss: &G2,
    pk_ref: &D,
) -> Result<(), Error> {
    let rpc = RandomizedPairingCheckerGuard::<E>::new_using_rng(rng, true);
    rpc.with_err(Error::InvalidIssuerSignature, |rpc| {
        let rmc = RandomizedMultCheckerGuard::<D>::new_using_rng(rng);
        rmc.with_err(Error::InvalidSignature, |rmc| {
            refund.verify(rng, pk_iss, pk_ref, &D::generator(), Some((rpc, rmc)))
        })
    })
}

#[test]
fn spend_and_refund() {
    let mut rng = StdRng::seed_from_u64(0);
    let sig_base = D::generator();
    let issued = issue(&mut rng, 5);
    let pk_ref = issued.refund_key.keypair.pk;

    let payment = Payment::new(&mut rng, &issued.pre[..3], AD, &sig_base).unwrap();
    let pk_iss = vec![issued.keys.pk; 3];
    payment
        .verify(&mut rng, &pk_iss, AD, &sig_base, None)
        .unwrap();
    verify_payment_with_checkers(&mut rng, &payment, &pk_iss).unwrap();

    let refund =
        RefundRequest::new(&mut rng, &issued.refund_key, &issued.pre[3..], &sig_base).unwrap();
    refund
        .verify(&mut rng, &issued.keys.pk, &pk_ref, &sig_base, None)
        .unwrap();
    verify_refund_with_checkers(&mut rng, &refund, &issued.keys.pk, &pk_ref).unwrap();

    issued
        .reveal
        .verify(
            &issued.keys.pk,
            &issued.request.commitment_to_sig_mask,
            None,
        )
        .unwrap();
    RandomizedMultCheckerGuard::<G2>::new_using_rng(&mut rng)
        .with_err(Error::InvalidSignatureMask, |rmc| {
            issued.reveal.verify(
                &issued.keys.pk,
                &issued.request.commitment_to_sig_mask,
                Some(rmc),
            )
        })
        .unwrap();
}

#[test]
fn forgeries_fail_with_and_without_checkers() {
    let mut rng = StdRng::seed_from_u64(0);
    let sig_base = D::generator();
    let issued = issue(&mut rng, 3);
    let pk_iss = vec![issued.keys.pk; 3];

    let mut forged = Payment::new(&mut rng, &issued.pre, AD, &sig_base).unwrap();
    forged.tokens[2].unblinded_sig =
        (forged.tokens[2].unblinded_sig * Fr::from(2u64)).into_affine();
    assert_eq!(
        forged.verify(&mut rng, &pk_iss, AD, &sig_base, None),
        Err(Error::InvalidIssuerSignature)
    );
    assert_eq!(
        verify_payment_with_checkers(&mut rng, &forged, &pk_iss),
        Err(Error::InvalidIssuerSignature)
    );

    let mut wrong_msg = Payment::new(&mut rng, &issued.pre, b"other", &sig_base).unwrap();
    assert_eq!(
        wrong_msg.verify(&mut rng, &pk_iss, AD, &sig_base, None),
        Err(Error::InvalidSignature)
    );
    assert_eq!(
        verify_payment_with_checkers(&mut rng, &wrong_msg, &pk_iss),
        Err(Error::InvalidSignature)
    );

    // Tokens of another issuer, checked against the session's issuer.
    let other = issue(&mut rng, 2);
    let refund = RefundRequest::new(&mut rng, &issued.refund_key, &other.pre, &sig_base).unwrap();
    assert_eq!(
        refund.verify(
            &mut rng,
            &issued.keys.pk,
            &issued.refund_key.keypair.pk,
            &sig_base,
            None
        ),
        Err(Error::InvalidIssuerSignature)
    );

    let mut bad_reveal = issued.reveal.clone();
    bad_reveal.signature_mask.0 += Fr::one();
    assert_eq!(
        bad_reveal.verify(
            &issued.keys.pk,
            &issued.request.commitment_to_sig_mask,
            None
        ),
        Err(Error::InvalidSignatureMask)
    );

    wrong_msg.tokens.truncate(2);
    assert_eq!(
        wrong_msg.verify(&mut rng, &pk_iss[..2], b"other", &sig_base, None),
        Err(Error::InvalidSignature)
    );
}

#[test]
fn payment_rejects_malformed() {
    let mut rng = StdRng::seed_from_u64(0);
    let sig_base = D::generator();
    let issued = issue(&mut rng, 3);
    let payment = Payment::new(&mut rng, &issued.pre, AD, &sig_base).unwrap();
    let pk_iss = vec![issued.keys.pk; 3];

    assert_eq!(
        Payment::<E, D>::new(&mut rng, &[], AD, &sig_base),
        Err(Error::Empty)
    );
    let empty = Payment::<E, D> {
        tokens: vec![],
        signature: payment.signature.clone(),
    };
    assert_eq!(
        empty.verify(&mut rng, &[], AD, &sig_base, None),
        Err(Error::Empty)
    );
    assert_eq!(
        payment.verify(&mut rng, &pk_iss[..2], AD, &sig_base, None),
        Err(Error::LengthMismatch)
    );

    let mut dup = payment.clone();
    dup.tokens[2] = dup.tokens[0].clone();
    assert_eq!(
        dup.verify(&mut rng, &pk_iss, AD, &sig_base, None),
        Err(Error::DuplicateKey)
    );

    // An identity key with an identity signature satisfies the pairing equation on its own.
    let kp = Keypair::new(&mut rng, &sig_base);
    let zero_token = Payment::<E, D> {
        tokens: vec![Token {
            pk_e: kp.pk,
            unblinded_sig: <E as Pairing>::G1Affine::zero(),
        }],
        signature: BatchSig::new(&mut rng, &[kp], AD, &sig_base).unwrap(),
    };
    assert_eq!(
        zero_token.verify(&mut rng, &[G2::zero()], AD, &sig_base, None),
        Err(Error::IdentityPoint)
    );
}

#[test]
fn batch_sig_rejects_empty_key_set() {
    let mut rng = StdRng::seed_from_u64(0);
    let sig_base = D::generator();
    assert_eq!(
        BatchSig::<D>::new(&mut rng, &[], AD, &sig_base),
        Err(Error::Empty)
    );
    let s = <D as AffineRepr>::ScalarField::rand(&mut rng);
    let sig = BatchSig {
        t: (sig_base * s).into_affine(),
        s,
    };
    assert_eq!(sig.verify(&[], AD, &sig_base, None), Err(Error::Empty));
}

#[test]
fn issuance_rejects_mismatch() {
    let mut rng = StdRng::seed_from_u64(0);
    let keys = IssuerKeypair::<E>::new(&mut rng);
    let (session, req) = ClientSession::<E, D>::new(&mut rng, 3, &D::generator()).unwrap();
    let (issuer_session, resp) = IssuerSession::new(&mut rng, &req, &keys).unwrap();
    let request = OnChainIssuanceRequest::new(&session, &resp);

    let mut short = resp.clone();
    short.blinded.pop();
    assert_eq!(
        short.verify(&mut rng, &req, None),
        Err(Error::LengthMismatch)
    );
    let mask = SignatureMask::<E>(Fr::rand(&mut rng));
    assert!(matches!(
        session.clone().unmask(&short, &mask),
        Err(Error::LengthMismatch)
    ));

    let zero_com = IssueResponse {
        blinded: resp.blinded.clone(),
        commitment_to_sig_mask: CommitmentToSigMask(G2::zero()),
    };
    assert_eq!(
        zero_com.verify(&mut rng, &req, None),
        Err(Error::IdentityPoint)
    );

    // A client paying for fewer tokens than were signed.
    let mut underpaid = request.clone();
    underpaid.count -= 1;
    assert!(matches!(
        issuer_session.clone().reveal(&underpaid),
        Err(Error::SessionMismatch)
    ));
    let mut other_com = request.clone();
    other_com.commitment_to_sig_mask = CommitmentToSigMask::new(&mask, &keys.pk);
    assert!(matches!(
        issuer_session.clone().reveal(&other_com),
        Err(Error::SessionMismatch)
    ));
    assert!(issuer_session.reveal(&request).is_ok());

    let mut zero_count = request.clone();
    zero_count.count = 0;
    assert_eq!(zero_count.verify(), Err(Error::Empty));
    let mut zero_ref = request;
    zero_ref.pk_ref = D::zero();
    assert_eq!(zero_ref.verify(), Err(Error::IdentityPoint));

    let empty_req = polymesh_bat::protocol::IssueRequest::<E> {
        sid: [0u8; 32],
        blinded_public_keys: vec![],
    };
    assert!(matches!(
        IssuerSession::new(&mut rng, &empty_req, &keys),
        Err(Error::Empty)
    ));
}

#[test]
fn serialization_round_trip() {
    let mut rng = StdRng::seed_from_u64(0);
    let sig_base = D::generator();
    let issued = issue(&mut rng, 2);
    let payment = Payment::new(&mut rng, &issued.pre, AD, &sig_base).unwrap();
    let refund = RefundRequest::new(&mut rng, &issued.refund_key, &issued.pre, &sig_base).unwrap();

    fn round_trip<T: CanonicalSerialize + CanonicalDeserialize + PartialEq + core::fmt::Debug>(
        t: &T,
    ) {
        let mut bytes = vec![];
        t.serialize_compressed(&mut bytes).unwrap();
        assert_eq!(&T::deserialize_compressed(&bytes[..]).unwrap(), t);
    }
    round_trip(&payment);
    round_trip(&refund);
    round_trip(&issued.request);
    round_trip(&issued.reveal);

    let mut bytes = vec![];
    issued.refund_key.serialize_compressed(&mut bytes).unwrap();
    let key = RefundKey::<D>::deserialize_compressed(&bytes[..]).unwrap();
    assert_eq!(key.keypair.pk, issued.refund_key.keypair.pk);
    assert_eq!(key.sid, issued.refund_key.sid);
}

#[test]
fn issuer_key_from_seed() {
    let a = IssuerKeypair::<E>::new_with_seed(b"seed 1");
    let b = IssuerKeypair::<E>::new_with_seed(b"seed 1");
    let c = IssuerKeypair::<E>::new_with_seed(b"seed 2");
    assert_eq!(a.sk, b.sk);
    assert_eq!(a.pk, b.pk);
    assert_ne!(a.pk, c.pk);
    assert_eq!(a.pk, (G2::generator() * a.sk).into_affine());
}
