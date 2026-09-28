//! # BAT Protocol - POC
//!
//! Measures the crypto cost of BAT issuance, spend and refund on two pairing curves, to price
//! replacing the `dart-bp/docs/6.md` fee path. Protocol A only (Fig. 7 of
//! <https://eprint.iacr.org/2026/1074>). Protocol B is out of scope. See `BAT_FEE_PAYMENT_EVALUATION.md`.
//!
//! Nothing here is a protocol implementation. Counters, escrow, balances, sessions, retirement and
//! the nullifier store are all absent. What is measured is exactly the group and field arithmetic,
//! plus the serialized bytes that arithmetic rides on.
//!

#[path = "bat_poc/baseline.rs"]
mod baseline;
#[path = "bat_poc/measure.rs"]
mod measure;

use polymesh_bat::{Error, hash, protocol, signature};

use ark_bls12_381::Bls12_381;
use ark_bn254::Bn254;
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing, scalar_mul::BatchMulPreprocessing};
use ark_ed25519::EdwardsAffine;
use ark_ff::{AdditiveGroup, Field, UniformRand, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::{
    rngs::StdRng,
    {CryptoRng, RngCore, SeedableRng},
};
use dock_crypto_utils::randomized_mult_checker::RandomizedMultCheckerGuard;
use hash::HashToG1;
use measure::{Table, bench, fmt_ms};
use protocol::{
    ClientSession, CommitmentToSigMask, IssuerKeypair, IssuerSession, OnChainIssuanceRequest,
    Payment, PreToken, RefundKey, RefundRequest, Reveal, SignatureMask,
};
use signature::{BatchSig, Keypair};

const AD: &[u8] = b"dart-fee-payment-associated-data";

fn rng() -> StdRng {
    StdRng::seed_from_u64(0xBA7)
}

fn issue<E, D, R>(
    rng: &mut R,
    keys: &IssuerKeypair<E>,
    nt: usize,
    ds_base: &D,
) -> (RefundKey<D>, Vec<PreToken<E, D>>)
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
    R: RngCore + CryptoRng,
{
    let (session, req) = ClientSession::<E, D>::new(rng, nt as u32, ds_base).unwrap();
    let (issuer_session, resp) = IssuerSession::new(rng, &req, keys).unwrap();
    resp.verify(rng, &req, None).unwrap();
    let reveal = issuer_session
        .reveal(&OnChainIssuanceRequest::new(&session, &resp))
        .unwrap();
    let (pre, refund_key) = session.unmask(&resp, &reveal.signature_mask).unwrap();
    (refund_key, pre)
}

/// `n` tokens spread round-robin over `j` issuer keys, all at one denomination, with the one batch
/// signature that authorizes spending them and the issuer key of each token.
fn spend_fixture<E, D, R>(
    rng: &mut R,
    n: usize,
    j: usize,
    ds_base: &D,
) -> (Payment<E, D>, Vec<E::G2Affine>)
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
    R: RngCore + CryptoRng,
{
    let issuers: Vec<IssuerKeypair<E>> = (0..j).map(|_| IssuerKeypair::new(rng)).collect();
    let issuer_of: Vec<usize> = (0..n).map(|i| i % j).collect();
    let mut per_issuer = vec![0usize; j];
    for idx in &issuer_of {
        per_issuer[*idx] += 1;
    }
    let mut pools: Vec<ark_std::vec::IntoIter<PreToken<E, D>>> = Vec::with_capacity(j);
    for (k, count) in per_issuer.iter().enumerate() {
        let (_, pre) = issue::<E, D, _>(rng, &issuers[k], *count, ds_base);
        pools.push(pre.into_iter());
    }
    let pre: Vec<PreToken<E, D>> = issuer_of
        .iter()
        .map(|k| pools[*k].next().unwrap())
        .collect();
    let payment = Payment::new(rng, &pre, AD, ds_base).unwrap();
    (payment, issuer_of.iter().map(|k| issuers[*k].pk).collect())
}

fn iters_for(work: usize) -> usize {
    match work {
        0..=16 => 25,
        17..=128 => 10,
        _ => 5,
    }
}

// ---------------------------------------------------------------------------------------------
// Issuance
// ---------------------------------------------------------------------------------------------

fn issuance_report<E, D>(label: &str, num_tokens: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
{
    let mut r = rng();
    let ds_base = D::generator();
    let keys = IssuerKeypair::<E>::new(&mut r);

    let mut main = Table::new(&[
        "l",
        "C blind",
        "I sign",
        "C verify",
        "C unmask",
        "verify, per token",
    ]);
    for &nt in num_tokens {
        let it = iters_for(nt);
        let t_blind = bench(it, || {
            ClientSession::<E, D>::new(&mut r, nt as u32, &ds_base).unwrap()
        });
        let (session, req) = ClientSession::<E, D>::new(&mut r, nt as u32, &ds_base).unwrap();

        let t_sign = bench(it, || IssuerSession::new(&mut r, &req, &keys));
        let (issuer_session, resp) = IssuerSession::new(&mut r, &req, &keys).unwrap();

        assert!(
            resp.verify(&mut r, &req, None).is_ok(),
            "{label} masked verify at l={nt}"
        );
        let mut tampered = resp.clone();
        tampered.blinded[nt - 1] = (tampered.blinded[nt - 1] * E::ScalarField::from(2u64)).into();
        assert!(
            tampered.verify(&mut r, &req, None).is_err(),
            "{label} masked verify accepted a tampered signature"
        );
        let mut short = resp.clone();
        short.blinded.pop();
        assert_eq!(
            short.verify(&mut r, &req, None),
            Err(Error::LengthMismatch),
            "{label} masked verify accepted fewer signatures than requested"
        );

        let t_verify = bench(it, || resp.verify(&mut r, &req, None));

        let reveal = issuer_session
            .reveal(&OnChainIssuanceRequest::new(&session, &resp))
            .unwrap();
        let t_unmask = bench(it, || session.clone().unmask(&resp, &reveal.signature_mask));

        let (pre, _) = session.unmask(&resp, &reveal.signature_mask).unwrap();
        let h = E::G2Affine::generator();
        for p in &pre {
            assert!(
                E::multi_pairing([p.unblinded_sig, -p.token().hash()], [h, keys.pk]).is_zero(),
                "{label} unmasked signature invalid"
            );
        }

        main.row(vec![
            nt.to_string(),
            fmt_ms(t_blind),
            fmt_ms(t_sign),
            fmt_ms(t_verify),
            fmt_ms(t_unmask),
            format!("{:.4}", measure::ms(t_verify) / nt as f64),
        ]);
    }

    main.print(&format!("{label} — issuance, off chain (ms)"));
}

// ---------------------------------------------------------------------------------------------
// Pi-Execute
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RevealCheck {
    /// Windowed table per issuer key, reused across that key's reveals.
    FixedBase,
    /// `RandomizedMultChecker` over `G2`, which merges the repeated `pk_iss` bases and settles the
    /// whole block as one `G2` MSM of size `J + m`.
    Rmc,
}

#[derive(Clone)]
struct IssuerReveal<E: Pairing> {
    issuer: usize,
    reveal: Reveal<E>,
    commitment: CommitmentToSigMask<E>,
}

fn build_reveal_tables<E: Pairing>(
    keys: &[E::G2Affine],
    per_key: usize,
) -> Vec<BatchMulPreprocessing<E::G2>> {
    keys.iter()
        .map(|k| BatchMulPreprocessing::new((*k).into(), per_key.max(1)))
        .collect()
}

/// `tables` supplied means a warm cache, which is what a node holds since issuer keys are long-lived
/// registry state; `None` charges the build.
fn check_reveals<E: Pairing, R: RngCore + CryptoRng>(
    rng: &mut R,
    reveals: &[IssuerReveal<E>],
    keys: &[E::G2Affine],
    tables: Option<&[BatchMulPreprocessing<E::G2>]>,
    variant: RevealCheck,
) -> bool {
    match variant {
        RevealCheck::FixedBase => {
            let built;
            let tables = match tables {
                Some(t) => t,
                None => {
                    built = build_reveal_tables::<E>(keys, reveals.len());
                    &built
                }
            };
            (0..keys.len()).all(|j| {
                let ks: Vec<E::ScalarField> = reveals
                    .iter()
                    .filter(|r| r.issuer == j)
                    .map(|r| r.reveal.signature_mask.0)
                    .collect();
                if ks.is_empty() {
                    return true;
                }
                let got = tables[j].batch_mul(&ks);
                reveals
                    .iter()
                    .filter(|r| r.issuer == j)
                    .map(|r| r.commitment.0)
                    .eq(got)
            })
        }
        RevealCheck::Rmc => RandomizedMultCheckerGuard::new_using_rng(rng)
            .with_err(Error::InvalidSignatureMask, |rmc| {
                for r in reveals {
                    r.reveal
                        .verify(&keys[r.issuer], &r.commitment, Some(&mut *rmc))?;
                }
                Ok(())
            })
            .is_ok(),
    }
}

fn execute_report<E, D>(label: &str, configs: &[(usize, usize)])
where
    E: Pairing,
    D: AffineRepr,
{
    let mut r = rng();
    let ds_base = D::generator();

    let issuer = IssuerKeypair::<E>::new(&mut r);
    let pk_bytes = protocol::to_bytes(&issuer.pk);
    let decode_key = |b: &[u8]| {
        E::G2Affine::deserialize_compressed(b)
            .ok()
            .filter(|pk| !pk.is_zero())
    };
    assert!(decode_key(&pk_bytes).is_some());
    let t_decode_key = bench(25, || decode_key(&pk_bytes));

    let request = OnChainIssuanceRequest::<E, D> {
        sid: [0u8; 32],
        pk_ref: Keypair::new(&mut r, &ds_base).pk,
        commitment_to_sig_mask: CommitmentToSigMask::new(
            &SignatureMask(E::ScalarField::rand(&mut r)),
            &issuer.pk,
        ),
        count: 1,
    };
    let request_bytes = protocol::to_bytes(&request);
    let decode_request = |b: &[u8]| {
        OnChainIssuanceRequest::<E, D>::deserialize_compressed(b).is_ok_and(|e| e.verify().is_ok())
    };
    assert!(decode_request(&request_bytes));
    let t_client_msg = bench(25, || decode_request(&request_bytes));

    let mut decode = Table::new(&["check", "time (ms)"]);
    decode.row(vec![
        "issuer key decode + subgroup".into(),
        fmt_ms(t_decode_key),
    ]);
    decode.row(vec![
        "client msg decode (com_k + pk_ref)".into(),
        fmt_ms(t_client_msg),
    ]);
    decode.print(&format!("{label} — Pi-Execute decode (ms)"));

    let mut t = Table::new(&[
        "m reveals",
        "J keys",
        "fixed-base cold",
        "fixed-base warm",
        "RMC",
        "RMC per reveal",
    ]);

    for &(m, j) in configs {
        let issuers: Vec<IssuerKeypair<E>> = (0..j).map(|_| IssuerKeypair::new(&mut r)).collect();
        let keys: Vec<E::G2Affine> = issuers.iter().map(|i| i.pk).collect();
        let reveals: Vec<IssuerReveal<E>> = (0..m)
            .map(|i| {
                let mask = SignatureMask(E::ScalarField::rand(&mut r));
                IssuerReveal {
                    issuer: i % j,
                    commitment: CommitmentToSigMask::new(&mask, &keys[i % j]),
                    reveal: Reveal {
                        sid: [0u8; 32],
                        signature_mask: mask,
                    },
                }
            })
            .collect();
        let tables = build_reveal_tables::<E>(&keys, m.div_ceil(j));

        for v in [RevealCheck::FixedBase, RevealCheck::Rmc] {
            assert!(
                check_reveals(&mut r, &reveals, &keys, Some(&tables), v),
                "{label} reveal check {v:?} at m={m} J={j}"
            );
        }
        let mut bad = reveals.clone();
        bad[m - 1].reveal.signature_mask.0 += E::ScalarField::ONE;
        for v in [RevealCheck::FixedBase, RevealCheck::Rmc] {
            assert!(
                !check_reveals(&mut r, &bad, &keys, Some(&tables), v),
                "{label} reveal check {v:?} accepted a bad opening"
            );
        }

        let it = iters_for(m);
        let t_cold = bench(it, || {
            check_reveals(&mut r, &reveals, &keys, None, RevealCheck::FixedBase)
        });
        let t_warm = bench(it, || {
            check_reveals(
                &mut r,
                &reveals,
                &keys,
                Some(&tables),
                RevealCheck::FixedBase,
            )
        });
        let t_rmc = bench(it, || {
            check_reveals(&mut r, &reveals, &keys, None, RevealCheck::Rmc)
        });

        t.row(vec![
            m.to_string(),
            j.to_string(),
            fmt_ms(t_cold),
            fmt_ms(t_warm),
            fmt_ms(t_rmc),
            format!("{:.4}", measure::ms(t_rmc) / m as f64),
        ]);
    }
    t.print(&format!(
        "{label} — Pi-Execute issuer reveal, on chain (ms)"
    ));
}

// ---------------------------------------------------------------------------------------------
// Spend
// ---------------------------------------------------------------------------------------------

fn spend_report<E, D>(label: &str, configs: &[(usize, usize)])
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
{
    let mut r = rng();
    let ds_base = D::generator();

    let mut t = Table::new(&["n", "J", "hash-to-curve", "DS batch", "chain", "per token"]);

    for &(n, j) in configs {
        let (payment, pk_iss) = spend_fixture::<E, D, _>(&mut r, n, j, &ds_base);

        assert!(
            payment.verify(&mut r, &pk_iss, AD, &ds_base, None).is_ok(),
            "{label} spend at n={n} J={j}"
        );
        let mut forged = payment.clone();
        forged.tokens[n - 1].unblinded_sig =
            (forged.tokens[n - 1].unblinded_sig * E::ScalarField::from(2u64)).into_affine();
        assert!(
            forged.verify(&mut r, &pk_iss, AD, &ds_base, None).is_err(),
            "{label} spend accepted a forged alpha"
        );
        assert_eq!(
            payment.verify(&mut r, &pk_iss[..n - 1], AD, &ds_base, None),
            Err(Error::LengthMismatch),
            "{label} spend accepted fewer issuer keys than tokens"
        );
        if n > 1 {
            let mut dup = payment.clone();
            dup.tokens[n - 1] = dup.tokens[0].clone();
            assert!(
                dup.verify(&mut r, &pk_iss, AD, &ds_base, None).is_err(),
                "{label} spend accepted a duplicate nullifier"
            );
            // The batch signature binds the ordered key set, so a reordered spend must fail even
            // though every token in it is genuine.
            let mut swapped = payment.clone();
            swapped.tokens.swap(0, n - 1);
            let mut iss_swapped = pk_iss.clone();
            iss_swapped.swap(0, n - 1);
            assert!(
                swapped
                    .verify(&mut r, &iss_swapped, AD, &ds_base, None)
                    .is_err(),
                "{label} spend accepted a reordered batch"
            );
        }

        let it = iters_for(n);
        let t_h2c = bench(it, || {
            payment.tokens.iter().map(|t| t.hash()).collect::<Vec<_>>()
        });
        let t_chain = bench(it, || payment.verify(&mut r, &pk_iss, AD, &ds_base, None));

        let pks: Vec<D> = payment.tokens.iter().map(|t| t.pk_e).collect();
        assert!(payment.signature.verify(&pks, AD, &ds_base, None).is_ok());
        let t_ds = bench(it, || payment.signature.verify(&pks, AD, &ds_base, None));

        t.row(vec![
            n.to_string(),
            j.to_string(),
            fmt_ms(t_h2c),
            fmt_ms(t_ds),
            fmt_ms(t_chain),
            format!("{:.4}", measure::ms(t_chain) / n as f64),
        ]);
    }
    t.print(&format!(
        "{label} — spend, on chain (ms). The chain column is the whole check, hash-to-curve plus \
         nullifier distinctness plus the pairing plus the batch DS verify, so the hash-to-curve and \
         DS-batch columns are components of it rather than addends"
    ));
}

/// Denomination pools against `6.md`. A set of `D` powers of two covers every fee up to `2^D - 1`;
/// the worst case is all `D` bits set, so `D` tokens, and the average over uniformly drawn fees is
/// `D/2`. Each denomination has its own issuer key, so a payment touching `d` of them is a `1 + d`
/// pair multi-pairing and the `G1` side splits into `d` MSMs of size 1.
fn denom_comparison_report<E, D>(label: &str, base: &baseline::Baseline, set_sizes: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
{
    let mut r = rng();
    let ds_base = D::generator();

    let mut t = Table::new(&[
        "denominations D",
        "largest fee payable",
        "worst case, D tokens",
        "average case, D/2 tokens",
        "worst vs 6.md",
        "average vs 6.md",
        "bytes, worst case",
    ]);

    let base_ms = measure::ms(base.payment.verify);

    for &d in set_sizes {
        let spend = |n: usize, r: &mut StdRng| {
            let (payment, pk_iss) = spend_fixture::<E, D, _>(r, n, n, &ds_base);
            let t = bench(iters_for(n), || {
                payment.verify(r, &pk_iss, AD, &ds_base, None)
            });
            (t, payment)
        };
        let (t_worst, payment) = spend(d, &mut r);
        let (t_avg, _) = spend(d / 2, &mut r);

        let token = payment.tokens[0].pk_e.compressed_size()
            + payment.tokens[0].unblinded_sig.compressed_size();
        let sig = payment.signature.t.compressed_size() + payment.signature.s.compressed_size();

        t.row(vec![
            d.to_string(),
            format!("2^{d} - 1"),
            fmt_ms(t_worst),
            fmt_ms(t_avg),
            format!("{:.2}x", base_ms / measure::ms(t_worst)),
            format!("{:.2}x", base_ms / measure::ms(t_avg)),
            (d * token + sig).to_string(),
        ]);
    }
    t.print(&format!(
        "{label} — denomination pools against 6.md at {:.3} ms verify / {} B. Ratios \
         above 1 favour BAT",
        base_ms, base.payment.size
    ));
}

// ---------------------------------------------------------------------------------------------
// Refund
// ---------------------------------------------------------------------------------------------

fn refund_report<E, D>(label: &str, num_tokens: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
{
    let mut r = rng();
    let ds_base = D::generator();
    let keys = IssuerKeypair::<E>::new(&mut r);

    let mut t = Table::new(&["l_ref", "C sign", "chain", "per token", "payload (B)"]);

    for &nt in num_tokens {
        let (refund_key, pre) = issue::<E, D, _>(&mut r, &keys, nt, &ds_base);
        let pk_ref = refund_key.keypair.pk;
        let req = RefundRequest::new(&mut r, &refund_key, &pre, &ds_base).unwrap();

        assert!(
            req.verify(&mut r, &keys.pk, &pk_ref, &ds_base, None)
                .is_ok(),
            "{label} refund at l_ref={nt}"
        );
        if nt > 1 {
            let mut dup_pre = pre.clone();
            dup_pre[nt - 1] = dup_pre[0].clone();
            assert_eq!(
                RefundRequest::new(&mut r, &refund_key, &dup_pre, &ds_base),
                Err(Error::DuplicateKey)
            );
            // Signed by hand, so only the verifier stands in the way.
            let tokens: Vec<_> = dup_pre.iter().map(|p| p.token()).collect();
            let msg = RefundRequest::message(&refund_key.sid, &tokens);
            let dup = RefundRequest {
                sid: refund_key.sid,
                signature: BatchSig::new(
                    &mut r,
                    core::slice::from_ref(&refund_key.keypair),
                    &msg,
                    &ds_base,
                )
                .unwrap(),
                tokens,
            };
            assert_eq!(
                dup.verify(&mut r, &keys.pk, &pk_ref, &ds_base, None),
                Err(Error::DuplicateKey),
                "{label} refund accepted a duplicate token in the batch"
            );
        }

        let it = iters_for(nt);
        let t_sign = bench(it, || {
            RefundRequest::new(&mut r, &refund_key, &pre, &ds_base)
        });
        let t_chain = bench(it, || req.verify(&mut r, &keys.pk, &pk_ref, &ds_base, None));

        let payload = 32
            + req
                .tokens
                .iter()
                .map(|t| t.unblinded_sig.compressed_size() + t.pk_e.compressed_size())
                .sum::<usize>()
            + req.signature.compressed_size();

        t.row(vec![
            nt.to_string(),
            fmt_ms(t_sign),
            fmt_ms(t_chain),
            format!("{:.4}", measure::ms(t_chain) / nt as f64),
            payload.to_string(),
        ]);
    }
    t.print(&format!("{label} — refund (ms, bytes)"));
}

// ---------------------------------------------------------------------------------------------
// Sizes and primitives
// ---------------------------------------------------------------------------------------------

fn sizes_report<E, D>(label: &str, num_tokens: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
{
    let mut r = rng();
    let ds_base = D::generator();
    let keys = IssuerKeypair::<E>::new(&mut r);
    let (_, pre) = issue::<E, D, _>(&mut r, &keys, 1, &ds_base);
    let gamma = Payment::new(&mut r, &pre, AD, &ds_base).unwrap().signature;
    let token = pre[0].token();

    let g1 = token.unblinded_sig.compressed_size();
    let g2 = keys.pk.compressed_size();
    let pk_d = token.pk_e.compressed_size();
    let sig = gamma.t.compressed_size() + gamma.s.compressed_size();
    let fr = E::ScalarField::ZERO.compressed_size();

    let mut t = Table::new(&["item", "formula", "bytes"]);
    t.row(vec!["G1 point".into(), "-".into(), g1.to_string()]);
    t.row(vec!["G2 point".into(), "-".into(), g2.to_string()]);
    t.row(vec!["DS public key".into(), "-".into(), pk_d.to_string()]);
    t.row(vec![
        "DS signature, one per payment".into(),
        "|D| + |Fr_D|".into(),
        sig.to_string(),
    ]);
    t.row(vec![
        "token".into(),
        "|pk_e| + |G1|".into(),
        (pk_d + g1).to_string(),
    ]);
    t.row(vec![
        "execute, client msg".into(),
        "sid + |pk_ref| + |G2| + 4".into(),
        (32 + pk_d + g2 + 4).to_string(),
    ]);
    t.row(vec![
        "execute, issuer msg".into(),
        "sid + |Fr|".into(),
        (32 + fr).to_string(),
    ]);
    for &nt in num_tokens {
        t.row(vec![
            format!("MIssue request, l={nt}"),
            "sid + l.|G1|".into(),
            (32 + nt * g1).to_string(),
        ]);
        t.row(vec![
            format!("MIssue response, l={nt}"),
            "sid + l.|G1| + |G2|".into(),
            (32 + nt * g1 + g2).to_string(),
        ]);
        t.row(vec![
            format!("spend, l={nt}"),
            "l.(|pk_e| + |G1|) + |gamma|".into(),
            (nt * (pk_d + g1) + sig).to_string(),
        ]);
        t.row(vec![
            format!("refund, l_ref={nt}"),
            "sid + l.(|G1| + |pk_e|) + |gamma|".into(),
            (32 + nt * (g1 + pk_d) + sig).to_string(),
        ]);
    }
    t.print(&format!("{label} — serialized sizes (compressed)"));
}

fn primitives_report<E, D>(label: &str)
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
{
    let mut r = rng();
    let ds_base = D::generator();
    let s = E::ScalarField::rand(&mut r);
    let g1 = E::G1Affine::generator();
    let g2 = E::G2Affine::generator();
    let msm1: Vec<E::G1Affine> = (0..100)
        .map(|_| (g1 * E::ScalarField::rand(&mut r)).into_affine())
        .collect();
    let msm2: Vec<E::G2Affine> = (0..100)
        .map(|_| (g2 * E::ScalarField::rand(&mut r)).into_affine())
        .collect();
    let sc: Vec<E::ScalarField> = (0..100).map(|_| E::ScalarField::rand(&mut r)).collect();
    let kp = Keypair::new(&mut r, &ds_base);
    let kps = core::slice::from_ref(&kp);
    let pks = core::slice::from_ref(&kp.pk);
    let sig = BatchSig::new(&mut r, kps, AD, &ds_base).unwrap();

    let mut t = Table::new(&["primitive", "time (ms)"]);
    t.row(vec!["G1 scalar mult".into(), fmt_ms(bench(50, || g1 * s))]);
    t.row(vec!["G2 scalar mult".into(), fmt_ms(bench(50, || g2 * s))]);
    t.row(vec![
        "G1 MSM, 100".into(),
        fmt_ms(bench(25, || {
            <E::G1 as ark_ec::VariableBaseMSM>::msm_unchecked(&msm1, &sc)
        })),
    ]);
    t.row(vec![
        "G2 MSM, 100".into(),
        fmt_ms(bench(25, || {
            <E::G2 as ark_ec::VariableBaseMSM>::msm_unchecked(&msm2, &sc)
        })),
    ]);
    t.row(vec![
        "pairing".into(),
        fmt_ms(bench(25, || E::pairing(g1, g2))),
    ]);
    t.row(vec![
        "multi-pairing, 2".into(),
        fmt_ms(bench(25, || E::multi_pairing([g1, g1], [g2, g2]))),
    ]);
    t.row(vec![
        "multi-pairing, 10".into(),
        fmt_ms(bench(25, || E::multi_pairing([g1; 10], [g2; 10]))),
    ]);
    t.row(vec![
        "final exponentiation".into(),
        fmt_ms(bench(25, || {
            E::final_exponentiation(E::multi_miller_loop([g1], [g2]))
        })),
    ]);
    t.row(vec![
        "hash-to-G1".to_string(),
        fmt_ms(bench(50, || E::hash_to_g1(AD))),
    ]);
    t.row(vec![
        "Fr inversion".into(),
        fmt_ms(bench(50, || s.inverse().unwrap())),
    ]);
    t.row(vec![
        "DS keygen".into(),
        fmt_ms(bench(50, || Keypair::new(&mut r, &ds_base))),
    ]);
    t.row(vec![
        "DS sign".into(),
        fmt_ms(bench(50, || BatchSig::new(&mut r, kps, AD, &ds_base))),
    ]);
    t.row(vec![
        "DS verify".into(),
        fmt_ms(bench(50, || sig.verify(pks, AD, &ds_base, None))),
    ]);
    t.print(&format!("{label} — primitives (ms)"));
}

/// The paper's scheme mints one unit per accepted spend, so a fee of `l` base units costs `l`
/// tokens, while `6.md` pays any amount with one proof. One denomination throughout; the pool
/// scheme is measured separately.
fn comparison_report<E, D>(label: &str, base: &baseline::Baseline, num_tokens: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    E: HashToG1,
{
    let mut r = rng();
    let ds_base = D::generator();
    let keys = IssuerKeypair::<E>::new(&mut r);

    // Funding: BAT issuance of L tokens against one FeeAccountTopupProof of any amount.
    let mut fund = Table::new(&[
        "L tokens bought",
        "client off-chain",
        "issuer off-chain",
        "chain, both txns",
        "off-chain bytes",
        "on-chain bytes",
        "chain vs topup",
    ]);
    for &nt in num_tokens {
        let it = iters_for(nt);
        let t_blind = bench(it, || {
            ClientSession::<E, D>::new(&mut r, nt as u32, &ds_base).unwrap()
        });
        let (session, req) = ClientSession::<E, D>::new(&mut r, nt as u32, &ds_base).unwrap();
        let t_sign = bench(it, || IssuerSession::new(&mut r, &req, &keys));
        let (issuer_session, resp) = IssuerSession::new(&mut r, &req, &keys).unwrap();
        let t_verify = bench(it, || resp.verify(&mut r, &req, None));
        let request = OnChainIssuanceRequest::new(&session, &resp);
        let reveal = issuer_session.reveal(&request).unwrap();
        let t_unmask = bench(it, || session.clone().unmask(&resp, &reveal.signature_mask));

        let request_bytes = protocol::to_bytes(&request);
        let reveals = [IssuerReveal {
            issuer: 0,
            reveal: reveal.clone(),
            commitment: request.commitment_to_sig_mask.clone(),
        }];
        let t_chain = bench(25, || {
            OnChainIssuanceRequest::<E, D>::deserialize_compressed(&request_bytes[..])
                .is_ok_and(|e| e.verify().is_ok())
                && check_reveals(
                    &mut r,
                    &reveals,
                    core::slice::from_ref(&keys.pk),
                    None,
                    RevealCheck::Rmc,
                )
        });

        let g1 = resp.blinded[0].compressed_size();
        let g2 = resp.commitment_to_sig_mask.0.compressed_size();
        let pk_d = session.refund.pk.compressed_size();
        let fr = E::ScalarField::ZERO.compressed_size();
        let off_bytes = (32 + nt * g1) + (32 + nt * g1 + g2);
        let on_bytes = (32 + pk_d + g2 + 4) + (32 + fr);

        let client = measure::ms(t_blind) + measure::ms(t_verify) + measure::ms(t_unmask);
        fund.row(vec![
            nt.to_string(),
            format!("{:.2}", client),
            fmt_ms(t_sign),
            fmt_ms(t_chain),
            off_bytes.to_string(),
            on_bytes.to_string(),
            format!(
                "{:.2}x",
                measure::ms(base.topup.verify) / measure::ms(t_chain)
            ),
        ]);
    }
    fund.print(&format!(
        "{label} — funding: BAT issuance of L tokens against one FeeAccountTopupProof at \
         {:.2} ms prove / {:.3} ms verify / {} B",
        measure::ms(base.topup.prove),
        measure::ms(base.topup.verify),
        base.topup.size
    ));

    // Payment: BAT spends l tokens for a fee of l base units, 6.md spends one proof for any amount.
    let mut pay = Table::new(&[
        "fee amount l",
        "6.md client",
        "BAT client",
        "6.md chain",
        "BAT chain",
        "6.md bytes",
        "BAT bytes",
        "chain ratio",
        "bytes ratio",
    ]);
    for &nt in num_tokens {
        let (_, pre) = issue::<E, D, _>(&mut r, &keys, nt, &ds_base);
        let payment = Payment::new(&mut r, &pre, AD, &ds_base).unwrap();
        let pk_iss = vec![keys.pk; nt];

        let it = iters_for(nt);
        let t_sign = bench(it, || Payment::new(&mut r, &pre, AD, &ds_base));
        let t_chain = bench(it, || payment.verify(&mut r, &pk_iss, AD, &ds_base, None));
        assert!(payment.verify(&mut r, &pk_iss, AD, &ds_base, None).is_ok());

        let token_size = payment.tokens[0].pk_e.compressed_size()
            + payment.tokens[0].unblinded_sig.compressed_size();
        let bat_bytes = nt * token_size
            + payment.signature.t.compressed_size()
            + payment.signature.s.compressed_size();

        pay.row(vec![
            nt.to_string(),
            fmt_ms(base.payment.prove),
            fmt_ms(t_sign),
            fmt_ms(base.payment.verify),
            fmt_ms(t_chain),
            base.payment.size.to_string(),
            bat_bytes.to_string(),
            format!(
                "{:.2}x",
                measure::ms(base.payment.verify) / measure::ms(t_chain)
            ),
            format!("{:.2}x", base.payment.size as f64 / bat_bytes as f64),
        ]);
    }
    pay.print(&format!(
        "{label} — payment of l base units. 6.md is one proof for any amount, BAT is l tokens. \
         Ratios above 1 favour BAT"
    ));
}

const NUM_TOKENS: &[usize] = &[1, 5, 10, 20, 30, 40, 50, 100, 200];
const EXECUTE: &[(usize, usize)] = &[
    (1, 1),
    (5, 1),
    (10, 1),
    (20, 1),
    (50, 1),
    (100, 1),
    (200, 1),
    (1000, 1),
    (100, 10),
];
const SPEND: &[(usize, usize)] = &[
    (1, 1),
    (2, 2),
    (4, 1),
    (4, 4),
    (8, 1),
    (8, 8),
    (16, 1),
    (16, 16),
    (32, 1),
    (64, 1),
    (64, 8),
    (128, 1),
    (256, 1),
    (512, 1),
    (512, 64),
];
const DENOM_SETS: &[usize] = &[8, 16, 24, 32, 48, 64];

#[test]
fn comparison() {
    let base = baseline::measure(10, 200);
    let mut t = Table::new(&["6.md proof", "prove (ms)", "verify (ms)", "SCALE size (B)"]);
    for (name, row) in [
        ("FeeAccountTopupProof", &base.topup),
        ("FeeAccountPaymentProof", &base.payment),
    ] {
        t.row(vec![
            name.into(),
            fmt_ms(row.prove),
            fmt_ms(row.verify),
            row.size.to_string(),
        ]);
    }
    t.print("Current mechanism, measured on this machine");

    comparison_report::<Bls12_381, EdwardsAffine>("BLS12-381 / Ed25519", &base, NUM_TOKENS);
    comparison_report::<Bls12_381, ark_pallas::Affine>("BLS12-381 / Pallas", &base, NUM_TOKENS);
    comparison_report::<Bn254, EdwardsAffine>("BN254 / Ed25519", &base, NUM_TOKENS);
    comparison_report::<Bn254, ark_pallas::Affine>("BN254 / Pallas", &base, NUM_TOKENS);
}

#[test]
fn primitives() {
    primitives_report::<Bls12_381, EdwardsAffine>("BLS12-381 / Ed25519");
    primitives_report::<Bls12_381, ark_pallas::Affine>("BLS12-381 / Pallas");
    primitives_report::<Bn254, EdwardsAffine>("BN254 / Ed25519");
    primitives_report::<Bn254, ark_pallas::Affine>("BN254 / Pallas");
    primitives_report::<Bn254, ark_bn254::G1Affine>("BN254 / BN254-G1");
}

#[test]
fn issuance() {
    issuance_report::<Bls12_381, EdwardsAffine>("BLS12-381 / Ed25519", NUM_TOKENS);
    issuance_report::<Bls12_381, ark_pallas::Affine>("BLS12-381 / Pallas", NUM_TOKENS);
    issuance_report::<Bn254, EdwardsAffine>("BN254 / Ed25519", NUM_TOKENS);
    issuance_report::<Bn254, ark_pallas::Affine>("BN254 / Pallas", NUM_TOKENS);
}

#[test]
fn execute() {
    execute_report::<Bls12_381, EdwardsAffine>("BLS12-381 / Ed25519", EXECUTE);
    execute_report::<Bls12_381, ark_pallas::Affine>("BLS12-381 / Pallas", EXECUTE);
    execute_report::<Bn254, EdwardsAffine>("BN254 / Ed25519", EXECUTE);
    execute_report::<Bn254, ark_pallas::Affine>("BN254 / Pallas", EXECUTE);
}

#[test]
fn spend() {
    spend_report::<Bls12_381, EdwardsAffine>("BLS12-381 / Ed25519", SPEND);
    spend_report::<Bls12_381, ark_pallas::Affine>("BLS12-381 / Pallas", SPEND);
    spend_report::<Bn254, EdwardsAffine>("BN254 / Ed25519", SPEND);
    spend_report::<Bn254, ark_pallas::Affine>("BN254 / Pallas", SPEND);
}

#[test]
fn denominations() {
    let base = baseline::measure(10, 200);
    denom_comparison_report::<Bls12_381, EdwardsAffine>("BLS12-381 / Ed25519", &base, DENOM_SETS);
    denom_comparison_report::<Bls12_381, ark_pallas::Affine>(
        "BLS12-381 / Pallas",
        &base,
        DENOM_SETS,
    );
    denom_comparison_report::<Bn254, EdwardsAffine>("BN254 / Ed25519", &base, DENOM_SETS);
    denom_comparison_report::<Bn254, ark_pallas::Affine>("BN254 / Pallas", &base, DENOM_SETS);
}

#[test]
fn refund() {
    refund_report::<Bls12_381, EdwardsAffine>("BLS12-381 / Ed25519", NUM_TOKENS);
    refund_report::<Bls12_381, ark_pallas::Affine>("BLS12-381 / Pallas", NUM_TOKENS);
    refund_report::<Bn254, EdwardsAffine>("BN254 / Ed25519", NUM_TOKENS);
    refund_report::<Bn254, ark_pallas::Affine>("BN254 / Pallas", NUM_TOKENS);
}

#[test]
fn sizes() {
    sizes_report::<Bls12_381, EdwardsAffine>("BLS12-381 / Ed25519", &[1, 10, 50, 100, 200]);
    sizes_report::<Bls12_381, ark_pallas::Affine>("BLS12-381 / Pallas", &[1, 10, 50, 100, 200]);
    sizes_report::<Bn254, EdwardsAffine>("BN254 / Ed25519", &[1, 10, 50, 100, 200]);
    sizes_report::<Bn254, ark_pallas::Affine>("BN254 / Pallas", &[1, 10, 50, 100, 200]);
}
