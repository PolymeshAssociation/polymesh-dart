//! # BAT Protocol A proof of concept — plan
//!
//! Measures the crypto cost of BAT issuance, spend and refund on two pairing curves, to price
//! replacing the `dart-bp/docs/6.md` fee path. Protocol A only (Fig. 7 of
//! <https://eprint.iacr.org/2026/1074>). Protocol B is out of scope: its refund reveals the PRF
//! seed, which retroactively links every already-spent token of the session, and that disqualifies
//! it for fee payment regardless of cost. See `BAT_FEE_PAYMENT_EVALUATION.md`.
//!
//! Nothing here is a protocol implementation. Counters, escrow, balances, sessions, retirement and
//! the nullifier store are all absent. What is measured is exactly the group and field arithmetic,
//! plus the serialized bytes that arithmetic rides on.
//!
//! ## What the split isolates
//!
//! The paper's Table 1 is Protocol A on BLS12-381, Table 2 is Protocol B on BN254. Curve and
//! protocol move together, so neither table prices the curve. Running Protocol A on both, with the
//! client signature scheme DS held fixed, makes the curve the only variable.
//!
//! - `E = Bls12_381`, `DS` over `ark_ed25519` — reproduces Table 1, gives the calibration point
//! - `E = Bn254`, `DS` over `ark_ed25519` — the same protocol, cheaper pairings, smaller points
//! - `E = Bn254`, `DS` over `E::G1Affine` — drops the second curve from the node's arithmetic
//!
//! BN254 sits at roughly 100-bit security after Kim–Barbulescu, against 126 for BLS12-381. The PoC
//! reports the speed; the security gap is a separate decision and is not priced here.
//!
//! ## Notation
//!
//! Groups are written additively, as in the paper. `P*x` is the scalar multiple of a group element
//! `P` by a scalar `x`, `.` is ordinary multiplication between scalars, and `e(P, Q)` is the
//! pairing. `GT` is additive too, so a product of pairings is a sum and the checks below compare
//! against `0` rather than `1`.
//!
//! Pairing groups `G1, G2, GT` with `e : G1 x G2 -> GT`, generator `h` in `G2`, hash
//! `H : {0,1}^* -> G1`. Issuer key `pk_iss = h*sk_iss`. DS is an ordinary signature scheme over a
//! group `D` with no pairing. Client wants `l` tokens in session `sid`.
//!
//! Actors: `C` client, `I` issuer, `E` chain. Only `E`'s column is "on-chain cost"; `C` and `I` are
//! measured because they set the wallet's latency and the issuer's service cost.
//!
//! ## Phases, and what each one costs
//!
//! ### Register
//!
//! `I` publishes `pk_iss`. No protocol crypto, but `E` must decode: subgroup check and non-identity
//! on `pk_iss` in `G2`. An identity `pk_iss` makes every later pairing check trivially satisfiable,
//! so the check is load-bearing rather than hygiene. G2 subgroup checks are not free and are
//! measured as their own line.
//!
//! ### Pi-MIssue, off chain
//!
//! `C` generates `l` ephemeral DS keypairs and blinds:
//!
//! ```text
//! X_i = H(pk_e,i)*r_i,   r_i random
//! ```
//!
//! and sends `(sid, {X_i}, l)` to `I`. Cost: `l` DS keygens, `l` hash-to-curve, `l` G1 scalar mults.
//!
//! `I` picks one session mask `k` and returns `({sigma~_i}, com_k)`:
//!
//! ```text
//! sigma~_i = X_i*(k.sk_iss),   com_k = pk_iss*k
//! ```
//!
//! Cost: 1 field mult, 1 G2 scalar mult, `l` G1 scalar mults all sharing the scalar `k.sk_iss`.
//! Shared scalar with varying base, so this is `l` separate mults, not an MSM. Measure whether a
//! windowed form of the single scalar beats `l` independent `mul_bigint` calls.
//!
//! `C` checks `e(sigma~_i, h) == e(X_i, com_k)` for all `i`. Three variants, see *Batching* below.
//!
//! `C` then generates the refund keypair `(sk_ref, pk_ref)`.
//!
//! ### Pi-Execute, on chain
//!
//! Two transactions, both `O(1)` in `l`. This is the whole point of the masking construction and the
//! reason issuance is cheap enough to consider at all.
//!
//! `C` sends `(sid, pk_ref, com_k, l)`. `E` decodes: subgroup and non-identity on `com_k` in `G2`,
//! subgroup on `pk_ref` in `D`. That is the entire cost of transaction one.
//!
//! `I` sends `(sid, k)`. `E` checks `k . pk_iss == com_k`. One G2 scalar mult, one compare.
//!
//! A block carries `m` such reveals. Three ways to check them, all measured:
//!
//! ```text
//! E1  naive           m G2 scalar mults, m compares
//! E2  fixed base      BatchMulPreprocessing::new(pk_iss, m), then batch_mul
//! E3  randomized MSM  pick rho, check
//!                     pk_iss*(\sum_m{rho^m . k_m}) - \sum_m{com_k_m*rho^m} == 0
//! ```
//!
//! E3 is one G2 MSM of size `m+1`: base `pk_iss` with scalar `\sum_m{rho^m . k_m}`, and each
//! `com_k_m` with scalar `-rho^m`. Across `J` issuer keys the per-key scalars accumulate
//! independently, so it stays one G2 MSM of size `J + m`. E2's table is per issuer key and issuer
//! keys are long-lived registry state, so it is reported twice: table build charged in, and warm
//! table. A warm table is the realistic node behaviour and makes cache invalidation on
//! register/retire a pallet obligation.
//!
//! E3 is a locally randomized check, not Fiat-Shamir. Each node draws its own `rho` and never
//! reveals it, so an adversary cannot aim at a node's coin. An honest batch passes for every `rho`;
//! a dishonest one fails except with probability `m/p`. Two obligations fall out, and they belong to
//! the pallet rather than to this PoC. Consensus needs the divergence probability argued explicitly,
//! not assumed. And a failing batch identifies no culprit, so rejection has to fall back to
//! per-item checking to attribute the failure, which is a liveness and attribution requirement, not
//! a soundness one.
//!
//! `C` unmasks locally once `k` is public calldata:
//!
//! ```text
//! alpha_i = sigma~_i*((r_i.k)^-1) = H(pk_e,i)*sk_iss
//! ```
//!
//! Cost: `l` field inversions plus `l` G1 scalar mults. Measured with naive inversion and with
//! Montgomery batch inversion, which turns `l` inversions into one inversion and `3l` mults.
//!
//! ### TokGen and Spend
//!
//! `C` signs the associated data: `gamma = DS.Sign(sk_e, ad)`, token `= (pk_e, alpha, gamma)`.
//!
//! `E` accepts a spend when `e(alpha, h) == e(H(pk_e), pk_iss)` and `DS.Verify(pk_e, ad, gamma)` and
//! `pk_e` is unnullified. Per token: 1 hash-to-curve, 1 two-pair multi-pairing, 1 DS verify, plus
//! decode checks on `alpha` and `pk_e`.
//!
//! In DART the extrinsic is already signed by `pk_e`, so `gamma` is the extrinsic signature the node
//! verifies anyway. Spend verification is therefore reported twice, with DS and without, and the
//! without-DS figure is the one that belongs in the fee comparison.
//!
//! ### Refund
//!
//! `C` signs one authorization over the whole batch, `gamma_ref = DS.Sign(sk_ref, (sid, {alpha_i,
//! pk_e,i}))`, and sends it with the `l_ref` unspent tokens.
//!
//! `E` verifies `gamma_ref` once, then for each `i` checks `e(alpha_i, h) == e(H(pk_e,i), pk_iss)` and
//! that `pk_e,i` is unnullified. One DS verify for the batch, not `l_ref`, so refund is cheaper per
//! token than spend on the crypto side even though it is far more expensive on gas.
//!
//! Figure 7 checks membership for each `i` and inserts all of them only after the loop, so
//! `l_ref` copies of one token pass every check and mint `l_ref` units. The PoC includes the fix,
//! pairwise distinctness of `{pk_e,i}` within the batch, in the measured path. It is a sort or a
//! hash set and costs nothing, but leaving it out would measure the wrong protocol.
//!
//! ## Batching
//!
//! Every pairing check in the protocol has the shape `\forall i : e(A_i, h) == e(B_i, Y_j)` with a
//! small number of distinct right-hand `G2` elements. That structure collapses, and collapsing it is
//! most of the available win.
//!
//! Nothing bypasses `RandomizedPairingChecker` and nothing hand-collapses the equations either. The
//! checker groups the accumulated pairs by their `G2` element, so a batch whose `G2` side takes `k`
//! distinct values settles as `k` `G1` MSMs against a `k`-pair multi-miller-loop and one final
//! exponentiation, which is exactly the collapse. Masked verification has `k = 2`, `h` and `com_k`.
//! Spend over `J` issuer keys has `k = 1 + J`, `h` and the keys. Refund is spend at `J = 1`, so two
//! pairs for any `l_ref`.
//!
//! The grouping only happens on the `G2Affine` overloads, `add_sources_g2_affine` and
//! `add_multiple_sources_g2_affine`, which key the group by x coordinate and prepare once per
//! distinct point at the end. The plain `add_sources` takes `impl Into<G2Prepared>`, so it accepts an
//! affine point silently and prepares it on every call, then keys the group by serializing the
//! prepared form. At `l = 100` on BLS12-381 that is 200 preparations, 18.9 ms against 2.9.
//!
//! Hand-written aggregation over the top of the grouping was measured and removed. Pre-combining the
//! `G1` sides into MSMs and handing the checker two points costs an extra `into_affine` per group and
//! a `powers` vector the checker then re-randomizes, and it loses everywhere: 5.0 ms against 2.9 for
//! masked verification at `l = 100`, and 68.5 against 61.0 for spend at `n = 512, J = 1`. A direct
//! pairing path bypassing the checker went the same way: at `n = 1` the checker costs 0.800 ms
//! against 0.798 for a direct multi-pairing. So the pairing side carries no variants at all, and the
//! only ones left anywhere are `FixedBase` and `Rmc` for the issuer reveal.
//!
//! Spend, `n` tokens across `J` issuer keys with `S_j` the tokens under key `j`, is what the checker
//! ends up evaluating:
//!
//! ```text
//! e(-\sum_i{alpha_i*beta_i}, h) + \sum_j{e(\sum_{i in S_j}{H(pk_e,i)*beta_i}, pk_iss,j)} == 0
//! ```
//!
//! Cost: `n` hash-to-curve, one G1 MSM of size `n`, `J` G1 MSMs totalling `n`, one `(1+J)`-pair
//! multi-pairing. Hash-to-curve and nullifier distinctness stay per token and become the floor once
//! `J` is small.
//!
//! DS batch verification. Writing the Schnorr signature as `(t, s)` with `c = H(t, pk, m)`, one
//! signature checks `g*s == t + pk*c` and `n` of them check as
//!
//! ```text
//! g*\sum_i{delta_i.s_i} == \sum_i{t_i*delta_i} + \sum_i{pk_i*(delta_i.c_i)}
//! ```
//!
//! which is one MSM of size `2n+1`. This is what `RandomizedMultChecker::add_2` accumulates and what
//! `PokDiscreteLog::verify_using_randomized_mult_checker` already exposes, so DS is built on
//! `schnorr_pok::discrete_log` rather than on `dock_crypto_utils::schnorr_signature`, which has no
//! batch path.
//!
//! ## Generic function inventory
//!
//! Two type parameters throughout, `E: Pairing` and `D: AffineRepr` for the DS group, plus a
//! hash-to-`G1` strategy as a third. Tests supply concrete types and counts; no function hardcodes a
//! curve.
//!
//! ```text
//! trait HashToG1<E: Pairing> { fn hash(msg: &[u8]) -> E::G1Affine; }
//!   Standard<Dig>  blanket, any curve, via dock_crypto_utils::hashing_utils
//!   Standard               BLS12-381 only, MapToCurveBasedHasher + WBMap
//!
//! issuer_keygen<E>()                                    -> (sk_iss, pk_iss)
//! chain_decode_issuer_key<E>(bytes)                     -> subgroup + non-identity, timed
//!
//! client_issue_request<E, D, H>(l)                     -> (ClientState<E, D>, Request<E>)
//! issuer_issue_response<E>(req, sk_iss)                -> (Session<E>, Response<E>)
//! client_verify_blinded<E>(state, resp)                 -> bool
//!
//! chain_execute_client_msg<E, D>(msgs)                  -> decode checks only
//! chain_execute_issuer_msg<E>(reveals, keys, Variant)   -> fixed-base warm | cold | RMC
//! client_unmask<E>(state, k)                            -> Vec<PreToken<E, D>>
//!
//! PreToken::token_gen<D>(ad)                             -> Token<E, D>
//! chain_spend<E, D, H>(tokens, keys, n, j, ds: DsCheck)  -> bool
//!
//! client_refund_request<E, D>(pre_tokens, l_ref, sid, sk_ref)
//! chain_refund<E, D, H>(req, pk_iss, l_ref)
//! ```
//!
//! `n` and `J` are independent arguments to `chain_spend` because the denomination-pool adaptation
//! makes them so: one issuer key per power-of-two denomination, so a single fee payment of value `V`
//! spends up to `ceil(log2 V)` tokens across as many keys, and `J = n` is the realistic worst case
//! for one payment while `J << n` is the block-level case.
//!
//! ## Measurement matrix
//!
//! Issuance and refund at `l` in `{1, 10, 50, 100}`, matching the paper's tables so the BLS12-381
//! column is directly checkable against Table 1.
//!
//! Spend at `n` in `{1, 8, 64, 512}` crossed with `J` in `{1, n}`, plus the per-payment shape
//! `n = J` in `{1, 4, 8, 16}` which is what a DART fee actually looks like.
//!
//! Reported per configuration: chain time, client time, issuer time, and chain time per token. The
//! comparison target is 5.831 ms verify and 52.97 ms generate for `FeeAccountPaymentProof` from
//! `perf_comparison_results_1.md`.
//!
//! ## Sizes
//!
//! Compressed `CanonicalSerialize` sizes, reported alongside every timing:
//!
//! ```text
//! token = |pk_e| + |G1| + |gamma|
//!   BLS12-381 + Ed25519   32 + 48 + 64 = 144 B    reproduces the paper
//!   BN254     + Ed25519   32 + 32 + 64 = 128 B
//!
//! missue request    32 + l.|G1|
//! missue response   l.|G1| + |G2|
//! execute, client   32 + |pk_ref| + |G2| + 4
//! execute, issuer   32 + 32
//! spend             |token| + issuer index
//! refund            32 + l_ref.(|G1| + |pk_e|) + |gamma_ref|
//! ```
//!
//! The refund line is the one that decides deployability. It is linear in `l_ref` and it is the
//! payload every client of a griefing issuer must get included inside `T_grace`.
//!
//! ## Excluded
//!
//! Counters, escrow, balances, session and refund-set bookkeeping, retirement, and the nullifier
//! store. These are storage, not crypto, and on Substrate they are trie writes whose cost does not
//! follow from anything measured here. Storage reads and writes per operation are *counted* and
//! reported as counts so the arithmetic timings are not mistaken for a total.
//!
//! Also excluded: the on-chain balance transfer, the reclaim timeout, and anything that depends on
//! block production.
//!
//! ## Known biases, stated because they move the numbers
//!
//! Hash-to-curve is asymmetric in availability. BLS12-381 has a WB/SWU map in the arkworks fork;
//! BN254 has none and arkworks 0.5 ships no SVDW, so the common baseline is hash-to-field followed
//! by try-and-increment on `x`. BLS12-381 is measured both ways to size what that substitution
//! costs. It costs nothing measurable: both clear a `2^126` cofactor and that dominates the map.
//! The curve gap in hash-to-curve is therefore cofactor clearing, since BN254's `G1` has cofactor 1,
//! and it is intrinsic rather than an artifact of the baseline.
//!
//! Try-and-increment is still variable time in the number of increments, so a deployment on BN254
//! needs SVDW written whichever way the curve decision goes.
//!
//! DS is a Schnorr proof of knowledge of a discrete log over `ark_ed25519`, not RFC 8032. Same group
//! arithmetic, different challenge derivation, no clamping, no cofactor handling. Generic arkworks
//! Twisted Edwards is well behind `curve25519-dalek`, so every DS number here is an upper bound and
//! the spend column inherits that.
//!
//! Single-threaded, to match the paper. The `parallel` feature changes MSM and multi-pairing costs
//! and would make the batched variants look better than the paper's numbers for reasons unrelated to
//! the protocol.
//!
//! Native Rust throughout. The paper's gas figures are Ethereum precompiles and do not transfer;
//! Table 3 is context for the refund-congestion argument, not a target.
//!
//! ## Cargo wiring
//!
//! Dev-dependencies on `ark-bls12-381`, `ark-bn254`, `ark-ed25519`, `dock_crypto_utils`,
//! `schnorr_pok`, `sha2`, all at the workspace versions. `ark-ed25519` is already patched to the
//! fork; the two pairing curves need adding to the root `[patch.crates-io]` alongside the others:
//!
//! ```text
//! ark-bls12-381 = { path = "../arkworks-algebra/curves/bls12_381" }
//! ark-bn254     = { path = "../arkworks-algebra/curves/bn254" }
//! ```
//!
//! Without the patch entries they resolve from crates.io and build against the patched `ark-ec` and
//! `ark-ff` anyway, which works until the fork diverges and then fails obscurely. Patch them.
//!
//! ## Harness
//!
//! `Instant`, median of `N` runs with a discarded warmup, matching how
//! `perf_comparison_results_1.md` was produced. Not criterion: the configuration matrix is large and
//! the output wanted is one markdown table per curve, not a statistical report per cell.
//!
//! Run with `cargo test --release --test bat_poc -- --nocapture`. Each test emits its table to
//! stdout. Correctness assertions accompany every timed path, so a mismeasured variant that quietly
//! computes the wrong thing fails rather than reporting a fast number.

#[path = "bat_poc/baseline.rs"]
mod baseline;
#[path = "bat_poc/ds.rs"]
mod ds;
#[path = "bat_poc/hash.rs"]
mod hash;
#[path = "bat_poc/measure.rs"]
mod measure;
#[path = "bat_poc/protocol.rs"]
mod protocol;

use ark_bls12_381::Bls12_381;
use ark_bn254::Bn254;
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ed25519::EdwardsAffine;
use ark_ff::{AdditiveGroup, Field, UniformRand, Zero};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::{
    rngs::StdRng,
    {CryptoRng, RngCore, SeedableRng},
};
use hash::{HashToG1, Standard};
use measure::{Table, bench, fmt_ms};
use protocol::{ClientSession, DsCheck, IssuerKeys, PreToken, Reveal, RevealCheck, Token};

const AD: &[u8] = b"dart-fee-payment-associated-data";

fn rng() -> StdRng {
    StdRng::seed_from_u64(0xBA7)
}

fn issue<E, D, H, R>(
    rng: &mut R,
    keys: &IssuerKeys<E>,
    nt: usize,
    ds_base: &D,
) -> (ClientSession<E, D>, Vec<PreToken<E, D>>)
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
    R: RngCore + CryptoRng,
{
    let (session, req) = protocol::client_issue_request::<E, D, H, _>(rng, nt, ds_base);
    let (k, resp) = protocol::issuer_issue_response(rng, &req, keys);
    assert!(protocol::client_verify_blinded(rng, &session, &resp));
    let pre = protocol::client_unmask(&session, &resp, k);
    (session, pre)
}

/// `n` tokens spread round-robin over `j` issuer keys, all at one denomination.
fn spend_fixture<E, D, H, R>(
    rng: &mut R,
    n: usize,
    j: usize,
    ds_base: &D,
) -> (Vec<Token<E, D>>, Vec<usize>, Vec<E::G2Affine>)
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
    R: RngCore + CryptoRng,
{
    let issuers: Vec<IssuerKeys<E>> = (0..j).map(|_| protocol::issuer_keygen(rng)).collect();
    let issuer_of: Vec<usize> = (0..n).map(|i| i % j).collect();
    let mut per_issuer = vec![0usize; j];
    for idx in &issuer_of {
        per_issuer[*idx] += 1;
    }
    let mut pools: Vec<ark_std::vec::IntoIter<PreToken<E, D>>> = Vec::with_capacity(j);
    for (k, count) in per_issuer.iter().enumerate() {
        let (_, pre) = issue::<E, D, H, _>(rng, &issuers[k], *count, ds_base);
        pools.push(pre.into_iter());
    }
    let tokens: Vec<Token<E, D>> = issuer_of
        .iter()
        .map(|k| pools[*k].next().unwrap().token_gen(rng, AD, ds_base))
        .collect();
    (tokens, issuer_of, issuers.iter().map(|i| i.pk).collect())
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

fn issuance_report<E, D, H>(label: &str, num_tokens: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();
    let keys = protocol::issuer_keygen::<E, _>(&mut r);

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
            protocol::client_issue_request::<E, D, H, _>(&mut r, nt, &ds_base)
        });
        let (session, req) = protocol::client_issue_request::<E, D, H, _>(&mut r, nt, &ds_base);

        let t_sign = bench(it, || protocol::issuer_issue_response(&mut r, &req, &keys));
        let (k, resp) = protocol::issuer_issue_response(&mut r, &req, &keys);

        assert!(
            protocol::client_verify_blinded(&mut r, &session, &resp),
            "{label} masked verify at l={nt}"
        );
        let mut tampered = resp.clone();
        tampered.blinded[nt - 1] = (tampered.blinded[nt - 1] * E::ScalarField::from(2u64)).into();
        assert!(
            !protocol::client_verify_blinded(&mut r, &session, &tampered),
            "{label} masked verify accepted a tampered signature"
        );

        let t_verify = bench(it, || {
            protocol::client_verify_blinded(&mut r, &session, &resp)
        });

        let t_unmask = bench(it, || protocol::client_unmask(&session, &resp, k));

        let pre = protocol::client_unmask(&session, &resp, k);
        let h = E::G2Affine::generator();
        for (p, kp) in pre.iter().zip(&session.eph) {
            assert!(
                E::multi_pairing(
                    [p.alpha, -H::hash(&protocol::to_bytes(&kp.pk))],
                    [h, keys.pk]
                )
                .is_zero(),
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

fn execute_report<E, D>(label: &str, configs: &[(usize, usize)])
where
    E: Pairing,
    D: AffineRepr,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();

    let issuer = protocol::issuer_keygen::<E, _>(&mut r);
    let pk_bytes = protocol::to_bytes(&issuer.pk);
    assert!(protocol::chain_decode_issuer_key::<E>(&pk_bytes).is_some());
    let t_decode_key = bench(25, || protocol::chain_decode_issuer_key::<E>(&pk_bytes));

    let com_k = (issuer.pk * E::ScalarField::rand(&mut r)).into_affine();
    let com_bytes = protocol::to_bytes(&com_k);
    let ref_bytes = protocol::to_bytes(&ds::keygen(&mut r, &ds_base).pk);
    assert!(protocol::chain_execute_client_msg::<E, D>(
        &com_bytes, &ref_bytes
    ));
    let t_client_msg = bench(25, || {
        protocol::chain_execute_client_msg::<E, D>(&com_bytes, &ref_bytes)
    });

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
        let issuers: Vec<IssuerKeys<E>> = (0..j).map(|_| protocol::issuer_keygen(&mut r)).collect();
        let keys: Vec<E::G2Affine> = issuers.iter().map(|i| i.pk).collect();
        let reveals: Vec<Reveal<E>> = (0..m)
            .map(|i| {
                let k = E::ScalarField::rand(&mut r);
                Reveal {
                    issuer: i % j,
                    k,
                    com_k: (keys[i % j] * k).into_affine(),
                }
            })
            .collect();
        let tables = protocol::build_reveal_tables::<E>(&keys, m.div_ceil(j));

        for v in [RevealCheck::FixedBase, RevealCheck::Rmc] {
            assert!(
                protocol::chain_execute_issuer_msg(&mut r, &reveals, &keys, Some(&tables), v),
                "{label} reveal check {v:?} at m={m} J={j}"
            );
        }
        let mut bad = reveals.clone();
        bad[m - 1].k += E::ScalarField::ONE;
        for v in [RevealCheck::FixedBase, RevealCheck::Rmc] {
            assert!(
                !protocol::chain_execute_issuer_msg(&mut r, &bad, &keys, Some(&tables), v),
                "{label} reveal check {v:?} accepted a bad opening"
            );
        }

        let it = iters_for(m);
        let t_cold = bench(it, || {
            protocol::chain_execute_issuer_msg(
                &mut r,
                &reveals,
                &keys,
                None,
                RevealCheck::FixedBase,
            )
        });
        let t_warm = bench(it, || {
            protocol::chain_execute_issuer_msg(
                &mut r,
                &reveals,
                &keys,
                Some(&tables),
                RevealCheck::FixedBase,
            )
        });
        let t_rmc = bench(it, || {
            protocol::chain_execute_issuer_msg(&mut r, &reveals, &keys, None, RevealCheck::Rmc)
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

fn spend_report<E, D, H>(label: &str, configs: &[(usize, usize)])
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();

    let mut t = Table::new(&[
        "n",
        "J",
        "hash-to-curve",
        "chain, no DS",
        "DS RMC",
        "chain, with DS",
        "per token, no DS",
    ]);

    for &(n, j) in configs {
        let (tokens, issuer_of, keys) = spend_fixture::<E, D, H, _>(&mut r, n, j, &ds_base);

        for d in [DsCheck::Rmc, DsCheck::Skip] {
            assert!(
                protocol::chain_spend::<E, D, H, _>(
                    &mut r, &tokens, &issuer_of, &keys, AD, &ds_base, d
                ),
                "{label} spend {d:?} at n={n} J={j}"
            );
        }
        let mut forged = tokens.clone();
        forged[n - 1].alpha = (forged[n - 1].alpha * E::ScalarField::from(2u64)).into_affine();
        assert!(
            !protocol::chain_spend::<E, D, H, _>(
                &mut r,
                &forged,
                &issuer_of,
                &keys,
                AD,
                &ds_base,
                DsCheck::Skip
            ),
            "{label} spend accepted a forged alpha"
        );
        if n > 1 {
            let mut dup = tokens.clone();
            dup[n - 1] = dup[0].clone();
            assert!(
                !protocol::chain_spend::<E, D, H, _>(
                    &mut r,
                    &dup,
                    &issuer_of,
                    &keys,
                    AD,
                    &ds_base,
                    DsCheck::Skip
                ),
                "{label} spend accepted a duplicate nullifier"
            );
        }

        let it = iters_for(n);
        let t_h2c = bench(it, || protocol::hash_tokens::<E, D, H>(&tokens));
        let run = |d: DsCheck, r: &mut StdRng| {
            protocol::chain_spend::<E, D, H, _>(r, &tokens, &issuer_of, &keys, AD, &ds_base, d)
        };
        let t_no_ds = bench(it, || run(DsCheck::Skip, &mut r));
        let t_with_ds = bench(it, || run(DsCheck::Rmc, &mut r));

        let sigs: Vec<ds::Sig<D>> = tokens.iter().map(|t| t.gamma.clone()).collect();
        let pks: Vec<D> = tokens.iter().map(|t| t.pk_e).collect();
        assert!(ds::batch_verify(&mut r, &sigs, &pks, AD, &ds_base));
        let t_ds_rmc = bench(it, || ds::batch_verify(&mut r, &sigs, &pks, AD, &ds_base));

        t.row(vec![
            n.to_string(),
            j.to_string(),
            fmt_ms(t_h2c),
            fmt_ms(t_no_ds),
            fmt_ms(t_ds_rmc),
            fmt_ms(t_with_ds),
            format!("{:.4}", measure::ms(t_no_ds) / n as f64),
        ]);
    }
    t.print(&format!(
        "{label} — spend, on chain (ms). Both chain columns are the whole check, hash-to-curve plus \
         nullifier distinctness plus the pairing, so the hash-to-curve column is a component of \
         them rather than an addend; they differ only in whether DS is verified"
    ));
}

/// One `RandomizedPairingChecker` and one `RandomizedMultChecker` across a whole block of
/// independent fee payments, against settling each payment on its own.
fn block_report<E, D, H>(label: &str, payments: &[usize], per_payment: usize)
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();

    let mut t = Table::new(&[
        "payments",
        "tokens/payment",
        "per-payment settle",
        "one checker for block",
        "per token, block",
        "speedup",
    ]);

    for &p in payments {
        let n = p * per_payment;
        let (tokens, issuer_of, keys) = spend_fixture::<E, D, H, _>(&mut r, n, 1, &ds_base);
        let batches: Vec<(Vec<Token<E, D>>, Vec<usize>)> = tokens
            .chunks(per_payment)
            .zip(issuer_of.chunks(per_payment))
            .map(|(t, i)| (t.to_vec(), i.to_vec()))
            .collect();

        assert!(protocol::chain_block_spend::<E, D, H, _>(
            &mut r, &batches, &keys, AD, &ds_base
        ));

        let it = iters_for(n);
        let t_each = bench(it, || {
            batches.iter().all(|(tk, io)| {
                protocol::chain_spend::<E, D, H, _>(
                    &mut r,
                    tk,
                    io,
                    &keys,
                    AD,
                    &ds_base,
                    DsCheck::Rmc,
                )
            })
        });
        let t_block = bench(it, || {
            protocol::chain_block_spend::<E, D, H, _>(&mut r, &batches, &keys, AD, &ds_base)
        });

        t.row(vec![
            p.to_string(),
            per_payment.to_string(),
            fmt_ms(t_each),
            fmt_ms(t_block),
            format!("{:.4}", measure::ms(t_block) / n as f64),
            format!("{:.2}x", measure::ms(t_each) / measure::ms(t_block)),
        ]);
    }
    t.print(&format!(
        "{label} — block settlement, one checker pair for the whole block (ms)"
    ));
}

/// Denomination pools against `6.md`. A set of `D` powers of two covers every fee up to `2^D - 1`;
/// the worst case is all `D` bits set, so `D` tokens, and the average over uniformly drawn fees is
/// `D/2`. Each denomination has its own issuer key, so a payment touching `d` of them is a `1 + d`
/// pair multi-pairing and the `G1` side splits into `d` MSMs of size 1.
fn denom_comparison_report<E, D, H>(label: &str, base: &baseline::Baseline, set_sizes: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();

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
            let (tokens, issuer_of, keys) = spend_fixture::<E, D, H, _>(r, n, n, &ds_base);
            let t = bench(iters_for(n), || {
                protocol::chain_spend::<E, D, H, _>(
                    r,
                    &tokens,
                    &issuer_of,
                    &keys,
                    AD,
                    &ds_base,
                    DsCheck::Skip,
                )
            });
            (t, tokens)
        };
        let (t_worst, tokens) = spend(d, &mut r);
        let (t_avg, _) = spend(d / 2, &mut r);

        let token = tokens[0].pk_e.compressed_size()
            + tokens[0].alpha.compressed_size()
            + tokens[0].gamma.compressed_size();

        t.row(vec![
            d.to_string(),
            format!("2^{d} - 1"),
            fmt_ms(t_worst),
            fmt_ms(t_avg),
            format!("{:.2}x", base_ms / measure::ms(t_worst)),
            format!("{:.2}x", base_ms / measure::ms(t_avg)),
            (d * token).to_string(),
        ]);
    }
    t.print(&format!(
        "{label} — denomination pools against 6.md at {:.3} ms verify / {} B, DS excluded. Ratios \
         above 1 favour BAT",
        base_ms, base.payment.size
    ));
}

// ---------------------------------------------------------------------------------------------
// Refund
// ---------------------------------------------------------------------------------------------

fn refund_report<E, D, H>(label: &str, num_tokens: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();
    let keys = protocol::issuer_keygen::<E, _>(&mut r);

    let mut t = Table::new(&["l_ref", "C sign", "chain", "per token", "payload (B)"]);

    for &nt in num_tokens {
        let (session, pre) = issue::<E, D, H, _>(&mut r, &keys, nt, &ds_base);
        let req = protocol::client_refund_request(&mut r, &session, &pre, &ds_base);

        assert!(
            protocol::chain_refund::<E, D, H, _>(
                &mut r,
                &req,
                &keys.pk,
                &session.refund.pk,
                &ds_base
            ),
            "{label} refund at l_ref={nt}"
        );
        if nt > 1 {
            let mut dup = req.clone();
            dup.pk_e[nt - 1] = dup.pk_e[0];
            dup.alpha[nt - 1] = dup.alpha[0];
            let msg = protocol::refund_msg::<E, D>(&dup.sid, &dup.alpha, &dup.pk_e);
            dup.gamma_ref = ds::sign(&mut r, &session.refund, &msg, &ds_base);
            assert!(
                !protocol::chain_refund::<E, D, H, _>(
                    &mut r,
                    &dup,
                    &keys.pk,
                    &session.refund.pk,
                    &ds_base,
                ),
                "{label} refund accepted a duplicate token in the batch"
            );
        }

        let it = iters_for(nt);
        let t_sign = bench(it, || {
            protocol::client_refund_request(&mut r, &session, &pre, &ds_base)
        });
        let t_chain = bench(it, || {
            protocol::chain_refund::<E, D, H, _>(
                &mut r,
                &req,
                &keys.pk,
                &session.refund.pk,
                &ds_base,
            )
        });

        let payload = 32
            + req.alpha.iter().map(|a| a.compressed_size()).sum::<usize>()
            + req.pk_e.iter().map(|p| p.compressed_size()).sum::<usize>()
            + req.gamma_ref.compressed_size();

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

fn sizes_report<E, D, H>(label: &str, num_tokens: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();
    let keys = protocol::issuer_keygen::<E, _>(&mut r);
    let (session, req) = protocol::client_issue_request::<E, D, H, _>(&mut r, 1, &ds_base);
    let (k, resp) = protocol::issuer_issue_response(&mut r, &req, &keys);
    let pre = protocol::client_unmask(&session, &resp, k);
    let token = pre
        .into_iter()
        .next()
        .unwrap()
        .token_gen(&mut r, AD, &ds_base);

    let g1 = token.alpha.compressed_size();
    let g2 = keys.pk.compressed_size();
    let pk_d = token.pk_e.compressed_size();
    let sig = token.gamma.compressed_size();
    let fr = E::ScalarField::ZERO.compressed_size();

    let mut t = Table::new(&["item", "formula", "bytes"]);
    t.row(vec!["G1 point".into(), "-".into(), g1.to_string()]);
    t.row(vec!["G2 point".into(), "-".into(), g2.to_string()]);
    t.row(vec!["DS public key".into(), "-".into(), pk_d.to_string()]);
    t.row(vec![
        "DS signature".into(),
        "|D| + |Fr_D|".into(),
        sig.to_string(),
    ]);
    t.row(vec![
        "token".into(),
        "|pk_e| + |G1| + |gamma|".into(),
        (pk_d + g1 + sig).to_string(),
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
            format!("refund, l_ref={nt}"),
            "sid + l.(|G1| + |pk_e|) + |gamma|".into(),
            (32 + nt * (g1 + pk_d) + sig).to_string(),
        ]);
    }
    t.print(&format!("{label} — serialized sizes (compressed)"));
}

fn primitives_report<E, D, H>(label: &str)
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();
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
    let kp = ds::keygen(&mut r, &ds_base);
    let sig = ds::sign(&mut r, &kp, AD, &ds_base);

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
        format!("hash-to-G1 ({})", <H as HashToG1<E>>::NAME),
        fmt_ms(bench(50, || H::hash(AD))),
    ]);
    t.row(vec![
        "Fr inversion".into(),
        fmt_ms(bench(50, || s.inverse().unwrap())),
    ]);
    t.row(vec![
        "DS keygen".into(),
        fmt_ms(bench(50, || ds::keygen(&mut r, &ds_base))),
    ]);
    t.row(vec![
        "DS sign".into(),
        fmt_ms(bench(50, || ds::sign(&mut r, &kp, AD, &ds_base))),
    ]);
    t.row(vec![
        "DS verify".into(),
        fmt_ms(bench(50, || ds::verify(&sig, &kp.pk, AD, &ds_base))),
    ]);
    t.print(&format!("{label} — primitives (ms)"));
}

// ---------------------------------------------------------------------------------------------
// Against the current fee mechanism
// ---------------------------------------------------------------------------------------------

/// The paper's scheme mints one unit per accepted spend, so a fee of `l` base units costs `l`
/// tokens, while `6.md` pays any amount with one proof. One denomination throughout; the pool
/// scheme is measured separately.
fn comparison_report<E, D, H>(label: &str, base: &baseline::Baseline, num_tokens: &[usize])
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
{
    let mut r = rng();
    let ds_base = ds::generator::<D>();
    let keys = protocol::issuer_keygen::<E, _>(&mut r);

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
            protocol::client_issue_request::<E, D, H, _>(&mut r, nt, &ds_base)
        });
        let (session, req) = protocol::client_issue_request::<E, D, H, _>(&mut r, nt, &ds_base);
        let t_sign = bench(it, || protocol::issuer_issue_response(&mut r, &req, &keys));
        let (k, resp) = protocol::issuer_issue_response(&mut r, &req, &keys);
        let t_verify = bench(it, || {
            protocol::client_verify_blinded(&mut r, &session, &resp)
        });
        let t_unmask = bench(it, || protocol::client_unmask(&session, &resp, k));

        let com_bytes = protocol::to_bytes(&resp.com_k);
        let ref_bytes = protocol::to_bytes(&session.refund.pk);
        let reveals: [Reveal<E>; 1] = [Reveal {
            issuer: 0,
            k,
            com_k: resp.com_k,
        }];
        let t_chain = bench(25, || {
            protocol::chain_execute_client_msg::<E, D>(&com_bytes, &ref_bytes)
                && protocol::chain_execute_issuer_msg(
                    &mut r,
                    &reveals,
                    core::slice::from_ref(&keys.pk),
                    None,
                    RevealCheck::Rmc,
                )
        });

        let g1 = resp.blinded[0].compressed_size();
        let g2 = resp.com_k.compressed_size();
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
        "BAT chain no DS",
        "BAT chain with DS",
        "6.md bytes",
        "BAT bytes",
        "chain ratio",
        "bytes ratio",
    ]);
    for &nt in num_tokens {
        let (_, pre) = issue::<E, D, H, _>(&mut r, &keys, nt, &ds_base);
        let tokens: Vec<Token<E, D>> = pre
            .iter()
            .cloned()
            .map(|p| p.token_gen(&mut r, AD, &ds_base))
            .collect();
        let issuer_of = vec![0usize; nt];
        let iss_keys = vec![keys.pk];

        let it = iters_for(nt);
        let t_sign = bench(it, || {
            pre.iter()
                .cloned()
                .map(|p| p.token_gen(&mut r, AD, &ds_base))
                .collect::<Vec<_>>()
        });
        let t_no_ds = bench(it, || {
            protocol::chain_spend::<E, D, H, _>(
                &mut r,
                &tokens,
                &issuer_of,
                &iss_keys,
                AD,
                &ds_base,
                DsCheck::Skip,
            )
        });
        let t_with_ds = bench(it, || {
            protocol::chain_spend::<E, D, H, _>(
                &mut r,
                &tokens,
                &issuer_of,
                &iss_keys,
                AD,
                &ds_base,
                DsCheck::Rmc,
            )
        });
        assert!(protocol::chain_spend::<E, D, H, _>(
            &mut r,
            &tokens,
            &issuer_of,
            &iss_keys,
            AD,
            &ds_base,
            DsCheck::Rmc
        ));

        let token_size = tokens[0].pk_e.compressed_size()
            + tokens[0].alpha.compressed_size()
            + tokens[0].gamma.compressed_size();
        let bat_bytes = nt * token_size;

        pay.row(vec![
            nt.to_string(),
            fmt_ms(base.payment.prove),
            fmt_ms(t_sign),
            fmt_ms(base.payment.verify),
            fmt_ms(t_no_ds),
            fmt_ms(t_with_ds),
            base.payment.size.to_string(),
            bat_bytes.to_string(),
            format!(
                "{:.2}x",
                measure::ms(base.payment.verify) / measure::ms(t_no_ds)
            ),
            format!("{:.2}x", base.payment.size as f64 / bat_bytes as f64),
        ]);
    }
    pay.print(&format!(
        "{label} — payment of l base units. 6.md is one proof for any amount, BAT is l tokens. \
         Ratios above 1 favour BAT"
    ));
}

// ---------------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------------

const NUM_TOKENS: &[usize] = &[1, 5, 10, 20, 30, 40, 50, 100, 200];
const EXECUTE: &[(usize, usize)] = &[
    (1, 1),
    (5, 1),
    (10, 1),
    (20, 1),
    (50, 1),
    (100, 1),
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
const BLOCK: &[usize] = &[1, 8, 32, 128];

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

    comparison_report::<Bls12_381, EdwardsAffine, Standard>(
        "BLS12-381 / Ed25519",
        &base,
        NUM_TOKENS,
    );
    comparison_report::<Bls12_381, ark_pallas::Affine, Standard>(
        "BLS12-381 / Pallas",
        &base,
        NUM_TOKENS,
    );
    comparison_report::<Bn254, EdwardsAffine, Standard>("BN254 / Ed25519", &base, NUM_TOKENS);
    comparison_report::<Bn254, ark_pallas::Affine, Standard>("BN254 / Pallas", &base, NUM_TOKENS);
}

#[test]
fn primitives() {
    primitives_report::<Bls12_381, EdwardsAffine, Standard>("BLS12-381 / Ed25519");
    primitives_report::<Bls12_381, ark_pallas::Affine, Standard>("BLS12-381 / Pallas");
    primitives_report::<Bn254, EdwardsAffine, Standard>("BN254 / Ed25519");
    primitives_report::<Bn254, ark_pallas::Affine, Standard>("BN254 / Pallas");
    primitives_report::<Bn254, ark_bn254::G1Affine, Standard>("BN254 / BN254-G1");
}

#[test]
fn issuance() {
    issuance_report::<Bls12_381, EdwardsAffine, Standard>("BLS12-381 / Ed25519", NUM_TOKENS);
    issuance_report::<Bls12_381, ark_pallas::Affine, Standard>("BLS12-381 / Pallas", NUM_TOKENS);
    issuance_report::<Bn254, EdwardsAffine, Standard>("BN254 / Ed25519", NUM_TOKENS);
    issuance_report::<Bn254, ark_pallas::Affine, Standard>("BN254 / Pallas", NUM_TOKENS);
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
    spend_report::<Bls12_381, EdwardsAffine, Standard>("BLS12-381 / Ed25519", SPEND);
    spend_report::<Bls12_381, ark_pallas::Affine, Standard>("BLS12-381 / Pallas", SPEND);
    spend_report::<Bn254, EdwardsAffine, Standard>("BN254 / Ed25519", SPEND);
    spend_report::<Bn254, ark_pallas::Affine, Standard>("BN254 / Pallas", SPEND);
}

#[test]
fn denominations() {
    let base = baseline::measure(10, 200);
    denom_comparison_report::<Bls12_381, EdwardsAffine, Standard>(
        "BLS12-381 / Ed25519",
        &base,
        DENOM_SETS,
    );
    denom_comparison_report::<Bls12_381, ark_pallas::Affine, Standard>(
        "BLS12-381 / Pallas",
        &base,
        DENOM_SETS,
    );
    denom_comparison_report::<Bn254, EdwardsAffine, Standard>("BN254 / Ed25519", &base, DENOM_SETS);
    denom_comparison_report::<Bn254, ark_pallas::Affine, Standard>(
        "BN254 / Pallas",
        &base,
        DENOM_SETS,
    );
}

#[test]
fn block() {
    block_report::<Bls12_381, EdwardsAffine, Standard>("BLS12-381 / Ed25519", BLOCK, 4);
    block_report::<Bls12_381, ark_pallas::Affine, Standard>("BLS12-381 / Pallas", BLOCK, 4);
    block_report::<Bn254, EdwardsAffine, Standard>("BN254 / Ed25519", BLOCK, 4);
    block_report::<Bn254, ark_pallas::Affine, Standard>("BN254 / Pallas", BLOCK, 4);
}

#[test]
fn refund() {
    refund_report::<Bls12_381, EdwardsAffine, Standard>("BLS12-381 / Ed25519", NUM_TOKENS);
    refund_report::<Bls12_381, ark_pallas::Affine, Standard>("BLS12-381 / Pallas", NUM_TOKENS);
    refund_report::<Bn254, EdwardsAffine, Standard>("BN254 / Ed25519", NUM_TOKENS);
    refund_report::<Bn254, ark_pallas::Affine, Standard>("BN254 / Pallas", NUM_TOKENS);
}

#[test]
fn sizes() {
    sizes_report::<Bls12_381, EdwardsAffine, Standard>(
        "BLS12-381 / Ed25519",
        &[1, 10, 50, 100, 200],
    );
    sizes_report::<Bls12_381, ark_pallas::Affine, Standard>(
        "BLS12-381 / Pallas",
        &[1, 10, 50, 100, 200],
    );
    sizes_report::<Bn254, EdwardsAffine, Standard>("BN254 / Ed25519", &[1, 10, 50, 100, 200]);
    sizes_report::<Bn254, ark_pallas::Affine, Standard>("BN254 / Pallas", &[1, 10, 50, 100, 200]);
}
