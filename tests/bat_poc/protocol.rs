//! BAT Protocol A, Fig. 7 of <https://eprint.iacr.org/2026/1074>, arithmetic only.
//!
//! Counters, escrow, balances, sessions, retirement and the nullifier store are absent. Distinctness
//! of ephemeral keys within a batch is present because Fig. 7 omits it and the omission mints
//! `l_ref` units for one token, so measuring the figure as written would measure the wrong protocol.
//!
//! Every pairing check goes through `RandomizedPairingChecker` and every group-equation check
//! through `RandomizedMultChecker`, both taken by reference so a caller verifying a whole block pays
//! one final exponentiation and one MSM rather than one per operation. The pairing equations are
//! handed over one at a time through the `G2Affine` overloads, which group by the `G2` element, so
//! the checker performs the collapse itself. The `Into<G2Prepared>` overloads would prepare the
//! repeated `h`, `com_k` and `pk_iss` on every call.
//!
//! This module is the paper's scheme exactly, message = `pk_e`. Denominations are the paper's §8
//! pools, one issuer key per denomination, so they need no separate code: a payment touching `d`
//! denominations is a spend over `d` issuer keys.

use crate::{ds, hash::HashToG1};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing, scalar_mul::BatchMulPreprocessing};
use ark_ff::{PrimeField, batch_inversion};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{
    UniformRand,
    collections::BTreeSet,
    rand::{CryptoRng, RngCore},
    vec::Vec,
};
use dock_crypto_utils::{
    randomized_mult_checker::RandomizedMultChecker,
    randomized_pairing_check::RandomizedPairingChecker,
};

pub fn to_bytes<T: CanonicalSerialize>(t: &T) -> Vec<u8> {
    let mut b = Vec::with_capacity(t.compressed_size());
    t.serialize_compressed(&mut b).unwrap();
    b
}

// ---------------------------------------------------------------------------------------------
// Registration
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct IssuerKeys<E: Pairing> {
    pub sk: E::ScalarField,
    pub pk: E::G2Affine,
}

pub fn issuer_keygen<E: Pairing, R: RngCore + CryptoRng>(rng: &mut R) -> IssuerKeys<E> {
    let sk = E::ScalarField::rand(rng);
    let pk = (E::G2Affine::generator() * sk).into_affine();
    IssuerKeys { sk, pk }
}

/// `deserialize_compressed` validates on-curve and subgroup membership. An identity `pk_iss`
/// satisfies every later pairing check, so it is rejected here.
pub fn chain_decode_issuer_key<E: Pairing>(bytes: &[u8]) -> Option<E::G2Affine> {
    let pk = E::G2Affine::deserialize_compressed(bytes).ok()?;
    (!pk.is_zero()).then_some(pk)
}

// ---------------------------------------------------------------------------------------------
// Pi-MIssue
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct IssueRequest<E: Pairing> {
    pub x: Vec<E::G1Affine>,
}

#[derive(Clone, Debug)]
pub struct IssueResponse<E: Pairing> {
    pub blinded: Vec<E::G1Affine>,
    pub com_k: E::G2Affine,
}

#[derive(Clone, Debug)]
pub struct ClientSession<E: Pairing, D: AffineRepr> {
    pub sid: [u8; 32],
    pub eph: Vec<ds::Keypair<D>>,
    pub r: Vec<E::ScalarField>,
    pub x: Vec<E::G1Affine>,
    pub refund: ds::Keypair<D>,
}

/// `X_i = H(pk_e,i)*r_i`.
pub fn client_issue_request<E, D, H, R>(
    rng: &mut R,
    num_tokens: usize,
    ds_base: &D,
) -> (ClientSession<E, D>, IssueRequest<E>)
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
    R: RngCore + CryptoRng,
{
    let mut sid = [0u8; 32];
    rng.fill_bytes(&mut sid);
    let eph = ds::keygen_batch(rng, ds_base, num_tokens);
    let r: Vec<E::ScalarField> = (0..num_tokens).map(|_| E::ScalarField::rand(rng)).collect();
    let blinded: Vec<E::G1> = eph
        .iter()
        .zip(&r)
        .map(|(kp, r_i)| H::hash(&to_bytes(&kp.pk)) * r_i)
        .collect();
    let x = E::G1::normalize_batch(&blinded);
    let refund = ds::keygen(rng, ds_base);
    (
        ClientSession {
            sid,
            eph,
            r,
            x: x.clone(),
            refund,
        },
        IssueRequest { x },
    )
}

/// `sigma~_i = X_i*(k.sk_iss)`, `com_k = pk_iss*k`. One mask for the whole batch, which is what makes
/// the on-chain step `O(1)` in `l`.
pub fn issuer_issue_response<E: Pairing, R: RngCore + CryptoRng>(
    rng: &mut R,
    req: &IssueRequest<E>,
    keys: &IssuerKeys<E>,
) -> (E::ScalarField, IssueResponse<E>) {
    let k = E::ScalarField::rand(rng);
    let com_k = (keys.pk * k).into_affine();
    let ks = (k * keys.sk).into_bigint();
    let proj: Vec<E::G1> = req.x.iter().map(|x| x.mul_bigint(ks)).collect();
    let blinded = E::G1::normalize_batch(&proj);
    (k, IssueResponse { blinded, com_k })
}

/// Contributes `\forall i : e(sigma~_i, h) == e(X_i, com_k)` to `rpc`. The `G2` elements are the same
/// `h` and `com_k` in all `l` equations, so the checker holds them as two groups and settles them as
/// two `G1` MSMs of size `l` against a two-pair multi-miller-loop.
pub fn pairing_contribution_of_blinded<E: Pairing, D: AffineRepr>(
    session: &ClientSession<E, D>,
    resp: &IssueResponse<E>,
    rpc: &mut RandomizedPairingChecker<E>,
) {
    let h = E::G2Affine::generator();
    for (x, m) in session.x.iter().zip(&resp.blinded) {
        rpc.add_sources_g2_affine(m, &h, x, &resp.com_k);
    }
}

pub fn client_verify_blinded<E: Pairing, D: AffineRepr, R: RngCore + CryptoRng>(
    rng: &mut R,
    session: &ClientSession<E, D>,
    resp: &IssueResponse<E>,
) -> bool {
    let mut rpc = RandomizedPairingChecker::<E>::new_using_rng(rng, true);
    pairing_contribution_of_blinded(session, resp, &mut rpc);
    rpc.verify().is_ok()
}

// ---------------------------------------------------------------------------------------------
// Pi-Execute
// ---------------------------------------------------------------------------------------------

/// The client's transaction carries no arithmetic beyond decode. An identity `com_k` makes the
/// blinded signature check vacuous, so the non-identity check is load-bearing.
pub fn chain_execute_client_msg<E: Pairing, D: AffineRepr>(
    com_k_bytes: &[u8],
    pk_ref_bytes: &[u8],
) -> bool {
    let Ok(com_k) = E::G2Affine::deserialize_compressed(com_k_bytes) else {
        return false;
    };
    !com_k.is_zero() && ds::decode_pk::<D>(pk_ref_bytes).is_some()
}

#[derive(Clone, Debug)]
pub struct Reveal<E: Pairing> {
    pub issuer: usize,
    pub k: E::ScalarField,
    pub com_k: E::G2Affine,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RevealCheck {
    /// Windowed table per issuer key, reused across that key's reveals.
    FixedBase,
    /// `RandomizedMultChecker` over `G2`, which merges the repeated `pk_iss` bases and settles the
    /// whole block as one `G2` MSM of size `J + m`.
    Rmc,
}

pub fn build_reveal_tables<E: Pairing>(
    keys: &[E::G2Affine],
    per_key: usize,
) -> Vec<BatchMulPreprocessing<E::G2>> {
    keys.iter()
        .map(|k| BatchMulPreprocessing::new((*k).into(), per_key.max(1)))
        .collect()
}

/// Contributes `pk_iss*k == com_k` to `rmc`.
pub fn reveal_contribute<E: Pairing>(
    reveals: &[Reveal<E>],
    keys: &[E::G2Affine],
    rmc: &mut RandomizedMultChecker<E::G2Affine>,
) {
    for r in reveals {
        rmc.add_1(keys[r.issuer], &r.k, r.com_k);
    }
}

/// `tables` supplied means a warm cache, which is what a node holds since issuer keys are long-lived
/// registry state; `None` charges the build.
pub fn chain_execute_issuer_msg<E: Pairing, R: RngCore + CryptoRng>(
    rng: &mut R,
    reveals: &[Reveal<E>],
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
                    .map(|r| r.k)
                    .collect();
                if ks.is_empty() {
                    return true;
                }
                let got = tables[j].batch_mul(&ks);
                reveals
                    .iter()
                    .filter(|r| r.issuer == j)
                    .map(|r| r.com_k)
                    .eq(got)
            })
        }
        RevealCheck::Rmc => {
            #[allow(deprecated)]
            let mut rmc = RandomizedMultChecker::<E::G2Affine>::new_using_rng(rng);
            reveal_contribute(reveals, keys, &mut rmc);
            rmc.verify().is_ok()
        }
    }
}

#[derive(Clone, Debug)]
pub struct PreToken<E: Pairing, D: AffineRepr> {
    pub alpha: E::G1Affine,
    pub eph: ds::Keypair<D>,
}

/// `alpha_i = sigma~_i*((r_i.k)^-1)`.
pub fn client_unmask<E: Pairing, D: AffineRepr>(
    session: &ClientSession<E, D>,
    resp: &IssueResponse<E>,
    k: E::ScalarField,
) -> Vec<PreToken<E, D>> {
    let mut inv: Vec<E::ScalarField> = session.r.iter().map(|r| *r * k).collect();
    batch_inversion(&mut inv);
    let proj: Vec<E::G1> = resp
        .blinded
        .iter()
        .zip(&inv)
        .map(|(m, s)| m.mul_bigint(s.into_bigint()))
        .collect();
    E::G1::normalize_batch(&proj)
        .into_iter()
        .zip(session.eph.iter().cloned())
        .map(|(alpha, eph)| PreToken { alpha, eph })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// TokGen and Spend
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct Token<E: Pairing, D: AffineRepr> {
    pub pk_e: D,
    pub alpha: E::G1Affine,
    pub gamma: ds::Sig<D>,
}

impl<E: Pairing, D: AffineRepr> PreToken<E, D> {
    pub fn token_gen<R: RngCore + CryptoRng>(
        self,
        rng: &mut R,
        ad: &[u8],
        ds_base: &D,
    ) -> Token<E, D> {
        Token {
            pk_e: self.eph.pk,
            alpha: self.alpha,
            gamma: ds::sign(rng, &self.eph, ad, ds_base),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DsCheck {
    /// `RandomizedMultChecker`, one MSM over the distinct points.
    Rmc,
    /// In DART `gamma` is the extrinsic signature, already verified by the node.
    Skip,
}

/// Contributes the batch's issuer-signature equation to `rpc`. `hs` is the hashed message per token.
/// The `G2` side takes `J + 1` distinct values, `h` and the issuer keys, so the checker holds `J + 1`
/// groups and settles the batch as `J + 1` `G1` MSMs against a `J + 1` pair multi-miller-loop.
pub fn spend_contribute_pairing<E: Pairing>(
    alphas: &[E::G1Affine],
    hs: &[E::G1Affine],
    issuer_of: &[usize],
    keys: &[E::G2Affine],
    rpc: &mut RandomizedPairingChecker<E>,
) {
    let h = E::G2Affine::generator();
    for ((a, h_i), j) in alphas.iter().zip(hs).zip(issuer_of) {
        rpc.add_sources_g2_affine(a, &h, h_i, &keys[*j]);
    }
}

pub fn spend_contribute_ds<E: Pairing, D: AffineRepr>(
    tokens: &[Token<E, D>],
    ad: &[u8],
    ds_base: &D,
    rmc: &mut RandomizedMultChecker<D>,
) {
    for t in tokens {
        ds::add_to_checker(&t.gamma, &t.pk_e, ad, ds_base, rmc);
    }
}

pub fn hash_tokens<E: Pairing, D: AffineRepr, H: HashToG1<E>>(
    tokens: &[Token<E, D>],
) -> Vec<E::G1Affine> {
    tokens.iter().map(|t| H::hash(&to_bytes(&t.pk_e))).collect()
}

pub fn keys_distinct<D: AffineRepr>(pk_e: impl IntoIterator<Item = D>) -> bool {
    let mut seen = BTreeSet::new();
    pk_e.into_iter().all(|p| seen.insert(to_bytes(&p)))
}

/// `\forall i : e(alpha_i, h) == e(H(pk_e,i), pk_iss)` plus `DS.Verify` plus nullifier distinctness,
/// settled as one final exponentiation and one MSM.
pub fn chain_spend<E, D, H, R>(
    rng: &mut R,
    tokens: &[Token<E, D>],
    issuer_of: &[usize],
    keys: &[E::G2Affine],
    ad: &[u8],
    ds_base: &D,
    ds_check: DsCheck,
) -> bool
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
    R: RngCore + CryptoRng,
{
    let hs = hash_tokens::<E, D, H>(tokens);
    if !keys_distinct(tokens.iter().map(|t| t.pk_e)) {
        return false;
    }
    let alphas: Vec<E::G1Affine> = tokens.iter().map(|t| t.alpha).collect();

    let mut rpc = RandomizedPairingChecker::<E>::new_using_rng(rng, true);
    spend_contribute_pairing(&alphas, &hs, issuer_of, keys, &mut rpc);
    if !rpc.verify().is_ok() {
        return false;
    }

    match ds_check {
        DsCheck::Skip => true,
        DsCheck::Rmc => {
            #[allow(deprecated)]
            let mut rmc = RandomizedMultChecker::<D>::new_using_rng(rng);
            spend_contribute_ds(tokens, ad, ds_base, &mut rmc);
            rmc.verify().is_ok()
        }
    }
}

/// Several independent spend batches settled together: one `RandomizedPairingChecker` and one
/// `RandomizedMultChecker` across the whole block.
pub fn chain_block_spend<E, D, H, R>(
    rng: &mut R,
    batches: &[(Vec<Token<E, D>>, Vec<usize>)],
    keys: &[E::G2Affine],
    ad: &[u8],
    ds_base: &D,
) -> bool
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
    R: RngCore + CryptoRng,
{
    let mut rpc = RandomizedPairingChecker::<E>::new_using_rng(rng, true);
    #[allow(deprecated)]
    let mut rmc = RandomizedMultChecker::<D>::new_using_rng(rng);
    let mut seen = BTreeSet::new();
    for (tokens, issuer_of) in batches {
        if !tokens.iter().all(|t| seen.insert(to_bytes(&t.pk_e))) {
            rpc.cancel();
            return false;
        }
        let hs = hash_tokens::<E, D, H>(tokens);
        let alphas: Vec<E::G1Affine> = tokens.iter().map(|t| t.alpha).collect();
        spend_contribute_pairing(&alphas, &hs, issuer_of, keys, &mut rpc);
        spend_contribute_ds(tokens, ad, ds_base, &mut rmc);
    }
    rpc.verify().is_ok() && rmc.verify().is_ok()
}

// ---------------------------------------------------------------------------------------------
// Refund
// ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
pub struct RefundRequest<E: Pairing, D: AffineRepr> {
    pub sid: [u8; 32],
    pub alpha: Vec<E::G1Affine>,
    pub pk_e: Vec<D>,
    pub gamma_ref: ds::Sig<D>,
}

pub fn refund_msg<E: Pairing, D: AffineRepr>(
    sid: &[u8; 32],
    alpha: &[E::G1Affine],
    pk_e: &[D],
) -> Vec<u8> {
    let mut m = sid.to_vec();
    for (a, p) in alpha.iter().zip(pk_e) {
        m.extend_from_slice(&to_bytes(a));
        m.extend_from_slice(&to_bytes(p));
    }
    m
}

/// One signature under `sk_ref` authorizes the whole batch, so refund pays one `DS.Verify` rather
/// than `l_ref`.
pub fn client_refund_request<E: Pairing, D: AffineRepr, R: RngCore + CryptoRng>(
    rng: &mut R,
    session: &ClientSession<E, D>,
    unspent: &[PreToken<E, D>],
    ds_base: &D,
) -> RefundRequest<E, D> {
    let alpha: Vec<E::G1Affine> = unspent.iter().map(|p| p.alpha).collect();
    let pk_e: Vec<D> = unspent.iter().map(|p| p.eph.pk).collect();
    let msg = refund_msg::<E, D>(&session.sid, &alpha, &pk_e);
    let gamma_ref = ds::sign(rng, &session.refund, &msg, ds_base);
    RefundRequest {
        sid: session.sid,
        alpha,
        pk_e,
        gamma_ref,
    }
}

pub fn chain_refund<E, D, H, R>(
    rng: &mut R,
    req: &RefundRequest<E, D>,
    pk_iss: &E::G2Affine,
    pk_ref: &D,
    ds_base: &D,
) -> bool
where
    E: Pairing,
    D: AffineRepr,
    H: HashToG1<E>,
    R: RngCore + CryptoRng,
{
    let msg = refund_msg::<E, D>(&req.sid, &req.alpha, &req.pk_e);
    if !ds::verify(&req.gamma_ref, pk_ref, &msg, ds_base) {
        return false;
    }

    // Fig. 7 checks membership per token and inserts only after the loop, so `l_ref` copies of one
    // token pass. Without this the batch mints `l_ref` units for one token.
    let mut seen = BTreeSet::new();
    if !req.pk_e.iter().all(|p| seen.insert(to_bytes(p))) {
        return false;
    }

    let hs: Vec<E::G1Affine> = req.pk_e.iter().map(|p| H::hash(&to_bytes(p))).collect();
    let mut rpc = RandomizedPairingChecker::<E>::new_using_rng(rng, true);
    let issuer_of = vec![0usize; req.alpha.len()];
    spend_contribute_pairing(
        &req.alpha,
        &hs,
        &issuer_of,
        core::slice::from_ref(pk_iss),
        &mut rpc,
    );
    rpc.verify().is_ok()
}
