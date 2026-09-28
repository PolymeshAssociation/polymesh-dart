//! BAT Protocol A, Fig. 7 of <https://eprint.iacr.org/2026/1074>.
//! This module is the paper's scheme exactly, message = `pk_e`. Denominations are the paper's
//! section 8's pools, one issuer key per denomination.

use crate::{
    error::Error,
    hash::HashToG1,
    signature::{BatchSig, Keypair},
};
use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::{
    PrimeField, batch_inversion,
    field_hashers::{DefaultFieldHasher, HashToField},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{UniformRand, collections::BTreeSet, vec, vec::Vec};
use core::mem;
use dock_crypto_utils::{
    randomized_mult_checker::RandomizedMultChecker,
    randomized_pairing_check::{RandomizedPairingChecker, RandomizedPairingCheckerGuard},
};
use rand_core::CryptoRngCore;
use sha2::Sha256;
use zeroize::{Zeroize, ZeroizeOnDrop};

pub type SessionId = [u8; 32];

const REFUND_MSG_PREFIX: &[u8] = b"POLYMESH-BAT-V01-REFUND";
const ISSUER_KEY_DST: &[u8] = b"POLYMESH-BAT-V01-ISSUER-KEY";

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct IssuerKeypair<E: Pairing> {
    pub sk: E::ScalarField,
    #[zeroize(skip)]
    pub pk: E::G2Affine,
}

impl<E: Pairing> IssuerKeypair<E> {
    pub fn new<R: CryptoRngCore>(rng: &mut R) -> Self {
        let sk = E::ScalarField::rand(rng);
        Self::from_secret(sk)
    }

    /// `sk` is the seed hashed to the scalar field.
    pub fn new_with_seed(seed: &[u8]) -> Self {
        let hasher =
            <DefaultFieldHasher<Sha256, 128> as HashToField<E::ScalarField>>::new(ISSUER_KEY_DST);
        let [sk] = hasher.hash_to_field::<1>(seed);
        Self::from_secret(sk)
    }

    fn from_secret(sk: E::ScalarField) -> Self {
        let pk = (E::G2Affine::generator() * sk).into_affine();
        Self { sk, pk }
    }
}

/// Applied by the issuer to every blinded signature of a session, called `k` in the paper.
#[derive(
    Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct SignatureMask<E: Pairing>(pub E::ScalarField);

/// Called `pk_iss*k` in the paper.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommitmentToSigMask<E: Pairing>(pub E::G2Affine);

impl<E: Pairing> CommitmentToSigMask<E> {
    pub fn new(mask: &SignatureMask<E>, pk_iss: &E::G2Affine) -> Self {
        Self((*pk_iss * mask.0).into_affine())
    }
}

/// Off-chain issuance request sent by the client to the issuer
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct IssueRequest<E: Pairing> {
    pub sid: SessionId,
    /// Called `X` in the paper
    pub blinded_public_keys: Vec<E::G1Affine>,
}

/// Off-chain issuance response sent to the client by the issuer
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct IssueResponse<E: Pairing> {
    pub blinded: Vec<E::G1Affine>,
    /// Called `com_k` in the paper.
    pub commitment_to_sig_mask: CommitmentToSigMask<E>,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct ClientSession<E: Pairing, G: AffineRepr> {
    #[zeroize(skip)]
    pub sid: SessionId,
    pub eph: Vec<Keypair<G>>,
    /// Caller `r` in paper
    pub public_key_blinders: Vec<E::ScalarField>,
    pub refund: Keypair<G>,
}

impl<E: Pairing, G: AffineRepr> ClientSession<E, G> {
    /// `X_i = H(pk_e,i)*r_i`.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        num_tokens: u32,
        sig_base: &G,
    ) -> Result<(Self, IssueRequest<E>), Error>
    where
        E: HashToG1,
    {
        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if num_tokens == 0 {
            return Err(Error::Empty);
        }
        let mut sid = [0u8; 32];
        rng.fill_bytes(&mut sid);
        let eph = Keypair::new_batch(rng, sig_base, num_tokens as usize);
        let public_key_blinders = (0..num_tokens)
            .map(|_| E::ScalarField::rand(rng))
            .collect::<Vec<_>>();
        let blinded = eph
            .iter()
            .zip(&public_key_blinders)
            .map(|(kp, r_i)| E::hash_to_g1(&to_bytes(&kp.pk)) * r_i)
            .collect::<Vec<_>>();
        let blinded_public_keys = E::G1::normalize_batch(&blinded);
        let refund = Keypair::new(rng, sig_base);
        Ok((
            Self {
                sid,
                eph,
                public_key_blinders,
                refund,
            },
            IssueRequest {
                sid,
                blinded_public_keys,
            },
        ))
    }

    /// `alpha_i = sigma~_i*((r_i.k)^-1)`.
    pub fn unmask(
        mut self,
        response: &IssueResponse<E>,
        mask: &SignatureMask<E>,
    ) -> Result<(Vec<PreToken<E, G>>, RefundKey<G>), Error> {
        if response.blinded.len() != self.public_key_blinders.len() {
            return Err(Error::LengthMismatch);
        }
        let mut inv = self
            .public_key_blinders
            .iter()
            .map(|r| *r * mask.0)
            .collect::<Vec<_>>();
        batch_inversion(&mut inv);
        let tokens = response
            .blinded
            .iter()
            .zip(&inv)
            .map(|(m, s)| m.mul_bigint(s.into_bigint()))
            .collect::<Vec<_>>();
        inv.zeroize();
        let tokens = E::G1::normalize_batch(&tokens)
            .into_iter()
            .zip(mem::take(&mut self.eph))
            .map(|(unblinded_sig, eph)| PreToken { unblinded_sig, eph })
            .collect();
        let refund_key = RefundKey {
            sid: self.sid,
            keypair: self.refund.clone(),
        };
        Ok((tokens, refund_key))
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct IssuerSession<E: Pairing> {
    #[zeroize(skip)]
    pub sid: SessionId,
    /// Called `k` in the paper.
    pub signature_mask: SignatureMask<E>,
    /// Called `com_k` in the paper.
    #[zeroize(skip)]
    pub commitment_to_sig_mask: CommitmentToSigMask<E>,
    /// Number of blinded signatures made under the mask.
    #[zeroize(skip)]
    pub count: u32,
}

impl<E: Pairing> IssuerSession<E> {
    /// `sigma~_i = X_i*(k.sk_iss)`, `com_k = pk_iss*k`.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        request: &IssueRequest<E>,
        keys: &IssuerKeypair<E>,
    ) -> Result<(Self, IssueResponse<E>), Error> {
        if request.blinded_public_keys.is_empty() {
            return Err(Error::Empty);
        }
        let count =
            u32::try_from(request.blinded_public_keys.len()).map_err(|_| Error::TooManyTokens)?;
        let signature_mask = SignatureMask::<E>(E::ScalarField::rand(rng));
        let commitment_to_sig_mask = CommitmentToSigMask::new(&signature_mask, &keys.pk);
        let mut ks = (signature_mask.0 * keys.sk).into_bigint();
        // TODO: Following can benefit from Eisenstein encoding since `ks` is same.
        let proj = request
            .blinded_public_keys
            .iter()
            .map(|x| x.mul_bigint(ks))
            .collect::<Vec<_>>();
        ks.zeroize();
        let response = IssueResponse {
            blinded: E::G1::normalize_batch(&proj),
            commitment_to_sig_mask: commitment_to_sig_mask.clone(),
        };
        let session = Self {
            sid: request.sid,
            signature_mask,
            commitment_to_sig_mask,
            count,
        };
        Ok((session, response))
    }

    /// Reveal the signature mask once satisfied with the client's request.
    pub fn reveal<G: AffineRepr>(
        self,
        request: &OnChainIssuanceRequest<E, G>,
    ) -> Result<Reveal<E>, Error> {
        if request.sid != self.sid
            || request.count != self.count
            || request.commitment_to_sig_mask != self.commitment_to_sig_mask
        {
            return Err(Error::SessionMismatch);
        }
        Ok(Reveal {
            sid: self.sid,
            signature_mask: self.signature_mask.clone(),
        })
    }
}

impl<E: Pairing> IssueResponse<E> {
    /// `\forall i : e(sigma~_i, h) == e(X_i, com_k)`.
    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        request: &IssueRequest<E>,
        rpc: Option<&mut RandomizedPairingChecker<E>>,
    ) -> Result<(), Error> {
        if request.blinded_public_keys.is_empty() {
            return Err(Error::Empty);
        }
        if self.blinded.len() != request.blinded_public_keys.len() {
            return Err(Error::LengthMismatch);
        }
        let com_k = self.commitment_to_sig_mask.0;
        if com_k.is_zero() {
            return Err(Error::IdentityPoint);
        }
        let h = E::G2Affine::generator();
        let add = |rpc: &mut RandomizedPairingChecker<E>| {
            for (x, m) in request.blinded_public_keys.iter().zip(&self.blinded) {
                rpc.add_sources_g2_affine(m, &h, x, &com_k);
            }
        };
        match rpc {
            Some(rpc) => {
                add(rpc);
                Ok(())
            }
            None => RandomizedPairingCheckerGuard::new_using_rng(rng, true).with_err(
                Error::InvalidIssuerSignature,
                |rpc| {
                    add(rpc);
                    Ok(())
                },
            ),
        }
    }
}

/// The client's half of Π-Execute. Its payment is held until the issuer posts the mask.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct OnChainIssuanceRequest<E: Pairing, G: AffineRepr> {
    pub sid: SessionId,
    pub pk_ref: G,
    /// Called `com_k` in the paper.
    pub commitment_to_sig_mask: CommitmentToSigMask<E>,
    pub count: u32,
}

impl<E: Pairing, G: AffineRepr> OnChainIssuanceRequest<E, G> {
    pub fn new(session: &ClientSession<E, G>, response: &IssueResponse<E>) -> Self {
        Self {
            sid: session.sid,
            pk_ref: session.refund.pk,
            commitment_to_sig_mask: response.commitment_to_sig_mask.clone(),
            count: session.public_key_blinders.len() as u32,
        }
    }

    /// At this point, chain won't have the signature mask used by issuer.
    pub fn verify(&self) -> Result<(), Error> {
        if self.count == 0 {
            return Err(Error::Empty);
        }
        if self.commitment_to_sig_mask.0.is_zero() || self.pk_ref.is_zero() {
            return Err(Error::IdentityPoint);
        }
        Ok(())
    }
}

/// The issuer's half of Π-Execute.
#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Reveal<E: Pairing> {
    pub sid: SessionId,
    /// Called `k` in the paper.
    pub signature_mask: SignatureMask<E>,
}

impl<E: Pairing> Reveal<E> {
    /// Check that issuer posted the correct mask
    pub fn verify(
        &self,
        pk_iss: &E::G2Affine,
        commitment: &CommitmentToSigMask<E>,
        rmc: Option<&mut RandomizedMultChecker<E::G2Affine>>,
    ) -> Result<(), Error> {
        if pk_iss.is_zero() || commitment.0.is_zero() {
            return Err(Error::IdentityPoint);
        }
        match rmc {
            Some(rmc) => {
                rmc.add_1(*pk_iss, &self.signature_mask.0, commitment.0);
                Ok(())
            }
            None => {
                if CommitmentToSigMask::new(&self.signature_mask, pk_iss) == *commitment {
                    Ok(())
                } else {
                    Err(Error::InvalidSignatureMask)
                }
            }
        }
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct RefundKey<G: AffineRepr> {
    #[zeroize(skip)]
    pub sid: SessionId,
    pub keypair: Keypair<G>,
}

/// This is not the token to be sent on chain as it contains the secret key as well.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop)]
pub struct PreToken<E: Pairing, G: AffineRepr> {
    /// Called `alpha` in the paper.
    pub unblinded_sig: E::G1Affine,
    pub eph: Keypair<G>,
}

/// The token to be sent on chain. Signature (called `gamma` in the paper) is not here as  one batch  
/// Schnorr covers every token in a payment, so it's sent alongside the list.
#[derive(
    Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct Token<E: Pairing, G: AffineRepr> {
    pub pk_e: G,
    /// Called `alpha` in the paper.
    pub unblinded_sig: E::G1Affine,
}

impl<E: Pairing, G: AffineRepr> PreToken<E, G> {
    pub fn token(&self) -> Token<E, G> {
        Token {
            pk_e: self.eph.pk,
            unblinded_sig: self.unblinded_sig,
        }
    }
}

impl<E: Pairing, G: AffineRepr> Token<E, G> {
    /// `H(pk_e)`, the message the issuer signed.
    pub fn hash(&self) -> E::G1Affine
    where
        E: HashToG1,
    {
        E::hash_to_g1(&to_bytes(&self.pk_e))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct Payment<E: Pairing, G: AffineRepr> {
    pub tokens: Vec<Token<E, G>>,
    /// Called `gamma` in the paper. Covers the ordered `pk_e` of `tokens`.
    pub signature: BatchSig<G>,
}

impl<E: Pairing, G: AffineRepr> Payment<E, G> {
    /// `msg` is the arbitrary message signed during paying. Could be hash to another txn or
    /// anything this payment is being bound to.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pre: &[PreToken<E, G>],
        msg: &[u8],
        sig_base: &G,
    ) -> Result<Self, Error> {
        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        if !keys_distinct(pre.iter().map(|p| p.eph.pk)) {
            return Err(Error::DuplicateKey);
        }
        let keypairs = pre.iter().map(|p| p.eph.clone()).collect::<Vec<_>>();
        let signature = BatchSig::new(rng, &keypairs, msg, sig_base)?;
        Ok(Self {
            tokens: pre.iter().map(|p| p.token()).collect(),
            signature,
        })
    }

    /// `\forall i : e(alpha_i, h) == e(H(pk_e_i), pk_iss_i)` plus the signature plus nullifier
    /// (`pk_e_i`) distinctness. `pk_iss_i` is the issuer key of each token, in order.
    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        pk_iss: &[E::G2Affine],
        msg: &[u8],
        sig_base: &G,
        checkers: Option<(
            &mut RandomizedPairingChecker<E>,
            &mut RandomizedMultChecker<G>,
        )>,
    ) -> Result<(), Error>
    where
        E: HashToG1,
    {
        if self.tokens.is_empty() {
            return Err(Error::Empty);
        }
        if pk_iss.len() != self.tokens.len() {
            return Err(Error::LengthMismatch);
        }
        let signers = self.tokens.iter().map(|t| t.pk_e).collect::<Vec<_>>();
        verify_tokens::<E, G, R>(
            rng,
            &self.tokens,
            pk_iss,
            &self.signature,
            &signers,
            msg,
            sig_base,
            checkers,
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, CanonicalSerialize, CanonicalDeserialize)]
pub struct RefundRequest<E: Pairing, G: AffineRepr> {
    pub sid: SessionId,
    pub tokens: Vec<Token<E, G>>,
    /// Called `gamma_ref` in the paper.
    pub signature: BatchSig<G>,
}

impl<E: Pairing, G: AffineRepr> RefundRequest<E, G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        refund_key: &RefundKey<G>,
        unspent: &[PreToken<E, G>],
        sig_base: &G,
    ) -> Result<Self, Error> {
        #[cfg(not(feature = "ignore_prover_input_sanitation"))]
        {
            if unspent.is_empty() {
                return Err(Error::Empty);
            }
            if !keys_distinct(unspent.iter().map(|p| p.eph.pk)) {
                return Err(Error::DuplicateKey);
            }
        }
        let tokens = unspent.iter().map(|p| p.token()).collect::<Vec<_>>();
        let msg = Self::message(&refund_key.sid, &tokens);
        let signature = BatchSig::new(
            rng,
            core::slice::from_ref(&refund_key.keypair),
            &msg,
            sig_base,
        )?;
        Ok(Self {
            sid: refund_key.sid,
            tokens,
            signature,
        })
    }

    /// `pk_iss` and `pk_ref` are the ones stored with the session, not anything the refunder supplies.
    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        pk_iss: &E::G2Affine,
        pk_ref: &G,
        sig_base: &G,
        checkers: Option<(
            &mut RandomizedPairingChecker<E>,
            &mut RandomizedMultChecker<G>,
        )>,
    ) -> Result<(), Error>
    where
        E: HashToG1,
    {
        if self.tokens.is_empty() {
            return Err(Error::Empty);
        }
        if pk_ref.is_zero() {
            return Err(Error::IdentityPoint);
        }
        let msg = Self::message(&self.sid, &self.tokens);
        verify_tokens::<E, G, R>(
            rng,
            &self.tokens,
            &vec![*pk_iss; self.tokens.len()],
            &self.signature,
            core::slice::from_ref(pk_ref),
            &msg,
            sig_base,
            checkers,
        )
    }

    /// The bytes `signature` covers.
    pub fn message(sid: &SessionId, tokens: &[Token<E, G>]) -> Vec<u8> {
        let mut m = REFUND_MSG_PREFIX.to_vec();
        m.extend_from_slice(sid);
        for t in tokens {
            m.extend_from_slice(&to_bytes(&t.unblinded_sig));
            m.extend_from_slice(&to_bytes(&t.pk_e));
        }
        m
    }
}

/// Issuer signatures of `tokens` under `pk_iss`, plus `signature` over `signers`. Callers check that
/// `pk_iss` has one key per token.
fn verify_tokens<E: HashToG1, G: AffineRepr, R: CryptoRngCore>(
    rng: &mut R,
    tokens: &[Token<E, G>],
    pk_iss: &[E::G2Affine],
    signature: &BatchSig<G>,
    signers: &[G],
    msg: &[u8],
    sig_base: &G,
    checkers: Option<(
        &mut RandomizedPairingChecker<E>,
        &mut RandomizedMultChecker<G>,
    )>,
) -> Result<(), Error> {
    // The checker skips a pair with an identity element, so an identity `pk_iss` and `alpha` would
    // pass unchecked.
    if tokens
        .iter()
        .any(|t| t.pk_e.is_zero() || t.unblinded_sig.is_zero())
        || pk_iss.iter().any(|pk| pk.is_zero())
    {
        return Err(Error::IdentityPoint);
    }
    if !keys_distinct(tokens.iter().map(|t| t.pk_e)) {
        return Err(Error::DuplicateKey);
    }
    let h = E::G2Affine::generator();
    let add = |rpc: &mut RandomizedPairingChecker<E>| {
        for (t, pk) in tokens.iter().zip(pk_iss) {
            rpc.add_sources_g2_affine(&t.unblinded_sig, &h, &t.hash(), pk);
        }
    };
    match checkers {
        Some((rpc, rmc)) => {
            add(rpc);
            signature.verify(signers, msg, sig_base, Some(rmc))
        }
        None => {
            signature.verify(signers, msg, sig_base, None)?;
            RandomizedPairingCheckerGuard::new_using_rng(rng, true).with_err(
                Error::InvalidIssuerSignature,
                |rpc| {
                    add(rpc);
                    Ok(())
                },
            )
        }
    }
}

pub fn to_bytes<T: CanonicalSerialize>(t: &T) -> Vec<u8> {
    let mut b = Vec::with_capacity(t.compressed_size());
    t.serialize_compressed(&mut b).unwrap();
    b
}

pub fn keys_distinct<G: AffineRepr>(pk_e: impl IntoIterator<Item = G>) -> bool {
    let mut seen = BTreeSet::new();
    pk_e.into_iter().all(|p| seen.insert(to_bytes(&p)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::{SeedableRng, rngs::StdRng};

    type G = ark_pallas::Affine;

    /// Runs a function on every enabled pairing curve.
    macro_rules! on_each_curve {
        ($f:ident) => {
            #[cfg(feature = "bn254")]
            $f::<ark_bn254::Bn254>();
            #[cfg(feature = "bls12-381")]
            $f::<ark_bls12_381::Bls12_381>();
        };
    }

    struct Issued<E: Pairing> {
        session: ClientSession<E, G>,
        request: IssueRequest<E>,
        issuer_session: IssuerSession<E>,
        response: IssueResponse<E>,
    }

    fn issue<E: Pairing>(rng: &mut StdRng, keys: &IssuerKeypair<E>, count: u32) -> Issued<E>
    where
        E: HashToG1,
    {
        let (session, request) = ClientSession::new(rng, count, &G::generator()).unwrap();
        let (issuer_session, response) = IssuerSession::new(rng, &request, keys).unwrap();
        response.verify(rng, &request, None).unwrap();
        Issued {
            session,
            request,
            issuer_session,
            response,
        }
    }

    fn unmask<E: Pairing>(issued: Issued<E>) -> (Vec<PreToken<E, G>>, RefundKey<G>) {
        let request = OnChainIssuanceRequest::new(&issued.session, &issued.response);
        let reveal = issued.issuer_session.reveal(&request).unwrap();
        issued
            .session
            .unmask(&issued.response, &reveal.signature_mask)
            .unwrap()
    }

    fn issue_response_rejects_tampering_on<E: Pairing>()
    where
        E: HashToG1,
    {
        let mut rng = StdRng::seed_from_u64(0);
        let keys = IssuerKeypair::<E>::new(&mut rng);
        let issued = issue(&mut rng, &keys, 3);

        let mut reordered = issued.response.clone();
        reordered.blinded.swap(0, 2);
        assert_eq!(
            reordered.verify(&mut rng, &issued.request, None),
            Err(Error::InvalidIssuerSignature)
        );

        let mut other_mask = issued.response.clone();
        other_mask.commitment_to_sig_mask =
            CommitmentToSigMask::new(&SignatureMask(E::ScalarField::rand(&mut rng)), &keys.pk);
        assert_eq!(
            other_mask.verify(&mut rng, &issued.request, None),
            Err(Error::InvalidIssuerSignature)
        );
    }

    #[test]
    fn issue_response_rejects_tampering() {
        // The masked signatures must be in the order of the blinded keys and under the committed mask.
        on_each_curve!(issue_response_rejects_tampering_on);
    }

    fn unmask_with_wrong_mask_on<E: Pairing>()
    where
        E: HashToG1,
    {
        let mut rng = StdRng::seed_from_u64(1);
        let sig_base = G::generator();
        let keys = IssuerKeypair::<E>::new(&mut rng);
        let issued = issue(&mut rng, &keys, 3);

        let wrong = SignatureMask(E::ScalarField::rand(&mut rng));
        let (pre, _) = issued.session.unmask(&issued.response, &wrong).unwrap();
        let payment = Payment::new(&mut rng, &pre, b"msg", &sig_base).unwrap();
        assert_eq!(
            payment.verify(&mut rng, &[keys.pk; 3], b"msg", &sig_base, None),
            Err(Error::InvalidIssuerSignature)
        );
    }

    #[test]
    fn unmask_with_wrong_mask() {
        // Unmasking succeeds with any mask, but tokens unmasked with the wrong one don't verify.
        on_each_curve!(unmask_with_wrong_mask_on);
    }

    fn reveal_and_execute_request_rejections_on<E: Pairing>()
    where
        E: HashToG1,
    {
        let mut rng = StdRng::seed_from_u64(2);
        let keys = IssuerKeypair::<E>::new(&mut rng);
        let first = issue(&mut rng, &keys, 2);
        let second = issue(&mut rng, &keys, 2);

        let request = OnChainIssuanceRequest::new(&first.session, &first.response);
        let commitment = request.commitment_to_sig_mask.clone();
        let reveal = first.issuer_session.reveal(&request).unwrap();
        reveal.verify(&keys.pk, &commitment, None).unwrap();

        let identity = CommitmentToSigMask(E::G2Affine::zero());
        assert_eq!(
            reveal.verify(&E::G2Affine::zero(), &commitment, None),
            Err(Error::IdentityPoint)
        );
        assert_eq!(
            reveal.verify(&keys.pk, &identity, None),
            Err(Error::IdentityPoint)
        );

        let other = second
            .issuer_session
            .reveal(&OnChainIssuanceRequest::new(
                &second.session,
                &second.response,
            ))
            .unwrap();
        assert_eq!(
            other.verify(&keys.pk, &commitment, None),
            Err(Error::InvalidSignatureMask)
        );

        let mut zero_com = request;
        zero_com.commitment_to_sig_mask = identity;
        assert_eq!(zero_com.verify(), Err(Error::IdentityPoint));
    }

    #[test]
    fn reveal_and_execute_request_rejections() {
        // Identity keys or commitments, and a mask from another session, are rejected.
        on_each_curve!(reveal_and_execute_request_rejections_on);
    }

    fn refund_binding_on<E: Pairing>()
    where
        E: HashToG1,
    {
        let mut rng = StdRng::seed_from_u64(3);
        let sig_base = G::generator();
        let keys = IssuerKeypair::<E>::new(&mut rng);
        let (pre, refund_key) = unmask(issue(&mut rng, &keys, 3));
        let (_, other_refund_key) = unmask(issue(&mut rng, &keys, 1));
        let pk_ref = refund_key.keypair.pk;
        let verify = |rng: &mut StdRng, req: &RefundRequest<E, G>| {
            req.verify(rng, &keys.pk, &pk_ref, &sig_base, None)
        };

        let refund = RefundRequest::new(&mut rng, &refund_key, &pre, &sig_base).unwrap();
        verify(&mut rng, &refund).unwrap();

        let other_key = RefundRequest::new(&mut rng, &other_refund_key, &pre, &sig_base).unwrap();
        assert_eq!(verify(&mut rng, &other_key), Err(Error::InvalidSignature));

        let mut other_sid = refund.clone();
        other_sid.sid = other_refund_key.sid;
        assert_eq!(verify(&mut rng, &other_sid), Err(Error::InvalidSignature));

        let mut dropped = refund.clone();
        dropped.tokens.pop();
        assert_eq!(verify(&mut rng, &dropped), Err(Error::InvalidSignature));

        let mut swapped = refund.clone();
        let sig = swapped.tokens[0].unblinded_sig;
        swapped.tokens[0].unblinded_sig = swapped.tokens[1].unblinded_sig;
        swapped.tokens[1].unblinded_sig = sig;
        assert_eq!(verify(&mut rng, &swapped), Err(Error::InvalidSignature));

        // Signed again after the swap, so only the issuer signatures are wrong.
        let mut swapped_pre = pre.clone();
        swapped_pre[0].unblinded_sig = pre[1].unblinded_sig;
        swapped_pre[1].unblinded_sig = pre[0].unblinded_sig;
        let resigned = RefundRequest::new(&mut rng, &refund_key, &swapped_pre, &sig_base).unwrap();
        assert_eq!(
            verify(&mut rng, &resigned),
            Err(Error::InvalidIssuerSignature)
        );
    }

    #[test]
    fn refund_binding() {
        // The refund signature binds the session and every token, and the tokens must carry their
        // own issuer signatures.
        on_each_curve!(refund_binding_on);
    }

    fn empty_refund_on<E: Pairing>()
    where
        E: HashToG1,
    {
        let mut rng = StdRng::seed_from_u64(4);
        let sig_base = G::generator();
        let keys = IssuerKeypair::<E>::new(&mut rng);
        let (_, refund_key) = unmask(issue(&mut rng, &keys, 2));
        let msg = RefundRequest::<E, G>::message(&refund_key.sid, &[]);
        let empty = RefundRequest::<E, G> {
            sid: refund_key.sid,
            tokens: vec![],
            signature: BatchSig::new(&mut rng, &[refund_key.keypair.clone()], &msg, &sig_base)
                .unwrap(),
        };
        assert_eq!(
            empty.verify(&mut rng, &keys.pk, &refund_key.keypair.pk, &sig_base, None),
            Err(Error::Empty)
        );
    }

    #[test]
    fn empty_refund() {
        // A refund of no tokens is rejected even when properly signed.
        on_each_curve!(empty_refund_on);
    }

    fn underpaid_reveal_on<E: Pairing>()
    where
        E: HashToG1,
    {
        let mut rng = StdRng::seed_from_u64(9);
        let sig_base = G::generator();
        let keys = IssuerKeypair::<E>::new(&mut rng);
        let issued = issue(&mut rng, &keys, 3);

        let mut underpaid = OnChainIssuanceRequest::new(&issued.session, &issued.response);
        underpaid.count -= 1;
        underpaid.verify().unwrap();
        assert!(matches!(
            issued.issuer_session.clone().reveal(&underpaid),
            Err(Error::SessionMismatch)
        ));

        // The mask posted anyway opens the commitment, and the client unmasks every token.
        let reveal = Reveal {
            sid: issued.issuer_session.sid,
            signature_mask: issued.issuer_session.signature_mask.clone(),
        };
        reveal
            .verify(&keys.pk, &underpaid.commitment_to_sig_mask, None)
            .unwrap();
        let (pre, _) = issued
            .session
            .unmask(&issued.response, &reveal.signature_mask)
            .unwrap();
        assert_eq!(pre.len() as u32, underpaid.count + 1);
        Payment::new(&mut rng, &pre, b"msg", &sig_base)
            .unwrap()
            .verify(&mut rng, &[keys.pk; 3], b"msg", &sig_base, None)
            .unwrap();
    }

    #[test]
    fn underpaid_reveal() {
        // The issuer refuses a request paying for fewer tokens than it signed. Nothing on chain
        // catches it.
        on_each_curve!(underpaid_reveal_on);
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    fn prover_input_sanitation_on<E: Pairing>()
    where
        E: HashToG1,
    {
        let mut rng = StdRng::seed_from_u64(5);
        let sig_base = G::generator();
        let keys = IssuerKeypair::<E>::new(&mut rng);
        let (pre, refund_key) = unmask(issue(&mut rng, &keys, 2));
        let dup = [pre[0].clone(), pre[0].clone(), pre[1].clone()];

        assert!(matches!(
            ClientSession::<E, G>::new(&mut rng, 0, &sig_base),
            Err(Error::Empty)
        ));
        assert_eq!(
            Payment::new(&mut rng, &dup, b"msg", &sig_base),
            Err(Error::DuplicateKey)
        );
        assert_eq!(
            RefundRequest::new(&mut rng, &refund_key, &dup, &sig_base),
            Err(Error::DuplicateKey)
        );
        assert_eq!(
            RefundRequest::<E, G>::new(&mut rng, &refund_key, &[], &sig_base),
            Err(Error::Empty)
        );
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    #[test]
    fn prover_input_sanitation() {
        // The client refuses to make a session of no tokens, or a payment or refund that repeats or
        // lacks tokens.
        on_each_curve!(prover_input_sanitation_on);
    }

    // Run these tests as cargo test --features=ignore_prover_input_sanitation input_sanitation_disabled
    #[cfg(feature = "ignore_prover_input_sanitation")]
    mod input_sanitation_disabled {
        use super::*;
        use dock_crypto_utils::randomized_mult_checker::RandomizedMultCheckerGuard;

        /// Runs `f` with both checkers as args.
        fn with_checkers<E: Pairing>(
            rng: &mut StdRng,
            f: impl FnOnce(
                &mut StdRng,
                (
                    &mut RandomizedPairingChecker<E>,
                    &mut RandomizedMultChecker<G>,
                ),
            ) -> Result<(), Error>,
        ) -> Result<(), Error> {
            RandomizedPairingCheckerGuard::<E>::new_using_rng(rng, true).with_err(
                Error::InvalidIssuerSignature,
                |rpc| {
                    RandomizedMultCheckerGuard::<G>::new_using_rng(rng)
                        .with_err(Error::InvalidSignature, |rmc| f(rng, (rpc, rmc)))
                },
            )
        }

        fn payment_with_duplicate_tokens_on<E: Pairing>()
        where
            E: HashToG1,
        {
            let mut rng = StdRng::seed_from_u64(6);
            let sig_base = G::generator();
            let keys = IssuerKeypair::<E>::new(&mut rng);
            let (pre, _) = unmask(issue(&mut rng, &keys, 2));
            let dup = [pre[0].clone(), pre[0].clone(), pre[1].clone()];
            let pk_iss = [keys.pk; 3];

            let payment = Payment::new(&mut rng, &dup, b"msg", &sig_base).unwrap();
            // The signature over the repeated key is valid on its own.
            let signers = payment.tokens.iter().map(|t| t.pk_e).collect::<Vec<_>>();
            payment
                .signature
                .verify(&signers, b"msg", &sig_base, None)
                .unwrap();
            assert_eq!(
                payment.verify(&mut rng, &pk_iss, b"msg", &sig_base, None),
                Err(Error::DuplicateKey)
            );
            assert_eq!(
                with_checkers::<E>(&mut rng, |rng, checkers| {
                    payment.verify(rng, &pk_iss, b"msg", &sig_base, Some(checkers))
                }),
                Err(Error::DuplicateKey)
            );
        }

        #[test]
        fn payment_with_duplicate_tokens() {
            // A payment that spends one token twice is rejected with and without checkers.
            on_each_curve!(payment_with_duplicate_tokens_on);
        }

        fn refund_with_duplicate_or_no_tokens_on<E: Pairing>()
        where
            E: HashToG1,
        {
            let mut rng = StdRng::seed_from_u64(7);
            let sig_base = G::generator();
            let keys = IssuerKeypair::<E>::new(&mut rng);
            let (pre, refund_key) = unmask(issue(&mut rng, &keys, 2));
            let pk_ref = refund_key.keypair.pk;
            let dup = [pre[0].clone(), pre[0].clone(), pre[1].clone()];

            let refund = RefundRequest::new(&mut rng, &refund_key, &dup, &sig_base).unwrap();
            assert_eq!(
                refund.verify(&mut rng, &keys.pk, &pk_ref, &sig_base, None),
                Err(Error::DuplicateKey)
            );
            assert_eq!(
                with_checkers::<E>(&mut rng, |rng, checkers| {
                    refund.verify(rng, &keys.pk, &pk_ref, &sig_base, Some(checkers))
                }),
                Err(Error::DuplicateKey)
            );

            let empty = RefundRequest::<E, G>::new(&mut rng, &refund_key, &[], &sig_base).unwrap();
            assert_eq!(
                empty.verify(&mut rng, &keys.pk, &pk_ref, &sig_base, None),
                Err(Error::Empty)
            );
        }

        #[test]
        fn refund_with_duplicate_or_no_tokens() {
            // A refund that repeats a token or has none is rejected.
            on_each_curve!(refund_with_duplicate_or_no_tokens_on);
        }

        fn session_with_no_tokens_on<E: Pairing>()
        where
            E: HashToG1,
        {
            let mut rng = StdRng::seed_from_u64(8);
            let keys = IssuerKeypair::<E>::new(&mut rng);
            let (session, request) =
                ClientSession::<E, G>::new(&mut rng, 0, &G::generator()).unwrap();
            assert!(matches!(
                IssuerSession::new(&mut rng, &request, &keys),
                Err(Error::Empty)
            ));

            let mask = SignatureMask(E::ScalarField::rand(&mut rng));
            let response = IssueResponse {
                blinded: vec![],
                commitment_to_sig_mask: CommitmentToSigMask::new(&mask, &keys.pk),
            };
            assert_eq!(response.verify(&mut rng, &request, None), Err(Error::Empty));
            assert_eq!(
                OnChainIssuanceRequest::new(&session, &response).verify(),
                Err(Error::Empty)
            );
        }

        #[test]
        fn session_with_no_tokens() {
            // The issuer, the client's check of the response and the chain all reject an empty
            // session.
            on_each_curve!(session_with_no_tokens_on);
        }
    }
}
