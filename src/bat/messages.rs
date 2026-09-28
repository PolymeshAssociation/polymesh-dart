//! What goes on chain, and the checks the chain runs on it.

use ark_std::{
    collections::{BTreeMap, BTreeSet},
    vec::Vec,
};
use bounded_collections::{BoundedVec, Get};
use codec::{Decode, DecodeWithMemTracking, Encode, MaxEncodedLen};
use rand_core::CryptoRngCore;
use scale_info::TypeInfo;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use polymesh_bat::protocol::{
    CommitmentToSigMask, OnChainIssuanceRequest, Payment, RefundRequest, Reveal, SignatureMask,
    Token,
};

use super::*;

/// Issuer keys the pallet treats as spendable. A retired key should look up as `None`.
pub trait BatIssuerKeyLookup {
    fn bat_issuer_key(&self, id: BatIssuerKeyId) -> Option<BatIssuerPublicKey>;
}

impl BatIssuerKeyLookup for BTreeMap<BatIssuerKeyId, BatIssuerPublicKey> {
    fn bat_issuer_key(&self, id: BatIssuerKeyId) -> Option<BatIssuerPublicKey> {
        self.get(&id).copied()
    }
}

/// The client's half of Π-Execute, posted with the payment for `count` tokens.
#[derive(
    Copy,
    Clone,
    Debug,
    PartialEq,
    Eq,
    Encode,
    Decode,
    DecodeWithMemTracking,
    MaxEncodedLen,
    TypeInfo,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatOnChainIssuanceRequest {
    #[cfg_attr(feature = "serde", serde(with = "human_hex"))]
    pub sid: BatSessionId,
    pub issuer: BatIssuerKeyId,
    pub pk_ref: BatRefundPublicKey,
    /// Called `com_k` in the paper.
    pub commitment_to_sig_mask: BatCommitmentToSigMask,
    pub count: u32,
}

impl BatOnChainIssuanceRequest {
    pub fn verify<T: BatLimits>(&self) -> Result<(), Error> {
        if self.count > T::MaxBatTokensPerSession::get() {
            return Err(polymesh_bat::Error::TooManyTokens.into());
        }
        self.to_inner()?.verify()?;
        Ok(())
    }

    pub fn from_inner(
        issuer: BatIssuerKeyId,
        request: &OnChainIssuanceRequest<BatPairing, PallasA>,
    ) -> Result<Self, Error> {
        Ok(Self {
            sid: request.sid,
            issuer,
            pk_ref: BatRefundPublicKey::from_affine(request.pk_ref)?,
            commitment_to_sig_mask: BatCommitmentToSigMask::from_affine(
                request.commitment_to_sig_mask.0,
            )?,
            count: request.count,
        })
    }

    pub fn to_inner(&self) -> Result<OnChainIssuanceRequest<BatPairing, PallasA>, Error> {
        Ok(OnChainIssuanceRequest {
            sid: self.sid,
            pk_ref: self.pk_ref.get_affine()?,
            commitment_to_sig_mask: CommitmentToSigMask(self.commitment_to_sig_mask.get_affine()?),
            count: self.count,
        })
    }
}

/// The issuer's half of Π-Execute.
#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatReveal {
    #[cfg_attr(feature = "serde", serde(with = "human_hex"))]
    pub sid: BatSessionId,
    /// Called `k` in the paper.
    pub signature_mask: BatSignatureMask,
}

impl BatReveal {
    /// `pk_iss` and `commitment` are the ones stored with the session.
    pub fn verify(
        &self,
        pk_iss: &BatIssuerPublicKey,
        commitment: &BatCommitmentToSigMask,
    ) -> Result<(), Error> {
        Reveal::try_from(self)?.verify(
            &pk_iss.get_affine()?,
            &CommitmentToSigMask(commitment.get_affine()?),
            None,
        )?;
        Ok(())
    }
}

impl TryFrom<&Reveal<BatPairing>> for BatReveal {
    type Error = Error;

    fn try_from(reveal: &Reveal<BatPairing>) -> Result<Self, Self::Error> {
        Ok(Self {
            sid: reveal.sid,
            signature_mask: WrappedCanonical::wrap(&reveal.signature_mask.0)?,
        })
    }
}

impl TryFrom<&BatReveal> for Reveal<BatPairing> {
    type Error = Error;

    fn try_from(reveal: &BatReveal) -> Result<Self, Self::Error> {
        Ok(Self {
            sid: reveal.sid,
            signature_mask: SignatureMask(reveal.signature_mask.decode()?),
        })
    }
}

#[derive(
    Copy,
    Clone,
    Debug,
    PartialEq,
    Eq,
    Encode,
    Decode,
    DecodeWithMemTracking,
    MaxEncodedLen,
    TypeInfo,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatToken {
    pub pk_e: BatNullifier,
    /// Called `alpha` in the paper.
    pub unblinded_sig: BatTokenSignature,
}

impl TryFrom<&Token<BatPairing, PallasA>> for BatToken {
    type Error = Error;

    fn try_from(token: &Token<BatPairing, PallasA>) -> Result<Self, Self::Error> {
        Ok(Self {
            pk_e: BatNullifier::from_affine(token.pk_e)?,
            unblinded_sig: BatTokenSignature::from_affine(token.unblinded_sig)?,
        })
    }
}

impl TryFrom<&BatToken> for Token<BatPairing, PallasA> {
    type Error = Error;

    fn try_from(token: &BatToken) -> Result<Self, Self::Error> {
        Ok(Self {
            pk_e: token.pk_e.get_affine()?,
            unblinded_sig: token.unblinded_sig.get_affine()?,
        })
    }
}

/// What the pallet records for an accepted spend.
#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
pub struct BatSpend {
    pub nullifiers: Vec<BatNullifier>,
    pub tokens_per_issuer: BTreeMap<BatIssuerKeyId, u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct BatFeePayment<T: BatLimits = ()> {
    /// Each token with the issuer key it was signed under.
    pub tokens: BoundedVec<(BatIssuerKeyId, BatToken), T::MaxBatTokensPerPayment>,
    /// Called `gamma` in the paper. Covers the ordered `pk_e` of `tokens`.
    pub signature: BatSignature,
}

impl<T: BatLimits> BatFeePayment<T> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        tokens: &[BatPreToken],
        msg: &[u8],
    ) -> Result<Self, Error> {
        let pre = tokens.iter().map(|t| t.token.clone()).collect::<Vec<_>>();
        let payment = Payment::new(rng, &pre, msg, &bat_signature_base())?;
        let tokens = tokens
            .iter()
            .zip(&payment.tokens)
            .map(|(w, t)| Ok((w.issuer, BatToken::try_from(t)?)))
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Self {
            tokens: BoundedVec::try_from(tokens)
                .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?,
            signature: WrappedCanonical::wrap(&payment.signature)?,
        })
    }

    /// Issuer keys the payment spends under, for the caller to look up.
    pub fn issuers(&self) -> BTreeSet<BatIssuerKeyId> {
        self.tokens.iter().map(|(id, _)| *id).collect()
    }

    /// Checks every token against its issuer key in `issuers` and the signature over `msg`. The
    /// caller checks the nullifiers are unspent and the issuer caps.
    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        msg: &[u8],
        issuers: &impl BatIssuerKeyLookup,
    ) -> Result<BatSpend, Error> {
        let ids = self.issuers();
        if ids.len() > T::MaxBatIssuerKeysPerPayment::get() as usize {
            return Err(Error::TooManyBatIssuerKeys);
        }
        let mut keys = BTreeMap::new();
        for id in &ids {
            let pk = issuers
                .bat_issuer_key(*id)
                .ok_or(Error::UnknownBatIssuer(*id))?;
            keys.insert(*id, pk.get_affine()?);
        }
        let pk_iss = self
            .tokens
            .iter()
            .map(|(id, _)| keys.get(id).copied().ok_or(Error::UnknownBatIssuer(*id)))
            .collect::<Result<Vec<_>, Error>>()?;
        Payment::try_from(self)?.verify(rng, &pk_iss, msg, &bat_signature_base(), None)?;

        let mut tokens_per_issuer = BTreeMap::new();
        for (id, _) in &self.tokens {
            *tokens_per_issuer.entry(*id).or_insert(0) += 1;
        }
        Ok(BatSpend {
            nullifiers: self.tokens.iter().map(|(_, t)| t.pk_e).collect(),
            tokens_per_issuer,
        })
    }
}

impl<T: BatLimits> TryFrom<&BatFeePayment<T>> for Payment<BatPairing, PallasA> {
    type Error = Error;

    fn try_from(payment: &BatFeePayment<T>) -> Result<Self, Self::Error> {
        Ok(Self {
            tokens: payment
                .tokens
                .iter()
                .map(|(_, t)| Token::try_from(t))
                .collect::<Result<Vec<_>, Error>>()?,
            signature: payment.signature.decode()?,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct BatRefundRequest<T: BatLimits = ()> {
    pub sid: BatSessionId,
    pub tokens: BoundedVec<BatToken, T::MaxBatTokensPerSession>,
    /// Called `gamma_ref` in the paper. Made with `sk_ref`.
    pub signature: BatSignature,
}

impl<T: BatLimits> BatRefundRequest<T> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        refund_key: &BatRefundKey,
        unspent: &[BatPreToken],
    ) -> Result<Self, Error> {
        let pre = unspent.iter().map(|t| t.token.clone()).collect::<Vec<_>>();
        let refund = RefundRequest::new(rng, &refund_key.0, &pre, &bat_signature_base())?;
        Self::try_from(&refund)
    }

    /// `pk_iss` and `pk_ref` are the ones stored with the session. Returns the nullifiers. The caller
    /// checks they are unspent, that the session has not been refunded, and that `tokens` is no
    /// longer than the session's count.
    pub fn verify<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        pk_iss: &BatIssuerPublicKey,
        pk_ref: &BatRefundPublicKey,
    ) -> Result<Vec<BatNullifier>, Error> {
        RefundRequest::try_from(self)?.verify(
            rng,
            &pk_iss.get_affine()?,
            &pk_ref.get_affine()?,
            &bat_signature_base(),
            None,
        )?;
        Ok(self.tokens.iter().map(|t| t.pk_e).collect())
    }
}

impl<T: BatLimits> TryFrom<&RefundRequest<BatPairing, PallasA>> for BatRefundRequest<T> {
    type Error = Error;

    fn try_from(refund: &RefundRequest<BatPairing, PallasA>) -> Result<Self, Self::Error> {
        let tokens = refund
            .tokens
            .iter()
            .map(BatToken::try_from)
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(Self {
            sid: refund.sid,
            tokens: BoundedVec::try_from(tokens)
                .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?,
            signature: WrappedCanonical::wrap(&refund.signature)?,
        })
    }
}

impl<T: BatLimits> TryFrom<&BatRefundRequest<T>> for RefundRequest<BatPairing, PallasA> {
    type Error = Error;

    fn try_from(refund: &BatRefundRequest<T>) -> Result<Self, Self::Error> {
        Ok(Self {
            sid: refund.sid,
            tokens: refund
                .tokens
                .iter()
                .map(Token::try_from)
                .collect::<Result<Vec<_>, Error>>()?,
            signature: refund.signature.decode()?,
        })
    }
}
