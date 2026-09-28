//! Client side: buying tokens, holding them, and the off-chain messages exchanged with the issuer.

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use codec::{Decode, DecodeWithMemTracking, Encode};
use rand_core::CryptoRngCore;
use scale_info::TypeInfo;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use polymesh_bat::protocol::{
    ClientSession, IssueRequest, IssueResponse, OnChainIssuanceRequest, PreToken, RefundKey,
    SignatureMask,
};

use super::*;

/// Off-chain, client to issuer: the blinded token keys.
#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatIssueRequest(pub WrappedCanonical<IssueRequest<BatPairing>>);

/// Off-chain, issuer to client: the masked signatures and `com_k`.
#[derive(Clone, Debug, PartialEq, Eq, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct BatIssueResponse(pub WrappedCanonical<IssueResponse<BatPairing>>);

/// Per issuer key, from the blinded request until the mask is revealed.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatClientSession {
    pub issuer: BatIssuerKeyId,
    request: IssueRequest<BatPairing>,
    session: ClientSession<BatPairing, PallasA>,
}

impl BatClientSession {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        issuer: BatIssuerKeyId,
        count: u32,
    ) -> Result<(Self, BatIssueRequest), Error> {
        let (session, request) = ClientSession::new(rng, count, &bat_signature_base())?;
        let wrapped = BatIssueRequest(WrappedCanonical::wrap(&request)?);
        Ok((
            Self {
                issuer,
                request,
                session,
            },
            wrapped,
        ))
    }

    pub fn sid(&self) -> BatSessionId {
        self.session.sid
    }

    /// Checks the issuer's response and makes the on-chain request that pays for the tokens.
    pub fn on_chain_issue_request<R: CryptoRngCore>(
        &self,
        rng: &mut R,
        response: &BatIssueResponse,
    ) -> Result<BatOnChainIssuanceRequest, Error> {
        let response = response.0.decode()?;
        response.verify(rng, &self.request, None)?;
        BatOnChainIssuanceRequest::from_inner(
            self.issuer,
            &OnChainIssuanceRequest::new(&self.session, &response),
        )
    }

    /// Unmasks the tokens once the issuer's reveal is on chain.
    pub fn unmask(
        self,
        response: &BatIssueResponse,
        reveal: &BatReveal,
    ) -> Result<(Vec<BatPreToken>, BatRefundKey), Error> {
        if reveal.sid != self.session.sid {
            return Err(polymesh_bat::Error::SessionMismatch.into());
        }
        let (issuer, sid) = (self.issuer, self.session.sid);
        let mask = SignatureMask(reveal.signature_mask.decode()?);
        let (tokens, refund_key) = self.session.unmask(&response.0.decode()?, &mask)?;
        let tokens = tokens
            .into_iter()
            .map(|token| BatPreToken { issuer, sid, token })
            .collect();
        Ok((tokens, BatRefundKey(refund_key)))
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatPreToken {
    pub issuer: BatIssuerKeyId,
    /// Session the token was bought in.
    pub sid: BatSessionId,
    pub token: PreToken<BatPairing, PallasA>,
}

impl BatPreToken {
    pub fn nullifier(&self) -> Result<BatNullifier, Error> {
        BatNullifier::from_affine(self.token.eph.pk)
    }
}

/// Signs the refund of a session's unspent tokens.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatRefundKey(pub RefundKey<PallasA>);

impl BatRefundKey {
    pub fn sid(&self) -> BatSessionId {
        self.0.sid
    }
}
