//! Issuer side: signing blinded token keys and revealing the mask once the client has paid.

use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rand_core::{CryptoRng, RngCore};

use polymesh_bat::protocol::{IssuerKeypair, IssuerSession};

use super::*;

/// One key per denomination.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatIssuerKeys(IssuerKeypair<BatPairing>);

impl BatIssuerKeys {
    pub fn new<R: RngCore + CryptoRng>(rng: &mut R) -> Self {
        Self(IssuerKeypair::new(rng))
    }

    pub fn new_with_seed(seed: &[u8]) -> Self {
        Self(IssuerKeypair::new_with_seed(seed))
    }

    pub fn public_key(&self) -> Result<BatIssuerPublicKey, Error> {
        BatIssuerPublicKey::from_affine(self.0.pk)
    }

    /// `issuer` is this key's id in the registry.
    pub fn sign<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        issuer: BatIssuerKeyId,
        request: &BatIssueRequest,
    ) -> Result<(BatIssuerSession, BatIssueResponse), Error> {
        let (session, response) = IssuerSession::new(rng, &request.0.decode()?, &self.0)?;
        Ok((
            BatIssuerSession { issuer, session },
            BatIssueResponse(WrappedCanonical::wrap(&response)?),
        ))
    }
}

/// Kept until the client's payment is final.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct BatIssuerSession {
    pub issuer: BatIssuerKeyId,
    session: IssuerSession<BatPairing>,
}

impl BatIssuerSession {
    pub fn sid(&self) -> BatSessionId {
        self.session.sid
    }

    /// Opens the mask for the client's on-chain request. A reveal is public once posted, even if the
    /// chain rejects it, so a request naming another issuer key is refused here: the chain would
    /// reject the reveal only after the mask was out.
    pub fn reveal(self, request: &BatOnChainIssuanceRequest) -> Result<BatReveal, Error> {
        if request.issuer != self.issuer {
            return Err(polymesh_bat::Error::SessionMismatch.into());
        }
        let reveal = self.session.reveal(&request.to_inner()?)?;
        BatReveal::try_from(&reveal)
    }
}
