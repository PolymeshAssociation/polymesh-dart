use codec::{Decode, DecodeWithMemTracking, Encode};
use rand_core::{CryptoRng, RngCore};
use scale_info::TypeInfo;

use super::*;

pub const BAT_FEE_PAYMENT_BATCH_CTX: &[u8] = b"BatFeePaymentBatch";

/// Fee paid in tokens + batch of proofs.
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct BatFeePaymentWithBatchedProofs<T: BatLimits = ()> {
    pub fee_payment: BatFeePayment<T>,
    pub batched_proofs: BatchedProofs<T>,
}

impl<T: BatLimits> BatFeePaymentWithBatchedProofs<T> {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        tokens: &[BatPreToken],
        batched_proofs: BatchedProofs<T>,
    ) -> Result<Self, Error> {
        let ctx = batched_proofs.ctx(BAT_FEE_PAYMENT_BATCH_CTX);
        let fee_payment = BatFeePayment::new(rng, tokens, &ctx.0)?;
        Ok(Self {
            fee_payment,
            batched_proofs,
        })
    }

    /// Verifies only the fee payment for this batch of proofs.
    pub fn verify_fee_payment<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        issuers: &impl BatIssuerKeyLookup,
    ) -> Result<BatSpend, Error> {
        let ctx = self.fee_payment_ctx();
        self.fee_payment.verify(rng, &ctx.0, issuers)
    }

    /// The message the fee payment's signature covers.
    pub fn fee_payment_ctx(&self) -> ProofHash {
        self.batched_proofs.ctx(BAT_FEE_PAYMENT_BATCH_CTX)
    }
}
