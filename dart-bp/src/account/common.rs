use crate::account::AccountState;
use crate::error::{Error, Result};
use crate::leg_new::{LegEncryption, LegEncryptionRandomness};
use crate::util::{
    enforce_balance_change_prover, generate_schnorr_responses_for_balance_change,
    generate_sigma_t_values_for_balance_change,
};
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use bulletproofs::r1cs::Prover;
use bulletproofs::{BulletproofGens, PedersenGens};
use dock_crypto_utils::transcript::MerlinTranscript;
use polymesh_dart_common::Balance;
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::PokPedersenCommitmentProtocol;
use schnorr_pok::partial::{Partial1PokPedersenCommitment, PartialSchnorrResponse};
use schnorr_pok::SchnorrCommitment;
use zeroize::{Zeroize, ZeroizeOnDrop};

/// Configuration for a leg in common state change operations (prover side)
#[derive(Clone)]
pub struct LegProverConfig<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub encryption: LegEncryption<Affine<G0>>,
    pub randomness: LegEncryptionRandomness<F0>,
    pub is_sender: bool,
    pub has_balance_changed: bool,
}

/// Configuration for a leg in common state change operations (verifier side)
#[derive(Clone)]
pub struct LegVerifierConfig<G0: SWCurveConfig + Clone + Copy> {
    pub encryption: LegEncryption<Affine<G0>>,
    pub is_sender: bool,
    pub has_balance_decreased: Option<bool>,
    pub has_counter_decreased: Option<bool>,
}

/// Configuration for balance change in a single leg
pub struct BalanceChangeConfig<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub amount: Balance,
    pub ct_amount: Affine<G0>,
    pub r_3: F0,
    pub has_balance_decreased: bool,
}

/// Proof for variables that change only when the account state transition involves a change in account balance
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeProof<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub comm_bp_bal: Affine<G0>,
    pub t_comm_bp_bal: Affine<G0>,
    pub resp_comm_bp_bal: PartialSchnorrResponse<Affine<G0>>,
    /// Commitment to randomness and response for proving knowledge of amount in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_amount: Vec<Partial1PokPedersenCommitment<Affine<G0>>>,
}

#[derive(Zeroize, ZeroizeOnDrop)]
pub struct BalanceChangeProver<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub amount: Vec<Balance>,
    pub old_balance: Balance,
    pub new_balance: Balance,
    pub comm_bp_bal_blinding: G0::ScalarField,
    #[zeroize(skip)]
    pub comm_bp_bal: Affine<G0>,
    pub t_comm_bp_bal: SchnorrCommitment<Affine<G0>>,
    pub t_leg_amount: Vec<PokPedersenCommitmentProtocol<Affine<G0>>>,
}

impl<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy>
    BalanceChangeProver<F0, G0>
{
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        balance_change_config: Vec<BalanceChangeConfig<F0, G0>>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        mut old_balance_blinding: F0,
        mut new_balance_blinding: F0,
        mut even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<Self> {
        let mut delta = 0i64;
        for config in &balance_change_config {
            if config.has_balance_decreased {
                delta = delta + (config.amount as i64);
            } else {
                delta = delta - (config.amount as i64);
            }
        }
        let (amount, has_balance_decreased) = if delta > 0 {
            (delta as Balance, true)
        } else {
            (-delta as Balance, false)
        };
        ensure_correct_balance_change(account, updated_account, amount, has_balance_decreased)?;

        let mut amounts = Vec::with_capacity(balance_change_config.len());
        let mut ct_amounts = Vec::with_capacity(balance_change_config.len());
        let mut r_3 = Vec::with_capacity(balance_change_config.len());
        let mut has_balance_decreased = Vec::with_capacity(balance_change_config.len());
        for config in balance_change_config {
            amounts.push(config.amount);
            ct_amounts.push(config.ct_amount);
            r_3.push(config.r_3);
            has_balance_decreased.push(config.has_balance_decreased);
        }

        let (comm_bp_bal_blinding, comm_bp_bal) = enforce_balance_change_prover(
            rng,
            account.balance,
            updated_account.balance,
            amounts.clone(),
            has_balance_decreased,
            &mut even_prover,
            bp_gens,
        )?;

        let mut transcript = even_prover.transcript();

        let amount_blinding = (0..amounts.len())
            .map(|_| F0::rand(rng))
            .collect::<Vec<_>>();
        let (t_comm_bp_bal, t_leg_amount) = generate_sigma_t_values_for_balance_change(
            rng,
            amounts.clone(),
            ct_amounts,
            old_balance_blinding,
            new_balance_blinding,
            amount_blinding,
            r_3,
            pc_gens,
            bp_gens,
            enc_key_gen,
            enc_gen,
            &mut transcript,
        )?;

        Zeroize::zeroize(&mut old_balance_blinding);
        Zeroize::zeroize(&mut new_balance_blinding);

        Ok(Self {
            amount: amounts,
            old_balance: account.balance,
            new_balance: updated_account.balance,
            comm_bp_bal_blinding,
            comm_bp_bal,
            t_comm_bp_bal,
            t_leg_amount,
        })
    }

    pub fn gen_proof(self, challenge: &F0) -> Result<BalanceChangeProof<F0, G0>> {
        let t_comm_bp_bal = self.t_comm_bp_bal.t;
        let (resp_comm_bp_bal, resp_leg_amount) = generate_schnorr_responses_for_balance_change(
            self.amount.clone(),
            self.comm_bp_bal_blinding,
            self.t_comm_bp_bal.clone(),
            self.t_leg_amount.clone(),
            challenge,
        )?;
        Ok(BalanceChangeProof {
            comm_bp_bal: self.comm_bp_bal,
            t_comm_bp_bal,
            resp_comm_bp_bal,
            resp_leg_amount,
        })
    }
}

pub fn ensure_correct_balance_change<G: AffineRepr>(
    old_state: &AccountState<G>,
    new_state: &AccountState<G>,
    amount: Balance,
    has_balance_decreased: bool,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if has_balance_decreased {
            if new_state.balance != old_state.balance - amount {
                return Err(Error::ProofGenerationError(
                    "Balance decrease incorrect".to_string(),
                ));
            }
        } else {
            if new_state.balance != old_state.balance + amount {
                return Err(Error::ProofGenerationError(
                    "Balance increase incorrect".to_string(),
                ));
            }
        }
        Ok(())
    }
}
