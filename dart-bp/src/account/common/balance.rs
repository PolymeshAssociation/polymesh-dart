use crate::account::AccountState;
use crate::util::{
    create_balance_bp_t_values, enforce_balance_change_prover,
    generate_schnorr_responses_for_balance_change, generate_sigma_t_values_for_balance_change,
};
use crate::{Error, error::Result};
use ark_ec::AffineRepr;
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use ark_std::{format, string::ToString};
use bulletproofs::r1cs::{ConstraintSystem, Prover};
use bulletproofs::{BulletproofGens, PedersenGens};
use dock_crypto_utils::transcript::MerlinTranscript;
use polymesh_dart_common::{Balance, MAX_BALANCE};
use rand_core::CryptoRngCore;
use schnorr_pok::partial::PartialSchnorrResponse;
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// Configuration for balance change in a single leg. ct_amount is proven in the leg-link.
pub struct BalanceChangeConfig {
    pub amount: Balance,
    pub has_balance_decreased: bool,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeProofPartial<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Clone + Copy,
> {
    /// Commitment to old and new balances and amounts used in BP
    pub comm_bp_bal: Affine<G0>,
    /// For the sigma protocol for above commitment
    pub t_comm_bp_bal: Affine<G0>,
    pub resp_comm_bp_bal: PartialSchnorrResponse<Affine<G0>>,
}

/// Proof for variables that change only when the account state transition involves a change in account balance
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeProof<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub partial: BalanceChangeProofPartial<F0, G0>,
}

/// Balance change proof for split (host/auth) workflows.
/// Contains the host's balance BP partial proof and PokPedersenCommitment proofs for ct_amount_2.
/// Split (W2/W3) balance proof. `ct_amount_2` now lives in the host common proof (over every
/// `needs_ct_amount` leg), so this carries only the balance BP, like the solo `BalanceChangeProof`.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeSplitProof<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Clone + Copy,
> {
    pub partial: BalanceChangeProofPartial<F0, G0>,
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
}

impl<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy>
    BalanceChangeProver<F0, G0>
{
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        balance_change_config: Vec<BalanceChangeConfig>,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        mut old_balance_blinding: F0,
        mut new_balance_blinding: F0,
        amount_blindings: Vec<F0>,
        mut even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
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
        let mut has_balance_decreased = Vec::with_capacity(balance_change_config.len());
        for config in balance_change_config {
            amounts.push(config.amount);
            has_balance_decreased.push(config.has_balance_decreased);
        }

        let (comm_bp_bal_blinding, comm_bp_bal) = enforce_balance_change_prover(
            rng,
            account.balance(),
            updated_account.balance(),
            amounts.clone(),
            has_balance_decreased,
            &mut even_prover,
            bp_gens,
        )?;

        let mut transcript = even_prover.transcript();

        // amount_blindings are shared with the leg-link ct_amount whose v this BP consumes
        let t_comm_bp_bal = generate_sigma_t_values_for_balance_change(
            rng,
            old_balance_blinding,
            new_balance_blinding,
            amount_blindings,
            pc_gens,
            bp_gens,
            &mut transcript,
        )?;

        Zeroize::zeroize(&mut old_balance_blinding);
        Zeroize::zeroize(&mut new_balance_blinding);

        Ok(Self {
            amount: amounts,
            old_balance: account.balance(),
            new_balance: updated_account.balance(),
            comm_bp_bal_blinding,
            comm_bp_bal,
            t_comm_bp_bal,
        })
    }

    pub fn gen_proof(self, challenge: &F0) -> Result<BalanceChangeProof<F0, G0>> {
        let t_comm_bp_bal = self.t_comm_bp_bal.t;
        let resp_comm_bp_bal = generate_schnorr_responses_for_balance_change(
            self.comm_bp_bal_blinding,
            self.t_comm_bp_bal.clone(),
            challenge,
        )?;
        Ok(BalanceChangeProof {
            partial: BalanceChangeProofPartial {
                comm_bp_bal: self.comm_bp_bal,
                t_comm_bp_bal,
                resp_comm_bp_bal,
            },
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
        if amount > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount));
        }

        if has_balance_decreased {
            if new_state.balance() != old_state.balance() - amount {
                return Err(Error::ProofGenerationError(
                    "Balance decrease incorrect".to_string(),
                ));
            }
        } else {
            if new_state.balance() != old_state.balance() + amount {
                return Err(Error::ProofGenerationError(
                    "Balance increase incorrect".to_string(),
                ));
            }
        }
        Ok(())
    }
}

/// Balance change prover for the split (W2/W3) affirmation flow.
/// Analogous to `BalanceChangeProver` for the non-split (solo) flow. `ct_amount_2` is owned by the
/// host common protocol; this consumes the shared `amount_blindings` so the balance BP amount slots
/// use the same amounts as those `ct_amount_2`, which match the amount in the leg ciphertext.
#[derive(Zeroize, ZeroizeOnDrop)]
pub struct BalanceSplitProver<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    comm_bp_bal_blinding: F0,
    #[zeroize(skip)]
    comm_bp_bal: Affine<G0>,
    t_comm_bp_bal: SchnorrCommitment<Affine<G0>>,
}

impl<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy>
    BalanceSplitProver<F0, G0>
{
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        balance_changes: &[BalanceChangeConfig],
        old_balance: Balance,
        new_balance: Balance,
        old_balance_blinding: F0,
        new_balance_blinding: F0,
        amount_blindings: Vec<F0>,
        even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
    ) -> Result<Self> {
        if amount_blindings.len() != balance_changes.len() {
            return Err(Error::ProofGenerationError(format!(
                "amount_blindings length {} does not match number of balance-changing legs {}",
                amount_blindings.len(),
                balance_changes.len()
            )));
        }

        let amounts: Vec<Balance> = balance_changes.iter().map(|c| c.amount).collect();
        let has_decreased: Vec<bool> = balance_changes
            .iter()
            .map(|c| c.has_balance_decreased)
            .collect();

        let (comm_bp_bal_blinding, comm_bp_bal) = enforce_balance_change_prover(
            rng,
            old_balance,
            new_balance,
            amounts,
            has_decreased,
            even_prover,
            bp_gens,
        )?;

        let t_comm_bp_bal = create_balance_bp_t_values(
            rng,
            old_balance_blinding,
            new_balance_blinding,
            amount_blindings,
            pc_gens,
            bp_gens,
        );

        {
            let mut transcript = even_prover.transcript();
            t_comm_bp_bal.challenge_contribution(&mut transcript)?;
        }

        Ok(Self {
            comm_bp_bal_blinding,
            comm_bp_bal,
            t_comm_bp_bal,
        })
    }

    pub fn gen_proof(self, challenge: &F0) -> Result<BalanceChangeProofPartial<F0, G0>> {
        let t_comm_bp_bal = self.t_comm_bp_bal.t;
        let resp_comm_bp_bal = generate_schnorr_responses_for_balance_change(
            self.comm_bp_bal_blinding,
            self.t_comm_bp_bal.clone(),
            challenge,
        )?;
        Ok(BalanceChangeProofPartial {
            comm_bp_bal: self.comm_bp_bal,
            t_comm_bp_bal,
            resp_comm_bp_bal,
        })
    }
}
