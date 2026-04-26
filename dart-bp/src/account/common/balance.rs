use crate::account::AccountState;
use crate::util::{
    create_balance_bp_t_values, enforce_balance_change_prover,
    generate_host_sigma_responses_for_balance_change,
    generate_schnorr_responses_for_balance_change, generate_sigma_t_values_for_balance_change,
};
use crate::{Error, error::Result};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::vec::Vec;
use ark_std::{format, string::ToString};
use bulletproofs::r1cs::{ConstraintSystem, Prover};
use bulletproofs::{BulletproofGens, PedersenGens};
use dock_crypto_utils::transcript::MerlinTranscript;
use polymesh_dart_common::Balance;
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{PokPedersenCommitment, PokPedersenCommitmentProtocol};
use schnorr_pok::partial::{PartialPokPedersenCommitment, PartialSchnorrResponse};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// Configuration for balance change in a single leg
pub struct BalanceChangeConfig<G0: SWCurveConfig + Clone + Copy> {
    pub amount: Balance,
    pub ct_amount: Affine<G0>,
    /// Ephemeral public key for amount: eph_pk_s[2] (sender) or eph_pk_r[2] (receiver)
    pub eph_pk_amount: Affine<G0>,
    pub has_balance_decreased: bool,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeProofPartial<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Clone + Copy,
> {
    pub comm_bp_bal: Affine<G0>,
    pub t_comm_bp_bal: Affine<G0>,
    pub resp_comm_bp_bal: PartialSchnorrResponse<Affine<G0>>,
}

/// Proof for variables that change only when the account state transition involves a change in account balance
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeProof<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    pub partial: BalanceChangeProofPartial<F0, G0>,
    /// Commitment to randomness and response for proving the leg amount relation:
    /// `ct_amount = eph_pk[2] * sk_enc^{-1} * enc_gen * amount`
    /// Both responses (sk_enc_inv and amount) are shared.
    pub resp_leg_amount: Vec<PartialPokPedersenCommitment<Affine<G0>>>,
}

/// Balance change proof for split (host/auth) workflows.
/// Contains the host's balance BP partial proof and PokPedersenCommitment proofs for ct_amount_2.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct BalanceChangeSplitProof<
    F0: PrimeField,
    G0: SWCurveConfig<ScalarField = F0> + Clone + Copy,
> {
    pub partial: BalanceChangeProofPartial<F0, G0>,
    /// For relation `ct_amount_2 = enc_gen * amount + B_blinding * (-k)` for some randomness `k` which is used in auth proof as well.
    pub resp_ct_amount: Vec<PokPedersenCommitment<Affine<G0>>>,
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
    /// For relation `ct_amount_2 = enc_gen * amount + B_blinding * (-k)` for some randomness `k` which is used in auth proof as well.
    pub t_leg_amount: Vec<PokPedersenCommitmentProtocol<Affine<G0>>>,
}

impl<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy>
    BalanceChangeProver<F0, G0>
{
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        balance_change_config: Vec<BalanceChangeConfig<G0>>,
        sk_enc: F0,
        account: &AccountState<Affine<G0>>,
        updated_account: &AccountState<Affine<G0>>,
        mut old_balance_blinding: F0,
        mut new_balance_blinding: F0,
        mut sk_enc_inv_blinding: F0,
        mut even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
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
        let mut eph_pk_amounts = Vec::with_capacity(balance_change_config.len());
        let mut has_balance_decreased = Vec::with_capacity(balance_change_config.len());
        for config in balance_change_config {
            amounts.push(config.amount);
            ct_amounts.push(config.ct_amount);
            eph_pk_amounts.push(config.eph_pk_amount);
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
            sk_enc.inverse().ok_or(Error::InvertingZero)?,
            sk_enc_inv_blinding,
            eph_pk_amounts,
            pc_gens,
            bp_gens,
            enc_gen,
            &mut transcript,
        )?;

        Zeroize::zeroize(&mut old_balance_blinding);
        Zeroize::zeroize(&mut new_balance_blinding);
        Zeroize::zeroize(&mut sk_enc_inv_blinding);

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
            partial: BalanceChangeProofPartial {
                comm_bp_bal: self.comm_bp_bal,
                t_comm_bp_bal,
                resp_comm_bp_bal,
            },
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

/// Balance change prover for the split (W2/W3) affirmation flow.
/// Analogous to `BalanceChangeProver` for the non-split (solo) flow.
pub struct BalanceSplitProver<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy> {
    comm_bp_bal_blinding: F0,
    comm_bp_bal: Affine<G0>,
    t_comm_bp_bal: SchnorrCommitment<Affine<G0>>,
    amounts: Vec<Balance>,
    t_ct_amount: Vec<(Affine<G0>, PokPedersenCommitmentProtocol<Affine<G0>>)>,
}

impl<F0: PrimeField, G0: SWCurveConfig<ScalarField = F0> + Clone + Copy>
    BalanceSplitProver<F0, G0>
{
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        balance_changes: &[BalanceChangeConfig<G0>],
        old_balance: Balance,
        new_balance: Balance,
        old_balance_blinding: F0,
        new_balance_blinding: F0,
        enc_gen: Affine<G0>,
        k_amounts: &[F0],
        even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        pc_gens: &PedersenGens<Affine<G0>>,
        bp_gens: &BulletproofGens<Affine<G0>>,
    ) -> Result<Self> {
        if k_amounts.len() != balance_changes.len() {
            return Err(Error::ProofGenerationError(format!(
                "k_amounts length {} does not match number of balance-changing legs {}",
                k_amounts.len(),
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
            amounts.clone(),
            has_decreased,
            even_prover,
            bp_gens,
        )?;

        let amount_blindings: Vec<F0> = (0..amounts.len()).map(|_| F0::rand(rng)).collect();

        let t_comm_bp_bal = create_balance_bp_t_values(
            rng,
            old_balance_blinding,
            new_balance_blinding,
            amount_blindings.clone(),
            pc_gens,
            bp_gens,
        );

        let mut t_ct_amount_2_protos = Vec::with_capacity(amounts.len());
        for (i, b) in amount_blindings.into_iter().enumerate() {
            let ct_amount_2 = (enc_gen * F0::from(amounts[i])
                + pc_gens.B_blinding * (-k_amounts[i]))
                .into_affine();
            let proto = PokPedersenCommitmentProtocol::init(
                F0::from(amounts[i]),
                b,
                &enc_gen,
                -k_amounts[i],
                F0::rand(rng),
                &pc_gens.B_blinding,
            );
            t_ct_amount_2_protos.push((ct_amount_2, proto));
        }

        // Write challenge contributions to transcript
        {
            let mut transcript = even_prover.transcript();
            t_comm_bp_bal.challenge_contribution(&mut transcript)?;
            for (ct_amount_2, proto) in &t_ct_amount_2_protos {
                proto.challenge_contribution(
                    &enc_gen,
                    &pc_gens.B_blinding,
                    ct_amount_2,
                    &mut transcript,
                )?;
            }
        }

        Ok(Self {
            comm_bp_bal_blinding,
            comm_bp_bal,
            t_comm_bp_bal,
            amounts,
            t_ct_amount: t_ct_amount_2_protos,
        })
    }

    pub fn gen_proof(
        self,
        challenge: &F0,
    ) -> Result<(
        BalanceChangeProofPartial<F0, G0>,
        Vec<PokPedersenCommitment<Affine<G0>>>,
    )> {
        let resp_comm_bp_bal = generate_host_sigma_responses_for_balance_change(
            &self.amounts,
            self.comm_bp_bal_blinding,
            &self.t_comm_bp_bal,
            challenge,
        )?;
        let resp_ct_amount_2: Vec<_> = self
            .t_ct_amount
            .into_iter()
            .map(|(_, proto)| proto.gen_proof(challenge))
            .collect();
        Ok((
            BalanceChangeProofPartial {
                comm_bp_bal: self.comm_bp_bal,
                t_comm_bp_bal: self.t_comm_bp_bal.t,
                resp_comm_bp_bal,
            },
            resp_ct_amount_2,
        ))
    }
}
