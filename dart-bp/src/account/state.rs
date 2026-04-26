use crate::poseidon_impls::poseidon_2::{Poseidon_hash_2_simple, Poseidon2Params};
use crate::{Error, error::Result};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::Field;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::string::ToString;
use ark_std::vec::Vec;
use polymesh_dart_common::{
    AssetId, Balance, MAX_ASSET_ID, MAX_BALANCE, NullifierSkGenCounter, PendingTxnCounter,
};
use rand_core::CryptoRngCore;
use zeroize::{Zeroize, ZeroizeOnDrop};

pub const NUM_GENERATORS: usize = 10;

// TODO: Rewrite this and explain why optimization was dropped
// The account commitment has g * {sk_{en}}^{-1}. This is safe as it's called Inverse Diffie Hellman assumption and [this paper](https://ink.library.smu.edu.sg/cgi/viewcontent.cgi?params=/context/sis_research/article/2082/&path_info=Bao2003_VariationsOfDiffie_HellmanProblem_pv.pdf)
// shows DDH implies Inverse Diffie Hellman assumption. See section 3.1 and 3.2 where InvDDH ⇐ SDDH and SDDH ⇐ DDH, where SDDH is the square decisional Diffie-Hellman problem

// Constants for index of each item in the account commitment
pub(crate) const SK_GEN_INDEX: usize = 0;
pub(crate) const BALANCE_GEN_INDEX: usize = 1;
pub(crate) const COUNTER_GEN_INDEX: usize = 2;
pub(crate) const ASSET_ID_GEN_INDEX: usize = 3;
pub(crate) const RHO_GEN_INDEX: usize = 4;
pub(crate) const CURRENT_RHO_GEN_INDEX: usize = 5;
pub(crate) const RANDOMNESS_GEN_INDEX: usize = 6;
pub(crate) const CURRENT_RANDOMNESS_GEN_INDEX: usize = 7;
pub(crate) const ID_GEN_INDEX: usize = 8;
pub(crate) const SK_ENC_INV_GEN_INDEX: usize = 9;

/// This trait is used to abstract over the account commitment key. It allows us to use different
/// generators for the account commitment key while still providing the same interface.
pub trait AccountCommitmentKeyTrait<G: AffineRepr>: CanonicalSerialize + Clone {
    /// Returns the generator for the affirmation key.
    fn sk_gen(&self) -> G;

    /// Returns the generator for the balance.
    fn balance_gen(&self) -> G;

    /// Returns the generator for the pending transaction counter.
    fn counter_gen(&self) -> G;

    /// Returns the generator for the asset ID.
    fn asset_id_gen(&self) -> G;

    /// Returns the generator for the original rho value generated during registration
    fn rho_gen(&self) -> G;

    /// Returns the generator for the current rho value. This is used to generate nullifier.
    fn current_rho_gen(&self) -> G;

    /// Returns the generator for the randomness value.
    fn randomness_gen(&self) -> G;

    /// Returns the generator for the current randomness value.
    fn current_randomness_gen(&self) -> G;

    /// Returns the generator for the user's identity. This is bound to the public key but the relation
    /// between them is not proven in any of the proofs
    fn id_gen(&self) -> G;

    /// Returns the generator for the inverse of encryption secret key
    fn sk_enc_gen(&self) -> G;

    fn as_gens(&self) -> [G; NUM_GENERATORS] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.current_randomness_gen(),
            self.id_gen(),
            self.sk_enc_gen(),
        ]
    }

    fn as_gens_without_sk(&self) -> [G; NUM_GENERATORS - 2] {
        [
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.current_randomness_gen(),
            self.id_gen(),
        ]
    }

    fn as_gens_without_sk_and_asset_id(&self) -> [G; NUM_GENERATORS - 3] {
        [
            self.balance_gen(),
            self.counter_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.current_randomness_gen(),
            self.id_gen(),
        ]
    }

    fn as_gens_with_blinding_without_sk(&self, blinding_gen: G) -> [G; NUM_GENERATORS - 1] {
        [
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.current_randomness_gen(),
            self.id_gen(),
            blinding_gen,
        ]
    }

    fn as_gens_with_blinding_without_sk_and_asset_id(
        &self,
        blinding_gen: G,
    ) -> [G; NUM_GENERATORS - 2] {
        [
            self.balance_gen(),
            self.counter_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.current_randomness_gen(),
            self.id_gen(),
            blinding_gen,
        ]
    }

    fn as_gens_with_asset_id_revealed(&self) -> [G; NUM_GENERATORS - 1] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.current_randomness_gen(),
            self.id_gen(),
            self.sk_enc_gen(),
        ]
    }

    /// Used for re-randomized leaf
    fn as_gens_with_blinding(&self, blinding: G) -> [G; NUM_GENERATORS + 1] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.current_randomness_gen(),
            self.id_gen(),
            self.sk_enc_gen(),
            blinding,
        ]
    }

    /// Used for re-randomized leaf
    fn as_gens_with_blinding_and_asset_id_revealed(&self, blinding: G) -> [G; NUM_GENERATORS] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.current_randomness_gen(),
            self.id_gen(),
            self.sk_enc_gen(),
            blinding,
        ]
    }
}

impl<G: AffineRepr> AccountCommitmentKeyTrait<G> for [G; NUM_GENERATORS] {
    fn sk_gen(&self) -> G {
        self[SK_GEN_INDEX]
    }

    fn balance_gen(&self) -> G {
        self[BALANCE_GEN_INDEX]
    }

    fn counter_gen(&self) -> G {
        self[COUNTER_GEN_INDEX]
    }

    fn asset_id_gen(&self) -> G {
        self[ASSET_ID_GEN_INDEX]
    }

    fn rho_gen(&self) -> G {
        self[RHO_GEN_INDEX]
    }

    fn current_rho_gen(&self) -> G {
        self[CURRENT_RHO_GEN_INDEX]
    }

    fn randomness_gen(&self) -> G {
        self[RANDOMNESS_GEN_INDEX]
    }

    fn current_randomness_gen(&self) -> G {
        self[CURRENT_RANDOMNESS_GEN_INDEX]
    }

    fn id_gen(&self) -> G {
        self[ID_GEN_INDEX]
    }

    fn sk_enc_gen(&self) -> G {
        self[SK_ENC_INV_GEN_INDEX]
    }
}

/// Builder for constructing account state transitions.
/// Allows combining multiple updates before calling `refresh_randomness_for_state_change` at the end.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AccountStateBuilder<G: AffineRepr> {
    state: AccountState<G>,
    // net_counter_change and net_balance_change could be used to allow intermediate negatives when applying multiple updates
    // net_counter_change: i32,
    // net_balance_change: i128,
}

impl<G: AffineRepr> AccountStateBuilder<G> {
    /// Initialize builder from an existing account state
    pub fn init(initial_account: AccountState<G>) -> Self {
        Self {
            state: initial_account,
        }
    }

    /// Update state for minting (increase balance)
    pub fn update_for_mint(&mut self, amount: u64) -> Result<()> {
        if amount + self.state.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.state.balance));
        }
        self.state.balance += amount;
        Ok(())
    }

    /// Update state for sending (decrease balance, increment counter)
    pub fn update_for_send(&mut self, amount: u64) -> Result<()> {
        if amount > self.state.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        self.state.balance -= amount;
        self.state.counter += 1;
        Ok(())
    }

    /// Update state for receiving affirmation (increment counter only)
    pub fn update_for_receive(&mut self) {
        self.state.counter += 1;
    }

    /// Update state for claiming received amount (increase balance, decrement counter)
    pub fn update_for_claiming_received(&mut self, amount: u64) -> Result<()> {
        if self.state.counter == 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be greater than 0".to_string(),
            ));
        }
        if amount + self.state.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.state.balance));
        }
        self.state.balance += amount;
        self.state.counter -= 1;
        Ok(())
    }

    /// Update state for reversing a send (increase balance, decrement counter)
    pub fn update_for_reversing_send(&mut self, amount: u64) -> Result<()> {
        if self.state.counter == 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be greater than 0".to_string(),
            ));
        }
        if amount + self.state.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.state.balance));
        }
        self.state.balance += amount;
        self.state.counter -= 1;
        Ok(())
    }

    /// Update state for decreasing counter
    pub fn update_for_decreasing_counter(
        &mut self,
        decrease_counter_by: Option<PendingTxnCounter>,
    ) -> Result<()> {
        let decrease_counter_by = decrease_counter_by.unwrap_or(1);
        if self.state.counter < decrease_counter_by {
            return Err(Error::ProofOfBalanceError(
                "Counter cannot be decreased below zero".to_string(),
            ));
        }
        self.state.counter -= decrease_counter_by;
        Ok(())
    }

    /// Update state for irreversible send (decrease balance only, no counter change)
    pub fn update_for_irreversible_send(&mut self, amount: u64) -> Result<()> {
        if amount > self.state.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        self.state.balance -= amount;
        Ok(())
    }

    /// Update state for irreversible receive (increase balance only, no counter change)
    pub fn update_for_irreversible_receive(&mut self, amount: u64) -> Result<()> {
        if amount + self.state.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.state.balance));
        }
        self.state.balance += amount;
        Ok(())
    }

    /// Finalize the builder by refreshing randomness and returning the new account state
    pub fn finalize(mut self) -> AccountState<G> {
        self.state.refresh_randomness_for_state_change();
        self.state
    }

    /// Get a reference to the current state (without finalizing)
    pub fn state(&self) -> &AccountState<G> {
        &self.state
    }

    /// Get a mutable reference to the current state (without finalizing)
    pub fn state_mut(&mut self) -> &mut AccountState<G> {
        &mut self.state
    }
}

#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct AccountState<G: AffineRepr> {
    pub pk_aff: G,
    pub pk_enc: G,
    pub id: G::ScalarField,
    pub balance: Balance,
    pub counter: PendingTxnCounter,
    pub asset_id: AssetId,
    pub rho: G::ScalarField,
    pub current_rho: G::ScalarField,
    pub randomness: G::ScalarField,
    pub current_randomness: G::ScalarField,
}

// TODO: Add an account state batch abstraction that prevents manual update of field done in tests

impl<G> AccountState<G>
where
    G: AffineRepr,
{
    /// Returns `(AccountState, rho_randomness)` where `rho_randomness` is needed for the registration proof.
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        poseidon_config: Poseidon2Params<G::ScalarField>,
    ) -> Result<(Self, G::ScalarField)> {
        let randomness = G::ScalarField::rand(rng);
        let rho_randomness = G::ScalarField::rand(rng);
        let state = Self::new_given_randomness(
            id,
            pk_aff,
            pk_enc,
            asset_id,
            counter,
            randomness,
            rho_randomness,
            poseidon_config,
        )?;
        Ok((state, rho_randomness))
    }

    /// `rho_randomness` is the random value used to derive `rho` via Poseidon hash.
    pub fn new_given_randomness(
        id: G::ScalarField,
        pk_aff: G,
        pk_enc: G,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        randomness: G::ScalarField,
        rho_randomness: G::ScalarField,
        poseidon_config: Poseidon2Params<G::ScalarField>,
    ) -> Result<Self> {
        if asset_id > MAX_ASSET_ID {
            return Err(Error::AssetIdTooLarge(asset_id));
        }
        let combined = Self::concat_asset_id_counter(asset_id, counter);
        let rho =
            Poseidon_hash_2_simple::<G::ScalarField>(rho_randomness, combined, poseidon_config)?;
        let current_rho = rho.square();
        let current_randomness = randomness.square();
        Ok(Self {
            pk_aff,
            pk_enc,
            id,
            balance: 0,
            counter: 0,
            asset_id,
            rho,
            current_rho,
            randomness,
            current_randomness,
        })
    }

    pub fn commit(
        &self,
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<AccountStateCommitment<G>> {
        let comm = G::Group::msm(
            &account_comm_key.as_gens_without_sk()[..],
            &[
                G::ScalarField::from(self.balance),
                G::ScalarField::from(self.counter),
                G::ScalarField::from(self.asset_id),
                self.rho,
                self.current_rho,
                self.randomness,
                self.current_randomness,
                self.id,
            ],
        )
        .map_err(Error::size_mismatch)?
            + self.pk_aff
            + self.pk_enc;
        Ok(AccountStateCommitment(comm.into_affine()))
    }

    pub fn asset_id(&self) -> AssetId {
        self.asset_id
    }

    pub fn balance(&self) -> Balance {
        self.balance
    }

    pub fn counter(&self) -> PendingTxnCounter {
        self.counter
    }

    pub fn pk_aff(&self) -> G {
        self.pk_aff
    }

    pub fn pk_enc(&self) -> G {
        self.pk_enc
    }

    pub fn rho(&self) -> G::ScalarField {
        self.rho
    }

    pub fn current_rho(&self) -> G::ScalarField {
        self.current_rho
    }

    pub fn randomness(&self) -> G::ScalarField {
        self.randomness
    }

    pub fn current_randomness(&self) -> G::ScalarField {
        self.current_randomness
    }

    pub fn id(&self) -> G::ScalarField {
        self.id
    }

    pub fn nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        (comm_key.current_rho_gen() * self.current_rho).into()
    }

    /// Set rho and commitment randomness to new values. Used as each update to the account state
    /// needs these refreshed.
    pub fn refresh_randomness_for_state_change(&mut self) {
        self.current_rho *= self.rho;
        self.current_randomness *= self.randomness;
    }

    pub fn get_state_for_mint(&self, amount: u64) -> Result<Self> {
        if amount + self.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new = self.clone();
        new.balance += amount;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    pub fn get_state_for_send(&self, amount: u64) -> Result<Self> {
        if amount > self.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        let mut new = self.clone();
        new.balance -= amount;
        new.counter += 1;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    pub fn get_state_for_receive(&self) -> Self {
        let mut new = self.clone();
        new.counter += 1;
        new.refresh_randomness_for_state_change();
        new
    }

    pub fn get_state_for_claiming_received(&self, amount: u64) -> Result<Self> {
        if self.counter == 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be greater than 0".to_string(),
            ));
        }
        if amount + self.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new = self.clone();
        new.balance += amount;
        new.counter -= 1;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    pub fn get_state_for_reversing_send(&self, amount: u64) -> Result<Self> {
        if self.counter == 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be greater than 0".to_string(),
            ));
        }
        if amount + self.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new = self.clone();
        new.balance += amount;
        new.counter -= 1;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    pub fn get_state_for_decreasing_counter(
        &self,
        decrease_counter_by: Option<PendingTxnCounter>,
    ) -> Result<Self> {
        let decrease_counter_by = decrease_counter_by.unwrap_or(1);
        if self.counter < decrease_counter_by {
            return Err(Error::ProofOfBalanceError(
                "Counter cannot be decreased below zero".to_string(),
            ));
        }
        let mut new = self.clone();
        new.counter -= decrease_counter_by;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    pub fn get_state_for_irreversible_send(&self, amount: u64) -> Result<Self> {
        if amount > self.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        let mut new = self.clone();
        new.balance -= amount;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    pub fn get_state_for_irreversible_receive(&self, amount: u64) -> Result<Self> {
        if amount + self.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new = self.clone();
        new.balance += amount;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    pub fn get_state_for_deposit(&self, amount: u64) -> Result<Self> {
        if amount + self.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new = self.clone();
        new.balance += amount;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    pub fn get_state_for_withdraw(&self, amount: u64) -> Result<Self> {
        if amount > self.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        let mut new = self.clone();
        new.balance -= amount;
        new.refresh_randomness_for_state_change();
        Ok(new)
    }

    /// Append bytes of counter to bytes of asset id. `combined = asset_id || counter`
    /// NOTE: Assumes for correctness, that the concatenation can fit in 64 bytes
    pub(crate) fn concat_asset_id_counter(
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> G::ScalarField {
        let combined: u64 = (asset_id as u64) << 32 | (counter as u64);
        G::ScalarField::from(combined)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountStateCommitment<G: AffineRepr>(pub G);
