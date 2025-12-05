use crate::poseidon_impls::poseidon_2::{Poseidon_hash_2_simple, Poseidon2Params};
use crate::{Error, error::Result};
use ark_ec::short_weierstrass::{Affine, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::UniformRand;
use ark_std::string::ToString;
use ark_std::vec::Vec;
use polymesh_dart_common::{
    AssetId, Balance, MAX_ASSET_ID, MAX_BALANCE, NullifierSkGenCounter, PendingTxnCounter,
};
use rand_core::CryptoRngCore;
use zeroize::{Zeroize, ZeroizeOnDrop};

/// This trait is used to abstract over the account commitment key. It allows us to use different
/// generators for the account commitment key while still providing the same interface.
pub trait AccountCommitmentKeyTrait<G: AffineRepr>: CanonicalSerialize + Clone {
    /// Returns the generator for the signing key.
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

    /// Returns the generator for the user's identity. This is bound to the public key but the relation
    /// between them is not proven in any of the proofs
    fn id_gen(&self) -> G;

    fn as_gens(&self) -> [G; NUM_GENERATORS] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            self.id_gen(),
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
            self.id_gen(),
            blinding,
        ]
    }
}

impl<G: AffineRepr> AccountCommitmentKeyTrait<G> for [G; NUM_GENERATORS] {
    fn sk_gen(&self) -> G {
        self[0]
    }

    fn balance_gen(&self) -> G {
        self[1]
    }

    fn counter_gen(&self) -> G {
        self[2]
    }

    fn asset_id_gen(&self) -> G {
        self[3]
    }

    fn rho_gen(&self) -> G {
        self[4]
    }

    fn current_rho_gen(&self) -> G {
        self[5]
    }

    fn randomness_gen(&self) -> G {
        self[6]
    }

    fn id_gen(&self) -> G {
        self[7]
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
    pub id: G::ScalarField,
    // TODO: Remove this later.
    pub sk: G::ScalarField,
    pub balance: Balance,
    pub counter: PendingTxnCounter,
    pub asset_id: AssetId,
    pub rho: G::ScalarField,
    pub current_rho: G::ScalarField,
    pub randomness: G::ScalarField,
}

// TODO: Add an account state batch abstraction that prevents manual update of field done in tests

impl<G> AccountState<G>
where
    G: AffineRepr,
{
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        id: G::ScalarField, // User can hash its string ID onto the field
        sk: G::ScalarField,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        poseidon_config: Poseidon2Params<G::ScalarField>,
    ) -> Result<Self> {
        let randomness = G::ScalarField::rand(rng);
        Self::new_given_randomness(id, sk, asset_id, counter, randomness, poseidon_config)
    }

    pub fn new_given_randomness(
        id: G::ScalarField, // User can hash its string ID onto the field
        sk: G::ScalarField,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
        randomness: G::ScalarField,
        poseidon_config: Poseidon2Params<G::ScalarField>,
    ) -> Result<Self> {
        if asset_id > MAX_ASSET_ID {
            return Err(Error::AssetIdTooLarge(asset_id));
        }
        let combined = Self::concat_asset_id_counter(asset_id, counter);
        let rho = Poseidon_hash_2_simple::<G::ScalarField>(sk, combined, poseidon_config)?;
        let current_rho = rho.square();

        Ok(Self {
            id,
            sk,
            balance: 0,
            counter: 0,
            asset_id,
            rho,
            current_rho,
            randomness,
        })
    }

    /// To be used when using [`RegTxnProofAlt`]
    pub fn new_alt<
        R: CryptoRngCore,
        G2: SWCurveConfig<BaseField = G::ScalarField, ScalarField = G::BaseField>,
    >(
        rng: &mut R,
        id: G::ScalarField,
        sk: G::ScalarField,
        asset_id: AssetId,
        pk_T_gen: Affine<G2>,
    ) -> Result<(Self, G2::ScalarField, G2::ScalarField)> {
        if asset_id > MAX_ASSET_ID {
            return Err(Error::AssetIdTooLarge(asset_id));
        }
        let mut r_1 = G2::ScalarField::rand(rng);
        while r_1.is_zero() {
            r_1 = G2::ScalarField::rand(rng);
        }
        let mut r_2 = G2::ScalarField::rand(rng);
        while r_2.is_zero() {
            r_2 = G2::ScalarField::rand(rng);
        }
        let p_1 = (pk_T_gen * r_1).into_affine();
        let p_2 = (pk_T_gen * r_2).into_affine();
        // r_1 and r_2 can't be 0 so unwrap is fine
        let rho = p_1.x().unwrap();
        let randomness = p_2.x().unwrap();
        let current_rho = rho.square();

        Ok((
            Self {
                id,
                sk,
                balance: 0,
                counter: 0,
                asset_id,
                rho,
                current_rho,
                randomness,
            },
            r_1,
            r_2,
        ))
    }

    pub fn commit(
        &self,
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<AccountStateCommitment<G>> {
        let comm = G::Group::msm(
            &account_comm_key.as_gens()[..],
            &[
                self.sk,
                G::ScalarField::from(self.balance),
                G::ScalarField::from(self.counter),
                G::ScalarField::from(self.asset_id),
                self.rho,
                self.current_rho,
                self.randomness,
                self.id,
            ],
        )
        .map_err(Error::size_mismatch)?;
        Ok(AccountStateCommitment(comm.into_affine()))
    }

    pub fn get_state_for_mint(&self, amount: u64) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        builder.update_for_mint(amount)?;
        Ok(builder.finalize())
    }

    pub fn get_state_for_send(&self, amount: u64) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        builder.update_for_send(amount)?;
        Ok(builder.finalize())
    }

    pub fn get_state_for_receive(&self) -> Self {
        let mut builder = AccountStateBuilder::init(self.clone());
        builder.update_for_receive();
        builder.finalize()
    }

    pub fn get_state_for_claiming_received(&self, amount: u64) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        builder.update_for_claiming_received(amount)?;
        Ok(builder.finalize())
    }

    pub fn get_state_for_reversing_send(&self, amount: u64) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        builder.update_for_reversing_send(amount)?;
        Ok(builder.finalize())
    }

    pub fn get_state_for_decreasing_counter(
        &self,
        decrease_counter_by: Option<PendingTxnCounter>,
    ) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        builder.update_for_decreasing_counter(decrease_counter_by)?;
        Ok(builder.finalize())
    }

    /// This assumes that an asset either does not have a mediator or mediator cannot reject.
    /// The chain should not allow mediator to reject else a new kind of reverse call has to be
    /// supported
    pub fn get_state_for_irreversible_send(&self, amount: u64) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        builder.update_for_irreversible_send(amount)?;
        Ok(builder.finalize())
    }

    /// This assumes that an asset either does not have a mediator or mediator cannot reject.
    /// The chain should not allow mediator to reject else a new kind of reverse call has to be
    /// supported
    pub fn get_state_for_irreversible_receive(&self, amount: u64) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        builder.update_for_irreversible_receive(amount)?;
        Ok(builder.finalize())
    }

    /// Deposit amount into account (increase balance only, no counter change)
    pub fn get_state_for_deposit(&self, amount: u64) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        if amount + builder.state.balance > MAX_BALANCE {
            return Err(Error::AmountTooLarge(amount + builder.state.balance));
        }
        builder.state.balance += amount;
        Ok(builder.finalize())
    }

    /// Withdraw amount from account (decrease balance only, no counter change)
    pub fn get_state_for_withdraw(&self, amount: u64) -> Result<Self> {
        let mut builder = AccountStateBuilder::init(self.clone());
        if amount > builder.state.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        builder.state.balance -= amount;
        Ok(builder.finalize())
    }

    /// Set rho and commitment randomness to new values. Used as each update to the account state
    /// needs these refreshed.
    pub fn refresh_randomness_for_state_change(&mut self) {
        self.current_rho = self.current_rho * self.rho;
        self.randomness.square_in_place();
    }

    pub fn nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        (comm_key.current_rho_gen() * self.current_rho).into()
    }

    pub(crate) fn initial_nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        (comm_key.rho_gen() * self.rho).into()
    }

    /// Append bytes of counter to bytes of asset id. `combined = asset_id || asset_id`
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

pub const NUM_GENERATORS: usize = 8;
