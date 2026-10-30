use ark_ec::AffineRepr;
use ark_serialize::CanonicalSerialize;

pub const NUM_GENERATORS: usize = 10;

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
pub(crate) const SK_ENC_GEN_INDEX: usize = 9;

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
        self[SK_ENC_GEN_INDEX]
    }
}
