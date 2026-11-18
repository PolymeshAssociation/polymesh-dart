//! Test chain configuration.
//!
//! These values mirror the Confidential Assets pallet `Config` parameters
//! (`Polymesh/pallets/confidential-assets/src/lib.rs`) so the CLI enforces the same bounds and
//! time windows as the pallet. Defaults are the testnet runtime values plus the `testing` feature
//! tree heights.

use polymesh_dart::NodeLevel;
use polymesh_dart_common as dc;
use serde::{Deserialize, Serialize};

/// Pallet timestamp (`pallet_timestamp::Pallet::<T>::get()`), in milliseconds.
pub type Moment = u64;

/// Which curve tree a storage row belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TreeKind {
    Asset,
    Account,
    FeeAccount,
}

impl TreeKind {
    pub fn name(&self) -> &'static str {
        match self {
            TreeKind::Asset => "asset",
            TreeKind::Account => "account",
            TreeKind::FeeAccount => "fee_account",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct TestConfig {
    /// `T::MaxTotalSupply` — the DART balance bound (`MAX_BALANCE`, 48 bits).
    pub max_total_supply: dc::Balance,
    /// Fee-account balance bound (`MAX_FEE_BALANCE`, 40 bits).
    pub max_fee_balance: dc::Balance,
    /// `T::MaxRelayerCommission`, in the fee currency.
    pub max_relayer_commission: u128,
    /// `T::MaxAssetDataLength`.
    pub max_asset_data_length: usize,
    /// `T::MaxTrustedClaimIssuers`.
    pub max_trusted_claim_issuers: usize,
    /// `T::MaxSharedKeyRecipients`.
    pub max_shared_key_recipients: usize,

    // DART proof bounds (`PolymeshLimits`).
    pub max_keys_per_reg_proof: usize,
    pub max_key_distribution_recipients: usize,
    pub max_batched_proofs: usize,
    pub max_fee_account_reg_proofs: usize,
    pub max_fee_account_topup_proofs: usize,
    pub max_account_asset_reg_proofs: usize,
    pub max_settlement_legs: usize,
    pub max_settlement_memo_length: usize,
    pub max_asset_auditors: usize,
    pub max_asset_mediators: usize,
    pub max_asset_encryption_keys: usize,
    pub max_public_enc_keys: usize,
    pub max_inner_proof_size: usize,

    // Curve tree hooks.
    /// `T::MinCurveTreeRootUpdateInterval`.
    pub min_curve_tree_root_update_interval: Moment,
    /// `T::MaxAssetCurveTreeRootAge`.
    pub max_asset_curve_tree_root_age: Moment,
    /// `T::MaxAccountCurveTreeRootAge`.
    pub max_account_curve_tree_root_age: Moment,
    /// `T::MaxFeeAccountCurveTreeRootAge`.
    pub max_fee_account_curve_tree_root_age: Moment,
    /// `MAX_ROOT_PRUNING_BLOCKS`.
    pub max_root_pruning_blocks: u32,
    /// `RECENT_BLOCKS_TO_KEEP`.
    pub recent_blocks_to_keep: u32,

    /// Genesis tree heights, mirroring the pallet's `*_TREE_HEIGHT` constants.
    pub asset_tree_height: NodeLevel,
    pub account_tree_height: NodeLevel,
    pub fee_account_tree_height: NodeLevel,

    /// Block time used when `end-block` advances the clock.
    pub block_time: Moment,

    /// Fee model used by the relayer fee-bounds check: `fee = base + fee_per_weight * weight +
    /// fee_per_byte * len`. This approximates `pallet_transaction_payment::compute_fee`; the CLI
    /// has no real weight metering, so weights are estimated from `db_reads/db_writes`.
    pub base_fee: u128,
    pub fee_per_weight_unit: u128,
    pub fee_per_byte: u128,
    pub weight_per_read: u64,
    pub weight_per_write: u64,
}

impl Default for TestConfig {
    fn default() -> Self {
        Self {
            max_total_supply: dc::MAX_BALANCE,
            max_fee_balance: dc::MAX_FEE_BALANCE,
            max_relayer_commission: 10 * 1_000_000, // 10 POLYX with 6 decimals
            max_asset_data_length: 8192,
            max_trusted_claim_issuers: 2,
            max_shared_key_recipients: 5,

            max_keys_per_reg_proof: dc::MAX_KEYS_PER_REG_PROOF as usize,
            max_key_distribution_recipients: dc::MAX_KEY_DISTRIBUTION_RECIPIENTS as usize,
            max_batched_proofs: dc::MAX_BATCHED_PROOFS as usize,
            max_fee_account_reg_proofs: dc::MAX_FEE_ACCOUNT_REG_PROOFS as usize,
            max_fee_account_topup_proofs: dc::MAX_FEE_ACCOUNT_TOPUP_PROOFS as usize,
            max_account_asset_reg_proofs: dc::MAX_ACCOUNT_ASSET_REG_PROOFS as usize,
            max_settlement_legs: dc::SETTLEMENT_MAX_LEGS as usize,
            max_settlement_memo_length: dc::MEMO_MAX_LENGTH as usize,
            max_asset_auditors: dc::MAX_ASSET_AUDITORS as usize,
            max_asset_mediators: dc::MAX_ASSET_MEDIATORS as usize,
            max_asset_encryption_keys: dc::MAX_ASSET_ENC_KEYS as usize,
            max_public_enc_keys: dc::MAX_PUBLIC_ENC_KEYS as usize,
            max_inner_proof_size: dc::MAX_INNER_PROOF_SIZE as usize,

            min_curve_tree_root_update_interval: 600_000,
            max_asset_curve_tree_root_age: 86_400_000,
            max_account_curve_tree_root_age: 172_800_000,
            max_fee_account_curve_tree_root_age: 14_400_000,
            max_root_pruning_blocks: 10,
            recent_blocks_to_keep: 100,

            // Pallet `testing` feature heights.
            asset_tree_height: 4,
            account_tree_height: 5,
            fee_account_tree_height: 5,

            block_time: 6_000,

            base_fee: 146_640,
            fee_per_weight_unit: 25,
            fee_per_byte: 1,
            weight_per_read: 25,
            weight_per_write: 100,
        }
    }
}

impl TestConfig {
    /// The `ci-runtime` parameter set: short windows so root age / pruning can be exercised in a
    /// small number of blocks.
    pub fn ci_runtime() -> Self {
        Self {
            min_curve_tree_root_update_interval: 18_000,
            max_asset_curve_tree_root_age: 60_000,
            max_account_curve_tree_root_age: 120_000,
            max_fee_account_curve_tree_root_age: 120_000,
            ..Self::default()
        }
    }

    pub fn max_age(&self, tree: TreeKind) -> Moment {
        match tree {
            TreeKind::Asset => self.max_asset_curve_tree_root_age,
            TreeKind::Account => self.max_account_curve_tree_root_age,
            TreeKind::FeeAccount => self.max_fee_account_curve_tree_root_age,
        }
    }

    pub fn genesis_height(&self, tree: TreeKind) -> NodeLevel {
        match tree {
            TreeKind::Asset => self.asset_tree_height,
            TreeKind::Account => self.account_tree_height,
            TreeKind::FeeAccount => self.fee_account_tree_height,
        }
    }
}
