use ark_std::collections::BTreeMap;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use bounded_collections::BoundedVec;
use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use crate::curve_tree::CompressedCurveTreeRoot;

use super::*;

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct ProofHash(#[cfg_attr(feature = "serde", serde(with = "human_hex"))] pub [u8; 32]);

/// A single batched proof (no identity).
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub enum BatchedProof<T: DartLimits = ()> {
    CreateSettlement(SettlementProof<T>),
    SenderAffirmation(SenderAffirmationProof),
    ReceiverAffirmation(ReceiverAffirmationProof),
    MediatorAffirmation(MediatorAffirmationProof),
    SenderCounterUpdate(SenderCounterUpdateProof),
    SenderReversal(SenderReversalProof),
    ReceiverClaim(ReceiverClaimProof),
}

/// A batch of DART proofs.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct BatchedProofs<T: DartLimits = ()> {
    pub proofs: BoundedVec<BatchedProof<T>, T::MaxBatchedProofs>,
}

impl<T: DartLimits> BatchedProofs<T> {
    /// Creates a new, empty instance of `BatchedProofs`.
    pub fn new() -> Self {
        Self {
            proofs: BoundedVec::new(),
        }
    }

    /// Adds a new proof to the batch.
    pub fn push(&mut self, proof: BatchedProof<T>) -> Result<(), Error> {
        self.proofs
            .try_push(proof)
            .map_err(|_| Error::TooManyBatchedProofs)
    }

    /// Get the number of proofs in the batch.
    pub fn len(&self) -> usize {
        self.proofs.len()
    }

    pub fn hash(&self) -> ProofHash {
        ProofHash(blake2_256(self))
    }

    pub fn ctx(&self, ctx: &[u8]) -> Vec<u8> {
        (ctx, self.hash()).encode()
    }
}

/// This is used to collect roots from a batch of proofs.
pub struct BatchTreeRoots {
    pub asset_tree: BatchCompressedCurveTreeRoots<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>,
    pub account_tree:
        BatchCompressedCurveTreeRoots<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
    pub fee_account_tree:
        BatchCompressedCurveTreeRoots<FEE_ACCOUNT_TREE_L, FEE_ACCOUNT_TREE_M, FeeAccountTreeConfig>,
}

impl BatchTreeRoots {
    /// Creates a new instance of `BatchTreeRoots` with the given history length and parameters.
    pub fn new() -> Self {
        Self {
            asset_tree: BatchCompressedCurveTreeRoots::new(),
            account_tree: BatchCompressedCurveTreeRoots::new(),
            fee_account_tree: BatchCompressedCurveTreeRoots::new(),
        }
    }

    /// Adds a new asset tree root to the batch.
    pub fn push_asset_root(
        &mut self,
        block_number: BlockNumber,
        asset_tree: &impl ValidateCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>,
    ) -> Result<(), Error> {
        self.asset_tree.push_root(block_number, asset_tree)
    }

    /// Adds a new account tree root to the batch.
    pub fn push_account_root(
        &mut self,
        block_number: BlockNumber,
        account_tree: &impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
    ) -> Result<(), Error> {
        self.account_tree.push_root(block_number, account_tree)
    }

    /// Adds a new fee account tree root to the batch.
    pub fn push_fee_account_root(
        &mut self,
        block_number: BlockNumber,
        fee_account_tree: &impl ValidateCurveTreeRoot<
            FEE_ACCOUNT_TREE_L,
            FEE_ACCOUNT_TREE_M,
            FeeAccountTreeConfig,
        >,
    ) -> Result<(), Error> {
        self.fee_account_tree
            .push_root(block_number, fee_account_tree)
    }
}

/// This is used to collect compressed curve tree roots from a batch of proofs.
pub struct BatchCompressedCurveTreeRoots<const L: usize, const M: usize, C: CurveTreeConfig> {
    roots: BTreeMap<BlockNumber, CompressedCurveTreeRoot<L, M, C>>,
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> BatchCompressedCurveTreeRoots<L, M, C> {
    /// Creates a new instance of `RootHistory` with the given history length and parameters.
    pub fn new() -> Self {
        Self {
            roots: BTreeMap::new(),
        }
    }

    /// Adds a new root to the batch.
    pub fn push_root(
        &mut self,
        block_number: BlockNumber,
        tree: &impl ValidateCurveTreeRoot<L, M, C>,
    ) -> Result<(), Error> {
        if self.roots.contains_key(&block_number) {
            return Ok(());
        }
        let root = tree
            .get_block_root(block_number)
            .ok_or(Error::CurveTreeRootNotFound)?;
        self.roots.insert(block_number, root);
        Ok(())
    }
}

impl<const L: usize, const M: usize, C: CurveTreeConfig> ValidateCurveTreeRoot<L, M, C>
    for &BatchCompressedCurveTreeRoots<L, M, C>
{
    fn get_block_root(&self, block: BlockNumber) -> Option<CompressedCurveTreeRoot<L, M, C>> {
        let block: BlockNumber = block.try_into().ok()?;
        self.roots.get(&block).cloned()
    }

    fn params(&self) -> &CurveTreeParameters<C> {
        C::parameters()
    }
}
