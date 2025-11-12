#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, Encode};
use scale_info::TypeInfo;

use ark_ec::CurveConfig;
use ark_std::vec::Vec;

use bounded_collections::BoundedBTreeSet;
use rand_core::{CryptoRng, RngCore};

use super::*;
use crate::*;
use polymesh_dart_bp::account as bp_account;
use polymesh_dart_bp::account::mint::MintTxnProof;

/// Represents the state of an asset in the Dart BP protocol.
#[derive(Clone, Debug, Encode, Decode, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AssetState<T: DartLimits = ()> {
    pub asset_id: AssetId,
    pub mediators: BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetMediators>,
    pub auditors: BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
}

impl<T: DartLimits> AssetState<T> {
    /// Creates a new asset state with the given asset ID, mediator status, and public key.
    pub fn new(
        asset_id: AssetId,
        mediators: &[EncryptionPublicKey],
        auditors: &[EncryptionPublicKey],
    ) -> Self {
        let mut state = Self {
            asset_id,
            auditors: Default::default(),
            mediators: Default::default(),
        };

        for mediator in mediators {
            state
                .mediators
                .try_insert(*mediator)
                .expect("Too many asset mediators");
        }
        for auditor in auditors {
            state
                .auditors
                .try_insert(*auditor)
                .expect("Too many asset auditors");
        }

        state
    }

    /// Creates a new asset state with the given asset ID, mediator status, and public key.
    pub fn new_bounded(
        asset_id: AssetId,
        mediators: &BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetMediators>,
        auditors: &BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
    ) -> Self {
        Self {
            asset_id,
            auditors: auditors.clone(),
            mediators: mediators.clone(),
        }
    }

    pub fn keys(&self) -> Vec<(bool, PallasA)> {
        let mut keys = Vec::with_capacity(self.auditors.len() + self.mediators.len());
        for mediator in &self.mediators {
            keys.push((false, mediator.get_affine().unwrap()));
        }
        for auditor in &self.auditors {
            keys.push((true, auditor.get_affine().unwrap()));
        }
        keys
    }

    pub fn asset_data(&self) -> Result<AssetCommitmentData, Error> {
        let tree_params = get_asset_curve_tree_parameters();
        let asset_comm_params = get_asset_commitment_parameters();
        let asset_data = AssetCommitmentData::new(
            self.asset_id,
            self.keys(),
            asset_comm_params,
            tree_params.odd_parameters.delta,
        )?;
        Ok(asset_data)
    }

    pub fn commitment(&self) -> Result<CompressedLeafValue<AssetTreeConfig>, Error> {
        let asset_data = self.asset_data()?;
        CompressedLeafValue::from_affine(asset_data.commitment)
    }
}

type BPMintTxnProof<C> = MintTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// Asset minting proof.  Report section 5.1.4 "Increase Asset Supply".
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct AssetMintingProof<C: CurveTreeConfig = AccountTreeConfig> {
    // Public inputs.
    pub pk: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    // proof
    proof: WrappedCanonical<BPMintTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> AssetMintingProof<C>
{
    /// Generate a new asset minting proof.
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        amount: Balance,
    ) -> Result<Self, Error> {
        // Generate a new minting state for the account asset.
        let state_change = account_asset.mint(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;
        let pk = account.public;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let (proof, nullifier) = MintTxnProof::new(
            rng,
            pk.get_affine()?,
            amount,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            // TODO: Use the caller's identity?
            b"",
            tree_lookup.params(),
            dart_gens().account_comm_key(),
        )?;
        Ok(Self {
            pk,
            asset_id: account_asset.asset_id(),
            amount,
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        identity: &[u8],
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let id = hash_identity::<PallasScalar>(identity);
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for asset minting proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        let proof = self.proof.decode()?;
        proof.verify(
            self.pk.get_affine()?,
            id,
            self.asset_id,
            self.amount,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            &root,
            b"",
            tree_roots.params(),
            dart_gens().account_comm_key(),
            rng,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for AssetMintingProof<C> {
    fn account_state_commitment(&self) -> AccountStateCommitment {
        self.updated_account_state_commitment
    }

    fn nullifier(&self) -> AccountStateNullifier {
        self.nullifier
    }

    fn root_block(&self) -> BlockNumber {
        self.root_block
    }
}
