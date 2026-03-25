#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, DecodeWithMemTracking, Encode};
use scale_info::TypeInfo;

use ark_ec::CurveConfig;
use ark_std::vec::Vec;

use bounded_collections::{BoundedBTreeMap, BoundedBTreeSet};
use rand_core::{CryptoRng, RngCore};

use super::*;
use crate::*;
use polymesh_dart_bp::account::mint::MintTxnProof;

/// Represents the state of an asset in the Dart BP protocol.
///
/// The asset state includes the asset ID, the encryption keys for auditors and mediators, and the mapping of mediators to their encryption keys.
#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AssetState<T: DartLimits = ()> {
    pub asset_id: AssetId,
    // The encryption keys for both auditors and mediators are stored in the asset state.
    auditors: BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
    // The mediators are stored as a map from their `affirmation_key` to their encryption key.
    mediators: BoundedBTreeMap<AccountPublicKey, EncryptionPublicKey, T::MaxAssetMediators>,
}

impl<T: DartLimits> AssetState<T> {
    /// Creates a new asset state with the given asset ID, mediators, and auditors.
    ///
    /// `mediators` is a slice of `(enc_key_index, affirmation_key)` pairs. The index must point to
    /// a valid entry in `auditors` (i.e., `< auditors.len()`).
    pub fn new(
        asset_id: AssetId,
        mediators: &[(AccountPublicKey, EncryptionPublicKey)],
        auditors: &[EncryptionPublicKey],
    ) -> Result<Self, Error> {
        let mut state = Self {
            asset_id,
            auditors: Default::default(),
            mediators: Default::default(),
        };

        // Ensure the total number of encryption keys does not exceed the maximum allowed by the protocol limits.
        if (auditors.len() + mediators.len()) > T::MaxAssetEncryptionKeys::get() as usize {
            return Err(Error::BoundedContainerSizeLimitExceeded);
        }
        // Try adding the encryption keys for auditors and mediators to the asset state, ensuring that the number of each does not exceed the maximum allowed by the protocol limits.
        for auditor in auditors {
            state
                .auditors
                .try_insert(*auditor)
                .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        }

        for (acc_key, enc_key) in mediators {
            state
                .mediators
                .try_insert(*acc_key, *enc_key)
                .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        }
        Ok(state)
    }

    /// Creates a new asset state from pre-bounded collections.
    pub fn new_bounded(
        asset_id: AssetId,
        mediators: &BoundedBTreeMap<AccountPublicKey, EncryptionPublicKey, T::MaxAssetMediators>,
        auditors: &BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
    ) -> Result<Self, Error> {
        // Ensure the total number of encryption keys does not exceed the maximum allowed by the protocol limits.
        if (auditors.len() + mediators.len()) > T::MaxAssetEncryptionKeys::get() as usize {
            return Err(Error::BoundedContainerSizeLimitExceeded);
        }
        Ok(Self {
            asset_id,
            auditors: auditors.clone(),
            mediators: mediators.clone(),
        })
    }

    pub fn get_encryption_and_mediator_keys(
        &self,
    ) -> Result<(Vec<PallasA>, Vec<(u8, PallasA)>), Error> {
        // Create a sorted set of auditor and mediator encryption keys, ensuring that there are no duplicates.
        let mut enc_key_set = self.auditors.clone().into_inner();
        for enc_key in self.mediators.values() {
            enc_key_set.insert(*enc_key);
        }

        // Create a list of mediators with their corresponding encryption key indices.
        let mut med_keys = Vec::with_capacity(self.mediators.len());
        for (account_key, enc_key) in &self.mediators {
            // Get the index of the encryption key for the mediator.  This shouldn't fail since the encryption keys for mediators are included in the `enc_key_list`.
            let enc_idx = enc_key_set
                .iter()
                .position(|auditor_key| auditor_key == enc_key)
                .ok_or_else(|| Error::EncryptionKeyMissing)?;
            med_keys.push((enc_idx as u8, account_key.get_affine()?));
        }

        // Convert encryption keys to affine points and return them along with the mediator keys.
        let enc_keys = enc_key_set
            .into_iter()
            .map(|enc_key| enc_key.get_affine())
            .collect::<Result<_, _>>()?;

        Ok((enc_keys, med_keys))
    }

    pub fn asset_data(&self) -> Result<AssetCommitmentData, Error> {
        let tree_params = get_asset_curve_tree_parameters();
        let asset_comm_params = get_asset_commitment_parameters();
        let (enc_keys, med_keys) = self.get_encryption_and_mediator_keys()?;
        let asset_data = AssetCommitmentData::new(
            self.asset_id,
            enc_keys,
            med_keys,
            asset_comm_params,
            tree_params.odd_parameters.sl_params.delta,
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
#[derive(Clone, Encode, Decode, DecodeWithMemTracking, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct AssetMintingProof<C: CurveTreeConfig = AccountTreeConfig> {
    // Public inputs.
    pub pk: AccountPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    inner: WrappedCanonical<BPMintTxnProof<C>>,
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
        keys: &AccountKeys,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        amount: Balance,
    ) -> Result<Self, Error> {
        // Generate a new minting state for the account asset.
        let state_change = account_asset.mint(keys, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;
        let pk = keys.acct.public;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let (proof, nullifier) = MintTxnProof::new::<_, _, _>(
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

            inner: WrappedCanonical::wrap(&proof)?,
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
        let proof = self.inner.decode()?;
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
