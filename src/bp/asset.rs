use ark_std::collections::{BTreeMap, BTreeSet};
use core::ops::{Deref, DerefMut};

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, DecodeWithMemTracking, Encode};
use scale_info::TypeInfo;

use ark_ec::CurveConfig;
use ark_std::vec::Vec;

use bounded_collections::{BoundedBTreeMap, BoundedBTreeSet};
use dock_crypto_utils::randomized_mult_checker::PairRandomizedMultCheckerGuard;
use rand_core::{CryptoRng, RngCore};

use super::*;
use crate::{auth_proofs::create_registration_auth_proof, mint_split::MintHostProtocol, *};
use polymesh_dart_bp::account::mint::MintTxnProof;

#[derive(Clone, Debug, Encode, Decode, Default, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AssetKeysLookup {
    pub assets: BTreeMap<AssetId, AssetKeys>,
}

impl AssetKeysLookup {
    pub fn new() -> Self {
        Self {
            assets: BTreeMap::new(),
        }
    }

    pub fn add(&mut self, asset_state: AssetState) {
        self.assets.insert(asset_state.asset_id, asset_state.keys);
    }

    pub fn get_keys(&self, asset_id: AssetId) -> Result<(Vec<PallasA>, Vec<(u8, PallasA)>), Error> {
        let asset_keys = self
            .assets
            .get(&asset_id)
            .ok_or_else(|| Error::AssetNotFound(asset_id))?;
        asset_keys.get_keys()
    }
}

impl Deref for AssetKeysLookup {
    type Target = BTreeMap<AssetId, AssetKeys>;

    fn deref(&self) -> &Self::Target {
        &self.assets
    }
}

impl DerefMut for AssetKeysLookup {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.assets
    }
}

impl From<&AssetState> for AssetKeysLookup {
    fn from(asset_state: &AssetState) -> Self {
        let mut assets = BTreeMap::new();
        assets.insert(asset_state.asset_id, asset_state.keys.clone());
        Self { assets }
    }
}

/// Represents the encryption keys and mediator affirmation keys associated with an asset in the Dart BP protocol.
#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AssetKeys {
    /// The encryption keys for auditors and mediators are stored in a set to ensure uniqueness.
    pub enc_keys: BTreeSet<EncryptionPublicKey>,
    /// The mediators are stored as a map from their `affirmation_key` to their encryption key.
    pub mediators: BTreeMap<AccountPublicKey, u8>,
}

impl AssetKeys {
    pub fn new_bounded<T: DartLimits>(
        mediators: &BoundedBTreeMap<AccountPublicKey, EncryptionPublicKey, T::MaxAssetMediators>,
        auditors: &BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
    ) -> Result<Self, Error> {
        // Ensure the total number of encryption keys does not exceed the maximum allowed by the protocol limits.
        if (auditors.len() + mediators.len()) > T::MaxAssetEncryptionKeys::get() as usize {
            return Err(Error::BoundedContainerSizeLimitExceeded);
        }
        let mut asset = AssetKeys {
            enc_keys: Default::default(),
            mediators: Default::default(),
        };
        // Create a sorted set of auditor and mediator encryption keys, ensuring that there are no duplicates.
        for auditor_key in auditors {
            asset.enc_keys.insert(*auditor_key);
        }
        for enc_key in mediators.values() {
            asset.enc_keys.insert(*enc_key);
        }

        // Create a list of mediators with their corresponding encryption key indices.
        for (account_key, enc_key) in mediators {
            // Get the index of the encryption key for the mediator.  This shouldn't fail since the encryption keys for mediators are included in the `enc_key_list`.
            let enc_idx = asset
                .enc_keys
                .iter()
                .position(|auditor_key| auditor_key == enc_key)
                .ok_or_else(|| Error::EncryptionKeyMissing)?;
            asset.mediators.insert(*account_key, enc_idx as u8);
        }

        Ok(asset)
    }

    pub fn get_keys(&self) -> Result<(Vec<PallasA>, Vec<(u8, PallasA)>), Error> {
        // Convert encryption keys to affine points.
        let enc_keys = self
            .enc_keys
            .iter()
            .map(|enc_key| enc_key.get_affine())
            .collect::<Result<_, _>>()?;
        // Convert mediator encryption keys to affine points and pair them with their corresponding affirmation key indices.
        let med_keys = self
            .mediators
            .iter()
            .map(|(account_key, enc_idx)| Ok((*enc_idx, account_key.get_affine()?)))
            .collect::<Result<_, Error>>()?;

        Ok((enc_keys, med_keys))
    }

    /// Generates the asset commitment data for this asset state, which includes the asset ID, encryption keys, mediator keys, and the parameters for the asset commitment scheme.
    pub fn asset_data(&self, asset_id: AssetId) -> Result<AssetCommitmentData, Error> {
        let tree_params = get_asset_curve_tree_parameters();
        let asset_comm_params = get_asset_commitment_parameters();
        let (enc_keys, med_keys) = self.get_keys()?;
        let asset_data = AssetCommitmentData::new(
            asset_id,
            enc_keys,
            med_keys,
            asset_comm_params,
            tree_params.odd_parameters.sl_params.delta,
        )?;
        Ok(asset_data)
    }

    /// Computes the commitment for this asset state, which is used in the Dart BP protocol to represent the asset state in a compact form.
    pub fn commitment(
        &self,
        asset_id: AssetId,
    ) -> Result<CompressedLeafValue<AssetTreeConfig>, Error> {
        let asset_data = self.asset_data(asset_id)?;
        CompressedLeafValue::from_affine(asset_data.commitment)
    }
}

/// Represents the state of an asset in the Dart BP protocol.
///
/// The asset state includes the asset ID, the encryption keys for auditors and mediators, and the mapping of mediators to their encryption keys.
#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AssetState {
    /// The unique identifier for the asset.
    pub asset_id: AssetId,
    /// The encryption keys for auditors and mediators, along with the mapping of mediators to their encryption key indices.
    pub keys: AssetKeys,
}

impl AssetState {
    /// Creates a new asset state with the given asset ID, mediators, and auditors.
    ///
    /// `mediators` is a slice of `(enc_key_index, affirmation_key)` pairs. The index must point to
    /// a valid entry in `auditors` (i.e., `< auditors.len()`).
    pub fn new<T: DartLimits>(
        asset_id: AssetId,
        mediators: &[(AccountPublicKey, EncryptionPublicKey)],
        auditors: &[EncryptionPublicKey],
    ) -> Result<Self, Error> {
        // Ensure the total number of encryption keys does not exceed the maximum allowed by the protocol limits.
        if (auditors.len() + mediators.len()) > T::MaxAssetEncryptionKeys::get() as usize {
            return Err(Error::BoundedContainerSizeLimitExceeded);
        }
        let mut enc_keys = BoundedBTreeSet::new();
        let mut mediator_keys = BoundedBTreeMap::new();

        // Try adding the encryption keys for auditors and mediators to the asset state, ensuring that the number of each does not exceed the maximum allowed by the protocol limits.
        for auditor in auditors {
            enc_keys
                .try_insert(*auditor)
                .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        }

        for (acc_key, enc_key) in mediators {
            mediator_keys
                .try_insert(*acc_key, *enc_key)
                .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        }
        Self::new_bounded::<T>(asset_id, &mediator_keys, &enc_keys)
    }

    /// Creates a new asset state from pre-bounded collections.
    pub fn new_bounded<T: DartLimits>(
        asset_id: AssetId,
        mediators: &BoundedBTreeMap<AccountPublicKey, EncryptionPublicKey, T::MaxAssetMediators>,
        auditors: &BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
    ) -> Result<Self, Error> {
        Ok(Self {
            asset_id,
            keys: AssetKeys::new_bounded::<T>(mediators, auditors)?,
        })
    }

    /// Retrieves the encryption keys for auditors and mediators, along with the indices of the mediator keys in the list of encryption keys.
    pub fn get_encryption_and_mediator_keys(
        &self,
    ) -> Result<(Vec<PallasA>, Vec<(u8, PallasA)>), Error> {
        self.keys.get_keys()
    }

    /// Generates the asset commitment data for this asset state, which includes the asset ID, encryption keys, mediator keys, and the parameters for the asset commitment scheme.
    pub fn asset_data(&self) -> Result<AssetCommitmentData, Error> {
        self.keys.asset_data(self.asset_id)
    }

    /// Computes the commitment for this asset state, which is used in the Dart BP protocol to represent the asset state in a compact form.
    pub fn commitment(&self) -> Result<CompressedLeafValue<AssetTreeConfig>, Error> {
        self.keys.commitment(self.asset_id)
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
    pub pk_enc: EncryptionPublicKey,
    pub asset_id: AssetId,
    pub amount: Balance,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    pub(crate) inner: WrappedCanonical<BPMintTxnProof<C>>,
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
        identity: &[u8],
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        amount: Balance,
    ) -> Result<Self, Error> {
        let root_block = tree_lookup.get_block_number()?;

        let (protocol, device_request) = MintHostProtocol::<C>::init(
            rng,
            &keys.public_keys(),
            account_asset,
            amount,
            identity,
            &tree_lookup,
        )?;

        let gens = dart_gens();
        let device_response = create_registration_auth_proof(
            rng,
            keys.acct.secret.0.0,
            keys.enc.secret.0.0,
            &device_request,
            gens.account_comm_key().sk_gen(),
            gens.account_comm_key().sk_enc_gen(),
        )?;

        let proof = protocol.finish(rng, &device_response, root_block, tree_lookup.params())?;
        Ok(proof)
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

        PairRandomizedMultCheckerGuard::new_using_rng(rng).with(
            |even_rmc, odd_rmc| -> Result<(), Error> {
                proof.verify_split(
                    self.pk.get_affine()?,
                    self.pk_enc.get_affine()?,
                    id,
                    self.asset_id,
                    self.amount,
                    self.updated_account_state_commitment.as_commitment()?,
                    self.nullifier.get_affine()?,
                    &root,
                    identity,
                    tree_roots.params(),
                    dart_gens().account_comm_key(),
                    rng,
                    Some((even_rmc, odd_rmc)),
                )?;
                Ok(())
            },
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
