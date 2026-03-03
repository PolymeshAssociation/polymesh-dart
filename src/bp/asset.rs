#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, DecodeWithMemTracking, Encode};
use scale_info::TypeInfo;

use ark_ec::CurveConfig;
use ark_std::vec::Vec;

use bounded_collections::BoundedBTreeSet;
use rand_core::{CryptoRng, RngCore};

use super::*;
use crate::*;
use ark_ec_divisors::curves::{pallas::Point as PallasPoint, vesta::Point as VestaPoint};
use polymesh_dart_bp::account::mint::MintTxnProof;

/// Represents the state of an asset in the Dart BP protocol.
///
/// - `auditors`: encryption keys shared between auditors and mediators (used to decrypt leg contents)
/// - `mediators`: pairs of `(enc_key_index, affirmation_key)` where `enc_key_index` is an index into the
///   `auditors` set pointing to the shared encryption key this mediator uses for decryption, and
///   `affirmation_key` is the mediator's signing/affirmation key used to prove their identity.
///
/// This mirrors [`dart_bp::leg::AssetData`]'s `enc_keys` / `med_keys` fields exactly.
#[derive(Clone, Debug, Encode, Decode, DecodeWithMemTracking, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct AssetState<T: DartLimits = ()> {
    pub asset_id: AssetId,
    /// `(enc_key_index, affirmation_key)` — index points into `auditors` (the shared enc-keys list)
    pub mediators: BoundedBTreeSet<(u8, AccountPublicKey), T::MaxAssetMediators>,
    pub auditors: BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
}

impl<T: DartLimits> AssetState<T> {
    /// Creates a new asset state with the given asset ID, mediators, and auditors.
    ///
    /// `mediators` is a slice of `(enc_key_index, affirmation_key)` pairs. The index must point to
    /// a valid entry in `auditors` (i.e., `< auditors.len()`).
    pub fn new(
        asset_id: AssetId,
        mediators: &[(u8, AccountPublicKey)],
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

    /// Creates a new asset state from pre-bounded collections.
    pub fn new_bounded(
        asset_id: AssetId,
        mediators: &BoundedBTreeSet<(u8, AccountPublicKey), T::MaxAssetMediators>,
        auditors: &BoundedBTreeSet<EncryptionPublicKey, T::MaxAssetAuditors>,
    ) -> Self {
        Self {
            asset_id,
            auditors: auditors.clone(),
            mediators: mediators.clone(),
        }
    }

    pub fn asset_data(&self) -> Result<AssetCommitmentData, Error> {
        let tree_params = get_asset_curve_tree_parameters();
        let asset_comm_params = get_asset_commitment_parameters();
        let enc_keys: Vec<PallasA> = self
            .auditors
            .iter()
            .map(|a| a.get_affine())
            .collect::<Result<_, _>>()?;
        let med_keys: Vec<(u8, PallasA)> = self
            .mediators
            .iter()
            .map(|(idx, pk)| Ok((*idx, pk.get_affine()?)))
            .collect::<Result<_, Error>>()?;
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

        let (proof, nullifier) = MintTxnProof::new::<_, PallasPoint, VestaPoint, _, _>(
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
