#[cfg(feature = "parallel")]
use rayon::prelude::*;

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

use ark_ec::{CurveConfig, short_weierstrass::Affine};
use ark_std::{
    format,
    string::{String, ToString},
    vec::Vec,
};
use bulletproofs::r1cs::VerificationTuple;
use curve_tree_relations::curve_tree::Root;

use blake2::Blake2b512;
use rand_core::{CryptoRng, RngCore};

use bounded_collections::BoundedVec;

use polymesh_dart_bp::leg as bp_leg;
use polymesh_dart_bp::util::batch_verify_bp_with_rng;
use polymesh_dart_common::{LegId, MediatorId};

use super::WrappedCanonical;
use crate::curve_tree::*;
use crate::*;

pub mod proofs;
pub use proofs::*;

pub mod instant;
pub use instant::*;

/// Counts of the legs and sender/receiver affirmations in a settlement (batched or instant).
#[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct SettlementCounts {
    pub leg_count: u32,
    pub sender_count: u64,
    pub receiver_count: u64,
    pub mediator_count: u64,
}

impl SettlementCounts {
    pub fn total_affirmations(&self) -> u64 {
        self.sender_count + self.receiver_count + self.mediator_count
    }
}

/// The settlement reference is the hash of the settlement creation proof.
#[derive(
    Copy, Clone, Debug, Default, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, example = "0x0000000000000000000000000000000000000000000000000000000000000000", format = Binary))]
pub struct SettlementRef(#[cfg_attr(feature = "serde", serde(with = "human_hex"))] pub [u8; 32]);

/// FromStr for SettlementRef from hex string.
impl core::str::FromStr for SettlementRef {
    type Err = hex::FromHexError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let offset = if s.starts_with("0x") { 2 } else { 0 };
        let mut buf = [0u8; 32];
        hex::decode_to_slice(&s[offset..], &mut buf[..])?;
        Ok(SettlementRef(buf))
    }
}

#[derive(
    Copy, Clone, Debug, Default, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub struct LegRef {
    /// The settlement reference.
    pub settlement: SettlementRef,
    /// The leg ID within the settlement.
    #[cfg_attr(feature = "utoipa", schema(example = 0, value_type = u8))]
    pub leg_id: LegId,
}

impl LegRef {
    pub fn new(settlement: SettlementRef, leg_id: LegId) -> Self {
        Self { settlement, leg_id }
    }

    /// Returns the leg ID.
    pub fn leg_id(&self) -> LegId {
        self.leg_id
    }

    /// Returns the settlement reference.
    pub fn settlement_ref(&self) -> SettlementRef {
        self.settlement
    }

    /// The settlement/leg context to tie proofs to a leg.
    pub fn context(&self) -> String {
        format!("{:?}-{}", self.settlement, self.leg_id)
    }
}

#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub enum LegRole {
    Sender,
    Receiver,
    Auditor(u8),
    Mediator(u8),
}

impl LegRole {
    pub fn is_sender_or_receiver(&self) -> bool {
        matches!(self, LegRole::Sender | LegRole::Receiver)
    }

    pub fn is_sender(&self) -> bool {
        matches!(self, LegRole::Sender)
    }
}

/// The decrypted leg details in the Dart BP protocol.
#[derive(Copy, Clone, Debug, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
pub struct Leg {
    /// Sender's confidential account.
    #[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary, example = "0xceae8587b3e968b9669df8eb715f73bcf3f7a9cd3c61c515a4d80f2ca59c8114"))]
    pub sender: AccountPublicKey,
    /// Receiver's confidential account.
    #[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary, example = "0xceae8587b3e968b9669df8eb715f73bcf3f7a9cd3c61c515a4d80f2ca59c8114"))]
    pub receiver: AccountPublicKey,
    /// Asset id.
    #[cfg_attr(feature = "utoipa", schema(example = 1, value_type = u64))]
    pub asset_id: AssetId,
    /// The amount for the asset in the leg.
    #[cfg_attr(feature = "utoipa", schema(example = 1000, value_type = u64))]
    pub amount: Balance,
}

impl Leg {
    pub fn new(
        sender: AccountPublicKey,
        receiver: AccountPublicKey,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<Self, Error> {
        Ok(Self {
            sender,
            receiver,
            asset_id,
            amount,
        })
    }

    pub fn encrypt<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        sender: EncryptionPublicKey,
        receiver: EncryptionPublicKey,
        asset_keys: &[(bool, PallasA)],
    ) -> Result<(bp_leg::Leg<PallasA>, LegEncrypted, LegEncryptionRandomness), Error> {
        let leg = bp_leg::Leg::new(
            self.sender.get_affine()?,
            self.receiver.get_affine()?,
            asset_keys.into(),
            self.amount,
            self.asset_id,
        )?;
        let (leg_enc, leg_enc_rand) = leg.encrypt::<_, Blake2b512>(
            rng,
            sender.get_affine()?,
            receiver.get_affine()?,
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;
        Ok((
            leg,
            LegEncrypted::new(leg_enc)?,
            LegEncryptionRandomness::new(leg_enc_rand)?,
        ))
    }

    pub fn sender(&self) -> Result<AccountPublicKey, Error> {
        Ok(self.sender)
    }

    pub fn receiver(&self) -> Result<AccountPublicKey, Error> {
        Ok(self.receiver)
    }

    pub fn asset_id(&self) -> AssetId {
        self.asset_id
    }

    pub fn amount(&self) -> Balance {
        self.amount
    }
}

/// A helper type to build the encrypted leg and its proof in the Dart BP protocol.
///
/// This builder type is different from the `Leg` type, which represents the decrypted leg details.
/// The `Leg` type doesn't hold the sender/receiver encryption keys that are needed to encrypt the leg
/// and generate the proof.
///
/// The leg builder holds the necessary information to create a leg, encrypt it, and generate the proof.
/// It is used as part of the settlement building process.
#[derive(Clone, Debug, Encode, Decode)]
pub struct LegBuilder {
    pub sender: AccountPublicKeys,
    pub receiver: AccountPublicKeys,
    pub asset: AssetState,
    pub amount: Balance,
}

impl LegBuilder {
    /// Creates a new leg with the given sender, receiver, asset ID, amount, and optional mediator.
    pub fn new(
        sender: AccountPublicKeys,
        receiver: AccountPublicKeys,
        asset: AssetState,
        amount: Balance,
    ) -> Self {
        Self {
            sender,
            receiver,
            asset,
            amount,
        }
    }

    pub fn encrypt_and_prove<
        R: RngCore + CryptoRng,
        C: CurveTreeConfig<
                F0 = <VestaParameters as CurveConfig>::ScalarField,
                F1 = <PallasParameters as CurveConfig>::ScalarField,
                P0 = VestaParameters,
                P1 = PallasParameters,
            >,
    >(
        &self,
        rng: &mut R,
        ctx: &[u8],
        asset_tree: &impl CurveTreeLookup<ASSET_TREE_L, ASSET_TREE_M, C>,
    ) -> Result<SettlementLegProof<C>, Error> {
        let asset_data = self.asset.asset_data()?;

        let leg = Leg::new(
            self.sender.acct,
            self.receiver.acct,
            self.asset.asset_id,
            self.amount,
        )?;
        let (leg, leg_enc, leg_enc_rand) =
            leg.encrypt(rng, self.sender.enc, self.receiver.enc, &asset_data.keys)?;

        let leg_proof = SettlementLegProof::new(
            rng,
            leg,
            leg_enc,
            &leg_enc_rand,
            asset_data,
            ctx,
            asset_tree,
        )?;

        Ok(leg_proof)
    }
}

#[derive(Clone, Encode, Decode)]
pub struct SettlementBuilder<T: DartLimits = ()> {
    pub memo: Vec<u8>,
    pub legs: Vec<LegBuilder>,
    paths: Option<MultiLeafPathAndRoot<ASSET_TREE_L, ACCOUNT_TREE_M, AssetTreeConfig>>,
    _marker: core::marker::PhantomData<T>,
}

impl<T: DartLimits> SettlementBuilder<T> {
    pub fn new(memo: &[u8]) -> Self {
        Self::new_full(memo, 0, None)
    }

    pub fn new_full(
        memo: &[u8],
        block_number: BlockNumber,
        root: Option<CompressedCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>>,
    ) -> Self {
        let paths = if let Some(root) = root {
            Some(MultiLeafPathAndRoot::new_root(block_number, root))
        } else {
            None
        };
        Self {
            memo: memo.to_vec(),
            legs: Vec::new(),
            paths,
            _marker: core::marker::PhantomData,
        }
    }

    pub fn new_root(
        memo: &[u8],
        block_number: BlockNumber,
        root: CompressedCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig>,
    ) -> Self {
        Self::new_full(memo, block_number, Some(root))
    }

    pub fn block(&self) -> BlockNumber {
        self.paths.as_ref().map(|p| p.block_number()).unwrap_or(0)
    }

    pub fn add_path(
        &mut self,
        asset_id: AssetId,
        path: CurveTreePath<ASSET_TREE_L, AssetTreeConfig>,
    ) -> Result<(), Error> {
        if let Some(paths) = &mut self.paths {
            paths.push_path(asset_id as LeafIndex, path)
        } else {
            Err(Error::CurveTreeRootNotFound)
        }
    }

    pub fn leg(mut self, leg: LegBuilder) -> Self {
        self.add_leg(leg);
        self
    }

    pub fn add_leg(&mut self, leg: LegBuilder) {
        self.legs.push(leg);
    }

    pub fn build<R: RngCore + CryptoRng>(
        self,
        rng: &mut R,
    ) -> Result<SettlementProof<T, AssetTreeConfig>, Error> {
        if let Some(paths) = &self.paths {
            self.encrypt_and_prove(rng, paths)
        } else {
            Err(Error::CurveTreeRootNotFound)
        }
    }

    pub fn encrypt_and_prove<
        R: RngCore + CryptoRng,
        C: CurveTreeConfig<
                F0 = <VestaParameters as CurveConfig>::ScalarField,
                F1 = <PallasParameters as CurveConfig>::ScalarField,
                P0 = VestaParameters,
                P1 = PallasParameters,
            >,
    >(
        &self,
        rng: &mut R,
        asset_tree: impl CurveTreeLookup<ASSET_TREE_L, ASSET_TREE_M, C>,
    ) -> Result<SettlementProof<T, C>, Error> {
        let memo = BoundedVec::try_from(self.memo.clone())
            .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        // TODO: need to collect all asset leaf paths based on the `root_block` number.
        // To avoid getting paths based on different roots if a new block is produced during proof generation.
        let root_block = asset_tree.get_block_number()?;

        let mut legs = Vec::with_capacity(self.legs.len());

        for (idx, leg_builder) in self.legs.iter().enumerate() {
            let ctx = (&memo, idx as u8).encode();
            let leg_proof = leg_builder.encrypt_and_prove(rng, &ctx, &asset_tree)?;
            legs.push(leg_proof);
        }

        let legs =
            BoundedVec::try_from(legs).map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        Ok(SettlementProof {
            memo,
            root_block: try_block_number(root_block)?,
            legs,
        })
    }
}

#[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T, C))]
pub struct SettlementProof<T: DartLimits = (), C: CurveTreeConfig = AssetTreeConfig> {
    pub memo: BoundedVec<u8, T::MaxSettlementMemoLength>,
    pub root_block: BlockNumber,

    pub legs: BoundedVec<SettlementLegProof<C>, T::MaxSettlementLegs>,
}

impl<
    T: DartLimits,
    C: CurveTreeConfig<
            F0 = <VestaParameters as CurveConfig>::ScalarField,
            F1 = <PallasParameters as CurveConfig>::ScalarField,
            P0 = VestaParameters,
            P1 = PallasParameters,
        >,
> SettlementProof<T, C>
{
    pub fn settlement_ref(&self) -> SettlementRef {
        SettlementRef(blake2_256(self))
    }

    /// Get leg and sender, receiver and mediator affirmation counts.
    pub fn count_leg_affirmations(&self) -> Result<SettlementCounts, Error> {
        let mut leg_count = 0;
        let mut mediator_count = 0;

        for leg_aff in &self.legs {
            leg_count += 1;
            mediator_count += leg_aff.mediator_count()? as u64;
        }

        Ok(SettlementCounts {
            leg_count,
            sender_count: leg_count as u64,
            receiver_count: leg_count as u64,
            mediator_count,
        })
    }

    #[cfg(feature = "parallel")]
    pub fn verify<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        asset_tree: impl ValidateCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = asset_tree
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for settlement proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        let memo = &*self.memo;
        self.legs.par_iter().enumerate().try_for_each_init(
            || rng.clone(),
            |rng, (idx, leg)| {
                let ctx = (memo, idx as u8).encode();
                leg.verify(&ctx, &root, rng)
            },
        )?;
        Ok(())
    }

    #[cfg(not(feature = "parallel"))]
    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        asset_tree: impl ValidateCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = asset_tree
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for settlement proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        for (idx, leg) in self.legs.iter().enumerate() {
            let ctx = (&self.memo, idx as u8).encode();
            leg.verify(&ctx, &root, rng)?;
        }
        Ok(())
    }

    #[cfg(feature = "parallel")]
    pub fn batched_verify<R: RngCore + CryptoRng + Send + Sync + Clone>(
        &self,
        asset_tree: impl ValidateCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let batch_size = self.legs.len();
        if batch_size < 2 {
            return self.verify(asset_tree, rng);
        }

        // Get the curve tree root.
        let root = asset_tree
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for settlement proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;
        let memo = &*self.memo;

        let tuples = self
            .legs
            .par_iter()
            .enumerate()
            .map_init(
                || rng.clone(),
                |rng, (idx, leg)| {
                    let ctx = (memo, idx as u8).encode();
                    leg.batched_verify(&ctx, &root, rng)
                },
            )
            .collect::<Result<Vec<_>, Error>>()?;

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);
        for (even, odd) in tuples {
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        batch_verify_bp_with_rng(even_tuples, odd_tuples, C::parameters(), rng)?;

        Ok(())
    }

    #[cfg(not(feature = "parallel"))]
    pub fn batched_verify<R: RngCore + CryptoRng>(
        &self,
        asset_tree: impl ValidateCurveTreeRoot<ASSET_TREE_L, ASSET_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let batch_size = self.legs.len();
        if batch_size < 2 {
            return self.verify(asset_tree, rng);
        }

        // Get the curve tree root.
        let root = asset_tree
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for settlement proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);
        for (idx, leg) in self.legs.iter().enumerate() {
            let ctx = (&self.memo, idx as u8).encode();
            let (even, odd) = leg.batched_verify(&ctx, &root, rng)?;
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        batch_verify_bp_with_rng(even_tuples, odd_tuples, C::parameters(), rng)?;

        Ok(())
    }
}

type BPSettlementTxnProof<C> = bp_leg::LegCreationProof<
    ASSET_TREE_L,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::P1,
    <C as CurveTreeConfig>::P0,
>;

/// The proof for a settlement leg in the Dart BP protocol.
///
/// This is to prove that the leg includes the correct encryption of the leg details and
/// that the correct auditor/mediator for the asset is included in the leg.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SettlementLegProof<C: CurveTreeConfig = AssetTreeConfig> {
    pub leg_enc: LegEncrypted,

    inner: WrappedCanonical<BPSettlementTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <VestaParameters as CurveConfig>::ScalarField,
            F1 = <PallasParameters as CurveConfig>::ScalarField,
            P0 = VestaParameters,
            P1 = PallasParameters,
        >,
> SettlementLegProof<C>
{
    pub(crate) fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg: bp_leg::Leg<PallasA>,
        leg_enc: LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        asset_data: AssetCommitmentData,
        ctx: &[u8],
        asset_tree: &impl CurveTreeLookup<ASSET_TREE_L, ASSET_TREE_M, C>,
    ) -> Result<Self, Error> {
        let asset_path = asset_tree.get_path_to_leaf_index(leg.asset_id as LeafIndex)?;
        let asset_comm_params = get_asset_commitment_parameters();
        let root = asset_tree.root()?.root_node()?;

        let proof = bp_leg::LegCreationProof::new(
            rng,
            leg,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            asset_path,
            asset_data,
            &root,
            ctx,
            asset_tree.params(),
            asset_comm_params,
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_enc,

            inner: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn mediator_count(&self) -> Result<usize, Error> {
        self.leg_enc.mediator_count()
    }

    pub fn get_mediator_ids(&self) -> Result<Vec<MediatorId>, Error> {
        self.leg_enc.get_mediator_ids()
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        ctx: &[u8],
        root: &Root<ASSET_TREE_L, ASSET_TREE_M, C::P0, C::P1>,
        rng: &mut R,
    ) -> Result<(), Error> {
        let asset_comm_params = get_asset_commitment_parameters();
        let leg_enc = self.leg_enc.decode()?;
        log::debug!("Verify leg: {:?}", leg_enc);
        let proof = self.inner.decode()?;
        proof.verify(
            rng,
            leg_enc.clone(),
            &root,
            ctx,
            C::parameters(),
            asset_comm_params,
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }

    /// Verify this leg proof inside a batch of proofs.
    pub(crate) fn batched_verify<R: RngCore + CryptoRng>(
        &self,
        ctx: &[u8],
        root: &Root<ASSET_TREE_L, ASSET_TREE_M, C::P0, C::P1>,
        rng: &mut R,
    ) -> Result<
        (
            VerificationTuple<Affine<C::P0>>,
            VerificationTuple<Affine<C::P1>>,
        ),
        Error,
    > {
        let asset_comm_params = get_asset_commitment_parameters();
        let leg_enc = self.leg_enc.decode()?;
        log::debug!("Verify leg: {:?}", leg_enc);
        let proof = self.inner.decode()?;
        let tuples = proof.verify_and_return_tuples(
            leg_enc.clone(),
            &root,
            ctx,
            C::parameters(),
            asset_comm_params,
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            rng,
            None,
        )?;
        Ok(tuples)
    }
}

pub type WrappedLegEncryptionRandomness =
    WrappedCanonical<bp_leg::LegEncryptionRandomness<PallasScalar>>;

#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, example = "0x0000000000000000000000000000000000000000000000000000000000000000", format = Binary))]
pub struct LegEncryptionRandomness(WrappedLegEncryptionRandomness);

impl LegEncryptionRandomness {
    pub fn new(rand: bp_leg::LegEncryptionRandomness<PallasScalar>) -> Result<Self, Error> {
        Ok(Self(WrappedCanonical::wrap(&rand)?))
    }

    pub fn decode(&self) -> Result<bp_leg::LegEncryptionRandomness<PallasScalar>, Error> {
        self.0.decode()
    }
}

pub type WrappedLegEncryption = WrappedCanonical<bp_leg::LegEncryption<PallasA>>;

/// Represents an encrypted leg in the Dart BP protocol.  Stored onchain.
#[derive(Clone, Debug, Encode, Decode, PartialEq, Eq, TypeInfo)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, example = "0x0000000000000000000000000000000000000000000000000000000000000000", format = Binary))]
pub struct LegEncrypted(WrappedLegEncryption);

impl LegEncrypted {
    pub fn new(leg_enc: bp_leg::LegEncryption<PallasA>) -> Result<Self, Error> {
        Ok(Self(WrappedCanonical::wrap(&leg_enc)?))
    }

    pub fn decode(&self) -> Result<bp_leg::LegEncryption<PallasA>, Error> {
        self.0.decode()
    }

    pub fn mediator_count(&self) -> Result<usize, Error> {
        self.get_mediator_ids().map(|ids| ids.len())
    }

    pub fn get_mediator_ids(&self) -> Result<Vec<MediatorId>, Error> {
        let leg_enc = self.decode()?;
        let mediators = leg_enc
            .eph_pk_auds_meds
            .iter()
            .enumerate()
            .filter(|(_idx, (is_auditor, _pk))| !is_auditor)
            .map(|(idx, _)| idx as MediatorId)
            .collect();
        Ok(mediators)
    }

    /// Attempt to decrypt the leg using the provided key pair and optional auditor/mediator key index.
    pub fn try_decrypt_with_key(
        &self,
        keys: &EncryptionKeyPair,
        key_index: Option<usize>,
        max_asset_id: Option<AssetId>,
    ) -> Result<(Leg, LegRole), Error> {
        let enc_gen = dart_gens().leg_asset_value_gen();
        let leg_enc = self.decode()?;
        let (key_index, (sender, receiver, asset_id, amount)) = if let Some(key_index) = key_index {
            // The key index is provided, use it directly.
            (
                key_index,
                leg_enc.decrypt_given_key_with_limits(
                    &keys.secret.0.0,
                    key_index,
                    enc_gen,
                    max_asset_id,
                    None,
                )?,
            )
        } else {
            // No key index provided, try all key indices until one works.
            let max_keys = leg_enc.eph_pk_auds_meds.len();
            let mut idx = 0;
            loop {
                if let Ok(res) = leg_enc.decrypt_given_key_with_limits(
                    &keys.secret.0.0,
                    idx,
                    enc_gen,
                    max_asset_id,
                    None,
                ) {
                    break (idx, res);
                }
                idx += 1;
                if idx >= max_keys {
                    return Err(Error::LegDecryptionError(
                        "Failed to decrypt leg with provided key".to_string(),
                    ));
                }
            }
        };

        let leg_role = if leg_enc.eph_pk_auds_meds[key_index].0 {
            LegRole::Auditor(key_index as u8)
        } else {
            LegRole::Mediator(key_index as u8)
        };
        Ok((
            Leg {
                sender: AccountPublicKey::from_affine(sender)?,
                receiver: AccountPublicKey::from_affine(receiver)?,
                asset_id,
                amount,
            },
            leg_role,
        ))
    }

    pub fn get_encryption_randomness(
        &self,
        role: LegRole,
        keys: &EncryptionKeyPair,
    ) -> Result<LegEncryptionRandomness, Error> {
        let (rand, _leg_enc, _) = self.bp_decrypt_randomness_and_leg(role, keys)?;
        LegEncryptionRandomness::new(rand)
    }

    fn bp_decrypt_randomness_and_leg(
        &self,
        role: LegRole,
        keys: &EncryptionKeyPair,
    ) -> Result<
        (
            bp_leg::LegEncryptionRandomness<PallasScalar>,
            bp_leg::LegEncryption<PallasA>,
            bool,
        ),
        Error,
    > {
        let is_sender = match role {
            LegRole::Sender => true,
            LegRole::Receiver => false,
            _ => {
                return Err(Error::LegDecryptionError(format!(
                    "Invalid role for encryption randomness: {:?}",
                    role
                )));
            }
        };
        let leg_enc = self.decode()?;
        let randomness =
            leg_enc.get_encryption_randomness::<Blake2b512>(&keys.secret.0.0, is_sender)?;
        Ok((randomness, leg_enc, is_sender))
    }

    /// Try to decrypt the leg as either sender or receiver.
    ///
    /// Auditors and mediators should use `try_decrypt_with_key` instead.
    pub fn try_decrypt(&self, keys: &AccountKeys) -> Option<(Leg, LegRole)> {
        // TODO: optimize to avoid decoding leg encryption twice.
        if let Ok(leg) = self.decrypt(LegRole::Sender, keys) {
            Some((leg, LegRole::Sender))
        } else if let Ok(leg) = self.decrypt(LegRole::Receiver, keys) {
            Some((leg, LegRole::Receiver))
        } else {
            None
        }
    }

    /// Decrypt the leg using the provided role and account keys.  Only use this if the role is known.
    ///
    /// Senders/receivers should use `try_decrypt` instead.
    /// Auditors/mediators should use `try_decrypt_with_key` instead.
    pub fn decrypt(&self, role: LegRole, keys: &AccountKeys) -> Result<Leg, Error> {
        let enc_key_gen = dart_gens().enc_key_gen();
        let enc_gen = dart_gens().leg_asset_value_gen();
        let (sender, receiver, asset_id, amount) = match role {
            LegRole::Sender => {
                let (rand, leg_enc, _) = self.bp_decrypt_randomness_and_leg(role, &keys.enc)?;
                leg_enc.decrypt_given_r_checked(
                    rand,
                    enc_key_gen,
                    enc_gen,
                    keys.acct.public.get_affine()?,
                    true,
                )?
            }
            LegRole::Receiver => {
                let (rand, leg_enc, _) = self.bp_decrypt_randomness_and_leg(role, &keys.enc)?;
                leg_enc.decrypt_given_r_checked(
                    rand,
                    enc_key_gen,
                    enc_gen,
                    keys.acct.public.get_affine()?,
                    false,
                )?
            }
            LegRole::Auditor(idx) | LegRole::Mediator(idx) => {
                let leg_enc = self.decode()?;
                leg_enc.decrypt_given_key(&keys.enc.secret.0.0, idx as usize, enc_gen)?
            }
        };
        Ok(Leg {
            sender: AccountPublicKey::from_affine(sender)?,
            receiver: AccountPublicKey::from_affine(receiver)?,
            asset_id,
            amount,
        })
    }

    pub fn decrypt_with_randomness(
        &self,
        role: LegRole,
        keys: &AccountKeys,
    ) -> Result<(Leg, LegEncryptionRandomness), Error> {
        let enc_key_gen = dart_gens().enc_key_gen();
        let enc_gen = dart_gens().leg_asset_value_gen();
        let (rand, leg_enc, _) = self.bp_decrypt_randomness_and_leg(role, &keys.enc)?;
        let (sender, receiver, asset_id, amount) = leg_enc.decrypt_given_r_checked(
            rand.clone(),
            enc_key_gen,
            enc_gen,
            keys.acct.public.get_affine()?,
            role.is_sender(),
        )?;
        Ok((
            Leg {
                sender: AccountPublicKey::from_affine(sender)?,
                receiver: AccountPublicKey::from_affine(receiver)?,
                asset_id,
                amount,
            },
            LegEncryptionRandomness::new(rand)?,
        ))
    }

    pub fn decrypt_with_randomness_checked(
        &self,
        role: LegRole,
        keys: &EncryptionKeyPair,
        account_pk: &AccountPublicKey,
    ) -> Result<(Leg, LegEncryptionRandomness), Error> {
        let enc_key_gen = dart_gens().enc_key_gen();
        let enc_gen = dart_gens().leg_asset_value_gen();
        let (rand, leg_enc, is_sender) = self.bp_decrypt_randomness_and_leg(role, keys)?;
        let pk = account_pk.get_affine()?;
        let (sender, receiver, asset_id, amount) =
            leg_enc.decrypt_given_r_checked(rand.clone(), enc_key_gen, enc_gen, pk, is_sender)?;
        Ok((
            Leg {
                sender: AccountPublicKey::from_affine(sender)?,
                receiver: AccountPublicKey::from_affine(receiver)?,
                asset_id,
                amount,
            },
            LegEncryptionRandomness::new(rand)?,
        ))
    }
}
