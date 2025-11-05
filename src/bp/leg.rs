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

use polymesh_dart_bp::util::batch_verify_bp_with_rng;
use polymesh_dart_bp::{account as bp_account, leg as bp_leg};
use polymesh_dart_common::{LegId, MediatorId};

use super::WrappedCanonical;
use crate::curve_tree::*;
use crate::*;

/// The settlement reference is the hash of the settlement creation proof.
#[derive(
    Copy, Clone, Debug, Default, MaxEncodedLen, Encode, Decode, TypeInfo, PartialEq, Eq, Hash,
)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary))]
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
    pub sender: AccountPublicKey,
    pub receiver: AccountPublicKey,
    pub asset_id: AssetId,
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
        self,
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

#[derive(Clone, Debug, Encode, Decode)]
pub struct SettlementBuilder<T: DartLimits = ()> {
    pub memo: Vec<u8>,
    pub legs: Vec<LegBuilder>,
    _marker: core::marker::PhantomData<T>,
}

impl<T: DartLimits> SettlementBuilder<T> {
    pub fn new(memo: &[u8]) -> Self {
        Self {
            memo: memo.to_vec(),
            legs: Vec::new(),
            _marker: core::marker::PhantomData,
        }
    }

    pub fn leg(mut self, leg: LegBuilder) -> Self {
        self.legs.push(leg);
        self
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
        self,
        rng: &mut R,
        asset_tree: impl CurveTreeLookup<ASSET_TREE_L, ASSET_TREE_M, C>,
    ) -> Result<SettlementProof<T, C>, Error> {
        let memo = BoundedVec::try_from(self.memo)
            .map_err(|_| Error::BoundedContainerSizeLimitExceeded)?;
        // TODO: need to collect all asset leaf paths based on the `root_block` number.
        // To avoid getting paths based on different roots if a new block is produced during proof generation.
        let root_block = asset_tree.get_block_number()?;

        let mut legs = Vec::with_capacity(self.legs.len());

        for (idx, leg_builder) in self.legs.into_iter().enumerate() {
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

type BPSettlementTxnProof<C> = bp_leg::SettlementTxnProof<
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

    proof: WrappedCanonical<BPSettlementTxnProof<C>>,
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

        let proof = bp_leg::SettlementTxnProof::new(
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

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn mediator_count(&self) -> Result<usize, Error> {
        self.get_mediator_ids().map(|ids| ids.len())
    }

    pub fn get_mediator_ids(&self) -> Result<Vec<MediatorId>, Error> {
        let leg_enc = self.leg_enc.decode()?;
        let mediators = leg_enc
            .eph_pk_auds_meds
            .iter()
            .enumerate()
            .filter(|(_idx, (is_auditor, _pk))| !is_auditor)
            .map(|(idx, _)| idx as MediatorId)
            .collect();
        Ok(mediators)
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
        let proof = self.proof.decode()?;
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
        let proof = self.proof.decode()?;
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

/// Counts of the legs and sender/receiver affirmations in a batched settlement.
#[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq)]
pub struct BatchedSettlementCounts {
    pub leg_count: u32,
    pub sender_count: u64,
    pub receiver_count: u64,
}

/// Represents the affirmation proofs for each leg in a settlement.
/// This includes the sender, and receiver affirmation proofs.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct BatchedSettlementLegAffirmations<C: CurveTreeConfig = AccountTreeConfig> {
    /// The sender's affirmation proof.
    pub sender: Option<SenderAffirmationProof<C>>,
    /// The receiver's affirmation proof.
    pub receiver: Option<ReceiverAffirmationProof<C>>,
}

/// A batched settlement proof allows including the sender and receiver affirmation proofs
/// with the settlement creation proof to reduce the number of transactions
/// required to finalize a settlement.
#[derive(Clone, Debug, Encode, Decode, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(T))]
pub struct BatchedSettlementProof<
    T: DartLimits = (),
    C: CurveTreeConfig = AssetTreeConfig,
    A: CurveTreeConfig = AccountTreeConfig,
> {
    /// The settlement proof containing the memo, root, and legs.
    pub settlement: SettlementProof<T, C>,

    /// The leg affirmations for each leg in the settlement.
    pub leg_affirmations: BoundedVec<BatchedSettlementLegAffirmations<A>, T::MaxSettlementLegs>,
}

impl<
    T: DartLimits,
    C: CurveTreeConfig<
            F0 = <VestaParameters as CurveConfig>::ScalarField,
            F1 = <PallasParameters as CurveConfig>::ScalarField,
            P0 = VestaParameters,
            P1 = PallasParameters,
        >,
    A: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> BatchedSettlementProof<T, C, A>
{
    /// Get leg and sender/receiver affirmation counts.
    pub fn count_leg_affirmations(&self) -> BatchedSettlementCounts {
        let mut leg_count = 0;
        let mut sender_count = 0;
        let mut receiver_count = 0;

        for leg_aff in &self.leg_affirmations {
            leg_count += 1;
            if leg_aff.sender.is_some() {
                sender_count += 1;
            }
            if leg_aff.receiver.is_some() {
                receiver_count += 1;
            }
        }

        BatchedSettlementCounts {
            leg_count,
            sender_count,
            receiver_count,
        }
    }

    /// Check leg references in affirmation proofs.
    ///
    /// Returns `true` if all leg references match the settlement legs.
    pub fn check_leg_references(&self) -> bool {
        let settlement = self.settlement.settlement_ref();
        for (idx, leg_aff) in self.leg_affirmations.iter().enumerate() {
            let leg_ref = LegRef::new(settlement, idx as LegId);
            if let Some(sender) = &leg_aff.sender {
                if sender.leg_ref != leg_ref {
                    return false;
                }
            }
            if let Some(receiver) = &leg_aff.receiver {
                if receiver.leg_ref != leg_ref {
                    return false;
                }
            }
        }
        true
    }
}

pub type WrappedLegEncryptionRandomness =
    WrappedCanonical<bp_leg::LegEncryptionRandomness<PallasScalar>>;

#[derive(Clone, Encode, Decode)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
#[cfg_attr(feature = "utoipa", derive(utoipa::ToSchema))]
#[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary))]
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
#[cfg_attr(feature = "utoipa", schema(value_type = String, format = Binary))]
pub struct LegEncrypted(WrappedLegEncryption);

impl LegEncrypted {
    pub fn new(leg_enc: bp_leg::LegEncryption<PallasA>) -> Result<Self, Error> {
        Ok(Self(WrappedCanonical::wrap(&leg_enc)?))
    }

    pub fn decode(&self) -> Result<bp_leg::LegEncryption<PallasA>, Error> {
        self.0.decode()
    }

    /// Attempt to decrypt the leg using the provided key pair and optional auditor/mediator key index.
    pub fn try_decrypt_with_key(
        &self,
        keys: &EncryptionKeyPair,
        key_index: Option<usize>,
        max_asset_id: Option<AssetId>,
    ) -> Result<(Leg, usize), Error> {
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
        Ok((
            Leg {
                sender: AccountPublicKey::from_affine(sender)?,
                receiver: AccountPublicKey::from_affine(receiver)?,
                asset_id,
                amount,
            },
            key_index,
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

type BPAffirmAsSenderTxnProof<C> = bp_account::AffirmAsSenderTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// The sender affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderAffirmationProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPAffirmAsSenderTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderAffirmationProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        amount: Balance,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the sender affirmation.
        let state_change = account_asset.get_sender_affirm_state(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::AffirmAsSenderTxnProof::new(
            rng,
            amount,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for sender affirmation proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for SenderAffirmationProof<C> {
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

type BPAffirmAsReceiverTxnProof<C> = bp_account::AffirmAsReceiverTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// The receiver affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct ReceiverAffirmationProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPAffirmAsReceiverTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> ReceiverAffirmationProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for the receiver affirmation.
        let state_change = account_asset.get_receiver_affirm_state(account)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::AffirmAsReceiverTxnProof::new(
            rng,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for receiver affirmation proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for ReceiverAffirmationProof<C> {
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

type BPClaimReceivedTxnProof<C> = bp_account::ClaimReceivedTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// The proof for claiming received assets in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct ReceiverClaimProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPClaimReceivedTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> ReceiverClaimProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        amount: Balance,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for claiming received assets.
        let state_change = account_asset.get_state_for_claiming_received(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::ClaimReceivedTxnProof::new(
            rng,
            amount,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for receiver claim proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for ReceiverClaimProof<C> {
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

type BPSenderCounterUpdateTxnProof<C> = bp_account::SenderCounterUpdateTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// Sender counter update proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderCounterUpdateProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPSenderCounterUpdateTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderCounterUpdateProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for decreasing the counter.
        let state_change = account_asset.get_state_for_decreasing_counter(account)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::SenderCounterUpdateTxnProof::new(
            rng,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for sender counter update proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for SenderCounterUpdateProof<C> {
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

type BPSenderReverseTxnProof<C> = bp_account::SenderReverseTxnProof<
    ACCOUNT_TREE_L,
    <C as CurveTreeConfig>::F0,
    <C as CurveTreeConfig>::F1,
    <C as CurveTreeConfig>::P0,
    <C as CurveTreeConfig>::P1,
>;

/// Sender reversal proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
#[scale_info(skip_type_params(C))]
pub struct SenderReversalProof<C: CurveTreeConfig = AccountTreeConfig> {
    pub leg_ref: LegRef,
    pub root_block: BlockNumber,
    pub updated_account_state_commitment: AccountStateCommitment,
    pub nullifier: AccountStateNullifier,

    proof: WrappedCanonical<BPSenderReverseTxnProof<C>>,
}

impl<
    C: CurveTreeConfig<
            F0 = <PallasParameters as CurveConfig>::ScalarField,
            F1 = <VestaParameters as CurveConfig>::ScalarField,
            P0 = PallasParameters,
            P1 = VestaParameters,
        >,
> SenderReversalProof<C>
{
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        account: &AccountKeyPair,
        leg_ref: &LegRef,
        amount: Balance,
        leg_enc: &LegEncrypted,
        leg_enc_rand: &LegEncryptionRandomness,
        account_asset: &mut AccountAssetState,
        tree_lookup: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
    ) -> Result<Self, Error> {
        // Generate a new account state for reversing the send.
        let state_change = account_asset.get_state_for_reversing_send(account, amount)?;
        let updated_account_state_commitment = state_change.commitment()?;
        let current_account_path = state_change.get_path(&tree_lookup)?;

        let root_block = tree_lookup.get_block_number()?;
        let root = tree_lookup.root()?;
        let root = root.root_node()?;

        let ctx = leg_ref.context();
        let (proof, nullifier) = bp_account::SenderReverseTxnProof::new(
            rng,
            amount,
            leg_enc.decode()?,
            leg_enc_rand.decode()?,
            &state_change.current_state,
            &state_change.new_state,
            state_change.new_commitment,
            current_account_path,
            &root,
            ctx.as_bytes(),
            tree_lookup.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            root_block: try_block_number(root_block)?,
            updated_account_state_commitment,
            nullifier: AccountStateNullifier::from_affine(nullifier)?,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify<R: RngCore + CryptoRng>(
        &self,
        leg_enc: &LegEncrypted,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, C>,
        rng: &mut R,
    ) -> Result<(), Error> {
        // Get the curve tree root.
        let root = tree_roots
            .get_block_root(self.root_block.into())
            .ok_or_else(|| {
                log::error!("Invalid root for sender reversal proof");
                Error::CurveTreeRootNotFound
            })?;
        let root = root.root_node()?;

        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            rng,
            leg_enc.decode()?,
            &root,
            self.updated_account_state_commitment.as_commitment()?,
            self.nullifier.get_affine()?,
            ctx.as_bytes(),
            tree_roots.params(),
            dart_gens().account_comm_key(),
            dart_gens().enc_key_gen(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}

impl<C: CurveTreeConfig> AccountStateUpdate for SenderReversalProof<C> {
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

/// Mediator affirmation proof in the Dart BP protocol.
#[derive(Clone, Encode, Decode, Debug, TypeInfo, PartialEq, Eq)]
pub struct MediatorAffirmationProof {
    pub leg_ref: LegRef,
    pub accept: bool,
    pub key_index: MediatorId,

    proof: WrappedCanonical<bp_leg::MediatorTxnProof<PallasA>>,
}

impl MediatorAffirmationProof {
    pub fn new<R: RngCore + CryptoRng>(
        rng: &mut R,
        leg_ref: &LegRef,
        asset_id: AssetId,
        leg_enc: &LegEncrypted,
        mediator_sk: &EncryptionKeyPair,
        key_index: MediatorId,
        accept: bool,
    ) -> Result<Self, Error> {
        let ctx = leg_ref.context();
        let proof = bp_leg::MediatorTxnProof::new(
            rng,
            leg_enc.decode()?,
            asset_id,
            mediator_sk.secret.0.0,
            accept,
            key_index as usize,
            ctx.as_bytes(),
            dart_gens().leg_asset_value_gen(),
        )?;

        Ok(Self {
            leg_ref: leg_ref.clone(),
            accept,
            key_index,

            proof: WrappedCanonical::wrap(&proof)?,
        })
    }

    pub fn verify(&self, leg_enc: &LegEncrypted) -> Result<(), Error> {
        let ctx = self.leg_ref.context();
        let proof = self.proof.decode()?;
        proof.verify(
            leg_enc.decode()?,
            self.accept,
            self.key_index as usize,
            ctx.as_bytes(),
            dart_gens().leg_asset_value_gen(),
            None,
        )?;
        Ok(())
    }
}
