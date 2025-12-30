#![allow(dead_code)]

use anyhow::{Context, Result, anyhow};
use ark_std::rand;
use codec::{Decode, Encode};
use polymesh_dart_bp::util::reseed_rng;
use polymesh_dart_common::{MediatorId, SETTLEMENT_MAX_LEGS};
use rand_chacha::ChaCha20Rng;
use rand_core::{CryptoRng, RngCore};

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    sync::{Arc, RwLock},
};

use polymesh_dart::{
    curve_tree::{
        AccountTreeConfig, AssetCurveTree, AssetTreeConfig, CurveTreeLookup, CurveTreeWithBackend,
        ProverCurveTree, ValidateCurveTreeRoot,
    },
    *,
};

pub fn scale_encode_and_decode_test<T: Encode + Decode>(value: &T) -> Result<T> {
    let buf = value.encode();
    let decoded_value = T::decode(&mut buf.as_slice()).context("Failed to decode value")?;
    Ok(decoded_value)
}

pub fn new_rng() -> ChaCha20Rng {
    let mut rng = rand::thread_rng();
    reseed_rng(&mut rng)
}

/// A fake "Substrate" signer address for testing purposes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SignerAddress(pub String);

impl SignerAddress {
    pub fn ctx(&self) -> &[u8] {
        self.0.as_bytes()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignerState {
    pub nonce: u64,
}

#[derive(Debug, Clone)]
struct DartUserAccountInner {
    address: SignerAddress,
    keys: AccountKeys,
    assets: HashMap<AssetId, AccountAssetState>,
}

impl DartUserAccountInner {
    pub fn new<R: RngCore + CryptoRng>(rng: &mut R, address: SignerAddress) -> Result<Self> {
        let account_keys = AccountKeys::rand(rng)?;
        Ok(Self {
            address,
            keys: account_keys,
            assets: HashMap::new(),
        })
    }

    pub fn address(&self) -> &SignerAddress {
        &self.address
    }

    pub fn public_keys(&self) -> AccountPublicKeys {
        self.keys.public_keys()
    }

    pub fn get_account_asset_state(&self, asset_id: AssetId) -> Result<AccountAssetState> {
        let asset_state = self
            .assets
            .get(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;
        Ok(asset_state.clone())
    }

    pub fn set_account_asset_state(
        &mut self,
        asset_id: AssetId,
        new_state: AccountAssetState,
    ) -> Result<()> {
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;
        *asset_state = new_state;
        Ok(())
    }

    pub fn initialize_asset<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        asset_id: AssetId,
    ) -> Result<()> {
        if self.assets.contains_key(&asset_id) {
            return Err(anyhow!(
                "Asset ID {} is already initialized for this account",
                asset_id
            ));
        }
        let (proof, mut asset_state) = AccountAssetRegistrationProof::new(
            rng,
            &self.keys.acct,
            asset_id,
            0,
            self.address.ctx(),
            chain.account_tree.parameters(),
        )?;
        chain.initialize_account_asset(&self.address, proof)?;
        asset_state.commit_pending_state()?;
        self.assets.insert(asset_id, asset_state);
        Ok(())
    }

    pub fn commit_pending_asset_state(&mut self, asset_id: AssetId) -> Result<()> {
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;
        asset_state.commit_pending_state()?;
        Ok(())
    }

    pub fn mint_asset<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;
        let proof =
            AssetMintingProof::new(rng, &self.keys.acct, asset_state, account_tree, amount)?;
        chain.mint_assets(&self.address, proof)?;
        asset_state.commit_pending_state()?;
        Ok(())
    }

    pub fn sender_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        log::info!("Sender decrypts the leg");
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let (leg, leg_enc_rand) = leg_enc.decrypt_with_randomness(LegRole::sender(), &self.keys)?;

        if asset_id != leg.asset_id() {
            return Err(anyhow!(
                "Asset ID {} does not match leg asset ID {}",
                asset_id,
                leg.asset_id()
            ));
        }
        if amount != leg.amount() {
            return Err(anyhow!(
                "Amount {} does not match leg amount {}",
                amount,
                leg.amount()
            ));
        }

        // Get the asset state for the account.
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;

        // Create the sender affirmation proof.
        log::info!("Sender generate affirmation proof");
        let proof = SenderAffirmationProof::new(
            rng,
            &self.keys.acct,
            leg_ref,
            amount,
            &leg_enc,
            &leg_enc_rand,
            asset_state,
            account_tree,
        )?;
        log::info!("Sender affirms");
        chain.sender_affirmation(&self.address, proof)?;
        asset_state.commit_pending_state()?;
        Ok(())
    }

    pub fn receiver_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        log::info!("Receiver decrypts the leg");
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let (leg, leg_enc_rand) =
            leg_enc.decrypt_with_randomness(LegRole::receiver(), &self.keys)?;

        if asset_id != leg.asset_id() {
            return Err(anyhow!(
                "Asset ID {} does not match leg asset ID {}",
                asset_id,
                leg.asset_id()
            ));
        }
        if amount != leg.amount() {
            return Err(anyhow!(
                "Amount {} does not match leg amount {}",
                amount,
                leg.amount()
            ));
        }

        // Get the asset state for the account.
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;

        // Create the receiver affirmation proof.
        log::info!("Receiver generate affirmation proof");
        let proof = ReceiverAffirmationProof::new(
            rng,
            &self.keys.acct,
            leg_ref,
            &leg_enc,
            &leg_enc_rand,
            asset_state,
            account_tree,
        )?;
        log::info!("Receiver affirms");
        chain.receiver_affirmation(&self.address, proof)?;
        asset_state.commit_pending_state()?;
        Ok(())
    }

    pub fn instant_sender_affirmation_proof<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        leg_enc: &LegEncrypted,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<InstantSenderAffirmationProof> {
        log::info!("Sender decrypts the leg");
        let (leg, leg_enc_rand) = leg_enc.decrypt_with_randomness(LegRole::sender(), &self.keys)?;

        if asset_id != leg.asset_id() {
            return Err(anyhow!(
                "Asset ID {} does not match leg asset ID {}",
                asset_id,
                leg.asset_id()
            ));
        }
        if amount != leg.amount() {
            return Err(anyhow!(
                "Amount {} does not match leg amount {}",
                amount,
                leg.amount()
            ));
        }

        // Get the asset state for the account.
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;

        // Create the sender affirmation proof.
        log::info!("Sender generate instant affirmation proof");
        let proof = InstantSenderAffirmationProof::new(
            rng,
            &self.keys.acct,
            leg_ref,
            amount,
            &leg_enc,
            &leg_enc_rand,
            asset_state,
            &account_tree,
        )?;

        // Try to verify the proof before returning it.
        let root = account_tree.root()?;
        let res = proof.verify(leg_enc, &root, rng);
        log::info!("Verified instant sender affirmation proof: {:?}", res);
        res?;

        Ok(proof)
    }

    pub fn instant_receiver_affirmation_proof<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        leg_enc: &LegEncrypted,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<InstantReceiverAffirmationProof> {
        log::info!("Receiver decrypts the leg");
        let (leg, leg_enc_rand) =
            leg_enc.decrypt_with_randomness(LegRole::receiver(), &self.keys)?;

        if asset_id != leg.asset_id() {
            return Err(anyhow!(
                "Asset ID {} does not match leg asset ID {}",
                asset_id,
                leg.asset_id()
            ));
        }
        if amount != leg.amount() {
            return Err(anyhow!(
                "Amount {} does not match leg amount {}",
                amount,
                leg.amount()
            ));
        }

        // Get the asset state for the account.
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;

        // Create the receiver affirmation proof.
        log::info!("Receiver generate instant affirmation proof");
        let proof = InstantReceiverAffirmationProof::new(
            rng,
            &self.keys.acct,
            leg_ref,
            amount,
            &leg_enc,
            &leg_enc_rand,
            asset_state,
            account_tree,
        )?;
        Ok(proof)
    }

    pub fn instant_sender_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let proof = self.instant_sender_affirmation_proof(
            rng,
            &leg_enc,
            account_tree,
            leg_ref,
            asset_id,
            amount,
        )?;
        log::info!("Sender instant affirms");
        chain.instant_sender_affirmation(&self.address, proof)?;
        self.commit_pending_asset_state(asset_id)?;
        Ok(())
    }

    pub fn instant_receiver_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let proof = self.instant_receiver_affirmation_proof(
            rng,
            &leg_enc,
            account_tree,
            leg_ref,
            asset_id,
            amount,
        )?;
        log::info!("Receiver instant affirms");
        chain.instant_receiver_affirmation(&self.address, proof)?;
        self.commit_pending_asset_state(asset_id)?;
        Ok(())
    }

    pub fn mediator_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        leg_ref: &LegRef,
        accept: bool,
    ) -> Result<()> {
        log::info!("Mediator decrypts the leg");
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let leg = leg_enc.decrypt(LegRole::mediator(0), &self.keys)?;
        log::info!("Mediator's view of the leg: {:?}", leg);

        // Create the mediator affirmation proof.
        log::info!("Mediator generate affirmation proof");
        let proof = MediatorAffirmationProof::new(
            rng,
            leg_ref,
            leg.asset_id,
            &leg_enc,
            &self.keys.enc,
            0,
            accept,
        )?;
        log::info!("Mediator affirms");
        chain.mediator_affirmation(&self.address, proof)?;
        Ok(())
    }

    pub fn decrypt_leg(
        &self,
        chain: &DartChainState,
        leg_ref: &LegRef,
        role: LegRole,
    ) -> Result<Leg> {
        log::info!("Decrypting leg for role: {:?}", role);
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let leg = leg_enc.decrypt(role, &self.keys)?;
        log::info!("Decrypted leg: {:?}", leg);
        Ok(leg)
    }

    pub fn decrypt_leg_randomness(
        &self,
        chain: &DartChainState,
        leg_ref: &LegRef,
        role: LegRole,
    ) -> Result<LegEncryptionRandomness> {
        log::info!("Decrypting leg randomness for role: {:?}", role);
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let leg_enc_rand = leg_enc.get_encryption_randomness(role, &self.keys.enc)?;
        Ok(leg_enc_rand)
    }

    pub fn receiver_claims<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
    ) -> Result<()> {
        log::info!("Receiver decrypts the leg for claim");
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let (leg, leg_enc_rand) =
            leg_enc.decrypt_with_randomness(LegRole::receiver(), &self.keys)?;
        let asset_id = leg.asset_id();
        let amount = leg.amount();

        // Get the asset state for the account.
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;

        // Create the receiver claim proof.
        log::info!("Receiver generate claim proof");
        let proof = ReceiverClaimProof::new(
            rng,
            &self.keys.acct,
            leg_ref,
            amount,
            &leg_enc,
            &leg_enc_rand,
            asset_state,
            account_tree,
        )?;
        log::info!("Receiver claims");
        chain.receiver_claim(&self.address, proof)?;
        asset_state.commit_pending_state()?;
        Ok(())
    }

    pub fn sender_counter_update<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
    ) -> Result<()> {
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let (leg, leg_enc_rand) = leg_enc.decrypt_with_randomness(LegRole::sender(), &self.keys)?;
        let asset_id = leg.asset_id();

        // Get the asset state for the account.
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;

        // Create the sender counter update proof.
        log::info!("Sender generate counter update proof");
        let proof = SenderCounterUpdateProof::new(
            rng,
            &self.keys.acct,
            leg_ref,
            &leg_enc,
            &leg_enc_rand,
            asset_state,
            account_tree,
        )?;
        log::info!("Sender updates counter");
        chain.sender_counter_update(&self.address, proof)?;
        asset_state.commit_pending_state()?;
        Ok(())
    }

    pub fn sender_revert<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
    ) -> Result<()> {
        log::info!("Sender decrypts the leg for reversal");
        let leg_enc = chain.get_settlement_leg(leg_ref)?.enc.clone();
        let (leg, leg_enc_rand) = leg_enc.decrypt_with_randomness(LegRole::sender(), &self.keys)?;
        let asset_id = leg.asset_id();
        let amount = leg.amount();

        // Get the asset state for the account.
        let asset_state = self
            .assets
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} is not initialized for this account", asset_id))?;

        // Create the sender reversal proof.
        log::info!("Sender generate reversal proof");
        let proof = SenderReversalProof::new(
            rng,
            &self.keys.acct,
            leg_ref,
            amount,
            &leg_enc,
            &leg_enc_rand,
            asset_state,
            account_tree,
        )?;
        log::info!("Sender reverses");
        chain.sender_revert(&self.address, proof)?;
        asset_state.commit_pending_state()?;
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct DartUserAccount(Arc<RwLock<DartUserAccountInner>>);

impl DartUserAccount {
    pub fn new<R: RngCore + CryptoRng>(rng: &mut R, address: SignerAddress) -> Result<Self> {
        let inner = DartUserAccountInner::new(rng, address)?;
        Ok(Self(Arc::new(RwLock::new(inner))))
    }

    pub fn address(&self) -> SignerAddress {
        self.0.read().unwrap().address().clone()
    }

    pub fn public_keys(&self) -> AccountPublicKeys {
        self.0.read().unwrap().public_keys()
    }

    pub fn keys(&self) -> AccountKeys {
        self.0.read().unwrap().keys.clone()
    }

    pub fn get_account_asset_state(&self, asset_id: AssetId) -> Result<AccountAssetState> {
        self.0.read().unwrap().get_account_asset_state(asset_id)
    }

    pub fn set_account_asset_state(
        &self,
        asset_id: AssetId,
        new_state: AccountAssetState,
    ) -> Result<()> {
        self.0
            .write()
            .unwrap()
            .set_account_asset_state(asset_id, new_state)
    }

    pub fn initialize_asset<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        asset_id: AssetId,
    ) -> Result<()> {
        self.0
            .write()
            .unwrap()
            .initialize_asset(rng, chain, asset_id)
    }

    pub fn mint_asset<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        self.0
            .write()
            .unwrap()
            .mint_asset(rng, chain, account_tree, asset_id, amount)
    }

    pub fn sender_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        self.0.write().unwrap().sender_affirmation(
            rng,
            chain,
            account_tree,
            leg_ref,
            asset_id,
            amount,
        )
    }

    pub fn receiver_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        self.0.write().unwrap().receiver_affirmation(
            rng,
            chain,
            account_tree,
            leg_ref,
            asset_id,
            amount,
        )
    }

    pub fn instant_sender_affirmation_proof<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        leg_enc: &LegEncrypted,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<InstantSenderAffirmationProof> {
        self.0.write().unwrap().instant_sender_affirmation_proof(
            rng,
            leg_enc,
            account_tree,
            leg_ref,
            asset_id,
            amount,
        )
    }

    pub fn instant_receiver_affirmation_proof<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        leg_enc: &LegEncrypted,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<InstantReceiverAffirmationProof> {
        self.0.write().unwrap().instant_receiver_affirmation_proof(
            rng,
            leg_enc,
            account_tree,
            leg_ref,
            asset_id,
            amount,
        )
    }

    pub fn instant_sender_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        self.0.write().unwrap().instant_sender_affirmation(
            rng,
            chain,
            account_tree,
            leg_ref,
            asset_id,
            amount,
        )
    }

    pub fn instant_receiver_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
        asset_id: AssetId,
        amount: Balance,
    ) -> Result<()> {
        self.0.write().unwrap().instant_receiver_affirmation(
            rng,
            chain,
            account_tree,
            leg_ref,
            asset_id,
            amount,
        )
    }

    pub fn mediator_affirmation<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        leg_ref: &LegRef,
        accept: bool,
    ) -> Result<()> {
        self.0
            .write()
            .unwrap()
            .mediator_affirmation(rng, chain, leg_ref, accept)
    }

    pub fn decrypt_leg(
        &self,
        chain: &DartChainState,
        leg_ref: &LegRef,
        role: LegRole,
    ) -> Result<Leg> {
        self.0.read().unwrap().decrypt_leg(chain, leg_ref, role)
    }

    pub fn decrypt_leg_randomness(
        &self,
        chain: &DartChainState,
        leg_ref: &LegRef,
        role: LegRole,
    ) -> Result<LegEncryptionRandomness> {
        self.0
            .read()
            .unwrap()
            .decrypt_leg_randomness(chain, leg_ref, role)
    }

    pub fn receiver_claims<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
    ) -> Result<()> {
        self.0
            .write()
            .unwrap()
            .receiver_claims(rng, chain, account_tree, leg_ref)
    }

    pub fn sender_counter_update<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
    ) -> Result<()> {
        self.0
            .write()
            .unwrap()
            .sender_counter_update(rng, chain, account_tree, leg_ref)
    }

    pub fn sender_revert<R: RngCore + CryptoRng>(
        &self,
        rng: &mut R,
        chain: &mut DartChainState,
        account_tree: impl CurveTreeLookup<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        leg_ref: &LegRef,
    ) -> Result<()> {
        self.0
            .write()
            .unwrap()
            .sender_revert(rng, chain, account_tree, leg_ref)
    }
}

pub struct DartUser {
    pub address: SignerAddress,
    pub accounts: HashMap<String, DartUserAccount>,
}

impl DartUser {
    pub fn new(address: &SignerAddress) -> Self {
        Self {
            address: address.clone(),
            accounts: HashMap::new(),
        }
    }

    pub fn create_asset(
        &self,
        chain: &mut DartChainState,
        mediators: &[EncryptionPublicKey],
        auditors: &[EncryptionPublicKey],
    ) -> Result<AssetId> {
        chain
            .create_dart_asset(&self.address, auditors, mediators)
            .map(|details| details.asset_id)
    }

    /// Create a new account for the user and register it on chain.
    pub fn create_and_register_account<R: RngCore + CryptoRng>(
        &mut self,
        rng: &mut R,
        chain: &mut DartChainState,
        name: &str,
    ) -> Result<DartUserAccount> {
        // Generate the new account.
        let account = DartUserAccount::new(rng, self.address.clone())?;

        // Register the account on chain using our address.
        chain.register_account(&self.address, account.public_keys())?;

        self.accounts.insert(name.to_string(), account.clone());
        Ok(account)
    }

    pub fn create_settlement(
        &self,
        chain: &mut DartChainState,
        proof: SettlementProof<()>,
    ) -> Result<SettlementRef> {
        chain.create_settlement(&self.address, proof)
    }

    pub fn execute_instant_settlement(
        &self,
        chain: &mut DartChainState,
        proof: InstantSettlementProof<()>,
    ) -> Result<SettlementRef> {
        chain.execute_instant_settlement(&self.address, proof)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DartAssetDetails {
    pub asset_id: AssetId,
    pub owner: SignerAddress,
    pub total_supply: Balance,
    pub auditors: Vec<EncryptionPublicKey>,
    pub mediators: Vec<EncryptionPublicKey>,
}

impl DartAssetDetails {
    pub fn new(
        asset_id: AssetId,
        owner: SignerAddress,
        mediators: &[EncryptionPublicKey],
        auditors: &[EncryptionPublicKey],
    ) -> Self {
        Self {
            asset_id,
            owner,
            total_supply: 0,
            mediators: mediators.into(),
            auditors: auditors.into(),
        }
    }

    pub fn asset_state(&self) -> AssetState {
        AssetState::new(self.asset_id, &self.mediators, &self.auditors)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AffirmationStatus {
    Pending,
    Affirmed,
    Rejected,
    Finalized,
}

impl AffirmationStatus {
    pub fn apply(self, other: AffirmationStatus) -> Result<AffirmationStatus> {
        use AffirmationStatus::*;
        match (self, other) {
            (Pending, Pending) => Ok(Pending),
            (Pending, Affirmed) => Ok(Pending),
            (Pending, Rejected) => Ok(Rejected),
            (Pending, Finalized) => Err(anyhow!(
                "Cannot have a pending and finalized affirmation status at the same time in a settlement leg"
            )),

            (Affirmed, Pending) => Ok(Pending),
            (Affirmed, Affirmed) => Ok(Affirmed),
            (Affirmed, Rejected) => Ok(Rejected),
            (Affirmed, Finalized) => Ok(Affirmed),

            (Rejected, Pending) => Ok(Rejected),
            (Rejected, Affirmed) => Ok(Rejected),
            (Rejected, Rejected) => Ok(Rejected),
            (Rejected, Finalized) => Err(anyhow!(
                "Cannot have a rejected and finalized affirmation status at the same time in a settlement leg"
            )),

            (Finalized, Pending) => Err(anyhow!(
                "Cannot have a pending and finalized affirmation status at the same time in a settlement leg"
            )),
            (Finalized, Affirmed) => Ok(Affirmed),
            (Finalized, Rejected) => Err(anyhow!(
                "Cannot have a rejected and finalized affirmation status at the same time in a settlement leg"
            )),
            (Finalized, Finalized) => Ok(Finalized),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DartSettlementLeg {
    pub enc: LegEncrypted,
    pub sender: AffirmationStatus,
    pub receiver: AffirmationStatus,
    pub mediators: BTreeMap<MediatorId, AffirmationStatus>,
    pub status: AffirmationStatus,
}

impl DartSettlementLeg {
    /// Try to update the status of the leg based on the current sender, receiver, and mediator statuses.
    fn update_status(&mut self) -> Result<()> {
        let mut affirmation = self.sender.apply(self.receiver)?;
        for (_, mediator) in &self.mediators {
            affirmation = affirmation.apply(*mediator)?;
        }
        self.status = affirmation;
        Ok(())
    }

    pub fn pending_counts(&self) -> (u64, u64) {
        let mut pending_affirms = 0;
        let mut pending_finals = 0;
        match self.sender {
            AffirmationStatus::Pending => {
                pending_affirms += 1;
            }
            AffirmationStatus::Affirmed => {
                pending_finals += 1;
            }
            AffirmationStatus::Rejected | AffirmationStatus::Finalized => {}
        }
        match self.receiver {
            AffirmationStatus::Pending => {
                pending_affirms += 1;
            }
            AffirmationStatus::Affirmed => {
                pending_finals += 1;
            }
            AffirmationStatus::Rejected | AffirmationStatus::Finalized => {}
        }
        for (_, mediator) in &self.mediators {
            if mediator == &AffirmationStatus::Pending {
                pending_affirms += 1;
            }
        }

        (pending_affirms, pending_finals)
    }

    pub fn reject(&mut self) -> Result<()> {
        // If the leg is already finalized, we cannot reject it.
        if self.status == AffirmationStatus::Finalized {
            return Err(anyhow!("Cannot reject a finalized leg"));
        }
        self.status = AffirmationStatus::Rejected;

        // If the sender is still pending, we mark it as finalized.  Since they cannot affirm a rejected leg.
        if self.sender == AffirmationStatus::Pending {
            self.sender = AffirmationStatus::Finalized;
        }
        // If the receiver is still pending, we mark it as finalized.  Since they cannot claim a rejected leg.
        if self.receiver == AffirmationStatus::Pending {
            self.receiver = AffirmationStatus::Finalized;
        }

        // Finalize the mediators if they exist.
        self.finalize_mediators();

        Ok(())
    }

    /// When a settlement is rejected or affirmed (all legs are affirmed), then we can finalize the mediators.
    pub fn finalize_mediators(&mut self) {
        // Mark the mediator as finalized if it exists.  Since they cannot affirm or reject anymore.
        for (_, mediator) in &mut self.mediators {
            *mediator = AffirmationStatus::Finalized;
        }
    }

    /// Verify a sender affirmation proof for this leg.
    pub fn sender_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        proof: &SenderAffirmationProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.sender != AffirmationStatus::Pending {
            return Err(anyhow!("Sender has already affirmed this leg"));
        }
        // verify the proof.
        proof
            .verify(&self.enc, tree_roots, rng)
            .context("Invalid sender affirmation proof")?;

        // Update the leg's status.
        self.sender = AffirmationStatus::Affirmed;
        self.update_status()?;

        Ok(())
    }

    /// Verify a receiver affirmation proof for this leg.
    pub fn receiver_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        proof: &ReceiverAffirmationProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.receiver != AffirmationStatus::Pending {
            return Err(anyhow!("Receiver has already affirmed this leg"));
        }
        // verify the proof.
        proof
            .verify(&self.enc, tree_roots, rng)
            .context("Invalid receiver affirmation proof")?;

        // Update the leg's status.
        self.receiver = AffirmationStatus::Affirmed;
        self.update_status()?;

        Ok(())
    }

    /// Verify an instant sender affirmation proof for this leg.
    pub fn instant_sender_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        proof: &InstantSenderAffirmationProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.sender != AffirmationStatus::Pending {
            return Err(anyhow!("Sender has already affirmed this leg"));
        }
        // verify the proof.
        proof
            .verify(&self.enc, tree_roots, rng)
            .context("Invalid sender affirmation proof")?;

        // Update the leg's status.
        self.sender = AffirmationStatus::Finalized;

        Ok(())
    }

    /// Verify an instant receiver affirmation proof for this leg.
    pub fn instant_receiver_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        proof: &InstantReceiverAffirmationProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.receiver != AffirmationStatus::Pending {
            return Err(anyhow!("Receiver has already affirmed this leg"));
        }
        // verify the proof.
        proof
            .verify(&self.enc, tree_roots, rng)
            .context("Invalid receiver affirmation proof")?;

        // Update the leg's status.
        self.receiver = AffirmationStatus::Finalized;

        Ok(())
    }

    /// Verify a mediator affirmation proof for this leg.
    pub fn mediator_affirmation(&mut self, proof: &MediatorAffirmationProof) -> Result<()> {
        if self.mediators.is_empty() {
            return Err(anyhow!("Leg does not require a mediator affirmation"));
        }
        let mediator_id = proof.key_index;
        let mediator = self
            .mediators
            .get_mut(&mediator_id)
            .ok_or_else(|| anyhow!("Invalid mediator key index for this leg"))?;
        if *mediator != AffirmationStatus::Pending {
            return Err(anyhow!("Mediator has already affirmed this leg"));
        }
        // verify the proof.
        proof
            .verify(&self.enc)
            .context("Invalid mediator affirmation proof")?;

        // Update the leg's mediator status based on the proof.
        if proof.accept {
            *mediator = AffirmationStatus::Affirmed;
        } else {
            *mediator = AffirmationStatus::Rejected;
        }
        self.update_status()?;
        Ok(())
    }

    /// Verify the sender's counter update proof for this leg.
    ///
    /// The sender is only allowed to submit this proof if the settlement has been executed.
    pub fn sender_counter_update<R: RngCore + CryptoRng>(
        &mut self,
        proof: &SenderCounterUpdateProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.sender != AffirmationStatus::Affirmed {
            return Err(anyhow!(
                "The sender's status must still be in the affirmed state to update the counter"
            ));
        }
        if self.status != AffirmationStatus::Affirmed {
            return Err(anyhow!("Leg must be affirmed before counter update"));
        }
        // verify the proof.
        proof
            .verify(&self.enc, tree_roots, rng)
            .context("Invalid sender counter update proof")?;

        // Update the leg's status.
        self.sender = AffirmationStatus::Finalized;
        self.update_status()?;

        Ok(())
    }

    /// Verify the sender's Revert proof for this leg.
    ///
    /// The sender is only allowed to submit this proof if the settlement has been rejected.
    pub fn sender_revert<R: RngCore + CryptoRng>(
        &mut self,
        proof: &SenderReversalProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.sender != AffirmationStatus::Affirmed {
            return Err(anyhow!(
                "The sender's status must still be in the affirmed state to reverse"
            ));
        }
        if self.status != AffirmationStatus::Rejected {
            return Err(anyhow!("Leg must be rejected before reversal"));
        }
        // verify the proof.
        proof
            .verify(&self.enc, tree_roots, rng)
            .context("Invalid sender reversal proof")?;

        // Update the leg's status.
        self.sender = AffirmationStatus::Finalized;
        self.update_status()?;

        Ok(())
    }

    /// Verify the receiver's claim proof for this leg.
    ///
    /// The receiver is only allowed to submit this proof if the settlement has been executed.
    pub fn receiver_claim<R: RngCore + CryptoRng>(
        &mut self,
        proof: &ReceiverClaimProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.receiver != AffirmationStatus::Affirmed {
            return Err(anyhow!(
                "The receiver's status must still be in the affirmed state to claim"
            ));
        }
        if self.status != AffirmationStatus::Affirmed {
            return Err(anyhow!("Leg must be affirmed before claim"));
        }
        // verify the proof.
        proof
            .verify(&self.enc, tree_roots, rng)
            .context("Invalid receiver claim proof")?;

        // Update the leg's status.
        self.receiver = AffirmationStatus::Finalized;
        self.update_status()?;

        Ok(())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SettlementStatus {
    Pending,
    Executed,
    Rejected,
    Finalized,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DartSettlement {
    pub id: SettlementRef,
    pub legs: Vec<DartSettlementLeg>,
    pub status: SettlementStatus,
    pub pending_affirms: u64,
    pub pending_finals: u64,
}

impl DartSettlement {
    pub fn from_proof(proof: SettlementProof<()>) -> Result<Self> {
        let id = proof.settlement_ref();
        let affirm_counts = proof.count_leg_affirmations()?;
        let pending_affirms = affirm_counts.total_affirmations();
        let legs = proof
            .legs
            .into_iter()
            .map(|leg| {
                let mediators = leg
                    .get_mediator_ids()?
                    .into_iter()
                    .map(|idx| (idx, AffirmationStatus::Pending))
                    .collect();
                Ok(DartSettlementLeg {
                    enc: leg.leg_enc,
                    sender: AffirmationStatus::Pending,
                    receiver: AffirmationStatus::Pending,
                    mediators,
                    status: AffirmationStatus::Pending,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(Self {
            id,
            legs,
            status: SettlementStatus::Pending,
            pending_affirms,
            pending_finals: 0,
        })
    }

    /// Ensure the settlement is in a pending state.
    pub fn ensure_pending(&self) -> Result<()> {
        if self.status != SettlementStatus::Pending && self.pending_affirms > 0 {
            return Err(anyhow!("Settlement is not in a pending state"));
        }
        Ok(())
    }

    /// Verify Instant Settlement Leg Affirmations
    pub fn instant_leg_affirmations<R: RngCore + CryptoRng>(
        &mut self,
        proofs: &[InstantSettlementLegAffirmations<(), AccountTreeConfig>],
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        self.ensure_pending()?;

        for proof in proofs {
            let leg_ref = proof.sender.leg_ref;
            if self.id != leg_ref.settlement_ref() {
                return Err(anyhow!(
                    "Leg reference settlement ID does not match this settlement"
                ));
            }
            let leg_id = leg_ref.leg_id() as usize;
            if leg_id >= self.legs.len() {
                return Err(anyhow!("Leg index {} out of bounds", leg_id));
            }
            let leg = &mut self.legs[leg_id];

            // Verify sender affirmation
            leg.instant_sender_affirmation(&proof.sender, &tree_roots, rng)?;

            // Verify receiver affirmation
            leg.instant_receiver_affirmation(&proof.receiver, &tree_roots, rng)?;

            // Verify mediator affirmations
            for mediator_proof in &proof.mediators {
                leg.mediator_affirmation(mediator_proof)?;
            }

            leg.update_status()?;
        }

        // If all legs are affirmed, update the status of the settlement.
        self.check_for_updated_status()?;
        Ok(())
    }

    /// Verify a sender affirmation proof for a specific leg in the settlement.
    pub fn sender_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        proof: &SenderAffirmationProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        self.ensure_pending()?;

        let leg_id = proof.leg_ref.leg_id() as usize;
        if leg_id >= self.legs.len() {
            return Err(anyhow!("Leg index {} out of bounds", leg_id));
        }
        let leg = &mut self.legs[leg_id];
        leg.sender_affirmation(proof, tree_roots, rng)?;

        // If the sender has affirmed, update the status of the settlement.
        self.check_for_updated_status()?;
        Ok(())
    }

    /// Verify a receiver affirmation proof for a specific leg in the settlement.
    pub fn receiver_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        proof: &ReceiverAffirmationProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        self.ensure_pending()?;

        let leg_id = proof.leg_ref.leg_id() as usize;
        if leg_id >= self.legs.len() {
            return Err(anyhow!("Leg index {} out of bounds", leg_id));
        }
        let leg = &mut self.legs[leg_id];
        leg.receiver_affirmation(proof, tree_roots, rng)?;

        // If the receiver has affirmed, update the status of the settlement.
        self.check_for_updated_status()?;
        Ok(())
    }

    /// Verify an instant sender affirmation proof for a specific leg in the settlement.
    pub fn instant_sender_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        proof: &InstantSenderAffirmationProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        self.ensure_pending()?;

        if self.pending_affirms > 1 {
            return Err(anyhow!(
                "Instant sender affirmation can only be performed when there is one pending affirmation left"
            ));
        }

        let leg_id = proof.leg_ref.leg_id() as usize;
        if leg_id >= self.legs.len() {
            return Err(anyhow!("Leg index {} out of bounds", leg_id));
        }
        let leg = &mut self.legs[leg_id];
        leg.instant_sender_affirmation(proof, tree_roots, rng)?;
        leg.update_status()?;

        // If the sender has affirmed, update the status of the settlement.
        self.check_for_updated_status()?;
        Ok(())
    }

    /// Verify an instant receiver affirmation proof for a specific leg in the settlement.
    pub fn instant_receiver_affirmation<R: RngCore + CryptoRng>(
        &mut self,
        proof: &InstantReceiverAffirmationProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        self.ensure_pending()?;

        if self.pending_affirms > 1 {
            return Err(anyhow!(
                "Instant receiver affirmation can only be performed when there is one pending affirmation left"
            ));
        }

        let leg_id = proof.leg_ref.leg_id() as usize;
        if leg_id >= self.legs.len() {
            return Err(anyhow!("Leg index {} out of bounds", leg_id));
        }
        let leg = &mut self.legs[leg_id];
        leg.instant_receiver_affirmation(proof, tree_roots, rng)?;
        leg.update_status()?;

        // If the receiver has affirmed, update the status of the settlement.
        self.check_for_updated_status()?;
        Ok(())
    }

    /// Verify a mediator affirmation proof for a specific leg in the settlement.
    pub fn mediator_affirmation(&mut self, proof: &MediatorAffirmationProof) -> Result<()> {
        self.ensure_pending()?;

        let leg_id = proof.leg_ref.leg_id() as usize;
        if leg_id >= self.legs.len() {
            return Err(anyhow!("Leg index {} out of bounds", leg_id));
        }
        let leg = &mut self.legs[leg_id];
        leg.mediator_affirmation(proof)?;

        if proof.accept {
            // If the mediator has accepted, update the status of the settlement.
            self.check_for_updated_status()?;
        } else {
            // If the mediator has rejected, set the settlement status to rejected.
            self.reject_all_legs()?;
        }
        Ok(())
    }

    /// Verify the sender's counter update proof for a specific leg in the settlement.
    pub fn sender_counter_update<R: RngCore + CryptoRng>(
        &mut self,
        proof: &SenderCounterUpdateProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.status != SettlementStatus::Executed {
            return Err(anyhow!(
                "Settlement must be executed before sender counter update"
            ));
        }

        let leg_id = proof.leg_ref.leg_id() as usize;
        if leg_id >= self.legs.len() {
            return Err(anyhow!("Leg index {} out of bounds", leg_id));
        }
        let leg = &mut self.legs[leg_id];
        leg.sender_counter_update(proof, tree_roots, rng)?;

        // If the sender has finalized the leg, update the status of the settlement.
        self.check_for_updated_status()?;
        Ok(())
    }

    /// Verify the sender's reversal proof for a specific leg in the settlement.
    pub fn sender_revert<R: RngCore + CryptoRng>(
        &mut self,
        proof: &SenderReversalProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.status != SettlementStatus::Rejected {
            return Err(anyhow!(
                "Settlement must be rejected before sender reversal"
            ));
        }

        let leg_id = proof.leg_ref.leg_id() as usize;
        if leg_id >= self.legs.len() {
            return Err(anyhow!("Leg index {} out of bounds", leg_id));
        }
        let leg = &mut self.legs[leg_id];
        leg.sender_revert(proof, tree_roots, rng)?;

        // If the sender has finalized the leg, update the status of the settlement.
        self.check_for_updated_status()?;
        Ok(())
    }

    /// Verify the receiver's claim proof for a specific leg in the settlement.
    pub fn receiver_claim<R: RngCore + CryptoRng>(
        &mut self,
        proof: &ReceiverClaimProof,
        tree_roots: impl ValidateCurveTreeRoot<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
        rng: &mut R,
    ) -> Result<()> {
        if self.status != SettlementStatus::Executed {
            return Err(anyhow!("Settlement must be executed before receiver claim"));
        }

        let leg_id = proof.leg_ref.leg_id() as usize;
        if leg_id >= self.legs.len() {
            return Err(anyhow!("Leg index {} out of bounds", leg_id));
        }
        let leg = &mut self.legs[leg_id];
        leg.receiver_claim(proof, tree_roots, rng)?;

        // If the receiver has finalized the leg, update the status of the settlement.
        self.check_for_updated_status()?;
        Ok(())
    }

    fn update_pending_counts(&mut self) {
        let mut pending_affirms = 0;
        let mut pending_finals = 0;
        for leg in &self.legs {
            let (affirms, finals) = leg.pending_counts();
            pending_affirms += affirms;
            pending_finals += finals;
        }
        self.pending_affirms = pending_affirms;
        self.pending_finals = pending_finals;
    }

    fn check_for_updated_status(&mut self) -> Result<()> {
        match self.status {
            SettlementStatus::Pending => {
                // Update pending counts first.
                self.update_pending_counts();
                if self.pending_affirms > 0 {
                    return Ok(()); // Still pending
                }
                if self.pending_finals > 0 {
                    // If there are no pending affirms but there are pending finals, we can execute the settlement.
                    self.execute()
                } else {
                    // If all legs are finalized, update the settlement status to finalized.
                    self.finalize()
                }
            }
            SettlementStatus::Executed | SettlementStatus::Rejected => {
                // Update pending counts first.
                self.update_pending_counts();
                if self.pending_affirms > 0 {
                    // This state should not happen.
                    return Err(anyhow!(
                        "Settlement in Executed or Rejected state cannot have pending affirmations"
                    ));
                }
                if self.pending_finals > 0 {
                    return Ok(()); // Still pending finalization
                }
                // If all legs are finalized, update the settlement status to finalized.
                self.finalize()
            }
            SettlementStatus::Finalized => {
                // If the settlement is already finalized, do nothing.
                Ok(())
            }
        }
    }

    fn set_status(&mut self, status: SettlementStatus) {
        self.status = status;
    }

    fn reject_all_legs(&mut self) -> Result<()> {
        // Reject all legs in the settlement.
        for leg in &mut self.legs {
            leg.reject()?;
        }
        self.status = SettlementStatus::Rejected;
        Ok(())
    }

    /// Execute the settlement, marking it as executed.
    fn execute(&mut self) -> Result<()> {
        // Ensure the settlement is pending before executing.
        self.ensure_pending()?;

        // Finalize the mediators on all legs.
        for leg in &mut self.legs {
            leg.finalize_mediators();
        }

        // If the settlement is pending, we can execute it.
        self.set_status(SettlementStatus::Executed);
        log::debug!("Settlement {:?} executed", self.id);
        Ok(())
    }

    /// Finalize the settlement, marking it as finalized.
    fn finalize(&mut self) -> Result<()> {
        // Can prune the settlement state.

        // If the settlement is executed or rejected, we can finalize it.
        self.set_status(SettlementStatus::Finalized);
        log::debug!("Settlement {:?} finalized", self.id);
        Ok(())
    }
}

pub struct DartProverAccountTree {
    account_tree: ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
    last_leaf_index: usize,
}

impl DartProverAccountTree {
    pub fn new() -> Result<Self> {
        Ok(Self {
            account_tree: ProverCurveTree::new(ACCOUNT_TREE_HEIGHT)?,
            last_leaf_index: 0,
        })
    }

    pub fn prover_account_tree(
        &self,
    ) -> &ProverCurveTree<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig> {
        &self.account_tree
    }

    pub fn apply_updates(&mut self, chain: &DartChainState) -> Result<()> {
        let block_number = chain.get_block_number();
        let new_leafs = chain.get_new_account_leafs(self.last_leaf_index);
        log::info!(
            "Applying {} new account leafs to the prover account tree",
            new_leafs.len()
        );
        self.account_tree.set_block_number(block_number)?;
        for leaf in new_leafs {
            self.account_tree.insert(leaf.as_leaf_value()?)?;
            self.last_leaf_index += 1;
        }
        log::info!(
            "Prover account tree now has {} leaves",
            self.last_leaf_index
        );
        Ok(())
    }
}

pub trait AccountLookup {
    /// Get the encryption public key for the account.
    fn get_account_enc_pk(&self, account: &AccountPublicKey) -> Option<EncryptionPublicKey>;

    /// Get the account public key for the given encryption public key.
    fn get_account(&self, enc_pk: &EncryptionPublicKey) -> Option<AccountPublicKey>;
}

#[derive(Clone, Debug, Default)]
#[cfg(feature = "std")]
pub struct AccountLookupMap {
    enc_to_acct: HashMap<EncryptionPublicKey, AccountPublicKey>,
    acct_to_enc: HashMap<AccountPublicKey, EncryptionPublicKey>,
}

#[cfg(feature = "std")]
impl AccountLookup for AccountLookupMap {
    fn get_account_enc_pk(&self, account: &AccountPublicKey) -> Option<EncryptionPublicKey> {
        self.acct_to_enc.get(account).copied()
    }

    fn get_account(&self, enc_pk: &EncryptionPublicKey) -> Option<AccountPublicKey> {
        self.enc_to_acct.get(enc_pk).copied()
    }
}

#[cfg(feature = "std")]
impl AccountLookupMap {
    pub fn new() -> Self {
        Self {
            enc_to_acct: HashMap::new(),
            acct_to_enc: HashMap::new(),
        }
    }

    pub fn ensure_unregistered(&self, keys: &AccountPublicKeys) -> Result<(), Error> {
        if self.enc_to_acct.contains_key(&keys.enc) {
            return Err(Error::AccountPublicKeyExists);
        }
        if self.acct_to_enc.contains_key(&keys.acct) {
            return Err(Error::AccountPublicKeyExists);
        }
        Ok(())
    }

    /// Register an account's encryption public key and account public key in the lookup map.
    pub fn register_account_keys(&mut self, account_pk_keys: &AccountPublicKeys) {
        self.enc_to_acct
            .insert(account_pk_keys.enc, account_pk_keys.acct);
        self.acct_to_enc
            .insert(account_pk_keys.acct, account_pk_keys.enc);
    }
}

pub struct DartChainState {
    signers: HashMap<SignerAddress, SignerState>,

    /// Bidirectional map between account public and encryption key.
    accounts: AccountLookupMap,
    /// Account owner map.
    account_owners: HashMap<AccountPublicKey, SignerAddress>,

    block_number: BlockNumber,
    asset_tree: AssetCurveTree,
    next_asset_id: AssetId,
    asset_details: HashMap<AssetId, DartAssetDetails>,

    /// Accounts initialized with assets.
    account_assets: HashSet<(AccountPublicKey, AssetId)>,
    account_tree: CurveTreeWithBackend<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig>,
    account_nullifiers: HashSet<AccountStateNullifier>,

    /// Account leafs in the order they have been inserted.
    /// This is used by users to build the tree off-chain.
    account_leafs: Vec<AccountStateCommitment>,

    /// Pending account tree updates to be applied at the end of the block.
    pending_account_updates: Vec<AccountStateCommitment>,

    /// Settlements in the chain state.
    settlements: HashMap<SettlementRef, DartSettlement>,
}

impl DartChainState {
    pub fn new() -> Result<Self> {
        let asset_tree = AssetCurveTree::new()?;
        let account_tree = CurveTreeWithBackend::new(ACCOUNT_TREE_HEIGHT)?;
        Ok(Self {
            signers: HashMap::new(),

            accounts: AccountLookupMap::new(),
            account_owners: HashMap::new(),

            block_number: 0,
            asset_tree,
            next_asset_id: 0,
            asset_details: HashMap::new(),

            account_assets: HashSet::new(),
            account_tree,
            account_nullifiers: HashSet::new(),
            account_leafs: Vec::new(),
            pending_account_updates: Vec::new(),

            settlements: HashMap::new(),
        })
    }

    pub fn asset_tree(&self) -> &CurveTreeWithBackend<ASSET_TREE_L, ASSET_TREE_M, AssetTreeConfig> {
        &self.asset_tree.tree
    }

    pub fn account_tree(
        &self,
    ) -> &CurveTreeWithBackend<ACCOUNT_TREE_L, ACCOUNT_TREE_M, AccountTreeConfig> {
        &self.account_tree
    }

    pub fn account_leafs(&self) -> &[AccountStateCommitment] {
        &self.account_leafs
    }

    pub fn get_block_number(&self) -> BlockNumber {
        self.block_number
    }

    pub fn get_new_account_leafs(&self, last_idx: usize) -> &[AccountStateCommitment] {
        if last_idx >= self.account_leafs.len() {
            log::info!("No new account leafs to return");
            return &[];
        }
        log::info!(
            "get new accounts: {} -> {}",
            last_idx,
            self.account_leafs.len()
        );
        &self.account_leafs[last_idx..]
    }

    pub fn end_block(&mut self) -> Result<()> {
        // Make sure the curve tree are using the same block number.
        self.block_number += 1;
        self.asset_tree.set_block_number(self.block_number)?;
        self.account_tree.set_block_number(self.block_number)?;

        for commitment in self.pending_account_updates.drain(..) {
            // Add the commitment to the account tree.
            self.account_tree.insert_leaf(commitment.as_leaf_value()?)?;
            self.account_leafs.push(commitment);
        }
        // We need to store curve tree roots.
        self.asset_tree.store_root()?;
        self.account_tree.store_root()?;

        Ok(())
    }

    pub fn create_signer(&mut self, name: &str) -> Result<SignerAddress> {
        let address = SignerAddress(name.to_string());
        if self.signers.contains_key(&address) {
            return Err(anyhow!("Signer already exists: {}", name));
        }
        self.signers
            .insert(address.clone(), SignerState { nonce: 0 });
        Ok(address)
    }

    pub fn create_signers(&mut self, names: &[&str]) -> Result<Vec<SignerAddress>> {
        let mut addresses = Vec::new();
        for &name in names {
            let address = self.create_signer(name)?;
            addresses.push(address);
        }
        Ok(addresses)
    }

    pub fn ensure_caller(&self, caller: &SignerAddress) -> Result<()> {
        if !self.signers.contains_key(caller) {
            return Err(anyhow!("Caller does not exist: {:?}", caller));
        }
        Ok(())
    }

    pub fn register_account(
        &mut self,
        caller: &SignerAddress,
        keys: AccountPublicKeys,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        self.accounts.ensure_unregistered(&keys)?;

        self.accounts.register_account_keys(&keys);
        self.account_owners
            .insert(keys.acct.clone(), caller.clone());

        Ok(())
    }

    pub fn ensure_account_owner(
        &self,
        caller: &SignerAddress,
        account: &AccountPublicKey,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        if let Some(owner) = self.account_owners.get(account) {
            if owner != caller {
                return Err(anyhow!(
                    "Account {:?} is owned by {:?}, not {:?}",
                    account,
                    owner,
                    caller
                ));
            }
        } else {
            return Err(anyhow!("Account {:?} is not registered", account));
        }

        Ok(())
    }

    pub fn create_dart_asset(
        &mut self,
        caller: &SignerAddress,
        mediators: &[EncryptionPublicKey],
        auditors: &[EncryptionPublicKey],
    ) -> Result<DartAssetDetails> {
        self.ensure_caller(caller)?;

        let asset_id = self.next_asset_id;
        self.next_asset_id += 1;

        let asset_details = DartAssetDetails::new(asset_id, caller.clone(), mediators, auditors);
        let asset_state = asset_details.asset_state();

        self.asset_tree.set_asset_state(asset_state)?;
        self.asset_details.insert(asset_id, asset_details.clone());

        Ok(asset_details)
    }

    pub fn get_asset_state(&self, asset_id: AssetId) -> Result<AssetState> {
        self.ensure_asset_exists(asset_id)?;
        self.asset_tree
            .get_asset_state(asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} does not exist in the asset tree", asset_id))
    }

    pub fn ensure_asset_exists(&self, asset_id: AssetId) -> Result<&DartAssetDetails> {
        self.asset_details
            .get(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} does not exist", asset_id))
    }

    pub fn ensure_asset_owner(
        &mut self,
        caller: &SignerAddress,
        asset_id: AssetId,
    ) -> Result<&mut DartAssetDetails> {
        let asset_details = self
            .asset_details
            .get_mut(&asset_id)
            .ok_or_else(|| anyhow!("Asset ID {} does not exist", asset_id))?;
        if &asset_details.owner != caller {
            return Err(anyhow!(
                "Caller {:?} is not the owner of asset ID {}",
                caller,
                asset_id
            ));
        }
        Ok(asset_details)
    }

    fn _add_account_commitment(&mut self, commitment: AccountStateCommitment) -> Result<()> {
        // Queue the commitment for the end of the block.
        self.pending_account_updates.push(commitment);

        Ok(())
    }

    pub fn ensure_nullifier_unique(&self, nullifier: &AccountStateNullifier) -> Result<()> {
        if self.account_nullifiers.contains(nullifier) {
            return Err(anyhow!("Nullifier {:?} has already been used", nullifier));
        }
        Ok(())
    }

    fn _add_nullifier(&mut self, nullifier: AccountStateNullifier) {
        self.account_nullifiers.insert(nullifier);
    }

    pub fn initialize_account_asset(
        &mut self,
        caller: &SignerAddress,
        proof: AccountAssetRegistrationProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;
        self.ensure_account_owner(caller, &proof.account)?;
        self.ensure_asset_exists(proof.asset_id)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        // Ensure the account has not already been initialized with the asset.
        if !self.account_assets.insert((proof.account, proof.asset_id)) {
            return Err(anyhow!(
                "Account {:?} is already initialized with an asset",
                proof.account
            ));
        }

        // Verify the proof for the account and asset.
        let mut rng = new_rng();
        proof
            .verify(caller.ctx(), self.account_tree.parameters(), &mut rng)
            .with_context(|| {
                format!(
                    "Invalid proof for account {:?} and asset ID {}",
                    proof.account, proof.asset_id
                )
            })?;

        // Add the account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment)?;

        Ok(())
    }

    pub fn mint_assets(&mut self, caller: &SignerAddress, proof: AssetMintingProof) -> Result<()> {
        self.ensure_caller(caller)?;

        // Update the asset total supply.
        {
            let asset_details = self.ensure_asset_owner(caller, proof.asset_id)?;
            let new_total_supply = asset_details
                .total_supply
                .checked_add(proof.amount)
                .ok_or_else(|| anyhow!("Total supply overflow for asset ID {}", proof.asset_id))?;
            if new_total_supply > MAX_BALANCE {
                return Err(anyhow!(
                    "Total supply exceeds maximum amount for asset ID {}",
                    proof.asset_id
                ));
            }
            asset_details.total_supply = new_total_supply;
        }

        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        let mut rng = new_rng();
        // Verify the minting proof.
        proof
            .verify(caller.ctx(), &self.account_tree, &mut rng)
            .context("Invalid minting proof")?;

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        Ok(())
    }

    pub fn create_settlement(
        &mut self,
        caller: &SignerAddress,
        proof: SettlementProof<()>,
    ) -> Result<SettlementRef> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        // Ensure the settlement has a valid number of legs.
        if proof.legs.is_empty() || proof.legs.len() > SETTLEMENT_MAX_LEGS as usize {
            return Err(anyhow!(
                "Settlement must have between 1 and {} legs",
                SETTLEMENT_MAX_LEGS
            ));
        }

        let mut rng = new_rng();
        // verify the settlement proof.
        proof
            .verify(&self.asset_tree, &mut rng)
            .context("Invalid settlement proof")?;

        // Save the settlement.
        let settlement = DartSettlement::from_proof(proof)?;
        let settlement_ref = settlement.id;
        self.settlements.insert(settlement_ref, settlement);

        Ok(settlement_ref)
    }

    pub fn execute_instant_settlement(
        &mut self,
        caller: &SignerAddress,
        proof: InstantSettlementProof<()>,
    ) -> Result<SettlementRef> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        // Ensure the settlement has a valid number of legs.
        let leg_count = proof.leg_count();
        if leg_count == 0 || leg_count > SETTLEMENT_MAX_LEGS as usize {
            return Err(anyhow!(
                "Settlement must have between 1 and {} legs",
                SETTLEMENT_MAX_LEGS
            ));
        }

        // Ensure leg affirmation refernes are valid.
        if !proof.check_leg_references() {
            return Err(anyhow!(
                "Invalid leg references in instant settlement proof"
            ));
        }

        let mut rng = new_rng();
        // verify the settlement proof.
        proof
            .settlement
            .verify(&self.asset_tree, &mut rng)
            .context("Invalid settlement proof")?;

        // Create the settlement.
        let mut settlement = DartSettlement::from_proof(proof.settlement)?;
        let settlement_ref = settlement.id;

        // Process all instant affirmations.
        settlement.instant_leg_affirmations(
            &proof.leg_affirmations,
            &self.account_tree,
            &mut rng,
        )?;

        // Ensure that the settlement executed and finalized.
        if settlement.status != SettlementStatus::Finalized {
            return Err(anyhow!("Instant settlement did not finalize as expected"));
        }

        // Save the settlement.
        self.settlements.insert(settlement_ref, settlement);

        Ok(settlement_ref)
    }

    /// Query an encrypted settlement leg by reference.
    pub fn get_settlement_leg(&self, leg_ref: &LegRef) -> Result<&DartSettlementLeg> {
        let settlement_ref = leg_ref.settlement_ref();
        let leg_id = leg_ref.leg_id() as usize;

        // Get the settlement.
        let settlement = self
            .settlements
            .get(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        // Get the leg.
        settlement.legs.get(leg_id).ok_or_else(|| {
            anyhow!(
                "Leg index {} out of bounds for settlement {:?}",
                leg_id,
                settlement_ref
            )
        })
    }

    /// Query the settlement status by settlement ID.
    pub fn get_settlement_status(&self, settlement_ref: SettlementRef) -> Result<SettlementStatus> {
        self.settlements
            .get(&settlement_ref)
            .map(|settlement| settlement.status.clone())
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))
    }

    /// Verify a sender affirmation proof for a settlement leg.
    pub fn sender_affirmation(
        &mut self,
        caller: &SignerAddress,
        proof: SenderAffirmationProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        let settlement_ref = proof.leg_ref.settlement_ref();

        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        // Get the settlement.
        let settlement = self
            .settlements
            .get_mut(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        let mut rng = new_rng();
        // Verify the sender affirmation proof and update the settlement status.
        settlement.sender_affirmation(&proof, &self.account_tree, &mut rng)?;

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        Ok(())
    }

    /// Verify a receiver affirmation proof for a settlement leg.
    pub fn receiver_affirmation(
        &mut self,
        caller: &SignerAddress,
        proof: ReceiverAffirmationProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        let settlement_ref = proof.leg_ref.settlement_ref();

        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        // Get the settlement.
        let settlement = self
            .settlements
            .get_mut(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        let mut rng = new_rng();
        // Verify the receiver affirmation proof and update the settlement status.
        settlement.receiver_affirmation(&proof, &self.account_tree, &mut rng)?;

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        Ok(())
    }

    /// Verify a instant sender affirmation proof for a settlement leg.
    pub fn instant_sender_affirmation(
        &mut self,
        caller: &SignerAddress,
        proof: InstantSenderAffirmationProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        let settlement_ref = proof.leg_ref.settlement_ref();

        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        // Get the settlement.
        let settlement = self
            .settlements
            .get_mut(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        let mut rng = new_rng();
        // Verify the sender affirmation proof and update the settlement status.
        settlement.instant_sender_affirmation(&proof, &self.account_tree, &mut rng)?;

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        Ok(())
    }

    /// Verify a instant receiver affirmation proof for a settlement leg.
    pub fn instant_receiver_affirmation(
        &mut self,
        caller: &SignerAddress,
        proof: InstantReceiverAffirmationProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        let settlement_ref = proof.leg_ref.settlement_ref();

        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        // Get the settlement.
        let settlement = self
            .settlements
            .get_mut(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        let mut rng = new_rng();
        // Verify the receiver affirmation proof and update the settlement status.
        settlement.instant_receiver_affirmation(&proof, &self.account_tree, &mut rng)?;

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        Ok(())
    }

    /// Verify a mediator affirmation proof for a specific leg in the settlement.
    pub fn mediator_affirmation(
        &mut self,
        caller: &SignerAddress,
        proof: MediatorAffirmationProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        let settlement_ref = proof.leg_ref.settlement_ref();

        // Get the settlement.
        let settlement = self
            .settlements
            .get_mut(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        // Verify the mediator affirmation proof and update the settlement status.
        settlement.mediator_affirmation(&proof)?;

        Ok(())
    }

    /// Verify a sender counter update proof for a settlement leg.
    pub fn sender_counter_update(
        &mut self,
        caller: &SignerAddress,
        proof: SenderCounterUpdateProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        let settlement_ref = proof.leg_ref.settlement_ref();

        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        // Get the settlement.
        let settlement = self
            .settlements
            .get_mut(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        let mut rng = new_rng();
        // Verify the sender counter update proof and update the settlement status.
        settlement.sender_counter_update(&proof, &self.account_tree, &mut rng)?;

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        Ok(())
    }

    /// Verify a sender reversal proof for a settlement leg.
    pub fn sender_revert(
        &mut self,
        caller: &SignerAddress,
        proof: SenderReversalProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        let settlement_ref = proof.leg_ref.settlement_ref();

        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        // Get the settlement.
        let settlement = self
            .settlements
            .get_mut(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        let mut rng = new_rng();
        // Verify the sender reversal proof and update the settlement status.
        settlement.sender_revert(&proof, &self.account_tree, &mut rng)?;

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        Ok(())
    }

    /// Verify a receiver claim proof for a settlement leg.
    pub fn receiver_claim(
        &mut self,
        caller: &SignerAddress,
        proof: ReceiverClaimProof,
    ) -> Result<()> {
        self.ensure_caller(caller)?;

        // Test SCALE encoding of the proof.
        let proof = scale_encode_and_decode_test(&proof)?;

        let settlement_ref = proof.leg_ref.settlement_ref();

        // Ensure the nullifier is unique.
        let nullifier = proof.nullifier();
        self.ensure_nullifier_unique(&nullifier)?;

        // Get the settlement.
        let settlement = self
            .settlements
            .get_mut(&settlement_ref)
            .ok_or_else(|| anyhow!("Settlement {:?} does not exist", settlement_ref))?;

        let mut rng = new_rng();
        // Verify the receiver claim proof and update the settlement status.
        settlement.receiver_claim(&proof, &self.account_tree, &mut rng)?;

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment())?;
        self._add_nullifier(nullifier);

        Ok(())
    }
}
