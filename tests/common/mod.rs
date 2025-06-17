#![allow(dead_code)]

use anyhow::{anyhow, Result};

use std::collections::{HashMap, HashSet};

use dart::{curve_tree::{ProverCurveTree, RootHistory, VerifierCurveTree}, *};

/// A fake "Substrate" signer address for testing purposes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SignerAddress(pub String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignerState {
    pub nonce: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DartAssetDetails {
    pub asset_id: AssetId,
    pub owner: SignerAddress,
    pub total_supply: Balance,
    pub auditor: AuditorOrMediator,
}

impl DartAssetDetails {
    pub fn new(asset_id: AssetId, owner: SignerAddress, auditor: AuditorOrMediator) -> Self {
        Self {
            asset_id,
            owner,
            total_supply: 0,
            auditor,
        }
    }

    pub fn asset_state(&self) -> AssetState {
        let (is_mediator, pk) = match &self.auditor {
            AuditorOrMediator::Auditor(pk) => (false, pk.clone()),
            AuditorOrMediator::Mediator(pk) => (true, pk.enc.clone()),
        };
        AssetState::new(self.asset_id, is_mediator, pk)
    }
}

pub struct DartChainState {
    signers: HashMap<SignerAddress, SignerState>,

    /// Bidirectional map between account public and encryption key.
    accounts: AccountLookupMap,
    /// Account owner map.
    account_owners: HashMap<AccountPublicKey, SignerAddress>,

    asset_tree: AssetCurveTree,
    asset_roots: RootHistory<ASSET_TREE_L>,
    next_asset_id: AssetId,
    asset_details: HashMap<AssetId, DartAssetDetails>,

    /// Accounts initialized with assets.
    account_assets: HashSet<(AccountPublicKey, AssetId)>,
    account_tree: VerifierCurveTree<ACCOUNT_TREE_L>,
    account_roots: RootHistory<ACCOUNT_TREE_L>,
    account_nullifiers: HashSet<AccountStateNullifier>,

    /// Also build the prover account tree for testing purposes.
    prover_account_tree: ProverCurveTree<ACCOUNT_TREE_L>,
}

impl DartChainState {
    pub fn new() -> Result<Self> {
        let asset_tree = AssetCurveTree::new()?;
        let account_tree = VerifierCurveTree::new(ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_GENS)?;
        Ok(Self {
            signers: HashMap::new(),

            accounts: AccountLookupMap::new(),
            account_owners: HashMap::new(),

            asset_roots: RootHistory::new(10, asset_tree.params()),
            asset_tree,
            next_asset_id: 0,
            asset_details: HashMap::new(),

            account_assets: HashSet::new(),
            account_roots: RootHistory::new(10, account_tree.params()),
            account_tree,
            account_nullifiers: HashSet::new(),

            prover_account_tree: ProverCurveTree::new(ACCOUNT_TREE_HEIGHT, ACCOUNT_TREE_GENS)?,
        })
    }

    pub fn asset_tree(&self) -> &AssetCurveTree {
        &self.asset_tree
    }

    pub fn account_tree(&self) -> &VerifierCurveTree<ACCOUNT_TREE_L> {
        &self.account_tree
    }

    pub fn prover_account_tree(&self) -> &ProverCurveTree<ACCOUNT_TREE_L> {
        &self.prover_account_tree
    }

    pub fn create_signer(&mut self, name: &str) -> Result<SignerAddress> {
        let address = SignerAddress(name.to_string());
        if self.signers.contains_key(&address) {
            return Err(anyhow!("Signer already exists: {}", name));
        }
        self.signers.insert(address.clone(), SignerState { nonce: 0 });
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

    pub fn register_account(&mut self, caller: &SignerAddress, keys: AccountPublicKeys) -> Result<()> {
        self.ensure_caller(caller)?;

        self.accounts.ensure_unregistered(&keys)?;

        self.accounts.register_account_keys(&keys);
        self.account_owners.insert(keys.acct.clone(), caller.clone());

        Ok(())
    }

    pub fn ensure_account_owner(&self, caller: &SignerAddress, account: &AccountPublicKey) -> Result<()> {
        self.ensure_caller(caller)?;

        if let Some(owner) = self.account_owners.get(account) {
            if owner != caller {
                return Err(anyhow!("Account {:?} is owned by {:?}, not {:?}", account, owner, caller));
            }
        } else {
            return Err(anyhow!("Account {:?} is not registered", account));
        }

        Ok(())
    }

    pub fn create_dart_asset(&mut self, caller: &SignerAddress, auditor: AuditorOrMediator) -> Result<DartAssetDetails> {
        self.ensure_caller(caller)?;

        let asset_id = self.next_asset_id;
        self.next_asset_id += 1;

        let asset_details = DartAssetDetails::new(asset_id, caller.clone(), auditor);
        let asset_state = asset_details.asset_state();

        self.asset_tree.set_asset_state(asset_state)?;
        self.asset_details.insert(asset_id, asset_details.clone());

        Ok(asset_details)
    }

    pub fn ensure_asset_exists(&self, asset_id: AssetId) -> Result<&DartAssetDetails> {
        self.asset_details.get(&asset_id).ok_or_else(|| {
            anyhow!("Asset ID {} does not exist", asset_id)
        })
    }

    pub fn ensure_asset_owner(&mut self, caller: &SignerAddress, asset_id: AssetId) -> Result<&mut DartAssetDetails> {
        let asset_details = self.asset_details.get_mut(&asset_id).ok_or_else(|| {
            anyhow!("Asset ID {} does not exist", asset_id)
        })?;
        if &asset_details.owner != caller {
            return Err(anyhow!("Caller {:?} is not the owner of asset ID {}", caller, asset_id));
        }
        Ok(asset_details)
    }

    fn _add_account_commitment(&mut self, commitment: AccountStateCommitment) -> Result<()> {
        // Add the commitment to the account tree.
        self.account_tree.insert(commitment.0.0);
        self.prover_account_tree.insert(commitment.0.0)?;

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

    pub fn push_tree_roots(&mut self) {
        // Push the current asset and account tree roots to their respective histories.
        self.asset_roots.add_root(self.asset_tree.root_node());
        self.account_roots.add_root(self.account_tree.root_node());
    }

    pub fn initialize_account_asset(&mut self, caller: &SignerAddress, proof: AccountAssetRegistrationProof) -> Result<()> {
        self.ensure_caller(caller)?;
        self.ensure_account_owner(caller, &proof.account)?;
        self.ensure_asset_exists(proof.asset_id)?;

        // Ensure the account has not already been initialized with the asset.
        if !self.account_assets.insert((proof.account, proof.asset_id)) {
            return Err(anyhow!("Account {:?} is already initialized with an asset", proof.account));
        }

        // Verify the proof for the account and asset.
        if !proof.verify() {
            return Err(anyhow!("Invalid proof for account {:?} and asset ID {}", proof.account, proof.asset_id));
        }

        // Add the account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment)?;

        Ok(())
    }

    pub fn mint_assets(&mut self, caller: &SignerAddress, proof: AssetMintingProof) -> Result<()> {
        self.ensure_caller(caller)?;

        // Update the asset total supply.
        {
            let asset_details = self.ensure_asset_owner(caller, proof.asset_id)?;
            let new_total_supply = asset_details.total_supply.checked_add(proof.amount)
                .ok_or_else(|| anyhow!("Total supply overflow for asset ID {}", proof.asset_id))?;
            if new_total_supply > MAX_AMOUNT {
                return Err(anyhow!("Total supply exceeds maximum amount for asset ID {}", proof.asset_id));
            }
            asset_details.total_supply = new_total_supply;
        }

        self.ensure_nullifier_unique(&proof.nullifier)?;

        // Verify the minting proof.
        if !proof.verify(&self.account_roots) {
            return Err(anyhow!("Invalid minting proof for asset ID {}", proof.asset_id));
        }

        // Add the new account state commitment to the account tree.
        self._add_account_commitment(proof.account_state_commitment)?;
        self._add_nullifier(proof.nullifier);

        Ok(())
    }
}