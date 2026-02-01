use ark_ec::{AffineRepr, CurveGroup};
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizeMultiPath};
use curve_tree_relations::parameters::SelRerandParameters;
use ark_std::{vec, vec::Vec, io::{Read, Write}, collections::BTreeMap, format};
use ark_std::iterable::Iterable;
use bulletproofs::r1cs::{ConstraintSystem, LinearCombination, Prover, Variable, Verifier};
use curve_tree_relations::batched_curve_tree_prover::CurveTreeWitnessMultiPath;
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::partial::{Partial1PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::Zeroize;
use polymesh_dart_common::{Balance, BALANCE_BITS};
use crate::error::{Error, Result};
use crate::account::state::NUM_GENERATORS;
use crate::account::{AccountCommitmentKeyTrait, AccountState, AccountStateCommitment};
use crate::leg::AssetCommitmentParams;
use crate::{add_to_transcript, NONCE_LABEL, RE_RANDOMIZED_PATH_LABEL, TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL, UPDATED_ACCOUNT_COMMITMENT_LABEL};
use crate::util::{enforce_constraints_for_randomness_relations, prove_with_rng, verify_with_rng, BPProof};
use itertools::Itertools;
use schnorr_pok::discrete_log::{PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol};

const CT_ASSET_ID_LABEL: &'static [u8; 19] = b"asset_id_ciphertext";
const CT_PARTY_LABEL: &'static [u8; 16] = b"party_ciphertext";
const CT_AMOUNT_LABEL: &'static [u8; 17] = b"amount_ciphertext";

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PortfolioMoveCiphertext<G: AffineRepr> {
    pub ct_asset_id: G,
    pub ct_participants: Vec<G>,
    pub ct_amounts: Vec<(u16, u16, G)>,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AssetCorrectnessProof<
    const L_ASS: usize,
    const M_ASS: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub re_randomized_path_asset: SelectAndRerandomizeMultiPath<L_ASS, M_ASS, G1, G0>,
    pub re_randomized_points: Vec<Affine<G0>>,
    pub resp_asset_id: PokPedersenCommitment<Affine<G0>>,
}

// Question: Do other (except txn sender) accounts need to decrypt this? If yes, then we need to create extra DH elements such that each account can decrypt?
// If yes, then how much? Does each account need to be able to decrypt all other accounts and amounts or only the ones where its involved?
// Also, a malicious sender could still escape this since there is no (provable) connection between enc and aff. keys so sender can do DH with any key.

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PortfolioMoveProof<
    const L_ACC: usize,
    const M_ACC: usize,
    const L_ASS: usize,
    const M_ASS: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// When this is None, external [`R1CSProof`] will be used and [`PortfolioMoveProof`] only
    /// contains proof for the sigma protocols and enforces the Bulletproof constraints.
    pub r1cs_proof: Option<BPProof<G0, G1>>,
    pub re_randomized_paths_accounts: Vec<SelectAndRerandomizeMultiPath<L_ACC, M_ACC, G0, G1>>,
    pub t_r_leaves_acc: Vec<Affine<G0>>,
    pub t_acc_new: Vec<Affine<G0>>,
    pub comm_bp: Affine<G0>,
    pub t_comm_bp: Affine<G0>,
    pub resp_enc_asset_id: PokPedersenCommitment<Affine<G0>>,
    pub resp_leaves_acc: Vec<PartialSchnorrResponse<Affine<G0>>>,
    pub resp_acc_new: Vec<PartialSchnorrResponse<Affine<G0>>>,
    pub resp_null: Vec<PartialPokDiscreteLog<Affine<G0>>>,
    pub resp_enc_pk: Vec<Partial1PokPedersenCommitment<Affine<G0>>>,
    pub resp_enc_amounts: Vec<PokPedersenCommitment<Affine<G0>>>,
    pub resp_comm_bp: PartialSchnorrResponse<Affine<G0>>,
}

impl<
    const L_ACC: usize,
    const M_ACC: usize,
    const L_ASS: usize,
    const M_ASS: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> PortfolioMoveProof<L_ACC, M_ACC, L_ASS, M_ASS, F0, F1, G0, G1>
{
    /// Assumes that asset tree uses the same Bulletproofs params but odd and even layer swapped from account tree
    /// Returns the proof, ciphertext, new account states of all accounts, new state account commitments and nullifier of each account
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        accounts: Vec<AccountState<Affine<G0>>>,
        account_enc_keys: Vec<Affine<G0>>,
        transfers: Vec<(u16, u16, Balance)>,
        leaf_path_accounts: Vec<CurveTreeWitnessMultiPath<L_ACC, M_ACC, G0, G1>>,
        account_tree_root: &Root<L_ACC, M_ACC, G0, G1>,
        leaf_path_asset: CurveTreeWitnessMultiPath<L_ACC, M_ACC, G1, G0>,
        asset_tree_root: &Root<L_ASS, M_ASS, G1, G0>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParameters<G0, G1>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
    ) -> Result<(Self, PortfolioMoveCiphertext<Affine<G0>>, Vec<AccountState<Affine<G0>>>, Vec<AccountStateCommitment<Affine<G0>>>, Vec<Affine<G0>>)> {
        if accounts.is_empty() {
            return Err(Error::ProofGenerationError("Need at least one account".to_string()));
        }
        if transfers.is_empty() {
            return Err(Error::ProofGenerationError("Need at least one transfer".to_string()));
        }

        let num_accounts = accounts.len();
        let num_transfers = transfers.len();

        if account_enc_keys.len() != num_accounts {
            return Err(Error::ProofGenerationError("Need same number of encryption keys as accounts".to_string()))
        }
        if leaf_path_accounts
            .iter()
            .fold(0, |acc, path| acc + path.num_indices())
            != num_accounts as u32
        {
            return Err(Error::ProofGenerationError(
                "Total number of paths in leaf_path_accounts does not match number of accounts".to_string(),
            ));
        }

        let mut updated_accounts = Vec::with_capacity(num_accounts);
        let mut updated_account_commitments = Vec::with_capacity(num_accounts);
        let mut net_change = BTreeMap::new();

        // Calculate net change in account balances
        for (sender, receiver, amount) in transfers.clone() {
            if sender as usize > num_accounts {
                return Err(Error::ProofGenerationError(format!("Sender index {sender} out of bounds")));
            }
            if receiver as usize > num_accounts {
                return Err(Error::ProofGenerationError(format!("Receiver index {sender} out of bounds")));
            }
            if sender == receiver {
                return Err(Error::ProofGenerationError(format!("Sender and receiver {sender} cant be same")));
            }
            let s = net_change.get(&sender).unwrap_or(&0);
            net_change.insert(sender, s - amount as i128);
            let r = net_change.get(&receiver).unwrap_or(&0);
            net_change.insert(receiver, r + amount as i128);
        }

        if net_change.len() != num_accounts {
            return Err(Error::ProofGenerationError("Some accounts are not involved in transfers".to_string()));
        }

        let asset_id = accounts[0].asset_id;
        let id = accounts[0].id;
        // Create updated accounts and commitments
        for (i, account) in accounts.iter().enumerate() {
            if account.asset_id != asset_id {
                return Err(Error::ProofGenerationError(format!("Account index {i}'s asset id {} not the same as other's {asset_id}", account.asset_id)));
            }
            if account.id != id {
                return Err(Error::ProofGenerationError(format!("Account index {i}'s id {} not the same as other's {id}", account.id)));
            }

            let mut updated_account = account.clone();
            let change = net_change[&(i as u16)];
            if change < 0 {
                if (account.balance as i128 + change) < 0 {
                    return Err(Error::ProofGenerationError(format!("Account index {i}'s balance {} not sufficient for {change}", account.balance)));
                }
            }
            updated_account.balance = (account.balance as i128 + change) as Balance;
            updated_account.refresh_randomness_for_state_change();
            updated_account_commitments.push(updated_account.commit(account_comm_key.clone())?);
            updated_accounts.push(updated_account);
        }

        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.pc_gens(),
            even_transcript,
        );
        let mut odd_prover =
            Prover::new(&account_tree_params.odd_parameters.pc_gens(), odd_transcript);

        add_to_transcript!(
            even_prover.transcript(),
            NONCE_LABEL,
            nonce
        );

        let pk_gen = account_comm_key.sk_gen();
        // Encrypt encryption public key of participants, transfer amounts and asset id
        // Optimz: Lot of the following operations can benefit from `WindowTable`
        let enc_rands = (0..(num_accounts + num_transfers + 1)).map(|_| F0::rand(rng)).collect::<Vec<_>>();
        let enc_rand_blindings = (0..(num_accounts + num_transfers + 1)).map(|_| F0::rand(rng)).collect::<Vec<_>>();
        let ct_asset_id = (enc_key_gen * enc_rands[0] + enc_gen * F0::from(asset_id)).into_affine();
        let mut ct_participants = Vec::with_capacity(num_accounts);
        for i in 0..num_accounts {
            ct_participants.push(enc_key_gen * enc_rands[1+i] + pk_gen * accounts[i].sk);
        }
        let mut ct_amounts = Vec::with_capacity(num_transfers);
        for (i, (_, _, amount)) in transfers.iter().enumerate() {
            ct_amounts.push(enc_key_gen * enc_rands[1+num_accounts+i] + enc_gen * F0::from(*amount));
        }

        let ct_participants = Projective::normalize_batch(&ct_participants);
        let ct_amounts = Projective::normalize_batch(&ct_amounts);

        let ct_amounts = transfers.iter().enumerate().map(|(i, (from , to, _))| (*from, *to, ct_amounts[i])).collect::<Vec<_>>();

        add_to_transcript!(
            even_prover.transcript(),
            CT_ASSET_ID_LABEL,
            &ct_asset_id
        );
        println!("c0 {:?}", even_prover.transcript().challenge_scalar::<F0>(b"xx"));

        for i in 0..num_accounts {
            add_to_transcript!(
                even_prover.transcript(),
                UPDATED_ACCOUNT_COMMITMENT_LABEL,
                &updated_account_commitments[i],
                CT_PARTY_LABEL,
                &ct_participants[i]
            );
        }
        for i in 0..num_transfers {
            add_to_transcript!(
                even_prover.transcript(),
                CT_AMOUNT_LABEL,
                &ct_amounts[i]
            );
        }

        println!("c1 {:?}", even_prover.transcript().challenge_scalar::<F0>(b"xx"));

        let mut nullifiers = Vec::with_capacity(num_accounts);

        for i in 0..num_accounts {
            nullifiers.push(accounts[i].nullifier(&account_comm_key));
        }

        // Batch the curve tree operations for all accounts
        let mut re_randomized_paths = Vec::with_capacity(leaf_path_accounts.len());
        let mut rerandomized_leaves_and_randomizers = Vec::with_capacity(num_accounts);

        for leaf_path in leaf_path_accounts.iter() {
            // TODO: This could use the common root batch proving
            let (re_randomized_path, randomizers_of_leaves) = leaf_path
                .batched_select_and_rerandomize_prover_gadget(
                    &mut even_prover,
                    &mut odd_prover,
                    account_tree_params,
                    rng,
                )?;

            add_to_transcript!(
                even_prover.transcript(),
                RE_RANDOMIZED_PATH_LABEL,
                re_randomized_path
            );

            let rerandomized_leaves = re_randomized_path.get_rerandomized_leaves();
            rerandomized_leaves_and_randomizers.append(
                &mut (rerandomized_leaves
                    .into_iter()
                    .zip(randomizers_of_leaves)
                    .map(|(l, r)| (l, r))
                    .collect::<Vec<_>>()),
            );
            re_randomized_paths.push(re_randomized_path);
        }

        println!("c1 {:?}", even_prover.transcript().challenge_scalar::<F0>(b"xx"));

        debug_assert!(rerandomized_leaves_and_randomizers.len() == num_accounts);

        let mut asset_id_blinding = F0::rand(rng);
        let mut id_blinding = F0::rand(rng);
        let mut sk_blindings = Vec::with_capacity(num_accounts);
        let mut counter_blindings = Vec::with_capacity(num_accounts);
        let mut old_balance_blindings = Vec::with_capacity(num_accounts);
        let mut new_balance_blindings = Vec::with_capacity(num_accounts);
        let mut initial_rho_blindings = Vec::with_capacity(num_accounts);
        let mut old_rho_blindings = Vec::with_capacity(num_accounts);
        let mut new_rho_blindings = Vec::with_capacity(num_accounts);
        let mut old_randomness_blindings = Vec::with_capacity(num_accounts);
        let mut new_randomness_blindings = Vec::with_capacity(num_accounts);
        for _ in 0..num_accounts {
            sk_blindings.push(F0::rand(rng));
            counter_blindings.push(F0::rand(rng));
            old_balance_blindings.push(F0::rand(rng));
            new_balance_blindings.push(F0::rand(rng));
            initial_rho_blindings.push(F0::rand(rng));
            old_rho_blindings.push(F0::rand(rng));
            new_rho_blindings.push(F0::rand(rng));
            old_randomness_blindings.push(F0::rand(rng));
            new_randomness_blindings.push(F0::rand(rng));
        }

        let mut amount_blindings = Vec::with_capacity(num_transfers);
        for _ in 0..num_transfers {
            amount_blindings.push(F0::rand(rng));
        }

        // Commit the following in a Bulletproof commitment in the following order
        // - 5 values for randomness relations (rho, rho_i, rho_{i+1}, s_i, s_{i+1}) per account
        // - 2 values (old and new balance) per account
        // - 1 value (amount) per transfer
        // like this [rho_0, rho_{0,i}, rho_{0,i+1}, s_{0,i}, s_{0,i+1}, rho_1, rho_{1,i}, ... bal_{0,i}, bal_{0,i+1}, bal_{1,i}, bal_{1,i+1}, ... amount_0, amount_1, ...]
        // In Bulletproof, prove that
        // - randomness relations hold for each account
        // - For each account which was a sender in any transfer, its balance is non-negative
        // - Each amount is bounded
        let comm_bp_blinding = F0::rand(rng);
        let mut bp_wits = vec![F0::zero(); 7*num_accounts + num_transfers];
        for i in 0..num_accounts {
            bp_wits[i*5] = accounts[i].rho;
            bp_wits[i*5 + 1] = accounts[i].current_rho;
            bp_wits[i*5 + 2] = updated_accounts[i].current_rho;
            bp_wits[i*5 + 3] = accounts[i].randomness;
            bp_wits[i*5 + 4] = updated_accounts[i].randomness;
            bp_wits[num_accounts*5 + i*2 + 0] = accounts[i].balance.into();
            bp_wits[num_accounts*5 + i*2 + 1] = updated_accounts[i].balance.into();
        }
        for i in 0..num_transfers {
            bp_wits[7*num_accounts + i] = transfers[i].2.into();
        }
        let (comm_bp, mut vars) = even_prover.commit_vec(&bp_wits, comm_bp_blinding, &account_tree_params.even_parameters.bp_gens());

        Zeroize::zeroize(&mut bp_wits);

        for rand_vars in vars.drain(..5*num_accounts).chunks(5).into_iter() {
            enforce_constraints_for_randomness_relations(&mut even_prover, rand_vars.collect());
        }

        // Enforce
        // - new balance is consistent with old balance and all transfer amounts to and from
        // - range proof on new balance of any account whose balance was decreased, i.e. was a sender in any transfer
        // - sum of old balances = sum of new balances
        let mut total_old = LinearCombination::default();
        let mut total_new = LinearCombination::default();
        // Since 5*num_accounts vars have already been drained above
        let amount_vars = vars[2*num_accounts..].to_vec();

        for (i, balance_vars) in vars.drain(0..2*num_accounts).chunks(2).into_iter().enumerate() {
            let mut old_bal = LinearCombination::default();
            let mut new_bal = LinearCombination::default();
            for (j, var) in balance_vars.into_iter().enumerate() {
                if j == 0 {
                    old_bal = var.into();
                } else {
                    new_bal = var.into();
                }
            }

            let mut is_sender = false;
            let mut change = LinearCombination::default();
            // Enforce correct balance change
            for (j, (from, to, _)) in transfers.iter().enumerate() {
                if i == *from as usize {
                    is_sender = true;
                    change = change - amount_vars[j];
                } else if i == *to as usize {
                    change = change + amount_vars[j];
                }
            }
            even_prover.constrain(old_bal.clone() + change - new_bal.clone());

            // Enforce range proof on sender's new balance
            if is_sender {
                range_proof(
                    &mut even_prover,
                    new_bal.clone().into(),
                    Some(updated_accounts[i].balance.into()),
                    BALANCE_BITS.into(),
                )?;
            }

            total_old = total_old + old_bal;
            total_new = total_new + new_bal;
        }

        // sum of old balances = sum of new balances
        even_prover.constrain(total_old - total_new);

        // Enforce bounds on all transfer amounts
        for (i, amount_var) in amount_vars.into_iter().enumerate() {
            range_proof(
                &mut even_prover,
                amount_var.into(),
                Some(transfers[i].2.into()),
                BALANCE_BITS.into(),
            )?;
        }

        let leaf_comm_key = account_comm_key.as_gens_with_blinding(account_tree_params.even_parameters.pc_gens().B_blinding);
        let acc_comm_key = account_comm_key.as_gens();
        let pk_gen = account_comm_key.sk_gen();
        let null_gen = account_comm_key.current_rho_gen();

        let mut t_r_leaf = Vec::with_capacity(num_accounts);
        let mut t_acc_new = Vec::with_capacity(num_accounts);
        let mut t_null = Vec::with_capacity(num_accounts);
        let mut t_enc_pk = Vec::with_capacity(num_accounts);
        for i in 0..num_accounts {
            t_r_leaf.push(SchnorrCommitment::new(
                &leaf_comm_key,
                vec![
                    sk_blindings[i],
                    old_balance_blindings[i],
                    counter_blindings[i],
                    asset_id_blinding,
                    initial_rho_blindings[i],
                    old_rho_blindings[i],
                    old_randomness_blindings[i],
                    id_blinding,
                    F0::rand(rng),
                ]
            ));

            t_acc_new.push(SchnorrCommitment::new(
                &acc_comm_key,
                vec![
                    sk_blindings[i],
                    new_balance_blindings[i],
                    counter_blindings[i],
                    asset_id_blinding,
                    initial_rho_blindings[i],
                    new_rho_blindings[i],
                    new_randomness_blindings[i],
                    id_blinding,
                ]
            ));

            t_null.push(PokDiscreteLogProtocol::init(
                accounts[i].current_rho, old_rho_blindings[i], &null_gen
            ));

            t_enc_pk.push(PokPedersenCommitmentProtocol::init(
                enc_rands[1+i],
                enc_rand_blindings[i+1],
                &enc_key_gen,
                accounts[i].sk,
                sk_blindings[i],
                &pk_gen,
            ));
        }

        let t_enc_at = PokPedersenCommitmentProtocol::init(
            enc_rands[0],
            enc_rand_blindings[0],
            &enc_key_gen,
            asset_id.into(),
            asset_id_blinding,
            &enc_gen,
        );

        let mut t_enc_amounts = Vec::with_capacity(num_transfers);
        for i in 0..num_transfers {
            t_enc_amounts.push(PokPedersenCommitmentProtocol::init(
                enc_rands[1+num_accounts+i],
                enc_rand_blindings[1+num_accounts+i],
                &enc_key_gen,
                transfers[i].2.into(),
                amount_blindings[i],
                &enc_gen,
            ));
        }

        let mut bp_gens = Vec::with_capacity(1 + 7*num_accounts + num_transfers);
        bp_gens.push(account_tree_params.even_parameters.pc_gens().B_blinding);
        let mut t_comm_bp_blindings = vec![F0::zero(); 1 + 7*num_accounts + num_transfers];
        t_comm_bp_blindings[0] = F0::rand(rng);

        let mut gens_iter = account_tree_params.even_parameters.bp_gens.share(0).G((7*num_accounts + num_transfers) as u32).copied();
        for i in 0..num_accounts {
            t_comm_bp_blindings[1 + i*5 + 0] = initial_rho_blindings[i];
            t_comm_bp_blindings[1 + i*5 + 1] = old_rho_blindings[i];
            t_comm_bp_blindings[1 + i*5 + 2] = new_rho_blindings[i];
            t_comm_bp_blindings[1 + i*5 + 3] = old_randomness_blindings[i];
            t_comm_bp_blindings[1 + i*5 + 4] = new_randomness_blindings[i];

            t_comm_bp_blindings[1 + num_accounts*5 + i*2 + 0] = old_balance_blindings[i];
            t_comm_bp_blindings[1 + num_accounts*5 + i*2 + 1] = new_balance_blindings[i];

            for _ in 0..7 {
                bp_gens.push(gens_iter.next().unwrap());
            }
        }

        for i in 0..num_transfers {
            t_comm_bp_blindings[1 + num_accounts*7 + i] = amount_blindings[i];
            bp_gens.push(gens_iter.next().unwrap());
        }

        let t_comm_bp = SchnorrCommitment::new(&bp_gens, t_comm_bp_blindings);

        let mut transcript = even_prover.transcript();

        for i in 0..num_accounts {
            t_r_leaf[i].challenge_contribution(&mut transcript)?;
            t_acc_new[i].challenge_contribution(&mut transcript)?;
            t_null[i].challenge_contribution(&null_gen, &nullifiers[i], &mut transcript)?;
            t_enc_pk[i].challenge_contribution(&enc_key_gen, &pk_gen, &ct_participants[i], &mut transcript)?;
        }

        t_enc_at.challenge_contribution(&enc_key_gen, &enc_gen, &ct_asset_id, &mut transcript)?;

        for i in 0..num_transfers {
            t_enc_amounts[i].challenge_contribution(&enc_key_gen, &enc_gen, &ct_amounts[i].2, &mut transcript)?;
        }

        comm_bp.serialize_compressed(&mut transcript)?;
        t_comm_bp.challenge_contribution(&mut transcript)?;

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        println!("prover challenge: {}", challenge);

        let mut resp_leaf = Vec::with_capacity(num_accounts);
        let mut resp_acc_new = Vec::with_capacity(num_accounts);
        let mut resp_null = Vec::with_capacity(num_accounts);
        let mut resp_enc_pk = Vec::with_capacity(num_accounts);

        for (i, (t_null, t_enc_pk)) in t_null.into_iter().zip(t_enc_pk.into_iter()).enumerate() {
            let mut w = BTreeMap::new();
            w.insert(0, accounts[i].sk);
            w.insert(1, accounts[i].balance.into());
            w.insert(2, accounts[i].counter.into());
            w.insert(4, accounts[i].rho);
            w.insert(5, accounts[i].current_rho);
            w.insert(6, accounts[i].randomness);
            w.insert(8, rerandomized_leaves_and_randomizers[i].1);
            // id is included only for first leaf as rest of them will have same id
            if i == 0 {
                w.insert(7, accounts[i].id);
            }
            resp_leaf.push(t_r_leaf[i].partial_response(w, &challenge)?);

            let mut w = BTreeMap::new();
            w.insert(1, updated_accounts[i].balance.into());
            w.insert(5, updated_accounts[i].current_rho);
            w.insert(6, updated_accounts[i].randomness);
            resp_acc_new.push(t_acc_new[i].partial_response(w, &challenge)?);

            resp_null.push(t_null.gen_partial_proof());

            resp_enc_pk.push(t_enc_pk.gen_partial1_proof(&challenge));
        }

        let resp_enc_at = t_enc_at.gen_proof(&challenge);

        let mut resp_enc_amounts = Vec::with_capacity(num_transfers);
        for t_enc_amount in t_enc_amounts {
            resp_enc_amounts.push(t_enc_amount.gen_proof(&challenge));
        }

        let mut w = BTreeMap::new();
        w.insert(0, comm_bp_blinding);
        let resp_comm_bp = t_comm_bp.partial_response(w, &challenge)?;

        let ciphertext = PortfolioMoveCiphertext {
            ct_asset_id,
            ct_participants,
            ct_amounts
        };

        let (even_proof, odd_proof) =
            prove_with_rng(even_prover, odd_prover, &account_tree_params.even_parameters.bp_gens(), &account_tree_params.odd_parameters.bp_gens(), rng)?;

        Ok((
            Self {
                r1cs_proof: Some(BPProof {
                    even_proof, odd_proof
                }),
                re_randomized_paths_accounts: re_randomized_paths,
                t_r_leaves_acc: t_r_leaf.into_iter().map(|t| t.t).collect(),
                t_acc_new: t_acc_new.into_iter().map(|t| t.t).collect(),
                comm_bp,
                t_comm_bp: t_comm_bp.t,
                resp_leaves_acc: resp_leaf,
                resp_enc_asset_id: resp_enc_at,
                resp_acc_new,
                resp_null,
                resp_enc_pk,
                resp_enc_amounts,
                resp_comm_bp
            },
            ciphertext,
            updated_accounts,
            updated_account_commitments,
            nullifiers,
        ))
    }

    pub fn verify<R: CryptoRngCore>(
        &self,
        ciphertext: PortfolioMoveCiphertext<Affine<G0>>,
        account_tree_root: &Root<L_ACC, M_ACC, G0, G1>,
        asset_tree_root: &Root<L_ASS, M_ASS, G1, G0>,
        updated_account_commitments: Vec<AccountStateCommitment<Affine<G0>>>,
        nullifiers: Vec<Affine<G0>>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParameters<G0, G1>,
        asset_comm_params: &AssetCommitmentParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        enc_key_gen: Affine<G0>,
        enc_gen: Affine<G0>,
        rng: &mut R,
    ) -> Result<()> {
        // TODO: Check all sigma protocols have required number of responses
        if updated_account_commitments.len() != nullifiers.len() {
            return Err(Error::ProofVerificationError("Need same number of account commitments and nullifiers".to_string()));
        }
        if updated_account_commitments.len() != ciphertext.ct_participants.len() {
            return Err(Error::ProofVerificationError("Need same number of account commitments and encryption key ciphertexts".to_string()));
        }

        let num_accounts = updated_account_commitments.len();
        let num_transfers = ciphertext.ct_amounts.len();

        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut even_verifier = Verifier::new(even_transcript);
        let mut odd_verifier = Verifier::new(odd_transcript);

        add_to_transcript!(
            even_verifier.transcript(),
            NONCE_LABEL,
            nonce,
        );

        add_to_transcript!(
            even_verifier.transcript(),
            CT_ASSET_ID_LABEL,
            &ciphertext.ct_asset_id
        );
        println!("c0 {:?}", even_verifier.transcript().challenge_scalar::<F0>(b"xx"));

        for i in 0..num_accounts {
            add_to_transcript!(
                even_verifier.transcript(),
                UPDATED_ACCOUNT_COMMITMENT_LABEL,
                &updated_account_commitments[i],
                CT_PARTY_LABEL,
                &ciphertext.ct_participants[i]
            );
        }
        for i in 0..num_transfers {
            add_to_transcript!(
                even_verifier.transcript(),
                CT_AMOUNT_LABEL,
                &ciphertext.ct_amounts[i]
            );
        }

        println!("c1 {:?}", even_verifier.transcript().challenge_scalar::<F0>(b"xx"));

        let mut rerandomized_leaves = Vec::with_capacity(num_accounts);
        for re_randomized_path in &self.re_randomized_paths_accounts {
            re_randomized_path.batched_select_and_rerandomize_verifier_gadget(
                account_tree_root,
                &mut even_verifier,
                &mut odd_verifier,
                account_tree_params,
            )?;

            add_to_transcript!(
                even_verifier.transcript(),
                RE_RANDOMIZED_PATH_LABEL,
                re_randomized_path
            );

            rerandomized_leaves.extend(re_randomized_path.get_rerandomized_leaves());
        }

        println!("c2 {:?}", even_verifier.transcript().challenge_scalar::<F0>(b"xx"));

        debug_assert!(rerandomized_leaves.len() == num_accounts);

        let mut vars = even_verifier.commit_vec(7*num_accounts + num_transfers, self.comm_bp);

        for rand_vars in vars.drain(..5*num_accounts).chunks(5).into_iter() {
            enforce_constraints_for_randomness_relations(&mut even_verifier, rand_vars.collect());
        }

        let mut total_old = LinearCombination::default();
        let mut total_new = LinearCombination::default();
        // Since 5*num_accounts vars have already been drained above
        let amount_vars = vars[2*num_accounts..].to_vec();

        for (i, balance_vars) in vars.drain(0..2*num_accounts).chunks(2).into_iter().enumerate() {
            let mut old_bal = LinearCombination::default();
            let mut new_bal = LinearCombination::default();
            for (j, var) in balance_vars.into_iter().enumerate() {
                if j == 0 {
                    old_bal = var.into();
                } else {
                    new_bal = var.into();
                }
            }

            let mut is_sender = false;
            let mut change = LinearCombination::default();
            // Enforce correct balance change
            for (j, (from, to, _)) in ciphertext.ct_amounts.iter().enumerate() {
                if i == *from as usize {
                    is_sender = true;
                    change = change - amount_vars[j];
                } else if i == *to as usize {
                    change = change + amount_vars[j];
                }
            }
            even_verifier.constrain(old_bal.clone() + change - new_bal.clone());

            // Enforce range proof on sender's new balance
            if is_sender {
                range_proof(
                    &mut even_verifier,
                    new_bal.clone().into(),
                    None,
                    BALANCE_BITS.into(),
                )?;
            }

            total_old = total_old + old_bal;
            total_new = total_new + new_bal;
        }

        // sum of old balances = sum of new balances
        even_verifier.constrain(total_old - total_new);

        // Enforce bounds on all transfer amounts
        for (_, amount_var) in amount_vars.into_iter().enumerate() {
            range_proof(
                &mut even_verifier,
                amount_var.into(),
                None,
                BALANCE_BITS.into(),
            )?;
        }

        let leaf_comm_key = account_comm_key.as_gens_with_blinding(account_tree_params.even_parameters.pc_gens().B_blinding);
        let acc_comm_key = account_comm_key.as_gens();
        let pk_gen = account_comm_key.sk_gen();
        let null_gen = account_comm_key.current_rho_gen();

        let mut transcript = even_verifier.transcript();

        for i in 0..num_accounts {
            self.t_r_leaves_acc[i].serialize_compressed(&mut transcript)?;
            self.t_acc_new[i].serialize_compressed(&mut transcript)?;
            self.resp_null[i].challenge_contribution(&null_gen, &nullifiers[i], &mut transcript)?;
            self.resp_enc_pk[i].challenge_contribution(&enc_key_gen, &pk_gen, &ciphertext.ct_participants[i], &mut transcript)?;
        }

        self.resp_enc_asset_id.challenge_contribution(&enc_key_gen, &enc_gen, &ciphertext.ct_asset_id, &mut transcript)?;

        for i in 0..num_transfers {
            self.resp_enc_amounts[i].challenge_contribution(&enc_key_gen, &enc_gen, &ciphertext.ct_amounts[i].2, &mut transcript)?;
        }

        self.comm_bp.serialize_compressed(&mut transcript)?;
        self.t_comm_bp.serialize_compressed(&mut transcript)?;

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        println!("verifier challenge: {}", challenge);

        if !self.resp_enc_asset_id.verify(
            &ciphertext.ct_asset_id,
            &enc_key_gen,
            &enc_gen,
            &challenge,
        ) {
            return Err(Error::ProofVerificationError("Encrypted asset-id verification failed".to_string(), ));
        }

        for i in 0..num_accounts {
            let mut missing_responses = BTreeMap::new();
            if i > 0 {
                // Insert response for id
                missing_responses.insert(7, self.resp_leaves_acc[0].responses[&7]);
            }
            missing_responses.insert(3, self.resp_enc_asset_id.response2);
            self.resp_leaves_acc[i].is_valid(
                &leaf_comm_key,
                &rerandomized_leaves[i],
                &self.t_r_leaves_acc[i],
                &challenge,
                missing_responses
            )?;

            let mut missing_responses = BTreeMap::new();
            missing_responses.insert(0, self.resp_leaves_acc[i].responses[&0]);
            missing_responses.insert(2, self.resp_leaves_acc[i].responses[&2]);
            missing_responses.insert(3, self.resp_enc_asset_id.response2);
            missing_responses.insert(4, self.resp_leaves_acc[i].responses[&4]);
            missing_responses.insert(7, self.resp_leaves_acc[0].responses[&7]);

            self.resp_acc_new[i].is_valid(
                &acc_comm_key,
                &updated_account_commitments[i].0,
                &self.t_acc_new[i],
                &challenge,
                missing_responses
            )?;

            if !self.resp_null[i].verify(
                &nullifiers[i],
                &null_gen,
                &challenge,
                &self.resp_leaves_acc[i].responses[&5]
            ) {
                return Err(Error::ProofVerificationError(format!("Nullifier verification failed for account index {i}")));
            }

            if !self.resp_enc_pk[i].verify(
                &ciphertext.ct_participants[i],
                &enc_key_gen,
                &pk_gen,
                &challenge,
                &self.resp_leaves_acc[i].responses[&0]
            ) {
                return Err(Error::ProofVerificationError(format!("Encrypted public key verification failed for account index {i}")));
            }
        }

        for i in 0..num_transfers {
            if !self.resp_enc_amounts[i].verify(
                &ciphertext.ct_amounts[i].2,
                &enc_key_gen,
                &enc_gen,
                &challenge,
            ) {
                return Err(Error::ProofVerificationError(format!("Amount encryption failed for transfer index {i}")));
            }
        }

        let mut missing_responses = BTreeMap::new();
        let mut gens_iter = account_tree_params.even_parameters.bp_gens.share(0).G((7*num_accounts + num_transfers) as u32).copied();
        let mut bp_gens = Vec::with_capacity(1 + 7*num_accounts + num_transfers);
        bp_gens.push(account_tree_params.even_parameters.pc_gens().B_blinding);
        for i in 0..num_accounts {
            missing_responses.insert(1 + i*5 + 0, self.resp_leaves_acc[i].responses[&4]);
            missing_responses.insert(1 + i*5 + 1, self.resp_leaves_acc[i].responses[&5]);
            missing_responses.insert(1 + i*5 + 2, self.resp_acc_new[i].responses[&5]);
            missing_responses.insert(1 + i*5 + 3, self.resp_leaves_acc[i].responses[&6]);
            missing_responses.insert(1 + i*5 + 4, self.resp_acc_new[i].responses[&6]);

            missing_responses.insert(1 + num_accounts*5 + i*2 + 0, self.resp_leaves_acc[i].responses[&1]);
            missing_responses.insert(1 + num_accounts*5 + i*2 + 1, self.resp_acc_new[i].responses[&1]);

            for _ in 0..7 {
                bp_gens.push(gens_iter.next().unwrap());
            }
        }
        for i in 0..num_transfers {
            missing_responses.insert(1 + num_accounts*7 + i, self.resp_enc_amounts[i].response2);
            bp_gens.push(gens_iter.next().unwrap());
        }
        self.resp_comm_bp.is_valid(
            &bp_gens,
            &self.comm_bp,
            &self.t_comm_bp,
            &challenge,
            missing_responses
        )?;

        let r1cs_proof = self
            .r1cs_proof
            .as_ref()
            .ok_or_else(|| Error::ProofVerificationError("R1CS proof is missing".to_string()))?;

        Ok(verify_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            &account_tree_params,
            rng,
        )?)
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account::tests::{setup_asset_and_account_params, setup_gens};
    use crate::account::state_transition_multi::tests::get_batched_tree_with_account_comms;
    use crate::account::{
        AccountCommitmentKeyTrait, AccountState
    };
    use crate::account_registration::tests::new_account;
    use crate::keys::{keygen_enc, keygen_sig};
    use crate::leg::{AssetCommitmentParams, AssetData};
    use ark_std::UniformRand;
    use blake2::Blake2b512;
    use curve_tree_relations::curve_tree::CurveTree;
    use rand::thread_rng;
    use std::time::Instant;
    use ark_ff::Field;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;

    type PallasFr = ark_pallas::Fr;
    type PallasA = Affine<ark_pallas::PallasConfig>;

    #[test]
    fn test_single_sender_multi_receiver() {
        // Funds moved from a single account to several others
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 17;
        const L: usize = 512;
        const ASSET_TREE_M: usize = 4;
        const ACCOUNT_TREE_M: usize = 4;

        let num_receivers = 1;
        let total_accounts = num_receivers + 1;
        let asset_tree_height = 3;
        let transfer_amount = 100;

        // Setup parameters
        let (
            account_tree_params,
            asset_tree_params,
            _asset_comm_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
        ) = setup_asset_and_account_params::<NUM_GENS>();

        let num_auditors = 2;
        let num_mediators = 1;

        let asset_comm_params = AssetCommitmentParams::new(
            b"asset-comm-params",
            num_auditors + num_mediators,
            &account_tree_params.odd_parameters.bp_gens(),
        );

        // Setup auditor keys
        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity((num_auditors + num_mediators) as usize);
        keys.extend(keys_auditor.iter().map(|(_, k)| (true, k.0)));
        keys.extend(keys_mediator.iter().map(|(_, k)| (false, k.0)));

        // Create asset data (all accounts use same asset)
        let asset_id = 1u32;
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();

        // Create asset tree with the asset commitment
        let asset_commitments = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, ASSET_TREE_M, VestaParameters, PallasParameters>::from_leaves(
            &asset_commitments,
            &asset_tree_params,
            Some(asset_tree_height),
        );
        let asset_tree_root = asset_tree.root_node();
        
        // Get asset path (single asset at index 0)
        let asset_path = asset_tree.get_paths_to_leaves(&[0]).unwrap();

        // Create accounts - all with same asset_id and id but different keys
        let id = PallasFr::rand(&mut rng);
        let mut accounts = Vec::with_capacity(total_accounts);
        let mut account_enc_keys = Vec::with_capacity(total_accounts);

        // Sender account (index 0)
        let (sk_sender, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (_, pk_sender_e) = keygen_enc(&mut rng, enc_key_gen);
        let (mut sender_account, _, _) = new_account(&mut rng, asset_id, sk_sender, id);
        sender_account.balance = transfer_amount * num_receivers as u64 + 1000; // Ensure sufficient balance
        accounts.push(sender_account);
        account_enc_keys.push(pk_sender_e.0);

        // Receiver accounts (indices 1..total_accounts)
        for _ in 0..num_receivers {
            let (sk_receiver, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let (_, pk_receiver_e) = keygen_enc(&mut rng, enc_key_gen);
            let (mut receiver_account, _, _) = new_account(&mut rng, asset_id, sk_receiver, id);
            receiver_account.balance = 100; // Some initial balance
            accounts.push(receiver_account);
            account_enc_keys.push(pk_receiver_e.0);
        }

        // Create account tree with all accounts
        let account_tree = get_batched_tree_with_account_comms::<L, ACCOUNT_TREE_M>(
            accounts.iter().collect(),
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();
        let account_tree_root = account_tree.root_node();

        // Get account paths in batches
        let mut account_paths = Vec::new();
        for chunk in (0..total_accounts).collect::<Vec<_>>().chunks(ACCOUNT_TREE_M) {
            let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
            let path = account_tree.get_paths_to_leaves(&indices).unwrap();
            account_paths.push(path);
        }

        // Create transfers: sender (0) sends to each receiver (1..total_accounts)
        let mut transfers = Vec::new();
        for receiver_idx in 1..total_accounts {
            transfers.push((0u16, receiver_idx as u16, transfer_amount));
        }

        let nonce = b"test_nonce";

        let (proof, ciphertext, updated_accounts, updated_account_comms, nullifiers) = PortfolioMoveProof::new(
            &mut rng,
            accounts.clone(),
            account_enc_keys,
            transfers.clone(),
            account_paths,
            &account_tree_root,
            asset_path,
            &asset_tree_root,
            nonce,
            &account_tree_params,
            &asset_comm_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        assert_eq!(updated_accounts[0].balance, accounts[0].balance - (num_receivers as u64 * transfer_amount));
        for i in 1..total_accounts {
            assert_eq!(updated_accounts[i].balance, accounts[i].balance + transfer_amount);
        }
        for i in 0..total_accounts {
            assert_eq!(accounts[i].sk, updated_accounts[i].sk);
            assert_eq!(accounts[i].counter, updated_accounts[i].counter);
            assert_eq!(accounts[i].asset_id, updated_accounts[i].asset_id);
            assert_eq!(accounts[i].id, updated_accounts[i].id);
            assert_eq!(accounts[i].rho, updated_accounts[i].rho);
            assert_eq!(accounts[i].rho * accounts[i].current_rho, updated_accounts[i].current_rho);
            assert_eq!(accounts[i].randomness.square(), updated_accounts[i].randomness);
            assert_eq!(updated_accounts[i].commit(account_comm_key.clone()).unwrap(), updated_account_comms[i]);
        }
        for i in 0..transfers.len() {
            assert_eq!(transfers[i].0, ciphertext.ct_amounts[i].0);
            assert_eq!(transfers[i].1, ciphertext.ct_amounts[i].1);
        }

        proof.verify(
            ciphertext,
            &account_tree_root,
            &asset_tree_root,
            updated_account_comms,
            nullifiers,
            nonce,
            &account_tree_params,
            &asset_comm_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            &mut rng,
        )
        .unwrap();
    }

    #[test]
    fn test_multi_sender_single_receiver() {
        // Funds moved from several accounts to a single account
        let mut rng = thread_rng();

        const NUM_GENS: usize = 1 << 17;
        const L: usize = 512;
        const ASSET_TREE_M: usize = 4;
        const ACCOUNT_TREE_M: usize = 4;

        let num_senders = 2;
        let total_accounts = num_senders + 1;
        let asset_tree_height = 3;
        let transfer_amount = 100;

        // Setup parameters
        let (
            account_tree_params,
            asset_tree_params,
            _asset_comm_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
        ) = setup_asset_and_account_params::<NUM_GENS>();

        let num_auditors = 2;
        let num_mediators = 1;

        let asset_comm_params = AssetCommitmentParams::new(
            b"asset-comm-params",
            num_auditors + num_mediators,
            &account_tree_params.odd_parameters.bp_gens(),
        );

        // Setup auditor keys
        let keys_auditor = (0..num_auditors)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();
        let keys_mediator = (0..num_mediators)
            .map(|_| keygen_enc(&mut rng, enc_key_gen))
            .collect::<Vec<_>>();

        let mut keys = Vec::with_capacity((num_auditors + num_mediators) as usize);
        keys.extend(keys_auditor.iter().map(|(_, k)| (true, k.0)));
        keys.extend(keys_mediator.iter().map(|(_, k)| (false, k.0)));

        // Create asset data (all accounts use same asset)
        let asset_id = 1u32;
        let asset_data = AssetData::new(
            asset_id,
            keys.clone(),
            &asset_comm_params,
            asset_tree_params.odd_parameters.delta,
        )
        .unwrap();

        // Create asset tree with the asset commitment
        let asset_commitments = vec![asset_data.commitment];
        let asset_tree = CurveTree::<L, ASSET_TREE_M, VestaParameters, PallasParameters>::from_leaves(
            &asset_commitments,
            &asset_tree_params,
            Some(asset_tree_height),
        );
        let asset_tree_root = asset_tree.root_node();
        
        // Get asset path (single asset at index 0)
        let asset_path = asset_tree.get_paths_to_leaves(&[0]).unwrap();

        // Create accounts - all with same asset_id and id but different keys
        let id = PallasFr::rand(&mut rng);
        let mut accounts = Vec::with_capacity(total_accounts);
        let mut account_enc_keys = Vec::with_capacity(total_accounts);

        // Sender accounts (indices 0..num_senders)
        for _ in 0..num_senders {
            let (sk_sender, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let (_, pk_sender_e) = keygen_enc(&mut rng, enc_key_gen);
            let (mut sender_account, _, _) = new_account(&mut rng, asset_id, sk_sender, id);
            sender_account.balance = transfer_amount + 1000; // Ensure sufficient balance
            accounts.push(sender_account);
            account_enc_keys.push(pk_sender_e.0);
        }

        // Receiver account (index num_senders)
        let receiver_idx = num_senders;
        let (sk_receiver, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let (_, pk_receiver_e) = keygen_enc(&mut rng, enc_key_gen);
        let (mut receiver_account, _, _) = new_account(&mut rng, asset_id, sk_receiver, id);
        receiver_account.balance = 100; // Some initial balance
        accounts.push(receiver_account);
        account_enc_keys.push(pk_receiver_e.0);

        let account_tree = get_batched_tree_with_account_comms::<L, ACCOUNT_TREE_M>(
            accounts.iter().collect(),
            account_comm_key.clone(),
            &account_tree_params,
        )
        .unwrap();
        let account_tree_root = account_tree.root_node();

        // Get account paths in batches
        let mut account_paths = Vec::new();
        for chunk in (0..total_accounts).collect::<Vec<_>>().chunks(ACCOUNT_TREE_M) {
            let indices: Vec<_> = chunk.iter().map(|&i| i as u32).collect();
            let path = account_tree.get_paths_to_leaves(&indices).unwrap();
            account_paths.push(path);
        }

        // Create transfers: each sender (0..num_senders) sends to receiver (num_senders)
        let mut transfers = Vec::new();
        for sender_idx in 0..num_senders {
            transfers.push((sender_idx as u16, receiver_idx as u16, transfer_amount));
        }

        let nonce = b"test_nonce";

        let (proof, ciphertext, updated_accounts, updated_account_comms, nullifiers) = PortfolioMoveProof::new(
            &mut rng,
            accounts.clone(),
            account_enc_keys,
            transfers.clone(),
            account_paths,
            &account_tree_root,
            asset_path,
            &asset_tree_root,
            nonce,
            &account_tree_params,
            &asset_comm_params,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        for i in 0..total_accounts-1 {
            assert_eq!(updated_accounts[i].balance, accounts[i].balance - transfer_amount);
        }
        assert_eq!(updated_accounts[total_accounts-1].balance, accounts[total_accounts-1].balance + (num_senders as u64 * transfer_amount));

        for i in 0..total_accounts {
            assert_eq!(accounts[i].sk, updated_accounts[i].sk);
            assert_eq!(accounts[i].counter, updated_accounts[i].counter);
            assert_eq!(accounts[i].asset_id, updated_accounts[i].asset_id);
            assert_eq!(accounts[i].id, updated_accounts[i].id);
            assert_eq!(accounts[i].rho, updated_accounts[i].rho);
            assert_eq!(accounts[i].rho * accounts[i].current_rho, updated_accounts[i].current_rho);
            assert_eq!(accounts[i].randomness.square(), updated_accounts[i].randomness);
            assert_eq!(updated_accounts[i].commit(account_comm_key.clone()).unwrap(), updated_account_comms[i]);
        }
        for i in 0..transfers.len() {
            assert_eq!(transfers[i].0, ciphertext.ct_amounts[i].0);
            assert_eq!(transfers[i].1, ciphertext.ct_amounts[i].1);
        }

        proof.verify(
            ciphertext,
            &account_tree_root,
            &asset_tree_root,
            updated_account_comms,
            nullifiers,
            nonce,
            &account_tree_params,
            &asset_comm_params,
            account_comm_key,
            enc_key_gen,
            enc_gen,
            &mut rng,
        )
        .unwrap();
    }
}