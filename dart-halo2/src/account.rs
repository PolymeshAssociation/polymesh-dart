use crate::AffineSerializable;
use crate::error::{Error, Result};
use crate::leg::{LegEncryption, LegEncryptionRandomness};
use crate::poseidon::PoseidonParams;
use crate::types_and_constants::{TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_INSTANCE_LABEL, TXN_POB_LABEL};
use crate::utils::TranscriptWriter;
use ark_std::collections::BTreeMap;
use ark_std::collections::BTreeSet;
use ark_std::iterable::Iterable;
use ark_std::vec::Vec;
use ct_halo2::ec_chip::{Ec, PallasEc, VestaEc};
use ct_halo2::multi_layer::MultiLayerCircuit;
use ff::{Field, PrimeField};
use group::{Curve, Group};
use halo2_poseidon::{ConstantLength, Hash, P128Pow5T3, Spec};
use merlin::Transcript;
use polymesh_dart_common::{
    AssetId, Balance, MAX_AMOUNT, MAX_ASSET_ID, NullifierSkGenCounter, PendingTxnCounter,
};
use rand_core::CryptoRngCore;
use ct_halo2::tree::prover::{CurveTreeWitnessPath, SelectAndRerandomizePath};
use ct_halo2::tree::node::Root;
use ct_halo2::tree::params::{CTCircuitParams, CTProvingKey, CTVerifyingKey};
use ct_halo2::tree::sel_re_rand::{SelRerandProvingParams, SelRerandVerifyingParams};
use halo2_gadgets::utilities::lookup_range_check::LookupRangeCheckConfig;
use sigma_protocols::{
    SigmaChallengeContributor,
    discrete_log::{PokDiscreteLog, PokDiscreteLogProtocol},
    pok_generalized_pedersen::{CommitmentToRandomness, Response},
};
use halo2_proofs::circuit::Value;
use halo2_proofs::dev::MockProver;
use halo2_proofs::plonk::{create_proof, create_proof_with_given_column_blindings, get_the_only_precommitted_col_comm, Circuit};
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use sigma_protocols::discrete_log::{PokPedersenCommitment, PokPedersenCommitmentProtocol};
use crate::circuits::affirmation::{StateTransitionWithBalanceChangeCircuit, PRECOMMITTED_AMOUNT_IDX, PRECOMMITTED_FLAG_IDX, PRECOMMITTED_NEW_BALANCE_IDX, PRECOMMITTED_OLD_BALANCE_IDX};
use crate::circuits::mint::{StateTransitionCircuit, PRECOMMITTED_INITIAL_RHO_IDX, PRECOMMITTED_NEW_CURRENT_RHO_IDX, PRECOMMITTED_NEW_RANDOMNESS_IDX, PRECOMMITTED_OLD_CURRENT_RHO_IDX, PRECOMMITTED_OLD_RANDOMNESS_IDX};

pub const NUM_GENERATORS: usize = 7;

// TODO: Remove hardcoding
const LIMB_BITS: usize = 6;
const NUM_WORDS: usize = 8;

/// This trait is used to abstract over the account commitment key. It allows us to use different
/// generators for the account commitment key while still providing the same interface.
pub trait AccountCommitmentKeyTrait<G: AffineSerializable>: Clone {
    /// Returns the generator for the signing key.
    fn sk_gen(&self) -> G;

    /// Returns the generator for the balance.
    fn balance_gen(&self) -> G;

    /// Returns the generator for the pending transaction counter.
    fn counter_gen(&self) -> G;

    /// Returns the generator for the asset ID.
    fn asset_id_gen(&self) -> G;

    /// Returns the generator for the original rho value generated during registration
    fn rho_gen(&self) -> G;

    /// Returns the generator for the current rho value. This is used to generate nullifier.
    fn current_rho_gen(&self) -> G;

    /// Returns the generator for the randomness value.
    fn randomness_gen(&self) -> G;

    fn as_gens(&self) -> [G; NUM_GENERATORS] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
        ]
    }

    /// Used for re-randomized leaf
    fn as_gens_with_blinding(&self, blinding: G) -> [G; NUM_GENERATORS + 1] {
        [
            self.sk_gen(),
            self.balance_gen(),
            self.counter_gen(),
            self.asset_id_gen(),
            self.rho_gen(),
            self.current_rho_gen(),
            self.randomness_gen(),
            blinding,
        ]
    }

    /// Serialize the account commitment key to a buffer
    fn serialize_compressed(&self, buf: &mut impl ark_std::io::Write) -> ark_std::io::Result<()> {
        for generator in self.as_gens() {
            buf.write_all(generator.to_bytes().as_ref())?;
        }
        Ok(())
    }
}

impl<G: AffineSerializable> AccountCommitmentKeyTrait<G> for [G; NUM_GENERATORS] {
    fn sk_gen(&self) -> G {
        self[0]
    }

    fn balance_gen(&self) -> G {
        self[1]
    }

    fn counter_gen(&self) -> G {
        self[2]
    }

    fn asset_id_gen(&self) -> G {
        self[3]
    }

    fn rho_gen(&self) -> G {
        self[4]
    }

    fn current_rho_gen(&self) -> G {
        self[5]
    }

    fn randomness_gen(&self) -> G {
        self[6]
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct AccountState<G: AffineSerializable> {
    pub sk: G::ScalarExt,
    pub balance: Balance,
    pub counter: PendingTxnCounter,
    pub asset_id: AssetId,
    pub rho: G::ScalarExt,
    pub current_rho: G::ScalarExt,
    pub randomness: G::ScalarExt,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct AccountStateCommitment<G: AffineSerializable>(pub G);

impl<G: AffineSerializable> AccountState<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarExt,
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> Result<Self>
    where
        P128Pow5T3: Spec<G::Scalar, 3, 2>,
    {
        if asset_id > MAX_ASSET_ID {
            return Err(Error::AssetIdTooLarge(asset_id));
        }

        let combined = Self::concat_asset_id_counter(asset_id, counter);
        let rho = Hash::<_, P128Pow5T3, ConstantLength<2>, 3, 2>::init().hash([sk, combined]);

        let current_rho = rho.square();
        let randomness = G::ScalarExt::random(&mut *rng);
        Ok(Self {
            sk,
            balance: 0,
            counter: 0,
            asset_id,
            rho,
            current_rho,
            randomness,
        })
    }

    pub fn commit(
        &self,
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<AccountStateCommitment<G>> {
        let gens = account_comm_key.as_gens();
        let scalars = [
            self.sk,
            G::ScalarExt::from(self.balance),
            G::ScalarExt::from(self.counter.into()),
            G::ScalarExt::from(self.asset_id.into()),
            self.rho,
            self.current_rho,
            self.randomness,
        ];

        // TODO: Fix MSM
        let mut comm = G::CurveExt::identity();
        for (generator, scalar) in gens.iter().zip(scalars.iter()) {
            comm = comm + generator.mul(scalar);
        }

        Ok(AccountStateCommitment(comm.into()))
    }

    pub fn get_state_for_mint(&self, amount: u64) -> Result<Self> {
        if amount + self.balance > MAX_AMOUNT {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_send(&self, amount: u64) -> Result<Self> {
        if amount > self.balance {
            return Err(Error::AmountTooLarge(amount));
        }
        let mut new_state = self.clone();
        new_state.balance -= amount;
        new_state.counter += 1;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_receive(&self) -> Self {
        let mut new_state = self.clone();
        new_state.counter += 1;
        new_state.refresh_randomness_for_state_change();
        new_state
    }

    pub fn get_state_for_claiming_received(&self, amount: u64) -> Result<Self> {
        if self.counter == 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be greater than 0".to_string(),
            ));
        }
        if amount + self.balance > MAX_AMOUNT {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.counter -= 1;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_reversing_send(&self, amount: u64) -> Result<Self> {
        if self.counter == 0 {
            return Err(Error::ProofOfBalanceError(
                "Counter must be greater than 0".to_string(),
            ));
        }
        if amount + self.balance > MAX_AMOUNT {
            return Err(Error::AmountTooLarge(amount + self.balance));
        }
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.counter -= 1;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_decreasing_counter(
        &self,
        decrease_counter_by: Option<PendingTxnCounter>,
    ) -> Result<Self> {
        let decrease_counter_by = decrease_counter_by.unwrap_or(1);
        if self.counter < decrease_counter_by {
            return Err(Error::ProofOfBalanceError(
                "Counter cannot be decreased below zero".to_string(),
            ));
        }
        let mut new_state = self.clone();
        new_state.counter -= decrease_counter_by;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    /// Set rho and commitment randomness to new values. Used as each update to the account state
    /// needs these refreshed.
    pub fn refresh_randomness_for_state_change(&mut self) {
        self.current_rho = self.current_rho * self.rho;
        self.randomness = self.randomness.square();
    }

    pub fn nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        comm_key.current_rho_gen().mul(&self.current_rho).into()
    }

    pub(crate) fn initial_nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        comm_key.rho_gen().mul(&self.rho).into()
    }

    /// Append bytes of counter to bytes of asset id. `combined = asset_id || asset_id`
    /// NOTE: Assumes for correctness, that the concatenation can fit in 64 bytes
    pub(crate) fn concat_asset_id_counter(
        asset_id: AssetId,
        counter: NullifierSkGenCounter,
    ) -> G::ScalarExt {
        let combined: u64 = (asset_id as u64) << 32 | (counter as u64);
        G::ScalarExt::from(combined)
    }
}

/// This is the proof for minting assets. Report section 5.1.4, called "Mint Transaction"
/// We could register both signing and encryption keys by modifying this proof even though the encryption isn't used in account commitment.
#[derive(Clone, Debug)]
pub struct MintTxnProof<
    G0: AffineSerializable,
    G1: AffineSerializable<Base = G0::ScalarExt, ScalarExt = G0::Base>,
    const L: usize
> {
    /// This contains the old account state, but re-randomized (as re-randomized leaf)
    pub re_randomized_path: SelectAndRerandomizePath<G0, G1, L>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: Response<G0>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: Response<G0>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokDiscreteLog<G0>,
    /// Commitment to randomness and response for proving knowledge of issuer secret key using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_pk: PokDiscreteLog<G0>,
    pub resp_comm_rho_rand_halo2: Response<G0>,
    pub snark_proof_even: Vec<u8>,
    pub snark_proof_odd: Vec<u8>,
}

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    // G1: AffineSerializable<Base = G0::ScalarExt, ScalarExt = G0::Base>,
    const L: usize
> MintTxnProof<G0, G1, L> {
    /// `T` are the public key `pk_T`, generator used when creating key `pk_T` and the generator used to encrypt randomness chunk.
    /// This is intentionally kept different from the generator for randomness in account commitment to prevent anyone from
    /// learning the next nullifier
    pub fn new<
        R: CryptoRngCore,
        Ec0: Ec<Affine = G0, Base = G0::Base, Scalar = G0::ScalarExt>,
        Ec1: Ec<Affine = G1, Base = Ec0::Scalar, Scalar = Ec0::Base>,
    >(
        rng: &mut R,
        issuer_pk: G0,
        increase_bal_by: Balance,
        account: &AccountState<G0>,
        updated_account: &AccountState<G0>,
        updated_account_commitment: AccountStateCommitment<G0>,
        leaf_path: CurveTreeWitnessPath<G0, G1, L>,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_proving_key: &CTProvingKey<G0, G1>,
    ) -> Result<(Self, G0)> {
        ensure_same_accounts(account, updated_account)?;

        let mut transcript = Transcript::new(TXN_EVEN_LABEL);

        let mut extra_instance = Vec::new();
        // TODO: Serialize later
        // extra_instance.extend_from_slice(root.to_bytes().as_ref());
        // extra_instance.extend_from_slice(re_randomized_path.to_bytes().as_ref());
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(issuer_pk.to_bytes().as_ref());
        extra_instance.extend_from_slice(&account.asset_id.to_le_bytes());
        extra_instance.extend_from_slice(&increase_bal_by.to_le_bytes());
        extra_instance.extend_from_slice(updated_account_commitment.0.to_bytes().as_ref());
        // TODO: Serialize later
        // account_comm_key.serialize_compressed(&mut extra_instance)?;

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        // We don't need to check if the new balance overflows or not as the chain tracks the total supply
        // (total minted value) and ensures that it is bounded, i.e.<= MAX_AMOUNT

        // Need to prove that:
        // 1. sk, and counter are same in both old and new account commitment
        // 2. nullifier and commitment randomness are correctly formed
        // 3. sk in account commitment is the same as in the issuer's public key
        // 4. New balance = old balance + increase_bal_by

        let sk_blinding = F0::random(&mut *rng);
        let counter_blinding = F0::random(&mut *rng);
        let new_balance_blinding = F0::random(&mut *rng);
        let initial_rho_blinding = F0::random(&mut *rng);
        let old_rho_blinding = F0::random(&mut *rng);
        let new_rho_blinding = F0::random(&mut *rng);
        let old_s_blinding = F0::random(&mut *rng);
        let new_s_blinding = F0::random(&mut *rng);

        let nullifier_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();
        let nullifier = account.nullifier(&account_comm_key);

        // Schnorr commitment for proving correctness of re-randomized leaf (re-randomized account state)
        let t_r_leaf = CommitmentToRandomness::new(
            &Self::leaf_gens(&account_comm_key, sr_proving_params),
            vec![
                sk_blinding,
                new_balance_blinding,
                counter_blinding,
                initial_rho_blinding,
                old_rho_blinding,
                old_s_blinding,
                F0::random(&mut *rng),
            ],
        );

        // Schnorr commitment for proving correctness of new account state which will become new leaf
        let t_acc_new = CommitmentToRandomness::new(
            &Self::acc_new_gens(&account_comm_key),
            vec![
                sk_blinding,
                new_balance_blinding,
                counter_blinding,
                initial_rho_blinding,
                new_rho_blinding,
                new_s_blinding,
            ],
        );

        // Schnorr commitment for proving correctness of nullifier
        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, old_rho_blinding, &nullifier_gen);

        // Schnorr commitment for knowledge of secret key in public key
        let t_pk = PokDiscreteLogProtocol::init(account.sk, sk_blinding, &pk_gen);

        t_r_leaf.challenge_contribution(&mut transcript_writer)?;
        t_acc_new.challenge_contribution(&mut transcript_writer)?;
        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript_writer)?;
        t_pk.challenge_contribution(&pk_gen, &issuer_pk, &mut transcript_writer)?;

        let (
            even_layer_witnesses,
            odd_layer_witnesses,
            even_layer_public_inputs,
            odd_layer_public_inputs,
            re_randomized_path,
            re_randomization_of_leaf
        ) = leaf_path.prepare_witness::<R, Ec0, Ec1>(rng, &sr_proving_params);

        let odd_layer_circuit = StateTransitionCircuit::<G0, Ec1, L>::new(
            Value::known(account.rho),
            Value::known(account.current_rho),
            Value::known(updated_account.current_rho),
            Value::known(account.randomness),
            Value::known(updated_account.randomness),
            odd_layer_witnesses
        );

        let even_layer_circuit = MultiLayerCircuit::<Ec0, L> {
            layers: even_layer_witnesses,
        };

        let num_blindings_halo2 = ct_proving_key.even.get_vk().blinding_factors() + 2;
        let mut blinding_rows_halo2 = (0..num_blindings_halo2)
            .map(|_| G0::Scalar::random(&mut *rng))
            .collect::<Vec<_>>();
        let usable_rows = circuit_params.even.n as usize - (num_blindings_halo2 - 1);

        let mut bases_halo2 = Vec::with_capacity(5 + num_blindings_halo2);
        let mut witnesses_halo2 = Vec::with_capacity(5 + num_blindings_halo2);
        let mut blindings_halo2 = Vec::with_capacity(5 + num_blindings_halo2);

        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_INITIAL_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_CURRENT_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_CURRENT_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_RANDOMNESS_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_RANDOMNESS_IDX]);

        witnesses_halo2.push(account.rho);
        witnesses_halo2.push(account.current_rho);
        witnesses_halo2.push(updated_account.current_rho);
        witnesses_halo2.push(account.randomness);
        witnesses_halo2.push(updated_account.randomness);
        blindings_halo2.push(initial_rho_blinding);
        blindings_halo2.push(old_rho_blinding);
        blindings_halo2.push(new_rho_blinding);
        blindings_halo2.push(old_s_blinding);
        blindings_halo2.push(new_s_blinding);

        let mut halo2_transcript_even = Blake2bWrite::<_, G0, Challenge255<_>>::init(vec![]);
        // TODO: Write hash of merlin transcript into halo2_transcript using common_point

        create_proof_with_given_column_blindings(
            &circuit_params.even,
            &ct_proving_key.even,
            &[odd_layer_circuit],
            &[&[&odd_layer_public_inputs]],
            vec![Some(vec![blinding_rows_halo2.clone()])],
            &mut *rng,
            &mut halo2_transcript_even,
        )
            .unwrap();
        let snark_proof_odd = halo2_transcript_even.finalize();

        let mut halo2_transcript_odd = Blake2bWrite::<_, G1, Challenge255<_>>::init(vec![]);
        create_proof(
            &circuit_params.odd,
            &ct_proving_key.odd,
            &[even_layer_circuit],
            &[&[&even_layer_public_inputs]],
            &mut *rng,
            &mut halo2_transcript_odd,
        )
            .unwrap();
        let snark_proof_even = halo2_transcript_odd.finalize();

        for i in 0..(num_blindings_halo2 -1) {
            bases_halo2.push(circuit_params.even.g_lagrange[usable_rows+i]);
            witnesses_halo2.push(blinding_rows_halo2.remove(0));
            blindings_halo2.push(G0::Scalar::random(&mut *rng));
        }

        bases_halo2.push(circuit_params.even.w);
        witnesses_halo2.push(blinding_rows_halo2.remove(0));
        blindings_halo2.push(G0::Scalar::random(&mut *rng));

        debug_assert_eq!(blinding_rows_halo2.len(), 0);

        let mut t = Blake2bRead::<_, _, Challenge255<_>>::init(snark_proof_odd.as_slice());
        let comm_rho_rand_halo2 = get_the_only_precommitted_col_comm(ct_proving_key.even.get_vk(), &mut t).unwrap();

        let t_comm_rho_rand_halo2 = CommitmentToRandomness::new(&bases_halo2, blindings_halo2);
        t_comm_rho_rand_halo2.challenge_contribution(&mut transcript_writer)?;

        let prover_challenge = transcript_writer.generate_challenge::<G0>(TXN_CHALLENGE_LABEL);

        // TODO: Eliminate duplicate responses
        let resp_leaf = t_r_leaf.response(
            &[
                account.sk,
                F0::from(account.balance as u64),
                F0::from(account.counter as u64),
                account.rho,
                account.current_rho,
                account.randomness,
                re_randomization_of_leaf,
            ],
            &prover_challenge,
        )?;
        let resp_acc_new = t_acc_new.response(
            &[
                updated_account.sk,
                F0::from(updated_account.balance as u64),
                F0::from(updated_account.counter as u64),
                updated_account.rho,
                updated_account.current_rho,
                updated_account.randomness,
            ],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_proof(&prover_challenge);
        let resp_pk = t_pk.gen_proof(&prover_challenge);

        let resp_comm_rho_rand_halo2 = t_comm_rho_rand_halo2.response(&witnesses_halo2, &prover_challenge)?;

        Ok((
            Self {
                re_randomized_path,
                resp_leaf,
                resp_acc_new,
                resp_null,
                resp_pk,
                resp_comm_rho_rand_halo2,
                snark_proof_even,
                snark_proof_odd,
            },
            nullifier,
        ))
    }

    pub fn verify(
        &self,
        issuer_pk: G0,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: AccountStateCommitment<G0>,
        nullifier: G0,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_verifying_key: &CTVerifyingKey<G0, G1>,
    ) -> Result<()> {
        if self.resp_leaf.len() != 7 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(7, self.resp_leaf.len()))
        }
        if self.resp_acc_new.len() != 6 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(6, self.resp_acc_new.len()))
        }
        let num_blindings_halo2 = ct_verifying_key.even.blinding_factors() + 2;
        let usable_rows = circuit_params.even.n as usize - (num_blindings_halo2 - 1);
        if self.resp_comm_rho_rand_halo2.len() != (5 + num_blindings_halo2) {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(5 + num_blindings_halo2, self.resp_comm_rho_rand_halo2.len()))
        }

        let mut transcript = Transcript::new(TXN_EVEN_LABEL);

        let mut extra_instance = Vec::new();
        // TODO: Serialize later
        // extra_instance.extend_from_slice(root.to_bytes().as_ref());
        // extra_instance.extend_from_slice(self.re_randomized_path.to_bytes().as_ref());
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(issuer_pk.to_bytes().as_ref());
        extra_instance.extend_from_slice(&asset_id.to_le_bytes());
        extra_instance.extend_from_slice(&increase_bal_by.to_le_bytes());
        extra_instance.extend_from_slice(updated_account_commitment.0.to_bytes().as_ref());
        // TODO: Serialize later
        // account_comm_key.serialize_compressed(&mut extra_instance)?;

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        self.resp_leaf.challenge_contribution(
            &mut transcript_writer,
        )?;
        self.resp_acc_new.challenge_contribution(
            &mut transcript_writer,
        )?;
        self.resp_null.challenge_contribution(
            &nullifier_gen,
            &nullifier,
            &mut transcript_writer,
        )?;
        self.resp_pk
            .challenge_contribution(&pk_gen, &issuer_pk, &mut transcript_writer)?;

        let mut transcript_even = Blake2bRead::<_, _, Challenge255<_>>::init(self.snark_proof_odd.as_slice());
        let mut transcript_odd = Blake2bRead::<_, _, Challenge255<_>>::init(self.snark_proof_even.as_slice());
        let rerandomized_leaf = self.re_randomized_path.clone().select_and_rerandomize_verifier_gadget::<
            _, _, _, _
        >(
            &root, &sr_proving_params.verifying_params(),
            &circuit_params,
            &ct_verifying_key,
            &mut transcript_even, &mut transcript_odd
        ).unwrap();
        debug_assert_eq!(rerandomized_leaf, self.re_randomized_path.get_rerandomized_leaf());

        // TODO: Can't i remove this recreation of transcript
        let mut t = Blake2bRead::<_, _, Challenge255<_>>::init(self.snark_proof_odd.as_slice());
        let comm_rho_rand_halo2 = get_the_only_precommitted_col_comm(&ct_verifying_key.even, &mut t).unwrap();

        let mut bases_halo2 = Vec::with_capacity(5 + num_blindings_halo2);

        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_INITIAL_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_CURRENT_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_CURRENT_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_RANDOMNESS_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_RANDOMNESS_IDX]);

        for i in 0..(num_blindings_halo2 -1) {
            bases_halo2.push(circuit_params.even.g_lagrange[usable_rows+i]);
        }
        bases_halo2.push(circuit_params.even.w);

        self.resp_comm_rho_rand_halo2.challenge_contribution(&mut transcript_writer)?;

        let verifier_challenge = transcript_writer.generate_challenge::<G0>(TXN_CHALLENGE_LABEL);

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id as u64)).to_affine();

        let y = (self.re_randomized_path.get_rerandomized_leaf().to_curve() - asset_id_comm.to_curve()).to_affine();
        self.resp_leaf.verify(
            &Self::leaf_gens(&account_comm_key, sr_proving_params),
            &y,
            &verifier_challenge,
        )?;
        
        let y = (updated_account_commitment.0.to_curve() - asset_id_comm.to_curve()).to_affine();
        self.resp_acc_new.verify(
            &Self::acc_new_gens(&account_comm_key),
            &y,
            &verifier_challenge,
        )?;
        
        self.resp_null
            .verify(&nullifier, &nullifier_gen, &verifier_challenge)
            .map_err(|_| Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ))?;
        self.resp_pk
            .verify(&issuer_pk, &pk_gen, &verifier_challenge)
            .map_err(|_| Error::ProofVerificationError(
                "Issuer public key verification failed".to_string(),
            ))?;

        self.resp_comm_rho_rand_halo2.verify(&bases_halo2, &comm_rho_rand_halo2, &verifier_challenge)?;

        if self.resp_comm_rho_rand_halo2.s[0] != self.resp_leaf.s[3] {
            return Err(Error::ProofVerificationError(
                "Initial rho mismatch between the leaf and the one in Halo2 commitment".to_string(),
            ));
        }

        if self.resp_comm_rho_rand_halo2.s[1] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Old rho mismatch between the nullifier and the one in Halo2 commitment".to_string(),
            ));
        }

        if self.resp_comm_rho_rand_halo2.s[2] != self.resp_acc_new.s[4] {
            return Err(Error::ProofVerificationError(
                "New rho mismatch between the new account commitment and the one in Halo2 commitment"
                    .to_string(),
            ));
        }

        if self.resp_comm_rho_rand_halo2.s[3] != self.resp_leaf.s[5] {
            return Err(Error::ProofVerificationError(
                "Old randomness mismatch between the leaf and the one in Halo2 commitment".to_string(),
            ));
        }

        if self.resp_comm_rho_rand_halo2.s[4] != self.resp_acc_new.s[5] {
            return Err(Error::ProofVerificationError(
                "New randomness mismatch between the account commitment and the one in Halo2 commitment".to_string(),
            ));
        }

        Ok(())
    }

    /// Returns the generators used for the re-randomized leaf proof
    pub fn leaf_gens(account_comm_key: &impl AccountCommitmentKeyTrait<G0>, sr_proving_params: &SelRerandProvingParams<G0, G1>,) -> [G0; 7] {
        [
            account_comm_key.sk_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
            sr_proving_params.odd_level_blinding_gen
        ]
    }

    /// Returns the generators used for the new account commitment proof
    pub fn acc_new_gens(account_comm_key: &impl AccountCommitmentKeyTrait<G0>) -> [G0; 6] {
        [
            account_comm_key.sk_gen(),
            account_comm_key.balance_gen(),
            account_comm_key.counter_gen(),
            account_comm_key.rho_gen(),
            account_comm_key.current_rho_gen(),
            account_comm_key.randomness_gen(),
        ]
    }
}

/// Proof for variables that change during each account state transition
#[derive(Clone, Debug)]
pub struct StateChangeProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> {
    pub re_randomized_path: SelectAndRerandomizePath<G0, G1, L>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_leaf: Response<G0>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: Response<G0>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PokDiscreteLog<G0>,
    /// Commitment to randomness and response for proving knowledge of asset-id in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_asset_id: PokPedersenCommitment<G0>,
    /// Commitment to randomness and response for proving knowledge of secret key of the party's public key in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_pk: PokPedersenCommitment<G0>,
    pub resp_comm_halo2: Response<G0>,
    /// Commitment to randomness and response for proving knowledge of amount in the "leg" using Schnorr protocol (step 1 and 3 of Schnorr).
    pub resp_leg_amount: Option<PokPedersenCommitment<G0>>,
    pub snark_proof_even: Vec<u8>,
    pub snark_proof_odd: Vec<u8>,
}

pub struct BalanceChange {
    pub amount: Balance,
    pub has_decreased: bool,
}

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> StateChangeProof<F0, F1, G0, G1, L> {
    pub fn new<
        R: CryptoRngCore,
        Ec0: Ec<Affine = G0, Base = G0::Base, Scalar = G0::ScalarExt>,
        Ec1: Ec<Affine = G1, Base = Ec0::Scalar, Scalar = Ec0::Base>,
    >(
        rng: &mut R,
        leg_enc: LegEncryption<G0>,
        leg_enc_rand: LegEncryptionRandomness<G0::Scalar>,
        account: &AccountState<G0>,
        updated_account: &AccountState<G0>,
        updated_account_commitment: AccountStateCommitment<G0>,
        leaf_path: CurveTreeWitnessPath<G0, G1, L>,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        is_sender: bool,
        balance_change: Option<BalanceChange>,
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_proving_key: &CTProvingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<(Self, G0)> {
        ensure_same_accounts(account, updated_account)?;
        if let Some(balance_change) = &balance_change {
            if balance_change.has_decreased {
                if account.balance < updated_account.balance {
                    return Err(Error::ProofGenerationError(
                        "Balance should decrease when has_decreased is true".to_string(),
                    ));
                }
            } else {
                if account.balance > updated_account.balance {
                    return Err(Error::ProofGenerationError(
                        "Balance should increase when has_decreased is false".to_string(),
                    ));
                }
            }
        } else {
            if account.balance != updated_account.balance {
                return Err(Error::ProofGenerationError(
                    "Balance should not change when balance_change is None".to_string(),
                ));
            }
        }

        let mut transcript = Transcript::new(TXN_EVEN_LABEL);

        let mut extra_instance = Vec::new();
        // TODO: Serialize later
        // extra_instance.extend_from_slice(root.to_bytes().as_ref());
        // extra_instance.extend_from_slice(re_randomized_path.to_bytes().as_ref());
        extra_instance.extend_from_slice(nonce);

        extra_instance.extend_from_slice(updated_account_commitment.0.to_bytes().as_ref());
        // TODO: Serialize later
        // account_comm_key.serialize_compressed(&mut extra_instance)?;

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        let LegEncryptionRandomness(r_1, r_2, r_3, r_4) = leg_enc_rand;
        let r_pk = if is_sender { r_1 } else { r_2 };

        let nullifier = account.nullifier(&account_comm_key);

        // Generate blinding factors
        let sk_blinding = F0::random(&mut *rng);
        let new_counter_blinding = F0::random(&mut *rng);
        let asset_id_blinding = F0::random(&mut *rng);
        let initial_rho_blinding = F0::random(&mut *rng);
        let old_rho_blinding = F0::random(&mut *rng);
        let new_rho_blinding = F0::random(&mut *rng);
        let old_randomness_blinding = F0::random(&mut *rng);
        let new_randomness_blinding = F0::random(&mut *rng);

        let (old_balance_blinding, new_balance_blinding) = if balance_change.is_some() {
            (F0::random(&mut *rng), F0::random(&mut *rng))
        } else {
            let b = F0::random(&mut *rng);
            (b, b)
        };

        let old_bal = F0::from(account.balance);
        let new_bal = F0::from(updated_account.balance);
        let asset_id = F0::from(account.asset_id as u64);

        // Schnorr commitment for proving correctness of re-randomized leaf
        let t_r_leaf = CommitmentToRandomness::new(
            &account_comm_key.as_gens_with_blinding(sr_proving_params.odd_level_blinding_gen),
            vec![
                sk_blinding,
                old_balance_blinding,
                new_counter_blinding,
                asset_id_blinding,
                initial_rho_blinding,
                old_rho_blinding,
                old_randomness_blinding,
                F0::random(&mut *rng),
            ],
        );

        // Schnorr commitment for proving correctness of new account state
        let t_acc_new = CommitmentToRandomness::new(
            &account_comm_key.as_gens(),
            vec![
                sk_blinding,
                new_balance_blinding,
                new_counter_blinding,
                asset_id_blinding,
                initial_rho_blinding,
                new_rho_blinding,
                new_randomness_blinding,
            ],
        );

        let pk_gen = account_comm_key.sk_gen();
        let null_gen = account_comm_key.current_rho_gen();

        // Schnorr commitment for proving correctness of nullifier
        let t_null = PokDiscreteLogProtocol::init(
            account.current_rho,
            old_rho_blinding,
            &null_gen,
        );

        // Schnorr commitment for proving knowledge of asset-id in leg
        let t_leg_asset_id = PokPedersenCommitmentProtocol::init(
            r_4,
            F0::random(&mut *rng),
            &enc_key_gen,
            asset_id,
            asset_id_blinding,
            &enc_gen,
        );

        // Schnorr commitment for proving knowledge of secret key in leg
        let t_leg_pk = PokPedersenCommitmentProtocol::init(
            r_pk,
            F0::random(&mut *rng),
            &enc_key_gen,
            account.sk,
            sk_blinding,
            &pk_gen,
        );

        t_r_leaf.challenge_contribution(&mut transcript_writer)?;
        t_acc_new.challenge_contribution(&mut transcript_writer)?;
        t_null.challenge_contribution(&null_gen, &nullifier, &mut transcript_writer)?;
        t_leg_asset_id.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_asset_id,
            &mut transcript_writer,
        )?;
        t_leg_pk.challenge_contribution(
            &enc_key_gen,
            &pk_gen,
            if is_sender {
                &leg_enc.ct_s
            } else {
                &leg_enc.ct_r
            },
            &mut transcript_writer,
        )?;

        let (
            even_layer_witnesses,
            odd_layer_witnesses,
            even_layer_public_inputs,
            odd_layer_public_inputs,
            re_randomized_path,
            re_randomization_of_leaf
        ) = leaf_path.prepare_witness::<R, Ec0, Ec1>(rng, &sr_proving_params);

        let even_layer_circuit = MultiLayerCircuit::<Ec0, L> {
            layers: even_layer_witnesses,
        };

        let num_blindings_halo2 = ct_proving_key.even.get_vk().blinding_factors() + 2;
        let mut blinding_rows_halo2 = (0..num_blindings_halo2)
            .map(|_| G0::Scalar::random(&mut *rng))
            .collect::<Vec<_>>();
        let usable_rows = circuit_params.even.n as usize - (num_blindings_halo2 - 1);

        let mut bases_halo2 = Vec::with_capacity(8 + num_blindings_halo2);
        let mut witnesses_halo2 = Vec::with_capacity(8 + num_blindings_halo2);
        let mut blindings_halo2 = Vec::with_capacity(8 + num_blindings_halo2);

        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_INITIAL_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_CURRENT_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_CURRENT_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_RANDOMNESS_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_RANDOMNESS_IDX]);

        witnesses_halo2.push(account.rho);
        witnesses_halo2.push(account.current_rho);
        witnesses_halo2.push(updated_account.current_rho);
        witnesses_halo2.push(account.randomness);
        witnesses_halo2.push(updated_account.randomness);
        blindings_halo2.push(initial_rho_blinding);
        blindings_halo2.push(old_rho_blinding);
        blindings_halo2.push(new_rho_blinding);
        blindings_halo2.push(old_randomness_blinding);
        blindings_halo2.push(new_randomness_blinding);

        let mut halo2_transcript_even = Blake2bWrite::<_, G0, Challenge255<_>>::init(vec![]);
        // TODO: Write hash of merlin transcript into halo2_transcript using common_point

        let t_leg_amount = if let Some(balance_change) = balance_change {
            let amount_blinding = F0::random(&mut *rng);
            // Schnorr commitment for proving knowledge of amount used in the leg
            let amount = F0::from(balance_change.amount);
            let t_leg_amount = PokPedersenCommitmentProtocol::init(
                r_3,
                F0::random(&mut *rng),
                &enc_key_gen,
                amount,
                amount_blinding,
                &enc_gen,
            );
            t_leg_amount.challenge_contribution(
                &enc_key_gen,
                &enc_gen,
                &leg_enc.ct_amount,
                &mut transcript_writer,
            )?;

            let odd_layer_circuit = StateTransitionWithBalanceChangeCircuit::<G0, Ec1, LookupRangeCheckConfig<G0::Scalar, LIMB_BITS>, LIMB_BITS, L>::new(
                NUM_WORDS,
                Value::known(account.rho),
                Value::known(account.current_rho),
                Value::known(updated_account.current_rho),
                Value::known(account.randomness),
                Value::known(updated_account.randomness),
                Value::known(amount),
                Value::known(old_bal),
                Value::known(new_bal),
                odd_layer_witnesses
            );
            bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_BALANCE_IDX]);
            bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_AMOUNT_IDX]);
            bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_BALANCE_IDX]);

            witnesses_halo2.push(old_bal);
            witnesses_halo2.push(amount);
            witnesses_halo2.push(new_bal);
            blindings_halo2.push(old_balance_blinding);
            blindings_halo2.push(amount_blinding);
            blindings_halo2.push(new_balance_blinding);

            let flag = if balance_change.has_decreased {
                F0::ZERO
            } else {
                F0::from(2_u64)
            };

            create_proof_with_given_column_blindings(
                &circuit_params.even,
                &ct_proving_key.even,
                &[odd_layer_circuit],
                &[&[&[flag], &odd_layer_public_inputs]],
                vec![Some(vec![blinding_rows_halo2.clone()])],
                &mut *rng,
                &mut halo2_transcript_even,
            )
                .unwrap();

            Some(t_leg_amount)
        } else {
            let odd_layer_circuit = StateTransitionCircuit::<G0, Ec1, L>::new(
                Value::known(account.rho),
                Value::known(account.current_rho),
                Value::known(updated_account.current_rho),
                Value::known(account.randomness),
                Value::known(updated_account.randomness),
                odd_layer_witnesses
            );

            create_proof_with_given_column_blindings(
                &circuit_params.even,
                &ct_proving_key.even,
                &[odd_layer_circuit],
                &[&[&odd_layer_public_inputs]],
                vec![Some(vec![blinding_rows_halo2.clone()])],
                &mut *rng,
                &mut halo2_transcript_even,
            )
                .unwrap();
            None
        };

        let snark_proof_odd = halo2_transcript_even.finalize();

        let mut halo2_transcript_odd = Blake2bWrite::<_, G1, Challenge255<_>>::init(vec![]);
        create_proof(
            &circuit_params.odd,
            &ct_proving_key.odd,
            &[even_layer_circuit],
            &[&[&even_layer_public_inputs]],
            &mut *rng,
            &mut halo2_transcript_odd,
        )
            .unwrap();
        let snark_proof_even = halo2_transcript_odd.finalize();

        for i in 0..(num_blindings_halo2 -1) {
            bases_halo2.push(circuit_params.even.g_lagrange[usable_rows+i]);
            witnesses_halo2.push(blinding_rows_halo2.remove(0));
            blindings_halo2.push(G0::Scalar::random(&mut *rng));
        }

        bases_halo2.push(circuit_params.even.w);
        witnesses_halo2.push(blinding_rows_halo2.remove(0));
        blindings_halo2.push(G0::Scalar::random(&mut *rng));

        debug_assert_eq!(blinding_rows_halo2.len(), 0);

        // Schnorr commitment for proving randomness relations and balance change if needed
        let mut t = Blake2bRead::<_, _, Challenge255<_>>::init(snark_proof_odd.as_slice());
        let comm_halo2 = get_the_only_precommitted_col_comm(ct_proving_key.even.get_vk(), &mut t).unwrap();

        let t_comm_halo2 = CommitmentToRandomness::new(&bases_halo2, blindings_halo2);
        t_comm_halo2.challenge_contribution(&mut transcript_writer)?;

        let prover_challenge = transcript_writer.generate_challenge::<G0>(TXN_CHALLENGE_LABEL);

        // TODO: Eliminate duplicate responses
        let resp_leaf = t_r_leaf.response(
            &[
                account.sk,
                old_bal,
                F0::from(account.counter as u64),
                asset_id,
                account.rho,
                account.current_rho,
                account.randomness,
                re_randomization_of_leaf,
            ],
            &prover_challenge,
        )?;
        let resp_acc_new = t_acc_new.response(
            &[
                updated_account.sk,
                new_bal,
                F0::from(updated_account.counter as u64),
                asset_id,
                updated_account.rho,
                updated_account.current_rho,
                updated_account.randomness,
            ],
            &prover_challenge,
        )?;
        let resp_null = t_null.gen_proof(&prover_challenge);
        let resp_leg_asset_id = t_leg_asset_id.clone().gen_proof(&prover_challenge);
        let resp_leg_pk = t_leg_pk.clone().gen_proof(&prover_challenge);

        let resp_leg_amount = t_leg_amount.map(|t| t.gen_proof(&prover_challenge));
        let resp_comm_rho_rand_halo2 = t_comm_halo2.response(&witnesses_halo2, &prover_challenge)?;


        Ok((Self {
            re_randomized_path,
            resp_leaf,
            resp_acc_new,
            resp_null,
            resp_leg_asset_id,
            resp_leg_pk,
            resp_comm_halo2: resp_comm_rho_rand_halo2,
            resp_leg_amount,
            snark_proof_even,
            snark_proof_odd
        }, nullifier))
    }

    pub fn verify(
        &self,
        leg_enc: &LegEncryption<G0>,
        root: &Root<G0, G1, L, 1>,
        updated_account_commitment: AccountStateCommitment<G0>,
        nullifier: &G0,
        nonce: &[u8],
        prover_is_sender: bool,
        has_balance_decreased: Option<bool>,
        has_counter_decreased: bool,
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_verifying_key: &CTVerifyingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<()> {
        if self.resp_leaf.len() != 8 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(8, self.resp_leaf.len()))
        }
        if self.resp_acc_new.len() != 7 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(7, self.resp_acc_new.len()))
        }
        let num_blindings_halo2 = ct_verifying_key.even.blinding_factors() + 2;
        let usable_rows = circuit_params.even.n as usize - (num_blindings_halo2 - 1);
        if has_balance_decreased.is_some() {
            if self.resp_leg_amount.is_none() {
                return Err(Error::MissingRespForLegEncAmount)
            }
            if self.resp_comm_halo2.len() != (8 + num_blindings_halo2) {
                return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(8 + num_blindings_halo2, self.resp_comm_halo2.len()))
            }
        } else {
            if self.resp_comm_halo2.len() != (5 + num_blindings_halo2) {
                return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(5 + num_blindings_halo2, self.resp_comm_halo2.len()))
            }
        }

        let mut transcript = Transcript::new(TXN_EVEN_LABEL);

        let mut extra_instance = Vec::new();
        // TODO: Serialize later
        // extra_instance.extend_from_slice(root.to_bytes().as_ref());
        // extra_instance.extend_from_slice(self.re_randomized_path.to_bytes().as_ref());
        extra_instance.extend_from_slice(nonce);

        extra_instance.extend_from_slice(updated_account_commitment.0.to_bytes().as_ref());
        // TODO: Serialize later
        // account_comm_key.serialize_compressed(&mut extra_instance)?;

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        let nullifier_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        self.resp_leaf.challenge_contribution(&mut transcript_writer)?;
        self.resp_acc_new.challenge_contribution(&mut transcript_writer)?;
        self.resp_null.challenge_contribution(
            &nullifier_gen,
            nullifier,
            &mut transcript_writer,
        )?;
        self.resp_leg_asset_id.challenge_contribution(
            &enc_key_gen,
            &enc_gen,
            &leg_enc.ct_asset_id,
            &mut transcript_writer,
        )?;
        self.resp_leg_pk.challenge_contribution(
            &enc_key_gen,
            &pk_gen,
            if prover_is_sender {
                &leg_enc.ct_s
            } else {
                &leg_enc.ct_r
            },
            &mut transcript_writer,
        )?;

        let mut transcript_even = Blake2bRead::<_, _, Challenge255<_>>::init(self.snark_proof_odd.as_slice());
        let mut transcript_odd = Blake2bRead::<_, _, Challenge255<_>>::init(self.snark_proof_even.as_slice());

        // TODO: Allow skipping the proof to use a BatchVerifier later
        let (even_layer_public_inputs, odd_layer_public_inputs) = self.re_randomized_path.prepare_inputs(&root, &sr_proving_params.verifying_params());
        if let Some(has_balance_decreased) = has_balance_decreased {
            let flag = if has_balance_decreased {
                F0::ZERO
            } else {
                F0::from(2_u64)
            };
            let odd_inputs = vec![vec![flag], odd_layer_public_inputs];
            self.re_randomized_path.verify(
                circuit_params,
                ct_verifying_key,
                &[&[&even_layer_public_inputs]],
                &[odd_inputs.iter().map(|v| v.as_slice()).collect::<Vec<_>>().as_slice()],
                &mut transcript_even,
                &mut transcript_odd,
            ).unwrap();
        } else {
            self.re_randomized_path.verify(
                circuit_params,
                ct_verifying_key,
                &[&[&even_layer_public_inputs]],
                &[&[&odd_layer_public_inputs]],
                &mut transcript_even,
                &mut transcript_odd,
            ).unwrap();
        };

        // let rerandomized_leaf = self.re_randomized_path.clone().select_and_rerandomize_verifier_gadget::<
        //     _, _, _, _
        // >(
        //     &root, &sr_proving_params.verifying_params(),
        //     &circuit_params,
        //     &ct_verifying_key,
        //     &mut transcript_even, &mut transcript_odd
        // ).unwrap();
        // debug_assert_eq!(rerandomized_leaf, self.re_randomized_path.get_rerandomized_leaf());

        // TODO: Can't i remove this recreation of transcript
        let mut t = Blake2bRead::<_, _, Challenge255<_>>::init(self.snark_proof_odd.as_slice());
        let comm_halo2 = get_the_only_precommitted_col_comm(&ct_verifying_key.even, &mut t).unwrap();

        let mut bases_halo2 = Vec::with_capacity(8 + num_blindings_halo2);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_INITIAL_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_CURRENT_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_CURRENT_RHO_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_RANDOMNESS_IDX]);
        bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_RANDOMNESS_IDX]);

        if let Some(resp_leg_amount) = &self.resp_leg_amount {
            resp_leg_amount.challenge_contribution(
                &enc_key_gen,
                &enc_gen,
                &leg_enc.ct_amount,
                &mut transcript_writer,
            )?;
            bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_OLD_BALANCE_IDX]);
            bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_AMOUNT_IDX]);
            bases_halo2.push(circuit_params.even.g_lagrange[PRECOMMITTED_NEW_BALANCE_IDX]);
        }

        for i in 0..(num_blindings_halo2 -1) {
            bases_halo2.push(circuit_params.even.g_lagrange[usable_rows+i]);
        }
        bases_halo2.push(circuit_params.even.w);

        self.resp_comm_halo2.challenge_contribution(&mut transcript_writer)?;

        let verifier_challenge = transcript_writer.generate_challenge::<G0>(TXN_CHALLENGE_LABEL);

        self.resp_leaf.verify(
            &account_comm_key.as_gens_with_blinding(sr_proving_params.odd_level_blinding_gen),
            &self.re_randomized_path.get_rerandomized_leaf(),
            &verifier_challenge,
        )?;
        self.resp_acc_new.verify(
            &account_comm_key.as_gens(),
            &updated_account_commitment.0,
            &verifier_challenge,
        )?;
        self.resp_null
            .verify(&nullifier, &nullifier_gen, &verifier_challenge)
            .map_err(|_| Error::ProofVerificationError(
                "Nullifier verification failed".to_string(),
            ))?;
        self.resp_leg_asset_id
            .verify(&leg_enc.ct_asset_id,
                    &enc_key_gen,
                    &enc_gen,
                    &verifier_challenge,)
            .map_err(|_| Error::ProofVerificationError(
                "Leg asset ID verification failed".to_string(),
            ))?;
        self.resp_leg_pk.verify(
            if prover_is_sender {
                &leg_enc.ct_s
            } else {
                &leg_enc.ct_r
            },
            &enc_key_gen,
            &account_comm_key.sk_gen(),
            &verifier_challenge,
        ).map_err(|_| Error::ProofVerificationError(
            "Leg public key verification failed".to_string(),
        ))?;

        let mut y = comm_halo2;
        if let Some(has_balance_decreased) = has_balance_decreased {
            if !has_balance_decreased {
                y = (comm_halo2.to_curve() - (circuit_params.even.g_lagrange[PRECOMMITTED_FLAG_IDX] + circuit_params.even.g_lagrange[PRECOMMITTED_FLAG_IDX])).to_affine();
            }
            self.resp_leg_amount.as_ref().unwrap().verify(
                &leg_enc.ct_amount,
                &enc_key_gen,
                &enc_gen,
                &verifier_challenge,
            ).map_err(|_| Error::ProofVerificationError(
                "Leg amount verification failed".to_string(),
            ))?;
        }
        self.resp_comm_halo2.verify(&bases_halo2, &y, &verifier_challenge)?;

        // Sk, asset id, initial rho in leaf match the ones in updated account commitment
        if self.resp_leaf.s[0] != self.resp_acc_new.s[0] {
            return Err(Error::ProofVerificationError(
                "Secret key in leaf does not match the one in updated account commitment".to_string(),
            ));
        }
        if self.resp_leaf.s[3] != self.resp_acc_new.s[3] {
            return Err(Error::ProofVerificationError(
                "Asset ID in leaf does not match the one in updated account commitment".to_string(),
            ));
        }

        if self.resp_leaf.s[4] != self.resp_acc_new.s[4] {
            return Err(Error::ProofVerificationError(
                "Initial rho in leaf does not match the one in updated account commitment".to_string(),
            ));
        }

        if has_counter_decreased {
            // Counter in new account commitment is 1 less than the one in the leaf commitment
            if self.resp_acc_new.s[2] + verifier_challenge != self.resp_leaf.s[2] {
                return Err(Error::ProofVerificationError(
                    "Counter in new account does not match counter in leaf - 1".to_string(),
                ));
            }
        } else {
            // Counter in new account commitment is 1 more than the one in the leaf commitment
            if self.resp_acc_new.s[2] != self.resp_leaf.s[2] + verifier_challenge {
                return Err(Error::ProofVerificationError(
                    "Counter in new account does not match counter in leaf + 1".to_string(),
                ));
            }
        }

        // rho matches the one in nullifier
        if self.resp_leaf.s[5] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho in leaf does not match the one in nullifier".to_string(),
            ));
        }

        // Asset id in leg is same as in account commitment
        if self.resp_leg_asset_id.response2 != self.resp_acc_new.s[3] {
            return Err(Error::ProofVerificationError(
                "Asset ID in leg does not match the one in account commitment".to_string(),
            ));
        }

        // sk in account comm matches the one in pk
        if self.resp_leg_pk.response2 != self.resp_leaf.s[0] {
            return Err(Error::ProofVerificationError(
                "Secret key in leg public key does not match the one in leaf".to_string(),
            ));
        }

        if self.resp_comm_halo2.s[0] != self.resp_leaf.s[4] {
            return Err(Error::ProofVerificationError(
                "Initial rho mismatch between the leaf and the one in BP commitment".to_string(),
            ));
        }

        if self.resp_comm_halo2.s[1] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Old rho mismatch between the nullifier and the one in BP commitment".to_string(),
            ));
        }

        if self.resp_comm_halo2.s[2] != self.resp_acc_new.s[5] {
            return Err(Error::ProofVerificationError(
                "New rho mismatch between the new account commitment and the one in BP commitment"
                    .to_string(),
            ));
        }

        if self.resp_comm_halo2.s[3] != self.resp_leaf.s[6] {
            return Err(Error::ProofVerificationError(
                "Old randomness mismatch between the leaf and the one in BP commitment".to_string(),
            ));
        }

        if self.resp_comm_halo2.s[4] != self.resp_acc_new.s[6] {
            return Err(Error::ProofVerificationError(
                "New randomness mismatch between the account commitment and the one in BP commitment"
                    .to_string(),
            ));
        }

        if has_balance_decreased.is_some() {
            // Balance in leaf (old account) is same as in the old balance commitment
            if self.resp_leaf.s[1] != self.resp_comm_halo2.s[5] {
                return Err(Error::ProofVerificationError(
                    "Balance in leaf does not match old balance commitment".to_string(),
                ));
            }

            // Balance in new account commitment is same as in the new balance commitment
            if self.resp_acc_new.s[1] != self.resp_comm_halo2.s[7] {
                return Err(Error::ProofVerificationError(
                    "Balance in new account does not match new balance commitment".to_string(),
                ));
            }

            // Amount in leg is same as amount in commitment
            if self.resp_leg_amount.as_ref().unwrap().response2 != self.resp_comm_halo2.s[6] {
                return Err(Error::ProofVerificationError(
                    "Amount in leg does not match amount commitment".to_string(),
                ));
            }
        } else {
            // Balance in leaf (old account) is same as in the new account commitment
            if self.resp_leaf.s[1] != self.resp_acc_new.s[1] {
                return Err(Error::ProofVerificationError(
                    "Balance in leaf does not match the new account commitment".to_string(),
                ));
            }
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct AffirmAsSenderTxnProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
>(StateChangeProof<F0, F1, G0, G1, L>);

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> AffirmAsSenderTxnProof<F0, F1, G0, G1, L> {
    pub fn new<
        R: CryptoRngCore,
        Ec0: Ec<Affine = G0, Base = G0::Base, Scalar = G0::ScalarExt>,
        Ec1: Ec<Affine = G1, Base = Ec0::Scalar, Scalar = Ec0::Base>,
    >(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<G0>,
        leg_enc_rand: LegEncryptionRandomness<G0::Scalar>,
        account: &AccountState<G0>,
        updated_account: &AccountState<G0>,
        updated_account_commitment: AccountStateCommitment<G0>,
        leaf_path: CurveTreeWitnessPath<G0, G1, L>,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_proving_key: &CTProvingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<(Self, G0)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. old balance - new balance = amount.
        // 4. amount and asset id are the same as the ones committed in leg
        // 5. new counter - old counter = 1
        // 6. initial rho is same in both old and new commitments
        // 7. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 8. randomness in new account commitment is square of randomness in old account commitment
        // 9. pk in leg has the sk in account commitment

        let balance_change = BalanceChange {
            has_decreased: true,
            amount,
        };

        let (proof, nullifier) = StateChangeProof::new::<_, Ec0, Ec1>(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            true,
            Some(balance_change),
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_proving_key,
            enc_key_gen,
            enc_gen,
        )?;

        Ok((Self(proof), nullifier))
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G0>,
        root: &Root<G0, G1, L, 1>,
        updated_account_commitment: AccountStateCommitment<G0>,
        nullifier: G0,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_verifying_key: &CTVerifyingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<()> {
        self.0.verify(
            &leg_enc,
            root,
            updated_account_commitment,
            &nullifier,
            nonce,
            true,
            Some(true),
            false,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_verifying_key,
            enc_key_gen,
            enc_gen,
        )
    }
}

#[derive(Clone, Debug)]
pub struct AffirmAsReceiverTxnProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
>(StateChangeProof<F0, F1, G0, G1, L>);

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> AffirmAsReceiverTxnProof<F0, F1, G0, G1, L> {
    pub fn new<
        R: CryptoRngCore,
        Ec0: Ec<Affine=G0, Base=G0::Base, Scalar=G0::ScalarExt>,
        Ec1: Ec<Affine=G1, Base=Ec0::Scalar, Scalar=Ec0::Base>,
    >(
        rng: &mut R,
        leg_enc: LegEncryption<G0>,
        leg_enc_rand: LegEncryptionRandomness<G0::Scalar>,
        account: &AccountState<G0>,
        updated_account: &AccountState<G0>,
        updated_account_commitment: AccountStateCommitment<G0>,
        leaf_path: CurveTreeWitnessPath<G0, G1, L>,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_proving_key: &CTProvingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<(Self, G0)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id and balance are same in both old and new account commitment
        // 3. asset id is the same as the ones committed in leg
        // 4. new counter - old counter = 1
        // 5. initial rho is same in both old and new commitments
        // 6. nullifier is created from current_rho in old account commitment so this should be proven equal with other usages of current_rho.
        // 7. randomness in new account commitment is square of randomness in old account commitment
        // 8. pk in leg has the sk in account commitment

        let (proof, nullifier) = StateChangeProof::new::<_, Ec0, Ec1>(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            false,
            None,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_proving_key,
            enc_key_gen,
            enc_gen,
        )?;

        Ok((Self(proof), nullifier))
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G0>,
        root: &Root<G0, G1, L, 1>,
        updated_account_commitment: AccountStateCommitment<G0>,
        nullifier: G0,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_verifying_key: &CTVerifyingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<()> {
        self.0.verify(
            &leg_enc,
            root,
            updated_account_commitment,
            &nullifier,
            nonce,
            false,
            None,
            false,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_verifying_key,
            enc_key_gen,
            enc_gen,
        )
    }
}

#[derive(Clone, Debug)]
pub struct ClaimReceivedTxnProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
>(StateChangeProof<F0, F1, G0, G1, L>);

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> ClaimReceivedTxnProof<F0, F1, G0, G1, L> {
    pub fn new<
        R: CryptoRngCore,
        Ec0: Ec<Affine = G0, Base = G0::Base, Scalar = G0::ScalarExt>,
        Ec1: Ec<Affine = G1, Base = Ec0::Scalar, Scalar = Ec0::Base>,
    >(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<G0>,
        leg_enc_rand: LegEncryptionRandomness<G0::Scalar>,
        account: &AccountState<G0>,
        updated_account: &AccountState<G0>,
        updated_account_commitment: AccountStateCommitment<G0>,
        leaf_path: CurveTreeWitnessPath<G0, G1, L>,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_proving_key: &CTProvingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<(Self, G0)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. balance in new = balance in old + amount
        // 4. counter in new = counter in old (no change)
        // 5. current_rho is unchanged as well
        // 6. Leg is correctly created

        let balance_change = BalanceChange {
            has_decreased: false,
            amount,
        };

        let (proof, nullifier) = StateChangeProof::new::<_, Ec0, Ec1>(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            false,
            Some(balance_change),
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_proving_key,
            enc_key_gen,
            enc_gen,
        )?;

        Ok((Self(proof), nullifier))
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G0>,
        root: &Root<G0, G1, L, 1>,
        updated_account_commitment: AccountStateCommitment<G0>,
        nullifier: G0,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_verifying_key: &CTVerifyingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<()> {
        self.0.verify(
            &leg_enc,
            root,
            updated_account_commitment,
            &nullifier,
            nonce,
            false,
            Some(false),
            true,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_verifying_key,
            enc_key_gen,
            enc_gen,
        )
    }
}

#[derive(Clone, Debug)]
pub struct SenderCounterUpdateTxnProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
>(StateChangeProof<F0, F1, G0, G1, L>);

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> SenderCounterUpdateTxnProof<F0, F1, G0, G1, L> {
    pub fn new<
        R: CryptoRngCore,
        Ec0: Ec<Affine = G0, Base = G0::Base, Scalar = G0::ScalarExt>,
        Ec1: Ec<Affine = G1, Base = Ec0::Scalar, Scalar = Ec0::Base>,
    >(
        rng: &mut R,
        leg_enc: LegEncryption<G0>,
        leg_enc_rand: LegEncryptionRandomness<G0::Scalar>,
        account: &AccountState<G0>,
        updated_account: &AccountState<G0>,
        updated_account_commitment: AccountStateCommitment<G0>,
        leaf_path: CurveTreeWitnessPath<G0, G1, L>,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_proving_key: &CTProvingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<(Self, G0)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. balance is unchanged
        // 4. counter in new = counter in old - 1 (decreasing counter)
        // 5. current_rho is unchanged as well
        // 6. Leg is correctly created

        let (proof, nullifier) = StateChangeProof::new::<_, Ec0, Ec1>(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            true,
            None,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_proving_key,
            enc_key_gen,
            enc_gen,
        )?;

        Ok((Self(proof), nullifier))
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G0>,
        root: &Root<G0, G1, L, 1>,
        updated_account_commitment: AccountStateCommitment<G0>,
        nullifier: G0,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_verifying_key: &CTVerifyingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<()> {
        self.0.verify(
            &leg_enc,
            root,
            updated_account_commitment,
            &nullifier,
            nonce,
            true,
            None,
            true,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_verifying_key,
            enc_key_gen,
            enc_gen,
        )
    }
}

#[derive(Clone, Debug)]
pub struct SenderReverseTxnProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
>(StateChangeProof<F0, F1, G0, G1, L>);

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> SenderReverseTxnProof<F0, F1, G0, G1, L> {
    pub fn new<
        R: CryptoRngCore,
        Ec0: Ec<Affine = G0, Base = G0::Base, Scalar = G0::ScalarExt>,
        Ec1: Ec<Affine = G1, Base = Ec0::Scalar, Scalar = Ec0::Base>,
    >(
        rng: &mut R,
        amount: Balance,
        leg_enc: LegEncryption<G0>,
        leg_enc_rand: LegEncryptionRandomness<G0::Scalar>,
        account: &AccountState<G0>,
        updated_account: &AccountState<G0>,
        updated_account_commitment: AccountStateCommitment<G0>,
        leaf_path: CurveTreeWitnessPath<G0, G1, L>,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_proving_key: &CTProvingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<(Self, G0)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. balance in new = balance in old + amount (reversing send means getting money back)
        // 4. counter in new = counter in old - 1 (decreasing counter)
        // 5. current_rho is unchanged as well
        // 6. Leg is correctly created

        let balance_change = BalanceChange {
            has_decreased: false,
            amount,
        };

        let (proof, nullifier) = StateChangeProof::new::<_, Ec0, Ec1>(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            true,
            Some(balance_change),
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_proving_key,
            enc_key_gen,
            enc_gen,
        )?;

        Ok((Self(proof), nullifier))
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G0>,
        root: &Root<G0, G1, L, 1>,
        updated_account_commitment: AccountStateCommitment<G0>,
        nullifier: G0,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_verifying_key: &CTVerifyingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<()> {
        self.0.verify(
            &leg_enc,
            root,
            updated_account_commitment,
            &nullifier,
            nonce,
            true,
            Some(false),
            true,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_verifying_key,
            enc_key_gen,
            enc_gen,
        )
    }
}

#[derive(Clone, Debug)]
pub struct ReceiverCounterUpdateTxnProof<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
>(StateChangeProof<F0, F1, G0, G1, L>);

impl<
    F0: PrimeField,
    F1: PrimeField,
    G0: AffineSerializable<ScalarExt = F0, Base = F1>,
    G1: AffineSerializable<ScalarExt = F1, Base = F0>,
    const L: usize
> ReceiverCounterUpdateTxnProof<F0, F1, G0, G1, L> {
    pub fn new<
        R: CryptoRngCore,
        Ec0: Ec<Affine = G0, Base = G0::Base, Scalar = G0::ScalarExt>,
        Ec1: Ec<Affine = G1, Base = Ec0::Scalar, Scalar = Ec0::Base>,
    >(
        rng: &mut R,
        leg_enc: LegEncryption<G0>,
        leg_enc_rand: LegEncryptionRandomness<G0::Scalar>,
        account: &AccountState<G0>,
        updated_account: &AccountState<G0>,
        updated_account_commitment: AccountStateCommitment<G0>,
        leaf_path: CurveTreeWitnessPath<G0, G1, L>,
        root: &Root<G0, G1, L, 1>,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_proving_key: &CTProvingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<(Self, G0)> {
        // Need to prove that:
        // 1. sk is same in both old and new account commitment
        // 2. asset-id is same in both old and new account commitment
        // 3. balance is unchanged
        // 4. counter in new = counter in old - 1 (decreasing counter)
        // 5. current_rho is unchanged as well
        // 6. Leg is correctly created

        let (proof, nullifier) = StateChangeProof::new::<_, Ec0, Ec1>(
            rng,
            leg_enc,
            leg_enc_rand,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            false,
            None,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_proving_key,
            enc_key_gen,
            enc_gen,
        )?;

        Ok((Self(proof), nullifier))
    }

    pub fn verify(
        &self,
        leg_enc: LegEncryption<G0>,
        root: &Root<G0, G1, L, 1>,
        updated_account_commitment: AccountStateCommitment<G0>,
        nullifier: G0,
        nonce: &[u8],
        sr_proving_params: &SelRerandProvingParams<G0, G1>,
        account_comm_key: impl AccountCommitmentKeyTrait<G0>,
        circuit_params: &CTCircuitParams<G0, G1>,
        ct_verifying_key: &CTVerifyingKey<G0, G1>,
        enc_key_gen: G0,
        enc_gen: G0,
    ) -> Result<()> {
        self.0.verify(
            &leg_enc,
            root,
            updated_account_commitment,
            &nullifier,
            nonce,
            false,
            None,
            true,
            sr_proving_params,
            account_comm_key,
            circuit_params,
            ct_verifying_key,
            enc_key_gen,
            enc_gen,
        )
    }
}

/// Proof of balance with an auditor
#[derive(Clone, Debug)]
pub struct PobWithAuditorProof<G: AffineSerializable> {
    pub nullifier: G,
    pub resp_acc: Response<G>,
    pub resp_null: PokDiscreteLog<G>,
    pub resp_pk: PokDiscreteLog<G>,
}

impl<G: AffineSerializable> PobWithAuditorProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<Self> {
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. nullifier is created from current_rho
        //
        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. If its not possible then do a membership proof

        let mut transcript = Transcript::new(TXN_POB_LABEL);

        let mut extra_instance = Vec::new();
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(account_commitment.0.to_bytes().as_ref());
        extra_instance.extend_from_slice(pk.to_bytes().as_ref());
        for generator in account_comm_key.as_gens() {
            extra_instance.extend_from_slice(generator.to_bytes().as_ref());
        }

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        let nullifier = account.nullifier(&account_comm_key);

        let sk_blinding = G::ScalarExt::random(&mut *rng);
        let current_rho_blinding = G::ScalarExt::random(&mut *rng);

        // For proving relation g_i * rho + g_j * current_rho + g_k * randomness = C - (pk + g_a * v + g_b * at + g_c * cnt)
        // where C is the account commitment and rho, current_rho and randomness are the witness, rest are instance
        let t_acc = CommitmentToRandomness::new(
            &[
                account_comm_key.rho_gen(),
                null_gen,
                account_comm_key.randomness_gen(),
            ],
            vec![
                G::ScalarExt::random(&mut *rng),
                current_rho_blinding,
                G::ScalarExt::random(&mut *rng),
            ],
        );

        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, current_rho_blinding, &null_gen);
        let t_pk = PokDiscreteLogProtocol::init(account.sk, sk_blinding, &pk_gen);

        t_acc.challenge_contribution(&mut transcript_writer)?;
        t_null.challenge_contribution(&null_gen, &nullifier, &mut transcript_writer)?;
        t_pk.challenge_contribution(&pk_gen, pk, &mut transcript_writer)?;

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        let resp_acc = t_acc.response(
            &[account.rho, account.current_rho, account.randomness],
            &challenge,
        )?;
        let resp_null = t_null.gen_proof(&challenge);
        let resp_pk = t_pk.gen_proof(&challenge);

        Ok(Self {
            nullifier,
            resp_acc,
            resp_null,
            resp_pk,
        })
    }

    pub fn verify(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<()> {
        let mut transcript = Transcript::new(TXN_POB_LABEL);

        let mut extra_instance = Vec::new();
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(account_commitment.0.to_bytes().as_ref());
        extra_instance.extend_from_slice(pk.to_bytes().as_ref());
        for generator in account_comm_key.as_gens() {
            extra_instance.extend_from_slice(generator.to_bytes().as_ref());
        }

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        self.resp_acc
            .challenge_contribution(&mut transcript_writer)?;
        self.resp_null.challenge_contribution(
            &null_gen,
            &self.nullifier,
            &mut transcript_writer,
        )?;
        self.resp_pk
            .challenge_contribution(&pk_gen, pk, &mut transcript_writer)?;

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        let y = account_commitment.0.to_curve()
            - (pk.to_curve()
            + account_comm_key.balance_gen() * G::ScalarExt::from(balance)
            + account_comm_key.counter_gen() * G::ScalarExt::from(counter as u64)
            + account_comm_key.asset_id_gen() * G::ScalarExt::from(asset_id as u64));

        self.resp_acc.verify(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
            ],
            &y.to_affine(),
            &challenge,
        )?;

        self.resp_null
            .verify(&self.nullifier, &null_gen, &challenge)
            .map_err(|_| {
                Error::ProofVerificationError("Nullifier proof verification failed".to_string())
            })?;

        self.resp_pk.verify(pk, &pk_gen, &challenge).map_err(|_| {
            Error::ProofVerificationError("Public key proof verification failed".to_string())
        })?;

        // rho matches the one in nullifier
        if self.resp_acc.s[1] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho in account does not match the one in nullifier".to_string(),
            ));
        }
        Ok(())
    }
}

/// Proof of balance with arbitrary party. Report section 5.1.11, fig 10
#[derive(Clone, Debug)]
pub struct PobWithAnyoneProof<G: AffineSerializable> {
    pub nullifier: G,
    pub resp_acc: Response<G>,
    pub resp_null: PokDiscreteLog<G>,
    pub resp_pk: PokDiscreteLog<G>,
    /// For proving correctness of twisted Elgamal ciphertext of asset-id in each leg
    pub resp_asset_id: Vec<PokDiscreteLog<G>>,
    /// For proving correctness of twisted Elgamal ciphertext of sender public key. Used when prover is sender.
    pub resp_pk_send: BTreeMap<usize, PokDiscreteLog<G>>,
    /// For proving correctness of twisted Elgamal ciphertext of receiver public key. Used when prover is receiver.
    pub resp_pk_recv: BTreeMap<usize, PokDiscreteLog<G>>,
    /// Proving knowledge of `\sum{r_3}` in `\sum{C_v} - h * \sum{v} = g * \sum{r_3}` where prover is receiver. `\sum{v}` is the total received amount in the legs
    pub resp_recv_amount: PokDiscreteLog<G>,
    /// Proving knowledge of `\sum{r_3}` in `\sum{C_v} - h * \sum{v} = g * \sum{r_3}` where prover is sender. `\sum{v}` is the total sent amount in the legs
    pub resp_sent_amount: PokDiscreteLog<G>,
}

impl<G: AffineSerializable> PobWithAnyoneProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: &G,
        account: &AccountState<G>,
        account_commitment: AccountStateCommitment<G>,
        // Next few fields args can be abstracted in a single argument. Like a map with key as index and value as legs, keys, etc for that index
        legs: Vec<(LegEncryption<G>, LegEncryptionRandomness<G::ScalarExt>)>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<Self> {
        if legs.len() != (sender_in_leg_indices.len() + receiver_in_leg_indices.len()) {
            return Err(Error::ProofGenerationError(
                "Number of legs and indices for sender and receiver do not match".to_string(),
            ));
        }

        let num_pending_txns = legs.len();
        // Need to prove that:
        // 1. sk used in commitment is for the revealed pk
        // 2. counter equals number of leg encryptions
        // 3. pk has the respective role in each leg
        // 4. asset-id is the given one in all legs
        // 5. sum of amounts in pending send txns equals the given public value
        // 6. sum of amounts in pending receive txns equals the given public value
        // 7. nullifier is created from current_rho of account commitment

        // The prover should share the index of account commitment in tree so verifier can efficiently fetch the commitment and compare. If its not possible then do a membership proof

        let at = G::ScalarExt::from(account.asset_id as u64);
        let h_at = enc_gen * at;

        let mut transcript = Transcript::new(TXN_POB_LABEL);

        let mut extra_instance = Vec::new();
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(account_commitment.0.to_bytes().as_ref());
        extra_instance.extend_from_slice(&pending_sent_amount.to_le_bytes());
        extra_instance.extend_from_slice(&pending_recv_amount.to_le_bytes());
        extra_instance.extend_from_slice(&account.asset_id.to_le_bytes());
        extra_instance.extend_from_slice(&account.balance.to_le_bytes());
        extra_instance.extend_from_slice(&(account.counter as u64).to_le_bytes());
        extra_instance.extend_from_slice(h_at.to_affine().to_bytes().as_ref());
        // TODO: Leg serialization
        extra_instance.extend_from_slice(pk.to_bytes().as_ref());
        for generator in account_comm_key.as_gens() {
            extra_instance.extend_from_slice(generator.to_bytes().as_ref());
        }
        extra_instance.extend_from_slice(enc_key_gen.to_bytes().as_ref());
        extra_instance.extend_from_slice(enc_gen.to_bytes().as_ref());

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        let nullifier = account.nullifier(&account_comm_key);

        let sk_blinding = G::ScalarExt::random(&mut *rng);
        let current_rho_blinding = G::ScalarExt::random(&mut *rng);

        // For proving correctness of twisted Elgamal ciphertext of asset-id
        let mut t_asset_id: Vec<PokDiscreteLogProtocol<G>> = vec![];

        // For proving correctness of twisted Elgamal ciphertext of sender public key. Used when prover is sender.
        let mut t_pk_send = BTreeMap::new();
        // For proving correctness of twisted Elgamal ciphertext of receiver public key. Used when prover is receiver.
        let mut t_pk_recv = BTreeMap::new();

        // Sum of all r_3 where prover is sender
        let mut sum_r_3_sent = G::ScalarExt::ZERO;
        // Sum of all r_3 where prover is receiver
        let mut sum_r_3_recv = G::ScalarExt::ZERO;

        let t_acc = CommitmentToRandomness::new(
            &[
                account_comm_key.rho_gen(),
                null_gen,
                account_comm_key.randomness_gen(),
            ],
            vec![
                G::ScalarExt::random(&mut *rng),
                current_rho_blinding,
                G::ScalarExt::random(&mut *rng),
            ],
        );

        // To prove nullifier correctness
        let t_null =
            PokDiscreteLogProtocol::init(account.current_rho, current_rho_blinding, &null_gen);
        // To prove secret key in account state is same as in public key
        let t_pk = PokDiscreteLogProtocol::init(account.sk, sk_blinding, &pk_gen);

        // Sum of all C_v where prover is sender
        let mut enc_total_send = G::Curve::identity();
        // Sum of all C_v where prover is receiver
        let mut enc_total_recv = G::Curve::identity();

        // TODO: These protocols can be aggregated together with an RLC. Oe even the batch-Sigma protocol can be used.
        for i in 0..num_pending_txns {
            let LegEncryptionRandomness(r_1, r_2, r_3, r_4) = legs[i].1;

            if receiver_in_leg_indices.contains(&i) {
                // Proving knowledge of r_2 in C_r - pk = g * r_2
                let t_leg_pk = PokDiscreteLogProtocol::init(
                    r_2,
                    G::ScalarExt::random(&mut *rng),
                    &enc_key_gen,
                );
                t_pk_recv.insert(i, t_leg_pk);
                sum_r_3_recv += r_3;
                enc_total_recv += legs[i].0.ct_amount;
            } else if sender_in_leg_indices.contains(&i) {
                // Proving knowledge of r_1 in C_s - pk = g * r_1
                let t_leg_pk = PokDiscreteLogProtocol::init(
                    r_1,
                    G::ScalarExt::random(&mut *rng),
                    &enc_key_gen,
                );
                t_pk_send.insert(i, t_leg_pk);
                sum_r_3_sent += r_3;
                enc_total_send += legs[i].0.ct_amount;
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            // Proving knowledge of r_4 in C_at - h * at = g * r_4
            let t_leg_asset_id =
                PokDiscreteLogProtocol::init(r_4, G::ScalarExt::random(&mut *rng), &enc_key_gen);
            t_asset_id.push(t_leg_asset_id);
        }

        // Proving knowledge of \sum{r_3} in \sum{C_v} - h * \sum{v} = g * \sum{r_3} where prover is sender. \sum{v} is the total sent amount in the legs
        let t_sent_amount = PokDiscreteLogProtocol::init(
            sum_r_3_sent,
            G::ScalarExt::random(&mut *rng),
            &enc_key_gen,
        );
        // Proving knowledge of \sum{r_3} in \sum{C_v} - h * \sum{v} = g * \sum{r_3} where prover is receiver. \sum{v} is the total received amount in the legs
        let t_recv_amount = PokDiscreteLogProtocol::init(
            sum_r_3_recv,
            G::ScalarExt::random(&mut *rng),
            &enc_key_gen,
        );

        // Add challenge contributions
        t_acc.challenge_contribution(&mut transcript_writer)?;
        t_null.challenge_contribution(&null_gen, &nullifier, &mut transcript_writer)?;
        t_pk.challenge_contribution(&pk_gen, pk, &mut transcript_writer)?;

        let pk_curve = pk.to_curve();

        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                let y = legs[i].0.ct_r.to_curve() - pk_curve;
                t_pk_recv[&i].challenge_contribution(
                    &enc_key_gen,
                    &y.to_affine(),
                    &mut transcript_writer,
                )?;
            } else if sender_in_leg_indices.contains(&i) {
                let y = legs[i].0.ct_s.to_curve() - pk_curve;
                t_pk_send[&i].challenge_contribution(
                    &enc_key_gen,
                    &y.to_affine(),
                    &mut transcript_writer,
                )?;
            } else {
                return Err(Error::ProofGenerationError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = legs[i].0.ct_asset_id.to_curve() - h_at;
            t_asset_id[i].challenge_contribution(
                &enc_key_gen,
                &y.to_affine(),
                &mut transcript_writer,
            )?;
        }

        let y_total_send =
            (enc_total_send - (enc_gen * G::ScalarExt::from(pending_sent_amount))).to_affine();
        t_sent_amount.challenge_contribution(
            &enc_key_gen,
            &y_total_send,
            &mut transcript_writer,
        )?;
        let y_total_recv =
            (enc_total_recv - (enc_gen * G::ScalarExt::from(pending_recv_amount))).to_affine();
        t_recv_amount.challenge_contribution(
            &enc_key_gen,
            &y_total_recv,
            &mut transcript_writer,
        )?;

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        // Generate responses
        let resp_acc = t_acc.response(
            &[account.rho, account.current_rho, account.randomness],
            &challenge,
        )?;
        let resp_null = t_null.gen_proof(&challenge);
        let resp_pk = t_pk.gen_proof(&challenge);

        let resp_asset_id = t_asset_id
            .into_iter()
            .map(|t| t.gen_proof(&challenge))
            .collect::<Vec<_>>();

        let mut resp_pk_send = BTreeMap::new();
        for (idx, t) in t_pk_send {
            resp_pk_send.insert(idx, t.gen_proof(&challenge));
        }

        let mut resp_pk_recv = BTreeMap::new();
        for (idx, t) in t_pk_recv {
            resp_pk_recv.insert(idx, t.gen_proof(&challenge));
        }

        let resp_recv_amount = t_recv_amount.gen_proof(&challenge);
        let resp_sent_amount = t_sent_amount.gen_proof(&challenge);

        Ok(Self {
            nullifier,
            resp_acc,
            resp_null,
            resp_pk,
            resp_asset_id,
            resp_pk_send,
            resp_pk_recv,
            resp_recv_amount,
            resp_sent_amount,
        })
    }

    pub fn verify(
        &self,
        asset_id: AssetId,
        balance: Balance,
        counter: PendingTxnCounter,
        pk: &G,
        account_commitment: AccountStateCommitment<G>,
        legs: Vec<LegEncryption<G>>,
        sender_in_leg_indices: BTreeSet<usize>,
        receiver_in_leg_indices: BTreeSet<usize>,
        pending_sent_amount: Balance,
        pending_recv_amount: Balance,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        enc_key_gen: G,
        enc_gen: G,
    ) -> Result<()> {
        if legs.len() != (sender_in_leg_indices.len() + receiver_in_leg_indices.len()) {
            return Err(Error::ProofVerificationError(
                "Number of legs and indices for sender and receiver do not match".to_string(),
            ));
        }

        let at = G::ScalarExt::from(asset_id as u64);
        let h_at = enc_gen * at;

        let mut transcript = Transcript::new(TXN_POB_LABEL);

        let mut extra_instance = Vec::new();
        extra_instance.extend_from_slice(nonce);
        extra_instance.extend_from_slice(account_commitment.0.to_bytes().as_ref());
        extra_instance.extend_from_slice(&pending_sent_amount.to_le_bytes());
        extra_instance.extend_from_slice(&pending_recv_amount.to_le_bytes());
        extra_instance.extend_from_slice(&asset_id.to_le_bytes());
        extra_instance.extend_from_slice(&balance.to_le_bytes());
        extra_instance.extend_from_slice(&(counter as u64).to_le_bytes());
        extra_instance.extend_from_slice(h_at.to_affine().to_bytes().as_ref());
        // TODO: Leg serialization
        extra_instance.extend_from_slice(pk.to_bytes().as_ref());
        for generator in account_comm_key.as_gens() {
            extra_instance.extend_from_slice(generator.to_bytes().as_ref());
        }
        extra_instance.extend_from_slice(enc_key_gen.to_bytes().as_ref());
        extra_instance.extend_from_slice(enc_gen.to_bytes().as_ref());

        let mut transcript_writer = TranscriptWriter(&mut transcript);
        transcript_writer.append_message(TXN_INSTANCE_LABEL, &extra_instance);

        let null_gen = account_comm_key.current_rho_gen();
        let pk_gen = account_comm_key.sk_gen();

        let num_pending_txns = legs.len();

        self.resp_acc
            .challenge_contribution(&mut transcript_writer)?;
        self.resp_null.challenge_contribution(
            &null_gen,
            &self.nullifier,
            &mut transcript_writer,
        )?;
        self.resp_pk
            .challenge_contribution(&pk_gen, pk, &mut transcript_writer)?;

        let mut enc_total_send = G::Curve::identity();
        let mut enc_total_recv = G::Curve::identity();
        let mut pk_recv_y = BTreeMap::new();
        let mut pk_send_y = BTreeMap::new();

        let pk_g = pk.to_curve();
        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                let y = (legs[i].ct_r.to_curve() - pk_g).to_affine();
                let resp = self
                    .resp_pk_recv
                    .get(&i)
                    .ok_or_else(|| Error::ProofOfBalanceError(format!("Missing pk recv: {i}")))?;
                resp.challenge_contribution(&enc_key_gen, &y, &mut transcript_writer)?;
                enc_total_recv += legs[i].ct_amount;
                pk_recv_y.insert(i, y);
            } else if sender_in_leg_indices.contains(&i) {
                let y = (legs[i].ct_s.to_curve() - pk_g).to_affine();
                let resp = self
                    .resp_pk_send
                    .get(&i)
                    .ok_or_else(|| Error::ProofOfBalanceError(format!("Missing pk send: {i}")))?;
                resp.challenge_contribution(&enc_key_gen, &y, &mut transcript_writer)?;
                enc_total_send += legs[i].ct_amount;
                pk_send_y.insert(i, y);
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = legs[i].ct_asset_id.to_curve() - h_at;
            self.resp_asset_id[i].challenge_contribution(
                &enc_key_gen,
                &y.to_affine(),
                &mut transcript_writer,
            )?;
        }

        let y_total_send =
            (enc_total_send - (enc_gen * G::ScalarExt::from(pending_sent_amount))).to_affine();
        self.resp_sent_amount.challenge_contribution(
            &enc_key_gen,
            &y_total_send,
            &mut transcript_writer,
        )?;
        let y_total_recv =
            (enc_total_recv - (enc_gen * G::ScalarExt::from(pending_recv_amount))).to_affine();
        self.resp_recv_amount.challenge_contribution(
            &enc_key_gen,
            &y_total_recv,
            &mut transcript_writer,
        )?;

        let challenge = transcript_writer.generate_challenge::<G>(TXN_CHALLENGE_LABEL);

        let y = account_commitment.0.to_curve()
            - (pk.to_curve()
            + account_comm_key.balance_gen() * G::ScalarExt::from(balance)
            + account_comm_key.counter_gen() * G::ScalarExt::from(counter as u64)
            + account_comm_key.asset_id_gen() * G::ScalarExt::from(asset_id as u64));

        self.resp_acc.verify(
            &[
                account_comm_key.rho_gen(),
                account_comm_key.current_rho_gen(),
                account_comm_key.randomness_gen(),
            ],
            &y.to_affine(),
            &challenge,
        )?;

        // Verify discrete log proofs
        self.resp_null
            .verify(&self.nullifier, &null_gen, &challenge)
            .map_err(|_| {
                Error::ProofVerificationError("Nullifier proof verification failed".to_string())
            })?;
        self.resp_pk.verify(pk, &pk_gen, &challenge).map_err(|_| {
            Error::ProofVerificationError("Public key proof verification failed".to_string())
        })?;

        for i in 0..num_pending_txns {
            if receiver_in_leg_indices.contains(&i) {
                let comm = self
                    .resp_pk_recv
                    .get(&i)
                    .ok_or_else(|| Error::ProofOfBalanceError(format!("Missing pk recv: {i}")))?;
                comm.verify(&pk_recv_y.remove(&i).unwrap(), &enc_key_gen, &challenge)
                    .map_err(|_| {
                        Error::ProofVerificationError(format!(
                            "Receiver public key verification failed for leg {}",
                            i
                        ))
                    })?
            } else if sender_in_leg_indices.contains(&i) {
                let comm = self
                    .resp_pk_send
                    .get(&i)
                    .ok_or_else(|| Error::ProofOfBalanceError(format!("Missing pk send: {i}")))?;
                comm.verify(&pk_send_y.remove(&i).unwrap(), &enc_key_gen, &challenge)
                    .map_err(|_| {
                        Error::ProofVerificationError(format!(
                            "Sender public key verification failed for leg {}",
                            i
                        ))
                    })?
            } else {
                return Err(Error::ProofOfBalanceError(format!(
                    "Could not find index {i} in sent or recv"
                )));
            }

            let y = legs[i].ct_asset_id.to_curve() - h_at;
            self.resp_asset_id[i]
                .verify(&y.to_affine(), &enc_key_gen, &challenge)
                .map_err(|_| {
                    Error::ProofVerificationError(format!(
                        "Asset ID verification failed for leg {}",
                        i
                    ))
                })?;
        }

        self.resp_recv_amount
            .verify(&y_total_recv, &enc_key_gen, &challenge)
            .map_err(|_| {
                Error::ProofVerificationError(
                    "Receive amount proof verification failed".to_string(),
                )
            })?;
        self.resp_sent_amount
            .verify(&y_total_send, &enc_key_gen, &challenge)
            .map_err(|_| {
                Error::ProofVerificationError("Sent amount proof verification failed".to_string())
            })?;

        // rho matches the one in nullifier
        if self.resp_acc.s[1] != self.resp_null.response {
            return Err(Error::ProofVerificationError(
                "Rho in account does not match the one in nullifier".to_string(),
            ));
        }

        Ok(())
    }
}

/// Ensure that the same asset_id and sk are in both account states
fn ensure_same_accounts<G: AffineSerializable>(
    old_state: &AccountState<G>,
    new_state: &AccountState<G>,
) -> Result<()> {
    if old_state.sk != new_state.sk {
        return Err(Error::ProofGenerationError(
            "Secret key mismatch between old and new account states".to_string(),
        ));
    }
    if old_state.asset_id != new_state.asset_id {
        return Err(Error::ProofGenerationError(
            "Asset ID mismatch between old and new account states".to_string(),
        ));
    }
    if old_state.rho != new_state.rho {
        return Err(Error::ProofGenerationError(
            "Initial rho mismatch between old and new account states".to_string(),
        ));
    }
    // Reconsider: Should I be checking such expensive relations
    if old_state.current_rho * old_state.rho != new_state.current_rho {
        return Err(Error::ProofGenerationError(
            "Randomness not correctly constructed".to_string(),
        ));
    }
    if old_state.randomness.square() != new_state.randomness {
        return Err(Error::ProofGenerationError(
            "Randomness not correctly constructed".to_string(),
        ));
    }
    Ok(())
}


/// Take each generator function and write its bytes to the buffer.
pub fn serialize_account_commitment_key<G: AffineSerializable>(
    account_comm_key: &impl AccountCommitmentKeyTrait<G>,
    buf: &mut impl ark_std::io::Write,
) -> ark_std::io::Result<()> {
    // Write bytes of each generator in the order they appear in the trait
    buf.write_all(account_comm_key.sk_gen().to_bytes().as_ref())?;
    buf.write_all(account_comm_key.balance_gen().to_bytes().as_ref())?;
    buf.write_all(account_comm_key.counter_gen().to_bytes().as_ref())?;
    buf.write_all(account_comm_key.asset_id_gen().to_bytes().as_ref())?;
    buf.write_all(account_comm_key.rho_gen().to_bytes().as_ref())?;
    buf.write_all(account_comm_key.current_rho_gen().to_bytes().as_ref())?;
    buf.write_all(account_comm_key.randomness_gen().to_bytes().as_ref())?;
    Ok(())
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::{DecKey, EncKey, Leg, SigKey, VerKey, keygen_enc, keygen_sig};
    use blake2::Blake2b512;
    use pasta_curves::{pallas, vesta};
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;
    use std::time::Instant;
    use ct_halo2::tree::tree::CurveTree;
    use crate::circuits::affirmation::tests::setup_curve_tree_params_for_affirm;
    use crate::circuits::mint::tests::{setup_curve_tree_params_for_state_transition, generate_pallas_sel_rerand_params};

    type PallasAffine = pallas::Affine;
    type VestaAffine = vesta::Affine;

    pub fn setup_comm_key<R: CryptoRngCore>(rng: &mut R) -> [pallas::Affine; NUM_GENERATORS] {
        [
            pallas::Point::random(&mut *rng).to_affine(),
            pallas::Point::random(&mut *rng).to_affine(),
            pallas::Point::random(&mut *rng).to_affine(),
            pallas::Point::random(&mut *rng).to_affine(),
            pallas::Point::random(&mut *rng).to_affine(),
            pallas::Point::random(&mut *rng).to_affine(),
            pallas::Point::random(&mut *rng).to_affine(),
        ]
    }

    /// This is just for testing and in practice, each party generates its own keys.
    pub fn setup_keys<R: CryptoRngCore, C: AffineSerializable>(
        rng: &mut R,
        sig_key_gen: C,
        enc_key_gen: C,
    ) -> (
        ((SigKey<C>, VerKey<C>), (DecKey<C>, EncKey<C>)),
        ((SigKey<C>, VerKey<C>), (DecKey<C>, EncKey<C>)),
        ((SigKey<C>, VerKey<C>), (DecKey<C>, EncKey<C>)),
    ) {
        // Account signing (affirmation) keys
        let (sk_s, pk_s) = keygen_sig(rng, sig_key_gen);
        let (sk_r, pk_r) = keygen_sig(rng, sig_key_gen);
        let (sk_a, pk_a) = keygen_sig(rng, sig_key_gen);

        // Encryption keys
        let (sk_s_e, pk_s_e) = keygen_enc(rng, enc_key_gen);
        let (sk_r_e, pk_r_e) = keygen_enc(rng, enc_key_gen);
        let (sk_a_e, pk_a_e) = keygen_enc(rng, enc_key_gen);
        (
            ((sk_s, pk_s), (sk_s_e, pk_s_e)),
            ((sk_r, pk_r), (sk_r_e, pk_r_e)),
            ((sk_a, pk_a), (sk_a_e, pk_a_e)),
        )
    }

    pub fn setup_leg<R: CryptoRngCore>(
        rng: &mut R,
        pk_s: PallasAffine,
        pk_r: PallasAffine,
        pk_a_e: PallasAffine,
        amount: Balance,
        asset_id: AssetId,
        pk_s_e: PallasAffine,
        pk_r_e: PallasAffine,
        enc_key_gen: PallasAffine,
        enc_gen: PallasAffine,
    ) -> (
        Leg<PallasAffine>,
        LegEncryption<PallasAffine>,
        LegEncryptionRandomness<pallas::Scalar>,
    ) {
        let leg = Leg::new(pk_s, pk_r, vec![(true, pk_a_e)], amount, asset_id).unwrap();
        let (leg_enc, leg_enc_rand) = leg
            .encrypt::<_, Blake2b512>(rng, pk_s_e, pk_r_e, enc_key_gen, enc_gen)
            .unwrap();
        (leg, leg_enc, leg_enc_rand)
    }


    /// Create a curve tree with a single account commitment 
    /// Generates curve tree params internally and returns both the tree and sr_proving_params
    pub fn setup_account_tree_with_account_comm<const L: usize>(
        account: &AccountState<PallasAffine>,
        account_comm_key: impl AccountCommitmentKeyTrait<PallasAffine>,
        height: Option<u8>,
    ) -> (CurveTree<PallasAffine, VestaAffine, L>, SelRerandProvingParams<PallasAffine, VestaAffine>, SelRerandVerifyingParams<PallasAffine, VestaAffine>) {
        let (sr_params, sr_proving_params, sr_verifying_params) = generate_pallas_sel_rerand_params::<L>();

        let account_comm = account.commit(account_comm_key).unwrap();
        let leaves = [account_comm.0];
        let tree = CurveTree::<PallasAffine, VestaAffine, L>::from_leaves(
            &leaves,
            &sr_params,
            height,
        );

        (tree, sr_proving_params, sr_verifying_params)
    }

    #[test]
    fn increase_supply_txn() {
        let mut rng = rand::thread_rng();

        let k = 12;
        const L: usize = 1024;
        let height = 3;

        // Create public params (generators, etc)
        let account_comm_key = setup_comm_key(&mut rng);

        let (circuit_params, ct_pk, ct_vk) = setup_curve_tree_params_for_state_transition::<L>(k, height);

        let asset_id = 1;

        // Issuer creates keys
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let account = AccountState::new(&mut rng, sk.0, asset_id, 1).unwrap();

        let (account_tree, sr_proving_params, _) = setup_account_tree_with_account_comm::<L>(&account, account_comm_key.clone(), Some(height as u8));
        let root = account_tree.root_node();

        let leaf_index = 0;
        let increase_bal_by = 10;

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_mint(increase_bal_by).unwrap();
        assert_eq!(updated_account.rho, account.rho);
        assert_eq!(
            updated_account.current_rho,
            account.current_rho * account.rho
        );
        assert_eq!(updated_account.randomness, account.randomness.square());
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(leaf_index, 0);

        let (proof, nullifier) = MintTxnProof::new::<_, PallasEc, VestaEc>(
            &mut rng,
            pk.0,
            increase_bal_by,
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &sr_proving_params,
            account_comm_key.clone(),
            &circuit_params,
            &ct_pk
        )
            .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                pk.0,
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &sr_proving_params,
                account_comm_key.clone(),
                &circuit_params,
                &ct_vk
            )
            .unwrap();

        let verifier_time = clock.elapsed();
        println!("Prover time: {:?}, Verifier time: {:?}", prover_time, verifier_time);
    }

    #[test]
    fn send_txn() {
        let mut rng = rand::thread_rng();

        let k = 12;
        const L: usize = 2000;
        let height = 3;

        let account_comm_key = setup_comm_key(&mut rng);

        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();

        println!("1");
        let (circuit_params, ct_pk, ct_vk) = setup_curve_tree_params_for_affirm::<L>(k, height);
        println!("2");
        let (((sk_s, pk_s), (_, pk_s_e)), ((_, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account
        let mut account = AccountState::new(&mut rng, sk_s.0, asset_id, 1).unwrap();
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;

        let (account_tree, sr_proving_params, _) = setup_account_tree_with_account_comm::<L>(&account, account_comm_key.clone(), Some(height as u8));

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = AffirmAsSenderTxnProof::new::<_, PallasEc, VestaEc>(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &sr_proving_params,
            account_comm_key.clone(),
            &circuit_params,
            &ct_pk,
            enc_key_gen,
            enc_gen,
        )
            .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &sr_proving_params,
                account_comm_key.clone(),
                &circuit_params,
                &ct_vk,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();
        println!("Prover time: {:?}, Verifier time: {:?}", prover_time, verifier_time);
    }

    #[test]
    fn receive_txn() {
        let mut rng = rand::thread_rng();

        let k = 12;
        const L: usize = 2000;
        let height = 3;

        let account_comm_key = setup_comm_key(&mut rng);

        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();

        let (circuit_params, ct_pk, ct_vk) = setup_curve_tree_params_for_state_transition::<L>(k, height);

        let (((_, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Receiver account
        let mut account = AccountState::new(&mut rng, sk_r.0, asset_id, 1).unwrap();
        // Assume that account had some balance. Either got it as the issuer or from another transfer
        account.balance = 200;

        let (account_tree, sr_proving_params, _) = setup_account_tree_with_account_comm::<L>(&account, account_comm_key.clone(), Some(height as u8));

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_receive();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = AffirmAsReceiverTxnProof::new::<_, PallasEc, VestaEc>(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &sr_proving_params,
            account_comm_key.clone(),
            &circuit_params,
            &ct_pk,
            enc_key_gen,
            enc_gen,
        )
            .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &sr_proving_params,
                account_comm_key.clone(),
                &circuit_params,
                &ct_vk,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();
        println!("Prover time: {:?}, Verifier time: {:?}", prover_time, verifier_time);
    }

    #[test]
    fn claim_received_funds() {
        // This is what report calls txn_cu (counter update) done by receiver
        let mut rng = rand::thread_rng();

        let k = 12;
        const L: usize = 2000;
        let height = 3;

        let account_comm_key = setup_comm_key(&mut rng);

        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();

        let (circuit_params, ct_pk, ct_vk) = setup_curve_tree_params_for_affirm::<L>(k, height);

        let (((_, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Receiver account
        let mut account = AccountState::new(&mut rng, sk_r.0, asset_id, 1).unwrap();
        // Assume that account had some balance and it had sent the receive transaction to increase its counter
        account.balance = 200;
        account.counter += 1;

        let (account_tree, sr_proving_params, _) = setup_account_tree_with_account_comm::<L>(&account, account_comm_key.clone(), Some(height as u8));

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_claiming_received(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = ClaimReceivedTxnProof::new::<_, PallasEc, VestaEc>(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &sr_proving_params,
            account_comm_key.clone(),
            &circuit_params,
            &ct_pk,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &sr_proving_params,
                account_comm_key.clone(),
                &circuit_params,
                &ct_vk,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();
        println!("Prover time: {:?}, Verifier time: {:?}", prover_time, verifier_time);
    }

    #[test]
    fn counter_update_txn_by_sender() {
        // This is similar to receive txn as only account's counter is decreased, balance remains same.
        let mut rng = rand::thread_rng();

        let k = 12;
        const L: usize = 2000;
        let height = 3;

        let account_comm_key = setup_comm_key(&mut rng);

        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();

        let (circuit_params, ct_pk, ct_vk) = setup_curve_tree_params_for_state_transition::<L>(k, height);

        let (((sk_s, pk_s), (_, pk_s_e)), ((_, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100; // Amount for leg creation, not used in actual state transition

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account
        let mut account = AccountState::new(&mut rng, sk_s.0, asset_id, 1).unwrap();
        // Assume that account had some balance
        account.balance = 200;
        account.counter += 1;

        let (account_tree, sr_proving_params, _) = setup_account_tree_with_account_comm::<L>(&account, account_comm_key.clone(), Some(height as u8));

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = SenderCounterUpdateTxnProof::new::<_, PallasEc, VestaEc>(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &sr_proving_params,
            account_comm_key.clone(),
            &circuit_params,
            &ct_pk,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &sr_proving_params,
                account_comm_key.clone(),
                &circuit_params,
                &ct_vk,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();
        println!("Prover time: {:?}, Verifier time: {:?}", prover_time, verifier_time);
    }

    #[test]
    fn reverse_send_txn() {
        let mut rng = rand::thread_rng();

        let k = 12;
        const L: usize = 2000;
        let height = 3;

        let account_comm_key = setup_comm_key(&mut rng);

        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();

        let (circuit_params, ct_pk, ct_vk) = setup_curve_tree_params_for_affirm::<L>(k, height);

        let (((sk_s, pk_s), (_, pk_s_e)), ((_, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100;

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Sender account
        let mut account = AccountState::new(&mut rng, sk_s.0, asset_id, 1).unwrap();
        // Assume that account had some balance and it had sent the send transaction to increase its counter
        account.balance = 200;
        account.counter += 1;

        let (account_tree, sr_proving_params, _) = setup_account_tree_with_account_comm::<L>(&account, account_comm_key.clone(), Some(height as u8));

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_reversing_send(amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = SenderReverseTxnProof::new::<_, PallasEc, VestaEc>(
            &mut rng,
            amount,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &sr_proving_params,
            account_comm_key.clone(),
            &circuit_params,
            &ct_pk,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &sr_proving_params,
                account_comm_key.clone(),
                &circuit_params,
                &ct_vk,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();
        println!("Prover time: {:?}, Verifier time: {:?}", prover_time, verifier_time);
    }

    #[test]
    fn reverse_receive_txn() {
        // This is similar to receive txn as only account's counter is decreased, balance remains same.
        let mut rng = rand::thread_rng();

        let k = 12;
        const L: usize = 2000;
        let height = 3;

        let account_comm_key = setup_comm_key(&mut rng);

        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();

        let (circuit_params, ct_pk, ct_vk) = setup_curve_tree_params_for_state_transition::<L>(k, height);

        let (((_, pk_s), (_, pk_s_e)), ((sk_r, pk_r), (_, pk_r_e)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let amount = 100; // Amount for leg creation, not used in actual state transition

        let (_, leg_enc, leg_enc_rand) = setup_leg(
            &mut rng,
            pk_s.0,
            pk_r.0,
            pk_a_e.0,
            amount,
            asset_id,
            pk_s_e.0,
            pk_r_e.0,
            enc_key_gen,
            enc_gen,
        );

        // Receiver account with non-zero counter
        let mut account = AccountState::new(&mut rng, sk_r.0, asset_id, 1).unwrap();
        account.balance = 50;
        account.counter = 1;

        let (account_tree, sr_proving_params, _) = setup_account_tree_with_account_comm::<L>(&account, account_comm_key.clone(), Some(height as u8));

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_decreasing_counter(None).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0);

        let root = account_tree.root_node();

        let (proof, nullifier) = ReceiverCounterUpdateTxnProof::new::<_, PallasEc, VestaEc>(
            &mut rng,
            leg_enc.clone(),
            leg_enc_rand.clone(),
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &sr_proving_params,
            account_comm_key.clone(),
            &circuit_params,
            &ct_pk,
            enc_key_gen,
            enc_gen,
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                leg_enc,
                &root,
                updated_account_comm,
                nullifier,
                nonce,
                &sr_proving_params,
                account_comm_key.clone(),
                &circuit_params,
                &ct_vk,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();
        println!("Prover time: {:?}, Verifier time: {:?}", prover_time, verifier_time);
    }

    #[test]
    fn pob_with_auditor_as_verifier() {
        let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

        let account_comm_key = setup_comm_key(&mut rng);
        let asset_id = 1;

        let sig_key_gen = account_comm_key.sk_gen();
        let (sk, pk) = keygen_sig(&mut rng, sig_key_gen);

        // Account exists with some balance and pending txns
        let mut account = AccountState::new(&mut rng, sk.0, asset_id, 1).unwrap();
        account.balance = 1000;
        account.counter = 7;
        let account_comm = account.commit(account_comm_key).unwrap();

        let nonce = b"test-nonce";

        let proof = PobWithAuditorProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm,
            nonce,
            account_comm_key,
        )
            .unwrap();

        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                &pk.0,
                account_comm,
                nonce,
                account_comm_key,
            )
            .unwrap();
    }

    #[test]
    fn pob_with_anyone() {
        let mut rng = ChaCha20Rng::from_seed([0u8; 32]);

        let account_comm_key = setup_comm_key(&mut rng);
        let enc_key_gen = pallas::Point::random(&mut rng).to_affine();
        let enc_gen = pallas::Point::random(&mut rng).to_affine();

        let (((sk, pk), (_, pk_e)), ((_, pk_other), (_, pk_e_other)), ((_, _), (_, pk_a_e))) =
            setup_keys(&mut rng, account_comm_key.sk_gen(), enc_key_gen);

        let asset_id = 1;
        let num_pending_txns = 20;

        let mut account = AccountState::new(&mut rng, sk.0, asset_id, 1).unwrap();
        account.balance = 1000000;
        account.counter = num_pending_txns as u16;
        let account_comm = account.commit(account_comm_key).unwrap();

        let mut legs = vec![];
        let amount = 10;
        let mut pending_sent_amount = 0;
        let mut pending_recv_amount = 0;
        let mut sender_in_leg_indices = BTreeSet::new();
        let mut receiver_in_leg_indices = BTreeSet::new();

        for i in 0..num_pending_txns {
            if i % 2 == 0 {
                // for odd i, account is sender, for even i, its receiver
                pending_recv_amount += amount;
                receiver_in_leg_indices.insert(i);
                let leg =
                    Leg::new(pk_other.0, pk.0, vec![(true, pk_a_e.0)], amount, asset_id).unwrap();
                let (leg_enc, leg_enc_rand) = leg
                    .encrypt::<_, Blake2b512>(&mut rng, pk_e_other.0, pk_e.0, enc_key_gen, enc_gen)
                    .unwrap();
                legs.push((leg_enc, leg_enc_rand));
            } else {
                pending_sent_amount += amount;
                sender_in_leg_indices.insert(i);
                let leg =
                    Leg::new(pk.0, pk_other.0, vec![(true, pk_a_e.0)], amount, asset_id).unwrap();
                let (leg_enc, leg_enc_rand) = leg
                    .encrypt::<_, Blake2b512>(&mut rng, pk_e.0, pk_e_other.0, enc_key_gen, enc_gen)
                    .unwrap();
                legs.push((leg_enc, leg_enc_rand));
            }
        }

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let proof = PobWithAnyoneProof::new(
            &mut rng,
            &pk.0,
            &account,
            account_comm.clone(),
            legs.clone(),
            sender_in_leg_indices.clone(),
            receiver_in_leg_indices.clone(),
            pending_sent_amount,
            pending_recv_amount,
            nonce,
            account_comm_key.clone(),
            enc_key_gen,
            enc_gen,
        )
            .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();

        proof
            .verify(
                asset_id,
                account.balance,
                account.counter,
                &pk.0,
                account_comm,
                legs.into_iter().map(|l| l.0).collect(),
                sender_in_leg_indices,
                receiver_in_leg_indices,
                pending_sent_amount,
                pending_recv_amount,
                nonce,
                account_comm_key,
                enc_key_gen,
                enc_gen,
            )
            .unwrap();

        let verifier_time = clock.elapsed();

        println!("For {num_pending_txns} pending txns");
        // println!("total proof size = {}", proof.compressed_size());
        println!(
            "total prover time = {:?}, total verifier time = {:?}",
            prover_time, verifier_time
        );
    }

}
