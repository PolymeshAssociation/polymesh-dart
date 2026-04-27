use crate::account::AccountCommitmentKeyTrait;
use crate::auth_proofs::fee_account::AuthProofFeePayment;
use crate::auth_proofs::{AuthProofOnlySk, AuthProofOnlySkProtocol};
use crate::error::*;
use crate::util::{
    BPProof, append_auth_proof_and_get_challenge, get_verification_tuples_with_rng,
    handle_verification_tuples, make_ledger_nonce, prove_with_rng,
};
use crate::{
    ASSET_ID_LABEL, INCREASE_BAL_BY_LABEL, NONCE_LABEL, PK_LABEL, RE_RANDOMIZED_PATH_LABEL,
    ROOT_LABEL, TXN_CHALLENGE_LABEL, TXN_EVEN_LABEL, TXN_ODD_LABEL,
    UPDATED_ACCOUNT_COMMITMENT_LABEL, add_to_transcript,
};
use ark_dlog_gadget::dlog::DiscreteLogParameters;
use ark_ec::short_weierstrass::{Affine, Projective, SWCurveConfig};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec_divisors::DivisorCurve;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::collections::BTreeMap;
use ark_std::string::ToString;
use ark_std::{UniformRand, format, io::Write, vec::Vec};
use bulletproofs::r1cs::{ConstraintSystem, Prover, VerificationTuple, Verifier};
use curve_tree_relations::curve_tree::{Root, SelectAndRerandomizePathWithDivisorComms};
use curve_tree_relations::curve_tree_prover::CurveTreeWitnessPath;
use curve_tree_relations::parameters::SelRerandProofParametersNew;
use curve_tree_relations::range_proof::range_proof;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use polymesh_dart_common::{AssetId, Balance, FEE_BALANCE_BITS, MAX_FEE_BALANCE};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::{
    PokDiscreteLogProtocol, PokPedersenCommitment, PokPedersenCommitmentProtocol,
};
use schnorr_pok::partial::{
    Partial2PokPedersenCommitment, PartialPokDiscreteLog, PartialSchnorrResponse,
};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};
use zeroize::{Zeroize, ZeroizeOnDrop};

// Aiming for 3 possible workflows:
// W1 - Solo. Single prover has all witnesses including secret key(s)
//
// W2 - Parallel. Two provers, device (ledger) has the secret key(s) and host (computer) has everything else and they run in parallel, independently.
//
// W3 - Sequential. Two provers, device (ledger) has the secret key(s) and host (computer) has everything else and they run sequentially.
//    1. host does the pre-challenge phase (commits to randomness, writes all instance in transcript), generates challenge and sends it to device.
//    2. device creates the full proof using the challenge as its instance data
//    3. device sends the proof to host.
//    4. Host does its post challenge phase where it generates the proof. Host might decide to generate new challenge based on device's proof.
//
// Following allows all 3 workflows by orchestrating functions in the appropriate order and allowing args (gen_proof takes challenge where host could give any challenge of its choice)
//
// I don't see any technical reason to have W3 but still allowing it.

pub const FEE_AMOUNT_LABEL: &'static [u8; 10] = b"fee_amount";
pub const FEE_REG_TXN_LABEL: &'static [u8; 24] = b"fee_account_registration";

#[derive(
    Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize, Zeroize, ZeroizeOnDrop,
)]
pub struct FeeAccountState<G: AffineRepr> {
    pub pk: G,
    pub balance: Balance,
    /// This is 0 for PolyX is always revealed when paying fee
    /// Including the asset-id as we might need to support multiple fee currencies in future.
    pub asset_id: AssetId,
    /// Not committed in fee account commitment
    pub initial_rho: G::ScalarField,
    /// Not committed in fee account commitment
    pub initial_randomness: G::ScalarField,
    pub rho: G::ScalarField,
    pub randomness: G::ScalarField,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeeAccountStateCommitment<G: AffineRepr>(pub G);

impl<G: AffineRepr> FeeAccountState<G> {
    pub fn new<R: CryptoRngCore>(rng: &mut R, pk: G, balance: Balance, asset_id: AssetId) -> Self {
        let rho = G::ScalarField::rand(rng);
        let randomness = G::ScalarField::rand(rng);

        Self {
            pk,
            balance,
            asset_id,
            initial_rho: rho,
            initial_randomness: randomness,
            rho,
            randomness,
        }
    }

    pub fn commit(
        &self,
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<FeeAccountStateCommitment<G>> {
        let comm = self.comm(account_comm_key)?;
        Ok(FeeAccountStateCommitment((comm + self.pk).into_affine()))
    }

    pub fn get_state_for_topup(&self, amount: u64) -> Result<Self> {
        let new_balance = amount
            .checked_add(self.balance)
            .ok_or_else(|| Error::AmountTooLarge(u64::MAX))?;
        if new_balance > MAX_FEE_BALANCE {
            return Err(Error::AmountTooLarge(new_balance));
        }
        let mut new_state = self.clone();
        new_state.balance += amount;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn get_state_for_payment(&self, fee_amount: u64) -> Result<Self> {
        if fee_amount > self.balance {
            return Err(Error::AmountTooLarge(fee_amount));
        }
        let mut new_state = self.clone();
        new_state.balance -= fee_amount;
        new_state.refresh_randomness_for_state_change();
        Ok(new_state)
    }

    pub fn refresh_randomness_for_state_change(&mut self) {
        // This isn't enforced in the verification and only here to let users have all randomness derived from a
        // "seed" such that they can recover. The cost is 2 extra items in the commitment.
        // An alternative could be a user held counter not part of state used to derive the randomness but above keeps
        // it similar to main account commitment.
        self.rho *= self.initial_rho;
        self.randomness *= self.initial_randomness;
    }

    pub fn nullifier(&self, comm_key: &impl AccountCommitmentKeyTrait<G>) -> G {
        (comm_key.rho_gen() * self.rho).into()
    }

    pub fn asset_id(&self) -> AssetId {
        self.asset_id
    }

    pub fn comm(&self, account_comm_key: impl AccountCommitmentKeyTrait<G>) -> Result<G::Group> {
        let comm = G::Group::msm(
            &[
                account_comm_key.balance_gen(),
                account_comm_key.asset_id_gen(),
                account_comm_key.rho_gen(),
                account_comm_key.randomness_gen(),
            ],
            &[
                G::ScalarField::from(self.balance),
                G::ScalarField::from(self.asset_id),
                self.rho,
                self.randomness,
            ],
        )
        .map_err(Error::size_mismatch)?;
        Ok(comm)
    }
}

// A non-split (single prover) proof proves that the account commitment is correctly formed and that prover knows the
// secret key, nullifier secret key, rho, commitment randomness, i.e. knowledge of opening
// of a commitment of the form `C = G_{aff} * sk + G_i * rho + G_j * s + ....`
//
// A split proof is created by 2 provers, one prover (more secure device like ledger) knows the secret key (might know other witnesses)
// and second prover does not know secret key but knows other witnesses. The split proof is then combination of 2 proofs, first prover's
// proof of knowledge of secret key in the public key and the second prover's proof of knowledge of other witnesses in `C' = G_i * rho + G_j * s + ....`
// Now the verifier can check that `C = C' + pk` as `pk(=G * sk)` is public

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RegTxnWithoutSkProof<G: AffineRepr>(pub PokPedersenCommitment<G>);

#[derive(Clone)]
pub struct RegTxnProofWithoutSkProtocol<G: AffineRepr> {
    pub comm_protocol: PokPedersenCommitmentProtocol<G>,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct RegTxnProof<G: AffineRepr> {
    pub partial: RegTxnWithoutSkProof<G>,
    pub auth_proof: AuthProofOnlySk<G>,
}

impl<G: AffineRepr> RegTxnProofWithoutSkProtocol<G> {
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        pk: G,
        account: &FeeAccountState<G>,
        account_commitment: FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        Self::init_with_given_transcript(
            rng,
            pk,
            account,
            account_commitment,
            nonce,
            account_comm_key,
            &mut transcript,
        )
    }

    /// Initial sigma protocol and add to transcript
    pub fn init_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        pk: G,
        account: &FeeAccountState<G>,
        account_commitment: FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            account.asset_id(),
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk
        );

        // D = pk + g_balance * balance + g_asset_id * asset_id
        let D = pk.into_group()
            + (account_comm_key.balance_gen() * G::ScalarField::from(account.balance))
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(account.asset_id()));

        let mut rho_blinding = G::ScalarField::rand(rng);
        let mut randomness_blinding = G::ScalarField::rand(rng);

        // For proving Comm - D = g_rho * rho + g_randomness * randomness
        let comm_protocol = PokPedersenCommitmentProtocol::init(
            account.rho,
            rho_blinding,
            &account_comm_key.rho_gen(),
            account.randomness,
            randomness_blinding,
            &account_comm_key.randomness_gen(),
        );

        rho_blinding.zeroize();
        randomness_blinding.zeroize();

        let reduced_acc_comm = (account_commitment.0.into_group() - D).into_affine();
        comm_protocol.challenge_contribution(
            &account_comm_key.rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript,
        )?;

        Ok(Self { comm_protocol })
    }

    /// Response for sigma protocol
    pub fn gen_proof(self, challenge: &G::ScalarField) -> RegTxnWithoutSkProof<G> {
        RegTxnWithoutSkProof(self.comm_protocol.gen_proof(challenge))
    }

    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        pk: G,
        account: &FeeAccountState<G>,
        account_commitment: FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<RegTxnWithoutSkProof<G>> {
        let mut transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        let proto = Self::init_with_given_transcript(
            rng,
            pk,
            account,
            account_commitment,
            nonce,
            account_comm_key,
            &mut transcript,
        )?;
        let challenge_h = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        let proof = proto.gen_proof(&challenge_h);
        Ok(proof)
    }
}

impl<G: AffineRepr> RegTxnWithoutSkProof<G> {
    pub fn challenge_contribution(
        &self,
        pk: &G,
        balance: Balance,
        asset_id: AssetId,
        account_commitment: &FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: &mut MerlinTranscript,
    ) -> Result<G> {
        add_to_transcript!(
            transcript,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            asset_id,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            account_commitment,
            PK_LABEL,
            pk
        );

        // D = pk + g_balance * balance + g_asset_id * asset_id
        let D = pk.into_group()
            + (account_comm_key.balance_gen() * G::ScalarField::from(balance))
            + (account_comm_key.asset_id_gen() * G::ScalarField::from(asset_id));

        let reduced_acc_comm = (account_commitment.0.into_group() - D).into_affine();
        self.0.challenge_contribution(
            &account_comm_key.rho_gen(),
            &account_comm_key.randomness_gen(),
            &reduced_acc_comm,
            &mut transcript,
        )?;
        Ok(reduced_acc_comm)
    }

    pub fn verify_with_given_transcript(
        &self,
        reduced_acc_comm: G,
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        challenge: &G::ScalarField,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        verify_or_rmc_3!(
            rmc,
            self.0,
            "Account commitment proof verification failed",
            reduced_acc_comm,
            account_comm_key.rho_gen(),
            account_comm_key.randomness_gen(),
            challenge,
        );

        Ok(())
    }
}

impl<G: AffineRepr> RegTxnProof<G> {
    pub fn new<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        account: &FeeAccountState<G>,
        account_commitment: FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<Self> {
        let mut transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        Self::new_with_given_transcript(
            rng,
            sk,
            account,
            account_commitment,
            nonce,
            account_comm_key,
            &mut transcript,
        )
    }

    pub fn new_with_given_transcript<R: CryptoRngCore>(
        rng: &mut R,
        sk: G::ScalarField,
        account: &FeeAccountState<G>,
        account_commitment: FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: &mut MerlinTranscript,
    ) -> Result<Self> {
        let pk = account.pk;
        let sk_gen = account_comm_key.sk_gen();
        let partial = RegTxnProofWithoutSkProtocol::init_with_given_transcript(
            rng,
            pk,
            account,
            account_commitment,
            nonce,
            account_comm_key,
            &mut transcript,
        )?;

        let auth_protocol = AuthProofOnlySkProtocol::init(rng, sk, &pk, &sk_gen, &mut transcript)?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);
        let auth_proof = auth_protocol.gen_proof(&challenge);

        let partial = partial.gen_proof(&challenge);

        Ok(Self {
            partial,
            auth_proof,
        })
    }

    pub fn verify(
        &self,
        pk: &G,
        balance: Balance,
        asset_id: AssetId,
        account_commitment: &FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        self.verify_with_given_transcript(
            pk,
            balance,
            asset_id,
            account_commitment,
            nonce,
            account_comm_key,
            &mut transcript,
            rmc,
        )
    }

    pub fn verify_with_given_transcript(
        &self,
        pk: &G,
        balance: Balance,
        asset_id: AssetId,
        account_commitment: &FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
        mut transcript: &mut MerlinTranscript,
        mut rmc: Option<&mut RandomizedMultChecker<G>>,
    ) -> Result<()> {
        let reduced_acc_comm = self.partial.challenge_contribution(
            pk,
            balance,
            asset_id,
            account_commitment,
            nonce,
            account_comm_key.clone(),
            &mut transcript,
        )?;

        self.auth_proof
            .challenge_contribution(pk, &account_comm_key.sk_gen(), &mut transcript)?;

        let challenge = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        self.auth_proof.verify_given_challenge(
            pk,
            &account_comm_key.sk_gen(),
            &challenge,
            rmc.as_deref_mut(),
        )?;

        self.partial.verify_with_given_transcript(
            reduced_acc_comm,
            account_comm_key,
            &challenge,
            rmc.as_deref_mut(),
        )
    }

    pub fn verify_split(
        &self,
        pk: &G,
        balance: Balance,
        asset_id: AssetId,
        account_commitment: &FeeAccountStateCommitment<G>,
        nonce: &[u8],
        account_comm_key: impl AccountCommitmentKeyTrait<G>,
    ) -> Result<()> {
        let mut transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        let reduced_acc_comm = self.partial.challenge_contribution(
            pk,
            balance,
            asset_id,
            account_commitment,
            nonce,
            account_comm_key.clone(),
            &mut transcript,
        )?;
        let challenge_h_v = transcript.challenge_scalar::<G::ScalarField>(TXN_CHALLENGE_LABEL);

        let ledger_nonce_v = make_ledger_nonce(&challenge_h_v, nonce)?;

        self.auth_proof
            .verify(*pk, &ledger_nonce_v, &account_comm_key.sk_gen(), None)?;

        let challenge_h_final_v =
            append_auth_proof_and_get_challenge(&self.auth_proof, &mut transcript)?;

        self.partial.verify_with_given_transcript(
            reduced_acc_comm,
            account_comm_key,
            &challenge_h_final_v,
            None,
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeeAccountTopupTxnWithoutSkProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub r1cs_proof: Option<BPProof<G0, G1>>,
    /// This contains the old account state, but re-randomized (as re-randomized leaf)
    pub re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
    /// Schnorr proof for both account commitments (T-values + responses), without secret key
    pub account_comm_proof: AccountCommitmentsWithoutSkProof<G0>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PartialPokDiscreteLog<Affine<G0>>,
    /// Commitment to the balance in new account commitment (which becomes new leaf) used with Bulletproof
    pub comm_new_bal: Affine<G0>,
    /// Response for Sigma protocol for proving knowledge of balance in `comm_new_bal`
    pub resp_bp: Partial2PokPedersenCommitment<Affine<G0>>,
}

pub struct FeeAccountTopupTxnWithoutSkProtocol<
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
    const L: usize,
> {
    acc_comm: AccountCommitmentsWithoutSkProtocol<G0>,
    t_null: PokDiscreteLogProtocol<Affine<G0>>,
    t_bp: PokPedersenCommitmentProtocol<Affine<G0>>,
    re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
    comm_new_bal: Affine<G0>,
    rerandomization: F0,
    old_account_state: FeeAccountState<Affine<G0>>,
    new_account_state: FeeAccountState<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeeAccountTopupTxnWithoutSkProtocol<F0, F1, G0, G1, L>
{
    /// Initializes sigma protocol, derives the challenge, creates proof for them and the R1CS proof.
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        pk: &Affine<G0>,
        increase_bal_by: Balance,
        account: FeeAccountState<Affine<G0>>,
        updated_account: FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        FeeAccountTopupTxnWithoutSkProof<L, F0, F1, G0, G1>,
        Affine<G0>,
    )> {
        let (proto, mut even_prover, odd_prover, nullifier) =
            Self::init::<_, Parameters0, Parameters1>(
                rng,
                pk,
                increase_bal_by,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
            )?;

        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        let mut partial = proto.gen_proof(&challenge_h)?;

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((partial, nullifier))
    }

    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        pk: &Affine<G0>,
        increase_bal_by: Balance,
        account: FeeAccountState<Affine<G0>>,
        updated_account: FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Self,
        Prover<'a, MerlinTranscript, Affine<G0>>,
        Prover<'a, MerlinTranscript, Affine<G1>>,
        Affine<G0>,
    )> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.sl_params.pc_gens(),
            even_transcript,
        );
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.sl_params.pc_gens(),
            odd_transcript,
        );

        let (proto, nullifier) = Self::init_with_given_prover::<_, Parameters0, Parameters1>(
            rng,
            pk,
            increase_bal_by,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            &mut even_prover,
            &mut odd_prover,
        )?;

        Ok((proto, even_prover, odd_prover, nullifier))
    }

    pub fn init_with_given_prover<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        pk: &Affine<G0>,
        increase_bal_by: Balance,
        account: FeeAccountState<Affine<G0>>,
        updated_account: FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        let (re_randomized_path, rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget_new::<_, Parameters0, Parameters1>(
                even_prover,
                odd_prover,
                account_tree_params,
                rng,
            )?;

        let mut transcript = even_prover.transcript();

        add_to_transcript!(
            transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
            NONCE_LABEL,
            nonce,
            PK_LABEL,
            pk,
            ASSET_ID_LABEL,
            account.asset_id(),
            INCREASE_BAL_BY_LABEL,
            increase_bal_by,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        let acc_comm =
            AccountCommitmentsWithoutSkProtocol::init(rng, account_comm_key.clone(), b_blinding);

        let mut comm_bp_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.rho_gen();
        let nullifier = (nullifier_gen * account.rho).into_affine();

        let new_balance = F0::from(updated_account.balance);

        acc_comm.t_acc_old.challenge_contribution(&mut transcript)?;
        acc_comm.t_acc_new.challenge_contribution(&mut transcript)?;

        let acc_old = <Projective<G0> as VariableBaseMSM>::msm_unchecked(
            &acc_old_gens_without_sk(&account_comm_key, b_blinding),
            &[
                new_balance,
                account.rho,
                account.randomness,
                rerandomization,
            ],
        )
        .into_affine();
        let acc_new = <Projective<G0> as VariableBaseMSM>::msm_unchecked(
            &acc_new_gens_without_sk(&account_comm_key),
            &[new_balance, updated_account.rho, updated_account.randomness],
        )
        .into_affine();

        acc_old.serialize_compressed(&mut transcript)?;
        acc_new.serialize_compressed(&mut transcript)?;

        let t_null =
            PokDiscreteLogProtocol::init(account.rho, acc_comm.old_rho_blinding, &nullifier_gen);
        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        // Drop reference to borrow even_prover below
        let _ = transcript;

        // Range proof on new balance to ensure it's non-negative.
        let (comm_new_bal, new_bal_var) = even_prover.commit(new_balance, comm_bp_blinding);
        range_proof(
            even_prover,
            new_bal_var.into(),
            Some(updated_account.balance as u128),
            FEE_BALANCE_BITS.into(),
        )?;

        let t_bp = PokPedersenCommitmentProtocol::init(
            new_balance,
            acc_comm.new_balance_blinding,
            &account_tree_params.even_parameters.sl_params.pc_gens().B,
            comm_bp_blinding,
            F0::rand(rng),
            &account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
        );

        comm_bp_blinding.zeroize();

        let mut transcript = even_prover.transcript();

        t_bp.challenge_contribution(
            &account_tree_params.even_parameters.sl_params.pc_gens().B,
            &account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
            &comm_new_bal,
            &mut transcript,
        )?;

        Ok((
            Self {
                acc_comm,
                t_null,
                t_bp,
                re_randomized_path,
                comm_new_bal,
                rerandomization,
                old_account_state: account,
                new_account_state: updated_account,
            },
            nullifier,
        ))
    }

    pub fn gen_proof(
        mut self,
        challenge: &F0,
    ) -> Result<FeeAccountTopupTxnWithoutSkProof<L, F0, F1, G0, G1>> {
        let account_comm_proof = self.acc_comm.gen_proof(
            challenge,
            F0::from(self.new_account_state.balance),
            self.old_account_state.rho,
            self.old_account_state.randomness,
            self.rerandomization,
            self.new_account_state.rho,
            self.new_account_state.randomness,
        )?;

        self.rerandomization.zeroize();

        let resp_null = self.t_null.gen_partial_proof();
        let resp_bp = self.t_bp.gen_partial2_proof(challenge);

        Ok(FeeAccountTopupTxnWithoutSkProof {
            r1cs_proof: None,
            re_randomized_path: self.re_randomized_path,
            account_comm_proof,
            resp_null,
            comm_new_bal: self.comm_new_bal,
            resp_bp,
        })
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeeAccountTopupTxnWithoutSkProof<L, F0, F1, G0, G1>
{
    pub fn challenge_contribution<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Verifier<MerlinTranscript, Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G1>>,
    )> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);
        self.challenge_contribution_with_verifier::<Parameters0, Parameters1>(
            pk,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            &mut even_verifier,
            &mut odd_verifier,
        )?;
        Ok((even_verifier, odd_verifier))
    }

    pub fn challenge_contribution_with_verifier<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
    ) -> Result<()> {
        self.re_randomized_path
            .select_and_rerandomize_verifier_gadget::<Parameters0, Parameters1>(
                root,
                even_verifier,
                odd_verifier,
                account_tree_params,
            )?;

        let mut transcript = even_verifier.transcript();

        add_to_transcript!(
            transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            self.re_randomized_path,
            NONCE_LABEL,
            nonce,
            PK_LABEL,
            pk,
            ASSET_ID_LABEL,
            asset_id,
            INCREASE_BAL_BY_LABEL,
            increase_bal_by,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let nullifier_gen = account_comm_key.rho_gen();

        self.account_comm_proof
            .t_acc_old
            .serialize_compressed(&mut transcript)?;
        self.account_comm_proof
            .t_acc_new
            .serialize_compressed(&mut transcript)?;

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();
        let reduce = (pk.into_group() + asset_id_comm).into_affine();
        let acc_old = (self
            .re_randomized_path
            .path
            .get_rerandomized_leaf()
            .into_group()
            - reduce
            + (account_comm_key.balance_gen() * F0::from(increase_bal_by)))
        .into_affine();
        let acc_new = (updated_account_commitment.0.into_group() - reduce).into_affine();
        acc_old.serialize_compressed(&mut transcript)?;
        acc_new.serialize_compressed(&mut transcript)?;

        self.resp_null
            .challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        // Drop reference to borrow even_verifier below
        let _ = transcript;

        let new_bal_var = even_verifier.commit(self.comm_new_bal);

        range_proof(
            even_verifier,
            new_bal_var.into(),
            None,
            FEE_BALANCE_BITS.into(),
        )?;

        let mut transcript = even_verifier.transcript();

        self.resp_bp.challenge_contribution(
            &account_tree_params.even_parameters.sl_params.pc_gens().B,
            &account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
            &self.comm_new_bal,
            &mut transcript,
        )?;

        Ok(())
    }

    pub fn verify_with_challenge<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        challenge: &F0,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        if self.account_comm_proof.resp_acc_old.len() != 4 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                4,
                self.account_comm_proof.resp_acc_old.len(),
            ));
        }
        if self.account_comm_proof.resp_acc_new.responses.len() != 2 {
            return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
                2,
                self.account_comm_proof.resp_acc_new.responses.len(),
            ));
        }

        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();

        let increase_bal_by = F0::from(increase_bal_by);

        let issuer_pk_proj = pk.into_group();
        let reduce = asset_id_comm + issuer_pk_proj;
        let acc_old = self
            .re_randomized_path
            .path
            .get_rerandomized_leaf()
            .into_group()
            - reduce
            + (account_comm_key.balance_gen() * increase_bal_by);
        let acc_old = acc_old.into_affine();

        let acc_new = (updated_account_commitment.0.into_group() - reduce).into_affine();
        let mut missing_resps = BTreeMap::new();
        missing_resps.insert(0, self.account_comm_proof.resp_acc_old.0[0]);

        let nullifier_gen = account_comm_key.rho_gen();

        verify_schnorr_resp_or_rmc!(
            rmc,
            self.account_comm_proof.resp_acc_old,
            acc_old_gens_without_sk(
                &account_comm_key,
                account_tree_params
                    .even_parameters
                    .sl_params
                    .pc_gens()
                    .B_blinding,
            )
            .to_vec(),
            acc_old,
            self.account_comm_proof.t_acc_old,
            challenge,
        );
        verify_partial_schnorr_resp_or_rmc!(
            rmc,
            self.account_comm_proof.resp_acc_new,
            acc_new_gens_without_sk(&account_comm_key).to_vec(),
            acc_new,
            self.account_comm_proof.t_acc_new,
            challenge,
            missing_resps,
        );
        // rho matches the one in nullifier
        verify_or_rmc_2!(
            rmc,
            self.resp_null,
            "Nullifier verification failed",
            nullifier,
            nullifier_gen,
            challenge,
            &self.account_comm_proof.resp_acc_old.0[1],
        );
        // Amount matches the one in response for old account commitment
        verify_or_rmc_3!(
            rmc,
            self.resp_bp,
            "Sigma protocol for Bulletproof commitment failed",
            self.comm_new_bal,
            account_tree_params.even_parameters.sl_params.pc_gens().B,
            account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
            challenge,
            &self.account_comm_proof.resp_acc_old.0[0],
        );
        Ok(())
    }

    pub fn verify_sigma_protocols<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Verifier<MerlinTranscript, Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G1>>,
    )> {
        let (mut even_verifier, odd_verifier) = self
            .challenge_contribution::<Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
            )?;
        let challenge_h = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        self.verify_with_challenge::<Parameters0, Parameters1>(
            pk,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            account_tree_params,
            account_comm_key,
            &challenge_h,
            None,
        )?;
        Ok((even_verifier, odd_verifier))
    }

    /// Returns R1CS verification tuples after sigma check.
    /// Equivalent to `verify` (Phase 1 + sigma) followed by `get_verification_tuples_with_rng`.
    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let (even_verifier, odd_verifier) = self
            .verify_sigma_protocols::<Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
            )?;
        let r1cs_proof = self
            .r1cs_proof
            .as_ref()
            .ok_or_else(|| Error::ProofVerificationError("R1CS proof is missing".to_string()))?;
        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )
    }

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let (even_tuple, odd_tuple) = self
            .verify_and_return_tuples::<_, Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                rng,
            )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }
}

/// Topup proof done in solo mode
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeeAccountTopupTxnProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// Proof that account commitments transitioned correctly and range proof works
    pub partial: FeeAccountTopupTxnWithoutSkProof<L, F0, F1, G0, G1>,
    /// Authorization proof for proving knowledge of secret key in the public key
    pub auth_proof: AuthProofOnlySk<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeeAccountTopupTxnProof<L, F0, F1, G0, G1>
{
    /// `pk` is the public key of the investor who is topping up his fee account
    /// and has the same secret key as the one in `account`
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        sk: G0::ScalarField,
        increase_bal_by: Balance,
        account: &FeeAccountState<Affine<G0>>,
        updated_account: &FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(Self, Affine<G0>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.sl_params.pc_gens(),
            even_transcript,
        );
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.sl_params.pc_gens(),
            odd_transcript,
        );

        let (mut proof, nullifier) = Self::new_with_given_prover::<_, Parameters0, Parameters1>(
            rng,
            sk,
            increase_bal_by,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            &mut even_prover,
            &mut odd_prover,
        )?;

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;

        proof.partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((proof, nullifier))
    }

    pub fn new_with_given_prover<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        sk: G0::ScalarField,
        increase_bal_by: Balance,
        account: &FeeAccountState<Affine<G0>>,
        updated_account: &FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_correct_account_state(account, updated_account, increase_bal_by, false)?;

        let pk_gen = account_comm_key.sk_gen();

        // Initialize proving for all except secret key
        let (partial_proto, nullifier) =
            FeeAccountTopupTxnWithoutSkProtocol::init_with_given_prover::<
                _,
                Parameters0,
                Parameters1,
            >(
                rng,
                &account.pk,
                increase_bal_by,
                account.clone(),
                updated_account.clone(),
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                even_prover,
                odd_prover,
            )?;

        // Initialize proving for secret key
        let mut transcript = even_prover.transcript();
        let auth_protocol =
            AuthProofOnlySkProtocol::init(rng, sk, &account.pk, &pk_gen, &mut transcript)?;

        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Generate proof for both
        let partial = partial_proto.gen_proof(&challenge)?;
        let auth_proof = auth_protocol.gen_proof(&challenge);

        Ok((
            Self {
                auth_proof,
                partial,
            },
            nullifier,
        ))
    }

    pub fn verify_split<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };

        let (even_tuple, odd_tuple) = self
            .verify_split_and_return_tuples::<R, Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                rng,
                rmc_0,
            )?;

        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    pub fn verify_split_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let (mut even_verifier, odd_verifier) = self
            .partial
            .challenge_contribution::<Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
            )?;

        let challenge_h_v = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let ledger_nonce_v = make_ledger_nonce(&challenge_h_v, nonce)?;

        self.auth_proof
            .verify(pk, &ledger_nonce_v, &account_comm_key.sk_gen(), None)?;

        let challenge_h_final_v: F0 =
            append_auth_proof_and_get_challenge(&self.auth_proof, even_verifier.transcript())?;

        self.partial
            .verify_with_challenge::<Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                account_tree_params,
                account_comm_key,
                &challenge_h_final_v,
                rmc,
            )?;

        let r1cs =
            self.partial.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;

        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs.even_proof,
            &r1cs.odd_proof,
            rng,
        )
    }

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };

        let (even_tuple, odd_tuple) = self
            .verify_and_return_tuples::<R, Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                rng,
                rmc_0,
            )?;

        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    /// Verifies the proof except for final Bulletproof verification
    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);
        self.verify_sigma_protocols_and_enforce_constraints::<Parameters0, Parameters1>(
            pk,
            asset_id,
            increase_bal_by,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            &mut even_verifier,
            &mut odd_verifier,
            rmc,
        )?;
        let r1cs_proof =
            self.partial.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;

        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )
    }

    pub fn verify_sigma_protocols_and_enforce_constraints<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        pk: Affine<G0>,
        asset_id: AssetId,
        increase_bal_by: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let pk_gen = account_comm_key.sk_gen();

        // Partial challenge contribution: re-rand gadget, public inputs, partial T-values, BP
        self.partial
            .challenge_contribution_with_verifier::<Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                even_verifier,
                odd_verifier,
            )?;

        // Auth challenge contribution + challenge derivation
        let mut transcript = even_verifier.transcript();
        self.auth_proof
            .challenge_contribution(&pk, &pk_gen, &mut transcript)?;
        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Verify partial sigma protocols
        self.partial
            .verify_with_challenge::<Parameters0, Parameters1>(
                pk,
                asset_id,
                increase_bal_by,
                updated_account_commitment,
                nullifier,
                account_tree_params,
                account_comm_key,
                &challenge,
                rmc.as_mut().map(|r| &mut **r),
            )?;

        // Verify auth sigma protocol
        self.auth_proof
            .verify_given_challenge(&pk, &pk_gen, &challenge, None)?;

        Ok(())
    }
}

/// Proves correctness of both full account commitments, i.e. including secret key
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountCommitmentsProof<G: SWCurveConfig + Clone + Copy> {
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_old: Affine<G>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_old: SchnorrResponse<Affine<G>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: PartialSchnorrResponse<Affine<G>>,
}

/// Proves correctness of both account commitments but without secret key
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountCommitmentsWithoutSkProof<G: SWCurveConfig + Clone + Copy> {
    /// Commitment to randomness for proving knowledge of re-randomized leaf using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_old: Affine<G>,
    /// Commitment to randomness for proving knowledge of new account commitment (which becomes new leaf) using Schnorr protocol (step 1 of Schnorr)
    pub t_acc_new: Affine<G>,
    /// Response for proving knowledge of re-randomized leaf using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_old: SchnorrResponse<Affine<G>>,
    /// Response for proving knowledge of new account commitment using Schnorr protocol (step 3 of Schnorr)
    pub resp_acc_new: PartialSchnorrResponse<Affine<G>>,
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsWithoutSkProof<G> {
    /// Verify account commitment Schnorr proofs (without sk).
    pub fn verify_with_challenge(
        &self,
        y_old: Affine<G>,
        y_new: Affine<G>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
        blinding_gen: Affine<G>,
        challenge: &G::ScalarField,
        rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
    ) -> Result<()> {
        verify_acc_comm(
            &self.resp_acc_old,
            &self.resp_acc_new,
            self.t_acc_old,
            self.t_acc_new,
            y_old,
            y_new,
            account_comm_key,
            blinding_gen,
            false,
            challenge,
            rmc,
        )
    }
}

/// Proves correctness of both account commitments when secret key is not known to the host
/// Used for workflows W2 and W3
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AccountCommitmentsSplitProof<G: SWCurveConfig + Clone + Copy> {
    /// Proves knowledge of secret key in account commitments
    pub auth_proof: AuthProofFeePayment<Affine<G>>,
    /// Proves knowledge of values other than secret key in account commitments
    pub host_proof: AccountCommitmentsWithoutSkProof<G>,
}

#[derive(Clone, Debug, Zeroize, ZeroizeOnDrop)]
pub struct AccountCommitmentsWithoutSkProtocol<G: SWCurveConfig + Clone + Copy> {
    pub t_acc_old: SchnorrCommitment<Affine<G>>,
    pub t_acc_new: SchnorrCommitment<Affine<G>>,
    /// Blindings shared with partial protocol
    pub new_balance_blinding: G::ScalarField,
    pub old_rho_blinding: G::ScalarField,
    /// Internal blindings (not shared with partial)
    pub new_rho_blinding: G::ScalarField,
    pub old_s_blinding: G::ScalarField,
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsWithoutSkProtocol<G> {
    /// Creates all blindings internally. Shared blindings (`new_balance_blinding`, `old_rho_blinding`)
    /// can be read from the struct and passed to the partial protocol.
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
        blinding_gen: Affine<G>,
    ) -> Self {
        let (
            t_acc_old,
            t_acc_new,
            new_balance_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_s_blinding,
        ) = init_acc_comm(rng, account_comm_key, blinding_gen, None, None);

        Self {
            t_acc_old,
            t_acc_new,
            new_balance_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_s_blinding,
        }
    }

    /// Generate the host's portion of the split proof.
    /// Witnesses for old: [new_balance, old_rho, old_randomness, host_rerandomization] (4 generators);
    /// for new: rho at index 1, host_new_randomness at index 2 (balance at 0 shared from old).
    pub fn gen_proof(
        self,
        challenge: &G::ScalarField,
        new_balance: G::ScalarField,
        old_rho: G::ScalarField,
        old_randomness: G::ScalarField,
        host_rerandomization: G::ScalarField,
        new_rho: G::ScalarField,
        host_new_randomness: G::ScalarField,
    ) -> Result<AccountCommitmentsWithoutSkProof<G>> {
        let (resp_acc_old, resp_acc_new) = resp_acc_comm(
            &self.t_acc_old,
            &self.t_acc_new,
            challenge,
            None,
            new_balance,
            old_rho,
            old_randomness,
            host_rerandomization,
            new_rho,
            host_new_randomness,
        )?;
        Ok(AccountCommitmentsWithoutSkProof {
            t_acc_old: self.t_acc_old.t,
            t_acc_new: self.t_acc_new.t,
            resp_acc_old,
            resp_acc_new,
        })
    }
}

/// When all values in commitment including secret key are known to host (solo)
#[derive(Clone, Debug)]
pub struct AccountCommitmentsProtocol<G: SWCurveConfig + Clone + Copy> {
    pub t_acc_old: SchnorrCommitment<Affine<G>>,
    pub t_acc_new: SchnorrCommitment<Affine<G>>,
    /// Blindings stored so caller can pass shared ones to partial protocol
    pub sk_blinding: G::ScalarField,
    pub new_balance_blinding: G::ScalarField,
    pub old_rho_blinding: G::ScalarField,
    pub new_rho_blinding: G::ScalarField,
    pub old_s_blinding: G::ScalarField,
    pub new_s_blinding: G::ScalarField,
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsProtocol<G> {
    pub fn init<R: CryptoRngCore>(
        rng: &mut R,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
        blinding_gen: Affine<G>,
    ) -> Self {
        let sk_blinding = G::ScalarField::rand(rng);
        let new_s_blinding = G::ScalarField::rand(rng);
        let (
            t_acc_old,
            t_acc_new,
            new_balance_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_s_blinding,
        ) = init_acc_comm(
            rng,
            account_comm_key,
            blinding_gen,
            Some(sk_blinding),
            Some(new_s_blinding),
        );

        Self {
            t_acc_old,
            t_acc_new,
            sk_blinding,
            new_balance_blinding,
            old_rho_blinding,
            new_rho_blinding,
            old_s_blinding,
            new_s_blinding,
        }
    }

    pub fn challenge_contribution<W: Write>(&self, writer: &mut W) -> Result<()> {
        self.t_acc_old.challenge_contribution(&mut *writer)?;
        self.t_acc_new.challenge_contribution(writer)?;
        Ok(())
    }

    pub fn gen_proof(
        self,
        challenge: &G::ScalarField,
        sk: G::ScalarField,
        new_balance: G::ScalarField,
        old_rho: G::ScalarField,
        old_randomness: G::ScalarField,
        rerandomization: G::ScalarField,
        new_rho: G::ScalarField,
        new_randomness: G::ScalarField,
    ) -> Result<AccountCommitmentsProof<G>> {
        let (resp_acc_old, resp_acc_new) = resp_acc_comm(
            &self.t_acc_old,
            &self.t_acc_new,
            challenge,
            Some(sk),
            new_balance,
            old_rho,
            old_randomness,
            rerandomization,
            new_rho,
            new_randomness,
        )?;
        Ok(AccountCommitmentsProof {
            t_acc_old: self.t_acc_old.t,
            t_acc_new: self.t_acc_new.t,
            resp_acc_old,
            resp_acc_new,
        })
    }
}

impl<G: SWCurveConfig + Clone + Copy> AccountCommitmentsProof<G> {
    pub fn challenge_contribution<W: Write>(&self, writer: &mut W) -> Result<()> {
        self.t_acc_old.serialize_compressed(&mut *writer)?;
        self.t_acc_new.serialize_compressed(writer)?;
        Ok(())
    }

    /// Verify account commitment Schnorr proofs (with sk).
    pub fn verify_with_challenge(
        &self,
        y_old: Affine<G>,
        y_new: Affine<G>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
        blinding_gen: Affine<G>,
        challenge: &G::ScalarField,
        rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
    ) -> Result<()> {
        verify_acc_comm(
            &self.resp_acc_old,
            &self.resp_acc_new,
            self.t_acc_old,
            self.t_acc_new,
            y_old,
            y_new,
            account_comm_key,
            blinding_gen,
            true,
            challenge,
            rmc,
        )
    }
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeePaymentWithoutCommitmentsProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    /// This contains the old account state, but re-randomized (as re-randomized leaf)
    pub re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
    /// Commitment to randomness and response for proving correctness of nullifier using Schnorr protocol (step 1 and 3 of Schnorr)
    pub resp_null: PartialPokDiscreteLog<Affine<G0>>,
    pub comm_new_bal: Affine<G0>,
    pub resp_bp: Partial2PokPedersenCommitment<Affine<G0>>,
    pub r1cs_proof: Option<BPProof<G0, G1>>,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeePaymentProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub partial: FeePaymentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
    pub commitment_proof: AccountCommitmentsProof<G0>,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct FeePaymentSplitProof<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: SWCurveConfig<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: SWCurveConfig<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub partial: FeePaymentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
    pub commitment_proof: AccountCommitmentsSplitProof<G0>,
}

pub struct FeePaymentWithoutCommitmentsProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    pub t_null: PokDiscreteLogProtocol<Affine<G0>>,
    pub t_bp: PokPedersenCommitmentProtocol<Affine<G0>>,
    pub re_randomized_path: SelectAndRerandomizePathWithDivisorComms<L, G0, G1>,
    pub rerandomization: F0,
    pub comm_new_bal: Affine<G0>,
    pub old_account_state: FeeAccountState<Affine<G0>>,
    pub new_account_state: FeeAccountState<Affine<G0>>,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeePaymentWithoutCommitmentsProtocol<L, F0, F1, G0, G1>
{
    /// Calls `init_with_given_prover`, derives the challenge, generates the partial proof and the R1CS proof.
    /// Returns `(partial_with_r1cs, nullifier, challenge_h)`.
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        fee_amount: Balance,
        account: FeeAccountState<Affine<G0>>,
        updated_account: FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        FeePaymentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
        Affine<G0>,
        F0,
    )> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.sl_params.pc_gens(),
            even_transcript,
        );
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.sl_params.pc_gens(),
            odd_transcript,
        );

        let mut new_balance_blinding = F0::rand(rng);
        let mut old_rho_blinding = F0::rand(rng);

        let (proto, nullifier) = Self::init_with_given_prover::<_, Parameters0, Parameters1>(
            rng,
            fee_amount,
            account,
            updated_account,
            updated_account_commitment,
            leaf_path,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            new_balance_blinding,
            old_rho_blinding,
            &mut even_prover,
            &mut odd_prover,
        )?;

        new_balance_blinding.zeroize();
        old_rho_blinding.zeroize();

        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        let mut partial = proto.gen_proof(&challenge_h);

        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((partial, nullifier, challenge_h))
    }

    /// `new_balance_blinding` and `old_rho_blinding` are shared with the account commitment
    /// Schnorr proofs (created by the caller) so the corresponding responses match during verification.
    pub fn init_with_given_prover<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        fee_amount: Balance,
        account: FeeAccountState<Affine<G0>>,
        updated_account: FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        new_balance_blinding: F0,
        old_rho_blinding: F0,
        even_prover: &mut Prover<MerlinTranscript, Affine<G0>>,
        odd_prover: &mut Prover<MerlinTranscript, Affine<G1>>,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_same_accounts_without_sk(&account, &updated_account, true)?;

        let (re_randomized_path, rerandomization) = leaf_path
            .select_and_rerandomize_prover_gadget_new::<_, Parameters0, Parameters1>(
                even_prover,
                odd_prover,
                account_tree_params,
                rng,
            )?;

        let mut transcript = even_prover.transcript();

        add_to_transcript!(
            transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            re_randomized_path,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            account.asset_id(),
            FEE_AMOUNT_LABEL,
            fee_amount,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        // Need to prove that:
        // 1. nullifier is correctly formed
        // 2. Old balance = new balance + fee_amount
        // 3. Range proof on new balance

        let mut comm_bp_blinding = F0::rand(rng);

        let nullifier_gen = account_comm_key.rho_gen();
        let nullifier = account.nullifier(&account_comm_key);

        let new_balance = F0::from(updated_account.balance);

        // Schnorr commitment for proving correctness of nullifier.
        // Uses old_rho_blinding shared with the account commitment proof so the rho response matches.
        let t_null = PokDiscreteLogProtocol::init(account.rho, old_rho_blinding, &nullifier_gen);

        t_null.challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        // Drop reference to borrow even_prover below
        let _ = transcript;

        // Range proof on new balance to ensure it's non-negative. We need the range proof even when the fee_amount is public
        // since the balance has be in a given range.
        let (comm_new_bal, new_bal_var) = even_prover.commit(new_balance, comm_bp_blinding);
        range_proof(
            even_prover,
            new_bal_var.into(),
            Some(updated_account.balance as u128),
            FEE_BALANCE_BITS.into(),
        )?;

        // Sigma protocol linking the BP commitment to the balance in the account commitment.
        // Uses new_balance_blinding shared with the account commitment proof so the balance response matches.
        let t_bp = PokPedersenCommitmentProtocol::init(
            new_balance,
            new_balance_blinding,
            &account_tree_params.even_parameters.sl_params.pc_gens().B,
            comm_bp_blinding,
            F0::rand(rng),
            &account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
        );

        comm_bp_blinding.zeroize();

        let mut transcript = even_prover.transcript();

        t_bp.challenge_contribution(
            &account_tree_params.even_parameters.sl_params.pc_gens().B,
            &account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
            &comm_new_bal,
            &mut transcript,
        )?;

        Ok((
            Self {
                t_null,
                t_bp,
                re_randomized_path,
                comm_new_bal,
                rerandomization,
                old_account_state: account,
                new_account_state: updated_account,
            },
            nullifier,
        ))
    }

    pub fn gen_proof(self, challenge: &F0) -> FeePaymentWithoutCommitmentsProof<L, F0, F1, G0, G1> {
        let resp_null = self.t_null.gen_partial_proof();

        // Response for witness will already be generated in sigma protocol for the new account commitment
        let resp_bp = self.t_bp.gen_partial2_proof(&challenge);

        FeePaymentWithoutCommitmentsProof {
            resp_null,
            resp_bp,
            re_randomized_path: self.re_randomized_path,
            r1cs_proof: None,
            comm_new_bal: self.comm_new_bal,
        }
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeePaymentWithoutCommitmentsProof<L, F0, F1, G0, G1>
{
    pub fn challenge_contribution_with_verifier<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        even_verifier: &mut Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: &mut Verifier<MerlinTranscript, Affine<G1>>,
    ) -> Result<()> {
        self.re_randomized_path
            .select_and_rerandomize_verifier_gadget::<Parameters0, Parameters1>(
                root,
                even_verifier,
                odd_verifier,
                account_tree_params,
            )?;

        let mut transcript = even_verifier.transcript();

        add_to_transcript!(
            transcript,
            ROOT_LABEL,
            root,
            RE_RANDOMIZED_PATH_LABEL,
            self.re_randomized_path,
            NONCE_LABEL,
            nonce,
            ASSET_ID_LABEL,
            asset_id,
            FEE_AMOUNT_LABEL,
            fee_amount,
            UPDATED_ACCOUNT_COMMITMENT_LABEL,
            updated_account_commitment
        );

        let nullifier_gen = account_comm_key.rho_gen();

        self.resp_null
            .challenge_contribution(&nullifier_gen, &nullifier, &mut transcript)?;

        // Drop reference to borrow even_verifier below
        let _ = transcript;

        let new_bal_var = even_verifier.commit(self.comm_new_bal);

        range_proof(
            even_verifier,
            new_bal_var.into(),
            None,
            FEE_BALANCE_BITS.into(),
        )?;

        let mut transcript = even_verifier.transcript();

        self.resp_bp.challenge_contribution(
            &account_tree_params.even_parameters.sl_params.pc_gens().B,
            &account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
            &self.comm_new_bal,
            &mut transcript,
        )?;

        Ok(())
    }

    /// Verify the partial proof's sigma protocols. The `rho_response` and `balance_response` must
    /// come from the account commitment proof (they are shared across sub-protocols).
    pub fn verify_with_given_challenge<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        challenge: &F0,
        rho_response: &F0,
        balance_response: &F0,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<()> {
        let nullifier_gen = account_comm_key.rho_gen();
        // rho in nullifier matches the rho in the old account commitment
        verify_or_rmc_2!(
            rmc,
            self.resp_null,
            "Nullifier verification failed",
            nullifier,
            nullifier_gen,
            challenge,
            rho_response,
        );
        // balance in BP commitment matches the balance in the account commitment
        verify_or_rmc_3!(
            rmc,
            self.resp_bp,
            "Sigma protocol for Bulletproof commitment failed",
            self.comm_new_bal,
            account_tree_params.even_parameters.sl_params.pc_gens().B,
            account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
            challenge,
            balance_response,
        );
        Ok(())
    }

    pub fn challenge_contribution<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Verifier<MerlinTranscript, Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G1>>,
    )> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);
        self.challenge_contribution_with_verifier::<Parameters0, Parameters1>(
            asset_id,
            fee_amount,
            updated_account_commitment,
            nullifier,
            root,
            nonce,
            account_tree_params,
            account_comm_key,
            &mut even_verifier,
            &mut odd_verifier,
        )?;
        Ok((even_verifier, odd_verifier))
    }

    /// Get the re-randomized leaf point (needed by the Ledger for its auth proof).
    pub fn rerandomized_leaf(&self) -> Affine<G0> {
        self.re_randomized_path.path.get_rerandomized_leaf()
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeePaymentProof<L, F0, F1, G0, G1>
{
    /// `nonce` is used to tie this fee payment proof to the corresponding txn and the eventual payee (relayer, etc) identity, eg. it can
    /// be constructed as b"<txn id>||<payee id>" and the verifier can ensure that the appropriate `nonce` is used
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        fee_amount: Balance,
        sk: G0::ScalarField,
        account: &FeeAccountState<Affine<G0>>,
        updated_account: &FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(Self, Affine<G0>)> {
        ensure_correct_account_state(account, updated_account, fee_amount, true)?;

        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.sl_params.pc_gens(),
            even_transcript,
        );
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.sl_params.pc_gens(),
            odd_transcript,
        );

        // Create account commitment protocol (creates all blindings internally)
        let acc_proto = AccountCommitmentsProtocol::init(
            rng,
            account_comm_key.clone(),
            account_tree_params
                .even_parameters
                .sl_params
                .pc_gens()
                .B_blinding,
        );

        // Write account commitment T-values to transcript first
        let mut transcript = even_prover.transcript();
        acc_proto.challenge_contribution(&mut transcript)?;
        let _ = transcript;

        // Create partial protocol, passing the shared blindings
        let (partial_proto, nullifier) =
            FeePaymentWithoutCommitmentsProtocol::init_with_given_prover::<
                _,
                Parameters0,
                Parameters1,
            >(
                rng,
                fee_amount,
                account.clone(),
                updated_account.clone(),
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                acc_proto.new_balance_blinding,
                acc_proto.old_rho_blinding,
                &mut even_prover,
                &mut odd_prover,
            )?;

        let transcript = even_prover.transcript();
        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Generate proofs
        let commitment_proof = acc_proto.gen_proof(
            &challenge,
            sk,
            F0::from(partial_proto.new_account_state.balance),
            partial_proto.old_account_state.rho,
            partial_proto.old_account_state.randomness,
            partial_proto.rerandomization,
            partial_proto.new_account_state.rho,
            partial_proto.new_account_state.randomness,
        )?;

        let mut partial = partial_proto.gen_proof(&challenge);

        // Finalize Bulletproof (R1CS proof)
        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((
            Self {
                partial,
                commitment_proof,
            },
            nullifier,
        ))
    }

    pub fn verify<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple) = self
            .verify_and_return_tuples::<R, Parameters0, Parameters1>(
                asset_id,
                fee_amount,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                rng,
                rmc_0,
            )?;

        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    /// Verifies the proof except for Bulletproof final verification
    pub fn verify_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

        // Account commitment T-values first (must match prover transcript order)
        let mut transcript = even_verifier.transcript();
        self.commitment_proof
            .challenge_contribution(&mut transcript)?;
        let _ = transcript;

        // Partial challenge contribution (re-rand path, public inputs, nullifier, BP)
        self.partial
            .challenge_contribution_with_verifier::<Parameters0, Parameters1>(
                asset_id,
                fee_amount,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                &mut even_verifier,
                &mut odd_verifier,
            )?;

        let transcript = even_verifier.transcript();
        let challenge = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Verify partial sigma protocols (nullifier + BP)
        // In the solo proof: rho is at index 2, balance at index 1 in resp_acc_old
        let expected_len = 5;
        if self.commitment_proof.resp_acc_old.len() != expected_len {
            return Err(Error::ProofVerificationError(format!(
                "Invalid resp_acc_old length. Expected {}, got {}",
                expected_len,
                self.commitment_proof.resp_acc_old.len()
            )));
        }

        self.partial
            .verify_with_given_challenge::<Parameters0, Parameters1>(
                nullifier,
                account_tree_params,
                account_comm_key.clone(),
                &challenge,
                &self.commitment_proof.resp_acc_old.0[2], // rho response
                &self.commitment_proof.resp_acc_old.0[1], // balance response
                rmc.as_mut().map(|r| &mut **r),
            )?;

        // Verify account commitment Schnorr proofs
        let asset_id_comm = (account_comm_key.asset_id_gen() * F0::from(asset_id)).into_affine();
        let fee_amount_f = F0::from(fee_amount);

        // Old re-randomized leaf minus public terms and fee_amount offset.
        // This gives: sk_gen*sk + balance_gen*new_balance + rho_gen*old_rho + randomness_gen*old_randomness + B_blinding*rerandomization
        let y_old = self
            .partial
            .re_randomized_path
            .path
            .get_rerandomized_leaf()
            .into_group()
            - asset_id_comm
            - (account_comm_key.balance_gen() * fee_amount_f);
        let y_old_affine = y_old.into_affine();

        // New account commitment minus public terms.
        // This gives: sk_gen*sk + balance_gen*new_balance + rho_gen*new_rho + randomness_gen*new_randomness
        let y_new = updated_account_commitment.0.into_group() - asset_id_comm;
        let y_new_affine = y_new.into_affine();

        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        self.commitment_proof.verify_with_challenge(
            y_old_affine,
            y_new_affine,
            account_comm_key,
            b_blinding,
            &challenge,
            rmc.as_mut().map(|r| &mut **r),
        )?;

        // Verify R1CS proof
        let r1cs_proof =
            self.partial.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;

        get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )
    }
}

// The split proof for fee payment is different since public key is not revealed here. So device proves knowledge of secret key in a
// blinded public key which is part of the account commitment. See docs on AuthProofFeePayment

/// Protocol state for the host side of the split (W2/W3) fee payment flow.
/// Created by `init` (which derives the challenge), consumed by `gen_proof`.
pub struct FeePaymentSplitProtocol<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> {
    acc_host: AccountCommitmentsWithoutSkProtocol<G0>,
    without_comm: FeePaymentWithoutCommitmentsProtocol<L, F0, F1, G0, G1>,
    host_rerandomization: F0,
    host_new_randomness: F0,
    /// Ledger's share of the leaf rerandomization scalar
    pub auth_rerandomization: F0,
    /// Ledger's share of the new account's randomness scalar
    pub auth_new_randomness: F0,
    /// Challenge derived from the transcript during init
    pub challenge_h: F0,
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeePaymentSplitProtocol<L, F0, F1, G0, G1>
{
    /// Initialize the split protocol: creates account commitment blindings, partial protocol
    /// (curve-tree, nullifier, BP), splits rerandomization/new_randomness into host and Ledger shares,
    /// and derives the challenge from the transcript.
    ///
    /// Returns `(protocol, even_prover, odd_prover, nullifier)`.
    /// The `challenge_h` is accessible via `protocol.challenge_h`.
    pub fn init<
        'a,
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        fee_amount: Balance,
        account: &FeeAccountState<Affine<G0>>,
        updated_account: &FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &'a SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Self,
        Prover<'a, MerlinTranscript, Affine<G0>>,
        Prover<'a, MerlinTranscript, Affine<G1>>,
        Affine<G0>,
    )> {
        ensure_same_accounts_without_sk(account, updated_account, true)?;

        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_prover = Prover::new(
            &account_tree_params.even_parameters.sl_params.pc_gens(),
            even_transcript,
        );
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_prover = Prover::new(
            &account_tree_params.odd_parameters.sl_params.pc_gens(),
            odd_transcript,
        );

        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        // Create host account commitment protocol (creates all blindings internally)
        let acc_host_proto =
            AccountCommitmentsWithoutSkProtocol::init(rng, account_comm_key.clone(), b_blinding);

        // Create partial protocol, passing the shared blindings from acc_host_proto
        let (partial_proto, nullifier) =
            FeePaymentWithoutCommitmentsProtocol::init_with_given_prover::<
                _,
                Parameters0,
                Parameters1,
            >(
                rng,
                fee_amount,
                account.clone(),
                updated_account.clone(),
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
                acc_host_proto.new_balance_blinding,
                acc_host_proto.old_rho_blinding,
                &mut even_prover,
                &mut odd_prover,
            )?;

        let rerandomization = partial_proto.rerandomization;
        let new_randomness = partial_proto.new_account_state.randomness;

        // Split rerandomization and new_randomness: host picks random shares,
        // derives auth (Ledger) shares as the remainder.
        let host_rerandomization = F0::rand(rng);
        let auth_rerandomization = rerandomization - host_rerandomization;
        let host_new_randomness = F0::rand(rng);
        let auth_new_randomness = new_randomness - host_new_randomness;

        let mut transcript = even_prover.transcript();

        // Write host account commitment T-values and Y-values (host's part of old re-randomized and new account commitments) to transcript

        acc_host_proto
            .t_acc_old
            .challenge_contribution(&mut transcript)?;
        acc_host_proto
            .t_acc_new
            .challenge_contribution(&mut transcript)?;

        // Compute Y-values directly from witnesses: no pk needed
        let acc_old = <Projective<G0> as VariableBaseMSM>::msm_unchecked(
            &acc_old_gens_without_sk(&account_comm_key, b_blinding),
            &[
                F0::from(partial_proto.new_account_state.balance),
                partial_proto.old_account_state.rho,
                partial_proto.old_account_state.randomness,
                host_rerandomization,
            ],
        )
        .into_affine();
        let acc_new = <Projective<G0> as VariableBaseMSM>::msm_unchecked(
            &acc_new_gens_without_sk(&account_comm_key),
            &[
                F0::from(partial_proto.new_account_state.balance),
                partial_proto.new_account_state.rho,
                host_new_randomness,
            ],
        )
        .into_affine();

        acc_old.serialize_compressed(&mut transcript)?;
        acc_new.serialize_compressed(&mut transcript)?;

        let challenge_h = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        Ok((
            Self {
                acc_host: acc_host_proto,
                without_comm: partial_proto,
                host_rerandomization,
                host_new_randomness,
                auth_rerandomization,
                auth_new_randomness,
                challenge_h,
            },
            even_prover,
            odd_prover,
            nullifier,
        ))
    }

    /// Get the re-randomized leaf point (needed by the Ledger for its auth proof).
    pub fn rerandomized_leaf(&self) -> Affine<G0> {
        self.without_comm
            .re_randomized_path
            .path
            .get_rerandomized_leaf()
    }

    /// Generate the host's proofs and finalize the Bulletproof.
    /// `challenge` is typically `self.challenge_h` but callers may pass a custom challenge
    /// (e.g. derived after receiving the Ledger's auth proof in a W3 flow).
    /// Returns `(partial_proof, host_commitment_proof)`.
    pub fn gen_proof<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        self,
        challenge: &F0,
        even_prover: Prover<MerlinTranscript, Affine<G0>>,
        odd_prover: Prover<MerlinTranscript, Affine<G1>>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        rng: &mut R,
    ) -> Result<(
        FeePaymentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
        AccountCommitmentsWithoutSkProof<G0>,
    )> {
        let host_commitment_proof = self.acc_host.gen_proof(
            challenge,
            F0::from(self.without_comm.new_account_state.balance),
            self.without_comm.old_account_state.rho,
            self.without_comm.old_account_state.randomness,
            self.host_rerandomization,
            self.without_comm.new_account_state.rho,
            self.host_new_randomness,
        )?;

        let mut partial = self.without_comm.gen_proof(challenge);

        // Finalize Bulletproof
        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            rng,
        )?;
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        Ok((partial, host_commitment_proof))
    }

    /// runs `init`, immediately derives the challenge (`challenge_h` stored in
    /// `protocol.challenge_h`), calls `gen_proof`, and returns all data the caller needs to
    /// build `AuthProofFeePayment`.
    ///
    /// Returns `(partial, host_commitment_proof, auth_rerandomization, auth_new_randomness, nullifier)`.
    pub fn new<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        rng: &mut R,
        fee_amount: Balance,
        account: &FeeAccountState<Affine<G0>>,
        updated_account: &FeeAccountState<Affine<G0>>,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        leaf_path: CurveTreeWitnessPath<L, G0, G1>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        FeePaymentWithoutCommitmentsProof<L, F0, F1, G0, G1>,
        AccountCommitmentsWithoutSkProof<G0>,
        F0,
        F0,
        Affine<G0>,
    )> {
        let (protocol, even_prover, odd_prover, nullifier) =
            Self::init::<_, Parameters0, Parameters1>(
                rng,
                fee_amount,
                account,
                updated_account,
                updated_account_commitment,
                leaf_path,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
            )?;

        let challenge_h = protocol.challenge_h;
        let auth_rerandomization = protocol.auth_rerandomization;
        let auth_new_randomness = protocol.auth_new_randomness;

        let (partial, host_commitment_proof) = protocol.gen_proof::<_, Parameters0, Parameters1>(
            &challenge_h,
            even_prover,
            odd_prover,
            account_tree_params,
            rng,
        )?;

        Ok((
            partial,
            host_commitment_proof,
            auth_rerandomization,
            auth_new_randomness,
            nullifier,
        ))
    }
}

impl<
    const L: usize,
    F0: PrimeField,
    F1: PrimeField,
    G0: DivisorCurve<ScalarField = F0, BaseField = F1> + Clone + Copy,
    G1: DivisorCurve<ScalarField = F1, BaseField = F0> + Clone + Copy,
> FeePaymentSplitProof<L, F0, F1, G0, G1>
{
    /// Phase 1: Set up verifier transcripts, write challenge contributions (host commitment T-values,
    /// partial re-randomization, public inputs, nullifier, BP), and derive the challenge.
    /// Returns `(even_verifier, odd_verifier, challenge_h)`.
    pub fn challenge_contribution<
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
    ) -> Result<(
        Verifier<MerlinTranscript, Affine<G0>>,
        Verifier<MerlinTranscript, Affine<G1>>,
        F0,
    )> {
        let even_transcript = MerlinTranscript::new(TXN_EVEN_LABEL);
        let mut even_verifier = Verifier::<_, Affine<G0>>::new(even_transcript);
        let odd_transcript = MerlinTranscript::new(TXN_ODD_LABEL);
        let mut odd_verifier = Verifier::<_, Affine<G1>>::new(odd_transcript);

        let (asset_id_gen, balance_gen) = (
            account_comm_key.asset_id_gen(),
            account_comm_key.balance_gen(),
        );

        // Partial challenge contribution (re-rand path, public inputs, nullifier, BP)
        self.partial
            .challenge_contribution_with_verifier::<Parameters0, Parameters1>(
                asset_id,
                fee_amount,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                &mut even_verifier,
                &mut odd_verifier,
            )?;

        let mut transcript = even_verifier.transcript();

        // Write host account commitment T-values and Y-values (host's part of old re-randomized and new account commitments) to transcript
        self.commitment_proof
            .host_proof
            .t_acc_old
            .serialize_compressed(&mut transcript)?;
        self.commitment_proof
            .host_proof
            .t_acc_new
            .serialize_compressed(&mut transcript)?;
        let (comm_old, comm_new) = self.old_and_new_host_commitments(
            asset_id,
            fee_amount,
            updated_account_commitment,
            asset_id_gen,
            balance_gen,
        );
        comm_old.serialize_compressed(&mut transcript)?;
        comm_new.serialize_compressed(&mut transcript)?;

        let challenge_h = transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        Ok((even_verifier, odd_verifier, challenge_h))
    }

    pub fn verify_host_and_return_tuples_with_given_challenge<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        challenge: &F0,
        even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(VerificationTuple<Affine<G0>>, VerificationTuple<Affine<G1>>)> {
        let expected_len = 4;
        if self.commitment_proof.host_proof.resp_acc_old.len() != expected_len {
            return Err(Error::ProofVerificationError(format!(
                "Invalid resp_acc_old length. Expected {}, got {}",
                expected_len,
                self.commitment_proof.host_proof.resp_acc_old.len()
            )));
        }

        // Verify partial sigma protocols (nullifier + BP).
        self.partial
            .verify_with_given_challenge::<Parameters0, Parameters1>(
                nullifier,
                account_tree_params,
                account_comm_key.clone(),
                challenge,
                &self.commitment_proof.host_proof.resp_acc_old.0[1], // rho response
                &self.commitment_proof.host_proof.resp_acc_old.0[0], // balance response
                rmc.as_mut().map(|r| &mut **r),
            )?;

        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        // Verify host's account commitment Schnorr proofs
        let (y_old_affine, y_new_affine) = self.old_and_new_host_commitments(
            asset_id,
            fee_amount,
            updated_account_commitment,
            account_comm_key.asset_id_gen(),
            account_comm_key.balance_gen(),
        );

        self.commitment_proof.host_proof.verify_with_challenge(
            y_old_affine,
            y_new_affine,
            account_comm_key,
            b_blinding,
            challenge,
            rmc.as_mut().map(|r| &mut **r),
        )?;

        let r1cs_proof =
            self.partial.r1cs_proof.as_ref().ok_or_else(|| {
                Error::ProofVerificationError("R1CS proof is missing".to_string())
            })?;

        let (even_tuple, odd_tuple) = get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            rng,
        )?;

        Ok((even_tuple, odd_tuple))
    }

    pub fn verify_host_and_return_tuples<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        rmc: Option<&mut RandomizedMultChecker<Affine<G0>>>,
    ) -> Result<(
        VerificationTuple<Affine<G0>>,
        VerificationTuple<Affine<G1>>,
        F0,
    )> {
        let (even_verifier, odd_verifier, challenge_h) = self
            .challenge_contribution::<Parameters0, Parameters1>(
                asset_id,
                fee_amount,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key.clone(),
            )?;

        let (even_tuple, odd_tuple) = self
            .verify_host_and_return_tuples_with_given_challenge::<_, Parameters0, Parameters1>(
                &challenge_h,
                even_verifier,
                odd_verifier,
                asset_id,
                fee_amount,
                updated_account_commitment,
                nullifier,
                account_tree_params,
                account_comm_key,
                rng,
                rmc,
            )?;

        Ok((even_tuple, odd_tuple, challenge_h))
    }

    /// verify sigma protocols and R1CS, then handle tuples.
    /// Takes `(even_verifier, odd_verifier, challenge)` from `challenge_contribution`.
    pub fn verify_host_with_challenge<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        challenge: &F0,
        even_verifier: Verifier<MerlinTranscript, Affine<G0>>,
        odd_verifier: Verifier<MerlinTranscript, Affine<G1>>,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<()> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple) = self
            .verify_host_and_return_tuples_with_given_challenge::<_, Parameters0, Parameters1>(
                challenge,
                even_verifier,
                odd_verifier,
                asset_id,
                fee_amount,
                updated_account_commitment,
                nullifier,
                account_tree_params,
                account_comm_key,
                rng,
                rmc_0,
            )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)
    }

    /// complete host verification from scratch.
    /// Returns the derived challenge for use in auth-proof coordination.
    pub fn verify_host<
        R: CryptoRngCore,
        Parameters0: DiscreteLogParameters,
        Parameters1: DiscreteLogParameters,
    >(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        nullifier: Affine<G0>,
        root: &Root<L, 1, G0, G1>,
        nonce: &[u8],
        account_tree_params: &SelRerandProofParametersNew<G0, G1, Parameters0, Parameters1>,
        account_comm_key: impl AccountCommitmentKeyTrait<Affine<G0>>,
        rng: &mut R,
        mut rmc: Option<(
            &mut RandomizedMultChecker<Affine<G0>>,
            &mut RandomizedMultChecker<Affine<G1>>,
        )>,
    ) -> Result<F0> {
        let rmc_0 = match rmc.as_mut() {
            Some((rmc_0, _)) => Some(&mut **rmc_0),
            None => None,
        };
        let (even_tuple, odd_tuple, challenge_h) = self
            .verify_host_and_return_tuples::<_, Parameters0, Parameters1>(
                asset_id,
                fee_amount,
                updated_account_commitment,
                nullifier,
                root,
                nonce,
                account_tree_params,
                account_comm_key,
                rng,
                rmc_0,
            )?;
        handle_verification_tuples(even_tuple, odd_tuple, account_tree_params, rmc)?;
        Ok(challenge_h)
    }

    fn old_and_new_host_commitments(
        &self,
        asset_id: AssetId,
        fee_amount: Balance,
        updated_account_commitment: FeeAccountStateCommitment<Affine<G0>>,
        asset_id_gen: Affine<G0>,
        balance_gen: Affine<G0>,
    ) -> (Affine<G0>, Affine<G0>) {
        let asset_id_comm = (asset_id_gen * F0::from(asset_id)).into_affine();
        let y_old = self
            .partial
            .re_randomized_path
            .path
            .get_rerandomized_leaf()
            .into_group()
            - asset_id_comm
            - (balance_gen * F0::from(fee_amount))
            - self
                .commitment_proof
                .auth_proof
                .partial_re_randomized_account_commitment;
        let y_old_affine = y_old.into_affine();

        let y_new = updated_account_commitment.0.into_group()
            - asset_id_comm
            - self
                .commitment_proof
                .auth_proof
                .partial_updated_account_commitment;
        let y_new_affine = y_new.into_affine();
        (y_old_affine, y_new_affine)
    }
}

/// Generators for the re-randomized leaf Schnorr proof (solo, with sk).
/// Order: [sk_gen, balance_gen, rho_gen, randomness_gen, B_blinding]
pub fn acc_old_gens_with_sk<G0: SWCurveConfig + Clone + Copy>(
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    blinding_gen: Affine<G0>,
) -> [Affine<G0>; 5] {
    [
        account_comm_key.sk_gen(),
        account_comm_key.balance_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.randomness_gen(),
        blinding_gen,
    ]
}

/// Generators for the new account commitment Schnorr proof (solo, with sk).
/// Order: [sk_gen, balance_gen, rho_gen, randomness_gen]
pub fn acc_new_gens_with_sk<G0: SWCurveConfig + Clone + Copy>(
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
) -> [Affine<G0>; 4] {
    [
        account_comm_key.sk_gen(),
        account_comm_key.balance_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.randomness_gen(),
    ]
}

/// Generators for the re-randomized leaf Schnorr proof (split, without sk).
/// AuthProofFeePayment handles `sk_gen*sk + B_blinding*auth_rerandomization`, the host proves the rest
/// including its share of the B_blinding rerandomization.
/// Order: [balance_gen, rho_gen, randomness_gen, B_blinding]
pub fn acc_old_gens_without_sk<G0: SWCurveConfig + Clone + Copy>(
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
    blinding_gen: Affine<G0>,
) -> [Affine<G0>; 4] {
    [
        account_comm_key.balance_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.randomness_gen(),
        blinding_gen,
    ]
}

/// Generators for the new account commitment Schnorr proof (split, without sk).
/// AuthProofFeePayment handles `sk_gen*sk + randomness_gen*auth_new_randomness`, the host proves the rest
/// including its share of the randomness_gen randomness.
/// Order: [balance_gen, rho_gen, randomness_gen]
pub fn acc_new_gens_without_sk<G0: SWCurveConfig + Clone + Copy>(
    account_comm_key: &impl AccountCommitmentKeyTrait<Affine<G0>>,
) -> [Affine<G0>; 3] {
    [
        account_comm_key.balance_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.randomness_gen(),
    ]
}

/// create SchnorrCommitments for fee account commitment Schnorr proofs.
/// When `sk_blinding` is `Some`, sk generators are included at position 0.
/// When `new_s_blinding` is `Some`, it's used for the last new-commitment blinding;
/// otherwise a random value is used (appropriate for split proofs where the
/// witness is the host's random share).
///
/// Returns `(t_acc_old, t_acc_new, new_balance_blinding, old_rho_blinding, new_rho_blinding, old_s_blinding)`.
fn init_acc_comm<R: CryptoRngCore, G: SWCurveConfig + Clone + Copy>(
    rng: &mut R,
    account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
    blinding_gen: Affine<G>,
    sk_blinding: Option<G::ScalarField>,
    new_s_blinding: Option<G::ScalarField>,
) -> (
    SchnorrCommitment<Affine<G>>,
    SchnorrCommitment<Affine<G>>,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
    G::ScalarField,
) {
    let new_balance_blinding = G::ScalarField::rand(rng);
    let old_rho_blinding = G::ScalarField::rand(rng);
    let new_rho_blinding = G::ScalarField::rand(rng);
    let old_s_blinding = G::ScalarField::rand(rng);

    let mut old_gens = Vec::new();
    let mut old_blindings = Vec::new();
    let mut new_gens = Vec::new();
    let mut new_blindings = Vec::new();

    if let Some(sk_b) = sk_blinding {
        old_gens.push(account_comm_key.sk_gen());
        old_blindings.push(sk_b);
        new_gens.push(account_comm_key.sk_gen());
        new_blindings.push(sk_b);
    }

    old_gens.extend_from_slice(&[
        account_comm_key.balance_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.randomness_gen(),
        blinding_gen,
    ]);
    old_blindings.extend_from_slice(&[
        new_balance_blinding,
        old_rho_blinding,
        old_s_blinding,
        G::ScalarField::rand(rng),
    ]);

    new_gens.extend_from_slice(&[
        account_comm_key.balance_gen(),
        account_comm_key.rho_gen(),
        account_comm_key.randomness_gen(),
    ]);
    new_blindings.push(new_balance_blinding);
    new_blindings.push(new_rho_blinding);
    new_blindings.push(new_s_blinding.unwrap_or_else(|| G::ScalarField::rand(rng)));

    let t_acc_old = SchnorrCommitment::new(&old_gens, old_blindings);
    let t_acc_new = SchnorrCommitment::new(&new_gens, new_blindings);

    (
        t_acc_old,
        t_acc_new,
        new_balance_blinding,
        old_rho_blinding,
        new_rho_blinding,
        old_s_blinding,
    )
}

/// generate responses for fee account commitment Schnorr proofs.
/// When `sk` is `Some`, it appears at position 0 of old witnesses;
/// new-commitment partial-response indices are shifted accordingly.
///
/// Returns `(resp_acc_old, resp_acc_new, t_acc_old, t_acc_new)`.
fn resp_acc_comm<G: SWCurveConfig + Clone + Copy>(
    t_acc_old: &SchnorrCommitment<Affine<G>>,
    t_acc_new: &SchnorrCommitment<Affine<G>>,
    challenge: &G::ScalarField,
    sk: Option<G::ScalarField>,
    new_balance: G::ScalarField,
    old_rho: G::ScalarField,
    old_randomness: G::ScalarField,
    rerandomization: G::ScalarField,
    new_rho: G::ScalarField,
    new_randomness: G::ScalarField,
) -> Result<(
    SchnorrResponse<Affine<G>>,
    PartialSchnorrResponse<Affine<G>>,
)> {
    let mut old_wits = Vec::new();
    let offset = if let Some(sk_val) = sk {
        old_wits.push(sk_val);
        1
    } else {
        0
    };
    old_wits.extend_from_slice(&[new_balance, old_rho, old_randomness, rerandomization]);

    let resp_acc_old = t_acc_old.response(&old_wits, challenge)?;

    let mut new_wits = BTreeMap::new();
    new_wits.insert(1 + offset, new_rho);
    new_wits.insert(2 + offset, new_randomness);
    let resp_acc_new = t_acc_new.partial_response(new_wits, challenge)?;

    Ok((resp_acc_old, resp_acc_new))
}

/// verify fee account commitment Schnorr proofs (old + new).
/// When `has_sk` is true, uses with-sk generators and shares sk + balance;
/// otherwise uses without-sk generators and shares only balance.
fn verify_acc_comm<G: SWCurveConfig + Clone + Copy>(
    resp_acc_old: &SchnorrResponse<Affine<G>>,
    resp_acc_new: &PartialSchnorrResponse<Affine<G>>,
    t_acc_old: Affine<G>,
    t_acc_new: Affine<G>,
    y_old: Affine<G>,
    y_new: Affine<G>,
    account_comm_key: impl AccountCommitmentKeyTrait<Affine<G>>,
    blinding_gen: Affine<G>,
    has_sk: bool,
    challenge: &G::ScalarField,
    mut rmc: Option<&mut RandomizedMultChecker<Affine<G>>>,
) -> Result<()> {
    let expected_old = if has_sk { 5 } else { 4 };
    if resp_acc_old.len() != expected_old {
        return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
            expected_old,
            resp_acc_old.len(),
        ));
    }
    if resp_acc_new.responses.len() != 2 {
        return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
            2,
            resp_acc_new.responses.len(),
        ));
    }

    let offset = if has_sk { 1usize } else { 0 };

    let mut missing_resps = BTreeMap::new();
    if has_sk {
        missing_resps.insert(0, resp_acc_old.0[0]); // sk
    }
    missing_resps.insert(offset, resp_acc_old.0[offset]); // balance

    let (old_gens, new_gens): (Vec<Affine<G>>, Vec<Affine<G>>) = if has_sk {
        (
            acc_old_gens_with_sk(&account_comm_key, blinding_gen).to_vec(),
            acc_new_gens_with_sk(&account_comm_key).to_vec(),
        )
    } else {
        (
            acc_old_gens_without_sk(&account_comm_key, blinding_gen).to_vec(),
            acc_new_gens_without_sk(&account_comm_key).to_vec(),
        )
    };

    verify_schnorr_resp_or_rmc!(rmc, resp_acc_old, old_gens, y_old, t_acc_old, challenge);
    verify_partial_schnorr_resp_or_rmc!(
        rmc,
        resp_acc_new,
        new_gens,
        y_new,
        t_acc_new,
        challenge,
        missing_resps,
    );

    Ok(())
}

pub fn ensure_same_accounts_without_sk<G: AffineRepr>(
    old_state: &FeeAccountState<G>,
    new_state: &FeeAccountState<G>,
    has_balance_changed: bool,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if old_state.asset_id != new_state.asset_id {
            return Err(Error::ProofGenerationError(format!(
                "Asset ID mismatch between old and new fee account states: old = {}, new = {}",
                old_state.asset_id, new_state.asset_id
            )));
        }
        if old_state.initial_rho != new_state.initial_rho {
            return Err(Error::ProofGenerationError(
                "Initial rho mismatch between old and new fee account states".to_string(),
            ));
        }
        if old_state.initial_randomness != new_state.initial_randomness {
            return Err(Error::ProofGenerationError(
                "Initial randomness mismatch between old and new fee account states".to_string(),
            ));
        }
        if has_balance_changed {
            if old_state.balance == new_state.balance {
                return Err(Error::ProofGenerationError(
                    "Balance should have changed but it hasn't".to_string(),
                ));
            }
        } else {
            if old_state.balance != new_state.balance {
                return Err(Error::ProofGenerationError(
                    "Balance shouldn't have changed but it has".to_string(),
                ));
            }
        }
        if old_state.rho * old_state.initial_rho != new_state.rho {
            return Err(Error::ProofGenerationError(
                "Rho not correctly updated in new fee account state".to_string(),
            ));
        }
        if old_state.randomness * old_state.initial_randomness != new_state.randomness {
            return Err(Error::ProofGenerationError(
                "Randomness not correctly updated in new fee account state".to_string(),
            ));
        }
        Ok(())
    }
}

pub fn ensure_same_sk<G: AffineRepr>(
    old_state: &FeeAccountState<G>,
    new_state: &FeeAccountState<G>,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        if old_state.pk != new_state.pk {
            return Err(Error::ProofGenerationError(
                "Public key mismatch between old and new account states".to_string(),
            ));
        }
        Ok(())
    }
}

pub fn ensure_correct_account_state<G: AffineRepr>(
    old_state: &FeeAccountState<G>,
    new_state: &FeeAccountState<G>,
    amount: Balance,
    has_balance_decreased: bool,
) -> Result<()> {
    #[cfg(feature = "ignore_prover_input_sanitation")]
    {
        return Ok(());
    }

    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        // Ensure accounts are consistent (same pk, asset_id)
        if old_state.pk != new_state.pk {
            return Err(Error::ProofGenerationError(
                "Public key mismatch between old and new account states".to_string(),
            ));
        }
        if old_state.asset_id != new_state.asset_id {
            return Err(Error::ProofGenerationError(format!(
                "Asset ID mismatch between old and new account states: old = {}, new = {}",
                old_state.asset_id, new_state.asset_id
            )));
        }
        if has_balance_decreased {
            let expected_balance = old_state.balance.checked_sub(amount).ok_or_else(|| {
                Error::ProofGenerationError("Balance decrease underflow".to_string())
            })?;
            if new_state.balance != expected_balance {
                return Err(Error::ProofGenerationError(
                    "Balance decrease incorrect".to_string(),
                ));
            }
        } else {
            let expected_balance = old_state.balance.checked_add(amount).ok_or_else(|| {
                Error::ProofGenerationError("Balance increase overflow".to_string())
            })?;
            if new_state.balance != expected_balance {
                return Err(Error::ProofGenerationError(
                    "Balance increase incorrect".to_string(),
                ));
            }
        }
        Ok(())
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::account::tests::setup_gens_new;
    use crate::account_registration::tests::setup_comm_key;
    use crate::keys::VerKey;
    use crate::keys::keygen_sig;
    use crate::util::{add_verification_tuples_batches_to_rmc, batch_verify_bp, verify_rmc};
    use ark_ec_divisors::curves::{pallas::PallasParams, vesta::VestaParams};
    use curve_tree_relations::curve_tree::CurveTree;
    use std::time::Instant;

    type PallasParameters = ark_pallas::PallasConfig;
    type VestaParameters = ark_vesta::VestaConfig;
    type PallasA = ark_pallas::Affine;
    type F0 = ark_pallas::Fr;
    type F1 = ark_vesta::Fr;

    pub fn new_fee_account<R: CryptoRngCore, G: AffineRepr>(
        rng: &mut R,
        asset_id: AssetId,
        pk: VerKey<G>,
        balance: Balance,
    ) -> FeeAccountState<G> {
        FeeAccountState::new(rng, pk.0, balance, asset_id)
    }

    #[test]
    fn fee_account_init() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;
        let balance = 1000;

        let (_sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let fee_account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk_i.clone(), balance);
        assert_eq!(fee_account.asset_id, asset_id);
        assert_eq!(fee_account.balance, balance);
        assert_eq!(fee_account.pk, pk_i.0);

        fee_account.commit(account_comm_key).unwrap();
    }

    #[test]
    fn fee_account_registration() {
        let mut rng = rand::thread_rng();

        let account_comm_key = setup_comm_key(b"testing");

        let asset_id = 1;
        let balance = 1000;

        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let fee_account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk_i, balance);
        let fee_account_comm = fee_account.commit(account_comm_key.clone()).unwrap();

        let nonce = b"test-nonce";

        let reg_proof = RegTxnProof::new(
            &mut rng,
            sk_i.0,
            &fee_account,
            fee_account_comm.clone(),
            nonce,
            account_comm_key.clone(),
        )
        .unwrap();

        reg_proof
            .verify(
                &pk_i.0,
                balance,
                asset_id,
                &fee_account_comm,
                nonce,
                account_comm_key,
                None,
            )
            .unwrap();
    }

    #[test]
    fn fee_account_registration_parallel() {
        // W2 (Parallel): Host and Ledger each build their own independent transcript.
        // Host derives challenge_h from public inputs + partial T-values.
        // Ledger derives challenge_l from its own auth-only transcript.
        // Verifier replicates each side's transcript independently.

        let mut rng = rand::thread_rng();
        let account_comm_key = setup_comm_key(b"testing");
        let asset_id = 1;
        let balance = 1000;
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let fee_account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk, balance);
        let fee_account_comm = fee_account.commit(account_comm_key.clone()).unwrap();
        let nonce = b"test-nonce";

        //  Host side: own transcript, public inputs + partial T-values
        let partial = RegTxnProofWithoutSkProtocol::new(
            &mut rng,
            pk.0,
            &fee_account,
            fee_account_comm.clone(),
            nonce,
            account_comm_key.clone(),
        )
        .unwrap();

        //  Ledger side: own transcript, auth T-values only
        // Uses AuthProofOnlySk::new which internally builds an AUTH_TXN_LABEL transcript
        let sk_gen = account_comm_key.sk_gen();
        let auth_proof = AuthProofOnlySk::new(&mut rng, sk.0, pk.0, nonce, &sk_gen).unwrap();

        let reg_proof = RegTxnProof {
            partial,
            auth_proof,
        };

        //  Verify each side with its own independent challenge
        // recreate host transcript, derive challenge_h, verify partial
        let mut verifier_transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        let reduced_acc_comm = reg_proof
            .partial
            .challenge_contribution(
                &pk.0,
                balance,
                asset_id,
                &fee_account_comm,
                nonce,
                account_comm_key.clone(),
                &mut verifier_transcript,
            )
            .unwrap();
        let challenge_h_v = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);
        reg_proof
            .partial
            .verify_with_given_transcript(
                reduced_acc_comm,
                account_comm_key.clone(),
                &challenge_h_v,
                None,
            )
            .unwrap();

        // Verify auth: uses its own AUTH_TXN_LABEL transcript
        reg_proof
            .auth_proof
            .verify(pk.0, nonce, &sk_gen, None)
            .unwrap();
    }

    #[test]
    fn fee_account_registration_sequential() {
        // W3 (Sequential): Host derives partial challenge first, sends it to Ledger.
        // Ledger uses the partial challenge (as part of the nonce) to create its auth proof.
        // Host uses the partial challenge to generate its partial proof.
        // Verifier replicates: derive partial challenge, verify partial; then verify auth with same nonce.

        let mut rng = rand::thread_rng();
        let account_comm_key = setup_comm_key(b"testing");
        let asset_id = 1;
        let balance = 1000;
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let fee_account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk, balance);
        let fee_account_comm = fee_account.commit(account_comm_key.clone()).unwrap();
        let nonce = b"test-nonce";

        //  Host builds its partial partial protocol, derives partial challenge
        let mut host_transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        let partial_proto = RegTxnProofWithoutSkProtocol::init_with_given_transcript(
            &mut rng,
            pk.0,
            &fee_account,
            fee_account_comm.clone(),
            nonce,
            account_comm_key.clone(),
            &mut host_transcript,
        )
        .unwrap();
        let challenge_h = host_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Host sends challenge_h to Ledger
        // Ledger creates auth proof with nonce = challenge_h_bytes + original_nonce
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();
        let sk_gen = account_comm_key.sk_gen();
        let auth_proof =
            AuthProofOnlySk::new(&mut rng, sk.0, pk.0, &ledger_nonce, &sk_gen).unwrap();

        // Host hashes auth_proof into the transcript to derive an updated challenge
        let mut auth_proof_bytes = Vec::new();
        auth_proof
            .serialize_compressed(&mut auth_proof_bytes)
            .unwrap();
        host_transcript.append_message(b"auth-proof", &auth_proof_bytes);
        let challenge_h_final = host_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        let partial = partial_proto.gen_proof(&challenge_h_final);

        let reg_proof = RegTxnProof {
            partial,
            auth_proof,
        };

        //  derive partial challenge, verify partial; verify auth with ledger nonce
        let mut verifier_transcript = MerlinTranscript::new(FEE_REG_TXN_LABEL);
        let reduced_acc_comm = reg_proof
            .partial
            .challenge_contribution(
                &pk.0,
                balance,
                asset_id,
                &fee_account_comm,
                nonce,
                account_comm_key.clone(),
                &mut verifier_transcript,
            )
            .unwrap();
        let challenge_h_v = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Verifier recomputes the ledger nonce from the partial challenge
        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v
            .serialize_compressed(&mut challenge_h_v_bytes)
            .unwrap();
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();
        reg_proof
            .auth_proof
            .verify(pk.0, &ledger_nonce_v, &sk_gen, None)
            .unwrap();

        // Verifier hashes auth_proof into the transcript to derive the updated challenge
        let mut auth_proof_bytes_v = Vec::new();
        reg_proof
            .auth_proof
            .serialize_compressed(&mut auth_proof_bytes_v)
            .unwrap();
        verifier_transcript.append_message(b"auth-proof", &auth_proof_bytes_v);
        let challenge_h_final_v = verifier_transcript.challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        reg_proof
            .partial
            .verify_with_given_transcript(
                reduced_acc_comm,
                account_comm_key.clone(),
                &challenge_h_final_v,
                None,
            )
            .unwrap();
    }

    #[test]
    fn fee_account_topup_txn() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;

        // Issuer creates keys
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

        let balance = 1000;
        let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk_i, balance);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // Add fee account commitment in curve tree
        // This tree size can be chosen independently of the one used for regular accounts and will likely be bigger
        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(6),
        );

        let increase_bal_by = 10;

        let nonce = b"test-nonce";

        let clock = Instant::now();

        let updated_account = account.get_state_for_topup(increase_bal_by).unwrap();
        assert_eq!(updated_account.balance, account.balance + increase_bal_by);
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = FeeAccountTopupTxnProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            sk_i.0,
            increase_bal_by,
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                pk_i.0,
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                None,
            )
            .unwrap();

        let verifier_time_regular = clock.elapsed();

        println!("L={L}, height={}", account_tree.height());

        let clock = Instant::now();
        let mut rmc_0 = RandomizedMultChecker::new(F0::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(F1::rand(&mut rng));
        proof
            .verify(
                pk_i.0,
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();

        let start = Instant::now();
        verify_rmc(rmc_0, rmc_1).unwrap();
        println!("verify_rmc time: {:?}", start.elapsed());
        let verifier_time_rmc = clock.elapsed();

        println!("For topup txn");
        println!("total proof size = {}", proof.compressed_size());
        println!("total prover time = {:?}", prover_time);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_regular, verifier_time_rmc
        );

        assert!(
            proof
                .verify(
                    pk_i.0,
                    asset_id,
                    increase_bal_by + 10,
                    updated_account_comm,
                    nullifier,
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    pk_i.0,
                    asset_id,
                    increase_bal_by,
                    updated_account_comm,
                    PallasA::rand(&mut rng),
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn fee_account_topup_txn_parallel() {
        // W2 (Parallel): Host creates partial topup proof, Ledger creates auth proof independently.
        // Both use their own transcripts; challenges are independent.

        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");
        let asset_id = 1;
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let balance = 1000;
        let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk_i, balance);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(6),
        );

        let increase_bal_by = 10;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_topup(increase_bal_by).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host side: creates transcripts/provers internally, derives challenge_h
        let pk_gen = account_comm_key.sk_gen();
        let (partial, nullifier) =
            FeeAccountTopupTxnWithoutSkProtocol::new::<_, PallasParams, VestaParams>(
                &mut rng,
                &pk_i.0,
                increase_bal_by,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        //  Ledger side: own AUTH_TXN_LABEL transcript, independently
        let auth_proof = AuthProofOnlySk::new(&mut rng, sk_i.0, pk_i.0, nonce, &pk_gen).unwrap();

        let proof = FeeAccountTopupTxnProof {
            auth_proof,
            partial,
        };

        //  verify each side with its own independent challenge
        let (even_verifier, odd_verifier) = proof
            .partial
            .verify_sigma_protocols::<PallasParams, VestaParams>(
                pk_i.0,
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        let r1cs_proof = proof.partial.r1cs_proof.as_ref().unwrap();
        let (even_tuple, odd_tuple) = get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            &mut rng,
        )
        .unwrap();
        handle_verification_tuples(even_tuple, odd_tuple, &account_tree_params, None).unwrap();

        // Verify auth proof using its own AUTH_TXN_LABEL transcript
        proof
            .auth_proof
            .verify(pk_i.0, nonce, &pk_gen, None)
            .unwrap();
    }

    #[test]
    fn fee_account_topup_txn_sequential() {
        // W3 (Sequential): Host derives partial challenge first, sends it to Ledger.
        // Ledger uses ledger_nonce = [challenge_h_bytes || original_nonce] for its own AUTH_TXN_LABEL transcript.
        // Host uses challenge_h to generate its partial proof.
        // Verifier replicates: derive partial challenge, verify partial, recompute ledger nonce, verify auth.

        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");
        let asset_id = 1;
        let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let balance = 1000;
        let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk_i, balance);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(6),
        );

        let increase_bal_by = 10;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_topup(increase_bal_by).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host pre-challenge phase
        let pk_gen = account_comm_key.sk_gen();
        let (protocol, mut even_prover, odd_prover, nullifier) =
            FeeAccountTopupTxnWithoutSkProtocol::init::<_, PallasParams, VestaParams>(
                &mut rng,
                &pk_i.0,
                increase_bal_by,
                account.clone(),
                updated_account.clone(),
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        let challenge_h = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        //  Host sends challenge_h bytes to Ledger
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();
        let auth_proof =
            AuthProofOnlySk::new(&mut rng, sk_i.0, pk_i.0, &ledger_nonce, &pk_gen).unwrap();

        // Host hashes auth_proof into the transcript to derive an updated challenge
        let mut auth_proof_bytes = Vec::new();
        auth_proof
            .serialize_compressed(&mut auth_proof_bytes)
            .unwrap();
        even_prover
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes);
        let challenge_h_final = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        //  Host post-challenge phase
        let mut partial = protocol.gen_proof(&challenge_h_final).unwrap();
        let (even_proof, odd_proof) = prove_with_rng(
            even_prover,
            odd_prover,
            &account_tree_params.even_parameters.bp_gens(),
            &account_tree_params.odd_parameters.bp_gens(),
            &mut rng,
        )
        .unwrap();
        partial.r1cs_proof = Some(BPProof {
            even_proof,
            odd_proof,
        });

        let proof = FeeAccountTopupTxnProof {
            auth_proof,
            partial,
        };

        //  derive partial challenge, verify partial, recompute ledger nonce, verify auth
        let (mut even_verifier, odd_verifier) = proof
            .partial
            .challenge_contribution::<PallasParams, VestaParams>(
                pk_i.0,
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        let challenge_h_v = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Verifier recomputes ledger nonce from the partial challenge
        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v
            .serialize_compressed(&mut challenge_h_v_bytes)
            .unwrap();
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();
        proof
            .auth_proof
            .verify(pk_i.0, &ledger_nonce_v, &pk_gen, None)
            .unwrap();

        // Verifier hashes auth_proof into the transcript to derive the updated challenge
        let mut auth_proof_bytes_v = Vec::new();
        proof
            .auth_proof
            .serialize_compressed(&mut auth_proof_bytes_v)
            .unwrap();
        even_verifier
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes_v);
        let challenge_h_final_v = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        proof
            .partial
            .verify_with_challenge::<PallasParams, VestaParams>(
                pk_i.0,
                asset_id,
                increase_bal_by,
                updated_account_comm,
                nullifier,
                &account_tree_params,
                account_comm_key.clone(),
                &challenge_h_final_v,
                None,
            )
            .unwrap();

        let r1cs_proof = proof.partial.r1cs_proof.as_ref().unwrap();
        let (even_tuple, odd_tuple) = get_verification_tuples_with_rng(
            even_verifier,
            odd_verifier,
            &r1cs_proof.even_proof,
            &r1cs_proof.odd_proof,
            &mut rng,
        )
        .unwrap();
        handle_verification_tuples(even_tuple, odd_tuple, &account_tree_params, None).unwrap();
    }

    #[test]
    fn fee_payment_proof() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;

        // Investor has fee payment account with some balance
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let balance = 1000;
        let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk, balance);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        // This tree size can be chosen independently of the one used for regular accounts and will likely be bigger
        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(6),
        );

        let fee_amount = 10;

        // Or could be hash(a_txn_id, a_payee_id)
        let nonce = b"a_txn_id,a_payee_id";

        let clock = Instant::now();

        let updated_account = account.get_state_for_payment(fee_amount).unwrap();
        assert_eq!(updated_account.balance, account.balance - fee_amount);
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();

        let root = account_tree.root_node();

        let (proof, nullifier) = FeePaymentProof::new::<_, PallasParams, VestaParams>(
            &mut rng,
            fee_amount,
            sk.0,
            &account,
            &updated_account,
            updated_account_comm,
            path,
            &root,
            nonce,
            &account_tree_params,
            account_comm_key.clone(),
        )
        .unwrap();

        let prover_time = clock.elapsed();

        let clock = Instant::now();
        proof
            .verify(
                asset_id,
                fee_amount,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                None,
            )
            .unwrap();

        let verifier_time_regular = clock.elapsed();

        println!("L={L}, height={}", account_tree.height());
        let clock = Instant::now();
        let mut rmc_0 = RandomizedMultChecker::new(F0::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(F1::rand(&mut rng));
        proof
            .verify(
                asset_id,
                fee_amount,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                Some((&mut rmc_0, &mut rmc_1)),
            )
            .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let verifier_time_rmc = clock.elapsed();

        println!("For fee payment txn");
        println!("total proof size = {}", proof.compressed_size());
        println!("total prover time = {:?}", prover_time);
        println!(
            "verifier time (regular) = {:?}, verifier time (RandomizedMultChecker) = {:?}",
            verifier_time_regular, verifier_time_rmc
        );

        assert!(
            proof
                .verify(
                    asset_id,
                    fee_amount + 10,
                    updated_account_comm,
                    nullifier,
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    asset_id,
                    fee_amount,
                    updated_account_comm,
                    PallasA::rand(&mut rng),
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                    None,
                )
                .is_err()
        );

        assert!(
            proof
                .verify(
                    asset_id + 1,
                    fee_amount,
                    updated_account_comm,
                    nullifier,
                    &root,
                    nonce,
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                    None,
                )
                .is_err()
        );
    }

    #[test]
    fn batch_fee_payment_proofs() {
        let mut rng = rand::thread_rng();

        // Setup begins
        const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

        let asset_id = 1;

        let batch_size = 5;

        let mut accounts = Vec::with_capacity(batch_size);
        let mut sks = Vec::with_capacity(batch_size);
        let mut account_comms = Vec::with_capacity(batch_size);
        let mut updated_accounts = Vec::with_capacity(batch_size);
        let mut updated_account_comms = Vec::with_capacity(batch_size);
        let mut paths = Vec::with_capacity(batch_size);
        for _ in 0..batch_size {
            let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let balance = 1000;
            let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk, balance);
            let account_comm = account.commit(account_comm_key.clone()).unwrap();
            sks.push(sk);
            accounts.push(account);
            account_comms.push(account_comm);
        }

        let fee_amount = 10;

        let set = account_comms.iter().map(|x| x.0).collect::<Vec<_>>();
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(4),
        );

        for i in 0..batch_size {
            let updated_account = accounts[i].get_state_for_payment(fee_amount).unwrap();
            assert_eq!(updated_account.balance, accounts[i].balance - fee_amount);
            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
            let path = account_tree.get_path_to_leaf_for_proof(i, 0).unwrap();
            updated_accounts.push(updated_account);
            updated_account_comms.push(updated_account_comm);
            paths.push(path);
        }

        let root = account_tree.root_node();

        // Create unique nonces for each proof
        let nonces: Vec<Vec<u8>> = (0..batch_size)
            .map(|i| format!("test_nonce_{}", i).into_bytes())
            .collect();

        let mut proofs = Vec::with_capacity(batch_size);
        let mut nullifiers = Vec::with_capacity(batch_size);

        for i in 0..batch_size {
            let (proof, nullifier) = FeePaymentProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                fee_amount,
                sks[i].0,
                &accounts[i],
                &updated_accounts[i],
                updated_account_comms[i],
                paths[i].clone(),
                &root,
                &nonces[i],
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();
            proofs.push(proof);
            nullifiers.push(nullifier);
        }

        let clock = Instant::now();

        for i in 0..batch_size {
            proofs[i]
                .verify(
                    asset_id,
                    fee_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                    None,
                )
                .unwrap();
        }

        let verifier_time = clock.elapsed();

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        // These can also be done in parallel
        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    asset_id,
                    fee_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                    None,
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        let pre_msm_check = clock.elapsed();

        let clock = Instant::now();
        batch_verify_bp(
            even_tuples,
            odd_tuples,
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
        )
        .unwrap();

        let batch_verifier_time = pre_msm_check + clock.elapsed();

        let clock = Instant::now();

        let mut even_tuples = Vec::with_capacity(batch_size);
        let mut odd_tuples = Vec::with_capacity(batch_size);

        let mut rmc_0 = RandomizedMultChecker::new(F0::rand(&mut rng));
        let mut rmc_1 = RandomizedMultChecker::new(F1::rand(&mut rng));

        for i in 0..batch_size {
            let (even, odd) = proofs[i]
                .verify_and_return_tuples(
                    asset_id,
                    fee_amount,
                    updated_account_comms[i],
                    nullifiers[i],
                    &root,
                    &nonces[i],
                    &account_tree_params,
                    account_comm_key.clone(),
                    &mut rng,
                    Some(&mut rmc_0),
                )
                .unwrap();
            even_tuples.push(even);
            odd_tuples.push(odd);
        }

        let pre_msm_check_rmc = clock.elapsed();

        let clock = Instant::now();
        add_verification_tuples_batches_to_rmc(
            even_tuples,
            odd_tuples,
            account_tree_params.even_parameters.pc_gens(),
            account_tree_params.odd_parameters.pc_gens(),
            account_tree_params.even_parameters.bp_gens(),
            account_tree_params.odd_parameters.bp_gens(),
            &mut rmc_0,
            &mut rmc_1,
        )
        .unwrap();
        verify_rmc(rmc_0, rmc_1).unwrap();
        let batch_verifier_rmc_time = pre_msm_check + clock.elapsed();

        println!(
            "For {batch_size} fee payment proofs, verifier time = {:?}, pre_msm_check time {:?}, total batch verifier time {:?}, \
            pre_msm_check_rmc time {:?}, total batch verifier_rmc time {:?}",
            verifier_time,
            pre_msm_check,
            batch_verifier_time,
            pre_msm_check_rmc,
            batch_verifier_rmc_time
        );
    }

    #[test]
    fn fee_payment_proof_parallel() {
        // W2 (Parallel): Host creates partial + host account commitment proof.
        // Ledger creates `AuthProofFeePayment` on its own `AUTH_TXN_LABEL` transcript.
        // Verifier checks host portion and auth portion independently.

        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");
        let asset_id = 1;
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let balance = 1000;
        let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk, balance);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(6),
        );

        let fee_amount = 10;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_payment(fee_amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host side: creates partial + host account commitment (without sk)
        let (partial, host_commitment_proof, auth_rerandomization, auth_new_randomness, nullifier) =
            FeePaymentSplitProtocol::new::<_, PallasParams, VestaParams>(
                &mut rng,
                fee_amount,
                &account,
                &updated_account,
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        //  Ledger side: creates AuthProofFeePayment on its own AUTH_TXN_LABEL transcript
        // Ledger needs: sk, auth's share of rerandomization/new_randomness, and public data from Host
        let rerandomized_leaf = partial.rerandomized_leaf();

        let sk_gen = account_comm_key.sk_gen();
        let randomness_gen = account_comm_key.randomness_gen();
        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        let auth_proof = AuthProofFeePayment::new(
            &mut rng,
            sk.0,
            auth_rerandomization,
            auth_new_randomness,
            &rerandomized_leaf,
            &updated_account_comm.0,
            nullifier,
            nonce,
            sk_gen,
            randomness_gen,
            b_blinding,
        )
        .unwrap();

        let proof = FeePaymentSplitProof {
            partial,
            commitment_proof: AccountCommitmentsSplitProof {
                auth_proof,
                host_proof: host_commitment_proof,
            },
        };

        // Verify host
        let (even_tuple, odd_tuple, _) = proof
            .verify_host_and_return_tuples::<_, PallasParams, VestaParams>(
                asset_id,
                fee_amount,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                None,
            )
            .unwrap();
        handle_verification_tuples(even_tuple, odd_tuple, &account_tree_params, None).unwrap();

        // Verify auth proof independently (its own AUTH_TXN_LABEL transcript)
        proof
            .commitment_proof
            .auth_proof
            .verify(
                &rerandomized_leaf,
                &updated_account_comm.0,
                nullifier,
                nonce,
                sk_gen,
                randomness_gen,
                b_blinding,
                None,
            )
            .unwrap();
    }

    #[test]
    fn fee_payment_proof_sequential() {
        // W3 (Sequential): Host creates partial + host account commitment, derives challenge_h.
        // Host sends challenge_h to Ledger. Ledger uses ledger_nonce = challenge_h_bytes || original_nonce
        // for its own AUTH_TXN_LABEL transcript.
        // Verifier derives challenge_h, verifies host, reconstructs ledger_nonce, verifies auth.

        let mut rng = rand::thread_rng();
        const NUM_GENS: usize = 1 << 13;
        const L: usize = 64;
        let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");
        let asset_id = 1;
        let (sk, pk) = keygen_sig(&mut rng, account_comm_key.sk_gen());
        let balance = 1000;
        let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, pk, balance);
        let account_comm = account.commit(account_comm_key.clone()).unwrap();

        let set = vec![account_comm.0];
        let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
            &set,
            &account_tree_params,
            Some(6),
        );

        let fee_amount = 10;
        let nonce = b"test-nonce";

        let updated_account = account.get_state_for_payment(fee_amount).unwrap();
        let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();
        let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
        let root = account_tree.root_node();

        //  Host creates partial + host account commitment
        let (protocol, mut even_prover, odd_prover, nullifier) =
            FeePaymentSplitProtocol::init::<_, PallasParams, VestaParams>(
                &mut rng,
                fee_amount,
                &account,
                &updated_account,
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        let challenge_h = protocol.challenge_h;

        //  Host sends challenge_h to Ledger
        // Ledger creates auth proof with ledger_nonce = challenge_h_bytes || original_nonce
        let mut challenge_h_bytes = Vec::new();
        challenge_h
            .serialize_compressed(&mut challenge_h_bytes)
            .unwrap();
        let ledger_nonce: Vec<u8> = challenge_h_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();

        let rerandomized_leaf = protocol.rerandomized_leaf();

        let sk_gen = account_comm_key.sk_gen();
        let randomness_gen = account_comm_key.randomness_gen();
        let b_blinding = account_tree_params
            .even_parameters
            .sl_params
            .pc_gens()
            .B_blinding;

        let auth_proof = AuthProofFeePayment::new(
            &mut rng,
            sk.0,
            protocol.auth_rerandomization,
            protocol.auth_new_randomness,
            &rerandomized_leaf,
            &updated_account_comm.0,
            nullifier,
            &ledger_nonce,
            sk_gen,
            randomness_gen,
            b_blinding,
        )
        .unwrap();

        // Host hashes auth_proof into the transcript to derive an updated challenge
        let mut auth_proof_bytes = Vec::new();
        auth_proof
            .serialize_compressed(&mut auth_proof_bytes)
            .unwrap();
        even_prover
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes);
        let challenge_h_final = even_prover
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        // Gen proof by host
        let (partial, host_commitment_proof) = protocol
            .gen_proof(
                &challenge_h_final,
                even_prover,
                odd_prover,
                &account_tree_params,
                &mut rng,
            )
            .unwrap();

        let proof = FeePaymentSplitProof {
            partial,
            commitment_proof: AccountCommitmentsSplitProof {
                auth_proof,
                host_proof: host_commitment_proof,
            },
        };

        //  Verifier derives challenge_h from host's transcript
        let (mut even_verifier, odd_verifier, challenge_h_v) = proof
            .challenge_contribution::<PallasParams, VestaParams>(
                asset_id,
                fee_amount,
                updated_account_comm,
                nullifier,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

        //  Reconstruct ledger_nonce from verifier's challenge_h
        let mut challenge_h_v_bytes = Vec::new();
        challenge_h_v
            .serialize_compressed(&mut challenge_h_v_bytes)
            .unwrap();
        let ledger_nonce_v: Vec<u8> = challenge_h_v_bytes
            .iter()
            .chain(nonce.iter())
            .copied()
            .collect();

        //  Verify auth proof with reconstructed ledger_nonce
        proof
            .commitment_proof
            .auth_proof
            .verify(
                &rerandomized_leaf,
                &updated_account_comm.0,
                nullifier,
                &ledger_nonce_v,
                sk_gen,
                randomness_gen,
                b_blinding,
                None,
            )
            .unwrap();

        // Verifier hashes auth_proof into the transcript to derive the updated challenge
        let mut auth_proof_bytes_v = Vec::new();
        proof
            .commitment_proof
            .auth_proof
            .serialize_compressed(&mut auth_proof_bytes_v)
            .unwrap();
        even_verifier
            .transcript()
            .append_message(b"auth-proof", &auth_proof_bytes_v);
        let challenge_h_final_v = even_verifier
            .transcript()
            .challenge_scalar::<F0>(TXN_CHALLENGE_LABEL);

        //  Verify host with challenge
        let (even_tuple, odd_tuple) = proof
            .verify_host_and_return_tuples_with_given_challenge::<_, PallasParams, VestaParams>(
                &challenge_h_final_v,
                even_verifier,
                odd_verifier,
                asset_id,
                fee_amount,
                updated_account_comm,
                nullifier,
                &account_tree_params,
                account_comm_key.clone(),
                &mut rng,
                None,
            )
            .unwrap();
        handle_verification_tuples(even_tuple, odd_tuple, &account_tree_params, None).unwrap();
    }

    #[cfg(feature = "ignore_prover_input_sanitation")]
    mod input_sanitation_disabled {
        use super::*;

        #[test]
        fn increase_balance_more_than_expected_in_topup_txn() {
            // A fee account sends FeeAccountTopupTxnProof but increases the balance more than the expected increase_bal_by amount. This proof should fail
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 64;
            let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

            let asset_id = 1;

            // Issuer creates keys
            let (sk_i, pk_i) = keygen_sig(&mut rng, account_comm_key.sk_gen());

            let balance = 1000;
            let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk_i, balance);
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            // Add fee account commitment in curve tree
            let set = vec![account_comm.0];
            let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
                &set,
                &account_tree_params,
                Some(3),
            );

            let increase_bal_by = 10;

            let nonce = b"test-nonce";

            // Create updated account but increase balance more than expected
            let mut updated_account = account.get_state_for_topup(increase_bal_by).unwrap();
            updated_account.balance = account.balance + 50; // Add extra on top of the actual increase amount

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let root = account_tree.root_node();

            let (proof, nullifier) = FeeAccountTopupTxnProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                &pk_i.0,
                increase_bal_by,
                &account,
                &updated_account,
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        pk_i.0,
                        asset_id,
                        increase_bal_by,
                        updated_account_comm,
                        nullifier,
                        &root,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        &mut rng,
                        None,
                    )
                    .is_err()
            );
        }

        #[test]
        fn decrease_balance_less_than_expected_in_payment_txn() {
            // A fee account sends FeePaymentProof but decreases the balance less than the expected fee_amount. This proof should fail
            let mut rng = rand::thread_rng();

            // Setup begins
            const NUM_GENS: usize = 1 << 13; // minimum sufficient power of 2 (for height 4 curve tree)
            const L: usize = 64;
            let (account_tree_params, account_comm_key, _) = setup_gens_new::<NUM_GENS>(b"testing");

            let asset_id = 1;

            // Investor has fee payment account with some balance
            let (sk, _) = keygen_sig(&mut rng, account_comm_key.sk_gen());
            let balance = 1000;
            let account = new_fee_account::<_, PallasA>(&mut rng, asset_id, sk, balance);
            let account_comm = account.commit(account_comm_key.clone()).unwrap();

            let set = vec![account_comm.0];
            let account_tree = CurveTree::<L, 1, PallasParameters, VestaParameters>::from_leaves(
                &set,
                &account_tree_params,
                Some(3),
            );

            let fee_amount = 10;
            let nonce = b"a_txn_id,a_payee_id";

            // Create updated account but decrease balance less than expected
            let mut updated_account = account.get_state_for_payment(fee_amount).unwrap();
            updated_account.balance = account.balance + 5; // Decrease by 5 less than the actual fee amount

            let updated_account_comm = updated_account.commit(account_comm_key.clone()).unwrap();

            let path = account_tree.get_path_to_leaf_for_proof(0, 0).unwrap();
            let root = account_tree.root_node();

            let (proof, nullifier) = FeePaymentProof::new::<_, PallasParams, VestaParams>(
                &mut rng,
                fee_amount,
                &account,
                &updated_account,
                updated_account_comm,
                path,
                &root,
                nonce,
                &account_tree_params,
                account_comm_key.clone(),
            )
            .unwrap();

            assert!(
                proof
                    .verify(
                        asset_id,
                        fee_amount,
                        updated_account_comm,
                        nullifier,
                        &root,
                        nonce,
                        &account_tree_params,
                        account_comm_key.clone(),
                        &mut rng,
                        None,
                    )
                    .is_err()
            );
        }
    }
}
