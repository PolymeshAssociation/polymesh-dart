use crate::Error;
use crate::auth_proofs::account_comm_key::{AccountCommitmentKeyTrait, NUM_GENERATORS};
use crate::error::Result;
#[cfg(not(feature = "ignore_prover_input_sanitation"))]
use ark_ec::VariableBaseMSM;
use ark_ec::{AffineRepr, CurveGroup};
use ark_std::UniformRand;
use ark_std::collections::BTreeMap;
#[cfg(not(feature = "ignore_prover_input_sanitation"))]
use ark_std::string::ToString;
use ark_std::vec;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use dock_crypto_utils::transcript::{MerlinTranscript, Transcript};
use rand_core::CryptoRngCore;
use schnorr_pok::discrete_log::PokDiscreteLogProtocol;
use schnorr_pok::partial::{PartialPokDiscreteLog, PartialSchnorrResponse};
use schnorr_pok::{SchnorrChallengeContributor, SchnorrCommitment, SchnorrResponse};

pub fn init_acc_comm_protocol<R: CryptoRngCore, G: AffineRepr>(
    rng: &mut R,
    sk: G::ScalarField,
    sk_enc: G::ScalarField,
    rand_part_old_comm: G::ScalarField, // part of commitment randomness used to re-randomize the old state commitment
    rand_new_comm: G::ScalarField,      // part of commitment randomness for new state commitment
    sk_blinding: G::ScalarField,
    sk_enc_blinding: G::ScalarField,
    sk_gen: G,
    enc_key_gen: G,
    comm_re_rand_gen: G, // generator used blind the old and new commitment parts
    dst_old: &[u8],
    dst_new: &[u8],
    transcript: &mut MerlinTranscript,
) -> Result<(SchnorrCommitment<G>, SchnorrCommitment<G>, G, G)> {
    // For old (re randomized) account commitment `G_aff * sk + G_enc * sk_enc + B_blinding * rand_part_old_comm` where `rand_part_old_comm` is part of the blinding used in curve tree
    let proto_old = SchnorrCommitment::new(
        &[sk_gen, enc_key_gen, comm_re_rand_gen],
        vec![sk_blinding, sk_enc_blinding, G::ScalarField::rand(rng)],
    );

    // For new account commitment `G_aff * sk + G_enc * sk_enc + B_blinding * rand_new_comm` where `rand_new_comm` is randomness used to blind part of this new commitment
    let proto_new = SchnorrCommitment::new(
        &[sk_gen, enc_key_gen, comm_re_rand_gen],
        vec![sk_blinding, sk_enc_blinding, G::ScalarField::rand(rng)],
    );

    let pk = sk_gen * sk + enc_key_gen * sk_enc;
    let partial_re_randomized_account_commitment =
        (pk + comm_re_rand_gen * rand_part_old_comm).into_affine();
    let partial_updated_account_commitment = (pk + comm_re_rand_gen * rand_new_comm).into_affine();

    proto_old.challenge_contribution(dst_old, transcript)?;
    transcript.append(
        b"partial_acc_comm_old",
        &partial_re_randomized_account_commitment,
    );
    proto_new.challenge_contribution(dst_new, transcript)?;
    transcript.append(b"partial_acc_comm_new", &partial_updated_account_commitment);
    Ok((
        proto_old,
        proto_new,
        partial_re_randomized_account_commitment,
        partial_updated_account_commitment,
    ))
}

pub fn resp_acc_comm<G: AffineRepr>(
    sk: G::ScalarField,
    sk_enc: G::ScalarField,
    rand_part_old_comm: G::ScalarField,
    rand_new_comm: G::ScalarField,
    proto_old: &SchnorrCommitment<G>,
    proto_new: &SchnorrCommitment<G>,
    challenge: &G::ScalarField,
) -> Result<(SchnorrResponse<G>, PartialSchnorrResponse<G>)> {
    // old commitment gets the full proof
    let resp_re_randomized_account_commitment =
        proto_old.response(&[sk, sk_enc, rand_part_old_comm], &challenge)?;
    // new commitment gets the partial proof (sk and sk_enc responses shared from old)
    let mut missing_resp = BTreeMap::new();
    missing_resp.insert(2, rand_new_comm);
    let resp_updated_account_commitment = proto_new.partial_response(missing_resp, &challenge)?;
    Ok((
        resp_re_randomized_account_commitment,
        resp_updated_account_commitment,
    ))
}

pub fn verify_acc_comm<G: AffineRepr>(
    partial_re_randomized_account_commitment: &G,
    resp_re_randomized_account_commitment: &SchnorrResponse<G>,
    partial_updated_account_commitment: &G,
    resp_updated_account_commitment: &PartialSchnorrResponse<G>,
    challenge: &G::ScalarField,
    sk_gen: G,
    enc_key_gen: G,
    comm_re_rand_gen: G, // generator used blind the old and new commitment parts
    mut rmc: Option<&mut RandomizedMultChecker<G>>,
) -> Result<()> {
    if resp_re_randomized_account_commitment.len() != 3 {
        return Err(Error::DifferentNumberOfResponsesForSigmaProtocol(
            3,
            resp_re_randomized_account_commitment.len(),
        ));
    }

    // Verify old account commitment (full Schnorr response over [sk_gen, enc_key_gen, comm_re_rand_gen])
    verify_schnorr_resp_or_rmc!(
        rmc,
        resp_re_randomized_account_commitment,
        vec![sk_gen, enc_key_gen, comm_re_rand_gen],
        *partial_re_randomized_account_commitment,
        challenge,
    );

    // Verify new account commitment (partial Schnorr response; sk and sk_enc responses shared from old)
    let mut missing_resps = BTreeMap::new();
    missing_resps.insert(0, resp_re_randomized_account_commitment.0[0]); // sk response
    missing_resps.insert(1, resp_re_randomized_account_commitment.0[1]); // sk_enc response
    verify_partial_schnorr_resp_or_rmc!(
        rmc,
        resp_updated_account_commitment,
        vec![sk_gen, enc_key_gen, comm_re_rand_gen],
        *partial_updated_account_commitment,
        challenge,
        missing_resps,
    );
    Ok(())
}

/// Starts the proof of `rand_new_comm_anchor = anchor_gen * rand_new_comm` and returns it with
/// `rand_new_comm_anchor`. Reuses the blinding of `rand_new_comm` in `proto_new`, so the proof shares
/// the response for `rand_new_comm` in `resp_updated_account_commitment`.
pub fn init_rand_new_comm_anchor_protocol<G: AffineRepr>(
    rand_new_comm: G::ScalarField,
    proto_new: &SchnorrCommitment<G>,
    anchor_gen: G,
    dst: &[u8],
    transcript: &mut MerlinTranscript,
) -> Result<(PokDiscreteLogProtocol<G>, G)> {
    let rand_new_comm_anchor = (anchor_gen * rand_new_comm).into_affine();
    let proto = PokDiscreteLogProtocol::init(rand_new_comm, proto_new.blindings[2], &anchor_gen);
    proto.challenge_contribution(&anchor_gen, &rand_new_comm_anchor, dst, transcript)?;
    Ok((proto, rand_new_comm_anchor))
}

/// Verifies `rand_new_comm_anchor = anchor_gen * rand_new_comm` using the response for
/// `rand_new_comm` in `resp_updated_account_commitment`.
pub fn verify_rand_new_comm_anchor<G: AffineRepr>(
    rand_new_comm_anchor: G,
    resp_rand_new_comm_anchor: &PartialPokDiscreteLog<G>,
    resp_updated_account_commitment: &PartialSchnorrResponse<G>,
    challenge: &G::ScalarField,
    anchor_gen: G,
    mut rmc: Option<&mut RandomizedMultChecker<G>>,
) -> Result<()> {
    let resp_rand_new_comm = resp_updated_account_commitment.get_response(2)?;
    verify_or_rmc_2!(
        rmc,
        resp_rand_new_comm_anchor,
        "rand_new_comm anchor proof is invalid",
        rand_new_comm_anchor,
        anchor_gen,
        challenge,
        resp_rand_new_comm,
    );
    Ok(())
}

/// Errors unless `updated_account_commitment = sk_gen * sk + sk_enc_gen * sk_enc + \sum_i{new_acc_openings[i] * as_gens_without_sk()[i]}`.
/// `account_comm_key` must be the device's own copy of the system generators, not one supplied by
/// the host.
#[cfg_attr(feature = "ignore_prover_input_sanitation", allow(unused_variables))]
pub fn ensure_correct_updated_account_commitment<G: AffineRepr>(
    sk: G::ScalarField,
    sk_enc: G::ScalarField,
    updated_account_commitment: &G,
    new_acc_openings: &[G::ScalarField; NUM_GENERATORS - 2],
    account_comm_key: &impl AccountCommitmentKeyTrait<G>,
) -> Result<()> {
    #[cfg(not(feature = "ignore_prover_input_sanitation"))]
    {
        let pk = account_comm_key.sk_gen() * sk + account_comm_key.sk_enc_gen() * sk_enc;
        let expected = G::Group::msm(&account_comm_key.as_gens_without_sk()[..], new_acc_openings)
            .map_err(Error::size_mismatch)?
            + pk;
        if expected.into_affine() != *updated_account_commitment {
            return Err(Error::ProofGenerationError(
                "updated account commitment is not a canonical account commitment for the supplied openings"
                    .to_string(),
            ));
        }
    }
    Ok(())
}
