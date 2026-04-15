use crate::Error;
use crate::error::Result;
use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_std::UniformRand;
use ark_std::collections::BTreeMap;
use ark_std::io::Write;
use ark_std::vec;
use dock_crypto_utils::randomized_mult_checker::RandomizedMultChecker;
use rand_core::CryptoRngCore;
use schnorr_pok::partial::PartialSchnorrResponse;
use schnorr_pok::{SchnorrCommitment, SchnorrResponse};

pub fn init_acc_comm_protocol<R: CryptoRngCore, G: AffineRepr, W: Write>(
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
    mut writer: W,
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

    proto_old.t.serialize_compressed(&mut writer)?;
    partial_re_randomized_account_commitment.serialize_compressed(&mut writer)?;
    proto_new.t.serialize_compressed(&mut writer)?;
    partial_updated_account_commitment.serialize_compressed(&mut writer)?;
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
    t_re_randomized_account_commitment: &G,
    resp_re_randomized_account_commitment: &SchnorrResponse<G>,
    partial_updated_account_commitment: &G,
    t_updated_account_commitment: &G,
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
        *t_re_randomized_account_commitment,
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
        *t_updated_account_commitment,
        challenge,
        missing_resps,
    );
    Ok(())
}
