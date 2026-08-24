//! Domain-separation tags for Fiat-Shamir challenge contributions.
//! Each constant names the relation the underlying Sigma protocol proves. It is passed as the
//! `dst` argument of `challenge_contribution`/`compute_challenge_contribution`.

/// Defines `pub const NAME: &[u8]` for each entry and registers them for the uniqueness test.
macro_rules! define_dsts {
    ($($(#[$m:meta])* $name:ident = $val:expr;)*) => {
        $($(#[$m])* pub const $name: &[u8] = $val;)*
        #[cfg(test)]
        pub(crate) const ALL: &[(&str, &[u8])] = &[$((stringify!($name), $val)),*];
    };
}

define_dsts! {
    // --- Authorization proofs (knowledge of secret keys) ---
    /// PoK of the affirmation secret key for `pk_aff` under `sk_aff_gen`.
    AUTH_SK_AFF = b"dart/auth/sk-aff";
    /// PoK of the encryption secret key for `pk_enc` under `sk_enc_gen`.
    AUTH_SK_ENC = b"dart/auth/sk-enc";
    /// PoK of a single secret key (fee registration / topup auth).
    AUTH_SK = b"dart/auth/sk";

    // --- Account state change (sigma commitments to randomness) ---
    /// Opening of the re-randomized old account commitment (leaf).
    ACCOUNT_COMM_OLD = b"dart/account/comm-old";
    /// Opening of the new account commitment (new leaf).
    ACCOUNT_COMM_NEW = b"dart/account/comm-new";
    /// Opening of the BP vector commitment for the randomness/sk_enc relations.
    BP_RANDOMNESS_RELATIONS = b"dart/account/bp-randomness-relations";
    /// Opening of the BP vector commitment for the balance change.
    BP_BALANCE = b"dart/account/bp-balance";
    /// PoK of the initial nullifier discrete log.
    NULLIFIER = b"dart/account/nullifier";

    // --- Leg link (party amount / asset-id ciphertext well-formedness) ---
    /// Amount ciphertext well-formedness for a leg (`eph_pk_amount`, `enc_gen`, `ct_amount`).
    LEG_AMOUNT = b"dart/leg/amount";
    /// Hidden asset-id ciphertext well-formedness for a leg.
    LEG_ASSET_ID = b"dart/leg/asset-id";
    /// Asset-id revealed elsewhere: discrete-log form for a leg.
    LEG_ASSET_ID_ELSEWHERE = b"dart/leg/asset-id-elsewhere";

    // --- Leg creation (leg's own internal well-formedness, distinct from the leg-link above) ---
    /// Opening of the BP vector commitment to amount, the `r_i` chain, and the auditor/mediator
    /// blinding ratios.
    LEG_CREATE_BP_R_I_AMOUNT = b"dart/leg-create/bp-r-i-amount";
    /// Sender's ciphertext `ct_s = enc_key_gen * r_1 + pk_s`.
    LEG_CREATE_CT_S = b"dart/leg-create/ct-s";
    /// Receiver's ciphertext `ct_r = enc_key_gen * r_2 + pk_r`.
    LEG_CREATE_CT_R = b"dart/leg-create/ct-r";
    /// `ct_amount = enc_key_gen * r_3 + enc_gen * amount`.
    LEG_CREATE_CT_AMOUNT = b"dart/leg-create/ct-amount";
    /// `ct_asset_id = enc_key_gen * r_4 + enc_gen * asset_id`.
    LEG_CREATE_CT_ASSET_ID = b"dart/leg-create/ct-asset-id";
    /// Sender's `S[2] = S[0] * r_3/r_1` (amount channel).
    LEG_CREATE_EPH_PK_S_V = b"dart/leg-create/eph-pk-s-v";
    /// Sender's `S[3] = S[0] * r_4/r_1` (asset-id channel).
    LEG_CREATE_EPH_PK_S_AT = b"dart/leg-create/eph-pk-s-at";
    /// Receiver's `R[2] = R[1] * r_3/r_2` (amount channel).
    LEG_CREATE_EPH_PK_R_V = b"dart/leg-create/eph-pk-r-v";
    /// Receiver's `R[3] = R[1] * r_4/r_2` (asset-id channel).
    LEG_CREATE_EPH_PK_R_AT = b"dart/leg-create/eph-pk-r-at";
    /// Sender's `S[1] = S[0] * r_2/r_1`, present only when parties see each other.
    LEG_CREATE_EPH_PK_S_R = b"dart/leg-create/eph-pk-s-r";
    /// Receiver's `R[0] = R[1] * r_1/r_2`, present only when parties see each other.
    LEG_CREATE_EPH_PK_R_S = b"dart/leg-create/eph-pk-r-s";
    /// Auditor's first ephemeral point tied to the asset-tree leaf's re-randomized point.
    LEG_CREATE_ENC_KEY_R1 = b"dart/leg-create/enc-key-r1";
    /// Auditor's blinding-consistency check for its re-randomized leaf point.
    LEG_CREATE_ENC_KEY_BLINDING = b"dart/leg-create/enc-key-blinding";
    /// Auditor's `eph_pk_enc_key.r2 = eph_pk_enc_key.r1 * r_2/r_1` (receiver channel).
    LEG_CREATE_ENC_KEY_R2 = b"dart/leg-create/enc-key-r2";
    /// Auditor's `eph_pk_enc_key.r3 = eph_pk_enc_key.r1 * r_3/r_1` (amount channel).
    LEG_CREATE_ENC_KEY_R3 = b"dart/leg-create/enc-key-r3";
    /// Auditor's `eph_pk_enc_key.r4 = eph_pk_enc_key.r1 * r_4/r_1` (asset-id channel).
    LEG_CREATE_ENC_KEY_R4 = b"dart/leg-create/enc-key-r4";
    /// Mediator's `ct_med - re_rand_point = enc_key_gen * m_i + B_blinding * (-blinding)`.
    LEG_CREATE_MED_KEY_CT = b"dart/leg-create/med-key-ct";
    /// Mediator's blinding-consistency check for its re-randomized leaf point.
    LEG_CREATE_MED_KEY_BLINDING = b"dart/leg-create/med-key-blinding";
    /// Mediator's ephemeral key tied to one auditor's ephemeral point via `m_i / r_1`.
    LEG_CREATE_MED_KEY_ENC = b"dart/leg-create/med-key-enc";
    /// Public (non-leaf) encryption key's `r_1` point.
    LEG_CREATE_PUBLIC_ENC_R1 = b"dart/leg-create/public-enc-r1";
    /// Public encryption key's `r_2` point.
    LEG_CREATE_PUBLIC_ENC_R2 = b"dart/leg-create/public-enc-r2";
    /// Public encryption key's `r_3` point.
    LEG_CREATE_PUBLIC_ENC_R3 = b"dart/leg-create/public-enc-r3";
    /// Public encryption key's `r_4` point.
    LEG_CREATE_PUBLIC_ENC_R4 = b"dart/leg-create/public-enc-r4";
    /// Opening of the asset-id point `j_0 * (asset_id + 1)` minus `j_0`, shared with the
    /// `ct_asset_id` relation's plaintext.
    LEG_CREATE_ASSET_ID_POINT = b"dart/leg-create/asset-id-point";

    // --- Public-asset leg creation (asset-id revealed: no curve tree, no mediator ciphertexts) ---
    /// Opening of the BP vector commitment to amount and the `r_i` chain, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_BP_R_I_AMOUNT = b"dart/public-asset-leg-create/bp-r-i-amount";
    /// Sender's ciphertext `ct_s = enc_key_gen * r_1 + pk_s`, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_CT_S = b"dart/public-asset-leg-create/ct-s";
    /// Receiver's ciphertext `ct_r = enc_key_gen * r_2 + pk_r`, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_CT_R = b"dart/public-asset-leg-create/ct-r";
    /// `ct_amount = enc_key_gen * r_3 + enc_gen * amount`, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_CT_AMOUNT = b"dart/public-asset-leg-create/ct-amount";
    /// Sender's `S[2] = S[0] * r_3/r_1`, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_EPH_PK_S_V = b"dart/public-asset-leg-create/eph-pk-s-v";
    /// Receiver's `R[2] = R[1] * r_3/r_2`, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_EPH_PK_R_V = b"dart/public-asset-leg-create/eph-pk-r-v";
    /// Sender's `S[1] = S[0] * r_2/r_1`, public-asset variant, present only when parties see each other.
    PUBLIC_ASSET_LEG_CREATE_EPH_PK_S_R = b"dart/public-asset-leg-create/eph-pk-s-r";
    /// Receiver's `R[0] = R[1] * r_1/r_2`, public-asset variant, present only when parties see each other.
    PUBLIC_ASSET_LEG_CREATE_EPH_PK_R_S = b"dart/public-asset-leg-create/eph-pk-r-s";
    /// Asset auditor's `A[i][0] = pk_en[i] * r_1`, public-asset variant (plain key, no curve tree).
    PUBLIC_ASSET_LEG_CREATE_ENC_KEY_R1 = b"dart/public-asset-leg-create/enc-key-r1";
    /// Asset auditor's `A[i][1] = pk_en[i] * r_2`, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_ENC_KEY_R2 = b"dart/public-asset-leg-create/enc-key-r2";
    /// Asset auditor's `A[i][2] = pk_en[i] * r_3`, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_ENC_KEY_R3 = b"dart/public-asset-leg-create/enc-key-r3";
    /// Public (leg-creator specified) auditor's `r_1` point, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_PUBLIC_ENC_R1 = b"dart/public-asset-leg-create/public-enc-r1";
    /// Public auditor's `r_2` point, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_PUBLIC_ENC_R2 = b"dart/public-asset-leg-create/public-enc-r2";
    /// Public auditor's `r_3` point, public-asset variant.
    PUBLIC_ASSET_LEG_CREATE_PUBLIC_ENC_R3 = b"dart/public-asset-leg-create/public-enc-r3";

    // --- Proof of balance (PoB) ---
    /// Opening of the reduced account commitment (rho, current_rho, randomness, current_randomness),
    /// shared by the with-auditor and with-anyone PoB proofs.
    POB_ACC = b"dart/pob/acc";
    /// PoK of the initial nullifier discrete log for a PoB proof.
    POB_NULLIFIER = b"dart/pob/nullifier";
    /// PoK of `sk` in the revealed affirmation public key.
    POB_PK = b"dart/pob/pk";
    /// PoK of `sk_enc` in the revealed encryption public key.
    POB_PK_ENC = b"dart/pob/pk-enc";
    /// PoK of `sk_enc^-1` in `pk_enc`, with bases swapped from [`POB_PK_ENC`].
    POB_ENC_KEY_GEN_INV = b"dart/pob/enc-key-gen-inv";
    /// PoB prover's sender-role ciphertext-participant proof: `ct_s - pk_enc = S[0] * sk_enc^-1`.
    POB_PARTICIPANT_SEND = b"dart/pob/participant-send";
    /// PoB prover's receiver-role ciphertext-participant proof: `ct_r - pk_enc = R[0] * sk_enc^-1`.
    POB_PARTICIPANT_RECV = b"dart/pob/participant-recv";
    /// PoB pending-leg asset-id ciphertext consistency: `ct_at - enc_gen * at = eph_pk * sk_enc^-1`.
    POB_ASSET_ID = b"dart/pob/asset-id";
    /// PoB total pending-sent-amount consistency across sender-role legs.
    POB_SENT_AMOUNT = b"dart/pob/sent-amount";
    /// PoB total pending-received-amount consistency across receiver-role legs.
    POB_RECV_AMOUNT = b"dart/pob/recv-amount";

    // --- Host-side split ciphertexts (welded into the leg link by the auth proof) ---
    /// Host's `ct_asset_id_2 = enc_gen * asset_id + B_blinding * (-k)`.
    HOST_CT_ASSET_ID_2 = b"dart/host/ct-asset-id-2";
    /// Host's `ct_amount_2 = enc_gen * amount + B_blinding * (-k)`.
    HOST_CT_AMOUNT_2 = b"dart/host/ct-amount-2";

    // --- Encryption-key distribution ---
    /// BP vector commitment to all chunks of the distributed secret key.
    KEY_DIST_COMM_SK_CHUNKS_BP = b"dart/key-dist/comm-sk-chunks-bp";
    /// Shared per-chunk ciphertext `C_i = enc_key_gen * r_i + enc_gen * sk_i`.
    KEY_DIST_SHARED_CT = b"dart/key-dist/shared-ct";
    /// Per-recipient per-chunk ciphertext `E_ji = recipient_pk_j * r_i`.
    KEY_DIST_RECIPIENT_CT = b"dart/key-dist/recipient-ct";
    /// Combined (weighted-sum) ciphertext tying the chunks to the full secret key.
    KEY_DIST_COMBINED = b"dart/key-dist/combined";
    /// PoK of `sk` in the public key `pk = enc_key_gen * sk`.
    KEY_DIST_PK = b"dart/key-dist/pk";

    // --- Fee account state change ---
    /// Opening of the re-randomized old fee-account commitment (leaf), solo mode (with sk).
    FEE_ACCOUNT_COMM_OLD_WITH_SK = b"dart/fee-account/comm-old-with-sk";
    /// Opening of the new fee-account commitment (new leaf), solo mode (with sk).
    FEE_ACCOUNT_COMM_NEW_WITH_SK = b"dart/fee-account/comm-new-with-sk";
    /// Opening of the re-randomized old fee-account commitment (leaf), split mode (without sk).
    FEE_ACCOUNT_COMM_OLD_WITHOUT_SK = b"dart/fee-account/comm-old-without-sk";
    /// Opening of the new fee-account commitment (new leaf), split mode (without sk).
    FEE_ACCOUNT_COMM_NEW_WITHOUT_SK = b"dart/fee-account/comm-new-without-sk";
    /// Opening of the reduced fee-account commitment at registration (rho, randomness).
    FEE_REG_COMM = b"dart/fee-account/reg-comm";
    /// PoK of the initial nullifier discrete log for a fee-account state change.
    FEE_NULLIFIER = b"dart/fee-account/nullifier";
    /// Pedersen commitment to the new balance, range-checked, for a fee-account state change.
    FEE_BP_BALANCE = b"dart/fee-account/bp-balance";

    // --- Transparent account state change (deposit/withdraw) ---
    /// Opening of the old transparent account commitment, solo mode (with sk).
    TRANSPARENT_ACCOUNT_COMM_OLD_WITH_SK = b"dart/transparent/comm-old-with-sk";
    /// Opening of the new transparent account commitment, solo mode (with sk).
    TRANSPARENT_ACCOUNT_COMM_NEW_WITH_SK = b"dart/transparent/comm-new-with-sk";
    /// Opening of the old transparent account commitment, split mode (without sk).
    TRANSPARENT_ACCOUNT_COMM_OLD_WITHOUT_SK = b"dart/transparent/comm-old-without-sk";
    /// Opening of the new transparent account commitment, split mode (without sk).
    TRANSPARENT_ACCOUNT_COMM_NEW_WITHOUT_SK = b"dart/transparent/comm-new-without-sk";
    /// PoK of the initial nullifier discrete log for a transparent state change.
    TRANSPARENT_NULLIFIER = b"dart/transparent/nullifier";
    /// Opening of the BP vector commitment for the rho/randomness relations (and balance
    /// range, for withdrawals) of a transparent state change.
    TRANSPARENT_BP = b"dart/transparent/bp";
    /// PoK of the encryption randomness/sk shared between an auditor's ephemeral key and the
    /// encrypted account public key.
    TRANSPARENT_ENC_PUBKEY_ENC = b"dart/transparent/enc-pubkey-enc";
    /// PoK of the encryption randomness for one auditor's ephemeral public key share.
    TRANSPARENT_ENC_PUBKEY_EPH = b"dart/transparent/enc-pubkey-eph";

    // --- Account registration ---
    /// Opening of the reduced account commitment (rho, current_rho, randomness, current_randomness).
    REG_COMM = b"dart/reg/comm";
    /// PoK of the initial nullifier discrete log (`rho`).
    REG_INITIAL_NULLIFIER = b"dart/reg/initial-nullifier";
    /// Opening of the BP vector commitment for the rho/randomness relation.
    REG_BP_RHO = b"dart/reg/bp-rho";
    /// Opening of the BP vector commitment to the encrypted-for-`T` scalar chunks (s and rho).
    REG_BP_S_RHO_CHUNKS = b"dart/reg/bp-s-rho-chunks";
    // --- Authorization proofs: device's account-commitment share (split affirmation) ---
    /// Opening of the auth device's share of the re-randomized old account commitment
    /// (`sk_gen * sk + enc_key_gen * sk_enc + comm_re_rand_gen * rand`), leg-affirmation domain.
    AUTH_ACC_COMM_OLD = b"dart/auth/acc-comm-old";
    /// Opening of the auth device's share of the new account commitment, leg-affirmation domain.
    AUTH_ACC_COMM_NEW = b"dart/auth/acc-comm-new";
    /// Opening of the auth device's share of the old account commitment, transparent
    /// (deposit/withdraw) domain.
    TRANSPARENT_AUTH_ACC_COMM_OLD = b"dart/auth/transparent-acc-comm-old";
    /// Opening of the auth device's share of the new account commitment, transparent domain.
    TRANSPARENT_AUTH_ACC_COMM_NEW = b"dart/auth/transparent-acc-comm-new";
    /// Opening of the auth device's share of the old account commitment, fee-account domain.
    FEE_AUTH_ACC_COMM_OLD = b"dart/auth/fee-acc-comm-old";
    /// Opening of the auth device's share of the new account commitment, fee-account domain.
    FEE_AUTH_ACC_COMM_NEW = b"dart/auth/fee-acc-comm-new";
    /// Auth device's `ct_amount_1 = Eph_amt * sk_enc^-1 + comm_re_rand_gen * k_1` for a leg.
    AUTH_LEG_AMOUNT = b"dart/auth/leg-amount";
    /// Auth device's hidden `ct_asset_id_1 = Eph_at * sk_enc^-1 + comm_re_rand_gen * k_2` for a leg.
    AUTH_LEG_ASSET_ID = b"dart/auth/leg-asset-id";
    /// Auth device's asset-id-revealed-elsewhere form: `ct_asset_id - enc_gen * at = Eph_at * sk_enc^-1`.
    AUTH_LEG_ASSET_ID_ELSEWHERE = b"dart/auth/leg-asset-id-elsewhere";
    /// `D = enc_key_gen * sk_enc + comm_re_rand_gen * r`.
    AUTH_D = b"dart/auth/d";
    /// `enc_key_gen = D * sk_enc^-1 - comm_re_rand_gen * r * sk_enc^-1`.
    AUTH_ENC_KEY_GEN_INV = b"dart/auth/enc-key-gen-inv";

    // --- Mint ---
    /// Opening of the re-randomized old account commitment (leaf) for a mint state change.
    MINT_ACCOUNT_COMM_OLD = b"dart/mint/account-comm-old";
    /// Opening of the new account commitment (new leaf) for a mint state change.
    MINT_ACCOUNT_COMM_NEW = b"dart/mint/account-comm-new";
    /// PoK of the initial nullifier discrete log for a mint state change.
    MINT_NULLIFIER = b"dart/mint/nullifier";
    /// Opening of the BP vector commitment for the mint rho/randomness relations.
    MINT_BP = b"dart/mint/bp";

    // --- Mediator (legacy pre-broadcast leg format) ---
    /// `ct_med = eph_pk_med_key * sk_enc^-1 + sig_key_gen * sk_aff` for the single mediator
    /// encryption key of a `MediatorEncryptionOld` leg.
    MEDIATOR_OLD_ENC_PK = b"dart/mediator/old-enc-pk";
    /// PoK of the mediator's affirmation secret key when the leg's asset-id is revealed.
    MEDIATOR_PUBLIC_ASSET = b"dart/mediator/public-asset";

    /// PoK of a chunk's encryption randomness in its ephemeral key, shared by the `s` and `rho`
    /// chunk encryptions (same `enc_key_gen` base for both).
    REG_ENC_CHUNK_EPH = b"dart/reg/enc-chunk-eph";
    /// Ciphertext well-formedness for one scalar chunk, shared by the `s` and `rho` chunk
    /// encryptions (same `pk_T`/`enc_gen` bases for both).
    REG_ENC_CHUNK_ENC = b"dart/reg/enc-chunk-enc";
    /// Ciphertext well-formedness for the combined (weighted-sum) scalar, shared by `s` and `rho`
    /// (same `pk_T`/`enc_gen` bases for both).
    REG_ENC_COMBINED = b"dart/reg/enc-combined";
}

#[cfg(test)]
mod tests {
    use super::ALL;
    use ark_std::collections::BTreeMap;

    /// Every relation tag must be distinct; a collision would silently merge two relations'
    /// challenge transcripts, which round-trip tests cannot catch.
    #[test]
    fn all_dsts_unique() {
        let mut seen: BTreeMap<&[u8], &str> = BTreeMap::new();
        for (name, val) in ALL {
            assert!(!val.is_empty(), "{name} has an empty DST");
            if let Some(prev) = seen.insert(val, name) {
                panic!(
                    "duplicate DST value shared by {prev} and {name}: {:?}",
                    core::str::from_utf8(val).unwrap_or("<non-utf8>")
                );
            }
        }
    }
}
