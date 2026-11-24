# Changelog

## Unreleased

### Mediator affirmation binds the leg

Mediator affirmation proofs bind the leg's `LegEncryptionCore` and the ephemeral public keys of all its asset encryption keys (`LegEncryption::eph_pk_enc_keys`). A signer such as a hardware wallet can then decrypt and display the leg from the same data the proof is bound to. Previously the hidden asset-id proof was bound only to the mediator entry, and the revealed asset-id proof only to the decision and nonce.

Proofs created before this change no longer verify. The serialized form of the proofs is unchanged.

#### `polymesh-dart-bp`

- `leg::mediator::MediatorTxnProof::{new, new_with_given_transcript, verify, verify_with_given_transcript}` take `core: &LegEncryptionCore<G>` and `eph_pk_enc_keys: &[EphemeralPublicKey<G>]` before `med: &MediatorEncryption<G>`. Both prover and verifier return an error when `core` has a revealed asset-id.
- `leg::mediator::PublicAssetMediatorTxnProof::{new, new_with_given_transcript}` take `med_index: usize` after `mediator_sk`, and `core` and `eph_pk_enc_keys` after `nonce`. `verify` and `verify_with_given_transcript` take `med_index` first, and `core` and `eph_pk_enc_keys` after `nonce`. Both prover and verifier return an error when `core` has a hidden asset-id. The transcript now binds `med_index`.
- New transcript label `ENC_KEYS_EPH_PK_LABEL`.

#### `polymesh-dart`

- `MediatorAffirmationProof::new` and `new_with_context` take `leg_enc: &LegEncrypted` instead of `&MediatorEncryption`, and choose the hidden or revealed asset-id proof from the leg.
- `MediatorAffirmationProof::new_revealed` and `new_revealed_with_context` are removed. Use `new` and `new_with_context`.
- `MediatorAffirmationProof::verify` and `verify_with_context` take `leg_enc: &LegEncrypted` and `lookup: impl FnOnce(AssetId, MediatorId) -> Result<AccountPublicKey, Error>`. `lookup` returns the asset's registered mediator key at the given position and is called only for a leg with a revealed asset-id. A proof whose kind does not match the leg returns `Error::InvalidProofType`.
- `MediatorAffirmationProof::verify_revealed` and `verify_revealed_with_context` are removed. Use `verify` and `verify_with_context`.
