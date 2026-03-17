# DART transaction flows (settlement-centric)

This document describes the *transaction-level* lifecycle of DART as implemented in this repo, with a focus on **settlement** creation and the actions that can happen after a settlement exists.

It is intended to be a shared “mental model” for humans and AIs reviewing the code: if the code does something different than what is described here, that mismatch is likely a bug, missing feature, or a doc gap.

## What this doc covers (and what it doesn’t)

- Covers: the externally-visible flow and state transitions for “DART txns” as they appear in the Rust API and tests.
- Does **not** cover: prover/verifier algebra, Bulletproof internals, curve-tree internals, or full cryptographic derivations (those live in `dart-bp/docs/*.md`).

## Repo structure and trust boundaries (useful for AI readers)

This repository is layered:

- `dart-bp/` is the **cryptographic specification + prover/verifier implementation** (Bulletproofs R1CS + sigma protocols). Treat anything it verifies as **untrusted input**: a verifier must not panic on malformed proofs.
- `src/bp/` is a **higher-level wrapper API** used by the rest of the repo/tests. It bridges runtime-friendly types (encoding, bounded vectors, etc.) to the lower-level `dart-bp` objects.

Practical implication for code review:

- Verifier entrypoints should return `Error::ProofVerificationError(...)` (or other `Error` variants) on malformed inputs.
- Avoid verifier-side `unwrap`, `expect`, `assert!`, unchecked indexing, or map indexing (which can panic) on any value that can be influenced by proof bytes.

## Testing-only feature: `ignore_prover_input_sanitation`

The `dart-bp` crate includes a feature flag `ignore_prover_input_sanitation`.

- When enabled, it **disables prover-side input checks** (sanity checks that normally prevent constructing inconsistent internal witness/state).
- This exists to support **negative testing**: generate “bad prover data” and ensure verifiers reject it safely.
- It must **not** be enabled in production builds.

This is especially relevant when reading tests that intentionally exercise verifier robustness.

## Batch verification and RMC (why some verifiers look unusual)

Some verification paths support batch-style operation:

- A verifier may compute intermediate “verification tuples” and then either:
   - verify them immediately, or
   - aggregate them into a `RandomizedMultChecker` (RMC) and verify once at the end.

This is a performance optimization; it should not change the functional flow/state machine described in this doc.

## Core objects and “where truth lives”

At a high level, the system is driven by three families of objects:

1. **State accumulators (curve trees)**
   - Asset tree (publicly tracks assets and their associated keys)
   - Account tree (append-only accumulator of confidential account state commitments)

2. **Encrypted settlement data**
   - A settlement is a list of “legs” (`Leg`s). Each leg is an intended transfer of one asset from a sender account to a receiver account.
   - The chain stores only *encrypted legs* plus proofs. Plaintext leg details are recovered only by authorized parties (sender/receiver/auditors/mediators) via decryption.

3. **Proof-bearing transactions**
   - Settlement creation proof: proves legs were formed consistently and encrypted correctly, and (when asset-id is hidden) proves the asset exists in the asset tree.
   - Settlement follow-on proofs: sender/receiver affirmations, mediator accept/reject, and finalization/reversal proofs.

The best “executable spec” for flows is the integration tests under `tests/`, especially `tests/simple_mint_and_transfer.rs`.

## Transaction taxonomy (big picture)

DART supports several user-visible transaction types. This doc lists them to give context, but the remainder focuses on settlement flows.

### Setup / provisioning

- **Key registration**: register (at least) an encryption key and an affirmation key on-chain.
- **Account registration / initialization for an asset**: create the initial confidential account state for a specific asset.
- **Asset creation**: issuer creates an asset and may attach auditors and/or mediators (both are optional).

### Fee accounts (separate from settlement)

There is an additional “fee account” subsystem used to pay transaction fees privately.

- **Fee account registration**: initialize a confidential fee account state for a specific payment asset.
- **Fee account top-up**: increase the confidential fee account balance.
- **Fee payment**: spend from a fee account to pay for a batch of proofs/transactions.

These flows are implemented via fee-account proofs in `dart-bp` and wrapped in `src/bp/fee.rs`.

### State transitions not involving other parties

- **Mint**: issuer increases balance of their own account for the asset.

### Settlement-related transactions (main focus)

- **Create settlement**: publish the encrypted legs + settlement creation proof.
- **Sender affirmation**: sender consumes its current account state and produces a new state reflecting “I have committed to sending”.
- **Receiver affirmation**: receiver consumes its current account state and produces a new state reflecting “I have committed to receiving”.
- **Mediator affirmation** (optional, per leg): mediator accepts or rejects a leg.

After enough affirmations exist, the settlement transitions into an **executed** phase, and then requires leg-by-leg finalization.

- **Receiver claim** (finalization): receiver updates state to actually claim the funds from an executed settlement.
- **Sender counter update** (finalization): sender updates its state to finalize its leg.

If a mediator rejects, the settlement transitions into a **rejected** phase.

- **Sender reversal** (rejection cleanup): sender can undo its earlier “send” transition for a rejected leg.

### “Instant” / batched variants

To reduce the number of on-chain calls, the code also supports submitting bundles:

- **Instant settlement**: submit the settlement creation proof and the sender/receiver affirmations together, and execute immediately.
- **Batched settlement**: submit a settlement creation proof with some (or all) sender/receiver affirmations included.

(These bundling types exist as dedicated proof containers; they don’t change the underlying state machine, they just reduce the number of separate extrinsics/txns.)

## Settlement model

### Settlement = memo + legs

In the Rust API, a settlement is built with:

- `SettlementBuilder::new(memo)` and `.leg(LegBuilder { ... })`, then
- `encrypt_and_prove(rng, asset_tree)`

Each leg is built from:

- `sender: AccountPublicKeys` (includes a confidential account public key and an encryption public key)
- `receiver: AccountPublicKeys`
- `asset: AssetState` (contains the asset id and the asset’s auditor/mediator key sets)
- `amount: Balance`
- `config: LegConfig` (options described below)
- `public_enc_keys` / `public_med_keys` (extra non-asset-tied auditors/mediators)

A settlement identifier/reference is derived from the settlement proof bytes (see `SettlementProof::settlement_ref()`); tests treat it as the settlement id.

### Leg options (what the settlement creator can choose)

Leg creation has two primary configuration knobs, exposed as `LegConfig`:

1. `reveal_asset_id: bool`
   - `false` (default): asset-id is encrypted in the leg; the leg proof includes **asset-tree membership** without revealing the asset.
   - `true`: asset-id is public in that leg; the proof is simpler and does not require the asset-tree membership sub-proof.

2. `parties_see_each_other: bool`
   - If `true`, sender can decrypt receiver’s account public key and vice versa (i.e., they can learn “who they are trading with” at the account-key level).
   - If `false`, ephemeral material for “learn the other party” is omitted unless needed for auditors/mediators.

Additionally, the leg creator can append:

- `public_enc_keys`: extra auditor-like encryption keys that are always revealed as explicit keys in the leg.
- `public_med_keys`: extra mediator affirmation keys associated with indices into `public_enc_keys`.

Key distribution note:

- The leg encryption keys used to encrypt leg details can be **shared** across auditors and mediators (i.e., both roles decrypt using keys drawn from the same encryption-key set).
- The fact that a given set of encryption keys is properly bound/authorized to a given asset/role set is proven via a **key distribution proof** (`KeyDistributionProof`).
- Conceptually, for a given leg there can be 0 or more **encryption keys** (used for decryption by auditors and/or mediators) and 0 or more **mediator affirmation keys** (each mediator has its own affirmation key).
- Constraint: if there is even 1 mediator (i.e., at least one mediator affirmation key is required), there must be at least 1 encryption key available so mediators can decrypt what they are affirming.

These appended keys are *not* “asset metadata”; they are leg-specific disclosure.

## Settlement encryption and who can decrypt

The encrypted leg contains ciphertexts and per-recipient ephemeral values so multiple recipients can decrypt the **same** on-chain ciphertext.

Conceptually, each leg encrypts:

- sender account public key
- receiver account public key
- amount
- (optionally) asset-id (omitted when `reveal_asset_id=true`)

Recipients and what they can do:

- **Sender / receiver**: decrypt using their encryption secret key.
- **Asset auditors (optional)**: if configured for the asset/leg, can decrypt using an authorized encryption secret key (the leg includes ephemeral material derived from the relevant encryption key set).
- **Asset mediators (optional)**: if configured for the asset/leg, can decrypt using an authorized encryption secret key, and can additionally submit an accept/reject affirmation using their own mediator affirmation key.

In code, this corresponds to decrypting a `LegEncrypted` using a `LegRole` and the party’s keys (see usage in tests via `decrypt_leg(...)` and mediator logic).

Important practical point: amount and (when encrypted) asset-id are chosen to be small enough that recovering the scalar from a group element (discrete log) is feasible for authorized parties.

## Settlement state machine

There are two nested state machines:

- **SettlementStatus** (settlement-level): `Pending → Executed → Finalized` or `Pending → Rejected → Finalized`
- **AffirmationStatus** (per leg, per role): `Pending / Affirmed / Rejected / Finalized`

### SettlementStatus

The code and tests use the following settlement-level statuses:

- `Pending`
  - Settlement exists on-chain (encrypted legs + creation proof are stored).
  - Parties can still submit required affirmations.

- `Executed`
  - All required *affirmations* (sender/receiver and any mediators) have been submitted and accepted.
  - The settlement is now “in the executed phase”: parties must submit finalization proofs (claim/counter updates) to finish the leg transitions.

- `Rejected`
  - At least one required mediator rejected a leg, which rejects the settlement.
  - Parties must clean up by submitting reversal/finalization proofs (e.g., sender reversal).

- `Finalized`
  - All legs are fully finalized (either executed+finalized, or rejected+cleaned up).
  - Settlement state can be pruned/archived.

### Leg-level statuses and when the settlement transitions

Each leg has (at minimum) sender and receiver statuses, and optionally mediator statuses.

- A settlement remains `Pending` while *any* required affirmation is still `Pending`.
- Once there are no pending affirmations:
  - If any mediator rejected, the settlement becomes `Rejected`.
  - Otherwise the settlement becomes `Executed`.

Then the settlement remains `Executed`/`Rejected` until all legs are fully `Finalized`, at which point the settlement becomes `Finalized`.

## Canonical settlement flows

The flows below describe the “intended” lifecycle. The tests provide runnable examples.

### Flow A: Normal settlement (no mediator)

Example: issuer transfers an asset to an investor, with no mediator and optionally an auditor watching.

1. Create settlement (`Pending`)
   - Creator builds settlement via `SettlementBuilder` + `LegBuilder` and calls `encrypt_and_prove(...)`.
   - Creator submits the settlement creation proof on-chain.

2. Sender affirmation
   - Sender decrypts the leg (to learn amount + asset-id) and generates a sender affirmation proof.
   - On-chain: sender’s nullifier is revealed; a new account state commitment is appended.

3. Receiver affirmation
   - Receiver decrypts the leg and generates a receiver affirmation proof.
   - On-chain: receiver’s nullifier is revealed; a new account state commitment is appended.

4. Transition to `Executed`
   - Once both sender and receiver are affirmed for the leg, the settlement is considered executed.

5. Finalization (executed-phase)
   - **Receiver claim**: receiver submits a claim proof; this updates receiver state to include the received amount and decrements the counter.
   - **Sender counter update**: sender submits a counter-update proof; this decrements sender counter to finalize the sender’s leg.

6. Settlement becomes `Finalized`
   - Once each leg’s required finalization operations are done.

Notes:
- If configured, auditors can decrypt the leg details for observability/audit.
- The chain does not learn plaintext leg details as part of settlement verification.

### Flow B: Normal settlement with mediator (accept path)

If a leg has mediators, they are additional required affirmers.

1. Create settlement (`Pending`)
2. Sender affirmation
3. Receiver affirmation
4. Mediator affirmation (accept)
   - A mediator decrypts the leg and submits an accept proof.

Then the settlement transitions to `Executed` only after all required mediators accept.
Finalization proceeds as in Flow A.

### Flow C: Mediator rejects after sender has affirmed

This is an important “rollback” scenario and is exercised in tests.

1. Create settlement (`Pending`)
2. Sender affirmation
3. Mediator affirmation (reject)
   - The settlement becomes `Rejected`.

4. Sender reversal (cleanup)
   - Sender submits a reversal proof for the rejected leg.
   - This undoes the sender’s earlier state transition for that rejected leg.

5. Settlement becomes `Finalized`
   - Once the necessary cleanup finalizations are completed.

### Flow D: Multi-leg settlement (atomic swap)

A settlement can contain multiple legs. Conceptually, each leg follows the same lifecycle, but the settlement-level status is derived from *all legs*.

- A classic example is an atomic swap with 2 legs:
  - Leg 0: A sends asset X to B
  - Leg 1: B sends asset Y to A

A settlement transitions to `Executed` only when *all* required affirmations across *all* legs are complete and accepted.
Finalization still happens leg-by-leg (each sender must finalize their send-side leg; each receiver must finalize their receive-side leg).

### Flow E: Instant settlement

An “instant settlement” packages:

- the settlement creation proof, and
- the sender/receiver affirmation proofs (and mediator proofs, when present)

into a single submission.

Outcome:

- The settlement is executed and finalized immediately.
- Follow-on finalization actions like receiver claim or sender counter update are not applicable (and should fail if attempted).

This is useful when all parties have already agreed off-chain and are willing to provide their proofs up-front.

## What changes in account state during settlement operations

The math spec (`dart-bp/docs/5.md`) defines a unified “state transition proof” that covers multiple transaction shapes.

At the flow level:

- Sender affirmation: consumes the sender’s current account state and produces a new state consistent with “I have committed to send this leg”.
- Receiver affirmation: consumes the receiver’s current account state and produces a new state consistent with “I have committed to receive this leg”.
- Receiver claim: in the executed phase, updates receiver state to actually claim the received amount for the leg.
- Sender counter update: in the executed phase, updates sender state to finalize the sender-side accounting for the leg.
- Sender reversal (after rejection): in the rejected phase, updates sender state to undo the earlier sender affirmation for the rejected leg.

The *chain* only sees:

- nullifiers (to prevent double-spends / reuse of old states),
- new account state commitments,
- proofs that these updates are consistent.

## Shared account-state proof model (important for AI reviewers)

Most non-setup account transitions in DART reuse the same shared proving/verification spine:

- `dart-bp/src/account/common.rs` implements the reusable account-state transition machinery.
- `dart-bp/src/account/state_transition.rs` assembles that machinery into concrete sender/receiver/finalization/reversal flows.

This shared layer is easy to misread if you look only at one high-level proof type.

### The shared proof is split into two layers

For settlement-related account updates, the proof is usually not “one monolithic object”.

- `CommonStateChangeProof` covers the parts that change on **every** account-state transition:
  - knowledge of the old account leaf / rerandomized leaf,
  - correctness of the new account commitment,
  - nullifier correctness,
  - per-leg linkage between the account and each encrypted leg,
  - the `rho`, `current_rho`, and randomness progression relations.
- `BalanceChangeProof` is a separate, optional component that exists **only if at least one leg changes balance**.

Practical implication:

- Some flows are “counter-only” and use only `CommonStateChangeProof`.
- Other flows are “balance + counter” and require **both** proof objects to stay in sync.

### `LegVerifierConfig` uses tri-state flags

The verifier-side leg config is intentionally richer than a simple boolean:

- `has_balance_decreased: Option<bool>`
- `has_counter_decreased: Option<bool>`

Interpretation:

- `None` means that dimension does **not** change for that leg.
- `Some(true)` means the dimension decreases.
- `Some(false)` means the dimension increases.

This is important because the shared verifier is reused across sender affirmations, receiver affirmations, claims, reversals, and counter-only finalization steps.

### Asset-id mode is global across the shared state-change proof

One subtle design choice in `account/common.rs` is that asset-id handling is not purely “per leg”.

- If **no** leg reveals the asset id, the shared proof stays in “asset hidden everywhere” mode.
- If **any** leg reveals the asset id, the shared proof switches into a global “asset revealed” mode.

In that mixed case:

- legs that reveal the asset id use the `AssetIdRevealed` relation,
- legs that keep it encrypted use the `AssetIdRevealedElsewhere` relation,
- all revealed legs must agree on the same asset id.

Mental model: a mixed settlement still treats the asset id as globally known inside the common state-transition proof, even if some individual legs keep their own ciphertext copy.

### Balance changes are aggregated, but per-leg amount consistency is still proven

For multi-leg transitions, the balance logic is split in a non-obvious way:

- the account proof checks a single **net** old-balance/new-balance transition,
- the balance-change sigma proofs still prove each leg amount ciphertext separately.

So a multi-leg sender/receiver proof is not “one amount proof per account delta only”.
It is:

- one aggregated account-balance transition, plus
- per-leg amount/encryption consistency checks.

This matters for review because balance conservation bugs can live either in the aggregation logic or in the per-leg linkage logic.

### Sender vs receiver flows share the same verifier core

The shared verifier does not have separate “sender code” and “receiver code” in the common layer.
Instead, it is driven by per-leg role metadata:

- `party_eph_pk.is_sender()` decides whether the verifier binds sender-side or receiver-side participant ciphertext/ephemeral values for that leg.

This is how the same state-transition engine can validate both sender-oriented and receiver-oriented flows without duplicating the low-level sigma logic.

### Order matters across all leg vectors

Several proof objects are order-coupled:

- the leg list,
- `resp_leg_link`,
- balance-change amount responses,
- ciphertext/ephemeral-key arrays passed into verifier helpers.

These arrays are not “set-like”; they are expected to match in length **and** position.
When reviewing call sites, preserve that ordering assumption across builders, proof containers, and verifier wrappers.

### The verifier is intentionally multi-phase when balance changes

At the low-level API, verification is not a single call in the balance-changing case.
The intended flow is:

1. Initialize the shared state-change verifier and enforce the common constraints.
2. If any leg changes balance, call `init_balance_change_verification...` to add the amount-specific transcript material and constraints.
3. Derive the transcript challenge.
4. Verify sigma protocols and then (optionally) the final Bulletproof tuples / batch check.

If step 2 is skipped in a balance-changing flow, the transcript/state for verification is incomplete.

### Batched proving/verification can supply the rerandomized leaf externally

The shared account-transition layer supports a batched mode where the rerandomized leaf/path work is performed outside `CommonStateChangeProver` / `StateChangeVerifier`.

- Prover side: `init_with_given_prover_with_rerandomized_leaf(...)`
- Verifier side: `init_with_given_verifier_with_rerandomized_leaf(...)`

This is how higher-level batched state transitions reuse external curve-tree work.

Important review note:

- when using these entrypoints, the caller is responsible for keeping transcript context aligned with the externally supplied rerandomized path/leaf state.

## Code landmarks (where to look)

If you’re validating this doc against the implementation, these are the most directly relevant locations:

- Settlement building + proof verification API:
  - `src/bp/leg.rs` (`SettlementBuilder`, `LegBuilder`, `LegConfig`, `SettlementProof`)

- Settlement follow-on proofs (affirm/claim/finalize/reverse):
  - `src/bp/leg/proofs.rs`

- Instant settlement proof container:
  - `src/bp/leg/instant.rs`

- Math / protocol docs:
  - `dart-bp/docs/4.md` (settlement + leg encryption)
  - `dart-bp/docs/5.md` (sender/receiver affirmations and post-settlement actions)

- Fee accounts:
   - `src/bp/fee.rs` (runtime-facing fee-account proof wrappers)
   - `dart-bp/src/fee_account.rs` (fee-account proving and verification logic)

- Account-state transition verifiers (common building blocks used across mint/affirm/claim/reverse):
   - `dart-bp/src/account/common.rs`
   - `dart-bp/src/account/state_transition.rs`
   - `dart-bp/src/account/transparent.rs`

- End-to-end flows:
  - `tests/simple_mint_and_transfer.rs`

## Quick map: action → proof type → code

This section links the settlement lifecycle actions in this doc to the concrete proof/container types you’ll see in the Rust API.

- Create settlement (encrypted legs + creation proof)
   - Proof/container: `SettlementProof`
   - Build: `SettlementBuilder::encrypt_and_prove(...)`
   - Verify: `SettlementProof::verify(...)`
   - Code: [src/bp/leg.rs](src/bp/leg.rs)

- Batched settlement submission (creation proof + optional per-leg sender/receiver affirmations)
   - Proof/container: `BatchedSettlementProof` with `BatchedSettlementLegAffirmations { sender: Option<...>, receiver: Option<...> }`
   - Code: [src/bp/leg/proofs.rs](src/bp/leg/proofs.rs)

- Sender affirmation (pre-execution phase)
   - Proof: `SenderAffirmationProof`
   - Build/verify: `SenderAffirmationProof::{new, verify}`
   - Code: [src/bp/leg/proofs.rs](src/bp/leg/proofs.rs)

- Receiver affirmation (pre-execution phase)
   - Proof: `ReceiverAffirmationProof`
   - Build/verify: `ReceiverAffirmationProof::{new, verify}`
   - Code: [src/bp/leg/proofs.rs](src/bp/leg/proofs.rs)

- Mediator accept/reject (when mediators are configured)
   - Proof: `MediatorAffirmationProof` (`accept: bool`, `key_index: MediatorId`)
   - Build/verify: `MediatorAffirmationProof::{new, verify}`
   - Code: [src/bp/leg/proofs.rs](src/bp/leg/proofs.rs)

- Receiver claim (executed-phase finalization)
   - Proof: `ReceiverClaimProof`
   - Build/verify: `ReceiverClaimProof::{new, verify}`
   - Code: [src/bp/leg/proofs.rs](src/bp/leg/proofs.rs)

- Sender counter update (executed-phase finalization)
   - Proof: `SenderCounterUpdateProof`
   - Build/verify: `SenderCounterUpdateProof::{new, verify}`
   - Code: [src/bp/leg/proofs.rs](src/bp/leg/proofs.rs)

- Sender reversal (rejected-phase cleanup)
   - Proof: `SenderReversalProof`
   - Build/verify: `SenderReversalProof::{new, verify}`
   - Code: [src/bp/leg/proofs.rs](src/bp/leg/proofs.rs)

- Instant settlement (creation proof + all affirmations packaged together)
   - Proof/container: `InstantSettlementProof` with per-leg `InstantSettlementLegAffirmations { sender, receiver, mediators }`
   - Code: [src/bp/leg/instant.rs](src/bp/leg/instant.rs)

Binding note (important for reviewers): most follow-on proofs are keyed by a `LegRef`, which is derived from `(settlement_ref, leg_id)` and used to derive a context string/hash for transcripts.

## Known gaps / things to double-check

This doc intentionally reflects what is exercised in the integration tests:

- Sender reversal is exercised for rejected settlements.
- Receiver-side “reversal” and some alternative counter/balance transition variants are described in the math spec, but may not be wired through all higher-level APIs/tests in this repo yet.

If you want this doc to be treated as the authoritative spec for *all* txn variants (including every reversal/irreversible mode), we should decide whether to:

1. expand the tests and high-level APIs to cover those variants, or
2. explicitly mark them as “spec-only / not currently implemented”.

## Operational constraints and “gotchas” observed in tests

- Some stress-style tests are bounded by internal Bulletproof transcript-label capacity in the upstream fork used here. When a proof tries to allocate too many transcript labels, proof generation can fail even if the logic is otherwise correct.
- When reading benchmark/stress tests, treat chosen sizes (number of legs, batch sizes) as “max under current constraints”, not a protocol limit.
