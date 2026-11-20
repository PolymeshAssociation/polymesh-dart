# dart-testing-cli

An off-chain **simulator of the Polymesh Confidential Assets pallet** for reviewing
DART proofs. It runs every DART extrinsic (account/asset registration, mint,
settlements, affirmations, claims, fees, batches, relayer payments, freeze,
encryption keys) against a SQLite-backed chain model whose storage layout, state
machine, curve-tree roots, nullifiers, limits, and error names mirror the pallet
(`Polymesh/pallets/confidential-assets/src/`), without needing a node.

Use it to:

* **validate real proof files** — apply a proof produced by a device/prover and
  see exactly which pallet check it passes or fails,
* **replay scenarios deterministically** — same `--seed`, same proofs, same trace,
* **study the settlement state machine** — per-party leg statuses, pending
  counters, finalization, pruning, tombstones,
* **exercise the relayer flow** — `atomic-but-paid` batch submission with fee
  pool accounting.

## Build

```bash
# from the polymesh-dart workspace root
cargo build --release -p dart-testing-cli
./target/release/dart-testing-cli --help
```

Everything persists in a SQLite database (default `dart_test.db`, override with
`--database`), so commands run as separate processes build on the same chain.

## The block model — read this first

The chain has **one block number** shared by all trees, exactly like
`frame_system`. A proof is verified against the curve-tree root that was
**published at the last block end**, and each party's proof updates **its own**
tree leaf. That means:

> **A proof binds the roots/leaves of the block it was generated against; end a
> block (`end-block`) before generating a proof that needs another party's
> freshly updated leaf.**

Concretely: the sender's counter update after the receiver claims binds the
receiver's claimed leaf, so `receiver-claim` must be followed by `end-block`
before `sender-counter-update` is generated. Same for mediator rejection →
revert. Sender/receiver/mediator affirmations for one leg do **not** need a
block between them: the relayer demo applies `create-settlement` + all three
affirmations in a single batch. The scenario script
(`reinit_db_and_run_testing.sh`) shows the correct placement.

`end-block` mirrors the pallet's `on_finalize`: commits appended account/fee
leaves, stores each tree's root for the block, applies
`MinCurveTreeRootUpdateInterval`, advances the block/timestamp, and prunes roots
older than `MAX_ROOT_PRUNING_BLOCKS`. The commit, clock advance and pruning are
one SQLite transaction. Root-age and pruning are enforced on proof verification
(`CurveTreeRootNotFound` on missing/expired roots).

Every extrinsic runs inside a SQLite transaction (check → verify → apply): a
failed dispatch leaves the database untouched, so negative testing is safe.

## Proof files: `-w`, `-r`, `--dry-run`

Proof subcommands share the same three options:

| Flag | Meaning |
| --- | --- |
| `-w FILE` | **generate only** — write the SCALE-encoded proof, do not touch the chain |
| `-r FILE` | **apply** a proof file produced by a compatible CLI version |
| (neither) | generate + apply in one shot |
| `--dry-run` | apply with full verification, then roll the transaction back |

`-w`/`-r` round-trips model the real world: the prover/device generates the
proof; the chain applies it. The settlement/leg a proof acts on is resolved
from the proof's own `leg_ref` — CLI `--asset/--amount` on affirmations are
assertions only, and `--settlement` on affirmations is only used to locate the
leg at generation time.

Replaying the same proof file is rejected by the pallet's own guards
(`NullifierAlreadyUsed`, `AffirmationAlreadySubmitted`,
`SettlementAlreadyExists`), not by CLI-specific logic.

`--seed <16-hex>` makes key generation and proof creation deterministic; `init`
stores the seed in the DB so later commands replay the same keys.

## Quick walkthrough

```bash
CLI="./target/release/dart-testing-cli"
SEED=0000000000000001

$CLI init --seed $SEED
$CLI create-signer -n issuer && $CLI create-signer -n investor && $CLI create-signer -n mediator
$CLI create-account -s issuer-0 --seed $SEED
$CLI create-account -s investor-0 --seed $SEED
$CLI create-account -s mediator-0 --seed $SEED
$CLI account-registration -s issuer-0 -w reg.proof --seed $SEED
$CLI account-registration -s issuer-0 -r reg.proof
$CLI end-block

# asset 0 is the fee asset; asset 1 is a normal one with a mediator
$CLI create-asset -s issuer-0 -t mediator -a mediator-0 --name fee-asset --decimals 0
$CLI create-asset -s issuer-0 -t mediator -a mediator-0 --name test_accept --decimals 6
$CLI register-account -s issuer-0 --asset 1
$CLI register-account -s investor-0 --asset 1
$CLI end-block
$CLI mint-assets -s issuer-0 -a 1 -m 1000 --seed $SEED
$CLI end-block

# settlement: create -> sender -> (block) -> receiver -> (block) -> mediator -> (block)
$CLI create-settlement -v venue -l issuer-0:investor-0:1:500 -w cs.proof
$CLI sender-affirm   -s issuer-0   -S 1 -l 0 -w sa.proof --seed $SEED
$CLI sender-affirm   -s issuer-0   -S 1 -l 0 -r sa.proof
$CLI end-block
$CLI receiver-affirm -s investor-0 -S 1 -l 0 -w ra.proof --seed $SEED
$CLI receiver-affirm -s investor-0 -S 1 -l 0 -r ra.proof
$CLI end-block
$CLI mediator-affirm -s mediator-0 -S 1 -l 0 --accept -w ma.proof --seed $SEED
$CLI mediator-affirm -s mediator-0 -S 1 -l 0 --accept -r ma.proof
$CLI end-block
$CLI get-settlement -S 1        # -> Executed
```

`create-settlement -w` assigns the numeric settlement id at generation time
(and seeds the leg rows + mediator snapshot), so parties can build proofs with
`-S <id> -l <idx>` **before** the settlement exists on-chain — exactly what a
batch/relayer submission needs.

`--settlement-id` is a CLI alias for the content-addressed `SettlementRef`
(hash of the settlement proof); status commands accept it via `-S`.

## Command reference

### Chain plumbing

| Command | Pallet call | Notes |
| --- | --- | --- |
| `init` | — | reset storage, store `--seed`, store genesis roots (heights from `--config`) |
| `end-block` | `on_finalize`/`on_initialize` | commit leaves, store roots, min-update, advance clock, prune roots |
| `show-storage` | — | block/moment, tree heights & leaf counters, root list, fee pool, assets (+frozen), identities, settlements |
| `trace` | — | replay the dispatch/event log (also appended to `trace.jsonl` in the run dir) |

### Identities & accounts

| Command | Pallet call |
| --- | --- |
| `create-signer` | (identity setup, off-pallet) |
| `create-account` | (device-side key derivation, off-pallet) |
| `account-registration` | `register_accounts` |
| `register-account` | `register_account_assets` |
| `list-signers`, `list-accounts` | — |

### Assets

| Command | Pallet call | Notes |
| --- | --- | --- |
| `create-asset` | `create_asset` | metadata bounds (`InvalidAssetName`/`NameTooLong`/`SymbolTooLong`/`TooManyDecimals`), `NoAuditorsOrMediators`, key-registration gates |
| `mint-assets` | `mint_asset` | owner + supply checks (`NotAssetOwner`, `MaxTotalSupplyExceeded`) run as preflights before proof generation |
| `update-asset-keys` | `update_asset_keys` | issuer only; mediators/auditors must stay registered |
| `set-asset-frozen` | `set_asset_frozen` | `--freeze/--unfreeze`, issuer origin `-s` vs `--root`; a root freeze can only be lifted by root (`AssetFrozenByRoot`); recomputes the asset leaf with the freeze bit |
| `list-assets` | — | |

### Settlements

| Command | Pallet call |
| --- | --- |
| `create-settlement` | `create_settlement` (legs `sender:receiver:asset:amount`, options below) |
| `sender-affirm` | `sender_affirmation` |
| `receiver-affirm` | `receiver_affirmation` |
| `mediator-affirm` | `mediator_affirmation` (`--accept/--reject`, `--key-index` for multi-mediator legs) |
| `sender-counter-update` | `sender_update_counter` |
| `sender-revert-affirmation` | `sender_revert_affirmation` |
| `receiver-revert-affirmation` | `receiver_revert_affirmation` |
| `receiver-claim` | `receiver_claim` |
| `instant-sender-affirmation` | `instant_sender_affirmation` |
| `instant-receiver-affirmation` | `instant_receiver_affirmation` |
| `get-settlement`, `show-legs` | — |

The settlement state machine mirrors the pallet exactly:
`SettlementPendingAffirmations` / `SettlementPendingFinalizations` counters,
per-party `LegAffirmParty` statuses (`Sender`/`Receiver`/`Mediator(i)`),
`check_for_execution` / `check_for_finalization` / `reject` semantics (a
mediator rejection finalizes immediately when no finalization is pending),
and `finalize_settlement` as a tombstone that prunes legs and blocks replays.

Leg builder options (`create-settlement`):

| Flag | Meaning |
| --- | --- |
| `--hidden-asset-id` | legs carry an asset membership proof instead of a revealed id |
| `--visibility full\|none\|sender-sees-receiver\|receiver-sees-sender` | `PartyVisibility` |
| `--public-enc-key signer-account` | extra encryption keys that can decrypt the leg |

### Fees & relayer

| Command | Pallet call | Notes |
| --- | --- | --- |
| `register-fee-accounts` | `register_fee_accounts` | `-f signer-account:amount` (batch), deposits into the fee pool, appends fee-tree leaves |
| `topup-fee-accounts` | `topup_fee_accounts` | batch topups with nullifier rotation, verified against the fee root |
| `list-fee-accounts` | — | fee pool balance + registered fee accounts |
| `relayer-fee-preview` | — | prints the nullifier the relayer's *next* payment of `-m` will burn |
| `relayer-batched-proofs` | `relayer_batched_proofs` | see below |
| `submit-batched-proofs` | `submit_batched_proofs` | assemble from proof files (`-p type=path`), `-w` write, `-r` apply; one atomic transaction |

**Relayer flow (atomic-but-paid).** Party proofs that should be paid by a
relayer batch are generated with `--relayer-fee-nullifier <hex>` (from
`relayer-fee-preview`), binding them to the spent fee state via
`verify_with_context`. This applies to `create-settlement`,
`sender-/receiver-/mediator-affirm`, counter updates, reverts and claims —
every proof in a batch must bind the same context. The relayer then assembles a
`FeePaymentWithBatchedProofs` (payment bound to the batch hash + relayer DID,
or `--broadcast` for open submission) and applies it: the **fee payment runs in
its own committed transaction** (nullifier burn, fee leaf append, pool
withdrawal) and the **batch runs atomically afterwards** — if any proof in the
batch fails, the batch is fully rolled back, but the relayer keeps the fee and
the host fee state still advances (so a retry uses a fresh nullifier). A failed
batch is recorded in the trace as `RelayerBatchedProofs ... batch_result=...`.
The pallet returns `Ok` for a paid-but-failed batch; the CLI deliberately exits
non-zero so scripts and `--expect-error` can assert on the batch failure.
`--dry-run` verifies the fee payment *and* the batch, then rolls both back.

### Encryption keys & roles

| Command | Pallet call | Notes |
| --- | --- | --- |
| `register-encryption-keys` | `register_encryption_keys` | generates `-n` fresh keys into the host keystore, registers them; prints key ids |
| `distribute-encryption-key` | `distribute_encryption_key` | `-k <host key id>` (must be unregistered) or omit for a fresh inline key, `-R signer-account` recipients; records `SharedKeyRecipients` |

Distributed keys enable the **shared-key mediator** path: an asset mediator
entry `(mediator-account, auditor-shared-enc-key)` validates through
`SharedKeyRecipients`; an unshared key fails with `EncryptionKeyNotShared`.
Role gates (`RequiredClaims`/`MissingRequiredClaim` for AssetCreator/Auditor/
Mediator) are wired: with no claims configured the gates are open (like a
genesis with default claims); `show-storage` reports the claim count.

## Determinism, trace & assertions

* `--seed <16-hex>` — deterministic keys and proofs (mixed with per-run chain
  progress so repeated commands draw distinct material). `init` **stores** the seed
  (normalized to 16 hex digits; a random one if `--seed` is omitted), and every later
  command defaults to the stored seed unless `--seed` is passed. A full run replays
  byte-for-byte by initializing with the same seed and replaying the same command
  sequence; the demo script does this with `init --seed "$SEED"`.
* `--run-dir DIR` — roots (`block_<n>_current_<tree>_root.bin`) and `trace.jsonl` go
  here.
* `--expect-error <Name>` — assert the dispatch fails with that pallet error
  name (e.g. `--expect-error NotLastPendingAffirmation`); the CLI exits
  non-zero if the chain accepted, or if the error name differs.
* `trace` — dispatch numbers, blocks, pallet events, and failure names.

## Corpus: record & replay (CI / upgrade testing)

Record every applied transaction once, then replay it against a fresh chain to detect
proof/state breaking changes:

```bash
CLI="./target/release/dart-testing-cli"
# One --record path for the whole run, starting with init. `init` starts a new session and
# refuses an existing corpus, so sessions never mix.
$CLI init --seed 0000000000000001 --record runs/run1/corpus.jsonl
$CLI create-signer -n issuer --record runs/run1/corpus.jsonl
# ... every command of the run ...
# Replay: derives its own scratch DB from the corpus; --database is not touched.
$CLI --run-dir /tmp/replay-run replay runs/run1/corpus.jsonl
```

`--record FILE` appends one JSONL record per applied transaction: the proof bytes, the
apply-side origin/flags, and the outcome (`Ok` or the pallet error name). Generation-only
(`-w`) and `--dry-run` commands are not recorded; failed proof attempts **are** recorded
with their error, so negative tests replay too.

The recording session has its own files, separate from the main `--database`:

| File | Purpose |
| --- | --- |
| `<corpus>` | JSONL: header (seed, config, tool version) + one record per applied transaction |
| `<corpus>.db` | chain snapshot after each recorded command (`VACUUM INTO`), for upgrade tests |
| `<corpus>.replay.db` | scratch DB used by `replay` (override with `--replay-db`) |

`replay` initializes the scratch DB from the corpus header (seed/config) and re-applies
every proof with the current verifier, comparing each outcome. It prints the sequence
number, operation, expected and actual error for mismatches, and exits non-zero if any
occur; `--continue-on-error` reports all of them instead of stopping at the first. The main
`--database` is never opened or reset by `replay`, so it can be reset independently.

Use it in CI like the serialization tests: check in a corpus produced by a known-good
release and replay it on every change. A mismatch means a proof, root, state transition or
proof-file format changed.

For an upgrade: record a session with release A, then open the session snapshot
(`<corpus>.db`) with release B or replay the corpus with B. The DB carries a
`schema_version` and `Store::migrate` is the hook for schema migrations (add a step and
bump `storage::SCHEMA_VERSION` when the schema changes). Old proofs the new release
rejects, and new proofs it accepts, appear in the replay report. End the recording run with
`end-block` so the snapshot has committed roots; you can then generate new proofs against
the recorded accounts/assets (the demo does this implicitly by ending the block after the
relayer batch).

The corpus stores the recorded account public keys, so replay does not re-derive clients
from the seed. Prover-side generation is not part of the chain replay; generate new proofs
against the replayed chain to exercise the new prover/verifier together.

## Configuration presets (`--config`)

| Preset | Tree heights (asset/account/fee) | Root-age windows |
| --- | --- | --- |
| `testing` (default) | 4/5/5 (pallet `testing` heights) | long, production-like windows |
| `production` | 1/1/1 (mainnet heights) | long, production-like windows |
| `ci-runtime` | 4/5/5 | short windows (18 s update interval, 60/120 s max root ages) so root-age/pruning run out in a few dozen blocks |

Limits come from `PolymeshLimits`: max legs (16), memo length (256),
batch sizes, key counts, mediators/auditors per asset, total supply, balances
(48-bit proof range). Individual heights override via
`--asset-tree-height/--account-tree-height/--fee-account-tree-height`.

## Errors & parity

`src/errors.rs` carries the full pallet error enum (`PALLET_ERROR_NAMES`, 57
variants) and `ChainError::name()` maps every CLI failure back to its pallet
name. Proof-internal failures map to `CurveTreeError`/`InvalidProof` exactly as
the pallet does (`From<DartError>`), while the pallet's own root lookups produce
`CurveTreeRootNotFound`. The `pallet_error_parity_table` test keeps the mapping
complete.

## Running the tests & scenario script

```bash
# in-process scenario suite (12 tests: flows, negatives, fees, batches, freeze,
# keys, hidden legs, relayer, corpus replay, error parity, seed replay, stale roots)
cargo test -p dart-testing-cli --release

# scripted demo on the built binary (same flow the README shows, incl. relayer)
cd dart-testing-cli && ./reinit_db_and_run_testing.sh
```

## Module map

| File | Mirrors |
| --- | --- |
| `src/storage.rs` | pallet storage maps + SQLite schema (identities, accounts, assets, legs, statuses, counters, tombstones, fee pool, nullifiers, claims, keystore) |
| `src/curve_tree.rs` | `curve_tree.rs` backends (`*CurveTreeStorage`): one chain block, roots per `(tree, block)`, batched inserts, root age, heights |
| `src/settlement.rs` | `settlement.rs` (`UpdateSettlementStatus`, counters, per-party transitions, finalize/prune) |
| `src/lib.rs` | pallet `lib.rs` extrinsics & `base_*`/`apply_*` bodies (shared by standalone and batch paths) |
| `src/config.rs` | runtime `Config` constants + limits (`PolymeshLimits`) |
| `src/errors.rs` | `pallet::Error` enum + `From<DartError>` mapping + parity table |
| `src/trace.rs` | dispatch/event log (`trace.jsonl`) |
| `src/corpus.rs` | transaction recording/replay (`--record`, `replay`): JSONL corpus, session DB snapshot, outcome checks |
| `src/main.rs` | clap CLI surface |

## Known caveats

* Fee amounts on a relayer batch are flat payouts from the pool per submission
  (legs carry no per-party fee splits — dart v1 `LegBuilder` has no fee field).
* `submit_batched_proofs` promotes prover states by recorded nullifier
  (`proof_state_index`); proofs generated for abandoned flows can leave a
  pending state that a later batch consumes — regenerate after abandoning.
* `ExecuteInstantSettlement` batch proofs are not generated by this CLI
  (`apply_batched_proof` rejects them explicitly).
* The CLI is a **single-host keystore model**: it holds every party's device
  keys locally so it can generate any party's proof; proof binding (not trust)
  enforces who may act.
* `GAPS.md` (gap analysis driving this implementation) is kept untracked by
  design.
