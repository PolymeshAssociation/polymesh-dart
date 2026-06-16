# Project: polymesh dart-bp

## Symbol Lookup — workspace first, then deps

This workspace has three members, all under the current working directory:
`dart-bp/`, `dart-common/`, `dart-testing-cli/`.

**Before assuming a symbol lives in a dependency, grep the workspace.** Most symbols
(app types, gadgets, constants, etc.) are defined in a workspace crate.
The whole tree is already greppable — no permission needed. From the workspace root:

```bash
grep -rn "SymbolName" .
```

This is one command, starts with `grep` (matches `Bash(grep *)`), and never prompts.
Do NOT scan `~/.cargo/git/checkouts/*/*/` or use `$(...)` to compute a crate path for a
symbol you haven't first confirmed is external. Only fall through to the dependency dep map
(below) when the workspace grep comes up empty.

## Rust Dependency Source Lookup

**Never spawn an agent or run `find /` to locate a dependency's source.**

### Primary strategy: build the dep map upfront

At the start of any task that will involve reading dependency source, resolve ALL relevant deps in one shot and keep the map for the entire session. Never re-derive a path you already have.

**Step 1 — Identify which crates the task will touch** (read the task description, scan imports in the relevant source files).

**Step 2 — Resolve all of them from Cargo.lock in one command:**

```bash
# Dump every git dep: name + full source line
grep -E '^name = |^source = ' Cargo.lock \
  | paste - - \
  | grep 'git+' \
  | grep -E 'schnorr_pok|dock_crypto_utils|elgamal|bulletproofs|relations|ark-dlog|ark-ec-div|ark-ff|ark-ec\b|ark-serialize|ark-poly|ark-pallas|ark-vesta|ark-wei|ark-curve25519|ark-ed25519'
```

Adjust the `grep -E` filter to the crates actually needed. Each output line gives you:
```
name = "schnorr_pok"    source = "git+https://…/crypto?branch=main#23da69b8…"
```

**Step 3 — Derive disk paths from the output (no further lookups needed):**

For each line:
- Repo slug: `ls ~/.cargo/git/checkouts/ | grep <REPO_NAME>` (one-time, stable)
- Rev prefix: first 7 chars of the SHA after `#` in the source field
- Full path: `~/.cargo/git/checkouts/<REPO-SLUG>/<REV7>/`

For path deps (no `git+` source): `grep 'CRATE' Cargo.toml` to get the `path =` value.

**Step 4 — Use the map for every subsequent symbol lookup:**

```bash
# After building the map, every lookup is just:
grep -rn "SymbolName" <RESOLVED_PATH>/crate_subdir/src/
```

No Cargo.lock re-read, no `find`, no agent, no permission prompts.

---

### Known repo slugs (stable — derived from git URL, not revision)

| Crates | Repo slug | Subdirectory layout |
|---|---|---|
| `schnorr_pok`, `dock-crypto-utils`, `elgamal` | `crypto-bb12fcac845a481a` | `schnorr_pok/src/`, `utils/src/`, `elgamal/src/` |
| `bulletproofs`, `relations`, `ark-dlog-gadget`, `ark-ec-divisors` | `curve-trees-45f5022729a17903` | `bulletproofs/src/r1cs/prover.rs`, `bulletproofs/src/r1cs/verifier/mod.rs`, `relations/src/`, `ark-dlog-gadget/src/`, `ark-ec-divisors/src/` |
| `ark-ff`, `ark-ec`, `ark-serialize`, `ark-poly`, `ark-pallas`, `ark-vesta`, `ark-wei25519`, `ark-curve25519`, `ark-ed25519`, `ark-selene`, `ark-helios`, `ark-host-msm` | `arkworks-algebra-791b8d279de8246f` (alt: `arkworks-algebra-bd4adecfb83624a4`) | `ff/src/`, `ec/src/`, `serialize/src/`, `poly/src/`, `curves/<CURVE>/src/`, `host-msm/src/` |

Slugs do not change when the revision changes. Rev comes from Cargo.lock.

---

### Fallback: single-crate lookup

If only one crate is needed:
```bash
REV=$(grep -A5 'name = "schnorr_pok"' Cargo.lock | grep -o '#[0-9a-f]*' | cut -c2-8)
grep -rn "PokDiscreteLog" ~/.cargo/git/checkouts/crypto-bb12fcac845a481a/${REV}/schnorr_pok/src/
```

---

## Permissions

All broad read/grep/find operations are pre-allowed in `.claude/settings.local.json`. You do not need to ask permission for:
- `grep`, `rg`, `find`, `cat`, `ls`, `head`, `tail` on any path
- `cargo check/build/test/nextest` (including `+nightly-2025-11-21`)
- `git log/diff/show/status/blame` in the workspace
- Reading `~/.cargo/**`

**Write one command per Bash call, starting with the actual tool. Permission matching is on the first token only — it does not cross `&&`, `;`, or `|`.** Patterns to avoid:

```bash
# BAD — cd preamble, permission match stops at 'cd':
cd <some/dir> && grep -rn "Symbol" dart-bp/src
cd <some/dir>; echo "==="; grep ...; sed ...; find ...

# BAD — shell variable preamble, match is on 'PARTIAL=' which has no allowlist entry:
PARTIAL=~/.cargo/git/checkouts/crypto-.../partial.rs
grep -n "fn is_valid" "$PARTIAL"

# BAD — for/while loop, starts with 'for':
for base in ...; do find "$base" -name "*.rs"; done

# BAD — glob scan across all checkouts (unknown path, ambiguous permission match):
grep -rn "SomeSymbol" ~/.cargo/git/checkouts/*/*/

# BAD — $(subshell) to compute path dynamically inside the same command:
grep -rn "SomeSymbol" $(grep "some-crate" Cargo.toml | sed 's/path = "//;s/"//') 2>/dev/null

# GOOD — single command, starts with the tool; workspace-relative or ~/.cargo path:
grep -rn "Symbol" dart-bp/src
grep -n "fn is_valid" ~/.cargo/git/checkouts/<REPO-SLUG>/<REV>/schnorr_pok/src/partial.rs
```

The glob scan and `$(subshell)` patterns are both symptoms of not having the dep map. If you don't know which crate defines a symbol, grep the workspace first; if it's external, look it up in the dep map (steps 1–3 above), resolve the exact path, then grep it directly.

**Prefer the `Read` tool over `sed -n '/pattern/,/}/p'`** for extracting a section of a file — it takes `offset` and `limit` line numbers and needs no shell.

**Never hardcode a revision hash** — always derive it from Cargo.lock at the start of the task. A hardcoded rev that drifts from Cargo.lock produces wrong paths silently.
