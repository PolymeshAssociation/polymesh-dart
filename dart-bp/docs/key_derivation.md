# Key and Randomness Derivation from a Master Seed

$\mathrm{AK} = \mathrm{sk} \cdot G_{\mathrm{Aff}}, \quad \mathrm{EK} = \mathrm{ek} \cdot G_{\mathrm{Enc}}$

$\mathrm{seed}$ is the master seed, an octet string of at least 32 bytes. $p$ is the order of $\mathbb{G}_p$, so all derived values are in $\mathbb{Z}_p$ and $\lceil \log_2 p \rceil = 255$ for Pallas. $\|$ is concatenation, $\mathrm{LE}_{16}(x)$ and $\mathrm{LE}_{32}(x)$ are the 2 and 4-byte little-endian encodings of $x$, and $|x|$ is the byte length of $x$.

**Code:** [`dart-bp/src/auth_proofs/keys.rs`](../src/auth_proofs/keys.rs) (`hkdf_to_field`, `ietf_keygen`, `MasterSeed`)

## KeyGen

**Spec:** [draft-irtf-cfrg-bls-signature-05, Section 2.3](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-05#section-2.3), with HKDF from [RFC 5869](https://datatracker.ietf.org/doc/html/rfc5869)

$\mathrm{KeyGen}(\mathrm{salt}, \mathrm{IKM}, \mathrm{key\_info})$ is the draft's KeyGen with $H = \mathrm{SHA\text{-}256}$ and $r = p$. $L = \lceil 3 \cdot \lceil \log_2 p \rceil / 16 \rceil = 48$.

1. Reject if $|\mathrm{IKM}| < 32$
2. $\mathrm{PRK} = \mathrm{HKDF\text{-}Extract}(\mathrm{salt}, \mathrm{IKM} \| \mathrm{I2OSP}(0, 1))$
3. $\mathrm{OKM} = \mathrm{HKDF\text{-}Expand}(\mathrm{PRK}, \mathrm{key\_info} \| \mathrm{I2OSP}(L, 2), L)$
4. $x = \mathrm{OS2IP}(\mathrm{OKM}) \bmod p$
5. If $x = 0$, set $\mathrm{salt} = H(\mathrm{salt})$ and go to step 2, else return $x$

$N$ values from one input are KeyGen with the index appended to $\mathrm{key\_info}$, under a domain separation tag $\mathrm{dst}$ used as the salt:

$$
\mathrm{Derive}_N(\mathrm{dst}, \mathrm{IKM}, \mathrm{info}) = [\mathrm{KeyGen}(\mathrm{dst}, \mathrm{IKM}, \mathrm{info} \| \mathrm{I2OSP}(0, 1)), \dots, \mathrm{KeyGen}(\mathrm{dst}, \mathrm{IKM}, \mathrm{info} \| \mathrm{I2OSP}(N-1, 1))]
$$

The index is one byte so $N \le 256$. Only $N = 1$ and $N = 2$ are used.

With $\mathrm{salt} = H(\texttt{"BLS-SIG-KEYGEN-SALT-"})$ and $p$ replaced by the BLS12-381 scalar field order, KeyGen is [EIP-2333](https://eips.ethereum.org/EIPS/eip-2333) `derive_master_SK`. With a caller-chosen salt it is [blst](https://github.com/supranational/blst) `SecretKey::key_gen_v5`. Tests `keygen_matches_eip2333_master_sk` and `keygen_matches_blst_key_gen_v5` check both.

## Domain separation tags

| Tag | Value | Outputs |
|---|---|---|
| $\mathrm{DST_{sig}}$ | `POLYMESH-DART-V1-SIG-KEY` | $\mathrm{sk}$ |
| $\mathrm{DST_{enc}}$ | `POLYMESH-DART-V1-ENC-KEY` | $\mathrm{ek}$ |
| $\mathrm{DST_{acc}}$ | `POLYMESH-DART-V1-ACCOUNT-RANDOMNESS` | $(s, \mathrm{rho\_randomness})$ |
| $\mathrm{DST_{fee}}$ | `POLYMESH-DART-V1-FEE-ACCOUNT-RANDOMNESS` | $(\rho_0, s_0)$ |

## Account keys

$\mathrm{path}$ is an opaque byte string naming the account and $\mathrm{ctr_s}$ is the secret key counter (`SkGenCounter`).

$$
\mathrm{info_{key}} = \mathrm{LE}_{32}(|\mathrm{path}|) \| \mathrm{path} \| \mathrm{LE}_{16}(\mathrm{ctr_s})
$$

$$
\mathrm{sk} = \mathrm{Derive}_1(\mathrm{DST_{sig}}, \mathrm{seed}, \mathrm{info_{key}})[0], \quad \mathrm{ek} = \mathrm{Derive}_1(\mathrm{DST_{enc}}, \mathrm{seed}, \mathrm{info_{key}})[0]
$$

The asset-id is not in $\mathrm{info_{key}}$, so accounts of different assets at the same $\mathrm{path}$ share $\mathrm{sk}, \mathrm{ek}$.

## Account randomness

$\mathrm{at}$ is the asset-id and $\mathrm{ctr}$ is the nullifier counter (`NullifierSkGenCounter`) of account registration.

$$
\mathrm{info_{rand}} = \mathrm{LE}_{32}(|\mathrm{path}|) \| \mathrm{path} \| \mathrm{LE}_{16}(\mathrm{ctr_s}) \| \mathrm{LE}_{32}(\mathrm{at}) \| \mathrm{LE}_{16}(\mathrm{ctr})
$$

For a regular account

$$
(s, \mathrm{rho\_randomness}) = \mathrm{Derive}_2(\mathrm{DST_{acc}}, \mathrm{seed}, \mathrm{info_{rand}})
$$

Here $s$ is the commitment randomness of $\mathrm{State}_0$ and $\mathrm{rho\_randomness}$ gives $\rho = \mathrm{Poseidon2}(\mathrm{rho\_randomness}, \mathrm{at} \| \mathrm{ctr})$.

For a fee account

$$
(\rho_0, s_0) = \mathrm{Derive}_2(\mathrm{DST_{fee}}, \mathrm{seed}, \mathrm{info_{rand}})
$$

Note that the first output is $\rho_0$ here and $s$ for a regular account.

## Seed sources

Ledger: $\mathrm{seed}$ is the key of the [SLIP-21](https://github.com/satoshilabs/slips/blob/master/slip-0021.md) node with label `POLYMESH-DART-V1` under the device's BIP-39 seed, derived with `HDW_SLIP21` and registered as `path_slip21` in the app's `Cargo.toml`. $\mathrm{path}$ is the byte string the host sends with each request and $\mathrm{ctr_s} = 0$.

Enclave: $\mathrm{seed}$ is 32 random bytes generated on first start and sealed. $\mathrm{path}$ is empty and $\mathrm{ctr_s} = 0$.

Host: `MasterSeed::from_seed` takes a `0x`-prefixed hex string as bytes, else the string's raw bytes. It is not a BIP-39 mnemonic. `derive_account_keys(path)` uses $\mathrm{ctr_s} = 0$, so the same $\mathrm{seed}$ and $\mathrm{path}$ give the same $\mathrm{sk}, \mathrm{ek}$ as the device.

$\mathrm{path}$ is not a BIP-32 path. Two byte strings that name the same BIP-32 path, eg `m/0` and `m/0/`, give unrelated keys. A wallet that wants to find an account again has to send the same bytes, so it should fix one canonical encoding.

## Randomness from the account secret key

The host also derives account randomness without a seed, from $\mathrm{sk}$ (`AccountKeyPair::derive_account_randomness` and `derive_fee_account_randomness` in [`src/bp/keys.rs`](../../src/bp/keys.rs)). $\mathrm{id}$ is the identity and $\mathrm{sk\_bytes}$ is the 32-byte little-endian encoding of $\mathrm{sk}$.

$$
\mathrm{info_{id}} = \mathrm{LE}_{32}(|\mathrm{id}|) \| \mathrm{id} \| \mathrm{LE}_{32}(\mathrm{at}) \| \mathrm{LE}_{16}(\mathrm{ctr})
$$

$$
(s, \mathrm{rho\_randomness}) = \mathrm{Derive}_2(\mathrm{DST_{acc}}, \mathrm{sk\_bytes}, \mathrm{info_{id}}), \quad (\rho_0, s_0) = \mathrm{Derive}_2(\mathrm{DST_{fee}}, \mathrm{sk\_bytes}, \mathrm{info_{id}})
$$

This gives different values than the seed derivation for the same account. An account opened with it is recoverable from $\mathrm{sk}$ and $\mathrm{id}$, and one opened by the device is recoverable from $\mathrm{seed}$ and $\mathrm{path}$, so whoever opens the account has to record which derivation it used. Making the device derive from $\mathrm{sk}$ as well would make the two agree, at the cost of changing every device-derived value.

## Test vectors

$\mathrm{seed} = \texttt{0x07}$ repeated 32 times, $\mathrm{path}$ empty, $\mathrm{ctr_s} = 0$, $\mathrm{at} = 5$, $\mathrm{ctr} = 3$. Values are the 32-byte little-endian encodings. Tests `from_master_seed_known_answer` and `derive_account_randomness_known_answer` in [`src/bp/auth_proofs.rs`](../../src/bp/auth_proofs.rs) pin them.

| Value | Hex |
|---|---|
| $\mathrm{sk}$ | `8366b68f9fa4a121d8de67c3e4be71373849d1002dbe21957a77c3e0ee449302` |
| $\mathrm{ek}$ | `9900e1bb51bd267c6dfc28b077be5face539354d74bb26b3bed6aea36afaec29` |
| $s$ | `5b4f1a1081044299a78562ab3b8b4e9a6669f2e3c765557e1d3573993164a514` |
| $\mathrm{rho\_randomness}$ | `b5e8eaf4f978da5735977141343622d80a0f7a9227a73087c942dcd00c923739` |
| $\rho_0$ | `d2c669287607e8ca90edb19c5e0a6296c9935db919ce871324ae892a6bc7b837` |
| $s_0$ | `08171ba37958458c19b91865096cbeb3a3d8373a6905f2e1d65aedab818c3a3f` |
