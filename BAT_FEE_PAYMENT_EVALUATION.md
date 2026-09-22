# BAT for DART fee payment: measured costs

Measurements of [Cryptocurrency-Backed Trustless Anonymous Tokens and Their
Applications](https://eprint.iacr.org/2026/1074) (BAT) Protocol A against the fee mechanism in
[`dart-bp/docs/6.md`](dart-bp/docs/6.md), from the implementation in
[`tests/bat_poc.rs`](tests/bat_poc.rs). Four combinations throughout: BLS12-381 and BN254 for the
tokens, crossed with Ed25519 and Pallas for the client signature scheme `DS`.

## Cost against the current mechanism

The current fee payment is a curve-tree membership proof plus a Bulletproofs range proof plus
linked sigmas. Numbers from `perf_comparison_results_1.md`, BAT numbers from the paper's Table 1
on BLS12-381 with Ed25519 client keys. *Measured costs* below replaces these with numbers from an
independent implementation and is what the decision should rest on.

This table is per token, which is the comparison the paper invites and it is misleading for a fee
mechanism. *Against the current mechanism, at one denomination* below carries it out to the payment
amounts where it stops holding.

| | `6.md` fee payment | BAT spend |
|---|---|---|
| Prove | 53 ms | 0.24 ms |
| Verify | 5.7 ms | 1.68 ms |
| Proof size | kilobytes | 144 B |
| Verifier work | curve tree + BP + sigma | 2 pairings + 1 DS verify |

The fee curve tree, the top-up proof, `MAX_FEE_BALANCE` range checks and the whole W2/W3 split
prover path for fees all disappear. The device holds nothing, since tokens are bearer objects on
the host.

Batched spends fold into one multi-pairing. For $n$ tokens across $J$ issuers with $\beta_i$ from
a hash of the fixed batch, the chain checks

$$
e(\sum_i{\alpha_i*\beta_i}, h) == \sum_{j \in J}{e(\sum_{i \in S_j}{H(pk_{e,i})*\beta_i}, pk_{iss,j})}
$$

which is $1 + |J|$ pairings for the whole block. Hash-to-curve and nullifier distinctness stay
per token. Within one extrinsic this is free. Across extrinsics it needs the fee check lifted out
of per-extrinsic validation, which is pallet work.

## Measured costs

Protocol A implemented and measured in [`tests/bat_poc.rs`](tests/bat_poc.rs), on both pairing
curves crossed with both client signature groups: BLS12-381 and BN254 for the tokens, Ed25519 and
Pallas for `DS`. The paper's Table 1 is Protocol A on BLS12-381 with Ed25519 and Table 2 is
Protocol B on BN254, so neither prices either axis on its own. Single-threaded, arkworks, native, no
precompiles. Storage is excluded throughout: nullifier writes are a trie cost that follows from
nothing measured here and will not be small. Every table in this section comes from one run so the
columns are comparable to each other. The `6.md` baseline is re-measured in the same run and drifts
several percent between runs, so the third digit of any ratio should not be quoted.

The two axes are independent and it shows. The pairing curve sets everything on the token side and
BN254 is roughly 2x to 4x cheaper than BLS12-381 throughout. The `DS` group sets only $\gamma$, and
in this implementation Pallas is about 2x Ed25519 on every `DS` operation, which moves the totals by
a few percent except where `DS` is the whole cost. Where a quantity depends on only one axis the
table says so rather than repeating four near-identical copies.

Serialized sizes come out on the paper's numbers to the byte and are the same for both `DS` groups,
since Pallas and Ed25519 both have 32-byte compressed points and 32-byte scalars. Token 144 B on
BLS12-381, issuance request 512 / 2,432 / 4,832 B and response 608 / 2,528 / 4,928 B at
$\ell = 10 / 50 / 100$. BN254 gives a 128 B token and 3,232 B at $\ell = 100$.

Every pairing check routes through `RandomizedPairingChecker` and every group-equation check through
`RandomizedMultChecker`, both from `dock_crypto_utils`, taken by reference so a caller settling a
whole block pays one final exponentiation and one MSM.

**Nothing in the PoC aggregates a pairing equation by hand.** The checker groups the pairs it
accumulates by their $G_2$ element, so a batch whose $G_2$ side takes $k$ distinct values settles as
$k$ $G_1$ MSMs against a $k$-pair multi-miller-loop and one final exponentiation. Masked verification
has $k = 2$, $h$ and $com_k$. Spend over $J$ issuer keys has $k = 1 + J$, $h$ and the keys. Refund is
spend at $J = 1$. The equations the checker ends up evaluating are exactly the ones an explicit
aggregation would build, so the caller hands over one equation at a time and the collapse happens
underneath.

That only holds on the `G2Affine` overloads, `add_sources_g2_affine` and
`add_multiple_sources_g2_affine`, which key the group by x coordinate and prepare each distinct point
once at the end. The plain `add_sources` takes `impl Into<G2Prepared>`, so it accepts an affine point
silently and prepares it on every call, then keys the group by serializing the prepared form. Three
paths for masked verification at $\ell = 100$ on BLS12-381 were measured while deciding this, and the
two losing ones deleted:

| | ms |
|---|---|
| per equation, `add_sources` (200 $G_2$ preparations) | 18.9 |
| hand-aggregated, two $G_1$ MSMs handed over as one equation | 5.0 |
| per equation, `add_sources_g2_affine` | 2.9 |

Hand-aggregating loses because it pays an `into_affine` per group and builds a `powers` vector that
the checker then re-randomizes, on top of the same MSMs the checker would have done. Spend behaves
the same way, 68.5 ms against 61.0 at $n = 512, J = 1$. A direct pairing path bypassing the checker
went the same way earlier: at $n = 1$ the checker cost 0.800 ms against 0.798 for a direct
multi-pairing. So the pairing side carries no variants at all, and the only ones left anywhere are
`FixedBase` and `Rmc` for the issuer reveal. Batch normalization on the issuer's $\ell$ scalar mults
and Montgomery batch inversion on unmasking are likewise unconditional; each saved about 3 percent at
$\ell = 100$ while they were still selectable.

Primitives, for reading the rest. The token side depends only on the pairing curve and the `DS` side
only on the signature group, so each is listed once:

| | BLS12-381 | BN254 |
|---|---|---|
| $G_1$ scalar mult | 0.088 ms | 0.042 ms |
| $G_2$ scalar mult | 0.245 ms | 0.110 ms |
| $G_1$ MSM, 100 | 1.78 ms | 0.94 ms |
| pairing | 0.55 ms | 0.30 ms |
| multi-pairing, 2 pairs | 0.69 ms | 0.39 ms |
| final exponentiation | 0.53 ms | 0.29 ms |
| hash to $G_1$ | 0.075 ms (WB/SWU) | 0.0060 ms (try-and-increment) |

| | Ed25519 | Pallas |
|---|---|---|
| `DS` keygen | 0.056 ms | 0.030 ms |
| `DS` sign | 0.056 ms | 0.029 ms |
| `DS` verify | 0.092 ms | 0.044 ms |

The hash-to-curve row needs reading carefully, because the two pairing curves are not running the
same construction. Each uses the best arkworks offers: BLS12-381 gets the RFC 9380 WB map, BN254 gets
hash-to-field plus try-and-increment on $x$. BN254 has no standard map available and this is not an
oversight of the fork. Its $G_1$ is $y^2 = x^3 + 3$ with $COEFF_A = 0$, arkworks' `SWUConfig` requires
$COEFF_A \neq 0$, no WB isogeny is shipped for it, and arkworks 0.5 has no SVDW at all. A BN254
deployment needs a constant-time map written before it ships, since try-and-increment is variable
time in the number of increments.

The 12x gap between the curves is nonetheless real and is not an artifact of that substitution. It is
cofactor clearing: BLS12-381's $G_1$ has cofactor about $2^{126}$ and BN254's is 1. Measuring
BLS12-381 both ways, before the fallback was removed as a selectable option, gave 0.079 for
try-and-increment against 0.078 for WB, indistinguishable, because both pay the cofactor and that
dominates the map. So writing SVDW for BN254 will not move its number much, and BLS12-381 cannot
close the gap by changing construction. Now that the pairings are grouped away this is the dominant
per-token cost on BLS12-381, and it is the term that does not batch: at $n = 512, J = 1$ it is
49.8 ms of a 58.0 ms pairing check.

### Issuance, off chain

The client's check $\forall i : e(\tilde\sigma_i, h) == e(X_i, com_k)$ has the same $h$ and $com_k$
in every one of the $\ell$ equations, so the checker holds two groups and settles it as two $G_1$
MSMs of size $\ell$ and a two-pair multi-miller-loop.

BLS12-381 with Ed25519, milliseconds:

| $\ell$ | client blind | issuer sign | client verify | client unmask | verify, per token |
|---|---|---|---|---|---|
| 1 | 0.534 | 0.386 | 0.863 | 0.087 | 0.863 |
| 5 | 1.41 | 0.796 | 1.172 | 0.466 | 0.235 |
| 10 | 2.50 | 1.31 | 1.292 | 0.897 | 0.129 |
| 20 | 4.70 | 2.35 | 1.527 | 1.95 | 0.076 |
| 30 | 6.80 | 3.39 | 1.735 | 2.95 | 0.058 |
| 40 | 8.88 | 4.34 | 2.028 | 3.98 | 0.051 |
| 50 | 11.0 | 5.41 | 2.160 | 4.97 | 0.043 |
| 100 | 21.5 | 10.6 | 2.823 | 10.1 | 0.028 |
| 200 | 42.3 | 20.4 | 4.154 | 20.1 | 0.021 |

BLS12-381 with Pallas:

| $\ell$ | client blind | issuer sign | client verify | client unmask | verify, per token |
|---|---|---|---|---|---|
| 1 | 0.538 | 0.417 | 0.864 | 0.093 | 0.864 |
| 5 | 1.41 | 0.799 | 1.171 | 0.438 | 0.234 |
| 10 | 2.50 | 1.29 | 1.294 | 0.925 | 0.129 |
| 20 | 4.68 | 2.38 | 1.521 | 1.89 | 0.076 |
| 30 | 6.84 | 3.38 | 1.739 | 2.94 | 0.058 |
| 40 | 8.96 | 4.34 | 2.036 | 3.98 | 0.051 |
| 50 | 11.3 | 5.62 | 2.234 | 5.01 | 0.045 |
| 100 | 21.8 | 10.5 | 2.922 | 10.0 | 0.029 |
| 200 | 42.7 | 20.2 | 4.166 | 20.1 | 0.021 |

BN254 with Ed25519:

| $\ell$ | client blind | issuer sign | client verify | client unmask | verify, per token |
|---|---|---|---|---|---|
| 1 | 0.396 | 0.219 | 0.462 | 0.046 | 0.462 |
| 5 | 0.745 | 0.459 | 0.766 | 0.230 | 0.153 |
| 10 | 1.18 | 0.752 | 0.840 | 0.479 | 0.084 |
| 20 | 2.06 | 1.36 | 0.979 | 1.05 | 0.049 |
| 30 | 2.99 | 1.98 | 1.096 | 1.69 | 0.037 |
| 40 | 3.69 | 2.55 | 1.251 | 2.27 | 0.031 |
| 50 | 4.55 | 3.22 | 1.328 | 2.91 | 0.027 |
| 100 | 8.79 | 6.22 | 1.678 | 5.92 | 0.017 |
| 200 | 16.8 | 12.3 | 2.445 | 11.9 | 0.012 |

BN254 with Pallas:

| $\ell$ | client blind | issuer sign | client verify | client unmask | verify, per token |
|---|---|---|---|---|---|
| 1 | 0.395 | 0.218 | 0.460 | 0.046 | 0.460 |
| 5 | 0.738 | 0.458 | 0.770 | 0.225 | 0.154 |
| 10 | 1.18 | 0.756 | 0.838 | 0.463 | 0.084 |
| 20 | 2.05 | 1.37 | 0.969 | 1.07 | 0.049 |
| 30 | 2.91 | 1.97 | 1.092 | 1.67 | 0.036 |
| 40 | 3.77 | 2.55 | 1.254 | 2.25 | 0.031 |
| 50 | 4.63 | 3.15 | 1.321 | 2.91 | 0.026 |
| 100 | 8.84 | 6.06 | 1.674 | 5.93 | 0.017 |
| 200 | 17.0 | 12.2 | 2.433 | 11.9 | 0.012 |

**The paper reports 60.72 ms for this step at $\ell = 100$ against 2.82 here, a factor of twenty.**
That matters because it is the wallet-visible latency of buying tokens, and it is available without
any protocol change: the whole win is that the two repeated $G_2$ elements are recognized as
repeated. Verification has stopped being the client's bottleneck. Blinding is, at 21.5 ms, and
unmasking is next at 10.1 against 2.82.

The `DS` group barely enters this table, which is not obvious in advance: blinding generates
$\ell$ ephemeral keys, so a 2x cheaper keygen ought to show. It does not, because keygen is batched
through a `BatchMulPreprocessing` window table over the shared `DS` generator. The table costs about
0.38 ms to build and then 0.011 ms per key against 0.098 for a loop, so on Ed25519 it is 0.478 ms
against 0.098 at one key, break-even at about six, and 1.51 against 5.71 at a hundred. What is left
after batching is small enough on both curves that blinding is dominated by the $\ell$ hash-to-$G_1$
and $G_1$ scalar mults on the pairing curve instead, which is why BLS12-381 with Pallas and with
Ed25519 agree to within noise. A client buying fewer than about six tokens should generate them in a
loop instead.

### Π-Execute, on chain

Both transactions are $O(1)$ in $\ell$. The client's message is decode only, a $G_2$ subgroup check
on $com_k$ plus the refund key, and this is the one place the `DS` group shows up on chain outside
$\gamma$:

| | client msg decode | issuer key decode |
|---|---|---|
| BLS12-381 / Ed25519 | 0.133 ms | 0.078 ms |
| BLS12-381 / Pallas | 0.083 ms | 0.079 ms |
| BN254 / Ed25519 | 0.135 ms | 0.080 ms |
| BN254 / Pallas | 0.085 ms | 0.080 ms |

Ed25519's subgroup check costs about 0.05 ms more than Pallas's, which is the whole difference.

The issuer's message is one check $k . pk_{iss} == com_k$ in $G_2$, and a block carries $m$ of them.
It touches no `DS` key at all, so it depends only on the pairing curve; the two `DS` columns agree
to within a percent everywhere and only one is given.

BLS12-381, milliseconds:

| $m$ | $J$ keys | fixed-base cold | fixed-base warm | RMC |
|---|---|---|---|---|
| 1 | 1 | 1.73 | 0.071 | 0.433 |
| 5 | 1 | 2.01 | 0.312 | 0.869 |
| 10 | 1 | 2.40 | 0.651 | 1.24 |
| 20 | 1 | 3.11 | 1.37 | 1.90 |
| 50 | 1 | 5.08 | 2.79 | 3.81 |
| 100 | 1 | 7.91 | 5.67 | 5.73 |
| 100 | 10 | 29.3 | 7.08 | 6.08 |

BN254:

| $m$ | $J$ keys | fixed-base cold | fixed-base warm | RMC |
|---|---|---|---|---|
| 1 | 1 | 0.720 | 0.033 | 0.228 |
| 5 | 1 | 0.849 | 0.156 | 0.474 |
| 10 | 1 | 1.03 | 0.327 | 0.669 |
| 20 | 1 | 1.39 | 0.650 | 1.02 |
| 50 | 1 | 2.53 | 1.43 | 2.03 |
| 100 | 1 | 4.12 | 2.98 | 3.03 |
| 100 | 10 | 14.2 | 3.91 | 3.21 |

Two ways to batch and they win in different places. A `BatchMulPreprocessing` window table on
$pk_{iss}$ is dramatic at small $m$, where the checker's fixed bookkeeping dominates: 0.071 ms
against 0.433 at $m = 1$, a factor of six. By $m = 100$ on one key the two have converged, 5.67
against 5.73. But the table is per key: at $J = 10$ each one serves ten scalars and it degrades to
7.08 while the checker holds at 6.08. And cold it is a loss everywhere, 1.73 ms at $m = 1$ and 7.91
at $m = 100$, so it only pays as a warm cache.

Issuer keys are long-lived registry state, so a warm cache is realistic, but it makes invalidation on
register and retire a pallet obligation. The checker needs no cache, no invalidation and does not
care how reveals distribute. Take the checker as the default and add the table only if blocks
routinely carry a handful of reveals concentrated on one key, which is where its six-fold advantage
lives; past $m \approx 100$ the table has nothing left to give. Under denomination pools an honest
issuer holds $D$ keys rather than one, which pushes the realistic case towards the $J = 10$ column
where the table is already behind.

The checker is a locally randomized check, not Fiat-Shamir. Each node draws its own randomness and
never reveals it, so nothing is aimable at a node's coin, an honest batch passes for every draw and a
dishonest one fails except with probability $m/p$. Two obligations follow and both belong to the
pallet. Consensus needs that divergence probability argued rather than assumed. And a failing batch
names no culprit, so rejection has to fall back to per-item checking to attribute the failure, which
is a liveness and attribution requirement rather than a soundness one.

### Spend, on chain

$n$ tokens across $J$ issuer keys fold into one multi-pairing of $1 + J$ pairs. Hash-to-curve and
nullifier distinctness stay per token. In DART $\gamma$ is the extrinsic signature the node verifies
regardless, so the no-DS column is the one that belongs against the current fee proof.

Both chain columns are the whole check, hash-to-curve plus nullifier distinctness plus the pairing,
so hash-to-curve is a component of them rather than something to add on. They are separate timings
of the same batch rather than one derived from the other, so at $n = 1$, where the `DS` batch is
0.03 to 0.17 ms against a 0.5 to 0.9 ms check, run-to-run noise can leave them within a few percent
of each other.

The $J$ column is the denomination question in disguise. Under pools a payment spending $d$ distinct
denominations has $J = d$, so the $J = n$ rows are what a multi-denomination fee actually costs.

BLS12-381 with Ed25519, milliseconds:

| $n$ | $J$ | hash-to-curve | chain, no DS | DS batched | chain, with DS | per token, no DS |
|---|---|---|---|---|---|---|
| 1 | 1 | 0.063 | 0.892 | 0.172 | 1.089 | 0.892 |
| 4 | 1 | 0.292 | 1.464 | 0.273 | 1.732 | 0.366 |
| 4 | 4 | 0.278 | 2.118 | 0.271 | 2.362 | 0.530 |
| 8 | 1 | 0.661 | 1.981 | 0.386 | 2.359 | 0.248 |
| 8 | 8 | 0.657 | 3.456 | 0.387 | 3.865 | 0.432 |
| 16 | 1 | 1.46 | 2.996 | 0.731 | 3.729 | 0.187 |
| 16 | 16 | 1.51 | 6.190 | 0.730 | 6.911 | 0.387 |
| 64 | 1 | 6.15 | 8.697 | 1.67 | 10.3 | 0.136 |
| 128 | 1 | 12.5 | 15.8 | 2.89 | 18.7 | 0.124 |
| 512 | 1 | 49.8 | 58.0 | 7.96 | 65.7 | 0.113 |
| 512 | 64 | 49.7 | 70.7 | 7.93 | 78.8 | 0.138 |

BLS12-381 with Pallas:

| $n$ | $J$ | hash-to-curve | chain, no DS | DS batched | chain, with DS | per token, no DS |
|---|---|---|---|---|---|---|
| 1 | 1 | 0.075 | 0.912 | 0.034 | 0.923 | 0.912 |
| 4 | 1 | 0.304 | 1.473 | 0.104 | 1.562 | 0.368 |
| 4 | 4 | 0.313 | 2.066 | 0.104 | 2.218 | 0.517 |
| 8 | 1 | 0.675 | 1.954 | 0.182 | 2.127 | 0.244 |
| 8 | 8 | 0.640 | 3.419 | 0.182 | 3.567 | 0.427 |
| 16 | 1 | 1.47 | 2.932 | 0.340 | 3.297 | 0.183 |
| 16 | 16 | 1.44 | 6.048 | 0.340 | 6.405 | 0.378 |
| 64 | 1 | 6.09 | 8.558 | 1.40 | 9.976 | 0.134 |
| 128 | 1 | 12.4 | 15.7 | 2.44 | 18.2 | 0.123 |
| 512 | 1 | 50.6 | 58.4 | 5.99 | 64.2 | 0.114 |
| 512 | 64 | 49.5 | 70.9 | 5.96 | 77.0 | 0.138 |

BN254 with Ed25519:

| $n$ | $J$ | hash-to-curve | chain, no DS | DS batched | chain, with DS | per token, no DS |
|---|---|---|---|---|---|---|
| 1 | 1 | 0.016 | 0.476 | 0.172 | 0.678 | 0.476 |
| 4 | 1 | 0.065 | 0.816 | 0.286 | 1.112 | 0.204 |
| 4 | 4 | 0.039 | 1.273 | 0.272 | 1.502 | 0.318 |
| 8 | 1 | 0.068 | 0.882 | 0.385 | 1.267 | 0.110 |
| 8 | 8 | 0.130 | 2.020 | 0.383 | 2.390 | 0.253 |
| 16 | 1 | 0.204 | 1.121 | 0.727 | 1.849 | 0.070 |
| 16 | 16 | 0.148 | 3.368 | 0.727 | 4.087 | 0.211 |
| 64 | 1 | 0.780 | 2.218 | 1.66 | 3.903 | 0.035 |
| 128 | 1 | 1.43 | 3.353 | 2.89 | 6.279 | 0.026 |
| 512 | 1 | 5.80 | 10.2 | 7.94 | 18.1 | 0.020 |
| 512 | 64 | 5.96 | 19.9 | 7.98 | 28.1 | 0.039 |

BN254 with Pallas:

| $n$ | $J$ | hash-to-curve | chain, no DS | DS batched | chain, with DS | per token, no DS |
|---|---|---|---|---|---|---|
| 1 | 1 | 0.006 | 0.482 | 0.034 | 0.503 | 0.482 |
| 4 | 1 | 0.049 | 0.798 | 0.104 | 0.901 | 0.199 |
| 4 | 4 | 0.049 | 1.256 | 0.105 | 1.347 | 0.314 |
| 8 | 1 | 0.074 | 0.885 | 0.181 | 1.065 | 0.111 |
| 8 | 8 | 0.089 | 1.965 | 0.182 | 2.132 | 0.246 |
| 16 | 1 | 0.153 | 1.075 | 0.339 | 1.411 | 0.067 |
| 16 | 16 | 0.143 | 3.326 | 0.339 | 3.653 | 0.208 |
| 64 | 1 | 0.703 | 2.151 | 1.42 | 3.586 | 0.034 |
| 128 | 1 | 1.60 | 3.519 | 2.43 | 6.022 | 0.028 |
| 512 | 1 | 6.17 | 10.6 | 6.02 | 16.6 | 0.021 |
| 512 | 64 | 5.87 | 19.9 | 5.97 | 25.9 | 0.039 |

Against the 5.714 ms verify of `FeeAccountPaymentProof` measured below, a single spend is 6.4x
cheaper on BLS12-381 and 12.0x on BN254. At block scale with one issuer the per-token figures are
0.113 and 0.020 ms, which is 50x and 287x. The order-of-magnitude claim in the paper's abstract
survives contact with a second implementation, and batching widens it rather than narrowing it. The
`DS` group changes none of this, because the pairing columns do not depend on it: it is the same
batch of tokens either way, differing only in which curve $\gamma$ lives on.

$J$ costs real time, and it is the cost denominations impose. At $n = 16$, going from one issuer key
to sixteen takes the batch from 3.00 to 6.19 ms on BLS12-381, because the multi-miller-loop goes
from 2 pairs to 17 and the $G_1$ side fragments from one MSM of 16 into sixteen of size 1.

Settling a whole block through one checker pair rather than one per payment is the largest single
win available on the verifier side, because the grouping is across the block rather than within a
payment. At 128 payments of four tokens under one issuer key:

| | per-payment settle | one checker for block | speedup | per token |
|---|---|---|---|---|
| BLS12-381 / Ed25519 | 231.3 ms | 65.9 ms | 3.51x | 0.129 ms |
| BLS12-381 / Pallas | 209.7 | 65.0 | 3.22x | 0.127 |
| BN254 / Ed25519 | 137.8 | 18.4 | 7.50x | 0.036 |
| BN254 / Pallas | 116.5 | 16.7 | 6.98x | 0.033 |

The whole block is two groups, so it is two $G_1$ MSMs of size 512 and a two-pair multi-miller-loop
for 128 fee payments. It needs the fee check lifted out of per-extrinsic validation, which is pallet
work. Pallas's smaller speedup is not a worse result: the per-payment column it is measured against
is already cheaper, because 512 Ed25519 signatures cost 8.0 ms against Pallas's 6.0. Under pools the
block carries $1 + D$ groups rather than 2, so this factor shrinks as $D$ grows.

### Client signature group

The paper uses Ed25519 for `DS`. Pallas is the obvious alternative here because DART already carries
it for the curve trees, so ephemeral keys on Pallas add no new curve to the verifier. Both are
measured throughout the tables above; neither is removed.

Sizes are identical. Both have 32-byte compressed points and 32-byte scalars, so the signature is
64 B and the token is 144 B on BLS12-381 and 128 B on BN254 either way.

Times, per signature and then batched through `RandomizedMultChecker`:

| | Ed25519 | Pallas |
|---|---|---|
| keygen | 0.056 ms | 0.030 ms |
| sign | 0.056 | 0.029 |
| verify | 0.092 | 0.044 |
| batch verify, $n = 1$ | 0.172 | 0.034 |
| batch verify, $n = 512$ | 7.96 | 5.99 |
| $com_k$ + $pk_{ref}$ decode | 0.133 | 0.083 |

End to end the effect is small, because the pairing dominates everything except the smallest batch.
Full chain verification including `DS` goes from 1.089 to 0.923 ms at $n = 1$ on BLS12-381 and from
0.678 to 0.503 on BN254, then converges: at $n = 512$ it is 65.7 against 64.2, and 18.1 against 16.6.
The largest effect anywhere is on the client, where producing a payment is nothing but signatures:
0.056 ms per token against 0.029.

**The 2x is not a property of the curves.** It is arkworks representing $2^{255} - 19$ as a generic
256-bit Montgomery field, where `curve25519-dalek` uses a radix representation specialised to that
prime and is several times quicker. A deployment would not use arkworks Ed25519, so this table
prices *this implementation* of Ed25519 against *this implementation* of Pallas, and a real Ed25519
library would likely close the gap or reverse it. Nothing here says Pallas is the faster curve. Nor
does the Montgomery form of the same curve recover anything: `ark-curve25519` is the same base field
in the parameterization with $COEFF_A = 486664$ and no `mul_by_a` override, so it pays a field
multiplication where `ark-ed25519`'s $COEFF_A = -1$ pays a negation, and it is strictly slower.

What does survive the caveat is architectural. Pallas is already in the verifier for curve trees, so
`pk_e` on Pallas introduces no new field arithmetic, no new subgroup check and no new audit surface,
where Ed25519 is a third curve alongside Pallas, Vesta and the pairing curve.

Against that sits an interaction with the wire format, and it may dominate. The claim that
$\gamma$ is free because it is the extrinsic signature needs the node to be verifying that
signature anyway. Substrate has no Pallas signature type, so a Pallas $\gamma$ has to ride in
the payload and be checked separately, which turns the whole `DS` column from free into real cost.
The Ed25519 case is better but not clean either: a fee token is spent by a fresh one-time key with
no account behind it, so it is not an ordinary signed extrinsic whichever curve signs it, and the
reuse needs a custom transaction extension to be real. Until that is settled the honest reading of
the spend tables is the *with DS* column, not the *no DS* one, on all four combinations.

### Against the current mechanism, at one denomination

The paper mints one unit per accepted spend, so a fee of $\ell$ base units costs $\ell$ tokens,
while `6.md` pays any amount with a single proof. That makes the comparison a function of $\ell$
rather than a single ratio. Everything in this subsection is a single denomination. The two current
proofs BAT would replace, measured on the same machine in the same run, with SCALE sizes because
that is what goes on chain:

| | prove | verify | size |
|---|---|---|---|
| `FeeAccountTopupProof` | 53.0 ms | 5.765 ms | 4,655 B |
| `FeeAccountPaymentProof` | 52.9 ms | 5.714 ms | 4,787 B |

`FeeAccountRegistrationProof` is not measured. It has no BAT counterpart, since tokens are bearer
objects and no fee account is ever created, so it appears in neither column of the comparison.

Funding is the part BAT wins outright. A top-up moves any amount for one proof; BAT's issuance moves
$L$ tokens for two transactions that are $O(1)$ in $L$. On-chain time is flat in $L$, so one row per
combination at $L = 100$ carries it, with the full sweep in the run output:

| | client off chain | issuer off chain | chain, both transactions | on-chain bytes | vs top-up |
|---|---|---|---|---|---|
| BLS12-381 / Ed25519 | 34.3 ms | 10.3 ms | 0.587 ms | 228 B | 9.8x |
| BLS12-381 / Pallas | 35.2 | 10.6 | 0.548 | 228 | 10.5x |
| BN254 / Ed25519 | 16.4 | 6.39 | 0.378 | 196 | 15.2x |
| BN254 / Pallas | 16.4 | 6.25 | 0.311 | 196 | 18.5x |

Against 5.765 ms and 4,655 B for a top-up that is 10x to 19x in chain time and 20x on bytes, flat in
$L$, and the traffic that does scale with $L$ is off chain between client and issuer where it costs
the chain nothing. The `DS` group is worth 7 to 18 percent here because most of the on-chain cost is
the $pk_{ref}$ subgroup check. Both reveals go through the checker; on a block carrying a single
reveal the warm window table would cut those figures by about 0.36 ms, which roughly triples the
ratio but buys a cache.

Payment is where the single denomination bites. Ratios above 1 favour BAT.

BLS12-381 with Ed25519:

| fee amount $\ell$ | `6.md` client | BAT client | `6.md` chain | BAT chain, no DS | BAT chain, with DS | BAT bytes | chain | bytes |
|---|---|---|---|---|---|---|---|---|
| 1 | 52.9 ms | 0.056 ms | 5.714 ms | 0.902 ms | 1.067 ms | 144 | 6.33x | 33.2x |
| 5 | 52.9 | 0.281 | 5.714 | 1.626 | 1.894 | 720 | 3.51x | 6.65x |
| 10 | 52.9 | 0.561 | 5.714 | 2.241 | 2.670 | 1,440 | 2.55x | 3.32x |
| 20 | 52.9 | 1.13 | 5.714 | 3.463 | 4.239 | 2,880 | 1.65x | 1.66x |
| 30 | 52.9 | 1.69 | 5.714 | 4.766 | 5.615 | 4,320 | 1.20x | 1.11x |
| 40 | 52.9 | 2.25 | 5.714 | 6.053 | 7.118 | 5,760 | 0.94x | 0.83x |
| 50 | 52.9 | 2.82 | 5.714 | 6.937 | 8.182 | 7,200 | 0.82x | 0.66x |
| 100 | 52.9 | 5.62 | 5.714 | 12.5 | 14.6 | 14,400 | 0.46x | 0.33x |
| 200 | 52.9 | 11.2 | 5.714 | 23.7 | 27.7 | 28,800 | 0.24x | 0.17x |

BLS12-381 with Pallas:

| fee amount $\ell$ | BAT client | BAT chain, no DS | BAT chain, with DS | BAT bytes | chain | bytes |
|---|---|---|---|---|---|---|
| 1 | 0.030 ms | 0.922 ms | 0.941 ms | 144 | 6.20x | 33.2x |
| 5 | 0.146 | 1.628 | 1.717 | 720 | 3.51x | 6.65x |
| 10 | 0.293 | 2.246 | 2.447 | 1,440 | 2.54x | 3.32x |
| 20 | 0.584 | 3.489 | 3.902 | 2,880 | 1.64x | 1.66x |
| 30 | 0.884 | 4.710 | 5.333 | 4,320 | 1.21x | 1.11x |
| 40 | 1.18 | 5.954 | 6.892 | 5,760 | 0.96x | 0.83x |
| 50 | 1.47 | 7.119 | 8.154 | 7,200 | 0.80x | 0.66x |
| 100 | 2.92 | 12.5 | 14.5 | 14,400 | 0.46x | 0.33x |
| 200 | 5.90 | 23.8 | 27.0 | 28,800 | 0.24x | 0.17x |

BN254 with Ed25519:

| fee amount $\ell$ | BAT client | BAT chain, no DS | BAT chain, with DS | BAT bytes | chain | bytes |
|---|---|---|---|---|---|---|
| 1 | 0.056 ms | 0.494 ms | 0.640 ms | 128 | 11.6x | 37.4x |
| 5 | 0.280 | 0.834 | 1.158 | 640 | 6.85x | 7.48x |
| 10 | 0.560 | 0.952 | 1.430 | 1,280 | 6.00x | 3.74x |
| 20 | 1.20 | 1.244 | 1.994 | 2,560 | 4.60x | 1.87x |
| 30 | 1.68 | 1.417 | 2.365 | 3,840 | 4.03x | 1.25x |
| 40 | 2.24 | 1.701 | 2.828 | 5,120 | 3.36x | 0.93x |
| 50 | 2.81 | 1.926 | 3.212 | 6,400 | 2.97x | 0.75x |
| 100 | 5.65 | 2.829 | 5.023 | 12,800 | 2.02x | 0.37x |
| 200 | 11.2 | 4.922 | 8.796 | 25,600 | 1.16x | 0.19x |

BN254 with Pallas:

| fee amount $\ell$ | BAT client | BAT chain, no DS | BAT chain, with DS | BAT bytes | chain | bytes |
|---|---|---|---|---|---|---|
| 1 | 0.030 ms | 0.471 ms | 0.547 ms | 128 | 12.1x | 37.4x |
| 5 | 0.146 | 0.828 | 0.945 | 640 | 6.90x | 7.48x |
| 10 | 0.292 | 0.934 | 1.152 | 1,280 | 6.12x | 3.74x |
| 20 | 0.583 | 1.160 | 1.581 | 2,560 | 4.93x | 1.87x |
| 30 | 0.877 | 1.425 | 2.044 | 3,840 | 4.01x | 1.25x |
| 40 | 1.17 | 1.659 | 2.610 | 5,120 | 3.44x | 0.93x |
| 50 | 1.46 | 1.849 | 2.944 | 6,400 | 3.09x | 0.75x |
| 100 | 2.91 | 2.858 | 4.738 | 12,800 | 2.00x | 0.37x |
| 200 | 5.86 | 4.702 | 7.915 | 25,600 | 1.22x | 0.19x |

The crossovers are the point, they are set by the pairing curve alone, and the two curves fail
differently.

On BLS12-381 bytes cross at $4787/144 = 33.2$ and chain time at $\ell \approx 37$ on both `DS`
groups, going 1.20x at 30 to 0.94x at 40. Both land in the thirties, with payload binding first, and
the byte crossover is fixed by serialization rather than tunable.

On BN254 they separate by most of an order of magnitude. Bytes cross at $4787/128 = 37.4$, confirmed
by the 1.25x at 30 and 0.93x at 40, while chain time does not cross until $\ell \approx 250$, still
at 1.16x at $\ell = 200$. So on BN254 the binding constraint is payload, not verification, and
choosing BN254 for its cheaper pairings buys nothing past $\ell \approx 37$ because bytes bind first.
Any argument that BN254's 100-bit security is worth taking for the speed has to contend with that:
the speed is not what runs out.

So BAT at one denomination beats the current mechanism for small fees by a wide margin, 6.2x to
12.1x on chain time and 33x to 37x on bytes at $\ell = 1$, and loses above roughly thirty-five base
units on all four combinations once payload is counted. The order-of-magnitude claim is real but it
is a claim about a one-unit payment, and a fee mechanism that only wins below thirty-five units is
not a fee mechanism.

Client cost is the exception that holds everywhere, and it is the one place the `DS` group decides
the answer, because producing a payment is $\ell$ signatures and nothing else. Against 52.9 ms for
one curve-tree proof plus a Bulletproofs range proof, charging the amortized issuance in as well at
a hundred tokens per purchase:

| | per token, issuance | per token, signing | total per payment | crosses 52.9 ms at |
|---|---|---|---|---|
| BLS12-381 / Ed25519 | 0.343 ms | 0.056 ms | $0.399\ell$ | $\ell = 133$ |
| BLS12-381 / Pallas | 0.352 | 0.029 | $0.381\ell$ | $\ell = 139$ |
| BN254 / Ed25519 | 0.164 | 0.057 | $0.221\ell$ | $\ell = 239$ |
| BN254 / Pallas | 0.164 | 0.029 | $0.193\ell$ | $\ell = 274$ |

The device and the wallet are comfortably better off under BAT across the whole realistic range even
where the chain is not.

**This is what makes denominations a precondition rather than an optimization.** Every number above
is for one denomination, one unit per token. The next subsection prices the only denomination scheme
that fits BAT's token shape.

### Against the current mechanism, with denominations

A set of $D$ powers of two covers every fee up to $2^D - 1$. The worst case is all $D$ bits set, so
$D$ tokens; the average over uniformly drawn fees is $D/2$. The scheme is the paper's §8 pools, one
issuer key per denomination, which makes a payment spending $d$ denominations a spend over $d$ issuer
keys. `DS` is excluded, since it is one signature per token under any scheme. Ratios above 1 favour
BAT.

BLS12-381 with Ed25519:

| $D$ | largest fee | worst case, $D$ tokens | average case, $D/2$ | worst vs `6.md` | average vs `6.md` | bytes, worst |
|---|---|---|---|---|---|---|
| 8 | 255 | 3.483 ms | 2.117 ms | 1.64x | 2.70x | 1,152 B |
| 16 | 65,535 | 6.194 | 3.531 | 0.92x | 1.62x | 2,304 |
| 24 | 16.8M | 8.897 | 4.877 | 0.64x | 1.17x | 3,456 |
| 32 | 4.29G | 11.3 | 6.221 | 0.51x | 0.92x | 4,608 |
| 48 | 2.81e14 | 16.7 | 8.745 | 0.34x | 0.65x | 6,912 |
| 64 | 1.84e19 | 22.0 | 11.4 | 0.26x | 0.50x | 9,216 |

BLS12-381 with Pallas:

| $D$ | worst case, $D$ tokens | average case, $D/2$ | worst vs `6.md` | average vs `6.md` |
|---|---|---|---|---|
| 8 | 3.531 ms | 2.138 ms | 1.62x | 2.67x |
| 16 | 6.156 | 3.562 | 0.93x | 1.60x |
| 24 | 8.917 | 4.842 | 0.64x | 1.18x |
| 32 | 11.4 | 6.181 | 0.50x | 0.92x |
| 48 | 16.6 | 8.789 | 0.34x | 0.65x |
| 64 | 21.6 | 11.4 | 0.26x | 0.50x |

BN254 with Ed25519:

| $D$ | worst case, $D$ tokens | average case, $D/2$ | worst vs `6.md` | average vs `6.md` | bytes, worst |
|---|---|---|---|---|---|
| 8 | 1.978 ms | 1.286 ms | 2.89x | 4.44x | 1,024 B |
| 16 | 3.355 | 2.046 | 1.70x | 2.79x | 2,048 |
| 24 | 5.067 | 2.767 | 1.13x | 2.06x | 3,072 |
| 32 | 6.214 | 3.391 | 0.92x | 1.68x | 4,096 |
| 48 | 8.870 | 4.821 | 0.64x | 1.19x | 6,144 |
| 64 | 11.7 | 6.214 | 0.49x | 0.92x | 8,192 |

BN254 with Pallas:

| $D$ | worst case, $D$ tokens | average case, $D/2$ | worst vs `6.md` | average vs `6.md` |
|---|---|---|---|---|
| 8 | 1.984 ms | 1.234 ms | 2.88x | 4.63x |
| 16 | 3.355 | 1.927 | 1.70x | 2.97x |
| 24 | 4.772 | 2.589 | 1.20x | 2.21x |
| 32 | 6.104 | 3.308 | 0.94x | 1.73x |
| 48 | 8.851 | 4.733 | 0.65x | 1.21x |
| 64 | 11.6 | 6.158 | 0.49x | 0.93x |

The `DS` group does not move these, as it should not, and the byte columns depend only on the
pairing curve: a pool token is the paper's token unchanged, since the issuer index the payload
already carries names the denomination.

**Pools do not clear `6.md` at a realistic denomination set.** In the worst case they fall below it
at $D = 16$ on BLS12-381 and $D = 32$ on BN254; in the average case at $D = 32$ and $D = 64$. Polymesh
needs $D$ in the 20 to 30 range, with six decimals putting one POLYX at $10^6$ base units and a
thousand at $10^9$. Over that range pools run at 0.64x to 0.51x worst case and 1.17x to 0.92x average
case on BLS12-381, and 1.20x to 0.92x worst and 2.21x to 1.68x average on BN254.

So on BLS12-381 the mechanism is slower than the one it would replace for any fee that sets more than
about half the bits, and slower on the average fee from $D = 32$. On BN254 it holds a small margin
through the range that matters and loses it by $D = 32$ worst case. Bytes stay favourable throughout,
4,608 B against 4,787 at $D = 32$ on BLS12-381 and half that on BN254, so payload is not what binds
here; verification is.

Two things drive the cost, and both are structural rather than implementation slack. Each denomination
is a distinct $G_2$ element, so a $d$-denomination payment is a $1 + d$ pair multi-pairing instead of
two pairs. And the $G_1$ side fragments with it: the checker groups by $G_2$ element, so $d$ keys give
$d$ MSMs of size 1 where one key gives a single MSM of size $d$, which is where the batching that
makes the single-denomination numbers good is lost. Comparing the $J = 1$ and $J = n$ rows of the
spend tables isolates it: at $n = 16$ on BLS12-381, 3.00 ms against 6.19.

One caveat the tables do not carry. $D$ is the size of the denomination set, and every denomination is
a separate anonymity pool, because value is public at spend. A larger $D$ buys reach and costs
unlinkability, and the pools it creates are not equal, since the top denominations will be thinly
used. Sizing $D$ trades privacy against a verification cost that grows in $D$, and these numbers
bound the second of those from above rather than settling the first.

### Refund

One `DS.Verify` for the whole batch rather than $\ell_{ref}$ of them, then the same grouped pairing
at $J = 1$, so two pairs for any $\ell_{ref}$. Chain time, milliseconds:

| $\ell_{ref}$ | BLS / Ed25519 | BLS / Pallas | BN254 / Ed25519 | BN254 / Pallas | payload, BLS |
|---|---|---|---|---|---|
| 1 | 1.022 | 0.985 | 0.577 | 0.550 | 176 B |
| 10 | 2.367 | 2.309 | 1.071 | 0.987 | 896 B |
| 30 | 4.907 | 4.790 | 1.571 | 1.469 | 2,496 B |
| 40 | 6.191 | 5.936 | 1.848 | 1.698 | 3,296 B |
| 50 | 7.316 | 7.074 | 2.020 | 1.973 | 4,096 B |
| 100 | 12.7 | 12.6 | 2.966 | 2.900 | 8,096 B |
| 200 | 24.0 | 23.9 | 4.886 | 4.697 | 16,096 B |

The `DS` group is worth almost nothing here, which is the construction working as intended: one
signature authorizes the whole batch, so $\gamma_{ref}$ is a single verification against
$\ell_{ref}$ pairings. The client side is where it shows, 0.087 ms against 0.090 to sign a
200-token refund request, and neither is a cost worth optimizing. Under pools a refund batch spans
$d$ issuer keys, so the $J = 1$ shape above is the single-denomination case and a real refund pays
the same $1 + d$ pairs a spend does.

This puts a number on the collective-refund congestion gap. At $\ell_{ref} = 100$ a node spends
12.7 ms on BLS12-381 or 2.97 on BN254 per refunding client. Give refunds 500 ms of a block's
execution budget and that is 39 clients per block on BLS12-381, 168 on BN254. Over a $T_{grace}$ of
half an hour at six-second blocks, roughly $1.2 \times 10^4$ and $5.1 \times 10^4$ clients. That is
the per-issuer client cap the paper never derives, and it is one to two orders of magnitude better
than the paper's Ethereum figures, where gas is dominated by storage rather than arithmetic.

The comparison is not decided by this, because the estimate excludes nullifier writes, which are
$\ell_{ref}$ trie insertions per client and are very likely to dominate on Substrate exactly as they
do on Ethereum. What the measurement establishes is that the pairing arithmetic is not the binding
constraint once grouped, so the cap should be derived from storage and payload, and the spike for
it is a runtime benchmark of the nullifier insert rather than anything cryptographic.

