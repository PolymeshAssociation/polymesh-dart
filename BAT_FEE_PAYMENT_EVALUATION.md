# BAT for DART fee payment: measured costs

## TL;DR

On-chain cost of BAT against the current DART fee payment. All times are node verification time and
all sizes are the bytes that go on chain. The current mechanism is a curve-tree membership proof plus
a Bulletproofs range proof plus linked sigmas over the Pasta cycle (Pallas/Vesta). BAT is a pairing
scheme: the numbers here use **BN254 for the tokens (the pairing curve) and Pallas for the client
signature `DS`**; the full report below also prices BLS12-381 tokens and Ed25519 signatures.

The current mechanism BAT would replace is two proofs, each a fixed cost for any amount:

| current mechanism | verify | size |
|---|---|---|
| top-up (funds the fee account) | 3.68 ms | 4,655 B |
| fee payment (pays a fee) | 3.51 ms | 4,787 B |

BAT replaces a fee payment of $n$ base units with $n$ one-unit tokens (one denomination). Issuance is
bought once and is a flat on-chain cost regardless of $n$, because the per-token traffic is off chain
between client and issuer; spend and refund are the per-payment costs and grow linearly in $n$:

| $n$ tokens | issuance time | issuance size | spend time | spend size | refund time | refund size |
|---|---|---|---|---|---|---|
| 1 | 0.30 ms | 196 B | 0.61 ms | 128 B | 0.48 ms | 160 B |
| 5 | 0.30 ms | 196 B | 0.99 ms | 384 B | 0.93 ms | 416 B |
| 10 | 0.30 ms | 196 B | 1.74 ms | 704 B | 1.50 ms | 736 B |
| 20 | 0.30 ms | 196 B | 2.16 ms | 1,344 B | 1.73 ms | 1,376 B |
| 50 | 0.30 ms | 196 B | 3.46 ms | 3,264 B | 2.62 ms | 3,296 B |
| 100 | 0.30 ms | 196 B | 4.80 ms | 6,464 B | 3.87 ms | 6,496 B |
| 200 | 0.30 ms | 196 B | 8.08 ms | 12,864 B | 6.76 ms | 12,896 B |

So BAT beats the current fee payment for small fees and loses the advantage as $n$ grows: against the
3.51 ms / 4,787 B fee-payment proof, a BAT spend is cheaper on time up to about 52 tokens and on size
up to about 74 tokens. Funding is the clear win — a purchase of any size is flat at 0.30 ms / 196 B
on chain against the top-up's 3.68 ms / 4,655 B. Denomination pools cut the token count $n$ carries
for a given fee; the report below prices them.

---

Measurements of [Cryptocurrency-Backed Trustless Anonymous Tokens and Their
Applications](https://eprint.iacr.org/2026/1074) (BAT) Protocol A against the current DART fee
mechanism. Four combinations throughout: BLS12-381 and BN254 for the
tokens, crossed with Ed25519 and Pallas for the client signature scheme `DS`.

## Cost against the current mechanism

The current fee payment is a curve-tree membership proof plus a Bulletproofs range proof plus
linked sigmas. BAT numbers here are from the paper's Table 1 on BLS12-381 with Ed25519 client keys.
*Measured costs* below replaces these with numbers from an
independent implementation and is what the decision should rest on.

This table is per token, which is the comparison the paper invites and it is misleading for a fee
mechanism. *Against the current mechanism, at one denomination* below carries it out to the payment
amounts where it stops holding.

| | current fee payment | BAT spend |
|---|---|---|
| Prove | 51 ms | 0.24 ms |
| Verify | 3.5 ms | 1.68 ms |
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

which is $1 + |J|$ pairings for the whole payment. Hash-to-curve and nullifier distinctness stay
per token. Batching stops there: aggregating across extrinsics would need the fee check lifted out
of per-extrinsic validation and would cost per-payment attribution, which is not a trade worth
making.

## Measured costs

Protocol A implemented and measured on both pairing
curves crossed with both client signature groups: BLS12-381 and BN254 for the tokens, Ed25519 and
Pallas for `DS`. The paper's Table 1 is Protocol A on BLS12-381 with Ed25519 and Table 2 is
Protocol B on BN254, so neither prices either axis on its own. Single-threaded, arkworks, native, no
precompiles. Storage is excluded throughout: nullifier writes are a trie cost that follows from
nothing measured here and will not be small. Every table in this section comes from one run so the
columns are comparable to each other. The current-mechanism baseline is re-measured in the same run and drifts
several percent between runs, so the third digit of any ratio should not be quoted.

Two departures from the paper, both measured here rather than assumed. `DS` is batch Schnorr, one
`(t, s)` for the whole payment instead of one per token, which the next-but-one paragraph explains.
And hash-to-`G1` on BN254 is the RFC 9380 Shallue-van de Woestijne map rather than try-and-increment,
which the arkworks fork now carries for `G1` and `G2`.

The two axes are independent and it shows. The pairing curve sets everything on the token side and
BN254 is roughly 2x to 3x cheaper than BLS12-381 throughout. The `DS` group sets only $\gamma$, and
in this implementation Pallas is about 2x Ed25519 on every `DS` operation, which now moves the
totals by very little, because batching has made `DS` a small term. Where a quantity depends on only
one axis the table says so rather than repeating four near-identical copies.

**`DS` is batch Schnorr**, Fig. 2 of
[the Asiacrypt 2004 protocol](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf) that
DART already uses for key registration. A payment's $\ell$ ephemeral keys were all generated by
one client, so one prover knows every $sk_e$, which is exactly that setting:

$$
t = g*r, \quad c = H(t, pk_{e,1} \dots pk_{e,\ell}, ad), \quad s = r + \sum_i{c^i . sk_{e,i}}
$$

$$
g*s == t + \sum_i{pk_{e,i}*c^i}
$$

One `G1` MSM of size $\ell + 1$ to verify, one scalar mult to sign, and 64 bytes per payment rather
than per token. It binds the ordered key set, so a reordered or truncated spend yields a different
challenge, and it does not reject a repeated key, so nullifier distinctness stays a separate check.
Aggregation stops at the payment: batching across submitters would go further still, but a rejected
batch would name no submitter, and per-extrinsic attribution is worth more than the factor.

Serialized sizes. A token is $pk_e$ and $\alpha$, 80 B on BLS12-381 and 64 B on BN254, both `DS`
groups alike since Pallas and Ed25519 have 32-byte points and 32-byte scalars. A payment adds one
64 B signature. Issuance is unchanged from the paper and matches it to the byte: request
512 / 2,432 / 4,832 B and response 608 / 2,528 / 4,928 B at $\ell = 10 / 50 / 100$ on BLS12-381.

Every pairing check routes through `RandomizedPairingChecker` from `dock_crypto_utils`, taken by
reference so a payment settling several equations pays one final exponentiation rather than one per
equation.

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
| $G_1$ scalar mult | 0.092 ms | 0.043 ms |
| $G_2$ scalar mult | 0.124 ms | 0.061 ms |
| $G_1$ MSM, 100 | 0.89 ms | 0.66 ms |
| pairing | 0.49 ms | 0.29 ms |
| multi-pairing, 2 pairs | 0.63 ms | 0.37 ms |
| final exponentiation | 0.49 ms | 0.27 ms |
| hash to $G_1$ | 0.055 ms (WB) | 0.025 ms (SVDW) |

| | Ed25519 | Pallas |
|---|---|---|
| `DS` keygen | 0.057 ms | 0.029 ms |
| `DS` sign | 0.056 ms | 0.029 ms |
| `DS` verify | 0.093 ms | 0.044 ms |

Both curves now run RFC 9380, BLS12-381 over the WB isogeny and BN254 over the Shallue-van de
Woestijne map, which applies where SWU does not because it admits `a.b = 0` and BN254's $G_1$ is
$y^2 = x^3 + 3$. The remaining 2.2x between them is cofactor clearing: BLS12-381's $G_1$ has cofactor
about $2^{126}$ and BN254's is 1.

**The constant-time map costs BN254 a factor of four.** Try-and-increment on the same curve measured
0.0060 ms against SVDW's 0.025. That is a larger gap than the earlier reading of this table
predicted, and the earlier reasoning was wrong in a way worth recording: measuring BLS12-381 both
ways gave 0.079 for try-and-increment against 0.078 for WB, indistinguishable, and the inference
drawn was that the map never matters because cofactor clearing dominates. It dominates on BLS12-381,
whose cofactor is $2^{126}$. BN254's cofactor is 1, so there is nothing to dominate the map and the
map is the whole cost. Try-and-increment is variable time in the number of increments and so is not
deployable; the 4x is what correctness costs, and it is paid per token on the term that does not
batch.

### Issuance, off chain

The client's check $\forall i : e(\tilde\sigma_i, h) == e(X_i, com_k)$ has the same $h$ and $com_k$
in every one of the $\ell$ equations, so the checker holds two groups and settles it as two $G_1$
MSMs of size $\ell$ and a two-pair multi-miller-loop.

BLS12-381 with Ed25519, milliseconds:

| $\ell$ | client blind | issuer sign | client verify | client unmask | verify, per token |
|---|---|---|---|---|---|
| 1 | 0.663 | 0.245 | 0.750 | 0.090 | 0.750 |
| 5 | 1.42 | 0.657 | 1.038 | 0.453 | 0.208 |
| 10 | 2.18 | 1.17 | 1.466 | 0.937 | 0.147 |
| 20 | 3.94 | 2.21 | 1.623 | 1.94 | 0.081 |
| 30 | 5.51 | 3.25 | 1.733 | 3.00 | 0.058 |
| 40 | 7.08 | 4.24 | 1.660 | 4.07 | 0.042 |
| 50 | 8.83 | 5.28 | 1.832 | 5.16 | 0.037 |
| 100 | 17.0 | 10.6 | 2.053 | 10.3 | 0.021 |
| 200 | 33.3 | 20.7 | 2.399 | 20.7 | 0.012 |

BLS12-381 with Pallas:

| $\ell$ | client blind | issuer sign | client verify | client unmask | verify, per token |
|---|---|---|---|---|---|
| 1 | 0.535 | 0.245 | 0.747 | 0.093 | 0.747 |
| 5 | 1.23 | 0.664 | 1.041 | 0.440 | 0.208 |
| 10 | 2.07 | 1.17 | 1.518 | 0.931 | 0.152 |
| 20 | 3.68 | 2.23 | 1.683 | 1.96 | 0.084 |
| 30 | 5.36 | 3.21 | 1.683 | 3.04 | 0.056 |
| 40 | 7.02 | 4.21 | 1.623 | 4.09 | 0.041 |
| 50 | 8.60 | 5.31 | 1.812 | 5.08 | 0.036 |
| 100 | 16.9 | 10.6 | 2.119 | 10.3 | 0.021 |
| 200 | 33.3 | 20.7 | 2.390 | 20.6 | 0.012 |

BN254 with Ed25519:

| $\ell$ | client blind | issuer sign | client verify | client unmask | verify, per token |
|---|---|---|---|---|---|
| 1 | 0.489 | 0.142 | 0.442 | 0.046 | 0.442 |
| 5 | 0.899 | 0.388 | 0.785 | 0.227 | 0.157 |
| 10 | 1.35 | 0.707 | 1.209 | 0.502 | 0.121 |
| 20 | 2.24 | 1.32 | 1.314 | 1.13 | 0.066 |
| 30 | 3.13 | 1.95 | 1.343 | 1.73 | 0.045 |
| 40 | 3.94 | 2.53 | 1.269 | 2.30 | 0.032 |
| 50 | 4.90 | 3.19 | 1.380 | 2.96 | 0.028 |
| 100 | 9.14 | 6.28 | 1.528 | 6.04 | 0.015 |
| 200 | 17.8 | 12.5 | 1.708 | 12.2 | 0.009 |

BN254 with Pallas:

| $\ell$ | client blind | issuer sign | client verify | client unmask | verify, per token |
|---|---|---|---|---|---|
| 1 | 0.443 | 0.141 | 0.433 | 0.047 | 0.433 |
| 5 | 0.846 | 0.388 | 0.764 | 0.227 | 0.153 |
| 10 | 1.29 | 0.694 | 1.254 | 0.492 | 0.125 |
| 20 | 2.17 | 1.30 | 1.382 | 1.12 | 0.069 |
| 30 | 3.00 | 1.93 | 1.377 | 1.76 | 0.046 |
| 40 | 3.91 | 2.49 | 1.305 | 2.35 | 0.033 |
| 50 | 4.74 | 3.15 | 1.319 | 2.94 | 0.026 |
| 100 | 8.96 | 6.13 | 1.513 | 6.09 | 0.015 |
| 200 | 17.7 | 12.4 | 1.675 | 12.2 | 0.008 |

**The paper reports 60.72 ms for this step at $\ell = 100$ against 2.05 here, a factor of thirty.**
That matters because it is the wallet-visible latency of buying tokens, and it is available without
any protocol change: the whole win is that the two repeated $G_2$ elements are recognized as
repeated. Verification has stopped being the client's bottleneck. Blinding is, at 17.0 ms, and
unmasking is next at 10.3 against 2.05.

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
| BLS12-381 / Ed25519 | 0.132 ms | 0.077 ms |
| BLS12-381 / Pallas | 0.082 ms | 0.077 ms |
| BN254 / Ed25519 | 0.102 ms | 0.045 ms |
| BN254 / Pallas | 0.050 ms | 0.046 ms |

Ed25519's subgroup check costs about 0.05 ms more than Pallas's, which is the whole difference.

The issuer's message is one check $k . pk_{iss} == com_k$ in $G_2$. An issuer settling $m$ of its own
sessions in one extrinsic pays the $m$ row; $m = 1$ is one session per extrinsic. Batching does not
cross extrinsics here either, so a rejected batch is chargeable to the issuer that submitted it. The
check touches no `DS` key, so it depends only on the pairing curve; the two `DS` columns agree to
within a percent everywhere and only one is given.

BLS12-381, milliseconds:

| $m$ | $J$ keys | fixed-base cold | fixed-base warm | RMC |
|---|---|---|---|---|
| 1 | 1 | 0.627 | 0.074 | 0.420 |
| 5 | 1 | 0.720 | 0.168 | 0.678 |
| 10 | 1 | 0.759 | 0.179 | 0.845 |
| 20 | 1 | 0.857 | 0.298 | 0.958 |
| 50 | 1 | 1.07 | 0.449 | 1.29 |
| 100 | 1 | 1.31 | 0.697 | 1.66 |
| 200 | 1 | 1.95 | 1.24 | 2.20 |
| 1000 | 1 | 5.54 | 4.34 | 6.93 |
| 100 | 10 | 8.02 | 2.09 | 1.74 |

BN254:

| $m$ | $J$ keys | fixed-base cold | fixed-base warm | RMC |
|---|---|---|---|---|
| 1 | 1 | 0.409 | 0.034 | 0.235 |
| 5 | 1 | 0.489 | 0.104 | 0.384 |
| 10 | 1 | 0.537 | 0.138 | 0.623 |
| 20 | 1 | 0.528 | 0.157 | 0.761 |
| 50 | 1 | 0.670 | 0.261 | 0.835 |
| 100 | 1 | 0.900 | 0.488 | 1.09 |
| 200 | 1 | 1.30 | 1.03 | 1.59 |
| 1000 | 1 | 4.15 | 2.68 | 4.21 |
| 100 | 10 | 6.53 | 1.46 | 1.27 |

A `BatchMulPreprocessing` window table on $pk_{iss}$ wins at every $m$ on one key: 0.074 ms against
the checker's 0.420 at $m = 1$, a factor of six, and still ahead at $m = 1000$, 4.34 ms against 6.93
on BLS12-381 (2.68 against 4.21 on BN254). But the table is per key: at $J = 10$ it fragments into ten
tables of a tenth the scalars each and loses to the checker, 2.09 ms against 1.74 at $m = 100$. And
cold it is a loss, 0.627 ms at $m = 1$ against the warm 0.074, so it only pays as a warm cache.

If issuers settle one session per extrinsic, which is the attribution-preserving default, $m = 1$ is
the only row that matters and the warm table wins six to one. It is a cache on long-lived registry
state, so invalidation on register and retire becomes a pallet obligation. The checker needs no cache
and wins only when reveals span many keys. Under denomination pools an honest issuer holds $D$ keys
rather than one, which pushes any batching towards the $J = 10$ column where the checker is ahead.

The checker is a locally randomized check, not Fiat-Shamir. Each node draws its own randomness and
never reveals it, so nothing is aimable at a node's coin, an honest batch passes for every draw and a
dishonest one fails except with probability $m/p$. Two obligations follow and both belong to the
pallet. Consensus needs that divergence probability argued rather than assumed. And a failing batch
names no culprit within the extrinsic, so rejection has to fall back to per-item checking to
attribute the failure, which is a liveness and attribution requirement rather than a soundness one.

### Spend, on chain

$n$ tokens across $J$ issuer keys fold into one multi-pairing of $1 + J$ pairs. Hash-to-curve,
nullifier distinctness and the batch `DS` verify all stay per payment. The chain column is the whole
check: hash-to-curve plus nullifier distinctness plus the pairing plus the batch `DS` verify, so the
hash-to-curve and DS-batch columns are components of it rather than addends. `DS` is always verified;
the batch signature is not a Substrate extrinsic signature, so a custom transaction extension checks
it whichever curve it lives on (see *Client signature group*).

The $J$ column is the denomination question in disguise. Under pools a payment spending $d$ distinct
denominations has $J = d$, so the $J = n$ rows are what a multi-denomination fee actually costs.

BLS12-381 with Ed25519, milliseconds:

| $n$ | $J$ | hash-to-curve | DS batch | chain | per token |
|---|---|---|---|---|---|
| 1 | 1 | 0.054 | 0.176 | 1.041 | 1.041 |
| 4 | 1 | 0.218 | 0.265 | 1.489 | 0.372 |
| 4 | 4 | 0.217 | 0.259 | 1.874 | 0.469 |
| 8 | 1 | 0.434 | 0.568 | 2.516 | 0.315 |
| 16 | 1 | 0.873 | 0.579 | 3.178 | 0.199 |
| 16 | 16 | 0.874 | 0.549 | 4.302 | 0.269 |
| 64 | 1 | 3.66 | 0.734 | 6.315 | 0.099 |
| 128 | 1 | 7.30 | 0.894 | 10.4 | 0.082 |
| 512 | 1 | 29.5 | 1.59 | 34.7 | 0.068 |
| 512 | 64 | 29.7 | 1.58 | 60.1 | 0.117 |

BLS12-381 with Pallas:

| $n$ | $J$ | hash-to-curve | DS batch | chain | per token |
|---|---|---|---|---|---|
| 1 | 1 | 0.055 | 0.032 | 0.854 | 0.854 |
| 4 | 1 | 0.213 | 0.057 | 1.323 | 0.331 |
| 4 | 4 | 0.217 | 0.056 | 1.713 | 0.428 |
| 8 | 1 | 0.434 | 0.089 | 1.956 | 0.245 |
| 16 | 1 | 0.874 | 0.153 | 2.599 | 0.162 |
| 16 | 16 | 0.875 | 0.153 | 3.925 | 0.245 |
| 64 | 1 | 3.71 | 0.615 | 6.266 | 0.098 |
| 128 | 1 | 7.46 | 0.738 | 10.4 | 0.081 |
| 512 | 1 | 29.7 | 1.32 | 34.8 | 0.068 |
| 512 | 64 | 29.6 | 1.44 | 58.4 | 0.114 |

BN254 with Ed25519:

| $n$ | $J$ | hash-to-curve | DS batch | chain | per token |
|---|---|---|---|---|---|
| 1 | 1 | 0.024 | 0.174 | 0.753 | 0.753 |
| 4 | 1 | 0.085 | 0.256 | 1.115 | 0.279 |
| 4 | 4 | 0.080 | 0.258 | 1.445 | 0.361 |
| 8 | 1 | 0.149 | 0.591 | 2.008 | 0.251 |
| 16 | 1 | 0.363 | 0.589 | 2.331 | 0.146 |
| 16 | 16 | 0.346 | 0.549 | 3.191 | 0.199 |
| 64 | 1 | 1.46 | 0.727 | 3.655 | 0.057 |
| 128 | 1 | 2.99 | 0.908 | 5.496 | 0.043 |
| 512 | 1 | 11.9 | 1.54 | 15.9 | 0.031 |
| 512 | 64 | 12.1 | 3.26 | 41.0 | 0.080 |

BN254 with Pallas:

| $n$ | $J$ | hash-to-curve | DS batch | chain | per token |
|---|---|---|---|---|---|
| 1 | 1 | 0.020 | 0.032 | 0.879 | 0.879 |
| 4 | 1 | 0.099 | 0.055 | 0.947 | 0.237 |
| 4 | 4 | 0.076 | 0.057 | 1.223 | 0.306 |
| 8 | 1 | 0.176 | 0.089 | 1.399 | 0.175 |
| 16 | 1 | 0.391 | 0.152 | 1.723 | 0.108 |
| 16 | 16 | 0.340 | 0.151 | 2.587 | 0.162 |
| 64 | 1 | 1.51 | 0.711 | 3.688 | 0.058 |
| 128 | 1 | 3.09 | 0.890 | 5.571 | 0.044 |
| 512 | 1 | 11.8 | 1.37 | 15.9 | 0.031 |
| 512 | 64 | 12.1 | 1.40 | 39.9 | 0.078 |

Against the 3.508 ms verify of `FeeAccountPaymentProof` measured below, a single spend is 3.4x
cheaper on BLS12-381 and 4.7x on BN254. At $n = 512$ with one issuer the per-token figures are
0.068 and 0.031 ms, which is 52x and 113x. The order-of-magnitude claim in the paper's abstract
survives at scale, though the current mechanism's faster verify has shrunk the single-payment margin.

Batch Schnorr keeps the `DS` term small. At $n = 512$ it is 1.59 ms on Ed25519 and 1.32 on
Pallas, an `n + 1` MSM instead of the `2n + 1` points individual verification would need. On the
client side the effect is larger and shows up in the payment table below, where producing a spend is
one scalar mult regardless of $\ell$.

$J$ costs real time, and it is the cost denominations impose. At $n = 16$, going from one issuer key
to sixteen takes the batch from 3.18 to 4.30 ms on BLS12-381, because the multi-miller-loop goes
from 2 pairs to 17 and the $G_1$ side fragments from one MSM of 16 into sixteen of size 1.

Hash-to-curve is the term that does not batch, and on BLS12-381 it is now most of the cost: 29.5 ms
of a 34.7 ms check at $n = 512$. On BN254 it is 11.9 of 15.9, which is a larger share than before the
constant-time map went in.

### Client signature group

The paper uses Ed25519 for `DS`. Pallas is the obvious alternative here because DART already carries
it for the curve trees, so ephemeral keys on Pallas add no new curve to the verifier. Both are
measured throughout the tables above; neither is removed.

Sizes are identical. Both have 32-byte compressed points and 32-byte scalars, so the signature is
64 B and the token is 80 B on BLS12-381 and 64 B on BN254 either way.

| | Ed25519 | Pallas |
|---|---|---|
| keygen | 0.056 ms | 0.029 ms |
| sign | 0.056 | 0.029 |
| verify, single | 0.093 | 0.044 |
| batch, $n = 1$ | 0.176 | 0.032 |
| batch, $n = 512$ | 1.59 | 1.32 |
| $com_k$ + $pk_{ref}$ decode | 0.135 | 0.082 |
| sign a payment of any size | 0.057 | 0.030 |

Batching has made the choice nearly free either way: at $n = 512$ full chain verification is 34.7
against 34.8 ms on BLS12-381 and 15.9 against 15.9 on BN254. The largest remaining difference is the
$pk_{ref}$ subgroup check in Π-Execute, not $\gamma$.

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

Against that sits an interaction with the wire format, and batch Schnorr settles it in one direction.
A batch signature over $\ell$ one-time keys is not a signature under any one of them, so it cannot be
a Substrate extrinsic signature on either curve: `MultiSignature` has no such variant. So $\gamma$ is
never free as an extrinsic signature, and a custom transaction extension has to verify it whichever
curve it lives on. That was already the conclusion for Ed25519, since a fee token is spent by a fresh
one-time key with no account behind it, so nothing is lost — and it is why every chain figure in this
document includes the batch `DS` verify, on all four combinations, which removes the last argument for
preferring Ed25519.

### Against the current mechanism, at one denomination

The paper mints one unit per accepted spend, so a fee of $\ell$ base units costs $\ell$ tokens,
while the current mechanism pays any amount with a single proof. That makes the comparison a function of $\ell$
rather than a single ratio. Everything in this subsection is a single denomination. The two current
proofs BAT would replace, measured on the same machine in the same run, with SCALE sizes because
that is what goes on chain:

| | prove | verify | size |
|---|---|---|---|
| `FeeAccountTopupProof` | 51.7 ms | 3.683 ms | 4,655 B |
| `FeeAccountPaymentProof` | 50.6 ms | 3.508 ms | 4,787 B |

`FeeAccountRegistrationProof` is not measured. It has no BAT counterpart, since tokens are bearer
objects and no fee account is ever created, so it appears in neither column of the comparison.

Funding is the part BAT wins outright. A top-up moves any amount for one proof; BAT's issuance moves
$L$ tokens for two transactions that are $O(1)$ in $L$. On-chain time is flat in $L$, so one row per
combination at $L = 100$ carries it, with the full sweep in the run output:

| | client off chain | issuer off chain | chain, both transactions | on-chain bytes | vs top-up |
|---|---|---|---|---|---|
| BLS12-381 / Ed25519 | 29.9 ms | 10.8 ms | 0.553 ms | 228 B | 6.7x |
| BLS12-381 / Pallas | 29.2 | 10.8 | 0.515 | 228 | 7.2x |
| BN254 / Ed25519 | 17.3 | 6.28 | 0.412 | 196 | 8.9x |
| BN254 / Pallas | 17.2 | 6.45 | 0.321 | 196 | 11.5x |

Against 3.683 ms and 4,655 B for a top-up that is 6.7x to 11.5x in chain time and 20x on bytes, flat in
$L$, and the traffic that does scale with $L$ is off chain between client and issuer where it costs
the chain nothing. The `DS` group is worth 10 to 20 percent here because most of the on-chain cost is
the $pk_{ref}$ subgroup check. Both reveals go through the checker; on a block carrying a single
reveal the warm window table would cut those figures by about 0.36 ms, which roughly triples the
ratio but buys a cache.

Payment is where the single denomination bites. Ratios above 1 favour BAT.

BLS12-381 with Ed25519:

| fee amount $\ell$ | current client | BAT client | current chain | BAT chain | BAT bytes | chain | bytes |
|---|---|---|---|---|---|---|---|
| 1 | 50.6 ms | 0.058 ms | 3.508 ms | 1.040 ms | 144 | 3.37x | 33.2x |
| 5 | 50.6 | 0.057 | 3.508 | 1.616 | 464 | 2.17x | 10.3x |
| 10 | 50.6 | 0.057 | 3.508 | 2.800 | 864 | 1.25x | 5.54x |
| 20 | 50.6 | 0.060 | 3.508 | 3.680 | 1,664 | 0.95x | 2.88x |
| 30 | 50.6 | 0.059 | 3.508 | 4.320 | 2,464 | 0.81x | 1.94x |
| 40 | 50.6 | 0.060 | 3.508 | 4.757 | 3,264 | 0.74x | 1.47x |
| 50 | 50.6 | 0.062 | 3.508 | 5.514 | 4,064 | 0.64x | 1.18x |
| 100 | 50.6 | 0.067 | 3.508 | 8.868 | 8,064 | 0.40x | 0.59x |
| 200 | 50.6 | 0.075 | 3.508 | 15.2 | 16,064 | 0.23x | 0.30x |

BLS12-381 with Pallas:

| fee amount $\ell$ | BAT client | BAT chain | BAT bytes | chain | bytes |
|---|---|---|---|---|---|
| 1 | 0.030 ms | 0.838 ms | 144 | 4.19x | 33.2x |
| 5 | 0.030 | 1.463 | 464 | 2.40x | 10.3x |
| 10 | 0.032 | 2.401 | 864 | 1.46x | 5.54x |
| 20 | 0.032 | 3.873 | 1,664 | 0.91x | 2.88x |
| 30 | 0.033 | 4.044 | 2,464 | 0.87x | 1.94x |
| 40 | 0.033 | 4.540 | 3,264 | 0.77x | 1.47x |
| 50 | 0.035 | 6.190 | 4,064 | 0.57x | 1.18x |
| 100 | 0.042 | 10.5 | 8,064 | 0.33x | 0.59x |
| 200 | 0.052 | 15.5 | 16,064 | 0.23x | 0.30x |

BN254 with Ed25519:

| fee amount $\ell$ | BAT client | BAT chain | BAT bytes | chain | bytes |
|---|---|---|---|---|---|
| 1 | 0.059 ms | 0.835 ms | 128 | 4.20x | 37.4x |
| 5 | 0.059 | 1.289 | 384 | 2.72x | 12.5x |
| 10 | 0.062 | 2.272 | 704 | 1.54x | 6.80x |
| 20 | 0.060 | 2.831 | 1,344 | 1.24x | 3.56x |
| 30 | 0.060 | 3.037 | 1,984 | 1.16x | 2.41x |
| 40 | 0.064 | 3.097 | 2,624 | 1.13x | 1.82x |
| 50 | 0.062 | 3.425 | 3,264 | 1.02x | 1.47x |
| 100 | 0.065 | 5.113 | 6,464 | 0.69x | 0.74x |
| 200 | 0.074 | 7.808 | 12,864 | 0.45x | 0.37x |

BN254 with Pallas:

| fee amount $\ell$ | BAT client | BAT chain | BAT bytes | chain | bytes |
|---|---|---|---|---|---|
| 1 | 0.031 ms | 0.608 ms | 128 | 5.77x | 37.4x |
| 5 | 0.031 | 0.985 | 384 | 3.56x | 12.5x |
| 10 | 0.031 | 1.741 | 704 | 2.02x | 6.80x |
| 20 | 0.032 | 2.156 | 1,344 | 1.63x | 3.56x |
| 30 | 0.034 | 2.668 | 1,984 | 1.31x | 2.41x |
| 40 | 0.034 | 3.032 | 2,624 | 1.16x | 1.82x |
| 50 | 0.035 | 3.464 | 3,264 | 1.01x | 1.47x |
| 100 | 0.038 | 4.804 | 6,464 | 0.73x | 0.74x |
| 200 | 0.048 | 8.075 | 12,864 | 0.43x | 0.37x |

The crossovers are set by the pairing curve alone, and batch Schnorr has moved the byte ones a long
way, because it took 64 of the 144 bytes out of every token and put one 64-byte signature on the
payment instead.

The faster current-mechanism verify (3.5 ms, down from 5.7 in an earlier arkworks build) pulls the
chain crossovers in sharply. On BLS12-381 chain time crosses at $\ell \approx 18$, going 1.25x at 10
to 0.95x at 20, while bytes cross at $(4787-64)/80 = 59$; chain binds first. On BN254 chain crosses at
$\ell \approx 52$, going 1.02x at 50 to 0.69x at 100, and bytes at $(4787-64)/64 = 74$; chain binds
first there too.

So BAT at one denomination beats the current mechanism for small fees, 3.4x to 5.8x on chain time and
33x to 37x on bytes at $\ell = 1$, and now holds only to about 18 base units on BLS12-381 and about 52
on BN254. The order-of-magnitude claim is real but it is a claim about a one-unit payment, and once
the fee proofs verify in 3.5 ms the window where BAT is cheaper on chain has narrowed to small fees.

Client cost is no longer a function of $\ell$ at all. Producing a payment is one batch signature,
0.057 ms on Ed25519 and 0.030 on Pallas whether it spends one token or two hundred, against 50.6 ms
for one curve-tree proof plus a Bulletproofs range proof. Charging the amortized issuance in as well
at a hundred tokens per purchase:

| | per token, issuance | per payment, signing | total per payment | crosses 50.6 ms at |
|---|---|---|---|---|
| BLS12-381 / Ed25519 | 0.299 ms | 0.057 ms | $0.299\ell + 0.06$ | $\ell = 169$ |
| BLS12-381 / Pallas | 0.292 | 0.030 | $0.292\ell + 0.03$ | $\ell = 173$ |
| BN254 / Ed25519 | 0.173 | 0.056 | $0.173\ell + 0.06$ | $\ell = 293$ |
| BN254 / Pallas | 0.172 | 0.030 | $0.172\ell + 0.03$ | $\ell = 294$ |

The device and the wallet are comfortably better off under BAT across the whole realistic range even
where the chain is not, and the margin is now set entirely by issuance rather than by spending.

**This is what makes denominations a precondition rather than an optimization.** Every number above
is for one denomination, one unit per token. The next subsection prices the only denomination scheme
that fits BAT's token shape.

### Against the current mechanism, with denominations

A set of $D$ powers of two covers every fee up to $2^D - 1$. The worst case is all $D$ bits set, so
$D$ tokens; the average over uniformly drawn fees is $D/2$. The scheme is the paper's §8 pools, one
issuer key per denomination, which makes a payment spending $d$ denominations a spend over $d$ issuer
keys. `DS` is included, one batch signature per payment under any scheme. Ratios above 1
favour BAT.

BLS12-381 with Ed25519:

| $D$ | largest fee | worst case, $D$ tokens | average case, $D/2$ | worst vs current | average vs current | bytes, worst |
|---|---|---|---|---|---|---|
| 8 | 255 | 3.152 ms | 1.936 ms | 1.20x | 1.95x | 704 B |
| 16 | 65,535 | 4.410 | 3.018 | 0.86x | 1.25x | 1,344 |
| 24 | 16.8M | 5.721 | 3.995 | 0.66x | 0.95x | 1,984 |
| 32 | 4.29G | 6.832 | 4.381 | 0.55x | 0.86x | 2,624 |
| 48 | 2.81e14 | 9.387 | 5.660 | 0.40x | 0.67x | 3,904 |
| 64 | 1.84e19 | 11.9 | 6.995 | 0.32x | 0.54x | 5,184 |

BLS12-381 with Pallas:

| $D$ | worst case, $D$ tokens | average case, $D/2$ | worst vs current | average vs current |
|---|---|---|---|---|
| 8 | 2.656 ms | 1.784 ms | 1.42x | 2.12x |
| 16 | 3.904 | 2.495 | 0.97x | 1.52x |
| 24 | 5.102 | 3.275 | 0.74x | 1.16x |
| 32 | 6.484 | 3.837 | 0.58x | 0.99x |
| 48 | 9.221 | 5.231 | 0.41x | 0.72x |
| 64 | 11.8 | 6.437 | 0.32x | 0.59x |

BN254 with Ed25519:

| $D$ | worst case, $D$ tokens | average case, $D/2$ | worst vs current | average vs current | bytes, worst |
|---|---|---|---|---|---|
| 8 | 2.400 ms | 1.428 ms | 1.58x | 2.65x | 576 B |
| 16 | 3.209 | 2.377 | 1.18x | 1.59x | 1,088 |
| 24 | 4.011 | 2.979 | 0.94x | 1.27x | 1,600 |
| 32 | 4.829 | 3.200 | 0.78x | 1.18x | 2,112 |
| 48 | 6.496 | 4.092 | 0.58x | 0.92x | 3,136 |
| 64 | 7.854 | 4.840 | 0.48x | 0.78x | 4,160 |

BN254 with Pallas:

| $D$ | worst case, $D$ tokens | average case, $D/2$ | worst vs current | average vs current |
|---|---|---|---|---|
| 8 | 1.812 ms | 1.248 ms | 2.09x | 3.03x |
| 16 | 2.686 | 1.826 | 1.41x | 2.07x |
| 24 | 3.632 | 2.317 | 1.04x | 1.63x |
| 32 | 4.369 | 2.727 | 0.87x | 1.39x |
| 48 | 6.433 | 3.601 | 0.59x | 1.05x |
| 64 | 7.912 | 4.503 | 0.48x | 0.84x |

The choice of `DS` group barely moves these, since its batch signature is one per payment either way,
and the byte columns depend only on the pairing curve: a pool token is the paper's token minus its
signature, since the issuer index the payload already carries names the denomination.

**Pools still do not clear the current mechanism at a realistic denomination set, and the faster fee
proofs have pulled the crossings in.** In the worst case they fall below it at $D = 16$ on BLS12-381
and $D = 24$ on BN254; in the average case at $D = 24$ on BLS12-381 and $D = 48$ on BN254.
Polymesh needs $D$ in the 20 to 30 range, with six decimals putting one POLYX at $10^6$ base units
and a thousand at $10^9$. Over that range pools run at 0.66x to 0.55x worst case and 0.95x to 0.86x
average case on BLS12-381, and 0.94x to 0.78x worst and 1.27x to 1.18x average on BN254.

So on BLS12-381 the mechanism is slower than the one it would replace in the worst case from $D = 16$
up, and on BN254 the worst case dips below at $D = 24$. Bytes are comfortably favourable throughout,
2,624 B against 4,787 at $D = 32$ on BLS12-381 and 2,112 on BN254, so payload is not what binds;
verification is.

Two things drive the cost, and both are structural rather than implementation slack. Each denomination
is a distinct $G_2$ element, so a $d$-denomination payment is a $1 + d$ pair multi-pairing instead of
two pairs. And the $G_1$ side fragments with it: the checker groups by $G_2$ element, so $d$ keys give
$d$ MSMs of size 1 where one key gives a single MSM of size $d$, which is where the batching that
makes the single-denomination numbers good is lost. Comparing the $J = 1$ and $J = n$ rows of the
spend tables isolates it: at $n = 16$ on BLS12-381, 3.18 ms against 4.30.

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
| 1 | 1.058 | 0.885 | 0.765 | 0.477 | 176 B |
| 10 | 2.983 | 2.187 | 1.601 | 1.497 | 896 B |
| 30 | 4.774 | 3.627 | 2.203 | 2.091 | 2,496 B |
| 40 | 4.375 | 4.033 | 2.353 | 2.233 | 3,296 B |
| 50 | 4.957 | 4.787 | 2.781 | 2.620 | 4,096 B |
| 100 | 8.162 | 8.116 | 4.017 | 3.865 | 8,096 B |
| 200 | 14.5 | 14.4 | 6.696 | 6.756 | 16,096 B |

Refund keeps the single-signature form, since it already authorizes its batch with one signature
under $sk_{ref}$ and has nothing to gain from the batch protocol. The `DS` group is worth almost
nothing here; the client side is where it shows, 0.110 ms against 0.068 to sign a 200-token refund
request, and neither is a cost worth optimizing. Under pools a refund batch spans $d$ issuer keys, so
the $J = 1$ shape above is the single-denomination case and a real refund pays the same $1 + d$ pairs
a spend does.

This puts a number on the collective-refund congestion gap. At $\ell_{ref} = 100$ a node spends
8.16 ms on BLS12-381 or 3.87 on BN254 per refunding client. Give refunds 500 ms of a block's
execution budget and that is 61 clients per block on BLS12-381, 129 on BN254. Over a $T_{grace}$ of
half an hour at six-second blocks, roughly $1.8 \times 10^4$ and $3.9 \times 10^4$ clients. That is
the per-issuer client cap the paper never derives, and it is one to two orders of magnitude better
than the paper's Ethereum figures, where gas is dominated by storage rather than arithmetic.

The comparison is not decided by this, because the estimate excludes nullifier writes, which are
$\ell_{ref}$ trie insertions per client and are very likely to dominate on Substrate exactly as they
do on Ethereum. What the measurement establishes is that the pairing arithmetic is not the binding
constraint once grouped, so the cap should be derived from storage and payload, and the spike for
it is a runtime benchmark of the nullifier insert rather than anything cryptographic.

