We are working in a 2-cycle EC groups $G_p$ and $G_q$.

$|G_p| = p$, $|G_q| = q$

Coordinates of $|G_p|$ are in $Z_q$ and coordinates of $|G_q|$ are in $Z_p$

Following are the group generators (curve points)

$g, g_i \in G_p$

$h, h_i, j, k \in G_q$

Keys
$$
pk_e = h * sk_e \\
pk_a = h * sk_a \\
pk_s = h * sk_s \\
pk_r = h * sk_r \\
$$

$pk_e$ is the ephemeral key freshly created for each settlement 

The public keys are curve points and notation $.x$ and $.y$ refers to their $x$ and $y$ coordinates. Eg, ${pk_s}.x$ refers to $x$ coordinate of public key $pk_s$.

$pk_s, pk_r, pk_a \in G_q$

$sk_s,sk_r, sk_a \in Z_q$

$pk_e \in G_q$, $sk_e \in Z_q$

${pk_s}.x, {pk_s}.y, {pk_r}.x, ... \in Z_p$

${pk_e}.x, {pk_e}.y \in Z_p$

Leg
$$
leg = (pk_s, pk_r, pk_a, v, at)
$$

Commitment to leg
$$
Com_{leg} = g_1 * {pk_s}.x + g_2 * {pk_s}.y + g_3 * {pk_r}.x + g_4 * {pk_r}.y + g_5 * {pk_a}.x + g_6 * {pk_a}.y + g_7 * v + g_8 * at + g_9 * r_0
$$

where $Com_{leg} \in G_p$


Venue commits to $leg$ as commitment $Com_{leg}$ and encrypts (using verifiable encryption from TZ21) $leg$ with $pk_e$ leading to the ciphertext and proof that the ciphertext is decryptable by $pk_e$ and is consistent with commitment $Com_{leg}$. 

$Com_{leg}$ should commit to auditor public key $pk_A$ since during auditor's approve/reject it has to prove that its $pk_a$ was part of the leg. And thats the only thing auditor proves for an **un-executed** txn.

For the Curve Tree used for auditor, the tree leaf is a non-hiding commitment to the auditor public key and asset type.

$$
Leaf = g1 * pk_a.x + g2 * pk_a.y + g3 * at
$$

Chain verifies the commitment and proof and sender/receiver/auditor get $sk_e$ from their respective $\alpha$

Account commitment

$$
Com_{account} = h_1 * sk_s + h_2 * bal + h_3 * cnt + h_4 * at + h_5 * \rho + h_6 * s
$$

Rerandomized account commitment created during curve tree proof

$$
Com_{account_r} = h_1 * sk_s + h_2 * bal + h_3 * cnt + h_4 * at + h_5 * \rho + h_6 * s + j * blinding
$$

where $Com_{account}, Com_{account_r} \in G_q$

For send/receive txn, the strategy is to commit to coordiantes of sender/receiver pk from $leg$ and use CDLS's protocol for scalar multiplication to prove the secret key in account (re-randomized) commitment is consistent with public key in $leg$. Eg. for send txn

Commit to sender public key $pk_s$ = ($pk_s.x$, $pk_s.y$) as 

$$
X = g_{10} * pk_s.x + g_{11} * r_1 \\
Y = g_{10} * pk_s.y + g_{11} * r_2
$$

where $X, Y \in G_p$

Commit to sender secret key $sk_s$ as $S = h_{10} * sk_s + h_{11} * r_3$ and $S \in G_q$

Prove equality of $sk_s$ in $S$ and $Com_{account_r}$ and equality of ${pk_s}.x$ in $X$ and $Com_{leg}$ and equality of ${pk_s}.y$ in $Y$ and $Com_{leg}$ using Schnorr protocol. Now we can use CDLS to prove that $sk_s * h = pk_s$ given commitments $X, Y, S$.


Nullifier $nul$: 

$$nul = DY_{PRF}(sk_s, \rho) = k * (sk_s + \rho)^{-1}$$

For proving correctness of $nul$, prove knowledge of $sk_s$ and $\rho$ in relation $nul * sk_s + nul * \rho = k$ and also the equality of $sk_s, \rho$ with the ones in commitment $Com_{account_r}$

-----------------



$$
\alpha_{A_1} = pk^{r_A} . h^{q_A} \\

leaf = pk . g^{at} \\

leaf_{rand} = pk . g^{at} . h^{u} \\

(C_1, C_2) = (g^r, W^r . pk) \\

pk = C_2 . W^{-r}
$$

Have to prove:

$$
\alpha_{A_1} = (C_2 . W^{-r})^{r_A} . h^{q_A} 

= C_2^{r_A} . W^{-r.r_A} . h^{q_A} \\
$$

and

$$
leaf_{rand} = (C_2 . W^{-r}) . g^{at} . h^{u}
$$

Also prove the following to establish product relation 
$$
leaf_{rand}^{r_A} = C_2^{r_A} . W^{-r.r_A} . g^{at.r_A} . h^{u.r_A} 
= \alpha_{A_1} . g^{at.r_A} . h^{u.r_A - q_A}
 
$$

Prove the above 3 relations where $leaf_{rand}, \alpha_{A_1}, C_2, W, g, h$ are instance and $r, r_A, q_A, at, u$ are witness.

---------------------

Prove the knowledge of committed values given 2 commitments $C_1 = g^x h^{r_1}, C_2 = g^{x+v} h^{r_2}$ and that $v$ is public

One solution is to transform $C_2$ into $C_2'$ as $C_2' = C_2 * g^{-v} = g^x h^{r_2}$ and now use sigma protocol with $C_1, C_2'$ and choose the same blinding for $x$ in first step of sigma protocol.

The other is to still choose the same blinding for $x$ and $x+v$ in in first step of sigma protocol but run the sigma protocol with $C_1, C_2$ instead. The verifier calculates the response for second relation using the first one. Protocol below

1. Prover picks random $k_1, k_2, k_3$ and calculates $t_1 = g^{k_1}, t_2 = h^{k_2}, t_3 = h^{k_3}$
2. Prover creates challenge $c = Hash(C_1, C_2, g, h, t_1, t_2, t_3)$
3. Prover creates responses $s_1 = k_1 + x.c, s_2 = k_2 + r_1.c, s_3 = k_3 + r_2.c$ and sends $t_i, s_i$ to verifier.
4. Verifier computes response for checking relation for $C_2$, $s$ as $s = s_1 + v.c$
5. Verifier checks

   $$
   g^{s_1} h^{s_2} == t_1 t_2 C_1 \\
   g^{s} h^{s_3} == t_1 t_3 C_2 \\
   $$

Another is to use sigma protocol over the realtion $C_2 g^{-v} C_1^{-1} = h^{r_2 - r_1}$. Here there is only 1 commitment to randomness ($t$) and 1 response ($s$).

-------------------

For proving that sum of amounts in many legs equals a public value.

A leg encryption contains 4 ciphertexts, the one for amount is of the form $(g^r, pk_e^r.h^v)$ where $v$ is the amount and $pk_e$ is the ephemeral public key. Call this pair $(g^r, pk_e^r.h^v)$ as $(C, D)$. Now given $n$ such pairs $(C_1, D_1), (C_2, D_2), ... (C_n, D_n)$ where $(C_i, D_i) = (g^{r_i}, {pk_e}_i^{r_i}.h^{v_i})$, prove $\sum_i{v_i} = V$ where $V$ is public.

$$
\prod_i{D_i} = \prod_i{{pk_e}_i^{r_i}}.h^V
$$

Since ${pk_e}_i = g^{sk_i}$, above relation can be written as 
 
$$ 
\prod_i{D_i}.h^{-V} = \prod_i{C_i^{sk_i}} 
$$

Now $g, h, V, C_i, D_i$ are public and knowledge of $sk_i$ can be proven using sigma protocol.

---------------------------



$$ g * v_0 + g_1 * v_1  $$

$$

pk_e = g * sk_e \\

(g*r, pk_e*r + pk_s)

sk_s * g == pk_s \\

g * r', w * r' + pk_s \\

g * r' = C_1 \\
w * r' + pk_s = C_2 \\

C_2 - w * r' = pk_s \\

C_2 - w * r' = g * sk_s

$$



