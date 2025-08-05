We are working in a 2-cycle EC groups $G_p$ and $G_q$.

$|G_p| = p$, $|G_q| = q$

Coordinates of $|G_p|$ are in $Z_q$ and coordinates of $|G_q|$ are in $Z_p$

Following are the group generators (curve points)

$g, g_i \in G_p$

$h, h_i, j, k \in G_q$

Keys
$$
pk_e = h * sk_e \\\
pk_a = h * sk_a \\\
pk_s = h * sk_s \\\
pk_r = h * sk_r \\\
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
Leaf = g_1 * pk_a.x + g_2 * pk_a.y + g_3 * at
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

**New construction for supporting auditor and mediator**

$pk_a, pk_m$ are auditor's encryption and mediator's public key respectively 

$leaf' = pk_a.h^{at}$

Auditor tree leaf is $ Leaf = pk_a.pk_m.h^{at}$ (This probably isnt correct as its a commitment to $pk_a.pk_m$ and not to each of them individually)

Ephemeral secret key encryption

$X_s = pk_s^k, X_r = pk_r^k, X_a = pk_a^k, X_m = pk_m^k, Y = g^k.h^m$

$Z = Y - X_s^{sk_s} = Y - X_r^{sk_r} = Y - X_a^{sk_a} = Y - X_a^{sk_m} = h^m$

Ephemeral keypair $sk_e = Hash(Z), pk_e = g^{sk_e}$ 

Leg encryption corresponding to mediator $(g^r, pk_e^r.pk_m)$

Elgamal commitments to $pk_a, pk_m$ as $Com_{pk_a} = (g^{r_1}, W^{r_1}.pk_a) = (E_0, E_1)$ and $Com_{pk_m} = (g^{r_2}, W^{r_2}.pk_m) = (F_0, F_1)$ where W is a random group element whose discrete log with other group elements is not known.

Now $pk_a = E_1.W^{-r_1}$ and $pk_m = F_1.W^{-r_2}$.

Substituting for $pk_m$, we get $Leaf = pk_a.F_1.W^{-r_2}.h^a$. Now $pk_a = Leaf.F_1^{-1}.W^{r_2}.h^{-a}$.   
Similarly $pk_m = Leaf.E_1^{-1}.W^{r_1}.h^{-a}$.


-------------------------------------------


$g, pk_a, pk_m \in G_q, sk_a \in Z_q$

$pk_a = g^{sk_a}$

$pk_a = (pk_a.x, pk_a.y)$

$pk_m = (pk_m.x, pk_m.y)$

$pk_a.x, pk_a.y, pk_m.x, pk_m.y \in Z_p$

$Leaf = PedCom_{NH}(pk_a.x, pk_a.y, pk_m.x, pk_m.y, at)$

$Leaf \in G_p$

$X_a = pk_a^k$, $X_a \in G_q$

$X_a^{k^{-1}} = pk_a$


1. CDLS allows to prove $j.s = u$ given commitment to $j$'s, $s$'s, and $u$'s coordinates.

2. CDLS allows to prove $j^t = y$ given commitment to $y$'s coordinates and commitment to $t$.


Mediator in Leg: $(g^r, pk_e^r.pk_m)$


$T = pk_e^r.pk_m$, $T.pk_e^{-r} = pk_m$

Now use CDLS's sum of points and scalar multiplication protocol to prove $T.pk_e^{-r} = pk_m$. 
First scalar mult. protocol to prove $pk_e^{-r} = J$. Now use the sum protocol to prove $T.J = pk_m$

--------------------------------

Twisted Elgamal ciphertext for auditor $(X_A = pk_A^k, Y = g^k.h^m)$

$j_0, j_1, j_2, j_3, B$ are public generators

In case of auditor
   
- Leaf $leaf = j_1^{at}.pk_A$ (role is 0 here)

- Rerandomized leaf $leaf_r = j_1^{at}.pk_A.B^t$
 

$leaf_r.j_1^{-at}.B^{-t} = pk_A$

Substituting for $pk_A$ in $X_A$ above

$(leaf_r.j_1^{-at}.B^{-t}) ^ k = X_A$

Need to prove relation: $leaf_r^k.(j_1^{-1})^{at.k}.B^{-t.k} = X_A$

The idea is to create 3 elements as $K_1 = j_2^k.j_3^{r_k}, K_2 = j_2^{at}.j_3^{r_{at}}, K_3 = j_2^{at.k}.j_3^{at.r_k}$, 
prove the product relation between these 3 while proving that exponent of $j_2$ in $K_3$ is same as 
the exponent of $j_1^{-1}$ in $X_A$, the exponent of $j_2$ in $K_1$ is same as the exponent of $leaf_r$ in $X_A$ and similarly 
for $at$.   
Note that $K_3$ is intentionally created as $K_1^{at}$ for efficiency.

So the 5 relations that need to be proven (for auditor only)
1. $leaf_r^k.(j_1^{-1})^{at.k}.B^{-t.k} = X_A$
2. $K_1 = j_2^k.j_3^{r_k}$
3. $K_2 = j_2^{at}.j_3^{r_{at}}$
4. $K_3 = j_2^{at.k}.j_3^{at.r_k}$
5. $K_3 = K_1^{at}$



--------------------


**Proposal for multiple auditors/mediators**

Leaf for asset metadata: $leaf_{at} = j_0^{at}.j_1^{auditor-count}.j_2^{mediator-count}$

Leaf for the $i$-th auditor/mediator: $leaf_{at_i} = j_0^{at}.j_1^{role}.j_2^{i}.j_3^{pk}$ ($i$ can probably be removed but there might be cases where auditor/mediator needs to prove that each $i$ is different in zero-knowledge)


Assume single auditor/mediator for now whose public key is $pk_A$. Sender and receiver keys are $pk_s, pk_r$ respectively. 


Leg encryption:

1. Create random $r_1, r_2, r_3, r_4$ (Created with DH with sender and receiver public keys, described later).
2. Now venue uses twisted DH for encrypting leg - 
   1. $D_{s_i} = {pk_s}^{r_i}$, $D_{r_i} = {pk_r}^{r_i}$, $D_{A_i} = {pk_A}^{r_i}$.
   2. $C_s =g^{r_1}.pk_s$, $C_r =g^{r_2}.pk_r$, $C_v =g^{r_3}.h^v$, $C_{at} =g^{r_4}.h^{at}$ 
3. Venue proves that $pk_A$ in each $D_{A_i}$ is correct for the asset type in $C_{at}$ when asset has auditor. For mediator, proving for single is sufficient. (more on what do when multiple later). Both of these involve membership proofs in accumulator as well.

Decryption follows from the usual twisted Elgamal decryption.

Venue picks random $y$ and adds these to txn: $F_s = pk_s^y, F_r = pk_r^y$. Sender and receiver now create $r_i = Hash(g^y || i)$. 

Scan alg: As sender can receiver can learn what $at$ is without knowing auditor key, they first learn $at$ and then query chain for that $at$'s auditor/mediator public keys.Auditor/mediator use $D_{A_4}, C{at}$ to learn if settlement involves them.

Sender and receiver during their affirmations prove the knowledge of secret key in $C_s, C_r$ respectively.

Mediator while accepting/rejecting proves that $(C_{at}.h^{-at})^{sk_A} = D_{A_4}$, since $C_{at}.h^{-at} = g^{r_4}$


In case of say $n$ mediators/auditors, venue will create $n$ $D_{A_i}$ such as for the $j$-th mediator/auditor, the $j$-th $D_{A_i}$ = $D_{A_{j, i}} = {pk_{A_j}}^{r_i}$. Venue will prove correctness of all $D_{A_{j, 4}}$ for $j$ mediators. In case of say $n$ auditors, venue has to prove correctness of $D_{A_{j, i}}$ for all $i, j$. Both of these involve membership proofs in accumulator as well and since we have many membership proofs, we can batch them.

$j$-th mediator will prove the correctness of $D_{A_{j, 4}}$ during accepting/rejecting as above. It will also point to the $D_{A_{j, 4}}$ its proving about so chain can track how many mediators have approved. The exact strategy might change depending on how many mediators need to accept/reject when multiple mediators. An optimization for scan alg. is to always palce $D_{A_{j, i}}$ in the order of $j$ like $D_{A_{0, i}}$, $D_{A_{1, i}}$, ... so that auditor/mediator knows which $D_{A_{j, i}}$ to try. This is done by venue proving this using the index field $i$ in the lesf.

We can also handle cases when asset has both say $n$ auditors and $m$ mediators by similar strategy as above.

-------------------------------

Leaf $leaf = j_0^{at}.j_1^{role}.j_2^{index}.j_3^{pk.x}.j_4^{pk.y}$


--------------------------------------------------


$pk_A$ in terms of randomized leaf: $pk_A = leaf_r.j_1^{-at}.B^{-t}$

Need to prove 4 relations: $D_{A_1} = {pk_A}^{r_1}$, $D_{A_2} = {pk_A}^{r_2}$, $D_{A_3} = {pk_A}^{r_3}$, $D_{A_4} = {pk_A}^{r_4}$

Prover picks a random value $u_1$ by hashing the proof transcript and set $u_2 = u^2, u_3 = u^3$. Both prover and verifier generate these independently. 

Now prover combines above 4 relations into 1 by using a random linear combination:

$D_{A_1}.{D_{A_2}}^{u_1}.{D_{A_3}}^{u_2}.{D_{A_4}}^{u_3} = {pk_A}^{r_1}.{pk_A}^{r_2.u_1}.{pk_A}^{r_3.u_2}.{pk_A}^{r_4.u_3}$

$D_{A_1}.{D_{A_2}}^{u_1}.{D_{A_3}}^{u_2}.{D_{A_4}}^{u_3} = {pk_A}^{r_1 + r_2.u_1 + r_3.u_2 + r_4.u_3}$

Let $z = r_1 + r_2.u_1 + r_3.u_2 + r_4.u_3$. 

Prover generates $T_1 = g^{u_1}, T_2 = g^{u_2}, T_3 = g^{u_3}$ where $g$ is a totally new generator and shares $g^z$

Both prover and verifier have: $D_{A_i}, T_i, g, u_i, leaf_r, j_1, B, g^z$ 

Prover's secret: $r_i, z, at, t, pk_A$

Need to prove these:

1. $D_{A_1}.{D_{A_2}}^{u_1}.{D_{A_3}}^{u_2}.{D_{A_4}}^{u_3} = (leaf_r.j_1^{-at}.B^{-t})^z = leaf_r^z.(j_1^{-1})^{at.z}.(B^{-1})^{t.z}$
2. $g^z = g^{r_1}.T_1^{r_2}.T_2^{r_3}.T_3^{r_4} \equiv g^{r_1}.T_1^{r_2}.T_2^{r_3}.T_3^{r_4}.(g^{-1})^z = 1$

For 1, the proving cost is 8G + 7F, 10M and verification cost is 16M

For 2, proving cost is G (for $g^z$) + G + 4F, 5M, verification cost is 5M (not 6M because 1 in RHS)

Total proving cost is 10G + 11F, 15M, verification cost is 21M

---------------------------------------------------
Failed attempt

$pk_A$ in terms of randomized leaf: $pk_A = leaf_r.j_1^{-at}.B^{-t}$

Need to prove 4 relations: $D_{A_1} = {pk_A}^{r_1}$, $D_{A_2} = {pk_A}^{r_2}$, $D_{A_3} = {pk_A}^{r_3}$, $D_{A_4} = {pk_A}^{r_4}$

Applying protocol in Fig 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf), with correction to the typo in last statement

1. Prover picks random $r$ and creates $x = leaf_r^r.j_1^{-at.r}.B^{-t.r}$ along with a proof $\pi$ of the correct exponents, using the protocol for product relation.
2. Prover generates challenge $e$ by hashing transcript.
3. Prover generates response $s = r + \sum{r_i.e^i}$ and sends $x, s$ it to verifier
4. Verifier first checks $\pi$ and then checks if ${leaf_r.j_1^{-at}.B^{-t}}$ ???

$(leaf_r.j_1.B)^s = leaf_r^{k + \sum{r_i.c^i}}.j_1^{k + \sum{r_i.c^i}}.B^{k + \sum{r_i.c^i}} = leaf_r^k.j_1^k.B^k . leaf_r^{\sum{r_i.c^i}}.j_1^{\sum{r_i.c^i}}.B^{\sum{r_i.c^i}} = leaf_r^k.j_1^k.B^k . leaf_r$

$com(pk_A) = (E0, E1) =(g^v, W^v.pk_A), pk_A = E1.W^{-v}$


$D_{A_1} = ({leaf_r.j_1^{-at}.B^{-t}})^{r_1} = leaf_r^{r_1}.j^{-at.r_1}.B^{-t.r_1}$

$U_1 = g^{at.r_1}$ ......??

-------------------------------------------------------

Working attempt

$pk_A$ in terms of randomized leaf: $pk_A = leaf_r.j_1^{-at}.B^{-t}$

Need to prove 4 relations: $D_{A_1} = {pk_A}^{r_1}$, $D_{A_2} = {pk_A}^{r_2}$, $D_{A_3} = {pk_A}^{r_3}$, $D_{A_4} = {pk_A}^{r_4}$

Applying protocol in Fig 2 of [this paper](https://iacr.org/archive/asiacrypt2004/33290273/33290273.pdf), with correction to the typo in last statement

1. Prover picks random $u_1, u_2, u_3$ and creates $x = leaf_r^{u_1}.j_1^{u_2}.B^{u_3}$.
2. Prover generates challenge $e$ by hashing transcript.
3. Prover generates response $s_1 = u_1 + \sum{r_i.e^i}, s_2 = u_2 + (-at).\sum{r_i.e^i}, s_3 = u_3 + (-t).\sum{r_i.e^i}$ and sends $x, s_1, s_2, s_3$ it to verifier
4. Verifier checks if $leaf_r^{s_1}.j_1^{s_2}.B^{s_3} = x . \prod_i{D_{A_i}^{e_i}}$

$leaf_r^{s_1}.j_1^{s_2}.B^{s_3} = leaf_r^{u_1}.leaf_r^{\sum{r_i.e^i}}.j_1^{u_2}.j_1^{(-at).\sum{r_i.e^i}}.B^{u_3}.B^{-t.\sum{r_i.e^i}}$

$ = leaf_r^{u_1}.j_1^{u_2}.B^{u_3} . leaf_r^{\sum{r_i.e^i}}.j_1^{(-at).\sum{r_i.e^i}}.B^{-t.\sum{r_i.e^i}}$

$i$ goes from 1 to 4 so expanding above

$leaf_r^{u_1}.j_1^{u_2}.B^{u_3} . leaf_r^{r_1.e + r_2.e^2 + r_3.e^3 + r_4.e^4} . (j_1^{-at})^{r_1.e + r_2.e^2 + r_3.e^3 + r_4.e^4} . (B^{-t})^{r_1.e + r_2.e^2 + r_3.e^3 + r_4.e^4}$

$ = x . (((leaf_r.j_1^{-at}.B^{-t})^{r_1})^e . (((leaf_r.j_1^{-at}.B^{-t})^{r_2})^{e^2} . (((leaf_r.j_1^{-at}.B^{-t})^{r_3})^{e^3} . (((leaf_r.j_1^{-at}.B^{-t})^{r_4})^{e^4}$

$ = x . D_{A_1}^e . D_{A_2}^{e^2} . D_{A_3}^{e^3} . D_{A_4}^{e^4}$

What if venue didn't create $s$ properly, like while creating $s_2$, don't include $at$? 

------------------------------------------------------------------


$pk_A$ in terms of randomized leaf: $pk_A = leaf_r.j_1^{-at}.B^{-t}$

Need to prove 4 relations: $D_{A_1} = {pk_A}^{r_1}$, $D_{A_2} = {pk_A}^{r_2}$, $D_{A_3} = {pk_A}^{r_3}$, $D_{A_4} = {pk_A}^{r_4}$

Multiplying these 4 gives 

$pk_A^{r_1 + r_2 + r_3 + r_4} = D_{A_1}.D_{A_2}.D_{A_3}.D_{A_4}$

Let $z = r_1 + r_2 + r_3 + r_4$

Now prove these 2 relations:

1. $leaf_r^z.j_1^{-at.z}.B^{-t.z} = D_{A_1}.D_{A_2}.D_{A_3}.D_{A_4}$

2. $g^z = g^{r_1}.g^{r_2}.g^{r_3}.g^{r_4} => g^{r_1}.g^{r_2}.g^{r_3}.g^{r_4}.(g^{-1})^z = 1$

For 1, the proving cost is 8G + 8F + 3F, 11M + 3M = 8G + 11F, 14M and verification cost is 16M + 3M = 19M

For 2, the proving cost is G, M (since responses for $z$ and $r_i$ are already sent in 1) and verification cost is 5M

-----------------------------------------------------------------

Per asset data = $A = [j_0^{at}.j_1^m.j_2^n, j_0^{role}.j_1^i.pk_i....] = [j_0^{at}.j_1^m.j_2^n, j_0^{role}.j_1^1.pk_1, j_0^{role}.j_1^2.pk_2, ..., j_0^{role}.j_1^{m+n}.pk_{m+n}]$ where $m, n$ are number of mediators and auditors respectively. Asset can have both auditors and mediators.

Leaf of asset tree = $L = PedCom(A[0].x, A[1].x, A[2].x, ..., A[m+n+1].x)$

$L \in H, A \in G^{m+n+1}$ where $G, H$ are groups on the 2 different curves which form a 2-cycle.

High level idea: Venue first proves about each item in $A$ and then the commitment $L$ is formed from x-coordinates from items of $A$

Details:

1. Re-randomize $A$ to $A_r$ such that $A_r[i] = A[i].B^{r_i}$ so $A_r = [j_0^{at}.j_1^m.j_2^n.B^{r_0}, j_0^{role}.j_1^1.pk_1.B^{r_1}, j_0^{role}.j_1^2.pk_2.B^{r_2}, ..., j_0^{role}.j_1^{m+n}.pk_{m+n}.B^{r_{m+n}}]$. The verifier gets $A_r$
2. Prove that each $A[i]$ lies on the curve.
3. Prove that each $A_r[i] = A[i].B^{r_i}$

-----------------------------------------------------------

Per asset data = $A = (at.j_0 + m.j_1 + n.j_2, role.j_0 + 1.j_1 + pk_1, ..., role.j_0 + (m+n).j_1 + pk_{m+n})$
where $m, n$ are the number of mediators and auditors. Asset can have both.

Leaf of asset tree = $L = PedCom(A[0].x, A[1].x, ..., A[m+n+1].x)$

$L \in H, A \in G^{m+n+1}$ where $G, H$ are groups on two different curves forming a 2-cycle.

High level idea: Venue first proves about each item in $A$, then commitment $L$ is formed from x-coordinates of $A$'s elements.

Details:
1. Re-randomize $A$ to $A_r$: such that $A_r[i] = A[i] + r_i.B$.
   So $A_r = (at.j_0 + m.j_1 + n.j_2 + r_0.B, ..., role.j_0 + (m+n).j_1 + pk_{m+n} + r_{m+n}.B)$.
   The verifier gets $A_r$

2. Prove each $A[i]$ lies on the curve

3. Prove each $A_r[i] = A[i] + r_i.B$


------------------------------


Proving knowledge of $sk_e$ in $pk_e = g^{sk_e}$. Decompose $sk_e$ into $b$ bit chunks and do twisted Elgamal encryption of each chunk. 

Chunk $i$ = $(pk_s^{r_i}, pk_r^{r_i}, pk_A^{r_i}, g^{r_i}.h^{sk_{e,i}})$

Since Elgamal is homomorphic, chunks can be multiplied after raising to appropriate power. Let $B_i$ be the appropriate power. Combining all the chunks, we get:

$\prod{(g^{r_i}.h^{sk_{e,i}})^{B_i}} = g^{\sum{B_i * r_i}}.h^{sk_e}$

Now with a sigma protocol, we can prove that $sk_e$ is same as in $pk_e$

There is a proof associated with each chunk proving $r_i$ is same in all 4 elements in the chunk but the overall proof should be smaller and efficient than using generic ZKP. Decryption is expensive but its done off chain so maybe acceptable.

Value of $b$ in practice is either 32, 40, 48 so for 256-bit $sk_e$, number of chunks is 8, 7 and 6 respectively. 

Each chunk $sk_{e,i}$ must be proved in range $[0, 2^b)$ else the encryptor can make the decryption impractical. To see why range proof is needed, consider a simplified case 
where $b = 1$ and $sk_e$ has 2 bits, i.e. $sk_e \in [0, 4)$. Now the relevant parts of the 2 chiphertexts (1 per chunk) are $g^{r_0}.h^{sk_{e,0}}, g^{r_1}.h^{sk_{e,1}}$.  
When these are combined as mentioned above, the result is $g^{r_0}.h^{sk_{e,0}}.(g^{r_1}.h^{sk_{e,1}})^2 = g^{r_0 + 2r_1}.h^{sk_{e,0} + 2sk_{e,1}}$. 
For the correctness of encryption (which is enforced by above sigma protocol) $(sk_{e,0} + 2sk_{e,1}) \% 4$ must equal $sk_e$ meaning $sk_{e,0} + 2sk_{e,1} = 4z + sk_e$ for some integer $z$ which can be much larger than 4.  
Now, if $sk_e$ is 1, the honest encryptor will choose $sk_{e,0} = 1, sk_{e,1} = 0$ which satisfies above equation but a malicious encryptor can also choose $sk_{e,0} = 201, sk_{e,1} = 100$
which satisfies the above equation but is much harder to decrypt.

So in general, working in mod $p$, the $sk_{e, i}$ need to satisfy the equation $(\sum{B_i * sk_{e, i}}) \% p = sk_e$ which implies $\sum{B_i * sk_{e, i}} = p.z + sk_e$ for some integer $z$ which can be much greater than $p$ and thus 
each $sk_{e, i}$ can be chosen to be much larger than $2^b$. To prevent this each $sk_{e, i}$ must be proven in range $[0, 2^b)$

-----------------------------------------------


$$C_1 = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho}.g_6^s$$

$$C_2 = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho^2}.g_6^{s^2}$$

$$C_3 = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho^3}.g_6^{s^3}$$

$$C_4 = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho^4}.g_6^{s^4}$$

$$C_i = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho^i}.g_6^{s^i}$$

---------------

$$C_1 = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho}.g_6^s$$

$$C_2 = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho^2}.g_6^{s^2}$$

$$C_3 = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho^4}.g_6^{s^4}$$

$$C_4 = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho^8}.g_6^{s^8}$$

$$C_i = g_1^{sk}.g_2^v.g_3^c.g_4^a.g_5^{rho^{2^{i-1}}}.g_6^{s^{2^{i-1}}}$$

---------------------------------------------------

$G_p, G_q$ are groups with order $p, q$ respectively.

$g, g_i \in G_p$. $h, h_i \in G_q$

$sk_T \in Z_p, pk_T = g^{sk_T}, pk_T \in G_p$

User keys: $sk \in Z_q, pk = h^{sk}, pk \in G_q$

User commitments: $C = h^{sk}...h_i^{\rho}$, $C \in G_q, \rho \in Z_q$

User picks random $r \in Z_p$, creates $g^r = P, pk_T^r = Y$. Now $P, Y \in G_p$.

User computes coordinates of $P$ as $(x,y)$ and commits to them in $D = h_1^x.h_2^y.h_3^u$ for some randomness u. Now $x, y \in Z_q, D \in G_q$

User posts $Y$ on chain with a proof that:
1. $pk_T^r = Y$ ($pk_T$ was used and something else) 
2. $(x,y)$ are valid coordinates of $g^r$ and committed in $D$.
3. $x$ equals $\rho$. This is done from usual Sigma protocol

Note that step 2 involves doing a scalar multiplication in circuit and doing the curve point membership (curve equation) check

---------------------------------------


$$ g * v_0 + g_1 * v_1  $$

$$
pk_e = g * sk_e \\

(g*r, pk_e*r + pk_s) \\

sk_s * g == pk_s \\

g * r', w * r' + pk_s \\

g * r' = C_1 \\

w * r' + pk_s = C_2 \\

C_2 - w * r' = pk_s \\

C_2 - w * r' = g * sk_s
$$



