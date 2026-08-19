# SoP2: coupling two independent permutations to a random function

> **Direct coupling proof frozen — 29 July 2026.**
>
> This file contains only the pen-and-paper proof for the sum of two
> independent permutations.  Its Lean formalization is in `SoP2.lean`.
> The governing proof is the direct sequential coupling through Corollary 9.
> It uses no ANOVA decomposition.

### Abstract

Let $G$ be an arbitrary finite group of order $N$, and compare the pointwise
product of two independent uniform permutations with a uniform random
function under at most $q$ adaptive queries.  We construct an explicit
maximal coupling of honest bounded-system representatives and obtain an exact
finite characterization of the optimal information-theoretic advantage.
We then construct an honest online coupling and, whenever $q^3\leq N^2$,
prove the residual-free bound
$$
  \operatorname{Adv}_q(G)
  \leq\frac{q(q-1)(2q-1)}{3N^2}
  \leq\frac{2q^3}{3N^2}.
$$
This argument works for every finite group, preserves adaptivity and repeated
queries, and uses neither ANOVA nor the H-technique.  We also determine the
exact advantage through three fresh queries and treat saturation separately.

The distinct construction using one permutation on an ordered-pair
partition is proved separately in `SoP1.md`.

### Source conventions

The probability and random-system conventions are those in David
Lanzenberger's thesis, Definitions 2.26–2.28, Theorems 2.31–2.32,
Lemma 2.33, Notation 2.34, and the successor proof in Section 2.4.2, together
with the corresponding distance and coupling results in Lanzenberger–Maurer
(2020).  In particular:

* finite distributions may have arbitrary nonnegative weights;
* statistical distance is the one-sided maximum
  $\max_E(P(E)-Q(E))$, which for equal-mass probability laws is symmetric
  and equals both half the $L^1$ distance and the maximal absolute event
  gap;
* a coupling must be a normalized joint law with the two claimed marginals;
* equality under a coupling controls every adaptive environment once the
  coupled objects are honest representatives of the two random systems.

The proof below constructs and normalizes the concrete joint law directly,
proves both marginals, and proves the representative equivalences.  Thus its
use of the coupling principle is not circular.  The successor induction from
the source is not invoked as a black box; the fresh-rank tape argument below
is the concrete induction specialized to this problem.

## 1. Problem and notation

Let $G$ be a finite group of order $N\geq 1$.  We use multiplicative
notation in the proofs so that no commutativity is hidden.  In additive
notation, $a^{-1}b$ is $-a+b$.

Let $\Pi_1,\Pi_2$ be independent uniform permutations of $G$.  The
pointwise product $\Pi_1(x)\Pi_2(x)$ has the same law as
$$
  R(x)=A(x)^{-1}B(x),
$$
where $A,B$ are independent uniform permutations: pointwise inversion is a
bijection on the set of permutations.  Thus this normalized form covers the
sum of two uniform permutations without assuming that $G$ is abelian.
The ideal system is a uniform random function $F:G\to G$.

For $r\leq N$, write
$$
  (N)_r=N(N-1)\cdots(N-r+1),\qquad (N)_0=1,
$$
and let $\operatorname{Inj}_r(G)$ be the set of ordered injective
$r$-tuples in $G$.  It has cardinality $(N)_r$.

**Definition 1 (adaptive advantage).**
For a query budget $q\in\mathbb N$, put
$$
  \mathcal D_q=\bigcup_{1\leq k\leq q}G^k,
$$
with $\mathcal D_0=\varnothing$.  This is the common prefix-closed domain of
nonempty input histories of length at most $q$.  For a total deterministic
oracle $O:G\to G$, its $q$-bounded restriction is the deterministic system on
exactly $\mathcal D_q$ which answers a history
$x^k=(x_1,\ldots,x_k)$ by $O(x_k)$.  Let $\mathsf R_q$ be the law of this
restriction for $O(x)=A(x)^{-1}B(x)$, and let $\mathsf F_q$ be its law for a
uniform random function $O=F$.

Define $\operatorname{Adv}_q(G)$ to be the supremum, over all possibly
randomized adaptive environments making at most $q$ oracle calls, of the
absolute difference between their acceptance probabilities against
$\mathsf R_q$ and $\mathsf F_q$.  Repeated queries are permitted and must
receive the previous answer.  Equivalently, this is the supremum of the
statistical distance between the two transcript laws: every transcript event
is realized by a deterministic final acceptance bit.  Conversely, a
randomized final bit is a postprocessing and cannot increase statistical
distance.  More generally, condition on the entire private coin tape of a
randomized adaptive environment.  Its acceptance gap is a convex combination
of deterministic-environment gaps, so its absolute value is bounded by the
deterministic supremum.
Set
$$
  m=\min(q,N),
$$
the largest possible number of fresh queries.

**Definition 2 (the real and ideal fresh-output tapes).**
Let $A=(A_1,\ldots,A_m)$ and $B=(B_1,\ldots,B_m)$ be independent and
uniform in $\operatorname{Inj}_m(G)$, and put
$$
  Y_i=A_i^{-1}B_i.
$$
Let $Z=(Z_1,\ldots,Z_m)$ be uniform in $G^m$, equivalently with independent
uniform coordinates.

For $y=(y_1,\ldots,y_m)\in G^m$, define its compatible-assignment count
$$
  C_G(y)
  =
  \#\left\{
    a\in\operatorname{Inj}_m(G):
    (a_1y_1,\ldots,a_my_m)\in\operatorname{Inj}_m(G)
  \right\}.
  \tag{1}
$$

The tape $y$ also defines a deterministic $q$-bounded system $D_y$ whose
domain is exactly $\mathcal D_q$.
It maintains a cache and a fresh-query counter, initially empty and zero.
On input $x$, it replays the cached answer if $x$ has appeared before.
Otherwise it increments the counter to $i$, stores $y_i$ at $x$, and returns
$y_i$.  No undefined coordinate can be requested: if $m=q$, the interaction
ends after at most $q$ fresh calls; if $m=N$, every element of the domain has
already been cached after $N$ fresh calls.  This algorithm defines a unique
answer at every compatible history of length at most $q$, and restricting a
history to a prefix gives the same earlier answers.

## 2. Exact adaptive reduction

**Lemma 3 (honest lazy representatives and adaptive reduction).**
The laws of $D_Y$ and $D_Z$ are honest $q$-bounded probabilistic
deterministic-system representatives of $\mathsf R_q$ and $\mathsf F_q$,
respectively.  Moreover
$$
  D_y=D_z\quad\Longleftrightarrow\quad y=z.
  \tag{1a}
$$
Consequently, every coupling of $Y,Z$ is a coupling of honest
representatives, and tape equality implies equality of the full transcripts
for every adaptive strategy, including randomized strategies, stopping
strategies, and strategies that repeat queries.

*Proof.*
All four probabilistic deterministic systems in question have the common
domain $\mathcal D_q$; for $q=0$ they are the unique laws on the empty
domain.  Now fix any input sequence of length at most $q$, with repeats
allowed.  List its distinct inputs
in order of first appearance.  The values of a uniform permutation at those
fresh inputs form a uniform ordered injection; two independent permutations
give independent ordered injections $A,B$.  Therefore the real output at
fresh rank $i$ is $A_i^{-1}B_i=Y_i$, and a repeat replays the same value.
The output law is exactly that of $D_Y$.  A uniform random function has
independent uniform values at the fresh ranks and consistent repeats, so its
output law is exactly that of $D_Z$.  This proves equivalence on every fixed
input sequence, which is the nonadaptive characterization of equivalence for
the bounded deterministic-system distributions used here.

Since an environment making at most $q$ calls never evaluates a history
outside $\mathcal D_q$, restriction does not change its transcript or
acceptance law.  Thus Definition 1 is also exactly the usual at-most-$q$
advantage between the original total real and ideal oracles.

Equivalently, one can verify the adaptive statement directly.  After $r$
distinct inputs have been queried, the exposed images of each permutation
form a uniform injection.  Conditional on them, the image at every
unqueried domain label is uniform among the unused values.  The next queried
label may depend on the preceding transcript, but unqueried labels remain
exchangeable.  Thus the next unused pair has conditional probability
$1/(N-r)^2$, exactly as in the ordered injection queues.

Choose once and for all $m$ distinct inputs.  Querying them in that order
against $D_y$ returns $y$, proving (1a).  Finally couple the private coins of
a randomized environment identically in the two runs.  If the sampled tapes
are equal, induction on the round shows that the prior transcripts, the next
queries, and the next answers are equal.  Early stopping and repeats are
included in this induction. $\square$

**Lemma 4 (fiber law and normalization).**
For every $y\in G^m$,
$$
  \Pr[Y=y]=\frac{C_G(y)}{(N)_m^2},
  \qquad
  \Pr[Z=y]=\frac1{N^m},
  \tag{2}
$$
and
$$
  \sum_{y\in G^m}C_G(y)=(N)_m^2.
  \tag{3}
$$

*Proof.*
If $A=a$ and $Y=y$, then necessarily $B_i=a_iy_i$ for every $i$.
This $B$ is injective exactly when $a$ is counted by $C_G(y)$.  Thus
there are $C_G(y)$ pairs $(a,b)$ in the fiber over $y$, out of the
$(N)_m^2$ equally likely pairs.  This proves the first identity in (2); the
second is immediate.  The fibers partition
$\operatorname{Inj}_m(G)^2$, giving (3). $\square$

**Proposition 5 (explicit maximal tape coupling).**
Define
$$
  \gamma(y)=
  \min\left\{\frac{C_G(y)}{(N)_m^2},\frac1{N^m}\right\},
  \qquad
  \rho=\sum_{y\in G^m}\gamma(y).
  \tag{4}
$$
There is a joint probability law of $(Y,Z)$ with the marginals (2) and
$$
  \Pr[Y\ne Z]=1-\rho.
  \tag{5}
$$
For $y$ in the real support, equivalently $C_G(y)>0$, the coupling can also
sample the honest hidden injection queues by choosing $A$ uniformly among
the $C_G(y)$ compatible assignments and setting $B_i=A_iy_i$.

*Proof.*
Here is an integer transport realization which makes normalization completely
explicit.  Put
$$
  L=N^m(N)_m^2.
$$
On the real side, take $N^m$ labeled copies of every hidden pair
$(a,b)\in\operatorname{Inj}_m(G)^2$.  On the ideal side, take
$(N)_m^2$ labeled copies of every $z\in G^m$.  Both sides contain exactly
$L$ microcopies.  The real $y$-fiber has
$N^mC_G(y)$ copies and the ideal $y$-fiber has $(N)_m^2$ copies.
Match the minimum of these two capacities inside the $y$-fiber.  The two
sets of residual copies have the same cardinality, so fix any bijection
between them.  At every $y$, at least one residual fiber is empty; hence no
residual edge joins equal tapes.  Sampling a uniform edge of this bijection
is already the required coupling.

Equivalently, after forgetting the labels, its law can be described as
follows.  With total mass $\rho$, sample $w$ with probability
$\gamma(w)/\rho$ and set $Y=Z=w$.  With the remaining mass, sample from the
two normalized residual laws
$$
  \frac{\Pr[Y=y]-\gamma(y)}{1-\rho},
  \qquad
  \frac{\Pr[Z=y]-\gamma(y)}{1-\rho}.
$$
At every $y$, at least one residual is zero, so the two residual supports are
disjoint; couple them in any way.  The displayed construction has total mass
one, its marginals are the two original laws, and disagreement occurs exactly
on the residual branch.  The cases $\rho=0$ or $\rho=1$ are interpreted by
omitting the empty branch.

For an injective pair $(a,b)$, put $y_i=a_i^{-1}b_i$.  The conditional
hidden-table procedure assigns it probability
$$
  \frac{C_G(y)}{(N)_m^2}\frac1{C_G(y)}
  =\frac1{(N)_m^2}.
$$
Hence $(A,B)$ is exactly a pair of independent uniform injective tapes.
Together with Lemma 3, the sampled objects $D_Y,D_Z$ are therefore honest
representatives of the $q$-bounded restrictions of the original systems.
$\square$

**Theorem 6 (exact finite characterization and optimal coupling).**
For every finite group $G$ and every query budget $q$,
$$
\boxed{
  \operatorname{Adv}_q(G)
  =
  1-\sum_{y\in G^m}
    \min\left\{\frac{C_G(y)}{(N)_m^2},\frac1{N^m}\right\}
  =
  \frac12\sum_{y\in G^m}
    \left|
      \frac{C_G(y)}{(N)_m^2}-\frac1{N^m}
    \right|
}
\tag{6}
$$
where $m=\min(q,N)$.  The coupling in Proposition 5 has disagreement
probability exactly equal to this advantage.

Equivalently, in the integer microcopy notation of Proposition 5,
$$
  \operatorname{Adv}_q(G)
  =
  \frac1{2N^m(N)_m^2}
  \sum_{y\in G^m}
  \left|N^mC_G(y)-(N)_m^2\right|.
  \tag{6a}
$$

*Proof.*
By Lemma 3 and Proposition 5, every adaptive environment has distinguishing
advantage at most the disagreement probability in (5).  The two expressions
in (6) are equal because the two laws have equal total mass.

For the reverse inequality, query any fixed list of $m$ distinct inputs.
The complete answer vector has law $Y$ in the real system and $Z$ in the
ideal system.  Accept on
$$
  S=\{y:\Pr[Y=y]>\Pr[Z=y]\}.
$$
The acceptance-probability difference is the positive part of the signed
measure $\Pr[Y=\cdot]-\Pr[Z=\cdot]$, hence equals the right-hand side of
(6).  This environment is nonadaptive, so it is among the environments in
Definition 1. $\square$

This theorem is an exact characterization, not yet by itself a satisfactory
closed security estimate for large $q$: evaluating its positive part can
retain genuine information about the algebra of $G$.

## 3. A direct online coupling and a residual-free bound

The next construction is weaker than the optimal coupling above but exposes
an actual online disagreement event and gives a clean all-group bound.

After $r$ successful fresh-query steps, let
$\mathcal A,\mathcal B\subseteq G$ be the two used image sets, each of size
$r$.  For $z\in G$, put
$$
  c_z=\#\{(\alpha,\beta)\in\mathcal A\times\mathcal B:
                 \alpha^{-1}\beta=z\}.
  \tag{7}
$$

**Lemma 7 (exact next-output law).**
For $0\leq r<N$, the following statements hold.
The conditional real probability of the next output $z$ is
$$
  p_r(z)=\frac{N-2r+c_z}{(N-r)^2}.
  \tag{8}
$$
Its statistical distance from a uniform element of $G$ is
$$
  \delta(\mathcal A,\mathcal B)
  =
  \frac{\sum_{z\in G}(Nc_z-r^2)_+}{N(N-r)^2}
  \leq
  d_r:=\min\left\{1,\frac{r^2}{N(N-r)}\right\}.
  \tag{9}
$$

*Proof.*
There are $N$ pairs $(a,b)\in G^2$ with $a^{-1}b=z$.  Of these, $r$
have $a\in\mathcal A$, $r$ have $b\in\mathcal B$, and $c_z$ were
subtracted twice.  This proves (8).

Since $\sum_zc_z=r^2$, subtracting $1/N$ from (8) gives
$$
  p_r(z)-\frac1N
  =\frac{Nc_z-r^2}{N(N-r)^2},
$$
which proves the equality in (9).  Moreover $0\leq c_z\leq r$.
Among $N$ numbers in $[0,r]$ with sum $r^2$, the convex function
$t\mapsto(Nt-r^2)_+$ has maximal sum when $r$ entries equal $r$ and
the others equal zero.  The resulting numerator is
$r^2(N-r)$.  Division by $N(N-r)^2$, followed by the trivial cap at one,
proves the bound. $\square$

**Proposition 8 (sequential maximal coupling).**
There is an honest online coupling of the real and ideal systems such that
$$
  \Pr[\text{some answer disagrees}]
  \leq
  1-\prod_{r=0}^{m-1}(1-d_r)
  \leq
  \sum_{r=0}^{m-1}d_r,
  \tag{10}
$$
with $d_r$ as in (9).

*Proof.*
As long as the transcripts agree, maximally couple the conditional real
next-output law (8) to a fresh uniform ideal output.  Given the real output
$z$, choose the hidden unused pair $(a,b)$ uniformly from its
$N-2r+c_z$ preimages.  Multiplying the probability of $z$ by this
conditional probability gives $1/(N-r)^2$ for every unused pair, so the real
hidden-table marginal is exact.  The ideal marginal is uniform by
construction.  After a first disagreement, continue each marginal
independently according to its honest conditional law from its current cache
and used-image tables.

Conditioned on agreement through step $r-1$, Lemma 7 bounds the next
disagreement probability by $d_r$.  Multiplication of the conditional
success probabilities gives the first bound in (10).  The second is the
elementary inequality $1-\prod_r(1-d_r)\leq\sum_rd_r$.  Repeated queries
only replay equal cached answers and therefore add no failure probability.
$\square$

**Corollary 9 (strict comparison with the $q^3/N^2$ benchmark).**
If $q^3\leq N^2$, then
$$
  \operatorname{Adv}_q(G)
  \leq
  \frac{q(q-1)(2q-1)}{3N^2}
  \leq
  \frac{2q^3}{3N^2}
  \leq
  \frac{q^3}{N^2}.
  \tag{11}
$$

*Proof.*
The hypothesis implies $q\leq N$, so $m=q$.
For $q\geq2$, the hypothesis implies $2(q-1)\leq N$: indeed
$(2q-2)^2\leq q^3\leq N^2$.  Hence $N-r\geq N/2$ for $0\leq r<q$.
Proposition 8 and $\sum_{r<q}r^2=q(q-1)(2q-1)/6$ give
$$
  \operatorname{Adv}_q(G)
  \leq
  \sum_{r<q}\frac{r^2}{N(N-r)}
  \leq
  \frac2{N^2}\sum_{r<q}r^2,
$$
which is (11).  The cases $q=0,1$ are immediate. $\square$

The middle inequality in (11) is strict for $q\geq1$.  At $q=0$, all four
quantities in (11) are zero.

The factor $2/3$ is a genuine improvement over the previously established
law-level adaptive benchmark
$\operatorname{Adv}_q(G)\leq q^3/N^2$ on the same finite-group setting and
parameter range.  Only that numerical benchmark is used here; no
H-technique proof or endpoint is invoked.  The exact small cases below show
that the worst-state estimate used to analyze this sequential coupling is
not sharp.

## 4. Exact audit cases

**Proposition 10 (exact advantages through three fresh queries).**
For every finite group $G$ of order $N$:

1. $\operatorname{Adv}_0(G)=\operatorname{Adv}_1(G)=0$.
2. If $N\geq2$, then
   $$
     \operatorname{Adv}_2(G)=\frac1{N(N-1)}.
     \tag{12}
   $$
3. For three fresh queries,
   $$
   \operatorname{Adv}_3(G)=
   \begin{cases}
     2/3,&N=3,\\[2mm]
     5/48,&N=4,\\[2mm]
     \dfrac{3N^2-12N+4}{N^2(N-1)(N-2)},&N\geq5.
   \end{cases}
   \tag{13}
   $$
   If $N=1$, the value is $0$; if $N=2$, a budget of three has only two
   fresh inputs and its value is $1/2$ by (12).

*Proof.*
The first claim is immediate from uniformity of one output.

For $m=2$, if $y_1=y_2$, every injective $a$ is compatible, so
$C_G(y)=N(N-1)$.  If $y_1\ne y_2$, then after choosing $a_1$, the value
$a_2$ must avoid both $a_1$ and $a_1y_1y_2^{-1}$, so
$C_G(y)=N(N-2)$.  There are $N$ equal-output vectors and $N(N-1)$
unequal-output vectors.  Substitution in (6) gives (12).

For $m=3$, first choose an injective $a$, giving $(N)_3$ choices.
For each pair $i<j$, let $E_{ij}$ be the event $a_iy_i=a_jy_j$.
If $y_i=y_j$, then $E_{ij}$ is impossible because $a_i\ne a_j$.
If $y_i\ne y_j$, the equality determines $a_j$ from $a_i$, after
which the third $a$-coordinate has $N-2$ choices; hence
$$
  |E_{ij}|=N(N-2).
$$
If exactly two $y$-coordinates are equal, precisely two of the events are
nonempty, and their intersection is empty: simultaneous equality would also
force the two equal-$y$ positions to have equal $a$-values.  If all three
$y_i$ are distinct, all three events are nonempty, and every intersection
of two is the event that all three values $a_iy_i$ are equal.  That event
has $N$ assignments (choose the common value), and it is also the triple
intersection.  Inclusion–exclusion therefore gives
$$
  C_G(y)=
  \begin{cases}
    N(N-1)(N-2),&y_1=y_2=y_3,\\
    N(N-2)(N-3),&\text{exactly two coordinates are equal},\\
    N(N^2-6N+10),&\text{all three coordinates are distinct}.
  \end{cases}
  \tag{14}
$$
There are respectively $N$, $3N(N-1)$, and
$N(N-1)(N-2)$ output vectors of these types.  Comparing each probability
$C_G(y)/(N)_3^2$ with $N^{-3}$ shows:

* for $N\geq5$, the first two types have positive excess and the third
  negative excess;
* for $N=4$, only the all-equal type has positive excess;
* for $N=3$, the all-equal and all-distinct types have positive excess.

Summing the corresponding positive excesses yields (13). $\square$

**Proposition 11 (saturation lower bound for abelian groups).**
If $G$ is abelian and $q\geq N$, then
$$
  \operatorname{Adv}_q(G)\geq1-\frac1N.
  \tag{15}
$$

*Proof.*
Query every domain point.  In additive notation the normalized real outputs
satisfy
$$
  \sum_{x\in G}(-A(x)+B(x))
  =-\sum_{g\in G}g+\sum_{g\in G}g=0.
$$
For a uniform random function, the sum of all outputs is uniform on $G$:
condition on all but one output and use uniformity of the remaining one.
Testing whether the total sum is zero therefore has real acceptance
probability one and ideal acceptance probability $1/N$. $\square$


## 5. Final theorem and proof dependency graph

The final closed theorem is Corollary 9.  The arrows below point from a result
to the results used in its proof.  This is the binding proof graph for the
closed security theorem; in particular, it records the construction that must
be formalized rather than merely an inequality with the same conclusion.

```text
R0. Corollary 9: law-level adaptive distinguishing bound
├─ R1. Coupling domination
│  ├─ R1a. Lemma 3: honest fresh-rank representatives
│  │  ├─ literal sum ↔ normalized difference
│  │  ├─ fresh permutation images ↔ uniform injection queues
│  │  └─ cache replay handles adaptivity, stopping, and repetitions
│  ├─ R1b. Proposition 8: explicit sequential tape coupling
│  │  ├─ R1b-i. normalization and real/ideal marginals
│  │  ├─ R1b-ii. one-step output coupling at every agreeing state
│  │  │  ├─ finite maximal-coupling theorem
│  │  │  ├─ Lemma 7: one-step statistical-distance bound
│  │  │  │  ├─ exact unused-pair fiber count N - 2r + c_z
│  │  │  │  ├─ sum_z c_z = r² and c_z ≤ r
│  │  │  │  └─ pointwise positive-excess estimate
│  │  │  └─ hidden-pair lift preserves the uniform-unused marginal
│  │  ├─ R1b-iii. after failure, honest independent continuation
│  │  └─ R1b-iv. failure induction
│  │     ├─ Pr[Fail_m] ≤ 1 - product_{r<m}(1-d_r)
│  │     └─ 1 - product_{r<m}(1-d_r) ≤ sum_{r<m} d_r
│  └─ R1c. tape disagreement implies transcript disagreement
│     └─ common deterministic replay of the coupled tapes
└─ R2. Close the sequential sum
   ├─ q³ ≤ N² implies q ≤ N
   ├─ 4(q-1)² ≤ q³, hence 2(q-1) ≤ N
   ├─ r²/[N(N-r)] ≤ 2r²/N² for r < q
   └─ sum_{r<q} r² = q(q-1)(2q-1)/6
```

Lemma 7 does **not** construct a coupling: it only calculates and bounds the
distance of the two one-step laws.  The finite maximal-coupling theorem and
the hidden-pair marginal lift are separate siblings needed to construct the
one-step joint in Proposition 8.  Likewise, Lemma 3 and coupling domination
are genuine ancestors of the law-level root; omitting them would leave only a
fixed-tape calculation.

The exact characterization and the audit results form separate, deliberately
non-circular verification graphs:

```text
E0. Theorem 6: exact adaptive advantage and optimal disagreement
├─ Lemma 3: honest representatives and fixed fresh schedule
├─ Lemma 4: exact tape point masses and normalization
├─ Proposition 5: normalized maximal tape coupling with both marginals
└─ equal-mass distance identities: overlap = positive part = half-L¹

A0. Proposition 10: exact q ≤ 3 audit
├─ Theorem 6
└─ direct classification of the compatible-count fibers

A1. Proposition 11: abelian saturation lower bound
└─ full-domain sum invariant and uniform ideal total
```

These results audit normalization, exactness, and boundary behavior, but the
proof of Corollary 9 does not use them.  In particular, Proposition 5's global
maximal coupling is not a substitute for Proposition 8's sequential joint.

## 6. Primary-source audit notes

The following defects were checked in the rendered source PDFs:

1. Dai–Hoang–Tessaro’s revised version reports a glitch in the original
   proceedings proofs of XOR and XOR2.
2. On PDF page 25, the denominator following the displayed value of $W$
   should be $(N-i+1)^4$, not $(N-2i+1)^4$.
3. Dutta–Nandi–Saha Theorem 3 repeats the equation at $x_1$; its second line
   should be the equation at $(x_2,\gamma_2)$.
4. The “non-zero” output restriction in that theorem is stale; Sections
   6.1–6.2 prove the XOR2 statement for arbitrary output strings.
5. The Mirror-paper range is $q\leq2^n/17=N/17$, not $q\leq2^{n/17}$.

For comparison only, the verified prior XOR2 bounds are
$$
  \left(\frac qN\right)^{3/2}
  \quad(q\leq N/16)
$$
from Dai–Hoang–Tessaro and
$$
  \frac{19q^2+8n^3}{N^2}
  \quad(N=2^n,\ q\leq N/17)
$$
from Dutta–Nandi–Saha.  Corollary 9 is claimed only as a strict
constant-factor improvement over the repository’s $q^3/N^2$ benchmark.
No domination over either source bound is claimed.

## 7. Frozen result-to-formalization correspondence

| Paper result | Lean declaration or declarations |
|---|---|
| Definition 1 | `xop`, `urf` |
| Definition 2 | `compatible_count`, `real_fresh_tape`, `ideal_fresh_tape` |
| Lemma 3 | representative-equivalence declarations in Sections 1–2 of `SoP2.lean` |
| Lemma 4 | `real_fresh_tape_apply`, `compatible_count_sum` |
| Proposition 5 | `maximal_tape_coupling` and its marginal/disagreement theorems |
| Theorem 6 | `sop_advantage_eq_half_l1_compatible_count` |
| Lemma 7 | `real_next_output_apply`, `real_next_output_distance_le` |
| Proposition 8 | `sequential_tape_coupling`, its marginal theorems, `sequential_tape_coupling_disagreement_le_product`, and `sequential_tape_coupling_disagreement_le_sum` |
| Coupling domination for the concrete systems | `sop_advantage_le_sequential_coupling_disagreement`, then `sop_advantage_le_sequential_coupling_sum` |
| Corollary 9 | `sop_advantage_closed_bound` |
| Proposition 10 | the exact zero-, one-, two-, and three-query audit theorems |
| Proposition 11 | `sop_abelian_saturation_lower_bound` |

## References

1. David Lanzenberger, *A Theory of Random Systems, Games, and Hardness
   Amplification*, doctoral dissertation, ETH Zurich, 2023.
2. David Lanzenberger and Ueli Maurer, “Coupling of Random Systems,” 2021.
3. Wei Dai, Viet Tung Hoang, and Stefano Tessaro, “Information-theoretic
   Indistinguishability via the Chi-squared Method,” revised full version,
   IACR ePrint 2017/537.
4. Avijit Dutta, Mridul Nandi, and Abishanka Saha, “Proof of Mirror Theory
   for xi_max = 2,” IACR ePrint 2020/669.
