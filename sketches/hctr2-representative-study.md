# Representative proofs for HCTR2 in the single-user and multi-user settings

**Status (2026-08-04).** Pen-and-paper research note. The source theorems and
the existing single-user coupling proof are **verified**. The tagged
multi-user coupling and its ordered-distinct-seed refinement are **derived at
paper level**, but have not been independently refereed or formalized. The
signed-rook improvement is **open**: its exact proxy terms and matching attacks
are proved below, but no global remainder estimate is claimed.

This note follows the notation and modeling discipline of
[FOUNDATIONS.md](../FOUNDATIONS.md). In particular, an honest coupling and a
signed virtual representative are kept separate.

## 1. Question and answer

The problem is to compare HCTR2, with its block cipher replaced by a uniform
$n$-bit permutation, with an ideal variable-input-length tweakable random
permutation. We want both the ordinary single-user comparison and the
multi-user comparison in which one adaptive environment can move between
independently keyed users.

The main conclusions are these.

1. Definition 2.27 of [FOUNDATIONS.md](../FOUNDATIONS.md) is not the native
   multi-user game. It couples several *alternative systems* simultaneously.
   Multi-user security is the ordinary pairwise advantage between two tagged
   parallel systems.
2. The Lanzenberger--Maurer tape representative gives the cleanest verified
   single-user information-theoretic bound, and the same carrier gives a
   two-game conditional-equivalence derivation:

   $$
   \operatorname{Adv}_{\mathrm{su}}
   \le
   \frac{3\sigma^2+2q\sigma+7\sigma+2}{2N},
   \qquad N=2^n.
   $$

   Both proof wrappers remove the separate PRP--RND switching term in the
   original HCTR2 proof.
3. Coupling all users in one tagged system gives the profile bound

   $$
   \operatorname{Adv}_{\mathrm{mu}}
   \le
   \min\!\left\{
     1,
     \frac{
       3\sum_i\sigma_i^2
       +2\sum_i q_i\sigma_i
       +7\sigma+2a
     }{2N}
   \right\},
   $$

   where $a$ is the number of active users and
   $\sigma=\sum_i\sigma_i$. There is no factor equal to the number of
   *declared* users.
4. The active-user scale is real for concrete POLYVAL HCTR2. One carefully
   chosen one-block query has exact advantage $1/N$. Repeating the test under
   independent users gives an advantage of order $a/N$. Thus no theorem can
   be independent of active users if one query per user is free.
5. A long-query collision test gives exact advantage

   $$
   1-\prod_i\frac{(N)_{r_i}}{N^{r_i}}
   \sim
   \frac{1}{N}\sum_i\binom{r_i}{2}.
   $$

   It proves that the within-user quadratic profile is also real.
6. Signed representatives expose both attacks very cleanly and may improve the
   leading constants. They have not yet produced a proved all-transcript upper
   bound because the higher connected collision diagrams remain uncontrolled.

## 2. Systems and resources

Let

$$
N=2^n,
$$

and let $\pi$ be a uniform permutation of $\{0,1\}^n$. Write

$$
\mathbf H=\mathbf{HCTR2}[\operatorname{Perm}(n)]
$$

for HCTR2 using $\pi$, and let $\widetilde{\mathbf T}$ be the ideal
variable-input-length tweakable permutation family. Different tweak--length
classes of $\widetilde{\mathbf T}$ are independent.

For a single user, $q$ is the number of forward or inverse construction
queries and $\sigma$ is the total number of $n$-bit tweak and message blocks,
using the convention of the original HCTR2 paper. The coupling proof assumes
$\sigma+2\le N$; once its displayed bound is at least one, the cap at one is
understood.

For user $i$, write

$$
q_i=\text{number of queries to user }i,
\qquad
\sigma_i=\text{block work sent to user }i.
$$

Let

$$
q=\sum_iq_i,
\qquad
\sigma=\sum_i\sigma_i,
\qquad
\sigma_{\max}=\max_i\sigma_i,
$$

and let $a$ be the number of indices for which $q_i>0$. Only active users are
sampled in the lazy representatives.

In a theorem statement, $(q_i,\sigma_i)$ denotes a deterministic cap that
holds on every path in the system horizon. If only the global cap
$\sum_i\sigma_i\le\sigma$ is fixed, an adaptive environment may produce
different profiles on different paths; the valid endpoint is then the maximum
of the profile expression over all allowed profiles, such as the global
envelopes derived below. A random realized profile must not simply be
substituted into a bound after the experiment.

### 2.1. The native random-system multi-user game

For independently keyed users, form

$$
\mathbf H^{[u]}
  =[\mathbf H_1,\ldots,\mathbf H_u],
\qquad
\widetilde{\mathbf T}^{[u]}
  =[\widetilde{\mathbf T}_1,\ldots,
    \widetilde{\mathbf T}_u].
$$

A query has the form $(x,i)$, where $i$ selects the user. Definition 2.13 of
[FOUNDATIONS.md](../FOUNDATIONS.md) routes the query only to component $i$ and
gives that component its own projected history. One adaptive environment may
choose the next user from the entire preceding transcript.

The native advantage is

$$
\operatorname{Adv}_{\mathrm{mu}}
  =\operatorname{Adv}\!\left(
      \mathbf H^{[u]},
      \widetilde{\mathbf T}^{[u]}
    \right).
$$

This is one real-vs-ideal comparison, not the several-system distance of
Definition 2.27.

A theorem with no explicit $u$ must use a global resource horizon, for example

$$
\sum_i\sigma_i\le\sigma.
$$

If instead the adversary receives $q$ queries for every user, then its total
work may be $uq$, and dependence on $u$ can be unavoidable.

## 3. Source bounds

### 3.1. Original single-user H-coefficient proof

Crowley, Huckleberry, and Biggers prove the information-theoretic main lemma

$$
\operatorname{Adv}^{\pm\mathrm{rnd}}_{\mathbf H}(q,\sigma)
\le
\frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}.
$$

Their final theorem changes the ideal randomized system to a tweakable random
permutation and therefore adds the switching term $q^2/(2N)$. In the present
notation,

$$
\operatorname{Adv}^{\pm\widetilde{\mathrm{prp}}}_{\mathrm{HCTR2}[E]}
\le
\operatorname{Adv}^{\pm\mathrm{prp}}_E
+
\frac{3\sigma^2+2q\sigma+q^2+7\sigma+2}{2N}.
$$

**Status: PUBLISHED.** See
[HCTR2: Efficient Wide-Block Encryption for Arbitrary-Length Inputs](../papers/2021-1441.pdf),
Sections 3.4--3.5.

### 3.2. Published multi-user theorem

Chen, Hiraga, Mouha, Naito, Sasaki, and Sugawara prove, for an
$\omega$-regular, $\omega$-AXU, and A2XU hash family with their stated
padding structure,

$$
\operatorname{Adv}^{\mathrm{mu-vil-stprp}}_{\mathrm{HCTR2}}
\le
\frac{3\omega\sigma_{\max}\sigma+4n\sigma}{N}
+
\operatorname{Adv}^{\mathrm{mu-sprp}}_E.
$$

The proof actually retains the sharper profile expression

$$
\frac{3\omega\sum_i\sigma_i^2+4n\sigma}{N}
$$

before applying
$\sum_i\sigma_i^2\le\sigma_{\max}\sigma$. POLYVAL has $\omega=1$.

**Status: PUBLISHED.** See
[ePrint 2026/085](https://eprint.iacr.org/2026/085) and the
[ASIACRYPT chapter](https://link.springer.com/chapter/10.1007/978-981-95-5018-0_1).
The theorem was checked in the 3 May 2026 PDF. The ePrint page records a later
revision; the final source should be checked again before quoting line-level
details in a publication.

## 4. Honest representative and coupling proofs

### 4.1. Single-user tape coupling

The complete construction is in
[HCTR2_COUPLING_PROOF.md](../papers/notes/HCTR2_COUPLING_PROOF.md).
The common tape contains:

1. the two initial hidden permutation values;
2. independent raw $n$-bit cells for the narrow call and XCTR calls of every
   query position;
3. rejection rankings for completing a lazy permutation; and
4. rejection rankings for the ideal tweak--length permutation classes.

The real representative interprets the tape as one global lazy permutation.
The ideal representative interprets the same raw cells as candidate ideal
answers and rejects only if a whole response repeats inside its tweak--length
class. Before the first raw input or output conflict, the visible transcripts
are identical.

Every possible first disagreement is a collision between two inferred
permutation sites. Hash-pinned collisions use POLYVAL regularity or AXU;
response-pinned collisions use a fresh raw cell and cost exactly $1/N$.
Consequently,

$$
\boxed{
\operatorname{Adv}_{\mathrm{su}}
\le
\min\!\left\{
  1,
  \frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}
\right\}.}
$$

This proves the same main-lemma expression directly against the tweakable
random permutation. It therefore removes the paper's $q^2/(2N)$ switching
term.

**Status: VERIFIED PEN-AND-PAPER.** The local proof has been audited in both
directions of the bidirectional interface. It is not claimed here as a new
Lean theorem.

### 4.2. Conditional equivalence on the common carrier

The representatives of Section 4.1 also give a conditional-equivalence proof.
Put both systems on the common seed space

$$
\Omega=(h^*,l^*)\times W\times R_G\times R_F
$$

and attach to both the hidden prefix-monotone condition
$\mathsf{Bad}_\omega(x^i)$ that records the first raw same-side collision in
the inferred permutation domain or range.

Before this condition fires, the complete response prefixes of the two
representatives agree for every seed. Consequently, for every fixed
$x^i,y^i$, their not-won transcript masses are equal. Theorem 4.17 may be
oriented with the ideal game first. Conditional on an ideal visible prefix,
the current raw tape cell remains uniform, and the collision inventory gives

The resulting endpoint is exactly

$$
\boxed{
\operatorname{Adv}_{\mathrm{su}}
\le
\min\!\left\{
1,
\frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}
\right\}.}
$$

The complete theorem and proof are given in
[Conditional Equivalence for HCTR2 on a Common Random
Tape](../papers/notes/HCTR2_CE_RAW_TAPE.md). The same game construction lifts
to the tagged multi-user carrier of Section 4.3.

### 4.3. Tagged multi-user coupling

Give each active user an independent copy of the single-user tape. Run all
copies inside one tagged DDS. The environment may interleave users, but at a
query to user $i$ the unread cells of tape $i$ remain independent of the whole
visible prefix. The single-user first-failure calculation therefore applies
conditionally at that step.

Sum the failure charges pathwise over the actually queried users. This gives

$$
B_i^{\mathrm{iid}}
  =\frac{3\sigma_i^2+2q_i\sigma_i+7\sigma_i+2}{2N}
$$

and hence

$$
\boxed{
\operatorname{Adv}_{\mathrm{mu}}
\le
\min\!\left\{
  1,
  \sum_{i:q_i>0}B_i^{\mathrm{iid}}
\right\}.}
$$

Equivalently,

$$
\operatorname{Adv}_{\mathrm{mu}}
\le
\min\!\left\{
1,
\frac{
3\sum_i\sigma_i^2
+2\sum_iq_i\sigma_i
+7\sigma+2a
}{2N}
\right\}.
$$

This is a direct tagged-system proof. No hybrid is charged for an inactive
user, and no cross-user collision term appears because the users have
independent permutations.

Since $q_i\le\sigma_i$, $a\le\sigma$, and
$\sum_i\sigma_i^2\le\sigma_{\max}\sigma$, a convenient envelope is

$$
\operatorname{Adv}_{\mathrm{mu}}
\le
\min\!\left\{
  1,
  \frac{5\sigma_{\max}\sigma+9\sigma}{2N}
\right\}.
$$

The still coarser global-work form is

$$
\operatorname{Adv}_{\mathrm{mu}}
\le
\min\!\left\{
  1,
  \frac{5\sigma^2+9\sigma}{2N}
\right\}.
$$

The profile theorem is the meaningful statement; the global form deliberately
hides how work is distributed.

For a computational theorem, add the multi-user SPRP advantage of the block
cipher with the simulator's total primitive-call budget. Initializing HCTR2
costs two primitive calls per active user, so the precise substitution budget
must retain $a$ unless those calls have already been included in $\sigma$.

**Status: DERIVED.** The conditional independence and pathwise summation are
complete. This multi-user lifting has not yet received the independent audit
given to the single-user tape proof.

### 4.4. Ordered-distinct hidden seeds

The preceding tape starts from two iid hidden values and repairs equality. It
pays $1/N$ once per active user. The ideal representative does not observe the
second hidden value, so both systems may instead sample the pair directly and
uniformly from ordered distinct pairs.

This removes the initial $1/N$ charge. A genuinely $L$-pinned equation then
costs $1/(N-1)$ instead of $1/N$. Most nominal $L$ cases can be re-pinned by a
fresh raw response cell and remain exactly $1/N$. Let $R_{L,i}$ count only the
irreducible cases for user $i$:

1. a fresh decryption relation $L=UU_s$;
2. a later-encryption relation $S_j^r=MM_s$; and
3. a fresh-decryption within-query relation $MM_s=S_{s,j}$.

If $M_i$ is the total number of message blocks of user $i$, then

$$
R_{L,i}\le M_i+q_i(M_i-q_i).
$$

The direct distinct-seed bound is

$$
B_i^{\mathrm{dist}}
  =B_i^{\mathrm{iid}}
   -\frac1N
   +\frac{R_{L,i}}{N(N-1)}.
$$

Choosing the better representative separately for each user gives

$$
\boxed{
B_i^*
=
\frac{3\sigma_i^2+2q_i\sigma_i+7\sigma_i}{2N}
+
\min\!\left\{
  \frac1N,
  \frac{R_{L,i}}{N(N-1)}
\right\}.}
$$

Thus

$$
\operatorname{Adv}_{\mathrm{mu}}
\le
\min\!\left\{1,\sum_iB_i^*\right\}.
$$

This refinement removes a mechanically charged active-user constant, but it
does **not** imply that HCTR2 has no real active-user signal. Section 5 gives a
different, visible $1/N$ signal.

**Status: DERIVED, NOT YET REFEREED.** The three irreducible families and the
displayed combinatorial envelope have been checked algebraically, but the full
case inventory should be independently audited before this replaces the iid
bound.

## 5. Matching attacks and necessary resource dependence

### 5.1. Exact one-block POLYVAL attack

Consider one user, empty tweak, and the one-block plaintext $0^n$. For the
concrete POLYVAL padding used by HCTR2, the hash of the empty right part has the
form

$$
H_h(\varepsilon,\varepsilon)=c h,
$$

where, under the paper's little-endian field convention,

$$
c=x^{1-n}\in\mathbb F_{2^n}^{\times}.
$$

The HCTR2 specification explicitly uses $x^{n-1}\ne1$, hence $c\ne1$.
With

$$
h=\pi(0),
$$

the ciphertext is

$$
C=\pi(ch)\mathbin\oplus ch.
$$

If $h=0$, then $C=0$ surely; this branch has probability $1/N$. If
$h\ne0$, then $ch$ is a nonzero input distinct from $0$, and the uniform
permutation condition gives one further aggregate probability $1/N$ that
$\pi(ch)=ch$. Therefore

$$
\Pr_{\mathrm{real}}[C=0]=\frac2N,
\qquad
\Pr_{\mathrm{ideal}}[C=0]=\frac1N.
$$

More precisely,

$$
\Pr_{\mathrm{real}}[C=z]
=
\begin{cases}
2/N,&z=0,\\[2mm]
(N-2)/(N(N-1)),&z\ne0.
\end{cases}
$$

The exact statistical distance is consequently

$$
\delta(C_{\mathrm{real}},C_{\mathrm{ideal}})=\frac1N.
$$

This law has an especially simple honest representative:

$$
\mathcal L(C_{\mathrm{real}})
=
\left(1-\frac1{N-1}\right)U
+
\frac1{N-1}\delta_0,
$$

where $U$ is uniform on $\{0,1\}^n$.

For $a$ independently keyed users, let the distinguisher query this same
plaintext once per user and accept if at least one ciphertext is zero. Its
exact gap is

$$
\boxed{
(1-1/N)^a-(1-2/N)^a.}
$$

For $a=o(N)$ this is $a/N+O(a^2/N^2)$. Hence a bound that grants one
query to each of $u$ users must depend on $u$ in this regime. Under a global
query budget, the same fact is written as a necessary $q/N$ term because
$a\le q$.

**Status: PROVED EXACTLY.** This attack is specific to the concrete POLYVAL
padding relation above; it must not be asserted for an arbitrary regular hash
family without rechecking the coefficient.

### 5.2. Exact long-stream collision attack

Make one known-plaintext encryption query to user $i$ whose XCTR tail exposes
$r_i$ complete blocks. From the plaintext and ciphertext, the distinguisher
recovers these stream blocks as the XOR of the corresponding right halves.

In real HCTR2 they are

$$
Y_j=\pi(S\mathbin\oplus\operatorname{bin}(j)),
\qquad 1\le j\le r_i.
$$

The counter inputs are distinct, so the $Y_j$ are always distinct. For one
fresh query to an ideal wide-block permutation, the corresponding visible tail
is uniform, and its complete blocks are iid uniform $n$-bit strings. Thus the
test for a repeated tail block has exact gap

$$
1-\frac{(N)_{r_i}}{N^{r_i}}.
$$

Across independent users, test whether any user's tail contains a collision.
The exact gap is

$$
\boxed{
1-\prod_i\frac{(N)_{r_i}}{N^{r_i}}.}
$$

In the sparse regime $\sum_i r_i^2=o(N)$,

$$
1-\prod_i\frac{(N)_{r_i}}{N^{r_i}}
=
\frac1N\sum_i\binom{r_i}{2}
+
O\!\left(
  \frac{\sum_i r_i^3+(\sum_i r_i^2)^2}{N^2}
\right).
$$

This proves the necessity of a within-user quadratic profile. In particular,
if $r_i$ is comparable with $\sigma_i$, then the correct scale is

$$
\frac{\sum_i\sigma_i^2}{N},
$$

not $u\sigma^2/N$ and not a cross-user collision term.

Nandi's more general hash--counter--hash attack uses $q$ nonadaptive queries
of $\ell+1$ blocks and reaches order $\ell^2q^2/N$, showing that the worst-case
single-user order $\sigma^2/N$ is optimal. See
[Improving upon HCTR and matching attacks for Hash-Counter-Hash](https://eprint.iacr.org/2008/090.pdf).

**Status: PROVED EXACTLY for the displayed one-query-per-user test.** The
generic Nandi attack supplies the broader order-tightness result.

## 6. Signed and exact-likelihood representatives

### 6.1. Exact transcript expression

For a fixed deterministic environment $e$, let $P_e$ and $Q_e$ be the real
and ideal transcript laws and define

$$
L_e(\tau)=\frac{P_e(\tau)}{Q_e(\tau)}
$$

on the support of $Q_e$. Then

$$
\delta(P_e,Q_e)
=
\frac12\mathbb E_{\tau\leftarrow Q_e}
  \left|L_e(\tau)-1\right|.
$$

After the hash key and unused last-block bits are introduced as hidden
coordinates, a transcript specifies inferred permutation input-output pairs.
The real likelihood is the ideal likelihood multiplied by the normalized
indicator that all inferred inputs and all inferred outputs are compatible
with one permutation.

For independent users, the full likelihood ratio factors by user after a full
transcript has fixed each projected query list:

$$
L_e(\tau)=\prod_i L_{e,i}(\tau_i).
$$

This remains useful under adaptive interleaving: the factorization is a
statement about the mass of a fixed complete transcript, not about the
environment choosing users nonadaptively.

### 6.2. Rook and partition expansion

The H-coefficient and bad-event proofs replace every incompatibility by a
positive union bound. The signed route instead expands the injectivity
indicator by inclusion--exclusion. Schematically,

$$
\mathbf 1_{\mathrm{injective}}
=
1
-\sum_{e}\mathbf 1_e
+\sum_{e<f}\mathbf 1_{e\cap f}
-\cdots,
$$

where an edge $e$ is an equality between two inferred inputs or two inferred
outputs. Input and output edges form a bipartite rook or gain graph. Terms are
first pushed through the map to the visible transcript and combined there;
only then is an $L^1$ norm taken.

The ordered-distinct hidden-seed law contributes a centered diagonal term of
the same kind. A signed representative can therefore combine the seed
correction with $L$-pinned collision terms instead of choosing between the
iid-seed and direct-distinct honest couplings.

This manipulation is sound in the repository's virtual-PDS theory: signed
mass is not called a probabilistic coupling, transcript pushforward equality
is required, and the final virtual $L^1$ certificate upper-bounds the ordinary
random-system advantage.

### 6.3. What the signed method already explains

The exact one-block law has centered likelihood

$$
L(z)-1
=
\begin{cases}
1,&z=0,\\[1mm]
-1/(N-1),&z\ne0.
\end{cases}
$$

Thus the positive spike and the negative background cancel before absolute
values, leaving exactly $1/N$. A collision-union proof does not expose this
calculation nearly as directly.

For a long query, the natural first visible proxy is the uniform
collision-free tail law

$$
\frac{N^{r}}{(N)_r}
\mathbf 1[\text{the }r\text{ recovered tail blocks are distinct}],
$$

whose exact distance from iid uniform is
$1-(N)_r/N^r$. The real HCTR2 tail is supported on the same collision-free
set, which is enough for the matching attack. We do not claim here that its
entire marginal law equals this uniform-injection proxy; any residual bias is
part of $R_e$ below.

These two components strongly suggest that a sharp proof should keep a
visible proxy containing:

1. the centered one-block POLYVAL spike;
2. the within-query stream-collision polynomial; and
3. cross-query connected diagrams that encode equal counter sites.

All isolated hidden collisions that do not alter a visible relation should
cancel from the proxy.

### 6.4. The missing theorem

Let $C_e$ denote the proposed visible proxy and write

$$
L_e= C_e+R_e.
$$

The desired bound is

$$
\operatorname{Adv}_{\mathrm{mu}}
\le
\sup_e
\left(
  \frac12\mathbb E_{Q_e}|C_e-1|
  +
  \frac12\mathbb E_{Q_e}|R_e|
\right).
$$

The first term should recover the exact attacks above and give the sharp
finite interpolation of the dominant collision statistic. The unresolved
step is a uniform estimate for $R_e$ after summing all connected diagrams with
three or more collision constraints and all hash-root diagrams.

No bound of the form

$$
\mathbb E|R_e|=o\!\left(
  \frac{a+\sum_i\sigma_i^2}{N}
\right)
$$

has been proved. Adaptivity, encryption/decryption asymmetry, truncated final
XCTR blocks, and polynomial-root equations must all be handled without taking
absolute values too early.

**Status: OPEN.** Signed representatives have supplied a cleaner target and
the exact dominant atoms, but not yet a better general HCTR2 theorem.

## 7. Comparison

The following table compares information-theoretic terms. Computational
statements additionally contain the appropriate single-user or multi-user
SPRP advantage of the block cipher.

| Method | Single-user information term | Multi-user information term | Status |
|---|---:|---:|---|
| Original HCTR2 H-coefficient proof | $(3\sigma^2+2q\sigma+q^2+7\sigma+2)/(2N)$ | not given there | published |
| Common-carrier conditional equivalence | $(3\sigma^2+2q\sigma+7\sigma+2)/(2N)$ | $[3\sum_i\sigma_i^2+2\sum_iq_i\sigma_i+7\sigma+2a]/(2N)$ | derived |
| Raw-tape LM coupling | $(3\sigma^2+2q\sigma+7\sigma+2)/(2N)$ | — | verified locally |
| 2026 H-coefficient MU proof | specialization not the best SU formula | $(3\omega\sum_i\sigma_i^2+4n\sigma)/N$ | published |
| Tagged raw-tape coupling | same best local SU formula | $[3\sum_i\sigma_i^2+2\sum_iq_i\sigma_i+7\sigma+2a]/(2N)$ | derived |
| Ordered-distinct refinement | $B_1^*$ | $\sum_iB_i^*$ | derived; unaudited |
| Signed rook / exact likelihood | exact one-block and long-query proxy terms | same proxies factor by user | remainder open |

For POLYVAL, $\omega=1$. Using only $q_i\le\sigma_i$, the tagged coupling's
quadratic envelope has coefficient $5/2$ in
$\sigma_{\max}\sigma/N$, compared with coefficient $3$ in the published
multi-user theorem. For long queries, where $q_i/\sigma_i$ is small, its leading
coefficient approaches $3/2$, a factor two below the published coefficient.
Its linear term is also much smaller than $4n\sigma/N$ after the two papers'
block-accounting conventions are aligned.

These comparisons must be read with their status labels. The 2026 theorem is
published; the tagged coupling is a new paper-level derivation awaiting an
independent case audit. The signed route is not yet a theorem at all.

The attacks give the benchmark that no proof can beat in order:

$$
\operatorname{Adv}_{\mathrm{mu}}
=
\Omega\!\left(
  \min\!\left\{
    1,
    \frac{a+\sum_i r_i^2}{N}
  \right\}
\right)
$$

for appropriate query profiles. Consequently, the principal remaining room
is in constants, lower-order terms, and a sharper profile statistic—not in
removing all active-user or within-user dependence.

## 8. Next proof obligations

The work should proceed in this order.

1. **Audit the tagged coupling.** Recheck every single-user first-failure slot
   under a globally adaptive user schedule and verify the precise primitive
   substitution budget $\sigma+2a$.
2. **Audit the ordered-distinct refinement.** Confirm that the listed three
   $L$-pin families are exhaustive and verify
   $R_{L,i}\le M_i+q_i(M_i-q_i)$ with encryption and decryption interleaved.
3. **Formalize the common-carrier CE games.** Realize the common raw seed, the two
   deterministic shadow representatives, and the universal first-correction
   MBO in the CR18 interface; the pen-and-paper mass identity is closed in
   `HCTR2_CE_RAW_TAPE.md`.
4. **Write the exact visible likelihood.** Express the injection constraints
   as a partition-lattice or rook polynomial before any triangle inequality.
5. **Choose a projectively consistent proxy.** It must include the one-block
   spike and the stream-collision law and must define one virtual PDS for all
   adaptive environments, not a different signed measure for each transcript.
6. **Bound the connected remainder.** Classify two-edge, three-edge, hash-root,
   and truncation diagrams. Prove an explicit finite $L^1$ or $L^2$ bound.
7. **Compare constants with attacks.** For each resource profile, compare the
   final upper bound with the exact zero-count and tail-collision tests.
8. **Only then formalize the signed improvement.** No signed-bound Lean claim
   should precede closure of the connected remainder; the already closed
   common-carrier CE packaging is a separate task.

## 9. Sources

- The Maurer--Lanzenberger random-system notation and representative coupling
  theory used here are summarized in
  [FOUNDATIONS.md](../FOUNDATIONS.md), based on
  [Lanzenberger's dissertation](<../papers/thesis (1).pdf>) and
  [Lanzenberger--Maurer](../papers/LanMau20.pdf).
- Crowley, Huckleberry, and Biggers,
  [HCTR2](../papers/2021-1441.pdf).
- Chen, Hiraga, Mouha, Naito, Sasaki, and Sugawara,
  [Beyond-Birthday-Bound Security with HCTR2](https://eprint.iacr.org/2026/085).
- Nandi,
  [Improving upon HCTR and matching attacks for Hash-Counter-Hash](https://eprint.iacr.org/2008/090.pdf).
- Local complete coupling derivation:
  [HCTR2_COUPLING_PROOF.md](../papers/notes/HCTR2_COUPLING_PROOF.md).
- Conditional-equivalence theorem:
  [Conditional Equivalence for HCTR2 on a Common Random
  Tape](../papers/notes/HCTR2_CE_RAW_TAPE.md).

## Appendix A. Alternative Completed-Response Representative

An alternative representative first samples each ideal class response without
replacement and then equalizes the good transcript fibers by a thinning tape.
Its construction and telescoping mass identity are recorded in
[A Completed-Response Conditional-Equivalence Representative for
HCTR2](../papers/notes/HCTR2_CE_CR18.md).
