# Appendix: A Completed-Response Conditional-Equivalence Representative for HCTR2

> **Correction (2026-08-06).** Sections A.2-A.5 correctly construct the two
> completed-response games and prove equality of their pre-winning masses.
> That equality is symmetric game equivalence; it does not by itself prove the
> one-sided CR18 factorization used in A.6. Moreover, the factor `alpha_q`
> bounds a freshly sampled response pin but not the hidden-key fibre after the
> response is fixed. The complete conservative strict-CE argument, including
> the required balancing rejection and fixed-completion fibre count, is now in
> [A Blind Conditional-Equivalence Proof for HCTR2](HCTR2_CE_BALANCED.md).
> Accordingly, (A.2) and the inference in A.6 below are retained as historical
> targets, not as established consequences of A.16-A.18.

This appendix records a second conditional-equivalence representative for the
HCTR2 comparison. Its ideal game samples the tweakable permutation response
before testing the monotone condition. The construction gives a direct
counting proof on canonical permutation fibers.

The principal HCTR2 theorem and proof are given in
[Conditional Equivalence for HCTR2 on a Common Random
Tape](HCTR2_CE_RAW_TAPE.md).

## A.1. Setting and Result

Let

$$
N=2^n,
$$

let $\mathbf H$ be HCTR2 using one uniform $n$-bit permutation, and let
$\widetilde{\mathbf T}$ be the ideal variable-input-length tweakable
permutation. Queries are adaptive and bidirectional, with at most $q$
construction queries and total block work at most $\sigma$.

Define

$$
\alpha_q=\frac{N}{N-q+1}.
\tag{A.1}
$$

The completed-response representative proves

$$
\operatorname{Adv}_{q,\sigma}
  (\mathbf H,\widetilde{\mathbf T})
\le
\min\!\left\{
1,
\alpha_q
\frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}
\right\}.
\tag{A.2}
$$

## A.2. Records and Good Completions

A query record contains its tweak, length, plaintext, and ciphertext. A query
is fresh if its queried side has no partner in an earlier record of the same
tweak–length class. Exact repeats and inverse queries replay the established
partner.

For every fresh query $s$, the HCTR2 equations infer the primitive pairs

$$
(MM_s,UU_s),
\qquad
(S_{s,j},Y_{s,j})\qquad(1\le j<m_s),
\tag{A.3}
$$

together with

$$
(\operatorname{bin}(0),h),
\qquad
(\operatorname{bin}(1),l).
\tag{A.4}
$$

For a transcript $(x^i,y^i)$ and hidden values $(h,l,D^i)$, let

$$
\mathsf{Good}_i(x^i,y^i,h,l,D^i)
\tag{A.5}
$$

mean that the inferred domain entries in (A.3)–(A.4) are pairwise distinct
and the inferred range entries are pairwise distinct. Let

$$
\widehat N_i(x^i,y^i)
=
\#\{(h,l,D^i):\mathsf{Good}_i(x^i,y^i,h,l,D^i)\}.
\tag{A.6}
$$

The conditions $\neg\mathsf{Good}_i$ are prefix-monotone.

## A.3. The Ideal Game

Let $\widehat F$ sample the following independent data:

1. a uniform permutation for every tweak–length class;
2. uniform $h,l\in\{0,1\}^n$;
3. the unused suffix bits $D^i$ required by partial final blocks.

Its visible response is the response of the sampled class permutation. Its
monotone condition fires precisely when (A.5) fails.

If the fresh class of query $s$ already contains $k_s$ records, its visible
response is uniform on

$$
2^{\ell_s}-k_s
\tag{A.7}
$$

unused values. Repeats and inverse queries are deterministic.

## A.4. The Real Game and Thinning Ratios

Let $\widehat G$ sample one uniform permutation $\pi$ and an independent
thinning tape. Its visible response is ordinary HCTR2 evaluated with $\pi$.

Before fresh query $s$, let $u_{s-1}$ be the number of primitive sites already
fixed by the transcript, let $m_s$ be the number of new primitive pairs, and
let $k_s$ be the number of occupied responses in its ideal class. Define

$$
r_s
=
\frac{
  \prod_{j<m_s}(N-u_{s-1}-j)
}{
  (2^{\ell_s}-k_s)2^{nm_s-\ell_s}
}.
\tag{A.8}
$$

For a replay, set $r_s=1$. At the first fresh query, include the initial
factor

$$
1-\frac1N,
\tag{A.9}
$$

which reconciles two independent uniform values $(h,l)$ with the ordered
distinct pair

$$
(\pi(\operatorname{bin}(0)),\pi(\operatorname{bin}(1))).
$$

The counting inequality

$$
0\le r_s\le1
\tag{A.10}
$$

follows by comparing the available global-permutation extensions with the
available ideal-class responses. The monotone condition of $\widehat G$ fires
if the inferred pairs cease to be injective or if the thinning coin at a
fresh step is rejected.

Stripping the condition leaves the original visible laws:

$$
\operatorname{ignore}(\widehat F)
  \in\widetilde{\mathbf T},
\qquad
\operatorname{ignore}(\widehat G)
  \in\mathbf H.
\tag{A.11}
$$

## A.5. Equality of Good Transcript Masses

Fix a transcript $(x^i,y^i)$. Let $c'_s$ denote the ideal fresh-response
factor, including the hidden suffix multiplicity, and let $c_s$ denote the
corresponding global-permutation extension factor. Equation (A.8) is

$$
r_s=\frac{c'_s}{c_s}.
\tag{A.12}
$$

Summing over the hidden tuples in (A.6) gives

$$
\begin{aligned}
&\Pr^{\widehat F}
  [Y^i=y^i,A_i=0\mid X^i=x^i]\\
&\qquad=
\widehat N_i(x^i,y^i)
N^{-2}
\prod_{s\text{ fresh}}c'_s
\prod_{s\text{ replay}}
  \mathbf 1[y_s=\mathsf{replay}_s],
\end{aligned}
\tag{A.13}
$$

and

$$
\begin{aligned}
&\Pr^{\widehat G}
  [Y^i=y^i,A_i=0\mid X^i=x^i]\\
&\qquad=
\widehat N_i(x^i,y^i)
\frac{1}{(N)_{u_i}}
\prod_{s\le i}r_s
\prod_{s\text{ replay}}
  \mathbf 1[y_s=\mathsf{replay}_s].
\end{aligned}
\tag{A.14}
$$

The falling factorial decomposes as

$$
(N)_{u_i}
=N(N-1)
\prod_{s\text{ fresh}}
\prod_{j<m_s}(N-u_{s-1}-j).
\tag{A.15}
$$

Substituting (A.8)–(A.9) into (A.14) and using (A.15) gives (A.13). Hence

$$
\Pr^{\widehat F}
  [Y^i=y^i,A_i=0\mid X^i=x^i]
=
\Pr^{\widehat G}
  [Y^i=y^i,A_i=0\mid X^i=x^i]
\tag{A.16}
$$

for every query and response sequence. The two games therefore have the same
pre-winning behavior.

## A.6. Historical Winning-Probability Target

Orient Maurer's conditional-equivalence theorem (CR18, Theorem 4.17) with
$\widehat F$ first. A hash-key collision has the same POLYVAL root bound as in
the principal proof. If a collision equation pins the next ideal response
after $k$ values have been used in its class, then

$$
\Pr[\text{pin}]
\le
\frac1{N-k}
\le
\frac{\alpha_q}{N}.
\tag{A.17}
$$

The original target was to apply (A.17) to the HCTR2 collision inventory and
deduce

$$
\nu(\widehat F)
\le
\alpha_q
\frac{3\sigma^2+2q\sigma+7\sigma+2}{2N}.
\tag{A.18}
$$

This deduction is not valid as stated. Equation (A.17) controls a response pin
at the step where that response is sampled. Strict CE additionally needs a
history-wise factorization. After earlier responses are fixed, some grey
response-pin rows become polynomial exclusions in the persistent hash key;
for example, $S_{r,i}=S_{s,j}$ can exclude up to
$\max(d_r,d_s)$ keys. The factor $\alpha_q$ does not cover that change.

Moreover, (A.16) proves equality between two monitored games, whereas CR18
Definition 4.19 requires one monitored source to factor through one ordinary
causal target. Thus (A.11), (A.16), and the proposed (A.18) do not by
themselves prove (A.2). The balanced proof and its corrected bound are given
in [HCTR2_CE_BALANCED.md](HCTR2_CE_BALANCED.md).

## A.7. Proof Status

**DERIVED.** The representative, thinning identity, and two-game good-mass
equality in Sections A.2-A.5 are complete pen-and-paper arguments.

**OPEN.** The bound (A.2) is not proved by this appendix. The missing strict-CE
factorization and fixed-completion fibre count are handled, with a more
conservative bound, in [HCTR2_CE_BALANCED.md](HCTR2_CE_BALANCED.md). The Lean
construction remains open.
