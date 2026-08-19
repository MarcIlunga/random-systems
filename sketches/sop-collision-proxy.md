# Collision-proxy route to a sharp bound for the XOR of two permutations

Status: finite theorem fully formalized in Lean, with no admissions.

Date: 2026-08-01.

The representative-first, elementary proof design is developed separately in
[`sop-elementary-representatives.md`](./sop-elementary-representatives.md).
Its main objects are the exact compatible-explanation deck, the equivalent
count-first SoP/URF representatives, and the interpretation of this note's
proxy as URF with one randomly planted answer collision.

## 1. Problem and proposed result

Let `G = F_2^n`, let `N = |G| = 2^n`, and consider the random function

```text
F(x) = pi_1(x) XOR pi_2(x),
```

where `pi_1` and `pi_2` are independent uniform permutations of `G`.  The
goal is to bound the maximum adaptive `q`-query distinguishing advantage
between `F` and a uniform random function.

Throughout the finite estimate, assume

```text
N >= 1000,
2 <= q < N/2,
M = binom(q,2),
lambda = M/N.
```

The proved headline is

```text
Adv(q,N) = O(min(q^2/N^2, q/N^(3/2))).
```

The derivation below gives a stronger, explicit, two-sided statement.  Under
the ideal law, let

```text
K(y) = number of pairs i < j such that y_i = y_j.
```

Define

```text
A_col(q,N)
  = N / (2(N-1)^2) * E_Q |K - lambda|.
```

Then

```text
|Adv(q,N) - A_col(q,N)| <= Delta(q,N),
```

where the tight compiled remainder is

```text
Delta(q,N)
  = 1/2 * sqrt(
      16 binom(q,3) / ((N-1)^3 (N-2)^3)
      + (1152/7) q^4/N^6
      + 8 q^4/N^8
    ).
```

The simpler rounded corollary replaces `1152/7` by `200` and `8` by `16`.
Consequently, the exact terminal theorem is

```text
Adv(q,N)
 <= min(
      M/(N-1)^2,
      sqrt(M)/(2(N-1)^(3/2))
    )
    + Delta(q,N).
```

This proves the desired asymptotic envelope in Lean.  It also improves
the initially expected `O(q/N^2)` higher-order remainder to `O(q^2/N^3)`.

## 2. Lanzenberger PDS model and representative choice

The random systems in this argument are not identified with particular
implementations.  A random system is a transcript-equivalence class `[S]` of
probabilistic discrete systems (PDSs).  A PDS is a finite nonnegative
distribution over deterministic discrete systems (DDSs) with one common
bounded domain.  The top-level systems here have weight one.  Successor PDSs
selected by a first answer are subdistributions and must retain their actual
weights; they are not normalized conditional laws.

For finite alphabets and a fixed query horizon, the representative class can
be viewed as a convex polytope:

```text
Rep(B) = all nonnegative laws mu on deterministic response trees such that

  for every fixed input sequence x[1..d] and output sequence y[1..d],
  sum of mu(s) over trees s agreeing with (x[1..d],y[1..d])
    = the behavior mass B(x[1..d],y[1..d]).
```

Lanzenberger's nonadaptive characterization says these fixed-path constraints
are exactly the observational constraints.  They determine the law along
every path that one execution can traverse, but they do not determine the
correlation between mutually exclusive paths.  That unobservable correlation
is the representative design space.

### 2.1 A URF is not canonically a uniform random-function table

The eager representative samples a complete table

```text
f : G -> G
```

with independent uniform entries.  This is only one representative of the
bounded URF random system.  Another one samples independent uniform values

```text
Z[1], ..., Z[q]
```

and gives `Z[r]` to the `r`-th distinct query, caching it for repeats.  This
fresh-rank PDS has only `q` visible random cells and correlates all
counterfactual query names at the same fresh rank.  Nevertheless, every one
execution sees exactly the URF law.  A position-tape variant consumes the cell
at the absolute position of a fresh query and also reuses the first cell on a
repeat; for exchangeable tape laws it is equivalent as well.

The thesis's one-query example makes the freedom explicit.  On Boolean input
and output, let `zero`, `one`, `id`, and `flip` be the four deterministic
single-query systems.  Every law

```text
V_alpha = alpha * zero
        + alpha * one
        + (1/2-alpha) * id
        + (1/2-alpha) * flip,

0 <= alpha <= 1/2,
```

represents the same uniform-bit random system.  At `alpha = 0` the two
counterfactual answers are opposite; at `alpha = 1/2` they are identical; at
`alpha = 1/4` they are the independently sampled table.  The two extremes
even have disjoint PDS supports and static distance one, while their random
systems are identical.  The single-query restriction is essential.  For more
than one distinct query, one constant bit would be visible; the fresh-rank
representative instead uses one independent bit per fresh rank.

More generally, at a history `h`, all potential next fresh inputs have the
same uniform answer marginal.  Their counterfactual answers may be coupled in
any way:

- product coupling gives the full random table;
- diagonal coupling gives one shared fresh-rank value;
- a twisted diagonal uses `phi(h,x,Z[r])`, where every `phi(h,x,.)` is a
  permutation of the output alphabet;
- an arbitrary multi-marginal coupling gives the most general branch law.

The successor systems below those answers can again be coupled arbitrarily,
recursively.  This is the construction used in Lanzenberger's attainment
theorem: choose representatives of every `(first query, first answer)`
successor subdistribution, preserve their unnormalized branch weights, and
then choose a joint distribution across first-query branches.  A single run
selects only one such branch, so every joint with the required marginals is an
equivalent representative.

### 2.2 The representatives used for SoP

For `q <= N`, sample independent uniform ordered injections

```text
A, B : Fin q -> G
```

and define the real fresh-output tape

```text
Y[i] = A[i]^-1 * B[i].
```

For XOR this is `A[i] XOR B[i]`.  Let `Z : Fin q -> G` have independent
uniform coordinates.  Turn either tape into a deterministic system `D_t` by
giving tape cell `r` to the `r`-th distinct query and caching repeats.  Then

```text
[SoP_q] = [law(D_Y)],
[URF_q] = [law(D_Z)].
```

These are honest Lanzenberger PDS representative equalities, not merely a
fixed-schedule heuristic.  Equality on every fixed input sequence gives full
adaptive equivalence.  Conversely, one fixed injective sequence of `q`
queries reads the entire tape, and the map `t -> D_t` is injective.  Therefore

```text
Adv(q,N) = delta(law(D_Y), law(D_Z))
         = TV(law(Y), law(Z)).
```

This representative pair already attains the class distance.  No alternative
representative can reduce it, because the fixed injective schedule is an
observable pushforward and already has this distance.  More elaborate
representatives can still make the exact distance easier to decompose or
couple; they cannot change its value.

The compiled endpoints are

- `adv_prf_eq_fresh_tape_distance_of_le_card` in
  [`SoP2.lean`](../RandomSystems/SoP/SoP2.lean);
- `sop_advantage_eq_half_l1_compatible_count_of_le_card` in the same file.

The Lean implementation currently realizes the DDS and transcript machinery
through the repository's CR18 carrier.  That is an encoding choice.  The
mathematical step is the Lanzenberger move from the natural PDSs to equivalent
fresh-tape representatives.

Thus, if `P` is the real output-tape law and `Q` is the uniform law on `G^q`,
then

```text
Adv(q,N) = TV(P,Q) = 1/2 E_Q |L-1|,
L(y) = P(y)/Q(y).
```

No loss is incurred in either direction.

### 2.3 General representative families worth keeping

The fresh tape is one chart in a larger atlas.

1. Full-tree representative.  Sample every counterfactual branch
   independently.  A full URF table is the stateless special case.
2. Shared-latent representative.  Generate many counterfactual branches from
   one latent variable while preserving every branch marginal.  Rank tapes,
   twisted rank tapes, and quantile/common-part couplings fit here.
3. Recursive transport representative.  At every history, choose an arbitrary
   joint distribution of the per-query successor PDSs.  This covers general,
   nonuniform and stateful random systems, not only query-symmetric oracles.
4. Block-first representative.  Choose a classifier label, then sample from a
   common conditional law inside its fiber.  If real and ideal share the
   conditional law given the label, their entire distance is the distance
   between label distributions.
5. Convex mixtures.  Any mixture of equivalent representatives is again an
   equivalent representative.  Mixtures can trade support size, symmetry, and
   coupling convenience without changing behavior.

For a general behavior, a single rank tape exists only when the fixed-path
laws have the required query-name symmetry and prefix consistency.  The
recursive transport construction is the most general construction within the
finite common-domain model.  It is also the right place to use Lanzenberger's
arbitrary-weight successor distributions; normalizing each branch would
destroy its true probability mass.

For a finite horizon, representative search is literally an optimal-transport
problem over two convex polytopes:

```text
minimize    delta(mu,nu)
subject to  mu in Rep(real behavior),
            nu in Rep(ideal behavior).
```

Equivalently, maximize the agreement probability of a joint distribution
whose two marginals may be chosen anywhere in the two representative classes.
Lanzenberger's Theorems 2.31 and 2.32 say that the optimum is attained and is
exactly the adaptive advantage.  The recursive proof is an existence
algorithm for the optimizer.  In applications, the raw polytope is too large;
query symmetry, shared latent variables, and orbit classifiers are ways to
compress it without discarding the representative freedom.

The theorem requires the finite, bounded, common-domain setting.  The
`q`-bounded SoP and URF systems satisfy it exactly.  It should not be read as an
attainment theorem for arbitrary varying-domain partial systems.

## 3. Exact pair marginal and degree-two projection

For two distinct queries, the real pair likelihood ratio is

```text
P(y_i,y_j)/Q(y_i,y_j)
  = N/(N-1)                  if y_i = y_j,
  = N(N-2)/(N-1)^2           if y_i != y_j.
```

Indeed, the two hidden permutation differences are independent and uniform
over the `N-1` nonzero group elements.  Their XOR is zero with probability
`1/(N-1)` and equals a fixed nonzero value with probability
`(N-2)/(N-1)^2`.

The centered pair kernel is therefore

```text
h(y_i,y_j)
  = N/(N-1)^2 * (1{y_i=y_j} - 1/N).
```

Every one-coordinate marginal is uniform.  Hence the exact degree-two
Hoeffding/ANOVA projection of `L-1` is

```text
H2(y)
  = sum_{i<j} h(y_i,y_j)
  = N/(N-1)^2 * (K(y) - M/N).
```

Write

```text
L - 1 = H2 + R.
```

The remainder `R` contains only interactions involving at least three
coordinates.  In an `L2(Q)` ANOVA or Walsh decomposition, `R` is orthogonal to
the constant, singleton, and pair levels.

## 4. The collision-proxy distribution

Define an intermediate distribution `C` relative to `Q` by

```text
C(y)/Q(y) = 1 + H2(y)
          = 1 + N/(N-1)^2 * (K(y)-lambda).
```

This is a genuine probability distribution:

1. `E_Q H2 = 0`, because `E_Q K = M/N`.
2. Its minimum occurs at `K=0` and equals

   ```text
   1 - M/(N-1)^2.
   ```

3. For every `q <= N`, this is at least

   ```text
   (N-2)/(2(N-1)) >= 0.
   ```

The proxy density depends only on `K`.  Therefore `C` and `Q` have the same
conditional law given `K`.  A concrete maximal coupling is:

1. Maximal-couple the one-dimensional `K` laws.
2. When the collision counts agree, sample the same transcript uniformly from
   that collision-count fiber.

Its disagreement probability is exactly

```text
TV(C,Q)
  = 1/2 E_Q |H2|
  = A_col(q,N).
```

The real-to-proxy distance satisfies

```text
TV(P,C)
  = 1/2 E_Q |R|
  <= 1/2 sqrt(E_Q R^2).
```

The triangle and reverse-triangle inequalities give

```text
|TV(P,Q) - TV(C,Q)| <= TV(P,C),
```

which is the source of the two-sided approximation theorem.

This is a fixed-horizon `q`-tape proxy.  It need not form a single
projectively consistent oracle for all values of `q`; the exact adaptive-tape
reduction means that this is irrelevant to the `q`-query advantage theorem.

### 4.1 Honest PDS interpretation of the proxy

`C` is a third random system, not an equivalent representative of either the
real system or URF.  A fixed injective query sequence observes the entire tape,
so replacing `P` by `C` inside the real equivalence class would be invalid.

There is nevertheless a fully Lanzenberger-native three-system construction.
Let `kappa` be any fine classifier on output tapes such that the real
compatible count is constant on every `kappa` fiber.  The affine-coordinate
orbit classifier already formalized in the repository has this property.
Collision count `K` is constant on those orbits, because coordinate
permutations and output bijections preserve equality.

Write the real, proxy, and ideal masses of an orbit `omega` as

```text
r[omega], c[omega], u[omega].
```

If `k(omega)` is its collision count and

```text
a(k) = 1 + N/(N-1)^2 * (k-M/N),
```

then the proxy orbit mass is

```text
c[omega] = a(k(omega)) * u[omega].
```

All three tape laws are uniform inside each fine orbit.  Hence each has the
honest block-first representative

```text
sample omega with its own orbit mass;
sample y uniformly from kappa^-1(omega);
run the fresh-rank or position-tape DDS D_y.
```

The exact distances reduce to label distances:

```text
TV(C,Q) = 1/2 * sum_omega |c[omega]-u[omega]|
        = A_col(q,N),

TV(P,C) = 1/2 * sum_omega |r[omega]-c[omega]|
        = 1/2 * E_Q |R|.
```

A maximal coupling of the labels lifts by sampling one common tape inside a
matched orbit.  This yields honest PDS couplings for `P` versus `C` and `C`
versus `Q`.  The triangle comparison is therefore a comparison of three
random-system representatives, not merely formal density algebra.

The coarse collision label alone is exact for `C` versus `Q`, because these
two laws share their conditional distribution given `K`.  It is generally too
coarse for the real law: the real compatible count can vary among tapes with
the same number of collisions.  The fine orbit label retains that residual
information.  Fourier/ANOVA terms are then signed analytic coordinates for
bounding the honest label discrepancy `r-c`; they are not themselves PDS
representatives.

## 5. Finite collision bounds

Under `Q`, write

```text
K = sum_{i<j} I_ij,
I_ij = 1{y_i=y_j}.
```

The indicators are pairwise independent.  This remains true when two pairs
share one coordinate.  Hence

```text
E_Q K   = M/N = lambda,
Var_Q K = M(N-1)/N^2.
```

Two general mean-absolute-deviation bounds are

```text
E|K-lambda| <= 2 lambda,
E|K-lambda| <= sqrt(Var K).
```

The first follows from nonnegativity of `K`; the second is Cauchy-Schwarz.
They imply

```text
A_col <= M/(N-1)^2,
A_col <= sqrt(M)/(2(N-1)^(3/2)).
```

Thus

```text
A_col
 <= min(
      M/(N-1)^2,
      sqrt(M)/(2(N-1)^(3/2))
    ).
```

The same one-dimensional collision statistic automatically produces the
sparse and dense regimes.

## 6. Exact sparse formula

When `lambda <= 1`, integrality and nonnegativity of `K` give

```text
E|K-lambda| = 2 lambda * Pr[K=0].
```

Moreover,

```text
Pr[K=0] = (N)_q/N^q,
```

where `(N)_q = N(N-1)...(N-q+1)`.  Consequently,

```text
A_col(q,N)
  = M/(N-1)^2 * (N)_q/N^q.
```

This is the quantity already named `spatialReconstructionBound` in
[`SmallQ.lean`](../RandomSystems/Legacy/Applications/SoP/SmallQ.lean).

For `q/sqrt(N) -> 0`, the no-collision probability tends to one, so

```text
Adv(q,N) ~ binom(q,2)/N^2.
```

At `q=2`, the formula gives the exact compiled value

```text
Adv(2,N) = 1/(N(N-1)).
```

## 7. Exact finite collision interpolation

The exact ideal distribution of `K` can be computed from occupancy numbers.
Its probability generating function is

```text
E[z^K]
  = q!/N^q * coefficient_of_t^q in
      (sum_{r=0}^q t^r z^(binom(r,2))/r!)^N.
```

Therefore the finite collision proxy is completely explicit:

```text
A_col(q,N)
  = N/(2(N-1)^2)
    * sum_k |k-M/N| Pr_Q[K=k].
```

This expression interpolates through the birthday transition without choosing
between separate sparse and dense proofs.

## 8. Poisson transition

Suppose

```text
q/sqrt(N) -> c,
lambda = M/N -> c^2/2.
```

The number of monochromatic edges in a uniform `N`-coloring of the complete
graph `K_q` converges to a Poisson random variable `X` of mean `lambda`.  The
formal proof is elementary and internal to this development.  Plant one edge
by copying its left endpoint's color to its right endpoint.  Averaging this
operation is the exact size-biased collision law.  Apart from edges meeting a
planted endpoint, planting changes the count by exactly one, so every fixed
atom satisfies an approximate Poisson recurrence.  The recurrence error
vanishes when `q/N -> 0`; induction begins at the exact birthday-product zero
atom.

For `X ~ Poisson(lambda)`, one has the exact identity

```text
E|X-lambda|
  = 2 lambda * Pr[X=floor(lambda)].
```

Only the finitely many atoms through `floor(lambda)` are needed: a lower-tail
telescope expresses the mean absolute deviation in terms of them.  This
avoids a separate uniform-integrability theorem and handles integer rates
without a boundary exception.  As `N/(N-1)^2 ~ 1/N` and the higher-order SoP
remainder is `o(1/N)` in this regime,

```text
N * Adv(q,N)
  -> lambda * Pr[Poisson(lambda)=floor(lambda)]
```

or

```text
N * Adv(q,N)
  -> lambda * exp(-lambda)
     * lambda^floor(lambda) / floor(lambda)!.
```

At `q ~ sqrt(N)`, `lambda = 1/2`, giving

```text
Adv(q,N) ~ 0.303265.../N.
```

## 9. Normal regime and sharp constant

Suppose

```text
q/sqrt(N) -> infinity,
q < N/2.
```

The universal monochromatic-edge central limit theorem gives

```text
(K-lambda)/sqrt(Var K) -> Normal(0,1).
```

The exact second moment supplies uniform integrability, so

```text
E|K-lambda|
  ~ sqrt(2/pi) * sqrt(Var K).
```

It follows that

```text
A_col(q,N)
  ~ q/(2 sqrt(pi) N^(3/2)).
```

Since

```text
Delta / (q/N^(3/2))
  = O(q/N^(3/2))
  = O(1/sqrt(N))
```

uniformly for `q < N/2`, the remainder is negligible and

```text
Adv(q,N)
  ~ q/(2 sqrt(pi) N^(3/2)).
```

The explicit distinguisher is the collision-threshold test

```text
output real iff K > lambda.
```

Its real-versus-ideal advantage is at least `A_col - Delta`.  Therefore the
same decomposition proves the matching lower bound and the constant
`1/(2 sqrt(pi))`; it is not merely an upper-bound calculation.

The fixed-rate Poisson statement is proved directly by planted-edge
size-biasing.  The dense normal statement uses the separately formalized
local-dependence Stein argument in this repository.

## 10. Fourier control of the higher-order remainder

Let `mu` be the density, relative to uniform measure on `G^q`, of sampling `q`
points without replacement.  The real XoP density is

```text
L = mu * mu.
```

For the Walsh character indexed by `alpha`,

```text
Fourier(L,alpha) = Fourier(mu,alpha)^2.
```

Let `V_k` denote the squared `L2` mass of the level-`k` part of `L-1`:

```text
V_k = sum_{level(alpha)=k} Fourier(mu,alpha)^4.
```

The constant level is one, the singleton level vanishes, and the complete
level-two component is exactly `H2`.  Parseval and orthogonality therefore give

```text
E_Q R^2 = sum_{k>=3} V_k.
```

### 10.1 Exact level three

For three nonzero Walsh masks `a`, `b`, and `c`, the sampling-without-
replacement coefficient is nonzero exactly when

```text
a XOR b XOR c = 0.
```

In that case its value is

```text
2/((N-1)(N-2)).
```

There are `(N-1)(N-2)` ordered nonzero triples satisfying this condition.
Thus

```text
V_3
  = 16 binom(q,3) / ((N-1)^3 (N-2)^3).
```

### 10.2 Levels at least four

Let `B_k` be the maximum magnitude of a level-`k` coefficient of `mu`, and let
`W_k` be the sum of squares of its level-`k` coefficients on `k` coordinates.
Dinur proves, for `k < N/2`,

```text
V_k <= binom(q,k) B_k^2 W_k,
B_k^2 <= 1/binom(N,k),
W_k <= (2(k+1)/N)^(k/2)             for k >= 4.
```

Since

```text
binom(q,k)/binom(N,k) <= (q/N)^k,
```

The formal proof uses the stronger one-dimensional normalized Pascal
recurrence

```text
(N-k) W_(k+1) = k (2 W_k + W_(k-1)).
```

The exact parity-sensitive Pascal bound supplies the two bases. For `n >= 10`
the recurrence then proves

```text
W_k <= 144/N^2 * (1/4)^(k-4),
4 <= k <= 4n+1.
```

Combining this with the exact falling-factorial support ratio, rather than a
worst-case `N-k` denominator, gives

```text
V_k <= 144 q^4/N^6 * (1/8)^(k-4).
```

Therefore the complete medium tail satisfies the stronger compiled estimate

```text
sum_{k=4}^{min(q,4n+1)} V_k
  <= (1152/7) q^4/N^6.
```

For the high tail the proof avoids a separate `W_k <= 1` lemma. It combines
the support multiplicity with the total sampling energy first. Every exposed
factor is then at most `rho = q/N` whenever `2q <= N`, so

```text
sum_{k=4n+2}^q V_k
  <= 2 rho^(4n+2)
  <= 8 q^4/N^8.
```

Combining the three ranges gives

```text
E_Q R^2
 <= 16 binom(q,3) / ((N-1)^3 (N-2)^3)
    + (1152/7) q^4/N^6
    + 8 q^4/N^8.
```

Replacing the last two constants by `200` and `16` gives the shorter rounded
corollary used in comparisons with the literature.

Finally,

```text
TV(P,C)
 <= 1/2 sqrt(E_Q R^2)
 <= Delta(q,N).
```

This is the decisive observation: after removing the exact level-two
collision projection, Dinur's existing `L2` estimates already make the
higher-order tail negligible.  A new cancellation-aware `L1` estimate of size
`O(q^3/N^3)` is not required.

## 11. Comparison with previous bounds

### Dai-Hoang-Tessaro

For XOR2, DHT prove

```text
Adv <= (q/N)^(3/2)
```

in their stated range.  The collision envelope improves it on both sides of
the birthday transition:

```text
q << sqrt(N):  q^2/N^2 instead of q^(3/2)/N^(3/2),
q >> sqrt(N):  q/N^(3/2) instead of q^(3/2)/N^(3/2).
```

### DNS mirror theory

The published DNS independent-permutation result gives

```text
(19q^2 + 8n^3)/N^2.
```

The tightened formal version in [`DNSMirror.lean`](../RandomSystems/SoP/DNSMirror.lean)
gives

```text
(10q^2 + 5n^3)/N^2.
```

The collision proxy has sparse leading coefficient `1/2`, eliminates the
`n^3/N^2` residue, and changes to the smaller `q/N^(3/2)` behavior above the
birthday transition.

### Dinur

Dinur proves

```text
Adv <= q/(2(N-1)^(3/2)).
```

The collision term improves the leading normal constant from

```text
1/2 = 0.500...
```

to

```text
1/(2sqrt(pi)) = 0.282094...
```

For the finite bound, throughout `q < N/2`,

```text
(new high branch + Delta) / Dinur
 < 1/sqrt(2) + sqrt(203)/(2sqrt(N))
 < 0.933                                      for N >= 1000.
```

Safe rounded finite constants are therefore

```text
Adv(q,N)
 <= min(
      0.509 q^2/N^2,
      0.468 q/N^(3/2)
    ).
```

These rounded constants are conveniences; the theorem should retain the exact
`M`, `Delta`, and denominator expressions.

## 12. What is established and what remains open

### Established in the repository

- The Lanzenberger random-system quotient, bounded attainment theorem, and
  optimal representative coupling:
  [`RandomSystemQuotient.lean`](../RandomSystems/RandomSystemQuotient.lean),
  [`BoundedAttainment.lean`](../RandomSystems/BoundedAttainment.lean), and
  [`RandomSystemCoupling.lean`](../RandomSystems/RandomSystemCoupling.lean).
- The full `V_alpha` family of inequivalent-looking PDS representatives of one
  uniform-bit random system: [`Example216.lean`](../RandomSystems/Example216.lean).
- Exact reduction from maximum adaptive advantage to fresh-tape statistical
  distance: [`SoP2.lean`](../RandomSystems/SoP/SoP2.lean).
- Exact compatible-count and half-`L1` characterizations in the same file.
- Generic position-tape PDS constructors, the fixed-input-to-adaptive
  equivalence bridge, and block-uniform representatives:
  [`Equiv.lean`](../RandomSystems/Legacy/Equiv.lean),
  [`Partition.lean`](../RandomSystems/Legacy/Applications/SoP/Partition.lean),
  and [`XoPModel.lean`](../RandomSystems/Legacy/Applications/XoPModel.lean).
- Honest affine-orbit block-first representatives for real XoP and URF,
  together with a lifted optimal coupling of their PDS laws:
  [`Affine.lean`](../RandomSystems/Legacy/Applications/SoP/Affine.lean).
- Exact two- and three-query values in the same file.
- ANOVA projection and reconstruction infrastructure:
  [`XoPANOVA.lean`](../RandomSystems/Legacy/Applications/XoPANOVA.lean).
- Collision-count and spatial-reconstruction infrastructure:
  [`SmallQ.lean`](../RandomSystems/Legacy/Applications/SoP/SmallQ.lean).
- The constrained DNS exact mirror proof:
  [`DNSMirror.lean`](../RandomSystems/SoP/DNSMirror.lean).

### Newly formalized collision-proxy lane

- `XORCollisionProxy.lean`: the exact planted-collision density,
  sparse and dense collision bounds, and the two-sided proxy comparison.
- `XORFourier.lean`: normalized Walsh analysis, inversion, Parseval, and
  convolution.
- `XORInjection.lean`: the ordered-injection PDS representative, exact
  level-zero/one/two decomposition, collision kernel, and broken-cycle
  remainder identity.
- `XORCore.lean`: exact closed-triangle level-three energy.
- `XORTail.lean`: support factorizations, exact forward differences, and
  the normalized one-dimensional Pascal recurrence.
- `XORCoefficient.lean`: the exposed-card merge recurrence and the
  reciprocal-binomial maximal-coefficient theorem, including its zero-link
  boundary.
- `XORPascal.lean`: both unrounded parity branches of Dinur
  Proposition 22.
- `XORBounds.lean`: the finite medium/high summations, exact two-sided
  approximation, and the expanded adaptive advantage theorem.
- `CollisionCountPoissonFixed.lean`: planted-edge size bias, atomwise Poisson
  recurrence, all fixed-rate collision MAD limits, and the scaled collision-
  proxy constant.
- `XORCollisionAsymptotics.lean`: transfer of that constant through the
  vanishing higher-order remainder to the true adaptive advantage, plus the
  matching centered-collision threshold attack.
- `SignedLocalRepair.lean`: an honest normalized pair-and-triple repair proxy,
  its exact finite distance, strict comparison with the earlier proxy bound,
  and the matching two-sided collision-test certificate.

All eight files compile without `sorry`, `admit`, declared axioms, or
`native_decide`. The endpoint axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

### Remaining scope restrictions

- The Fourier calculation is currently for XOR, hence `G = F_2^n`.
- The finite source inequalities assume `N >= 1000` and `q < N/2`.
- Extending the proof to arbitrary finite abelian groups requires a character-
  theoretic generalization of the maximal-coefficient bound.
- Extending beyond `q < N/2` requires new large-level Fourier estimates or a
  separate saturation argument.

The finite envelope, the fixed-rate Poisson interpolation, and the dense
normal limit are all formalized.  The remaining scope restrictions concern
the carrier and large-query range, not an omitted birthday-scale limit.

## 13. Formalization receipt

The representative and analytic routes are both closed. The final Lean
endpoints are:

- `abs_advantage_sub_collisionAdvantage_le` for the exact two-sided
  approximation;
- `adaptiveTranscriptAdvantage_le_explicit` for the fully expanded
  tight bound;
- `adaptiveTranscriptAdvantage_le_explicit_rounded` for the shorter
  `200`/`16` remainder presentation.

The proof is representative-first: ordered-injection fresh tapes identify the
exact SoP law, the planted-collision density isolates the visible degree-two
effect, and Walsh coordinates are used only to bound the honest distance from
that proxy. There is no conditioning loss or bad-event deletion.

The sharp fixed-rate endpoints are:

- `tendsto_card_mul_adaptiveTranscriptAdvantage_fixedPoisson`, giving
  `N * Adv -> lambda * Pr[Poisson(lambda)=floor(lambda)]` for every fixed
  nonnegative rate;
- `tendsto_card_mul_collisionThresholdTestGap_fixedPoisson`, proving the same
  limit for one explicit distinguisher;
- `tendsto_collisionThresholdTestGap_div_adaptiveAdvantage_fixedPoisson`,
  proving `attack gap / optimal advantage -> 1` at every positive fixed rate;
- the existing dense normal endpoint, giving the limiting coefficient
  `1/(2 sqrt(pi))`.

What remains open is a single finite formula proved to dominate every
published bound in every query regime, extension beyond `q < N/2`, and an
arbitrary-finite-abelian-group version.  Those claims are deliberately not
inferred from the now-complete fixed-rate asymptotics.

## 14. Sources

- David Lanzenberger, *A Theory of Random Systems, Games, and Hardness
  Amplification* (ETH dissertation, 2023):
  [`thesis (1).pdf`](../papers/thesis%20(1).pdf).
- David Lanzenberger and Ueli Maurer, "The Coupling Theorem and its
  Applications": [`LanMau20.pdf`](../papers/LanMau20.pdf).
- Itai Dinur, "Tight Indistinguishability Bounds for the XOR of Independent
  Random Permutations by Fourier Analysis," EUROCRYPT 2024:
  <https://doi.org/10.1007/978-3-031-58716-0_2>.
- Bhaswar B. Bhattacharya, Persi Diaconis, and Sumit Mukherjee, "Universal
  Limit Theorems in Graph Coloring Problems With Connections to Extremal
  Combinatorics": <https://arxiv.org/abs/1310.2336>.
- Wei Dai, Viet Tung Hoang, and Stefano Tessaro, "Information-theoretic
  Indistinguishability via the Chi-squared Method":
  [`2017-537.pdf`](../RandomSystems/SoP/2017-537.pdf).
- Avijit Dutta, Mridul Nandi, and Abishanka Saha, "Proof of Mirror Theory for
  xi_max = 2": [`2020-669.pdf`](../RandomSystems/SoP/2020-669.pdf).
