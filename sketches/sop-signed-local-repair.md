# Signed local repair for XOR SoP

Status: the finite sparse-range repair proxy, its exact distance, its strict
comparison with the previous closed certificate, and its matching collision
attack are formalized in
`RandomSystems/SoP/SignedLocalRepair.lean`.  The dense branch continues to use
the already-compiled collision-count proxy.  A collision-only local repair is
not exact from degree four onward: affine parallelograms are a genuine second
kind of defect.

Date: 2026-08-03.

## 1. Result first

Let

```text
G = F_2^n,
N = |G| = 2^n,
M = binom(q,2),
C3 = binom(q,3),
P0 = (N)_q / N^q.
```

Assume

```text
n >= 10,
2q <= N,
2M <= N.
```

The signed local-repair proof constructs an honest proxy distribution whose
distance from a uniform random function is exactly

```text
A23(q,N)
  = P0 *
      (M/(N-1)^2
        - 8*C3/((N-1)^2*(N-2)^2)).
```

The true XOR-of-two-permutations advantage satisfies the finite two-sided
bound

```text
|Adv(q,N) - A23(q,N)| <= E3(q,N),

E3(q,N)
  = 1/2 * sqrt(
      (1152/7)*q^4/N^6
      + 8*q^4/N^8).
```

The elementary distinguisher that makes `q` fixed distinct queries and
returns `real` exactly when two visible answers collide satisfies

```text
A23 - E3 <= collision-test gap <= Adv <= A23 + E3.
```

This is not a new numerical claim pasted onto the Fourier proof.  It gives a
different representative-level explanation of the already sharp signed
degree-three formula:

```text
uniform tape
  + pair-repair surplus
  + triple correction
  + small four-coordinate-and-higher residual.
```

The pair-plus-triple object is proved to be a genuine nonnegative probability
density.  Its surplus can be moved to its deficit by repeatedly repairing the
first visible collision.

## 2. Exact tape model

Fix `q` distinct inputs.  The two permutations restrict to independent
uniform ordered injections

```text
a = (a[1],...,a[q]),
b = (b[1],...,b[q]).
```

The visible tape is

```text
y[i] = a[i] XOR b[i].
```

Relative to the uniform tape law `Q` on `G^q`, one permutation restriction has
density

```text
mu(x)
  = N^q/(N)_q    if x is injective,
  = 0            otherwise.
```

Normalized XOR convolution is

```text
(f * g)(y) = E_x f(x) g(y XOR x).
```

Therefore the exact real likelihood ratio is

```text
L(y) = (mu * mu)(y).
```

This is the ordered-injection representative.  It is exact for the adaptive
random system because repeated queries can be removed and every fresh query
only reveals the next rank of this tape.

## 3. A signed repair is just recoloring one coordinate

For a real function `f` on visible tapes and coordinate `i`, define

```text
A_i f(y)
  = average of f(y with coordinate i replaced by z), over uniform z in G,

D_i f = f - A_i f.
```

`A_i` forgets coordinate `i`; `D_i` is the signed difference between keeping
the current color and recoloring it uniformly.  This is the promised local
repair.  It is not itself a stochastic coupling because the second term has a
minus sign, but it is a sound virtual-PDS operation.

The elementary identities are

```text
A_i^2 = A_i,
D_i^2 = D_i,
A_i D_i = D_i A_i = 0,
A_i A_j = A_j A_i,
A_i D_j = D_j A_i                 when i != j,
E D_i f = 0.
```

The last identity says that a repair moves signed mass but creates none.  It
is the first theorem in `SignedLocalRepair.lean`.

For a coordinate set `S`, put

```text
P_S f
  = product_(i in S) D_i
    product_(i not in S) A_i f.
```

Expanding `I = A_i + D_i` in every coordinate gives the exact Boolean-lattice
decomposition

```text
f = sum_(S subset [q]) P_S f.
```

The term `P_S f` is the part that genuinely needs every coordinate in `S`.
If an apparent graph contribution has a leaf or a coordinate that does not
affect its visible relation, applying `D_i` cancels it with its recolored copy.
This is local repair in the same sense that the gain-graph proof calls it tree
stripping.

## 4. Why only equal supports survive

Write

```text
u_S = P_S mu.
```

The empty component is `u_empty = 1`; singleton components vanish because one
permutation value is uniform.

The SoP likelihood expands as

```text
L
  = (sum_S u_S) * (sum_T u_T)
  = sum_(S,T) u_S * u_T.
```

If `S != T`, choose a coordinate in their symmetric difference.  One factor
is centered in that coordinate and the other is constant there.  Averaging
the convolution over that coordinate gives zero.  Thus

```text
u_S * u_T = 0 when S != T,

L = 1 + sum_(|S|>=2) h_S,
h_S = u_S * u_S.
```

This is the main cancellation.  No absolute value has been taken.  A failed
repair is now an interaction core `h_S` on at least two visible coordinates,
not a bad event charged independently at every query.

## 5. The successful two-coordinate repair

For a pair `S={i,j}`, direct averaging gives

```text
u_S(x)
  = -1          if x[i]=x[j],
  = 1/(N-1)     otherwise.
```

Convolving this two-coordinate card with itself gives

```text
h_S(y)
  = (N*1{y[i]=y[j]} - 1)/(N-1)^2.
```

Let `K(y)` be the number of equal visible pairs.  Summing over all query pairs
gives

```text
H2(y)
  = sum_(|S|=2) h_S(y)
  = (N*K(y)-M)/(N-1)^2.
```

This is exactly the planted-collision density minus one.  It is the signed
version of the following honest experiment: choose one query pair and force
its two answers to agree.

## 6. The first failures are triples

For one three-coordinate set, `h_S` has only three values:

```text
visible pattern        h_S(y)

all three equal        4/((N-1)(N-2))
one equal pair        -4/((N-1)^2(N-2))
all distinct           8/((N-1)^2(N-2)^2).
```

The negative middle line has the repair interpretation: repairing one
endpoint of a collision interacts with the third coordinate.  The all-equal
line records two overlapping collisions.  The all-distinct line is the small
compensating deficit/surplus required to keep the card centered.

Let

```text
H3(y) = sum_(|S|=3) h_S(y),
F23(y) = H2(y)+H3(y).
```

If `y` is injective, every pair misses and every triple is in the all-distinct
line, so

```text
F23(y)
  = -M/(N-1)^2
    + 8*C3/((N-1)^2(N-2)^2)
  = -A,

A = M/(N-1)^2
    - 8*C3/((N-1)^2(N-2)^2).
```

For a noninjective tape, `K>=1`, hence

```text
H2(y) >= (N-M)/(N-1)^2.
```

Every triple card is at least its one-pair value, hence

```text
H3(y) >= -4*C3/((N-1)^2(N-2)).
```

Consequently

```text
F23(y) >= 0
```

whenever

```text
4*C3 <= (N-M)(N-2).
```

The injective value is nonpositive whenever

```text
8*C3 <= M(N-2)^2.
```

Both inequalities follow from the transparent hypotheses

```text
N >= 6,
2q <= N,
2M <= N.
```

These are the exact finite sign calculations used by Lean; no asymptotic
notation or conditioning is hidden here.

## 7. The signed prefix is actually an honest proxy

Define a density relative to `Q` by

```text
C23(y)/Q(y) = 1+F23(y).
```

Every nonempty repair core has mean zero, so

```text
E_Q[1+F23] = 1.
```

On a colliding tape, `F23>=0`, so the density is at least one.  On an
injective tape it equals `1-A`.  Moreover

```text
A <= M/(N-1)^2 <= 1,
```

under `2M<=N` and `N>=6`.  Therefore

```text
1+F23(y) >= 0 for every y.
```

Thus `C23` is an honest probability law, not merely a signed certificate.
The Lean module proves both normalization and pointwise nonnegativity.

The sign partition is exact:

```text
C23-Q is negative on injective tapes,
C23-Q is nonnegative on colliding tapes.
```

Since a uniform tape is injective with probability

```text
P0 = (N)_q/N^q,
```

the common-part/Jordan identity immediately gives

```text
TV(C23,Q)
  = P0*A
  = A23(q,N).
```

This is the simplest derivation of the sharp sparse main term: count the
uniform deficit on the collision-free region.

## 8. An explicit first-collision repair coupling

The preceding distance calculation can be turned into a literal maximal
coupling.

After removing the pointwise common mass of `C23` and `Q`, the residual laws
are:

```text
surplus: supported on noninjective tapes, with density F23(y),
deficit: uniform over injective tapes, with constant density A.
```

Normalize the surplus and run this algorithm:

```text
while the tape has a repeated value:
  find the first coordinate whose value occurred at an earlier coordinate;
  replace that coordinate by a uniformly chosen value not currently used.
```

Each step increases the number of distinct values by one, so the algorithm
terminates after at most `q-1` repairs.  There is always an unused value because
`q<=N`.

Why is the terminal tape exactly uniform among injections?  The input surplus
depends only on the equality pattern of the tape.  It is therefore invariant
under every permutation of the value set `G`.  The repair rule uses only
equality and a uniform choice from the unused set, so its kernel is equivariant
under the same value permutations.  Hence the output law is invariant under
all value permutations.  The value-permutation group acts transitively on
injective `q`-tapes: map the `q` distinct values of one tape to those of any
other and extend this partial bijection to all of `G`.  The only invariant
probability law on this finite transitive set is the uniform law.

That uniform output is precisely the normalized deficit.  Pair the common
mass identically and use this repair kernel on the residual mass.  The coupling
disagrees with probability exactly `A23`, so it is maximal.

The important role of signed representatives is now visible.  They discover
the surplus and deficit by cancellation before an absolute value is taken.
Once their signs are known, the same algebra produces an ordinary positive
proxy and an ordinary coupling.

## 9. Returning to the true SoP law

The omitted signed density is

```text
R4(y) = sum_(|S|>=4) h_S(y).
```

Exactly,

```text
L(y)-1 = F23(y)+R4(y).
```

The existing centered-core estimate proves

```text
1/2 * E_Q |R4| <= E3(q,N),
```

with

```text
E3(q,N)
  = 1/2 * sqrt(
      (1152/7)*q^4/N^6
      + 8*q^4/N^8).
```

Reverse triangle inequality for total variation now gives

```text
|TV(P,Q)-TV(C23,Q)| <= TV(P,C23) <= E3,
```

which is the advertised

```text
|Adv-A23| <= E3.
```

The repair construction supplies the simple representative and exact main
term.  The only remaining analytic input is the already-formalized norm of
the four-coordinate-and-higher residual.

## 10. Matching attack

Let the test accept `real` exactly on the collision event

```text
B = {y : y is not injective}.
```

For the proxy, all positive mass of `C23-Q` lies on `B`, so

```text
C23(B)-Q(B) = A23.
```

Replacing `C23` by the true law changes the mass of any event by at most
`TV(P,C23)<=E3`.  Therefore

```text
|P(B)-Q(B)-A23| <= E3.
```

The test is a valid nonadaptive random-system environment: query a fixed
injective input schedule, inspect the visible answers, and output the collision
bit.  Hence

```text
A23-E3 <= P(B)-Q(B) <= Adv <= A23+E3.
```

This matching finite attack is why the main term is not a proof artifact.

## 11. One sharp strategy for both regimes

The local-repair sign classification is intended for the sparse side.  On the
dense side, retain the already-compiled exact collision-count proxy

```text
Acol(q,N)
  = N/(2(N-1)^2) * E_Q |K-M/N|.
```

Let

```text
Delta(q,N)
  = 1/2 * sqrt(
      16*C3/((N-1)^3(N-2)^3)
      + (1152/7)*q^4/N^6
      + 8*q^4/N^8).
```

A finite representative-first envelope is

```text
Bstar(q,N)
  = if 2M <= N then
      A23(q,N)+E3(q,N)
    else
      Acol(q,N)+Delta(q,N).
```

For a completely scalar displayed upper bound, replace `Acol` in the second
branch by

```text
min(
  M/(N-1)^2,
  sqrt(M)/(2(N-1)^(3/2))
).
```

Write the resulting closed collision endpoint as

```text
Bclosed(q,N)
  = min(
      M/(N-1)^2,
      sqrt(M)/(2(N-1)^(3/2))
    ) + Delta(q,N).
```

Properties:

1. In the sparse branch, the compiled comparison proves

   ```text
   A23+E3 <= old collision envelope,
   ```

   strictly for `q>=3`.

2. In the dense branch, `Bstar` is the old sharp collision endpoint, so the
   new piecewise theorem never sacrifices a regime.

3. One collision-count threshold attack works throughout.  Below mean one its
   threshold is simply `K>=1`, the collision test above.  Above the birthday
   transition it accepts when `K>M/N`.  The compiled attack differs from
   `Acol` by at most `Delta`.

The asymptotics are therefore

```text
q=o(sqrt(N)):
  Adv(q,N) = binom(q,2)/N^2 * (1+o(1)),

q/sqrt(N) -> infinity, q<=N/2:
  Adv(q,N) = q/(2*sqrt(pi)*N^(3/2)) * (1+o(1)).
```

The first follows from `P0->1`, the explicit triangle subtraction, and
`E3=O(q^2/N^3)`.  The second follows from the normal mean-absolute-deviation
limit for `K`; `Delta` is lower order throughout `q<=N/2`.

## 12. Comparison with the local literature

The following source statements were checked on rendered original PDF pages:

```text
DHT, Theorem 4:
  Adv <= q^(3/2)/N^(3/2),       n>=4, q<=N/16.

DNS, Corollary 2:
  Adv <= (19q^2+8n^3)/N^2,     n>=7, q<=N/17.

Dinur, Theorem 1:
  Adv <= q/(2(N-1)^(3/2)),      N>=1000, q<N/2.
```

The repository also has the tightened formal DNS constants

```text
(10q^2+5n^3)/N^2.
```

For `N>=1024`, `2<=q<=N/2`, elementary domination of `Bclosed` gives the
convenient simultaneous envelopes

```text
Bclosed(q,N) <= 0.509*q^2/N^2,
Bclosed(q,N) <= 0.468*q/N^(3/2).
```

These decimals are not assumptions.  They follow from `M<=q^2/2`,
`C3<=q^3/6`, `sqrt(a+b+c)<=sqrt(a)+sqrt(b)+sqrt(c)`, and the three terms of
`Delta`.  At `N=1024` the sparse collision coefficient is below `0.501`, the
three tail contributions are below `0.001`, `0.0065`, and `0.000002`; the
dense collision coefficient is below `0.355` and its complete tail is below
`0.113`.  Every bound decreases relative to these normalizations as `N`
increases.  The exact symbolic formula, rather than the decimals, remains the
preferred theorem statement.  These scalar comparisons have not yet been
exported as Lean theorems.

They imply, on every overlapping source range:

```text
Bstar <= Bclosed
      < q^(3/2)/N^(3/2)                         for q>=2,

Bstar <= Bclosed
      < q/(2(N-1)^(3/2)),

Bstar <= Bclosed
      < (10q^2+5n^3)/N^2
      < (19q^2+8n^3)/N^2.
```

Thus the piecewise repair/collision strategy is guaranteed to beat the
locally recorded DHT, Dinur, tightened DNS, and published DNS upper bounds in
their common parameter ranges.  The new local-repair branch is itself
strictly better than the previous repository endpoint for `q>=3`; the dense
branch inherits the already stronger collision result.

This is a range-qualified comparison.  It does not claim superiority over an
unknown result, over variants with a different oracle model, or outside
`N>=1024` and `q<=N/2`.

## 13. Why collision-only local repair stops at degree four

At four coordinates two qualitatively different failures survive:

1. two pair repairs can coexist, either overlapping or disjoint;
2. four distinct values can satisfy the affine relation

   ```text
   y[i] XOR y[j] XOR y[k] XOR y[l] = 0.
   ```

The second case is an affine parallelogram.  It can occur with no visible
collision.  Therefore no rule whose state records only the collision count or
the first repeated value can represent the exact degree-four correction.
`XORSignedDegreeFour.lean` proves this obstruction by classifying the exact
four-row coefficient.

This pinpoints the scope of the high-school proof:

```text
pair and triple prefix: equality patterns and first-collision repair suffice;
degree four onward:     affine relation data is genuinely necessary.
```

The obstruction does not invalidate the bound.  It explains why the residual
is estimated as a norm instead of being routed by the same collision-only
kernel.

## 14. A different next strategy: repair-aware exponential tilting

There is a natural route to a still simpler dense proof, but it is not closed
and is not claimed as a theorem.

Instead of the linear planted-collision density, use the honest Gibbs proxy

```text
C_theta(y)/Q(y)
  = exp(theta*K(y)) / E_Q exp(theta*K),
```

with `theta` chosen so its first centered term matches
`N/(N-1)^2*(K-M/N)`.  This proxy automatically resums repeated and disjoint
pair repairs.  Its likelihood ratio is monotone in `K`, so its exact optimal
test is still a collision-count threshold.  A gain-graph cluster expansion
of `P-C_theta` should then leave only connected triple and affine cores.

What must be proved before this becomes useful is an exact finite cluster
bound with constants smaller than `Delta`.  Positivity and the matching attack
are automatic; the residual estimate is not.  In particular, it would be
incorrect to assert that exponentiating the pair term necessarily matches the
degree-four coefficient: the affine parallelogram branch is invisible to `K`.

A second algebraic possibility is a direct `L1` repair bound.  For a support
of size `k`, the injection core has the exact Möbius formula

```text
u_k(x)
  = sum_(T subset [k]) (-1)^(k-|T|) mu_|T|(x restricted to T).
```

If the equality partition of `x` has block sizes `s_1,...,s_b`, this becomes

```text
u_k(x)
  = (-1)^k * sum_(j=0)^b (-1)^j
      * (N^j/(N)_j) * e_j(s_1,...,s_b),
```

where `e_j` is an elementary symmetric polynomial.  Young's inequality gives

```text
||u_k*u_k||_1 <= ||u_k||_1^2.
```

This is promising far below the birthday scale, but it loses the convolution
cancellation that supplies an extra power of `N` near `q~sqrt(N)`.  It cannot
replace the current `L2` residual estimate without a stronger sign-reversing
pairing.  The required pairing, or an exact Gibbs-cluster estimate, is the
genuinely open creative step.

The safe development policy is therefore:

```text
current guaranteed theorem:
  local pair+triple repair below the transition,
  collision-count proxy above it;

candidate future theorem:
  resum all disconnected pair repairs,
  count only connected affine failure cores,
  retain the minimum with the current theorem until strict improvement is
  proved symbolically.
```

## 15. Formalization receipt

`RandomSystems/SoP/SignedLocalRepair.lean` proves:

```text
uniform_average_repair_difference_eq_zero
average_three_core_proxy_density_eq_one
three_core_proxy_density_nonneg_sparse
three_core_proxy_advantage_eq_signed_degree_three_main
signed_local_repair_bound_lt_previous
signed_local_repair_two_sided
```

The final theorem packages the matching attack and upper bound in one
statement.  The module reuses the exact pair/triple evaluation and tail theorem
rather than duplicating their proofs.  Its focused source check passes against
the repository's coherent application cache.

## 16. Checked sources

- Wei Dai, Viet Tung Hoang, and Stefano Tessaro, *Information-theoretic
  Indistinguishability via the Chi-squared Method*, Appendix A, Theorem 4,
  local PDF `RandomSystems/SoP/2017-537.pdf`.
- Avijit Dutta, Mridul Nandi, and Abishanka Saha, *Proof of Mirror Theory for
  xi_max=2*, Theorem 3 and Corollary 2, local PDF
  `RandomSystems/SoP/2020-669.pdf`.
- Itai Dinur, *Tight Indistinguishability Bounds for the XOR of Independent
  Random Permutations by Fourier Analysis*, Theorem 1, rendered local copy
  `tmp/pdfs/sop-bound-audit/dinur.pdf`.
