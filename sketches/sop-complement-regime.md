# XOR SoP beyond half the domain

Status: the checksum-conditioned full proxy, global-shift quotient, complete
full-deck residual estimate, and all four marginal cases are formalized in
the `XORComplement*.lean` modules.  For `n >= 63`, Lean proves

```text
q <= N-3:
  |Adv(q,N) - CollisionAdv(q,N)| <= 7/N

q < N:
  |Adv(q,N) - CollisionAdv(q,N)|
    <= 7/N + 1/(2*(N-1))
    <= 8/N.
```

The concrete collision-threshold test is within twice the best certified
residual of the optimal adaptive advantage.  The point `q=N` is governed by
the separately formalized checksum-saturation attack.

This note studies the XOR of two independent random permutations on
`G = F_2^n`, with

```text
N = |G| = 2^n.
```

The adversary makes `q` distinct queries.  The exact reduction in
`RandomSystems/SoP/SoP2.lean` says that adaptive advantage is exactly the
statistical distance between the resulting `q`-answer tape and `q`
independent uniform answers, for every `q <= N`.

The existing finite collision/Fourier proof only analyzes `2*q <= N`.  That
is a restriction of the coefficient estimate, not of the random-system
reduction.

## 1. Executive conclusion

There are really two endpoints:

```text
q < N:  collision behavior, with a uniform explicit signed remainder
q = N:  checksum saturation, advantage at least 1 - 1/N
```

The compiled complement theorem for every strict prefix is

```text
|Adv(q,N) - CollisionAdv(q,N)|
  <= 7/N + 1/(2*(N-1))
  <= 8/N.
```

The public `preSaturationRemainderBound` combines this with the sharper
existing sparse-tail proof for `q<=N/2`, retaining the smaller certified
error in their overlap.  A still sharper finite theorem suggested by the
same representative is

```text
|Adv(q,N) - CollisionAdv(q,N)| <= C * q^2/N^3,    q <= N-3,
```

with the already-formal explicit corrections at `q=N-2` and `q=N-1`.
Here

```text
CollisionAdv(q,N)
  = N / (2*(N-1)^2) * E |K_q - choose(q,2)/N|,
```

and `K_q` is the number of equal pairs among `q` independent uniform
colors.

Together with the compiled collision-count limit theorems, this gives the
sharp leading behavior in every non-saturated asymptotic regime:

```text
q << sqrt(N):  Adv(q,N) ~ choose(q,2)/N^2

q/sqrt(N) -> a positive finite value:
  the exact Poisson collision-count expression

sqrt(N) << q < N:
  Adv(q,N) ~ q / (2*sqrt(pi)*N^(3/2))

q = N:
  1 - 1/N <= Adv(N,N) <= 1
```

The collision-threshold test is the matching attack for every `q<N`; the
full-table XOR-checksum test is the matching attack at `q=N`, up to the
unavoidable additive `1/N` interval.

This extends the sharp collision constant through every `q<N` and exposes
the discontinuity caused by the final query.  The stronger uniform finite
remainder `C*q^2/N^3` is still open above half the deck; it is no longer
needed for the sharp dense leading term because the compiled `8/N` residual
is already lower order there.

## 2. One honest representative for every query depth

Let the two random permutations be `pi1` and `pi2`.  Set

```text
sigma = pi2 o pi1^(-1).
```

For every `x in G`, make one card with color

```text
d_sigma(x) = x XOR sigma(x).
```

Then shuffle all `N` cards uniformly and reveal the first `q` colors.

This produces exactly the same answer tape as

```text
pi1(input) XOR pi2(input)
```

on any fixed list of `q` fresh inputs.  Indeed, the first permutation merely
chooses a uniformly random ordering of the vertices, while `sigma` is an
independent uniform permutation.

So the real experiment is:

```text
sample one uniform perfect matching of K_(N,N)
color edge (x,sigma(x)) by x XOR sigma(x)
shuffle the N colored matching edges
reveal q cards
```

The ideal experiment is a shuffled deck of `N` independent uniform colors.
For a prefix shorter than `N`, shuffling that ideal deck still gives exactly
`q` independent uniform answers.

This representative is honest, works for all `q`, and makes both collision
behavior and final checksum behavior visible.

## 3. The checksum and the final-query jump

For every real full deck,

```text
XOR over all N colors
  = XOR_x x XOR XOR_x sigma(x)
  = 0.
```

For an ideal full deck the total XOR is uniform in `G`.  Therefore the test
"accept real iff total XOR is zero" has gap

```text
1 - 1/N.
```

This is already formalized by
`sop_abelian_saturation_lower_bound` in `RandomSystems/SoP/SoP2.lean`.

The jump only occurs at the last query.  If even one color is hidden, that
hidden color can absorb the checksum.  In particular, the uniform law on
full zero-sum decks has a perfectly uniform marginal on the first `N-1`
coordinates.

Thus there is no contradiction between

```text
Adv(N-1,N) = order 1/sqrt(N)
```

and

```text
Adv(N,N) >= 1 - 1/N.
```

One additional answer can reveal a global invariant that was completely
masked before it arrived.

## 4. The checksum-conditioned collision representative

Let `U0` be the uniform distribution on full tapes whose total XOR is zero.
Relative to the fully uniform law `U`, its density is

```text
Z(y) = N * 1[totalXor(y)=0].
```

For a full tape let

```text
K_N(y) = number of equal coordinate pairs,
M_N    = choose(N,2),
h      = N/(N-1)^2.
```

Define the full proxy `C_full` by

```text
dC_full/dU
  = Z(y) * (1 + h*(K_N(y) - M_N/N)).
```

This is an honest probability distribution for `N>=4`.

First, it is nonnegative.  Since `K_N>=0`, its smallest bracket is

```text
1 - h*M_N/N
  = 1 - N/(2*(N-1))
  = (N-2)/(2*(N-1)).
```

Second, it has total mass one.  Under `U0`, every pair of coordinates agrees
with probability exactly `1/N`, so

```text
E_U0 K_N = M_N/N.
```

Third, its distance from the fully uniform full tape is exactly

```text
TV(C_full,U) = 1 - 1/N.
```

Indeed, outside the zero-sum slice its density is zero, while on that slice
its density relative to `U` is at least one when `N>=4`.

This proxy therefore has the correct global saturation behavior before any
remainder is considered.

## 5. Why this is a genuinely stronger use of signed representatives

Let `P_full` be the exact real full-deck law.  The object to analyze is the
signed residual

```text
R_signed = P_full - C_full.
```

The proxy is honest, but the residual is deliberately signed.  Its positive
and negative pieces must be combined on each transcript before taking an
absolute value.

In Walsh coordinates, a full mask is a list of `N` word characters.  Adding
the same character `beta` to every row does not change the Fourier
coefficient of the real two-permutation density: it may change the sign of
one permutation coefficient, but that coefficient is squared in the XOR of
two independent permutations.

Therefore masks occur in global-shift orbits.

The density `Z` contains the orbit of the constant mode.  Multiplying it by
the centered collision density adds the entire global-shift orbit of every
two-row collision mode.  Consequently `C_full` agrees exactly with the real
density on:

```text
quotient defect 0: global checksum modes
quotient defect 1: zero on both sides
quotient defect 2: collision modes and every global shift of them
```

For `N>=8` these pair orbits have a unique majority value, so there is no
double counting.  The small carrier `N=4` is a separate finite case.

This is the signed gain that the earlier truncation did not exploit.  The
old level decomposition took "number of nonzero rows" literally, so a
global shift could turn a two-row mode into an apparent level `N-2` mode.
The quotient subtraction recognizes these as the same mode and cancels all
of them before a norm is taken.

Signed representatives do not lower the true statistical distance.  They
lower the proof loss by preventing a low-complexity mode from being charged
again as a huge high-level tail.

## 6. Exact marginals of the full proxy

Write

```text
s = N-q
```

for the number of hidden cards.  Marginalize `C_full` to the `q` visible
coordinates.  Under `U0`, the hidden coordinates have XOR fixed by the
visible checksum.

### At least three hidden cards: `s>=3`

Every hidden coordinate is uniform, and every hidden pair is jointly
uniform: a third hidden coordinate absorbs the checksum constraint.
Therefore all visible-hidden and hidden-hidden collision terms average to
their ordinary value `1/N`.

The marginal is exactly the existing planted-collision proxy:

```text
dC_q/dU_q
  = 1 + h*(K_q - M_q/N).
```

Thus the same simple collision representative applies unchanged for every

```text
q <= N-3.
```

### Two hidden cards: `s=2`

The hidden pair agrees exactly when the visible total XOR is zero.  Hence

```text
dC_(N-2)/dU_(N-2)
  = 1 + h*(
      K_(N-2) - M_(N-2)/N
      + 1[visibleXor=0] - 1/N
    ).
```

The extra checksum indicator has exact half-`L1` cost

```text
1/(N*(N-1)).
```

This identity and cost are compiled in `XORComplementBoundary.lean`.

### One hidden card: `s=1`

The hidden color is forced to equal the visible total XOR.  Let

```text
D(y) = number of visible coordinates equal to visibleXor(y).
```

Then

```text
dC_(N-1)/dU_(N-1)
  = 1 + h*(
      K_(N-1) - M_(N-1)/N
      + D(y) - (N-1)/N
    ).
```

The centered `D` term is the sum of the co-singleton Walsh modes (constant on
all visible rows except one).  Orthogonality gives the compiled half-`L1`
bound

```text
1/(2*(N-1)).
```

It is lower order than the collision term, which has size `1/sqrt(N)`.

### No hidden cards: `s=0`

The proxy is supported on the zero-sum slice and has distance exactly
`1-1/N` from uniform, as above.

These four cases are one proof, not four unrelated models.  They are the four
possible ways the same full proxy behaves after hidden cards are averaged
out, and all four are now formalized.

## 7. The closed full-deck estimate and marginal theorem

The same full-deck representative permits two estimates, one on each side of
`N/2`.

For `q<=N/2`, the repository already proves

```text
TV(P_q,C_q) <= C_low*q^2/N^3
```

with explicit constants; the signed degree-three truncation is sharper still.

For `q>N/2`, do not estimate each prefix separately.  Let

```text
R_full = P_full - C_full.
```

Both terms are supported on the zero-checksum slice, which has uniform
probability `1/N`.  Restricted Cauchy--Schwarz therefore gives

```text
TV(P_full,C_full)
  <= (1/2) * sqrt((1/N) * E_U[R_full^2]).
```

This exact support-aware inequality is now formalized as
`full_residual_advantage_le_sqrt_energy` in
`RandomSystems/SoP/XORComplement.lean`.

The dense lemma proved in `XORComplementEntropy.lean` is stronger than the
energy target needed here and yields the explicit endpoint

```text
TV(P_full,C_full) <= 7/N,    n >= 63.
```

Every prefix residual is a marginal of this full residual, so data processing
gives the same `7/N` bound whenever at least three rows remain hidden.  The
exact proxy-marginal identity is compiled in
`XORComplementMarginal.lean`.  `XORComplementBoundary.lean` adds the exact
two-hidden correction and the orthogonal one-hidden correction, yielding

```text
TV(P_q,C_q) <= 7/N + 1/(2*(N-1)) <= 8/N,    q<N.
```

Since

```text
q^2/N^3 >= 1/(4N)
```

in the high-query range, the high and low estimates join at the desired
`O(q^2/N^3)` scale (with conversion constant `28` away from the two boundary
points and `32` uniformly for every `N/2<q<N`).
This is one representative and one signed cancellation; only the estimate
used on that residual changes by regime.

The Fourier meaning is especially clean.  The residual coefficients are
constant on global-shift orbits.  Ordinary full-space Parseval counts all `N`
members of each orbit, while checksum support divides that energy by `N`
before Cauchy--Schwarz.  After the constant and translated pair orbits have
been removed, the expected sizes are

```text
translated level 3: quotient energy O(1/N^3)
translated level 4: quotient energy O(1/N^2)
balanced minor arcs: quotient energy O(1/N^3)
```

so the quotient energy is `O(1/N^2)`, equivalently the raw full-space energy
is `O(1/N)`.

Eberhard's 2017 proof supplied the structural decomposition.  His Theorem 1.5
proves

```text
TV(P_q,U_q) = O(q/N^(3/2)) for every q<N.
```

Its proof quotients by character translation, isolates characters which are
up to four-sparse, and bounds the remaining fourth-power sum.  The two-sparse
characters dominate his un-subtracted estimate.  Our proxy removes their
entire translation orbit exactly; the remaining finite profile sums and their
explicit constants are now closed in `XORComplementSquareRoot.lean` and
`XORComplementEntropy.lean`.

## 8. Consequences

### One formula for every `q<N`

For every `q<N`, the compiled uniform comparison is

```text
|Adv(q,N) - CollisionAdv(q,N)|
  <= 7/N + 1/(2*(N-1))
  <= 8/N.
```

The actual public bound is tighter: for `2q<=N`, it takes the minimum of this
quantity and the older sparse Fourier remainder.  The collision-threshold
attack obeys the same residual estimate and is within twice it of optimal.

### Sharp sparse regime

When `q << sqrt(N)`, the collision count is almost always zero or one, so

```text
CollisionAdv(q,N) ~ choose(q,2)/N^2.
```

The residual is smaller by a factor of order `1/N`.

### Sharp birthday interpolation

When `choose(q,2)/N` tends to a fixed rate `lambda`, the already formalized
Poisson calculation gives

```text
N * Adv(q,N)
  -> lambda * Pr[Poisson(lambda)=floor(lambda)].
```

The collision-threshold test attains the same limit.

### Sharp dense regime, including above `N/2`

Whenever

```text
q/sqrt(N) -> infinity,
q < N,
```

the already formalized collision-count normal approximation gives

```text
Adv(q,N) ~ q/(2*sqrt(pi)*N^(3/2)).
```

In particular, if `q/N -> c` with `0<c<=1` while `q<N`, then

```text
sqrt(N) * Adv(q,N) -> c/(2*sqrt(pi)).
```

At `q=N-1` the constant is still

```text
1/(2*sqrt(pi)) = 0.282094...
```

The very next query changes the advantage to at least `1-1/N`.

### Matching attacks

For every `q<N`, use the centered collision test:

```text
accept real iff K_q > E[K_q].
```

Its gap equals the collision-proxy distance and differs from the true gap by
at most the same signed residual (plus the explicit lower-order boundary
correction for `q=N-2,N-1`).

For `q=N`, use the checksum test.

Thus the proposed upper bounds have matching information-theoretic attacks;
they are not artifacts of the representative.

## 9. Comparison with prior results

Let `N=2^n`.

```text
Dai-Hoang-Tessaro:
  Adv <= (q/N)^(3/2),                  q <= N/16

Dutta-Nandi-Saha:
  Adv <= 19*q^2/N^2 + 8*n^3/N^2,     q <= N/17

Dinur:
  Adv <= q/(2*(N-1)^(3/2)),          q < N/2, N>=1000

Eberhard:
  Adv = O(q/N^(3/2)),                 every q<N,
  asymptotic and with unspecified constant

candidate signed-quotient theorem:
  Adv = CollisionAdv + O(q^2/N^3),    every q<N,
  with explicit last-two-query corrections
```

The candidate improves what is known in three distinct senses:

1. Below the birthday threshold it has the right quadratic startup
   `choose(q,2)/N^2`, rather than the DHT `q^(3/2)/N^(3/2)`, the DNS cubic
   residue, or Dinur's linear dense envelope.
2. Above the birthday threshold it replaces Dinur's leading constant `1/2`
   by the collision-normal constant `1/(2*sqrt(pi))`.
3. It extends the sharp leading constant from `q<N/2` through every `q<N`,
   while Eberhard gives only an unspecified-constant big-O theorem there.

At `q=N`, no vanishing bound is possible; the checksum attack is essentially
perfect.

## 10. Exact small-carrier audit

The colored-deck representative permits exact enumeration by displacement
histograms.  The following values are diagnostics, not proof inputs.

```text
N=4:
q=2  Adv=0.0833333
q=3  Adv=0.1041667
q=4  Adv=0.7500000

N=8:
q=2  Adv=0.0178571
q=3  Adv=0.0372024
q=4  Adv=0.0425372
q=5  Adv=0.0628534
q=6  Adv=0.0826149
q=7  Adv=0.0951834
q=8  Adv=0.8750000
```

For `N=8`, the exact distance between the real full deck and `C_full` is
`0.0582218`; every marginal residual is no larger, as required by data
processing.  The full proxy itself has distance exactly `7/8` from uniform.

The data support an order-`1/N` residual and show the final-query jump
directly.  They do not establish the uniform theorem.

## 11. Formalization status

Compiled in `RandomSystems/SoP/XORComplement.lean`:

```text
DONE   global checksum density, normalization, and exact checksum distance
DONE   C_full pointwise nonnegative and normalized
DONE   C_full distance from uniform = 1-1/N
DONE   checksum modes are orthogonal to the centered collision kernel
DONE   global-shift invariance of squared injection coefficients
DONE   global-shift invariance of the exact full convolution coefficients
DONE   exact checksum support of the full convolution and signed residual
DONE   support-aware Cauchy with the extra 1/sqrt(N) factor
```

Compiled elsewhere:

```text
REUSE  adaptive advantage = fresh-tape distance for q<=N
REUSE  collision proxy MAD, Poisson limits, normal limit, threshold attack
DONE   exact full residual <= 7/N for n>=63
DONE   signed marginal contraction
DONE   exact ordinary-proxy marginal for s>=3
DONE   exact adaptive comparison |Adv-CollisionAdv| <= 7/N for s>=3
DONE   exact s=2 proxy correction with cost 1/(N*(N-1))
DONE   exact s=1 co-singleton correction with cost <=1/(2*(N-1))
DONE   |Adv-CollisionAdv| <= 8/N for every q<N
DONE   matching collision-threshold attack within twice the best residual
```

The full-deck estimate is factored and closed as follows:

```text
DONE   row-permutation and global-shift orbit accounting
DONE   nonzero row-XOR masks vanish exactly
DONE   profiles with multiplicity above 3N/4 reduce to the sparse tail
DONE   every remaining profile has a cut with N^2 <= 16*m*(N-m)
DONE   separated fourth moment <= pointwise maximum * cubic mass
DONE   exact finite-torus square-root bound for each row profile
DONE   exact histogram/permutation double count
DONE   support-layer aggregation of the high-entropy profiles
DONE   separated anchored cubic mass <= 1/N^2
DONE   full residual advantage <= 7/N
```

The marginal and boundary modules prove, coefficient by coefficient,

```text
prefixMarginal(fullProxyDensity) = proxyDensity
prefixMarginal(fullResidualDensity) = remainderDensity
```

For `s=N-q>=3`, a zero-padded mask belongs to a translated pair orbit exactly
when its visible part is an equal-row two-coordinate mask.  For `s=2`, one
additional constant orbit survives.  For `s=1`, the additional surviving
orbits are the co-singleton masks.  These classifications, their correction
norms, and the unified endpoint are axiom-audited and contain no admissions.

Still on paper:

```text
PAPER  colored displacement-deck presentation as a standalone PDS theorem
OPEN   tighter finite residual constant than 7/N
```

The full-table point `q=N` remains the separate checksum-saturation regime;
it cannot share a vanishing collision-remainder formula because the complete
real table has deterministic XOR checksum zero.

## 12. Sources checked

- Sean Eberhard, *More on additive triples of bijections*, Theorem 1.5 and
  its proof: `tmp/pdfs/high-query-audit/eberhard-1704.02407.pdf`.
- Itai Dinur, *Tight Indistinguishability Bounds for the XOR of Independent
  Random Permutations by Fourier Analysis*, Theorem 1:
  `tmp/pdfs/sop-bound-audit/dinur.pdf`.
- Wei Dai, Viet Tung Hoang, Stefano Tessaro,
  *Information-theoretic Indistinguishability via the Chi-squared Method*,
  Theorem 4: `RandomSystems/SoP/2017-537.pdf`.
- Avijit Dutta, Mridul Nandi, Abishanka Saha,
  *Proof of Mirror Theory for xi_max = 2*, Theorem 3 and Corollary 2:
  `RandomSystems/SoP/2020-669.pdf`.
