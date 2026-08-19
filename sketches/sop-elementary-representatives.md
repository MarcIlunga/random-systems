# An elementary representative proof for SoP versus URF

Status: the finite XOR theorem, exact gain-graph expansion, global
broken-circuit involution, pair-cycle interpretation, and bridge from the
surviving graph residual to the sharp theorem are compiled in Lean with no
admissions.  The final orthogonal core-pair estimate still uses the finite
Walsh/checkerboard basis; a completely spectral-free tail proof remains open.

Date: 2026-08-01.

## 1. The intended proof in one sentence

For `q < N/2`, represent both systems using the same deck of hidden matching
explanations, show that SoP is essentially URF with one randomly planted answer
collision, and show that everything not explained by that planted collision is
a much smaller interaction among closed-loop cores.

The desired story is:

```text
SoP = URF + one planted collision + rare multi-core correction.
```

The first equality sign is an honest probability mixture for the proxy.  The
second correction is initially signed; its positive and negative parts become
honest unnormalized PDS branches before any coupling theorem is applied.

This is meant to be the main proof narrative.  Fourier analysis can remain a
way of proving the closed-loop estimate, but it should not define the objects
or explain why the result is true.

### 1.1 Headline result and comparison

Assume

```text
G = F_2^n,
G = F_2^n with n >= 10,
N = |G| = 2^n,
2 <= q and 2q <= N,
M = binom(q,2),
lambda = M/N.
```

For a uniform tape `Y`, let `K(Y)` be its number of equal-coordinate pairs and
define

```text
A_col(q,N)
  = N/(2(N-1)^2) * E |K-lambda|.
```

The compiled collision-proxy theorem gives the two-sided estimate

```text
|Adv(q,N) - A_col(q,N)| <= Delta(q,N),

Delta(q,N)
  = 1/2 * sqrt(
      16 binom(q,3) / ((N-1)^3 (N-2)^3)
      + (1152/7) q^4/N^6
      + 8 q^4/N^8
    ).
```

In particular,

```text
Adv(q,N)
  <= min(
       M/(N-1)^2,
       sqrt(M)/(2(N-1)^(3/2))
     )
     + Delta(q,N).
```

The compiled rounded corollary replaces `1152/7` by `200` and `8` by `16`.
A simpler scalar `O(q^2/N^3)` corollary can be derived from either form, but
the Lean endpoint deliberately retains the stronger finite expression.

The leading asymptotics and the competing bounds are:

```text
                         q << sqrt(N)          q >> sqrt(N)

collision representative q^2/(2N^2)           q/(2sqrt(pi)N^(3/2))
DHT                      q^(3/2)/N^(3/2)       q^(3/2)/N^(3/2)
formal-tight DNS          (10q^2+5n^3)/N^2     same quadratic expression
published DNS             (19q^2+8n^3)/N^2     same quadratic expression
Dinur                     q/(2N^(3/2))         q/(2N^(3/2))
```

Thus the collision representative has the sharp sparse coefficient `1/2`,
removes DNS's `n^3/N^2` residue, changes from quadratic to linear query growth
at the birthday transition, and improves Dinur's dense leading constant from
`1/2` to `1/(2sqrt(pi))`.  The collision-threshold test gives the matching
lower estimate `A_col-Delta`, so this identifies the actual advantage up to
the smaller remainder rather than merely supplying another upper bound.

Status discipline: the exact two-sided approximation and the displayed upper
bound compile in `XORBounds.lean`.  `GainGraphCancellation.lean` proves the
global Dohmen--Trinks/Whitney involution and the exact restricted gain-graph
sum.  `XORGainGraph.lean` proves pointwise that this restricted sum is the SoP
likelihood, identifies its residual with the certified level-three-and-higher
tail, and restates the strongest endpoint.  The final orthogonal sign basis is
mathematically Fourier analysis, but Fourier is neither the representative nor
the proof's main explanatory object.

## 2. What Lanzenberger does and does not permit

An honest Lanzenberger PDS is a nonnegative finite distribution over DDSs.
The distribution need not have weight one in intermediate successor and
common-part arguments.  However, every representative equivalent to the
probability systems SoP or URF has top-level weight one.

Therefore:

- arbitrary-weight common and residual subdistributions are sound;
- arbitrary correlations between counterfactual branches are sound;
- nonuniform distributions over deterministic systems are sound;
- negative mass is not an honest PDS.

There is also a canonical signed linear envelope of PDSs.  Virtual equivalence
is equality of every transcript pushforward.  For normalized finite
common-domain systems, the infimum half-`L1` distance over signed equivalent
representatives is exactly the distinguishing advantage: transcript
pushforward contraction proves that signed representatives cannot understate
the advantage, and Lanzenberger's honest attainment theorem proves the reverse
inequality.  The source audit and proof are recorded in
[`signed-virtual-pds.md`](./signed-virtual-pds.md).

This equality is a soundness and completeness statement, not a claim that
signed representatives are quantitatively useless.  They can lower the best
bound currently known by keeping cancellations that a tractable positive
representative or an early triangle inequality destroys.  The exact optimum
does not move; our ability to approach and certify it can.

Signed measures may therefore be used directly as distance certificates.  The
accounting order is:

```text
form the complete signed expression;
perform all algebraic or sign-reversing cancellations;
combine all coefficients belonging to the same atom;
take an `L1` norm, or take positive and negative parts if an honest coupling is
required.
```

Taking an absolute value or positive part term by term before cancellation is
not sound: overlapping signed terms can cancel pointwise.  A signed joint is a
virtual joint, not an ordinary coupling, and general normalized conditioning
fails in the signed layer.

One fixed injective query schedule reads the entire fresh-output tape.  Hence
no representative can lower the exact tape distance.  The purpose of the
representatives below is to lower the best *proved upper bound* by turning that
fixed distance into a cancellation problem and then into a simple counting
and coupling problem.

## 3. The exact explanation-deck representatives

Let `G = F_2^n`, `N = |G|`, and let `y = (y[1],...,y[q])` be an output tape.
Define

```text
W(y) = number of injective tuples a[1..q] such that
       b[i] = a[i] XOR y[i]
       is also injective.
```

Thus `W(y)` is the number of hidden pairs of partial permutation images that
explain `y`.  Call `(y,a)` an explanation card whenever `a` is one of these
`W(y)` witnesses.

There are exactly

```text
sum_y W(y) = (N)_q^2
```

cards: choosing a card is the same as choosing two ordered injections `a,b`,
and then setting `y=a XOR b`.  If `Y` is a uniform tape, then

```text
Z = E[W(Y)] = (N)_q^2 / N^q.
```

For `q < N/2`, every pile is nonempty.  A greedy placement proves this: after
placing `k` colored edges, at most `k` left endpoints and `k` translated right
endpoints are forbidden, so at least `N-2k > 0` choices remain.

Now put two different distributions on the same card deck.

### Real deck

Choose an explanation card uniformly:

```text
mass_real(y,a) = 1/(N)_q^2.
```

After forgetting `a`, tape `y` has mass

```text
P(y) = W(y)/(N)_q^2,
```

which is exactly the sum-of-two-permutations tape law.

### Ideal deck

First choose `y` uniformly from `G^q`, then choose one of its explanation
cards uniformly:

```text
mass_ideal(y,a) = 1/(N^q W(y)).
```

After forgetting `a`, every tape has mass `1/N^q`.  This is an exotic but
honest URF presentation: internally it samples a hidden pair of partial
permutation explanations even though its visible tape is perfectly uniform.
The partial injections can be completed uniformly to full permutations if a
full-permutation sample space is desired; the completion factor is the same
for every card and changes nothing.

Both cards reveal the same deterministic fresh-rank DDS `D_y`.  Within one
pile, the real and ideal card weights have one common sign, so introducing the
hidden card does not inflate distance:

```text
1/2 * sum_(y,a) |mass_real(y,a)-mass_ideal(y,a)|
  = 1/2 * sum_y |P(y)-1/N^q|
  = Adv(q,N).
```

This is an explicit attaining representative pair.

It also exposes the exact maximal coupling without any theorem-specific
machinery.  Overlay the two weights on every card and keep

```text
common(y,a) = min(mass_real(y,a), mass_ideal(y,a)).
```

Both systems use the same card on this common part.  The leftover real cards
live exactly in piles with `W(y)>Z`, and the leftover ideal cards live exactly
in piles with `W(y)<Z`.  The total weight left on either side is `Adv(q,N)`.
This is the literal deck-of-cards form of the Jordan/common-part coupling.

### Count-first form

Group the deck by the scalar pile size `w=W(y)`.  Let

```text
u[w] = Pr_URF[W(Y)=w],
r[w] = Pr_SoP[W(Y)=w].
```

Then

```text
r[w] = (w/Z) * u[w].
```

Conditioned on `W=w`, SoP and URF have the same law: both are uniform among
tapes in that pile-size fiber.  Therefore the exact systems have the
block-first representatives

```text
URF: sample w with law u; sample y uniformly from {W(y)=w}; run D_y.
SoP: sample w with law r; sample y uniformly from {W(y)=w}; run D_y.
```

SoP's count label is the `W`-size-biased version of URF's count label.  An
optimal coupling only has to couple this one-dimensional label; after labels
match, it samples the same tape in the common fiber.

This is the coarsest exact sufficient statistic, up to merely renaming its
values.  The likelihood ratio is `P(y)/Q(y)=W(y)/Z`.  Therefore tapes with the
same `W` can be merged with no loss, whereas any block merging two different
`W` values still contains a real/ideal imbalance.  Affine orbits are a valid
finer classifier, but they carry much more information than this exact
coupling needs.

### Shared-sampler population form

There is a second exact representative that makes the permutation idea
concrete.  Write

```text
sigma = pi_2 after inverse(pi_1).
```

The change of variables from `(pi_1,pi_2)` to `(pi_1,sigma)` is a bijection,
so `pi_1` and `sigma` are still independent uniform permutations.  If
`a=pi_1(x)`, then the visible answer is

```text
pi_1(x) XOR pi_2(x) = a XOR sigma(a).
```

Thus SoP has the following exact card-table representative:

```text
shuffle the N positions using a uniform permutation sigma;
write label a XOR sigma(a) on position a;
answer fresh queries by sampling distinct positions in a random order.
```

URF has a matching representative with the same outer sampler:

```text
write an independent uniform label h(a) on every position a;
answer fresh queries by sampling distinct positions in a random order.
```

Randomly reordering the domain of a uniform random function does not change
its law, so the second experiment is exactly URF.  The two systems now differ
only in how the hidden population of labels is made:

```text
SoP population: colors of a uniform perfect matching;
URF population: independent uniform colors.
```

This is perhaps the simplest physical picture: put two copies of `G` on two
sides of a table, match them uniformly, and color the edge `(a,b)` by
`a XOR b`.  The queries reveal colors of randomly selected left endpoints.

Ordinary cycles of `sigma` do not retain enough information.  Already for
`G=F_2^2`, the permutations

```text
(0)(1)(2 3)  and  (0)(3)(1 2)
```

have the same ordinary cycle type, but their nonzero displacement colors are
respectively `1` and `3`.  What matters is the colored matching, or the
equivalent alternating gain cycles introduced in Section 6.

## 4. The planted-collision representative

Let

```text
M      = binom(q,2),
K(y)   = number of pairs i<j with y[i]=y[j],
lambda = M/N,
beta   = M/(N-1)^2.
```

Define the planted-collision tape law `J` by the following experiment:

```text
choose one pair {i,j} uniformly among the M pairs;
sample all tape values uniformly, except force y[j]=y[i].
```

For a fixed tape `y`, precisely `K(y)` choices of the planted pair are
compatible with it.  Hence, relative to the uniform tape law `Q`,

```text
J(y)/Q(y) = N*K(y)/M = K(y)/lambda.
```

Equivalently, the collision count under `J` is the `K`-size-biased collision
count under `Q`:

```text
Pr_J[K=k] = (k/lambda) * Pr_Q[K=k].
```

Now define the proxy tape law by the honest mixture

```text
C = (1-beta)*Q + beta*J.
```

Its density is exactly

```text
C(y)/Q(y)
  = 1 + N/(N-1)^2 * (K(y)-lambda).
```

Thus the degree-two collision proxy has a very simple representative:

```text
with probability 1-beta: run an ordinary fresh-rank URF tape;
with probability beta:  run a fresh-rank tape with one random planted
                        answer collision.
```

This is not an equivalent URF representative.  It is an honest third random
system used as a coupling bridge.

At `q=2`, this proxy is exactly the real SoP tape law.  For general `q`, the
remaining difference is the multi-core interaction correction.

## 5. Why the one planted collision gives both regimes

The laws `J` and `Q` have the same conditional tape law given `K`, because
their likelihood ratio is a function of `K` alone.  Consequently

```text
TV(C,Q) = beta * TV(J,Q)
        = beta * TV(K-size-biased law, K law)
        = N/(2(N-1)^2) * E_Q |K-lambda|.
```

This has an elementary interpretation.

### Sparse collisions: `q << sqrt(N)`

Usually `K=0`.  The planted experiment has `K>=1`, so the planted collision is
almost perfectly visible.  Therefore

```text
TV(J,Q) is about 1,
TV(C,Q) is about beta,
beta is about binom(q,2)/N^2.
```

The elementary finite bound is simply

```text
TV(C,Q) <= beta = M/(N-1)^2.
```

### Dense collisions: `q >> sqrt(N)`

There are already about `lambda` natural collisions with standard deviation
about `sqrt(lambda)`.  Size-biasing adds roughly one collision, which is hard
to notice inside that natural fluctuation.  Since

```text
Var_Q(K) = M(N-1)/N^2,
```

Cauchy-Schwarz gives

```text
TV(C,Q) <= sqrt(M)/(2(N-1)^(3/2)).
```

The normal approximation says that distinguishing `K` from a one-step shift
costs about `1/sqrt(2*pi*lambda)`.  Multiplying by `beta` gives

```text
TV(C,Q) ~ q/(2*sqrt(pi)*N^(3/2)).
```

So the two regimes are not separate tricks.  They are the easy-to-see and
hard-to-see regimes of one planted collision.

## 6. The right cycle decomposition

The useful picture is a colored matching, not the ordinary cycle type of
`pi_2 o pi_1^-1`.

Draw a bipartite graph with `G` on the left and `G` on the right.  Give edge
`(a,b)` the XOR color

```text
y = a XOR b.
```

Every color is a perfect matching.  An explanation card for `y[1..q]` is a
placement of one edge of each requested color such that no two chosen edges
share a left or right endpoint.  Thus `W(y)` counts colored partial matchings.

To count them, start from arbitrary placements and exclude endpoint
collisions.  For each query pair `{i,j}` there are two forbidden equations:

```text
hidden collision:   a[i] = a[j],
shifted collision:  a[i] XOR y[i] = a[j] XOR y[j].
```

In inclusion-exclusion, a selected family of such equations is a labelled
graph on query positions.  Choosing one root value determines every value in
a tree component.  A closed loop is consistent only when the XOR of its edge
labels is zero.

This yields the exact virtual expansion

```text
W(y) = sum_T (-1)^|T| * 1{T is cycle-consistent for y} * N^(components(T)).
```

The key elementary facts are:

- forest terms impose no condition on `y`, so they disappear after centering;
- the smallest mixed closed loop uses the hidden and shifted constraint for
  one query pair, and it is consistent exactly when `y[i]=y[j]`;
- after all pair-level terms are grouped, they give precisely the planted-
  collision density from Section 4;
- every remaining nonconstant term is a family of visible cycle cores.  It may
  be one genuinely larger core, or an interaction of two or more ordinary
  two-vertex cores.

Ordinary permutation cycle decompositions forget the XOR edge labels and are
therefore too coarse.  Two relative permutations with the same ordinary cycle
type can have different displacement geometry.  Alternating endpoint cycles,
or equivalently the labelled gain-graph cycles above, retain exactly the
information that can affect the visible tape.

## 7. Sound internal cancellation and the broken-cycle proof

Let

```text
R_signed = P-C.
```

The gain-graph formula is a signed way to calculate `R_signed`.  Perform its
cycle and sign-reversing cancellations pointwise first.  For a distance upper
bound, half-`L1` contraction is already sound in the virtual-PDS envelope.  If
one additionally wants a literal probabilistic coupling, take the Jordan parts

```text
R_plus (y) = max(P(y)-C(y),0),
R_minus(y) = max(C(y)-P(y),0).
```

They have the same arbitrary weight

```text
epsilon = sum_y R_plus(y) = sum_y R_minus(y) = TV(P,C).
```

The pointwise common part

```text
H(y) = min(P(y),C(y))
```

gives the honest decomposition

```text
P = H + R_plus,
C = H + R_minus.
```

Lift each term through `y -> D_y`.  The common sub-PDS `H` is coupled
identically.  Only the two residual sub-PDSs, each of weight `epsilon`, need to
disagree.  This is the sound use of Lanzenberger's arbitrary-weight
distributions: the cancellation is computed in the signed layer, while the
coupling sees only nonnegative common and residual branches.

Gluing this coupling to the planted-collision coupling gives

```text
Adv(q,N) <= TV(C,Q) + epsilon.
```

The target is therefore the finite estimate

```text
epsilon <= Delta(q,N).
```

There are three separate cancellations.  Keeping them separate prevents the
proof from taking absolute values too early:

1. Broken-circuit cancellation removes redundant constraint edges inside each
   balanced cycle.
2. Coordinate centering removes every tree attachment and every cycle relation
   that fails to involve all coordinates of its claimed interaction.
3. A sign-reversing pairing bounds the largest surviving centered core, after
   which orthogonality counts core pairs without cross-term inflation.

### 7.1 The exact broken-circuit cancellation

Fix an ordering of the hidden/shifted collision edges.  Suppose edge `e` is the
last edge of a balanced cycle.  The other edges of that cycle already force the
equation represented by `e`.  Consequently, whenever a selected family `T`
contains the other cycle edges:

```text
solutions(T with e) = solutions(T without e),
components(T with e) = components(T without e),
sign(T with e)       = -sign(T without e).
```

The two inclusion-exclusion terms cancel.  The standard first-broken-circuit
rule organizes these toggles into disjoint pairs, so every family containing a
selected broken circuit disappears exactly once.  This is the gain-graph
version of Whitney's broken-circuit cancellation, and is an instance of the
general inclusion-exclusion theorem of Dohmen and Trinks.

The global selector is worth spelling out because overlapping circuits are the
only subtlety.  For a bad family `T`, collect every balanced circuit `C` whose
broken part

```text
C without max(C)
```

is contained in `T`.  Choose the smallest value of `max(C)` among those
circuits and call it `e(T)`.  Pair `T` with the family obtained by toggling
`e(T)`.  The chosen circuit remains eligible because its broken part does not
contain its own maximum.  No circuit with a smaller maximum can be created by
the toggle: every edge of such a circuit is smaller than `e(T)`, so changing
membership of `e(T)` cannot change whether its broken part is contained.
Therefore

```text
e(T toggle e(T)) = e(T),
```

and toggling twice returns exactly to `T`.  The map has no fixed point.  This
least-pivot proof is what is formalized in `GainGraphCancellation.lean`; it
handles arbitrary overlaps without assuming that the graph circuits are
disjoint.

After all pairings, the compatible count can be summed only over families
containing no broken balanced cycle.  Every surviving family with nonzero
solution count is a forest, but the permitted forests depend on which labelled
cycles are balanced for the realized tape `y`.  That dependence is where all
visible information lives:

- a balanced two-edge parallel cycle records `y[i]=y[j]`;
- a longer balanced cycle records a higher affine relation;
- a tree by itself records nothing about `y`.

For presentation it may be cleaner to deduplicate equal hidden and shifted
constraints first.  Then an equality `y[i]=y[j]` removes one of the two
parallel forbidden edges directly.  The indexed version currently in Lean is
also valid; it expresses the equality case as cancellation of a balanced
parallel cycle.

This involution alone does not prove a norm bound: a large tape-dependent
family of allowed forests remains.  The next operation removes its irrelevant
attachments before anything is estimated.

### 7.2 Visible relations and exact tree stripping

For a function of a uniform tape, let

```text
Avg_i f = average f over coordinate y[i],
Ctr_i f = f - Avg_i f.
```

For a set `S` of coordinates, its exact interaction is obtained by averaging
outside `S` and centering every coordinate in `S`:

```text
Part_S f
  = product_(i in S) Ctr_i
    product_(i not in S) Avg_i f.
```

These parts are orthogonal, have mean zero in each coordinate they use, and
sum back to `f`.  This is the ANOVA decomposition, but here it is only repeated
subtraction of row, column, and higher-dimensional averages.

The gain graph makes `Part_S` concrete.  A selected constraint family `T` has
two kinds of edge:

```text
H edge i--j:  a[i] XOR a[j] = 0,
S edge i--j:  a[i] XOR a[j] = y[i] XOR y[j].
```

Walk around a graph cycle.  The hidden `a` values cancel.  What remains is one
XOR relation among the visible `y` values.  Record by a bit vector `r_C` which
coordinates occur an odd number of times among the shifted edges of cycle
`C`.  The cycle is consistent precisely when

```text
XOR_(i with r_C[i]=1) y[i] = 0.
```

Let `Rel(T)` be the span of all such cycle vectors, and let

```text
visible(T) = union of the supports of all r in Rel(T).
```

The consistency indicator for `T` depends only on the coordinates in
`visible(T)`.  Therefore

```text
Part_S 1{T is consistent} = 0

whenever visible(T) does not contain S.
```

This strips trees term by term.  A leaf is in no cycle, so its coordinate is
not visible and centering kills the term.  The same applies to every tree
hanging from a cyclic core.  It is slightly stronger than ordinary graph
two-core stripping: a vertex may lie on a mixed hidden/shifted cycle while its
`y` coefficient cancels, in which case centering strips it as well.

Thus the correct residual objects are full-visible relation cores, not merely
graphs of minimum degree two.

### 7.3 What survives after the planted collision is removed

The smallest visible relation is

```text
e_i + e_j,
```

which says `y[i]=y[j]`.  In the gain graph it is the balanced two-edge cycle
formed by the hidden and shifted edge on the same query pair.  Summing all
single copies of this core gives exactly

```text
H2(y) = N/(N-1)^2 * (K(y)-M/N).
```

Subtracting `H2` removes a single pair core, not every object built from pair
cores.  The remainder has two possible shapes:

```text
1. two or more pair cores, overlapping or disjoint;
2. a genuinely larger full-visible relation core.
```

This corrects the tempting but false statement that the remainder consists
only of long cycles.  For example, on four coordinates two disjoint equality
cores already form a level-four interaction.  These double-pair terms account
for the leading `q^4/N^6` part of the squared remainder.  On three coordinates,
two overlapping equality cores force all three answers equal and produce the
first nonzero residual.

### 7.4 The whole centered sum collapses before it is bounded

The clean way to sum all broken-cycle forests is to return temporarily to one
permutation.  Define its sampling-without-replacement density on `k` cards by

```text
mu_k(x)
  = N^k/(N)_k   if x[1],...,x[k] are all distinct,
  = 0           otherwise.
```

Let `u_S` be the exact centered interaction `Part_S mu_q`.  Then

```text
mu_q = sum_(S subset [q]) u_S.
```

Use normalized XOR convolution:

```text
(f * g)(y) = E_x f(x) g(y XOR x).
```

The SoP likelihood ratio is exactly

```text
L = mu_q * mu_q.
```

If `A` and `B` are different coordinate sets, then

```text
u_A * u_B = 0.
```

Indeed, choose a coordinate in the symmetric difference of `A` and `B`.  One
factor is centered there and the other is constant there, so the average in
that coordinate is zero.  Hence all cross terms disappear and

```text
L = 1 + sum_(nonempty S) u_S * u_S.
```

The singleton term is zero because one sample from a permutation is uniform.
The sum over pairs is exactly `H2`.  Therefore

```text
R = L - 1 - H2
  = sum_(|S|>=3) u_S * u_S.
```

Different `S` are again orthogonal.  If `u_k` denotes one canonical
`k`-coordinate component, then

```text
E R^2
  = sum_(k=3)^q V_k,

V_k
  = binom(q,k) * ||u_k * u_k||_2^2.
```

This is the exact core-pair identity.  Squaring does not create all possible
pairs of gain graphs: centering has already made every pair with different
visible support cancel to zero.

### 7.5 The first surviving core: an exact three-card calculation

For three answers, the compatible explanation count has only three values:

```text
answer pattern             W(y)

all three equal            N(N-1)(N-2)
exactly one equal pair     N(N-2)(N-3)
all three distinct         N(N^2-6N+10)
```

Subtract the constant and the three pair interactions from the normalized
likelihood.  The exact level-three component `h3=u_3*u_3` is

```text
answer pattern             h3(y)

all three equal             4/((N-1)(N-2))
exactly one equal pair     -4/((N-1)^2(N-2))
all three distinct          8/((N-1)^2(N-2)^2)
```

Under a uniform tape, the three rows have probabilities

```text
1/N^2,
3(N-1)/N^2,
(N-1)(N-2)/N^2.
```

Squaring and averaging gives the exact identity

```text
||h3||_2^2
  = 16/((N-1)^3(N-2)^3),

V_3
  = 16 binom(q,3)/((N-1)^3(N-2)^3).
```

This is the overlapping-pair boundary term.  It is kept exact rather than
rounded into the general tail estimate.

### 7.6 Exact energy of a centered permutation core

Define

```text
CoreEnergy(k) = ||u_[k]||_2^2.
```

There is a basis-free exact formula.  First,

```text
||mu_i||_2^2 = N^i/(N)_i.
```

Orthogonality and symmetry also give

```text
N^i/(N)_i
  = sum_(j=0)^i binom(i,j) CoreEnergy(j).
```

Binomial inversion therefore yields

```text
CoreEnergy(k)
  = sum_(i=0)^k (-1)^(k-i) binom(k,i) N^i/(N)_i.
```

This alternating sum is exactly the result of stripping every lower-support
forest.  To bound it without taking absolute values term by term, introduce

```text
F(k,a)
  = sum_(i=0)^k (-1)^(k-i) binom(k,i) N^i/(N-a)_i.
```

Pascal's identity gives the exact positive recursion

```text
F(k,a)
  = a/(N-a) * F(k-1,a+1)
    + (k-1)N/((N-a)(N-a-1)) * F(k-2,a+2),

F(0,a) = 1,
F(1,a) = a/(N-a).
```

The two branches have a direct core interpretation.  The exposed coordinate
either attaches to one of the `a` already exposed values, or pairs with one of
the other `k-1` fresh coordinates.  There is no third possibility after lower
supports have canceled.

Induction in this positive recursion gives the sharper finite forms

```text
F(k,a)
  <= (N(a+k-1))^(k/2)/(N-a)_k                 if k is even,

F(k,a)
  <= (N(a+k-1))^((k-1)/2)*(a+k-1)/(N-a)_k    if k is odd.
```

In particular, `CoreEnergy(k)=F(k,0)`.  The exact first values are

```text
CoreEnergy(1) = 0,
CoreEnergy(2) = 1/(N-1),
CoreEnergy(3) = 4/((N-1)(N-2)).
```

For the finite summation below, the sharp recursion implies the convenient
uniform consequences

```text
CoreEnergy(k) <= (2(k+1)/N)^(k/2)    for k>=4,
CoreEnergy(k) <= 1                    for k<N/2.
```

The exact recursion and parity-dependent bounds should be retained in the
formal library; the last two inequalities are only corollaries used to sum the
tail.

### 7.7 The second sign-reversing pairing

It remains to control the convolution `u_k*u_k`.  The required largest-term
bound also has a card-pairing proof.

Give each possible card value a plus or minus sign according to one nonzero
bit test.  For an ordered injection `x`, multiply the signs of its `k` cards.
If some card has no partner obtained by flipping the tested bit, choose the
first such card and flip it.  The new tuple is still injective, has the opposite
sign, and flips back to the original tuple.  All such tuples cancel in pairs.

Only self-paired tuples survive.  For even `k`, their fraction is exactly

```text
Gamma(N,k)
  = (k-1)/(N-1)
    * (k-3)/(N-3)
    * ...
    * 1/(N-k+1).
```

For odd `k`, no tuple can be self-paired under a single common bit test.

A general full-support sign pattern may test different nonzero linear bits in
different coordinates.  Gaussian elimination orders the coordinates into
blocks, one new tested bit per block.  At the first failed block, either flip
the first unpaired card, or swap it with its later partner.  Both operations
are involutions and reverse the total sign.  The survivors must pass every
nested pairing test.  Writing `B_k` for the largest surviving signed average,
the tight product bounds are

```text
B_k <= Gamma(N,k)                         if k is even,
B_k <= Gamma(N,k-1) * k/(N-k)             if k is odd.
```

For integer `k<N/2`, these imply

```text
B_k^2 <= 1/binom(N,k).
```

For `k=2`, retain the sharper special value

```text
B_2 <= 1/(N-1).
```

The only linear-algebra step now needed is that the plus/minus checkerboards
form an orthonormal basis and diagonalize XOR convolution.  Consequently,

```text
||u_k*u_k||_2^2
  = sum_(full-support signs alpha) coeff(alpha)^4
  <= B_k^2
     * sum_(full-support signs alpha) coeff(alpha)^2
  = B_k^2 * CoreEnergy(k).
```

This line is Parseval in its elementary finite form.  Calling the signs Walsh
characters makes it Fourier analysis; calling them checkerboard cards does not
change the mathematics.  The gain-graph cancellation supplies the physical
meaning of the surviving cores, while this sign basis is the simplest exact
way currently known to count their pairs.

### 7.8 Summing every surviving core family

For `k>=4`, combine the preceding two estimates:

```text
V_k
  <= binom(q,k)/binom(N,k) * CoreEnergy(k)
  <= (q/N)^k * (2(k+1)/N)^(k/2).
```

Set

```text
rho = q/N < 1/2,
n = log2(N).
```

For `4<=k<=4n`,

```text
rho^k <= 16 rho^4 2^(-k),
```

so

```text
sum_(k=4)^(4n) V_k
  <= 16 rho^4
     * sum_(k=4)^(4n) ((k+1)/(2N))^(k/2).
```

For `N>=1000` and `N=2^n`, consecutive terms in the last sum have ratio below
`1/2`.  One direct check is

```text
t_(k+1)/t_k
  < sqrt(e(4n+2)/(2N))
  <= sqrt(42e/2048)
  < 1/2.
```

The first term is `25/(4N^2)`, hence

```text
sum_(k=4)^(4n) ((k+1)/(2N))^(k/2)
  <= 25/(2N^2),

sum_(k=4)^(4n) V_k
  <= 200 q^4/N^6.
```

For `k>4n`, use `CoreEnergy(k)<=1` while keeping `rho`:

```text
sum_(k=4n+1)^q V_k
  <= rho^(4n+1)/(1-rho)
  < 2 rho^(4n+1)
  <= 16 rho^4/N^4
  = 16 q^4/N^8.
```

Together with the exact three-card term,

```text
E R^2
  <= 16 binom(q,3)/((N-1)^3(N-2)^3)
     + 200 q^4/N^6
     + 16 q^4/N^8.
```

This is the simpler rounded sum.  The compiled recurrence keeps the geometric
factors instead of rounding each interval and proves the stronger form

```text
E R^2
  <= 16 binom(q,3)/((N-1)^3(N-2)^3)
     + (1152/7) q^4/N^6
     + 8 q^4/N^8.
```

Cauchy-Schwarz now gives

```text
epsilon
  = TV(P,C)
  = 1/2 E|R|
  <= 1/2 sqrt(E R^2)
  <= Delta(q,N).
```

Combining this with the exact planted-collision distance proves the compiled
two-sided result

```text
|Adv(q,N)-A_col(q,N)| <= Delta(q,N).
```

### 7.9 What this does and does not complete

The constrained XOR broken-cycle argument now compiles in the following
precise sense:

```text
gain-graph broken circuits
  -> exact cancellation of redundant balanced edges
  -> coordinate centering strips invisible trees
  -> exact support/core decomposition
  -> sign-reversing survivor bound
  -> finite Delta estimate.
```

The exact inclusion-exclusion formula, global least-pivot broken-circuit
involution, redundant balanced-edge cancellation, two-edge pair-cycle
criterion, normalized density identity, graph-residual identity, tight energy
bound, and final advantage theorem are formalized.  The final core-pair count
uses the orthogonal plus/minus basis, which is the real Walsh basis in
elementary clothes.  Eliminating that last spectral step remains an open
generalization, but it is not an open obligation in the stated XOR theorem.

### 7.10 The first stronger signed truncation

The collision endpoint above still takes an absolute value after level two
and charges level three as error.  The first concrete gain from the signed
representative viewpoint is to retain both levels before taking the absolute
value.  Put

```text
M  = choose(q,2),
C3 = choose(q,3),
P0 = (N)_q / N^q.
```

On a collision-free tape, every three-coordinate card has three distinct
answers.  Its value is `2`, so the combined degree-two-plus-three density is

```text
-M/(N-1)^2 + 8*C3/((N-1)^2*(N-2)^2).
```

For an arbitrary tape, one three-coordinate card has only three possible
values:

```text
all distinct:       2
exactly one repeat: -(N-2)
all equal:          (N-1)(N-2).
```

Consequently every degree-three card is at least `-(N-2)`.  If

```text
2 <= q,
2*q <= N,
2*M <= N,
N >= 6,
```

this lower bound is already enough to prove that the combined density is
nonnegative whenever a collision exists.  It is nonpositive on the
collision-free region.  Since the combined density has mean zero, its exact
half-L1 norm is simply the probability of the negative region times the
magnitude of its constant value there:

```text
A23(q,N)
  = P0 *
      (M/(N-1)^2
        - 8*C3/((N-1)^2*(N-2)^2)).
```

Keeping levels two and three therefore gives the fully explicit operational
two-sided certificate and, in particular, the following upper bound:

```text
|Adv(q,N) - A23(q,N)|
  <= 1/2 * sqrt(
       (1152/7)*q^4/N^6
       + 8*q^4/N^8
     ).
```

```text
Adv(q,N)
  <= A23(q,N)
     + 1/2 * sqrt(
         (1152/7)*q^4/N^6
         + 8*q^4/N^8
       ).
```

Compared with the previous terminal formula, this keeps the exact
collision-free factor `P0`, subtracts the triangle correction before taking
L1, and removes the complete level-three energy from the error square root.
It is the first compiled example where allowing a signed intermediate object
actually lowers the closed proof certificate.  The argument after the local
three-card calculation is only sign classification and counting; it does not
use mirror theory or conditioning.

The improvement over the previous two-regime certificate is itself compiled.
Lean proves, throughout the range above,

```text
A23 + new level-4 tail
  <= min(old sparse branch, old dense branch) + old level-3 tail.
```

It proves strict inequality for every `q >= 3`.  The only extra idea needed
for the dense branch is the elementary no-collision estimate

```text
P0 <= N / (N + M).
```

This follows by repeatedly applying

```text
product(1-a_i) <= 1 / (1 + sum(a_i)).
```

Under `2*M <= N`, the right side damps the sparse term enough to put it below
the old square-root branch as well.

The matching test is equally elementary: query a fixed list of distinct
inputs and return `real` exactly when two visible outputs collide.  The module
`SoP/XORCollisionAttack.lean` proves its signed acceptance gap is within the
same level-four tail of `A23`, so

```text
A23 - new tail <= collision-test gap <= Adv <= A23 + new tail.
```

This turns the two-sided norm estimate into a concrete attack certificate.

The next member of the hierarchy retains level four as well.  Exact finite
enumeration strongly suggests another improvement, but its four-coordinate
class calculation and terminal theorem remain open; they are not claimed by
the degree-three result.

For scale, direct evaluation of the two closed formulas gives the following
illustrative ratios.  `gain` is the old terminal upper bound divided by the
signed degree-three upper bound; the formal comparison above proves that this
ratio is greater than one for `q >= 3`, while the table shows its size in a few
examples.

```text
N       q       choose(q,2)/N     gain
1024    16      0.117             1.12
1024    24      0.270             1.26
1024    32      0.484             1.17
4096    48      0.275             1.25
65536   192     0.280             1.25
```

These numbers compare certified formulas; they do not assert that either
upper bound is the true advantage.

## 8. Representative choices assessed

```text
choice                         verdict

uniform full function table    correct but hides all useful freedom
fresh-rank tape                exact adaptive reduction; keep as outer shell
explanation-card deck          best exact real/ideal alignment
compatible-count-first         simplest exact sufficient-statistic coupling
one planted collision          best elementary proxy and main intuition
ordinary permutation cycles    too coarse; lose XOR displacement geometry
displacement histogram         explains K but loses higher affine relations
labelled gain-cycle core        best physical picture of the residual
centered sign-card basis        simplest completed core-pair count
signed virtual PDS             exact distance certificate; not operational
Jordan positive/negative parts honest arbitrary-weight residual PDSs
```

## 9. Formalization crosswalk

```text
claim or layer                         compiled location

adaptive fresh-tape reduction          SoP/SoP2.lean
planted-collision proxy and L1 bounds  SoP/XORCollisionProxy.lean
uniform-injection convolution          SoP/XORInjection.lean
level-two collision identity           SoP/XORInjection.lean
exact three-row core                    SoP/XORCore.lean
checkerboard coefficient bounds         SoP/XORCoefficient.lean
tight positive Pascal recursion         SoP/XORPascal.lean
finite medium/high tail sums            SoP/XORBounds.lean
generic broken-circuit involution        SoP/GainGraphCancellation.lean
balanced gain-cycle specialization       SoP/GainGraphCancellation.lean
gain-graph density and sharp endpoint    SoP/XORGainGraph.lean
arbitrary signed low-level truncation     SoP/XORSignedTruncation.lean
exact signed levels two plus three        SoP/XORSignedDegreeThree.lean
finite local-dependence Stein theorem     SoP/CollisionStein.lean
absolute-value normal Stein certificate  SoP/CollisionSteinAnalytic.lean
finite normal bound and dense limit       SoP/CollisionCountNormal.lean
birthday product and subunit Poisson      SoP/CollisionCountPoisson.lean
birthday and normal transfer to true SoP  SoP/XORCollisionAsymptotics.lean
```

The explanation-card and count-first representatives remain presentation
devices rather than separate Lean objects; their visible pushforwards are the
already-formal compatible-count density.  The more general spectral-free
gain-graph core-pair theorem remains open and is deliberately not required by
the constrained XOR endpoint.  The sparse ratio, every fixed collision rate
below one (including the central rate `1/2`), and the dense normal constant are
now compiled.  Extending the exact Poisson interpolation to fixed limiting
rates at least one remains optional.

## 10. Sources for the cancellation and survivor steps

- Klaus Dohmen and Martin Trinks, "An Abstraction of Whitney's Broken Circuit
  Theorem," *Electronic Journal of Combinatorics* 21(4), 2014.  Theorem 1 is
  the general cancellation statement for sums over subsets:
  <https://doi.org/10.37236/4356>.
- Itai Dinur, "Tight Indistinguishability Bounds for the XOR of Independent
  Random Permutations by Fourier Analysis," EUROCRYPT 2024.  Sections 4--5
  contain the nested sign-reversing pairing, exact core-energy alternating sum,
  positive recursion, and finite bounds used in Sections 7.6--7.8 above:
  <https://doi.org/10.1007/978-3-031-58716-0_2>.
