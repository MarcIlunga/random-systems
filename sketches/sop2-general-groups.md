# Two-permutation SoP over general finite groups

Status: pen-and-paper research note.  Exact identities, a derived finite
certificate, and open asymptotic obligations are labeled separately.  No Lean
claim is made here.

Date: 2026-08-04.

Notation and presentation:
[FOUNDATIONS.md](../FOUNDATIONS.md). This note uses that document as its
notation authority.

Program context:
[`signed-pds-research-program.md`](signed-pds-research-program.md).

## 1. Question and conclusion

Let `G` be a finite group of order `N`, not necessarily abelian.  For two
independent uniform permutations `pi1, pi2 : X -> G`, study the random function

```text
F(x) = pi1(x) * pi2(x)
```

against a uniform random function with range `G`.

The collision component and its threshold attack are universal for every
finite group.  A basis-free signed partition-Mobius argument also gives an
explicit group-independent finite remainder certificate.  What is not yet
closed is the sharp summation of that certificate when the query depth grows
with `N`.

There is no universal exact all-depth answer depending only on `N`.  Higher
components and saturation genuinely depend on group structure.

## 2. Exact transcript law — CLOSED

For `q` distinct inputs define the normalized injection density

```text
mu_q(a) = N^q/(N)_q   if a : [q] -> G is injective,
          0           otherwise.
```

Coordinatewise group convolution gives the real answer likelihood relative to
the uniform tape:

```text
L_q(y) = (mu_q * mu_q)(y)

       = N^q/(N)_q^2
           * #{a injective : i |-> a_i^(-1) * y_i is injective}.
```

No commutativity is used.  Domain relabeling symmetry removes adaptivity after
fresh-query filtering, so the operational advantage is exactly

```text
Adv_G(q,N) = (1/2) * E_uniform |L_q - 1|.
```

This is the correct starting point for both honest and signed
representatives.

## 3. Universal collision representative — CLOSED

Let

```text
M    = binom(q,2),
K(y) = #{i<j : y_i=y_j}.
```

The exact two-coordinate component of `L_q-1` is

```text
H2(y) = N/(N-1)^2 * (K(y) - M/N).
```

Define

```text
C_q(y) = 1 + H2(y).
```

This is an honest probability density.  One representative is:

```text
with probability M/(N-1)^2:
  choose one query pair uniformly and force its two answers equal;

otherwise:
  sample an ordinary uniform-function tape.
```

The construction is projectively consistent: the `q`-coordinate proxy is the
corresponding marginal of the full-domain proxy.

Its exact distance from uniform is

```text
A_col(q,N)
  = N/(2*(N-1)^2) * E |K - M/N|.
```

Elementary bounds are

```text
A_col(q,N) <= min(
  M/(N-1)^2,
  sqrt(M)/(2*(N-1)^(3/2))
).
```

At two queries there is no higher component:

```text
Adv_G(2,N) = A_col(2,N) = 1/(N*(N-1)).
```

All formulas in this section are independent of the multiplication table of
`G`.

## 4. Matching attack — CLOSED conditional on the remainder bound

Use the deterministic test

```text
accept real iff K(y) > M/N.
```

Its gap against the proxy is exactly `A_col`.  For the real construction, any
bound

```text
(1/2) * E |L_q-C_q| <= Delta
```

immediately yields

```text
|attackGap-A_col| <= Delta,
|Adv_G-A_col|     <= Delta,
|Adv_G-attackGap| <= 2*Delta.
```

Thus the upper-bound statistic and lower-bound attack are the same object.

## 5. ANOVA support decomposition — CLOSED

Let `u_S` be the Hoeffding/ANOVA component of the injection density supported
exactly on coordinate set `S`.  Then

```text
L_q = 1 + sum over |S|>=2 of (u_S * u_S).
```

Different coordinate supports are orthogonal.  The sum over `|S|=2` is exactly
`H2`.  Therefore the signed residual is

```text
R_q = L_q-C_q
    = sum over |S|>=3 of (u_S*u_S).
```

This support identity is the formal version of the gain-graph statement that
the two-edge balanced cycle is the first visible obstruction.

## 6. Partition-Mobius remainder certificate — DERIVED

For a fixed `k`, define the set-only core energy

```text
E_k(N)
  = sum from j=0 to k of
      (-1)^(k-j) * binom(k,j) * N^j/(N)_j.
```

This is exactly

```text
||u_[k]||_2^2.
```

Define the derangement-partition polynomial

```text
D_k(N)
  = sum over set partitions P of [k] with no singleton blocks of
      N^(number of blocks of P)
      * product over blocks B of (|B|-1)!.

B_k(N) = D_k(N)/(N)_k.
```

Equivalent recurrence:

```text
D_0 = 1,
D_1 = 0,

D_k
  = N * sum from s=2 to k of
      binom(k-1,s-1) * (s-1)! * D_(k-s).
```

Exponential generating function:

```text
sum_k D_k z^k/k!
  = exp(N * (-log(1-z)-z)).
```

The key operator estimate is

```text
||u_[k] * u_[k]||_2
  <= B_k(N) * ||u_[k]||_2.
```

### Proof mechanism

1. Expand the injectivity predicate by inclusion-exclusion on the partition
   lattice.
2. Restrict to the fully centered coordinate subspace.
3. Every partition with a singleton block vanishes exactly.
4. A surviving partition convolution operator has norm at most its total
   mass.
5. Sum only the nonsingleton partitions after this exact cancellation.

The resulting finite certificate is

```text
Delta_group(q,N)
  = (1/2) * sqrt(
      sum from k=3 to q of
        binom(q,k) * B_k(N)^2 * E_k(N)
    ).
```

The derived comparison is

```text
|Adv_G(q,N)-A_col(q,N)| <= Delta_group(q,N).
```

This derivation is basis-free: it does not require scalar characters,
Peter-Weyl decomposition, or classification of noncommutative word maps.

### Current verification status

- All quantities and normalizations have been matched to the exact injection
  density.
- Singleton cancellation and the nonsingleton partition recurrence have been
  checked independently.
- Pair and triple cases agree with the direct expansion.
- The certificate has not yet received a line-by-line independent writeup
  review or formal verification.

It is therefore recorded as DERIVED, not CLOSED.

## 7. Open scalar summation

The principal analytic obligation is to bound

```text
sum from k=3 to q of
  binom(q,k) * B_k(N)^2 * E_k(N).
```

The desired target is

```text
Delta_group(q,N) = O(q^2/N^3),  q=o(N).
```

The work should proceed in increasing difficulty.

1. Fixed `q`, exact expansion.
2. Bounded collision rate `binom(q,2)/N -> lambda`.
3. `sqrt(N) << q=o(N)`.
4. A finite bound through `q<N/2`, if the same certificate remains efficient.

The first two cases should follow from elementary coefficient control of the
generating function.  Uniform `q=o(N)` likely needs a saddle-point or cluster
estimate.  A worst-case termwise bound may lose the cancellation that made the
certificate useful.

Until this summation is proved, the following sharp asymptotics remain targets,
not theorems for arbitrary finite groups:

```text
q << sqrt(N):
  Adv_G(q,N) ~ binom(q,2)/N^2.

binom(q,2)/N -> lambda>0:
  N*Adv_G(q,N)
    -> lambda * Pr[Poisson(lambda)=floor(lambda)].

sqrt(N) << q << N:
  Adv_G(q,N)
    ~ q/(2*sqrt(pi)*N^(3/2)).
```

## 8. Nonabelian gain-graph interpretation

For each query pair `i,j`, the exact compatible-count graph has two directed
constraint edges:

```text
red i->j:
  a_j = a_i,

blue i->j:
  a_j = (y_j*y_i^(-1)) * a_i.
```

A connected constraint family has `N` assignments exactly when every oriented
cycle has ordered gain product equal to the group identity.  This is the
nonabelian balanced-gain condition.

The smallest mixed balanced cycle is the red/blue two-edge cycle:

```text
balanced iff y_i=y_j.
```

That cycle is precisely the collision proxy.  Longer balanced cycles impose
noncommutative word equations.  The partition-Mobius operator argument bounds
them collectively without classifying each word equation.

## 9. Saturation and the limit of universality

### Abelian groups

At the full input domain,

```text
sum_x F(x) = 0.
```

The ideal checksum is uniform, so the checksum test has gap

```text
1-1/N.
```

### Nonabelian groups

After mapping to the abelianization `G_ab = G/[G,G]`, the full ordered product
is deterministic.  Hence

```text
Adv_G(N,N) >= 1-1/|G_ab|.
```

For a perfect group this lower bound is zero.  Full-depth behavior then depends
on genuinely nonabelian multiplication-table structure.

When the visible full table is itself a permutation, compatible explanations
are complete mappings of `G`.  The Hall-Paige condition and asymptotic counts
of multiplication-table transversals are therefore the relevant saturation
theory, not merely a checksum calculation.

References:

- Eberhard, Manners, and Mrazovic,
  [An asymptotic for the Hall-Paige conjecture](https://arxiv.org/abs/2003.01798).
- Eberhard, Manners, and Mrazovic,
  [A random Hall-Paige conjecture](https://arxiv.org/abs/2204.09666).

## 10. Exact equal-order counterexamples — CLOSED

Exact exhaustive enumeration gives:

```text
N=6, q=4:
  C6: 31/450
  S3: 61/900

N=6, q=6:
  C6: 5/6
  S3: 125/216
```

Even finite abelian groups of the same order differ:

```text
N=8, q=4:
  C8:       40787/940800
  C4 x C2: 40531/940800
  C2^3:    40019/940800
```

These examples establish that the collision term can be universal while the
higher-order remainder is group-dependent.

## 11. Literature boundary

- Dai-Hoang-Tessaro and DNS give concrete results for XOR on bitstrings, not
  for arbitrary nonabelian groups.
- Eberhard proves `O(q/N^(3/2))` for arbitrary finite abelian groups through an
  `L2` estimate, without the sharp collision constant.
- Dinur gives the concrete XOR bound and explicitly leaves the broader
  additive-group maximal-coefficient extension open.
- No primary source located in this audit gives the sharp collision-proxy
  asymptotics for the ordered product over arbitrary nonabelian groups.

Primary references:

- [Dai-Hoang-Tessaro](https://eprint.iacr.org/2017/537).
- [Dutta-Nandi-Saha](https://eprint.iacr.org/2020/669).
- [Eberhard](https://arxiv.org/abs/1704.02407).
- [Dinur](https://eprint.iacr.org/2024/338).

## 12. Next proof tasks

```text
GG2-1  Write the partition-Mobius operator proof line by line.
GG2-2  Verify Delta_group against exhaustive small N,q values.
GG2-3  Prove the fixed-collision-rate scalar summation.
GG2-4  Prove or refute Delta_group=O(q^2/N^3) for q=o(N).
GG2-5  Transfer the collision-threshold matching attack.
GG2-6  Develop a separate complement/saturation analysis parameterized by
       G_ab and multiplication-table structure.
```

The preferred proof route is the centered partition-operator argument.  A
full nonabelian Fourier decomposition is available in principle but introduces
matrix-valued bookkeeping without improving the current certificate.
