# Signed-PDS research program

Status: top-level pen-and-paper research charter.  Nothing in this document is
a Lean theorem unless a linked source explicitly says so.

Date: 2026-08-04.

Notation and presentation:
[FOUNDATIONS.md](../FOUNDATIONS.md). This note uses that document as its
notation authority.

## 1. North-star objective

Use Lanzenberger-style random-system representatives, honest couplings, and
signed virtual representatives to turn information-theoretic distinguishing
problems into the following common form:

```text
exact advantage
  = distance to one explicit low-complexity proxy
  + a certified lower-order connected remainder.
```

The proxy must do three jobs at once:

1. give the simplest explanation of the construction's first visible defect;
2. produce a concrete matching distinguisher;
3. interpolate automatically between sparse, Poisson, and normal regimes.

The objective is not merely to recover the correct security exponent.  A
successful result should retain sharp finite constants when practical, expose
the matching attack, and be simpler than a proof based on stepwise bad-event
deletion or threshold-tuned mirror counting.

Signed representatives do not change the true distinguishing advantage.
Their purpose is to combine transcript atoms and cancel disconnected hidden
structures before an absolute value is taken.  Every final operational claim
must still be transported back to honest transcript laws.

## 2. Evidence labels

Every item in this program uses one of four labels.

```text
CLOSED
  Exact identity or inequality checked from the model, with all normalizations
  and boundary cases accounted for.

DERIVED
  Complete pen-and-paper derivation with identified lemmas, but not yet
  independently formalized or peer reviewed.

OPEN
  A precisely stated mathematical obligation whose truth is not yet known.

CONJECTURAL
  A plausible target suggested by the representative or an attack, but not yet
  supported by a complete derivation.
```

Published results are marked separately from all four labels.  A literature
comparison is range-qualified: construction, oracle access, adaptivity,
group, query range, and normalization must agree.

## 3. Program-level success criteria

A branch is complete only when it has all of the following.

- An exact random-system game and a reduction from adaptive interaction to the
  claimed transcript law.
- A representative whose pushforward is proved to be the real or ideal law.
- An exact leading statistic and a concrete Boolean test of that statistic.
- A two-sided comparison between optimal advantage and proxy advantage.
- A finite remainder bound with stated constants and parameter range.
- Sparse, transition, dense, and saturation behavior where those regimes
  exist.
- A matching attack, preferably ratio-optimal asymptotically.
- A source-audited comparison with previous results in overlapping ranges.
- Explicit separation of abelian, nonabelian, public-permutation, inverse-query,
  and simulator-based games.

Lean formalization is a later gate.  It must not be used to conceal an
unsettled analytic estimate or an ambiguous model.

## 4. Research branches

### G1. Two-permutation SoP over a general finite group

Detailed note:
[`sop2-general-groups.md`](sop2-general-groups.md).

Exact construction:

```text
F(x) = pi1(x) * pi2(x),
```

where `pi1` and `pi2` are independent uniform permutations of a finite group
`G`, `N = |G|`.

Primary target:

```text
|Adv_G(q,N) - A_col(q,N)| <= Delta_group(q,N),

A_col(q,N)
  = N/(2*(N-1)^2)
      * E |K_q - binom(q,2)/N|.
```

Here `K_q` is the number of equal pairs in an ideal uniform answer tape.

Current state:

- CLOSED: exact compatible-count likelihood for every finite group.
- CLOSED: universal collision component, honest collision proxy, and threshold
  attack.
- CLOSED: `Adv_G(2,N) = 1/(N*(N-1))`.
- DERIVED: a basis-free partition-Mobius finite remainder certificate using
  only sampling-without-replacement ANOVA and singleton cancellation.
- OPEN: sharp scalar summation of that certificate as `q` grows with `N`.
- CLOSED: abelianization checksum lower bound at full depth.
- CLOSED: exact small-group examples showing that the higher-order answer
  cannot depend on `N` alone.

Desired analytic endpoint:

```text
Delta_group(q,N) = O(q^2/N^3),  q=o(N).
```

If this is proved, the same collision law and matching threshold attack give
the sharp sparse, fixed-Poisson, and dense-normal asymptotics uniformly across
finite groups before saturation.

Stop condition: do not claim a universal all-depth theorem depending only on
`N`.  At high query depth, the answer depends on the square/word-map profile,
abelianization, irreducible structure, and group-table transversals.

### G2. One-permutation SoP over a general finite group

Detailed note:
[`sop1-general-groups.md`](sop1-general-groups.md).

Repository construction:

```text
Y_i = A_i * B_i,
```

where all `2q` endpoints come from one uniform permutation and are therefore
distinct.

This must not be conflated with published Boolean XOR1 or with finite-abelian
difference constructions.  They agree only under additional algebraic
assumptions, most notably exponent two.

Primary exact statistic:

```text
r_G(y) = #{a in G : a*a = y}.
```

Current state:

- CLOSED: honest representative as independent endpoint pairs conditioned on
  global distinctness.
- CLOSED: exact one-query law and advantage in terms of `r_G`.
- CLOSED: impossibility of a sharp group-order-only theorem.
- CLOSED: for finite abelian groups, an exact independent-row binomial proxy
  parameterized by `t = |G[2]|`.
- CLOSED: explicit likelihood-threshold attack against that proxy.
- OPEN: an `L1` bound for connected diagrams spanning multiple endpoint pairs.
- CLOSED: checksum and abelianization saturation lower bounds.

Next constrained theorem:

```text
|Adv_G(q) - BinomialProxy(N,t,q)|
  <= explicit connected-diagram remainder
```

for finite abelian `G`, retaining every two-row component exactly and bounding
only components on at least three rows.

Stop condition: do not advertise this as an improvement to Boolean XOR1.
DNS already attains the exact zero-output statistic in its proved Boolean
range.  The new opportunity is a simpler explanation, a range extension, or a
new group-dependent theorem for the repository's sum/product model.

### G3. Broader symmetric-cryptography benchmarks

Detailed audit:
[`signed-pds-symmetric-benchmarks.md`](signed-pds-symmetric-benchmarks.md).

The current ranked portfolio is:

| Rank | Benchmark | Intended gain | Confidence |
|---:|---|---|---|
| 1 | Truncated permutation | Sharp occupancy formula in every regime | Very high |
| 2 | Key-alternating ciphers | Pointwise complete-link bound | High |
| 3 | Cascaded LRW2 / LRW+ | Remove a square-root mirror term | High-medium |
| 4 | Equal-length CBC-MAC | Resolve the message-length gap | Medium |
| 5 | OMAC/CMAC/XCBC/TMAC | Cancel invisible internal path accidents | Medium |
| 6 | HCTR2 | Remove switching loss and merge collision scores | High for simplification |
| 7 | FX/DESX | Exact finite interpolation and constants | High for constants |
| 8 | Three-round Luby-Rackoff | Exact occupancy proof and constant | High for simplicity |
| 9 | DbHtS/LightMAC+/PMAC+ | Replace mirror counting by gain cycles | Medium-high |
| 10 | Keyed sponge | Separate capacity collisions from links | Medium |
| 11 | Triple encryption | Direct complete-path process | Medium |
| 12 | Generalized Feistel | Connected coalescence proof | Medium-low |
| 13 | GCM | Profile-sensitive constants and cleaner separation | Medium for exposition |
| 14 | OCB3 | Offset-profile bound with fewer cases | Medium-low |
| 15 | Simulator indifferentiability | Requires a new minimax theorem | Speculative |

The first four concrete research targets are:

```text
Truncated permutation:
  Adv = pair-occupancy proxy + lower-order clusters.

t-round key-alternating cipher:
  Adv <= C_t * min(1, q_e * product_i(q_i) / N^t)
         + overlap remainder.

Cascaded LRW2:
  Adv <= C*q^4/N^3 + C'*q^2/N^2
         + higher connected cycles.

Equal-length permutation CBC-MAC:
  decide whether Adv = O(q^2/N), independent of message length,
  or extract the first surviving length-dependent attack.
```

Only the truncated-permutation target currently has both an exact published
likelihood and a clearly identified proxy that should support a short proof.
The other displayed bounds are research targets, not theorems.

## 5. Execution order

The program should proceed by proof mechanism, not by construction prestige.

### Phase A: validate the analytic engine

1. Truncated permutation: derive the signed occupancy expansion.
2. Prove an averaged cluster-tail bound uniform across the sparse-to-normal
   transition.
3. Recover sharp constants and the collision-count matching test.

Go/no-go gate: the method must beat a pointwise Taylor/union bound and preserve
the Poisson and normal constants.  Otherwise it is not ready for graph systems.

### Phase B: finish the group extensions

4. Sum the general-group SoP2 partition-Mobius certificate first at fixed
   collision rate, then for `q=o(N)`.
5. Work out finite-abelian SoP1 with the `2G` count and every two-row diagram
   retained exactly.
6. Audit dense complements and saturation separately; do not extrapolate a
   sparse proxy through a global invariant.

Go/no-go gate: obtain a two-sided theorem and one explicit test.  An upper
bound alone is insufficient.

### Phase C: connected graph systems

7. Key-alternating complete-link clusters.
8. Cascaded-LRW2 zero-gain cycle space.
9. CBC-MAC and OMAC rooted path forests.

Go/no-go gate: disconnected components must cancel by an exact involution,
quotient, or conditional expectation before any absolute-value estimate.

### Phase D: constant and exposition projects

10. HCTR2, FX/DESX, and three-round Luby-Rackoff.
11. DbHtS, keyed sponge, triple encryption, and generalized Feistel.
12. GCM and OCB3 only where the attack shows constants or query profiles can
    actually improve.

### Phase E: simulator-based systems

13. Prove a separate minimax/rounding theorem for signed virtual simulator
    certificates.
14. Only then study sponge, Merkle-Damgard, or public-function Feistel
    indifferentiability.

Signed mass cannot answer online simulator queries.  Applying the current
fixed-system theory directly to indifferentiability would be unsound.

## 6. Review gates before formalization

Each pen-and-paper theorem must pass these gates in order.

1. Model audit: exact oracle interface, inverse access, adaptivity, and query
   normalization.
2. Source audit: original theorem pages and attacks, not secondary summaries.
3. Carrier audit: prove the representative pushes forward to the intended
   honest law.
4. Sign audit: identify exactly where negative coefficients occur and why the
   operational inequality remains sound.
5. Boundary audit: `q=0`, `q=1`, first nonzero query depth, maximum query depth,
   and saturation.
6. Small-instance audit: exact enumeration on several nonisomorphic carriers
   wherever group or graph structure may matter.
7. Matching-attack audit: compare the same statistic to both the proxy and the
   real law.
8. Constant audit: avoid replacing denominators or summations prematurely.
9. Independent mathematical review.
10. Only after gates 1--9: design the Lean statement surface.

## 7. Deliverables

For each successful branch, produce:

- a standalone mathematical note;
- a one-page ELI5 representative explanation;
- an exact finite theorem and an asymptotic corollary;
- a matching-attack theorem;
- a source comparison table;
- a list of dependencies suitable for later formalization;
- explicit counterexamples showing where the theorem cannot generalize.

The immediate deliverables are therefore:

```text
T1  Truncated-permutation signed occupancy theorem.
T2  General-group SoP2 scalar tail summation.
T3  Finite-abelian SoP1 connected-pair theorem.
T4  Key-alternating complete-link identity.
T5  Cascaded-LRW2 forest-cancellation identity.
T6  CBC-MAC first surviving terminal-connected diagram.
```

## 8. What would count as failure

The program should report a negative result rather than force a favorable
bound when any of the following occurs.

- The proposed proxy misses a known attack statistic.
- A disconnected structure remains visible after transcript pushforward.
- The remainder is the same order as the proxy in the target regime.
- A claimed group-independent result is contradicted by equal-order groups.
- A public-permutation or inverse-query game is analyzed as if its primitive
  were hidden.
- A signed simulator is used without an honest causal rounding theorem.
- A purported improvement compares different security games or nonoverlapping
  parameter ranges.

The representative is a discovery tool.  If the calculation exposes a new
connected obstruction, the correct output may be a matching attack rather than
the hoped-for upper bound.
