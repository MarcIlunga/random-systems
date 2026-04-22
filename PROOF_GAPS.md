# Proof Gaps & Issues — Random Systems Formalization

## Status: 3 sorry, 0 custom axioms (verified 2026-04-08)

Full project builds successfully (1130 Lake jobs). Only standard Lean axioms
(propext, Classical.choice, Quot.sound) appear in `#print axioms`.

Sorry breakdown:
- 2 original core theory (Theorem 1 inductive step, Amplification general k)
- 0 condition-based proof technique — **ALL PROVED**
- 0 PRF/PRP switching application — **ALL PROVED**
- 1 adaptive Boneh–Shoup cascade application (prefix-free adaptive environment bound)
- 0 CBC-MAC application (delegates to condition-based framework)

---

## Sorry 1: Theorem 1 Inductive Step

**File:** `RandomSystems/FundamentalTheorem.lean:132`
**Theorem:** `exists_equiv_achieving_advantage_ind` (succ case)
**Severity:** HIGH — blocks full Theorem 1 (Δ = Adv)

**What's proved:**
- Base case (q=0): DDS is subsingleton, transcript function is injective, statDist preserved
- IH correctly formulated: for each (x,y), optimal S'_xy ≡ S^{↑x↓y}, T'_xy ≡ T^{↑x↓y}
- Both directions of Theorem 1 proved assuming this sorry

**What's needed for the inductive step (paper pp. 17-18):**
1. **Advantage decomposition via successor**:
   `advantage S T = sup_x ∑_y advantage(S.successor x y, T.successor x y)`
   This itself requires showing non-adaptive advantage equals adaptive advantage
   (our `PDS.equiv` definition sidesteps this, but advantage is over transcript
   distributions, so the decomposition via `Fin.cons` is needed).

2. **PDS reconstruction from successor families**: Given optimal successor distributions
   S'_xy for each (x,y), reconstruct a (q+1)-query PDS S' via `DDS.reconstruct`.
   Infrastructure exists (`DDS.reconstruct`, `DDS.decompose` equivalence) but the
   distribution-level reconstruction (building `Dist (DDS X Y (q+1))` from
   first-query marginal + successor distributions) is not formalized.

3. **Lemma 6 of the paper** (joint distribution from marginals): Given marginals
   X₁,...,Xₙ that sum to the same total weight, construct a joint distribution
   whose marginals match. Not formalized.

**Difficulty:** Hard. This is the core mathematical content of the paper.
Each sub-piece is ~100-200 lines of Lean. Total estimated: 400-600 lines.

**Source of difficulty:** Formalization, not paper bugs. The paper proof is correct
but relies on measure-theoretic constructions (conditional distributions, product
measures) that must be built from Finsupp primitives.

---

## Sorry 2: Amplification Theorem (General k)

**File:** `RandomSystems/Amplification.lean:57`
**Theorem:** `amplification_theorem`
**Severity:** MEDIUM — k=1 case and Corollary 1 are proved

**Statement:** For a (k,n)-combiner with black-box reduction:
  `Adv(C(Ss), I_out) ≤ binom(n, k-1) · ε^k`

**What's proved:**
- k=1 case (`amplification_theorem_k1`): ✅ fully proved via hybrid argument
- (1,2)-combiner bound (`threshold_combiner_bound_1_2`): ✅ fully proved

**What's needed:**
- Combinatorial counting: enumerate subsets of size k-1
- For each subset J of "bad" (non-ideal) components with |J| = k-1:
  the remaining n-(k-1) components include at least k ideal ones,
  so the threshold combiner gives C(Ss_J) ≡ I_out
- Combine via union bound / inclusion-exclusion

**Difficulty:** Medium. The combinatorics is standard but requires Mathlib's
`Finset.powerset` and `Nat.choose` machinery.

**Source of difficulty:** Formalization (combinatorial bookkeeping in Lean).
The paper proof is correct.

---

## Sorry 3: Adaptive Boneh–Shoup Cascade Bound

**File:** `RandomSystems/Applications/BonehShoupCascadeAdaptive.lean:63`
**Theorem:** `advantageAdaptiveOn_URFfunCascadeIdeal_URFfun_prefixFreeEnv_le_birthday`
**Severity:** LOW — adaptive extension only; the file is not imported by `RandomSystems.lean`

**Statement:** For prefix-free adaptive environments, the ideal cascade and URF
are indistinguishable up to the birthday bound:
  `advantageAdaptiveOn(...) ≤ birthdayBound (q * (ℓ + 1)) (Fintype.card K)`

**What's proved:**
- The fixed-input / non-adaptive Boneh–Shoup cascade development lives in
  `RandomSystems/Applications/BonehShoupCascade.lean`
- The adaptive condition-based infrastructure exists, including
  `ConditionBased.advantageAdaptive_le_condition_failure`
- The adaptive target theorem and proof plan are in place so downstream work can
  target a stable statement

**What's needed:**
- An environment-lifting lemma relating tag-only interaction under `e` to
  trace-level interaction under a lifted environment
- An adaptive variant of the trace-level "equal on good transcripts" lemma
- A proof of the adaptive failure-probability / birthday bound under the
  prefix-free restriction

**Difficulty:** Medium. The mathematics is standard; the missing work is mostly
adaptive-environment plumbing.

**Source of difficulty:** Formalization and environment-lifting infrastructure.
This is an extension module rather than a gap in the imported core development.

---

## Proved Results (Previously Sorry)

### ✅ Condition-Based Proof Technique (Maurer 2002)

**File:** `RandomSystems/ConditionBased.lean`

- `advantage_le_condition_failure`: **PROVED** — Two-sided bound
  `S ≡_A T → Adv(S,T) ≤ ν(S,A) + ν(T,A)`. Key technique: pushforward
  regrouping lemma `fTransform_filter_sum` that relates filtered fTransform
  sums to filtered sums over the original domain.

- `advantage_le_single_failure`: **PROVED** — One-sided bound
  `Adv(S,T) ≤ ν(S,A)`. Uses same pushforward regrouping directly without
  needing the equal-weight hypothesis (the one-directional statDist already
  gives the single-sided bound).

### ✅ PRF/PRP Switching Application (q=1)

**File:** `RandomSystems/Applications/PRPPRFSwitching.lean`

- `urf_urp_transcriptDist_eq`: **PROVED** — For q=1, URF and URP induce the
  same transcript distribution exactly.
- `urf_collision_bound`: **PROVED** — For q=1, the failure probability is 0
  because the "all outputs distinct" condition holds trivially (one element
  is always injective). The birthday bound `1·0/(2|X|) = 0` matches.

- `urf_urp_cond_equiv`: **PROVED** — Conditional equivalence follows from full
  transcript distribution equality.

- `prf_prp_switching_q1`: **PROVED** — The q=1 PRF/PRP switching advantage is 0
  by transcript distribution equality and `statDist_self`.

---

## Non-Sorry Issues

### Issue 1: Equiv.lean — Lemma 5 is Trivially True by Definition

**File:** `RandomSystems/Equiv.lean:85-89`

The paper's Lemma 5 states: "Non-adaptive environments suffice for checking
equivalence." This is a non-trivial statement: if two PDS agree on all
*non-adaptive* environments, they agree on all *adaptive* environments.

Our formalization DEFINES equivalence as agreement on non-adaptive environments
(transcript distributions for fixed input sequences). So Lemma 5 is trivial
by definition — both directions are `id`.

**Impact:** Low. The definition is the right one for all our theorems.
The "hard" direction (adaptive → non-adaptive) would require formalizing
adaptive environments and their transcript distributions, which we don't need.

**Status:** Acknowledged in code comments. Not a gap — a design choice.

### Issue 2: PDS Allows Sub-distributions

**File:** `RandomSystems/PDS.lean:46-48`

PDS wraps `Dist (DDS X Y q)` without requiring weight = 1. The `isProbPDS`
predicate exists but is not enforced.

**Impact:** None. This is intentional — sub-distributions arise in the
inductive proof of Theorem 1 (conditioning on first query produces
sub-distributions). All theorems are correct without the weight=1 assumption.

### Issue 3: Construction Has No "Uses Components" Requirement

**File:** `RandomSystems/Construction.lean:39-51`

The `Construction` structure only requires `respects_equiv`. A construction
could ignore all its components (constant function). The `black_box_reduction`
hypothesis in amplification theorems enforces meaningful component usage.

**Impact:** Low. This is standard in game-based security: the reduction
hypothesis captures what we need. Adding a structural requirement would be
non-trivial and not match the paper.

### Issue 4: Instance Management Complexity

Theorems that do induction on `q` (the query count) must use `DDS.instFintype`
explicitly rather than section variables `[Fintype (DDS X Y q)]`, because
induction changes `q` and the derived instance for `q+1` differs from the
section's assumed instance.

**Current fix:** `exists_equiv_achieving_advantage` uses `@PDS X Y q DDS.instFintype`
explicitly. The `MainTheorem` section derives instances automatically. Bridging
between them uses `Subsingleton.elim` on Fintype instances.

**Impact:** Adds complexity to theorem statements but is mathematically sound.

### Issue 5: URP Only Defined for q=1

**File:** `RandomSystems/Instances/URP.lean`

The Uniform Random Permutation is only formalized for single-query systems
(q=1). Multi-query URP requires handling the consistency constraint: a
permutation must respond consistently to repeated inputs.

**Impact:** Limits PRF/PRP switching to q=1 case. Multi-query requires
extending URP to handle the "lazy sampling" pattern where the permutation
is built incrementally.

---

## Paper vs Formalization Gaps

| Paper Concept | Formalized? | Notes |
|---|---|---|
| Def 1-4 (Dist, marginal, statDist, fTransform) | ✅ | |
| Lemma 1 (joint from marginals) | ❌ | Not needed yet; would help Theorem 1 step |
| Lemma 2 (partition of statDist) | ✅ | `statDist_partition` |
| Lemma 3 (data processing inequality) | ✅ | Both ≤ and = (injective) versions |
| Lemma 4 (coupling bound + optimal coupling) | ✅ | |
| Def 5-7 (DDS, DDE, transcript) | ✅ | |
| Def 8-10 (PDS, equiv) | ✅ | Equiv defined via non-adaptive only |
| Lemma 5 (non-adaptive suffices) | ✅ (trivial) | By definition; adaptive version not formalized |
| Notation 2 (successor) | ✅ | Both DDS and PDS levels |
| Def 11-12 (advantage, delta) | ✅ | |
| Lemma 6 (joint from marginals, systems) | ❌ | Needed for Theorem 1 step |
| **Theorem 1** (Δ = Adv) | ⚠️ | 1 sorry in inductive step |
| **Theorem 2** (system coupling) | ✅ | Uses Theorem 1 |
| Def 13-15 (construction, combiner) | ✅ | |
| Hybrid argument bound | ✅ | `construction_advantage_bound` |
| **Theorem 3** (amplification, general k) | ⚠️ | 1 sorry; k=1 proved |
| Corollary 1 ((1,2)-combiner) | ✅ | |
| Condition-based proof technique (Mau02) | ✅ | **ALL PROVED** |
| PRF/PRP switching (Mau02 Sec 4.1) | ✅ (q=1) | q=1 fully proved; multi-query still blocked because URP is only defined for q=1 |
| CBC-MAC security (Mau02 Sec 4.2) | ✅ | Delegates to ConditionBased |

---

## No Paper Bugs Found

The papers (Lanzenberger-Maurer TCC 2020, Maurer EUROCRYPT 2002) appear
mathematically correct. All difficulties encountered stem from formalization
challenges:
- Building distribution-level operations from Finsupp primitives
- Lean instance management during induction on type-level parameters
- Combinatorial bookkeeping for the amplification bound
- Bridging DDS types with Mathlib's function/permutation infrastructure
- Lifting fixed-input arguments to adaptive prefix-free environments
- URP only defined for single-query case

The paper proofs are sketches (especially Theorem 1 pp. 17-18 and
Theorem 3) but the mathematical content is sound.
