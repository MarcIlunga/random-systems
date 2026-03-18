# Blueprint: Maurer's Random Systems in Lean 4

## Overview

A standalone Lean 4 formalization of the random systems framework from:

> **Lanzenberger, D. & Maurer, U. (2020).**
> "Coupling of Random Systems." Theory of Cryptography Conference (TCC 2020).
> https://crypto.ethz.ch/publications/files/LanMau20.pdf

with foundations from:

> **Maurer, U. (2002).**
> "Indistinguishability of Random Systems." EUROCRYPT 2002.

> **Maurer, U., Pietrzak, K. & Renner, R. (2007).**
> "Indistinguishability Amplification." CRYPTO 2007.

## Design Philosophy

### Algebraic Layering

Each layer defines **axioms** (structures with required properties). The layer
below provides **models** (concrete objects verifying the axioms). Theorems
proved from axioms apply to all models.

```
Layer 4: Construction / Combiner    (Def 13-15, Theorem 3)
    |    axiom: respects PDS equivalence
Layer 3: Advantage / Delta          (Def 11-12, Theorem 1-2)
    |    axiom: well-defined on equivalence classes
Layer 2: PDS / Equivalence          (Def 8-10, Lemma 5)
    |    axiom: common domain, finite support
Layer 1: DDS / DDE / Transcript     (Def 5-7)
    |    axiom: prefix-closed domain
Layer 0: Dist / StatDist / Coupling (Def 1-4, Lemma 1-4)
    |    built on Mathlib's Finsupp + NNReal
```

### What We Don't Do

- **No ProbComp / VCVio.** Distributions are `A →₀ NNReal` (Mathlib's
  `Finsupp`), not monadic computations. Maurer's framework is purely
  distributional.
- **No quotient types.** Random systems are equivalence classes conceptually,
  but we avoid Lean's `Quotient` and instead prove that operations are
  well-defined on equivalence classes.
- **No measure theory.** Everything is finite and discrete. We use `Fintype`,
  `Finset.sum`, and `NNReal` — no sigma-algebras needed.

### What We Reuse from Mathlib

| Concept | Mathlib | Our usage |
|---------|---------|-----------|
| Sub-distributions | `Finsupp α NNReal` | `abbrev Dist A := A →₀ NNReal` |
| Finite sums | `Finset.sum`, `BigOperators` | Weight, statistical distance |
| Non-negative reals | `NNReal` | All probabilities |
| Supremum/infimum | `iSup`, `iInf` | Advantage (Def 11), Delta (Def 12) |
| Probability distributions | `PMF` (bridge only) | When weight = 1 |

### What We Write Fresh

| Concept | Paper reference | Why fresh |
|---------|----------------|-----------|
| Statistical distance | Def 3 | Not in Mathlib for Finsupp/NNReal |
| Coupling lemma | Lemma 4 | Reprove for our Dist type |
| DDS, DDE, Transcript | Def 5-7 | Domain-specific |
| PDS, Equivalence | Def 8-10 | Domain-specific |
| Successor operation | Notation 2 | Key proof technique |
| Advantage, Delta | Def 11-12 | Central definitions |
| Theorem 1 (Delta = Adv) | Theorem 1 | The main result |
| Theorem 2 (Coupling) | Theorem 2 | Corollary of Theorem 1 |
| Constructions, Combiners | Def 13-15 | Domain-specific |
| Theorem 3 (Amplification) | Theorem 3 | Application |

## File Structure

```
random-systems/
  lean-toolchain
  lakefile.lean
  RandomSystems.lean                    -- Root import
  RandomSystems/
    -- Layer 0: Probability primitives
    Dist.lean                           -- Def 1-2, 4: Distributions via Finsupp
    StatDist.lean                       -- Def 3, Lemma 2-3: Statistical distance
    Coupling.lean                       -- Lemma 4: Coupling lemma

    -- Layer 1: Deterministic systems
    DDS.lean                            -- Def 5: Deterministic discrete systems
    DDE.lean                            -- Def 6: Deterministic discrete environments
    Transcript.lean                     -- Def 7: Transcripts

    -- Layer 2: Probabilistic systems
    PDS.lean                            -- Def 8-9: Probabilistic discrete systems
    Equiv.lean                          -- Def 10, Lemma 5: PDS equivalence

    -- Proof technique
    Successor.lean                      -- Notation 2: s^{↑x↓y} operation on PDS

    -- Layer 3: Random systems (as equivalence classes)
    Advantage.lean                      -- Def 11-12: Adv and Delta
    FundamentalTheorem.lean             -- Theorem 1: Delta(S,T) = Adv(S,T)
    SystemCoupling.lean                 -- Theorem 2: Adv(S,T) = Pr(S != T)

    -- Layer 4: Constructions
    Construction.lean                   -- Def 13: n-ary constructions
    Combiner.lean                       -- Def 14-15: Combiners
    Amplification.lean                  -- Theorem 3, Corollary 1

    -- Proof technique (Maurer 2002)
    ConditionBased.lean                 -- Condition-based proofs

    -- Applications (Maurer 2002)
    Applications/
      PRPPRFSwitching.lean             -- PRF/PRP switching lemma
      CBCMAC.lean                      -- CBC-MAC security

    -- Concrete instances
    Instances/
      BoolDDS.lean                      -- Example 4: zero, one, id, flip
      URF.lean                          -- Uniform Random Function
      URP.lean                          -- Uniform Random Permutation

  papers/                              -- Reference PDFs
  BLUEPRINT.md                         -- This file
  PROOF_GAPS.md                        -- Proof gaps tracking
  README.md
```

## Import DAG

```
                    Dist
                   /    \
             StatDist    \
            /   |   \    |
      Coupling  |    \   |
                |     \  |
               DDS    DDE
                 \   /
              Transcript
                  |
                 PDS -----> Dist
                  |
                Equiv ----> StatDist
               /    \
        Successor  Advantage
              \      |
         FundamentalTheorem --> Coupling
                  |
           SystemCoupling
                  |
           Construction --> Equiv, Advantage
                  |
              Combiner
                  |
           Amplification --> FundamentalTheorem
```

## Paper-to-Code Map

### Section 2: Preliminaries

| Paper | Code | Status |
|-------|------|--------|
| Def 1 (Distribution) | `Dist.lean`: `abbrev Dist A := A →₀ NNReal` | M1 |
| Def 2 (Marginal) | `Dist.lean`: `Dist.marginal` | M1 |
| Def 3 (Statistical distance) | `StatDist.lean`: `statDist` | M1 |
| Def 4 (f-transformation) | `Dist.lean`: `Dist.fTransform` | M1 |
| Lemma 1 (Joint from marginals) | `Dist.lean`: `joint_from_marginals` | M3 |
| Lemma 2 (Partition of statDist) | `StatDist.lean`: `statDist_partition` | ✅ |
| Lemma 3 (Data processing) | `StatDist.lean`: `statDist_fTransform_le` | ✅ |
| Lemma 3+ (Injective equality) | `StatDist.lean`: `statDist_fTransform_injective` | ✅ |
| Lemma 4 (Coupling bound) | `Coupling.lean`: `coupling_bound` | ✅ |
| Lemma 4 (Optimal coupling) | `Coupling.lean`: `optimal_coupling_exists` | ✅ |

### Section 3: Discrete Random Systems

| Paper | Code | Status |
|-------|------|--------|
| Def 5 (DDS) | `DDS.lean`: `structure DDS` | M1 |
| Def 6 (DDE) | `DDE.lean`: `structure DDE` | M2 |
| Def 7 (Transcript) | `Transcript.lean`: `transcript` | M2 |
| Def 8 (PDS) | `PDS.lean`: `structure PDS` | M2 |
| Def 9 (PDE) | `DDE.lean` (environment analog) | M2 |
| Def 10 (Equivalence) | `Equiv.lean`: `PDS.equiv` | M2 |
| Notation 2 (Successor) | `Successor.lean`: `DDS.successor`, `PDS.successor` | M3 |
| Lemma 5 (Non-adaptive suffices) | `Equiv.lean`: `equiv_iff_nonadaptive` | M2 |
| Example 4 (Bool DDS) | `Instances/BoolDDS.lean` | M2 |
| Example 5 (V, V') | `Instances/URF.lean` | M2 |

### Section 4: Coupling Theorem

| Paper | Code | Status |
|-------|------|--------|
| Def 11 (Advantage) | `Advantage.lean`: `advantage` | ✅ |
| Def 12 (Delta) | `Advantage.lean`: `delta` | ✅ |
| Lemma 6 (Joint from marginals, systems) | `FundamentalTheorem.lean` | ⚠️ sorry |
| **Theorem 1** (Delta = Adv) | `FundamentalTheorem.lean`: `delta_eq_advantage` | ⚠️ 1 sorry |
| **Theorem 2** (System coupling) | `SystemCoupling.lean`: `system_coupling_exists` | ✅ |

### Section 5: Indistinguishability Amplification

| Paper | Code | Status |
|-------|------|--------|
| Def 13 (Construction) | `Construction.lean`: `structure Construction` | ✅ |
| Def 14 (A-combiner) | `Combiner.lean`: `IsCombiner` | ✅ |
| Def 15 ((k,n)-combiner) | `Combiner.lean`: `IsThresholdCombiner` | ✅ |
| Hybrid argument | `Construction.lean`: `construction_advantage_bound` | ✅ |
| **Theorem 3** (Amplification, general k) | `Amplification.lean`: `amplification_theorem` | ⚠️ sorry |
| **Theorem 3** (k=1 case) | `Amplification.lean`: `amplification_theorem_k1` | ✅ |
| Corollary 1 (1,2)-combiner | `Amplification.lean`: `threshold_combiner_bound_1_2` | ✅ |

### Maurer 2002: Condition-Based Proofs & Applications

| Paper | Code | Status |
|-------|------|--------|
| Condition-based proof technique | `ConditionBased.lean`: `advantage_le_condition_failure` | ⚠️ sorry |
| Conditional equivalence | `ConditionBased.lean`: `PDS.condEquiv` | ✅ |
| PRF/PRP switching (Sec 4.1) | `Applications/PRPPRFSwitching.lean` | ⚠️ 3 sorry |
| CBC-MAC security (Sec 4.2) | `Applications/CBCMAC.lean` | ⚠️ types done |
| Birthday bound | `Applications/PRPPRFSwitching.lean`: `birthdayBound` | ✅ defined |

## Milestones

### M1: Foundations (Layer 0 + DDS skeleton) — ✅ COMPLETE

All proof targets achieved with no sorry:
- `statDist_self`, `statDist_symm_of_eq_weight`, `statDist_triangle`
- `statDist_partition` (Lemma 2), `statDist_fTransform_le` (Lemma 3)
- `statDist_fTransform_injective` (Lemma 3+)
- `dds1Equiv : DDS X Y 1 ≃ (X → Y)`

### M2: Systems (Layer 1-2) — ✅ COMPLETE

All proof targets achieved with no sorry:
- `PDS.equiv_refl`, `PDS.equiv_symm`, `PDS.equiv_trans`
- `URF_isProbPDS`, `URP_isProbPDS`
- `interact_nonadaptive` (non-adaptive transcript = simple transcript)

### M3: Advantage + Coupling (Layer 3, partial) — ✅ COMPLETE

All proof targets achieved with no sorry:
- `advantage_self`, `advantage_respects_equiv`, `advantage_triangle`
- `coupling_bound`, `optimal_coupling_exists`
- `PDS.successor_preserves_equiv`, `PDS.successor_total_weight`

### M4: The Central Theorems — ⚠️ 1 SORRY

**Theorem 1** (`delta_eq_advantage`): Proved modulo 1 sorry in the
inductive step of `exists_equiv_achieving_advantage_ind`.

- `advantage_le_delta` (easy direction): ✅ proved
- `delta_le_advantage` (hard direction): Uses `exists_equiv_achieving_advantage`
- `exists_equiv_achieving_advantage` base case (q=0): ✅ proved
- `exists_equiv_achieving_advantage` inductive step: ⚠️ **sorry**
  - IH correctly formulated via `PDS.successor`
  - Requires: advantage decomposition via successor + PDS reconstruction
    from optimal successor families (Lemma 6 of the paper)

**Theorem 2** (`system_coupling_exists`): ✅ proved (uses Theorem 1)

### M5: Constructions + Amplification — ⚠️ 1 SORRY

- `Construction`, `IsCombiner`, `IsThresholdCombiner`: ✅ defined
- `construction_advantage_bound` (hybrid argument): ✅ proved
- `amplification_theorem_k1` (k=1 case): ✅ proved
- `threshold_combiner_bound_1_2` (Corollary 1): ✅ proved
- `amplification_theorem` (general k): ⚠️ **sorry** (needs combinatorial argument)

### M6: Applications (Maurer 2002) — ⚠️ 5 SORRY

- `ConditionBased.lean`: Condition-based proof technique
  - `TranscriptCondition`, `conditionFailureProb`, `PDS.condEquiv`: ✅ defined
  - `advantage_le_condition_failure`: ⚠️ **sorry**
  - `advantage_le_single_failure`: ⚠️ **sorry**
- `Applications/PRPPRFSwitching.lean`: PRF/PRP switching lemma
  - `allOutputsDistinct`, `birthdayBound`: ✅ defined
  - `urf_urp_cond_equiv`: ⚠️ **sorry** (URF ≡_A URP)
  - `urf_collision_bound`: ⚠️ **sorry** (birthday bound)
  - `prf_prp_switching_q1`: ⚠️ **sorry** (Adv = 0 for q=1)
- `Applications/CBCMAC.lean`: CBC-MAC security
  - `cbcMac1`, `cbcMacMulti`, `noInternalCollision`: ✅ defined
  - `cbcMac1_advantage_bound`: ✅ proved (delegates to ConditionBased)
  - `cbcMac1_is_identity_construction`: ✅ proved
  - `cbcMac_bound_value`: ✅ (existential witness)

## Key Design Decisions

### Why `A →₀ NNReal` (not `A → NNReal`)

Mathlib's `Finsupp` gives us `support`, `sum`, `add`, `smul`, decidable
equality, and lattice structure for free. The paper's distributions have
finite support by definition.

### Why `NNReal` (not `ENNReal`)

The paper works with `ℝ≥0`. Distributions have finite weight. No infinity
is needed. `NNReal` has cleaner arithmetic (cancellation, division) than
`ENNReal` where `∞ - ∞ = 0` causes problems.

If we need `PMF` (which uses `ENNReal`), we cast at the bridge point.

### Why No Quotient Types

Lean's `Quotient` requires `Quotient.lift` + equivalence-preservation proofs
for every operation. Instead, we:
1. Define `advantage` and `delta` as functions on PDS
2. Prove they are well-defined on equivalence classes
   (`advantage_respects_equiv`)
3. Use `transport_security_bound` to lift results

This gives the same mathematical content with far less boilerplate.

### Why No `IsRandomSystem` Typeclass

The original plan had a typeclass. But random systems are not a type-level
property — they are a specific mathematical structure (equivalence classes
of PDS). The typeclass pattern (like `Group G`) doesn't fit because we don't
have multiple "random system structures" on the same type. Instead, PDS IS
the concrete representation, and theorems about advantage/equivalence are
plain lemmas.

### DDS Representation: `respond : Fin q → (Fin (i+1) → X) → Y`

The i-th response depends on all inputs so far `(x₁, ..., x_{i+1})`,
making prefix-closure automatic from the type. The successor operation
`s^{↑x}` is natural: prepend x to the input sequence.

Alternative considered: inductive tree. Rejected because Fin-indexed
functions are easier to compute with in Lean (decidable equality, Fintype
instances).

## Estimated Effort

| Milestone | Lines (est.) | Dependencies |
|-----------|-------------|--------------|
| M1 | ~400 | Mathlib only |
| M2 | ~600 | M1 |
| M3 | ~500 | M1 |
| M4 | ~1000-1500 | M2, M3 |
| M5 | ~500-800 | M4 |
| **Total** | **~3000-3800** | |

## References

1. Lanzenberger, D. & Maurer, U. (2020). "Coupling of Random Systems." TCC 2020.
2. Maurer, U. (2002). "Indistinguishability of Random Systems." EUROCRYPT 2002.
3. Maurer, U., Pietrzak, K. & Renner, R. (2007). "Indistinguishability Amplification." CRYPTO 2007.
4. Aldous, D. (1983). "Random walks on finite groups and rapidly mixing Markov chains." (Coupling Lemma)
