# Random Systems in Lean 4

A standalone formalization of Maurer's random systems framework for
cryptographic indistinguishability proofs.

## What Are Random Systems?

A **random system** is an abstract object that answers queries
probabilistically. In round i, it receives input X_i and produces
output Y_i, where Y_i may depend (probabilistically) on all
previous inputs and outputs.

The framework, introduced by Maurer (EUROCRYPT 2002) and refined
by Lanzenberger & Maurer (TCC 2020), provides a clean theory for
proving that two systems are indistinguishable:

- A **DDS** (deterministic discrete system) is a concrete lookup
  table: a partial function `s : X+ -> Y`.
- A **PDS** (probabilistic discrete system) is a distribution
  over DDS — "fix the random tape to get a deterministic system."
- A **random system** is an equivalence class of PDS under
  behavioral equivalence.
- The **advantage** Adv(S, T) measures how well any adaptive
  environment can distinguish systems S from T.

The central result (Theorem 1) shows that the advantage equals
Delta(S, T), the infimum statistical distance over PDS representatives.
This means you can prove indistinguishability by exhibiting a
coupling of deterministic systems — no need to reason about
adaptive environments.

## Structure

```
RandomSystems/
  Dist.lean              -- Distributions (A ->_0 NNReal)
  StatDist.lean          -- Statistical distance
  Coupling.lean          -- Coupling lemma
  DDS.lean               -- Deterministic discrete systems
  DDE.lean               -- Environments
  Transcript.lean        -- Interaction transcripts
  PDS.lean               -- Probabilistic discrete systems
  Equiv.lean             -- PDS equivalence
  Successor.lean         -- Successor operation (key proof technique)
  Advantage.lean         -- Adv and Delta
  FundamentalTheorem.lean -- Theorem 1: Delta = Adv
  SystemCoupling.lean    -- Theorem 2: Adv = Pr(S != T)
  Construction.lean      -- n-ary constructions
  Combiner.lean          -- (k,n)-combiners
  Amplification.lean     -- Theorem 3: indistinguishability amplification
  Instances/
    URF.lean             -- Uniform Random Function
    URP.lean             -- Uniform Random Permutation
    BoolDDS.lean         -- Example: Boolean single-query systems
```

See [BLUEPRINT.md](BLUEPRINT.md) for the detailed plan, milestones,
and paper-to-code map.

## Building

```bash
lake update
lake build
```

Requires Lean 4 v4.28.0-rc1 and Mathlib.

## References

- Lanzenberger & Maurer, "Coupling of Random Systems" (TCC 2020)
- Maurer, "Indistinguishability of Random Systems" (EUROCRYPT 2002)
- Maurer, Pietrzak & Renner, "Indistinguishability Amplification" (CRYPTO 2007)

## License

Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license.
