# Random Systems in Lean 4

Standalone Lean 4 formalization of Maurer's random systems framework for cryptographic indistinguishability proofs.

A random system answers adaptive queries: at round $i$ it receives $X_i$ and returns $Y_i$, where each $Y_i$ may depend on the prior transcript. The central theorem identifies $\text{Adv}(S, T)$ with $\Delta(S, T)$, so indistinguishability proofs can be reduced to couplings of deterministic systems instead of direct reasoning about adaptive environments.

## Notation and Proof Tooling

`RandomSystems/Notation.lean` provides a paper-style DSL with `Pr[...]`, `sample ... return`, $\delta(X, Y)$, $\Delta(S, T)$, `𝒰[...]`, `Tr[...]`, and `Trₐ[...]`.

`RandomSystems/DistSimpAttr.lean` and `RandomSystems/DistSimp.lean` define the curated `dist_simp` simp set, used as `simp only [dist_simp]` to normalize common `Dist` expressions.

## Structure

```text
RandomSystems/
├── Dist.lean
├── Counting.lean
├── DistSimpAttr.lean
├── DistSimp.lean
├── Notation.lean
├── StatDist.lean
├── Coupling.lean
├── DDS.lean
├── DDE.lean
├── Transcript.lean
├── PDS.lean
├── Equiv.lean
├── Successor.lean
├── Advantage.lean
├── FundamentalTheorem.lean
├── SystemCoupling.lean
├── Construction.lean
├── HConstruction.lean
├── Combiner.lean
├── Amplification.lean
├── ConditionBased.lean
├── Instances/
│   ├── BoolDDS.lean
│   ├── URF.lean
│   ├── URFfunEval.lean
│   └── URP.lean
└── Applications/
    ├── PRPPRFSwitching.lean
    ├── PRPPRFSwitchingGeneral.lean
    ├── CBCMAC.lean
    ├── CTRMode.lean
    └── CascadePRF.lean
```

See [BLUEPRINT.md](BLUEPRINT.md) for the paper-to-code map.

## Building

```bash
lake update
lake build
```

Requires Lean 4 `v4.28.0-rc1` and Mathlib `v4.28.0-rc1`.

## References

- Lanzenberger & Maurer, "Coupling of Random Systems" (TCC 2020)
- Maurer, "Indistinguishability of Random Systems" (EUROCRYPT 2002)
- Maurer, Pietrzak & Renner, "Indistinguishability Amplification" (CRYPTO 2007)

## License

Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license.
