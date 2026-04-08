/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Crypto Notation DSL — Design Notes

Paper-like notation for cryptographic probability proofs in Lean 4.
This file sits in `random-systems` (foundation layer); h-technique imports
it and adds its own extensions in `HTechnique/Notation.lean`.

All notation should be `scoped` (opt-in via `open ... in`).

## Status: DESIGN ONLY — nothing implemented yet.

---

## V1 Notation Surface

### Foundation (this file)

| Paper             | Lean notation              | Expands to                              | Mechanism              |
|-------------------|----------------------------|-----------------------------------------|------------------------|
| `Unif(K)`         | `𝒰[K]`                    | `Dist.uniform K`                        | `scoped notation`      |
| `δ(X, Y)`        | `δ(X, Y)`                 | `statDist X Y`                          | `scoped notation`      |
| `Δ(S, T)`        | `Δ(S, T)`                 | `delta S T`                             | `scoped notation`      |
| `X ⊗ Y`          | `X ⊗ Y`                   | `Dist.prod X Y`                         | `scoped infix`         |
| `Pr[φ | x ←$ D]` | `Pr[φ | x ←$ D]`          | `Dist.evalPred D (fun x => φ)`  (new)  | `scoped syntax + macro`|
| `sample x ←$ D`  | `sample x ←$ D return t`  | `Dist.fTransform (fun x => t) D`       | `scoped syntax + macro`|
| `Tr(S, inputs)`   | `Tr[S, inputs]`            | `S.transcriptDist inputs`              | `scoped notation`      |
| `Trₐ(S, e)`      | `Trₐ[S, e]`               | `S.adaptiveTranscriptDist e`           | `scoped notation`      |

### H-Technique extensions (in HTechnique/Notation.lean)

| Paper               | Lean notation      | Expands to                    |
|----------------------|--------------------|------------------------------ |
| `Pr_bad(D, B)`       | `Pr_bad[D, B]`     | `probBad D B`                |
| `Advₙ(S, T)`        | `Advₙ[S, T]`      | `advantage S T`              |
| `Advₐ(S, T)`        | `Advₐ[S, T]`      | `advantageAdaptive S T`      |

---

## Design Decisions

### 1. Notation on top of named defs, not raw combinators

`Pr[φ | x ←$ D]` must expand to a named def `Dist.evalPred` (new),
NOT directly to `Dist.evalSet ... (Finset.univ.filter ...)`.
Otherwise `simp` and `rw` break because the notation hides structure
that lemmas are stated about.

**Action:** Define `Dist.evalPred` in `Dist.lean` before adding notation.

### 2. Explicit uniform: `𝒰[K]` not bare `K`

Lean macros run before elaboration, so they cannot distinguish a type
from a `Dist` value. Using `𝒰[K]` avoids needing a custom elaborator.
If we later want `x ←$ K` to mean `x ←$ 𝒰[K]`, that requires an
elaborator (v2).

### 3. No `C(q,2)` notation

`C` is already a common identifier (e.g., construction variable in
`Amplification.lean`). Too conflict-prone. Keep `Nat.choose q 2` or
define `choose₂ q` as a named def.

### 4. Advantage must distinguish adaptive vs non-adaptive

`Advantage.lean` defines both `advantage` and `advantageAdaptive`.
A bare `Adv[...]` is ambiguous. Use `Advₙ` and `Advₐ`.

### 5. No tactic macros in v1

Term notation is stable and local. Tactic macros (`by union_bound`,
`by h_technique`) are brittle, hide side conditions, and give worse
error messages. Defer to v2 if ever.

### 6. Start with identifier binders only

Tuple destructuring `(h, ρ) ←$ D` is feasible but adds complexity.
V1 supports `coin ←$ D` with manual `.1`/`.2` access. Tuple patterns
in v2.

---

## Lean 4 Mechanism Notes

- Simple aliases (`δ`, `Δ`, `𝒰`, `⊗`, `Tr`, `Trₐ`): plain `scoped notation`
  or `scoped infix`. Follow Mathlib's `Probability/Notation.lean` pattern.

- Binder notation (`Pr[... | x ←$ D]`, `sample x ←$ D return t`):
  custom `scoped syntax` + `scoped macro`. Same pattern as Mathlib's
  bracketed probability notation and `∫ x, f x ∂μ`.

- Use `notation3` for true binder notation where the binder precedes
  the body. Use `scoped macro` when the surface is bracketed.

- Be careful with precedence — document explicitly (Mathlib warns about
  this for integrals in `Bochner/Basic.lean`).

---

## What HashThenPRF Would Look Like

```
-- BEFORE (current):
Dist.evalSet (Dist.uniform K)
  (Finset.univ.filter (fun k => hash k m = hash k m')) ≤ eps

-- AFTER:
Pr[hash k m = hash k m' | k ←$ 𝒰[K]] ≤ ε


-- BEFORE:
Dist.fTransform
  (fun (coin : K × (X → Y)) =>
    (fun i => hashThenPRF Hf coin.1 coin.2 (ms i), coin.1))
  (Dist.uniform (K × (X → Y)))

-- AFTER:
sample coin ←$ 𝒰[K × (X → Y)] return
  (fun i => hashThenPRF Hf coin.1 coin.2 (ms i), coin.1)


-- BEFORE:
statDist (realExtDist Hf ms) (idealExtDist ms) ≤ choose2 q * Hf.eps

-- AFTER:
δ(realExtDist Hf ms, idealExtDist ms) ≤ choose₂ q * Hf.ε
```

---

## Implementation Order

1. Define `Dist.evalPred` in `Dist.lean` (the named def that `Pr[...]` expands to)
2. Simple scoped notations: `δ`, `Δ`, `𝒰`, `⊗`, `Tr`, `Trₐ`
3. Binder notation: `Pr[... | x ←$ D]`
4. Binder notation: `sample x ←$ D return t`
5. H-technique extensions: `Pr_bad`, `Advₙ`, `Advₐ`
6. Refactor one application (HashThenPRF) as proof-of-concept
7. v2: tuple binders, `Func(X,Y)`, `Perm(X)`

---

## References

- Mathlib `Probability/Notation.lean` — scoped notation pattern
- Mathlib `MeasureTheory/Integral/Bochner/Basic.lean` — binder notation with precedence
- Mathlib `Probability/Kernel/Composition/CompNotation.lean` — infix for distribution composition
- Our `RandomSystems/Equiv.lean` — existing scoped notation in this codebase
-/
