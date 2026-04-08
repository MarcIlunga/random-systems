/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Advantage

/-!
# Crypto Notation DSL

Paper-like notation for cryptographic probability proofs.

All notation is `scoped` — opt-in via `open RandomSystems.CryptoNotation`.

## Implemented (N-01, N-02)

| Paper           | Lean               | Expands to                        |
|-----------------|--------------------|-----------------------------------|
| `δ(X, Y)`      | `δ(X, Y)`         | `statDist X Y`                    |
| `Δ(S, T)`      | `Δ(S, T)`         | `delta S T`                       |
| `Unif(A)`       | `𝒰[A]`            | `Dist.uniform A`                  |
| `X ⊗ Y`        | `X ⊗ₚ Y`          | `Dist.prod X Y`                   |
| `Tr(S, xs)`     | `Tr[S, xs]`        | `S.transcriptDist xs`             |
| `Trₐ(S, e)`    | `Trₐ[S, e]`       | `S.adaptiveTranscriptDist e`      |

## Planned (N-03..N-07)

See design notes at the bottom of this file.
-/

namespace RandomSystems.CryptoNotation

open RandomSystems

-- ===== N-02: Simple scoped notations =====

/-- Statistical distance: `δ(X, Y)` for `statDist X Y`. -/
scoped notation "δ(" X ", " Y ")" => statDist X Y

/-- Infimum distance between PDS: `Δ(S, T)` for `delta S T`. -/
scoped notation "Δ(" S ", " T ")" => delta S T

/-- Uniform distribution: `𝒰[A]` for `Dist.uniform A`. -/
scoped notation "𝒰[" A "]" => Dist.uniform A

/-- Independent product: `X ⊗ₚ Y` for `Dist.prod X Y`.
Uses `⊗ₚ` (not bare `⊗`) to avoid conflict with Mathlib's tensor product. -/
scoped infixl:70 " ⊗ₚ " => Dist.prod

/-- Non-adaptive transcript distribution: `Tr[S, xs]`. -/
scoped notation "Tr[" S ", " xs "]" => PDS.transcriptDist S xs

/-- Adaptive transcript distribution: `Trₐ[S, e]`. -/
scoped notation "Trₐ[" S ", " e "]" => PDS.adaptiveTranscriptDist S e

-- ===== N-03 + N-07: Probability binder notation =====

/-- Probability notation with general binder pattern:
- `Pr[φ(x) | x ←$ D]` — single variable
- `Pr[φ(a,b) | (a, b) ←$ D]` — pair destructuring
- `Pr[φ(a,b,c) | (a, b, c) ←$ D]` — triple destructuring

Expands to `Dist.evalPred D (fun pat => φ(pat))`. -/
scoped syntax "Pr[" term " | " Lean.Parser.Term.funBinder " ←$ " term "]" : term
scoped macro_rules
  | `(Pr[$body | $b:funBinder ←$ $D]) => `(Dist.evalPred $D (fun $b => $body))

-- ===== N-04 + N-07: Sample/pushforward binder notation =====

/-- Sampling notation with general binder pattern:
- `sample x ←$ D return t` — single variable
- `sample (h, ρ) ←$ D return t` — pair destructuring
- `sample (a, b, c) ←$ D return t` — triple destructuring

Expands to `Dist.fTransform (fun pat => t) D`. -/
scoped syntax "sample " Lean.Parser.Term.funBinder " ←$ " term " return " term : term
scoped macro_rules
  | `(sample $b:funBinder ←$ $D return $body) =>
    `(Dist.fTransform (fun $b => $body) $D)

end RandomSystems.CryptoNotation

/-!
## Design Notes (N-03..N-07) — NOT YET IMPLEMENTED

### N-03: `Pr[φ | x ←$ D]`

Needs `scoped syntax` + `scoped macro`. Expands to `Dist.evalPred D (fun x => φ)`.
`evalPred` is defined in `Dist.lean` (N-01, done).

Lean mechanics: custom syntax with binder. Follow Mathlib `Probability/Notation.lean`.

### N-04: `sample x ←$ D return t`

Expands to `Dist.fTransform (fun x => t) D`. Also `scoped syntax` + `scoped macro`.
Start with identifier binders; tuple destructuring in v2.

### N-05: H-technique extensions (in `HTechnique/Notation.lean`)

- `Pr_bad[D, B]` → `probBad D B`
- `Advₙ[S, T]` → `advantage S T`
- `Advₐ[S, T]` → `advantageAdaptive S T`

### N-06: Refactor HashThenPRF as proof-of-concept

### N-07: v2 — tuple binders, `Func(X,Y)`, `Perm(X)`
-/
