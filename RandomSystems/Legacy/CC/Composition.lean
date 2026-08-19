/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.CC.Advantage

/-!
# Constructive Cryptography: Composition Theorem

Lean 4 formalization of the CC composition theorem: the central result
that enables modular security proofs.

## Main Definitions

* `CCConstruction` — a CC construction: resource R constructs resource S
  using protocol π within error ε
* `serial_composition` — compose two constructions sequentially

## Main Results

* `composition_theorem` — serial composition: if R →^{π₁,ε₁} S and
  S →^{π₂,ε₂} T, then R →^{π₂∘π₁, ε₁+ε₂} T

## Design Notes

The composition theorem is THE core result of CC. It says that
constructions compose: if you can build S from R with error ε₁,
and T from S with error ε₂, then you can build T from R with
error ε₁ + ε₂. The composed protocol applies π₁ first, then π₂.

References:
- Maurer, "Constructive Cryptography — A New Paradigm" (2011), Theorem 1
- Maurer-Renner, "Abstract Cryptography" (2011), Theorem 2
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

namespace CC

variable {n : ℕ}
  {X Y : Fin n → Type*} {q : Fin n → ℕ}
  [inst : ∀ i, Fintype (DDS (X i) (Y i) (q i))]
  [∀ i, Fintype (Transcript (X i) (Y i) (q i))]
  [∀ i, DecidableEq (Transcript (X i) (Y i) (q i))]
  [∀ i, Fintype (X i)]

/-- A CC construction: resource R constructs resource S at interface `i`
using converter `conv` within error `ε`.

This means: after applying `conv` at interface `i` of R, the result
is within distance ε of S. There exists a simulator `sim` for the
adversary's interface.

Maurer 2011, Definition 2: R →^{π,ε} S means
  d(πⁱR, S) ≤ ε

In the full CC framework, the construction also involves a simulator
at the adversary's interface, but we start with the simpler single-interface
version. -/
structure CCConstruction
    (R S : CCResource X Y q)
    (i : Fin n) where
  /-- The protocol converter applied at the honest interface. -/
  conv : Converter (X i) (Y i) (q i)
  /-- The security bound. -/
  ε : NNReal
  /-- The security guarantee: applying the converter yields something
      within distance ε of the target. -/
  secure : resourceAdvantage (applyConverter i conv R) S ≤ ε

/-- Serial composition of CC constructions.

If R →^{π₁,ε₁} S at interface i, and S →^{π₂,ε₂} T at interface i,
then R →^{π₂∘π₁, ε₁+ε₂} T at interface i.

Maurer 2011, Theorem 1: constructions compose with additive error. -/
def composition_theorem
    {R S T : CCResource X Y q} {i : Fin n}
    (c₁ : CCConstruction R S i)
    (c₂ : CCConstruction S T i)
    (c₂_nonexpansive : ∀ (A B : PDS (X i) (Y i) (q i)),
      advantage (c₂.conv.apply A) (c₂.conv.apply B) ≤ advantage A B) :
    CCConstruction R T i where
  conv := Converter.comp c₂.conv c₁.conv
  ε := c₁.ε + c₂.ε
  secure := by
    -- Goal: Adv(applyConverter i (c₂∘c₁) R, T) ≤ ε₁ + ε₂
    -- Strategy: triangle inequality through S
    --   Adv(c₂(c₁(R)), T) ≤ Adv(c₂(c₁(R)), c₂(S)) + Adv(c₂(S), T)
    --                       ≤ Adv(c₁(R), S)           + ε₂        [nonexpansive]
    --                       ≤ ε₁                       + ε₂        [c₁.secure]
    have h_comp : applyConverter i (Converter.comp c₂.conv c₁.conv) R =
        applyConverter i c₂.conv (applyConverter i c₁.conv R) := by
      simp [applyConverter, Converter.comp, Function.comp, Function.update_self]
    rw [h_comp]
    calc resourceAdvantage (applyConverter i c₂.conv (applyConverter i c₁.conv R)) T
        ≤ resourceAdvantage (applyConverter i c₂.conv (applyConverter i c₁.conv R))
            (applyConverter i c₂.conv S) +
          resourceAdvantage (applyConverter i c₂.conv S) T :=
          resourceAdvantage_triangle _ _ _
      _ ≤ resourceAdvantage (applyConverter i c₁.conv R) S +
          resourceAdvantage (applyConverter i c₂.conv S) T := by
          gcongr
          exact compose_context_nonexpansive i c₂.conv c₂_nonexpansive _ _
      _ ≤ c₁.ε + c₂.ε := by
          gcongr
          · exact c₁.secure
          · exact c₂.secure

/-- Parallel composition: converters at different interfaces compose.

If R →^{π₁,ε₁} S at interface i, and S →^{π₂,ε₂} T at interface j ≠ i,
then the combined construction has error ≤ ε₁ + ε₂. -/
theorem parallel_composition
    {R S T : CCResource X Y q}
    {i j : Fin n} (_hij : i ≠ j)
    (c₁ : CCConstruction R S i)
    (c₂ : CCConstruction S T j)
    (c₂_nonexpansive : ∀ (A B : PDS (X j) (Y j) (q j)),
      advantage (c₂.conv.apply A) (c₂.conv.apply B) ≤ advantage A B) :
    resourceAdvantage
        (applyConverter j c₂.conv (applyConverter i c₁.conv R)) T ≤
      c₁.ε + c₂.ε := by
  calc resourceAdvantage (applyConverter j c₂.conv (applyConverter i c₁.conv R)) T
      ≤ resourceAdvantage (applyConverter j c₂.conv (applyConverter i c₁.conv R))
          (applyConverter j c₂.conv S) +
        resourceAdvantage (applyConverter j c₂.conv S) T :=
        resourceAdvantage_triangle _ _ _
    _ ≤ resourceAdvantage (applyConverter i c₁.conv R) S +
        resourceAdvantage (applyConverter j c₂.conv S) T := by
        gcongr
        exact compose_context_nonexpansive j c₂.conv c₂_nonexpansive _ _
    _ ≤ c₁.ε + c₂.ε := by
        gcongr
        · exact c₁.secure
        · exact c₂.secure

end CC

end RandomSystems
