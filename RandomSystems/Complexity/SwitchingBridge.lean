/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.AdvantageSeq
import RandomSystems.SwitchingLemma

/-!
# Switching and birthday bridge

This file exposes the CR18 blind-converter and birthday/switching endpoints as
Complexity-layer statement forms.  The public theorem shape is deliberately:

`named hypothesis -> named goal`.

The long CR18 proof obligations still live inside the named hypothesis
predicate.  This keeps theorem use close to the constructive-crypto style:
first build the local statement from the relevant systems, then apply the
bridge.
-/

namespace RandomSystems.CR18
namespace Complexity

open scoped RandomSystems.CR18
open scoped RandomSystems.CR18.CondEquiv

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-- Statement form for CR18 Theorem 4.17's blind endpoint. -/
abbrev BlindTheorem417Bound (S T : PFunPDS X Y) (cond : List (X × Y) → Bool) : Prop :=
  (Δ(S, T) : ℝ) ≤ (Γᵇ (gameOf S cond) : ℝ)

/-- Named hypothesis package for CR18 Theorem 4.17's blind endpoint. -/
abbrev BlindTheorem417Hyp (S T : PFunPDS X Y) (cond : List (X × Y) → Bool) : Prop :=
  PFunDDS.MonotoneCond cond ∧
    S.isProbDist ∧
    T.isProbDist ∧
    CondEquiv.TotalOnNonempty S ∧
    CondEquiv.TotalOnNonempty T ∧
    DeltaFiniteQueryNormalization S T ∧
    (gameOf S cond |≡ T)

namespace BlindTheorem417Hyp

theorem bound {S T : PFunPDS X Y} {cond : List (X × Y) → Bool}
    (h : BlindTheorem417Hyp S T cond) :
    BlindTheorem417Bound S T cond := by
  rcases h with ⟨hcond, hS, hT, hStot, hTtot, hNorm, hCE⟩
  exact maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf S T cond hcond hS hT hStot hTtot hNorm hCE

end BlindTheorem417Hyp

/-- Statement form for CR18 Lemma 4.18, the birthday collision bound. -/
abbrev BirthdayCollisionBound (t q : Nat) : Prop :=
  (pcoll t q : ℝ) ≤ (q : ℝ) ^ 2 / (2 * t)

/-- Minimal named hypothesis for CR18 Lemma 4.18. -/
abbrev BirthdayCollisionHyp (t : Nat) : Prop :=
  0 < t

namespace BirthdayCollisionHyp

theorem bound {t q : Nat} (h : BirthdayCollisionHyp t) :
    BirthdayCollisionBound t q := by
  exact pcoll_le_birthday t q h

end BirthdayCollisionHyp

/-- Statement form for the filtered blind URF collision-game birthday bound. -/
abbrev BlindURFCollisionBound (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X]
    (q : Nat) : Prop :=
  (Γᵇ (gameOf (⌈q⌉ 𝖱 X) (collisionCond (X := X) (Y := X))) : ℝ)
    ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ)

namespace BlindURFCollisionBound

theorem of_finite (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : Nat) :
    BlindURFCollisionBound X q := by
  exact blindMaxWinProb_filterURF_collisionCond_le_birthday X q

end BlindURFCollisionBound

section URFURPClassical

open Classical

/-- Statement form for CR18 Lemma 4.19, the filtered URF/URP switching bound. -/
abbrev URFURPSwitchingBound (X : Type*) [Fintype X] [Nonempty X] (q : Nat) : Prop :=
  Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X)
    ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ)

namespace URFURPSwitchingBound

theorem of_finite (X : Type*) [Fintype X] [Nonempty X] (q : Nat) :
    URFURPSwitchingBound X q := by
  exact urf_urp_switching X q

end URFURPSwitchingBound

end URFURPClassical

end

end Complexity
end RandomSystems.CR18
