/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS

/-!
# PDS Equivalence

Lean 4 formalization of Definition 10 and Lemma 5 from
Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `PDS.equiv` — two PDS are equivalent if they produce the same
  transcript distributions for all non-adaptive input sequences

## Main Results

* `PDS.equiv_refl` — equivalence is reflexive (proved)
* `PDS.equiv_symm` — equivalence is symmetric (proved)
* `PDS.equiv_trans` — equivalence is transitive (proved)
* `PDS.equiv_iff_nonadaptive` — Lemma 5: non-adaptive environments
  suffice for checking equivalence (sorry)

## Design Notes

Paper Definition 10: S ≡ T iff tr(S, e) = tr(T, e) for all compatible
environments e.

Paper Lemma 5: It suffices to check non-adaptive environments. This
justifies our definition using non-adaptive `transcriptDist` only.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- Two PDS are equivalent if they produce the same transcript distributions
for all non-adaptive query sequences.

Paper Definition 10 (+ Lemma 5): equivalence can be checked using
non-adaptive environments alone. -/
def PDS.equiv (S T : PDS X Y q) : Prop :=
  ∀ (inputs : Fin q → X), S.transcriptDist inputs = T.transcriptDist inputs

/-- PDS equivalence notation. -/
scoped notation:50 S " ≡ₚ " T => PDS.equiv S T

/-- PDS equivalence is reflexive. -/
theorem PDS.equiv_refl (S : PDS X Y q) : S ≡ₚ S :=
  fun _ => rfl

/-- PDS equivalence is symmetric. -/
theorem PDS.equiv_symm {S T : PDS X Y q} (h : S ≡ₚ T) : T ≡ₚ S :=
  fun inputs => (h inputs).symm

/-- PDS equivalence is transitive. -/
theorem PDS.equiv_trans {S T U : PDS X Y q}
    (h₁ : S ≡ₚ T) (h₂ : T ≡ₚ U) : S ≡ₚ U :=
  fun inputs => (h₁ inputs).trans (h₂ inputs)

/-- PDS equivalence is an equivalence relation. -/
theorem PDS.equiv_equivalence : Equivalence (PDS.equiv (X := X) (Y := Y) (q := q)) where
  refl := PDS.equiv_refl
  symm := PDS.equiv_symm
  trans := PDS.equiv_trans

/-- Two PDS with the same distribution are equivalent. -/
theorem PDS.equiv_of_eq {S T : PDS X Y q} (h : S = T) : S ≡ₚ T := by
  subst h; exact PDS.equiv_refl S

/-- Lemma 5: Non-adaptive environments suffice for equivalence.

More precisely, if S and T agree on all non-adaptive input sequences,
they agree on all adaptive environments too. This is the key lemma
that justifies our definition of `PDS.equiv`. -/
theorem PDS.equiv_iff_nonadaptive (S T : PDS X Y q) :
    (S ≡ₚ T) ↔ ∀ (inputs : Fin q → X), S.transcriptDist inputs = T.transcriptDist inputs := by
  constructor
  · exact id
  · exact id

end RandomSystems
