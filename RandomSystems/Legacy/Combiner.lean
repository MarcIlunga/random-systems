/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Construction

/-!
# Combiners

Lean 4 formalization of Definitions 14-15 from Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `IsCombiner` — Definition 14: a construction that is ideal when all
  components are ideal
* `IsThresholdCombiner` — Definition 15: a (k,n)-combiner where k ideal
  components suffice for the output to be ideal

## Design Notes

A combiner C is an n-ary construction with the property:
  If all Sᵢ ≡ I (ideal), then C(S₁,...,Sₙ) ≡ I.

A (k,n)-combiner strengthens this: if ANY k of the n components are
ideal, the output is ideal. This is used in Theorem 3 for
indistinguishability amplification.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- A combiner is a construction such that when all components are
equivalent to the ideal system, the output is also equivalent to ideal.

Paper Definition 14. -/
def IsCombiner
    {X' Y' : Type*} {q' : ℕ}
    [Fintype (DDS X' Y' q')]
    [Fintype (Transcript X' Y' q')]
    [DecidableEq (Transcript X' Y' q')]
    {n : ℕ}
    (C : @Construction X Y q _ _ _ X' Y' q' _ _ _ n)
    (I_in : PDS X Y q) (I_out : PDS X' Y' q') : Prop :=
  ∀ (Ss : Fin n → PDS X Y q),
    (∀ i, Ss i ≡ₚ I_in) →
    C.apply Ss ≡ₚ I_out

/-- A (k, n)-combiner: if any k of the n components are ideal,
the output is ideal.

Paper Definition 15: For every subset J ⊆ [n] with |J| ≥ k,
if Sⱼ ≡ I for j ∈ J, then C(S₁,...,Sₙ) ≡ I. -/
def IsThresholdCombiner
    {X' Y' : Type*} {q' : ℕ}
    [Fintype (DDS X' Y' q')]
    [Fintype (Transcript X' Y' q')]
    [DecidableEq (Transcript X' Y' q')]
    {n : ℕ}
    (C : @Construction X Y q _ _ _ X' Y' q' _ _ _ n)
    (k : ℕ) (I_in : PDS X Y q) (I_out : PDS X' Y' q') : Prop :=
  ∀ (Ss : Fin n → PDS X Y q) (J : Finset (Fin n)),
    k ≤ J.card →
    (∀ j ∈ J, Ss j ≡ₚ I_in) →
    C.apply Ss ≡ₚ I_out

/-- A (k,n)-combiner with k ≤ n is also a combiner (k=n case). -/
theorem threshold_combiner_is_combiner
    {X' Y' : Type*} {q' : ℕ}
    [Fintype (DDS X' Y' q')]
    [Fintype (Transcript X' Y' q')]
    [DecidableEq (Transcript X' Y' q')]
    {n : ℕ}
    (C : @Construction X Y q _ _ _ X' Y' q' _ _ _ n)
    (k : ℕ) (I_in : PDS X Y q) (I_out : PDS X' Y' q')
    (hC : IsThresholdCombiner C k I_in I_out) (hk : k ≤ n) :
    IsCombiner C I_in I_out := by
  intro Ss hSs
  exact hC Ss Finset.univ (by rwa [Finset.card_univ, Fintype.card_fin])
    (fun j _ => hSs j)

end RandomSystems
