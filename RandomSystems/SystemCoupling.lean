/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.FundamentalTheorem

/-!
# System Coupling (Theorem 2)

Lean 4 formalization of Theorem 2 from Lanzenberger-Maurer (TCC 2020).

## Main Results

* `system_coupling_theorem` — **Theorem 2**: For any PDS S, T, there exist
  equivalent S' ≡ S and T' ≡ T with a joint distribution such that
  Adv(S, T) = Pr(S' ≠ T').

## Design Notes

Theorem 2 is a corollary of Theorem 1 combined with the optimal coupling
lemma (Lemma 4): the infimum in Delta is achieved by some S', T',
and the coupling lemma gives a joint distribution achieving equality.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}
  [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  [DecidableEq (DDS X Y q)]

/-- A system coupling of two PDS: equivalent representatives with a
joint distribution witnessing the advantage. -/
structure SystemCoupling (S T : PDS X Y q) where
  /-- An equivalent representative of S. -/
  S' : PDS X Y q
  /-- An equivalent representative of T. -/
  T' : PDS X Y q
  /-- S' is equivalent to S. -/
  hS : S ≡ₚ S'
  /-- T' is equivalent to T. -/
  hT : T ≡ₚ T'
  /-- The coupling of the representative distributions. -/
  coupling : DistCoupling S'.dist T'.dist
  /-- The coupling achieves equality: Adv = Pr(S' ≠ T'). -/
  achieves_equality : advantage S T = coupling.prDisagree

omit [DecidableEq (DDS X Y q)] in
/-- Equivalent PDS have equal weight.

  S ≡ₚ T → |S.dist| = |T.dist|

The transcript distribution is an fTransform of S.dist, which preserves
weight. So equal transcript distributions force equal weights. -/
theorem equiv_weight (S T : PDS X Y q) (h : S ≡ₚ T)
    (hne : Nonempty (Fin q → X)) :
    S.dist.weight = T.dist.weight := by
  obtain ⟨inputs⟩ := hne
  have h_eq := h inputs
  have : (S.transcriptDist inputs).weight = (T.transcriptDist inputs).weight := by
    rw [h_eq]
  simp only [PDS.transcriptDist] at this
  rw [Dist.weight_fTransform, Dist.weight_fTransform] at this
  exact this

/-- **Theorem 2**: For any two PDS S and T with equal weight,
there exists a system coupling.

There exist S' ≡ S and T' ≡ T with a joint distribution over DDS
pairs such that Adv(S, T) = Pr(S' ≠ T').

This combines Theorem 1 (Delta = Adv) with the optimal coupling lemma. -/
theorem system_coupling_exists
    (S T : PDS X Y q) (hw : S.dist.weight = T.dist.weight)
    (hne : Nonempty (Fin q → X)) :
    ∃ (_ : SystemCoupling S T), True := by
  -- Step 1: Get optimal representatives from Theorem 1's constructive content
  obtain ⟨S', T', hS, hT, hd⟩ := exists_equiv_achieving_advantage S T
  -- Step 2: The representatives have equal weight
  have hw' : S'.dist.weight = T'.dist.weight := by
    have h1 := equiv_weight S S' hS hne
    have h2 := equiv_weight T T' hT hne
    rw [← h1, ← h2]; exact hw
  -- Step 3: Get optimal coupling achieving statDist = prDisagree
  obtain ⟨C, hC⟩ := optimal_coupling_exists S'.dist T'.dist hw'
  exact ⟨⟨S', T', hS, hT, C, hd.symm.trans hC⟩, trivial⟩

end RandomSystems
