/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.PDS
import RandomSystems.Legacy.Equiv

/-!
# Successor Operation

Lean 4 formalization of Notation 2 from Lanzenberger-Maurer (TCC 2020).

The successor operation `S^{↑x↓y}` conditions a PDS on the first
query having input `x` and output `y`, then shifts to a (q-1)-query
system. This is the key proof technique for the inductive proof of
Theorem 1 (Delta = Advantage).

## Main Definitions

* `PDS.successorDist` — the distribution induced by successor on each DDS

## Design Notes

`DDS.successor` is defined in `DDS.lean`. Here we lift it to the PDS level.
The PDS successor conditions on the first query:

  S^{↑x↓y}(s') := ∑_{s : s.firstQuery x = y, s.successor x = s'} S(s)
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}

/-- The first-query distribution of a PDS: for each pair (x, y),
the total mass of DDS that respond with y to input x.

  P_S(y | x) := ∑_{s : s.firstQuery x = y} S.dist(s) -/
def PDS.firstQueryMass [DecidableEq Y] [Fintype (DDS X Y (q + 1))]
    (S : PDS X Y (q + 1)) (x : X) (y : Y) : NNReal :=
  ∑ s ∈ S.dist.support.filter
    (fun s => s.firstQuery (Nat.zero_lt_succ q) x = y),
    S.dist s

/-- The successor preserves weight (conditional weight).

  |S^{↑x↓y}| = P_S(y | x) -/
theorem PDS.successor_weight [DecidableEq X] [DecidableEq Y]
    [Fintype (DDS X Y (q + 1))] [Fintype (DDS X Y q)]
    (S : PDS X Y (q + 1)) (x : X) (y : Y) :
    (S.successor x y).dist.weight = S.firstQueryMass x y := by
  classical
  simp only [PDS.successor, PDS.firstQueryMass, Dist.weight]
  rw [Finsupp.sum_sum_index (fun _ => rfl) (fun _ _ _ => rfl),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  dsimp only
  split_ifs with h
  · exact Finsupp.sum_single_index rfl
  · exact Finsupp.sum_zero_index

/-- The total weight over all successor outputs equals the total weight
of mass assigned to DDS whose first input is `x`.

  ∑_y |S^{↑x↓y}| = |S| -/
theorem PDS.successor_total_weight [DecidableEq X] [DecidableEq Y]
    [Fintype X] [Fintype Y]
    [Fintype (DDS X Y (q + 1))] [Fintype (DDS X Y q)]
    (S : PDS X Y (q + 1)) (x : X) :
    ∑ y : Y, (S.successor x y).dist.weight = S.dist.weight := by
  simp_rw [PDS.successor_weight]
  unfold PDS.firstQueryMass Dist.weight
  rw [Finset.sum_fiberwise]
  rfl

/-- The successor PDS preserves equivalence.

If S ≡ₚ T then S.successor x y ≡ₚ T.successor x y for all x, y.

Proof idea: The transcript distribution of S.successor x y under inputs'
is determined by the transcript distribution of S under (x :: inputs'),
restricted to transcripts whose first output is y. Since S ≡ₚ T implies
equal transcript distributions for all inputs (including x :: inputs'),
the restricted/conditioned distributions are also equal. -/
-- Helper: the transcript distribution of a successor PDS can be computed
-- by conditioning and projecting the original transcript distribution.
private lemma successor_transcriptDist_eq
    [DecidableEq X] [DecidableEq Y]
    [Fintype (DDS X Y (q + 1))] [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y (q + 1))] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y (q + 1))] [DecidableEq (Transcript X Y q)]
    (S : PDS X Y (q + 1)) (x : X) (y : Y) (inputs' : Fin q → X) :
    (S.successor x y).transcriptDist inputs' =
    (S.transcriptDist (Fin.cons x inputs')).sum (fun t w =>
      if t ⟨0, Nat.zero_lt_succ q⟩ = (x, y)
      then Finsupp.single (fun i => t ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) w
      else 0) := by
  simp only [PDS.transcriptDist, PDS.successor, Dist.fTransform]
  rw [Finsupp.sum_sum_index (fun a => Finsupp.single_zero _)
    (fun a b₁ b₂ => Finsupp.single_add _ _ _)]
  rw [Finsupp.sum_sum_index
    (fun a => by split_ifs <;> simp)
    (fun a b₁ b₂ => by split_ifs <;> simp [Finsupp.single_add])]
  -- Now both sides are Finsupp.sum S.dist (fun s w => ...). Show they agree pointwise.
  congr 1; funext s w
  -- Simplify RHS via sum_single_index
  rw [Finsupp.sum_single_index (by split_ifs <;> simp)]
  -- Use DDS lemmas relating transcript to firstQuery/successor
  have h_tr0 : s.transcript (Fin.cons x inputs') ⟨0, Nat.zero_lt_succ q⟩ =
      (x, s.firstQuery (Nat.zero_lt_succ q) x) := DDS.transcript_zero_cons s x inputs'
  -- Split on firstQuery condition (LHS has this if-then-else)
  by_cases h : s.firstQuery (Nat.zero_lt_succ q) x = y
  · -- Case: firstQuery s x = y
    rw [if_pos h, Finsupp.sum_single_index (Finsupp.single_zero _)]
    rw [show s.transcript (Fin.cons x inputs') ⟨0, _⟩ = (x, y) by rw [h_tr0]; exact Prod.ext rfl h]
    simp only [ite_true]
    congr 1; funext i
    exact (DDS.transcript_succ_cons s x inputs' i).symm
  · -- Case: firstQuery s x ≠ y
    rw [if_neg h, Finsupp.sum_zero_index]
    have : ¬(s.transcript (Fin.cons x inputs') ⟨0, Nat.zero_lt_succ q⟩ = (x, y)) := by
      rw [h_tr0]; exact fun heq => h (Prod.ext_iff.mp heq).2
    rw [if_neg this]

theorem PDS.successor_preserves_equiv
    [DecidableEq X] [DecidableEq Y]
    [Fintype (DDS X Y (q + 1))] [Fintype (DDS X Y q)]
    [Fintype (Transcript X Y (q + 1))] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y (q + 1))] [DecidableEq (Transcript X Y q)]
    {S T : PDS X Y (q + 1)} (h : S ≡ₚ T) (x : X) (y : Y) :
    S.successor x y ≡ₚ T.successor x y := by
  intro inputs'
  rw [successor_transcriptDist_eq S x y inputs',
      successor_transcriptDist_eq T x y inputs',
      h (Fin.cons x inputs')]

end RandomSystems
