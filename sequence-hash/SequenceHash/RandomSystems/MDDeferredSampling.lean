import SequenceHash.RandomSystems.DeferredSampling
import SequenceHash.RandomSystems.MDHash

/-!
# Merkle--Damgaard instance of deferred sampling

This file connects the generic adaptive-fibre theorem to an MD path.  The
schedule's next compression point is `(IV, block[0])` initially and thereafter
`(previous chaining value, block[m])`.  Thus the generic `FreshAt` predicate is
literally freshness of all compression points on the path.
-/

noncomputable section

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

universe u

variable {C B : Type u}

/-- First `m` blocks of a block stream. -/
def blockPrefix (blocks : ℕ → B) (m : ℕ) : List B :=
  (List.range m).map blocks

@[simp]
theorem blockPrefix_zero (blocks : ℕ → B) : blockPrefix blocks 0 = [] := by
  rfl

theorem blockPrefix_succ (blocks : ℕ → B) (m : ℕ) :
    blockPrefix blocks (m + 1) = blockPrefix blocks m ++ [blocks m] := by
  simp [blockPrefix, List.range_succ]

/-- Adaptive compression schedule of one MD path. -/
def mdPathSchedule (iv : C) (blocks : ℕ → B) :
    AdaptiveSchedule (C × B) C where
  next := fun {m} history =>
    match m with
    | 0 => (iv, blocks 0)
    | previous + 1 => (history (Fin.last previous), blocks (previous + 1))

@[simp]
theorem mdPathSchedule_next_zero (iv : C) (blocks : ℕ → B)
    (history : Fin 0 → C) :
    (mdPathSchedule iv blocks).next history = (iv, blocks 0) := by
  rfl

@[simp]
theorem mdPathSchedule_next_succ (iv : C) (blocks : ℕ → B) (m : ℕ)
    (history : Fin (m + 1) → C) :
    (mdPathSchedule iv blocks).next history =
      (history (Fin.last m), blocks (m + 1)) := by
  rfl

/-- The final answer of the adaptive schedule is exactly the ordinary MD fold
over the corresponding stream prefix. -/
theorem adaptiveRun_mdPath_last (compression : Compression C B) (iv : C)
    (blocks : ℕ → B) (m : ℕ) :
    adaptiveRun (mdPathSchedule iv blocks)
        (fun point : C × B => compression point.1 point.2) (m + 1)
        (Fin.last m) =
      mdIterate compression iv (blockPrefix blocks (m + 1)) := by
  induction m with
  | zero =>
      rw [adaptiveRun_succ, Fin.snoc_last,
        mdPathSchedule_next_zero, blockPrefix_succ]
      rfl
  | succ m inductionHypothesis =>
      calc
        adaptiveRun (mdPathSchedule iv blocks)
            (fun point : C × B => compression point.1 point.2) (m + 1 + 1)
            (Fin.last (m + 1)) =
            compression
              (mdIterate compression iv (blockPrefix blocks (m + 1)))
              (blocks (m + 1)) := by
          rw [adaptiveRun_succ, Fin.snoc_last,
            mdPathSchedule_next_succ, inductionHypothesis]
        _ = mdIterate compression iv
              (blockPrefix blocks (m + 1) ++ [blocks (m + 1)]) := by
          rw [mdIterate_append]
          rfl
        _ = mdIterate compression iv (blockPrefix blocks (m + 1 + 1)) := by
          exact congrArg (mdIterate compression iv)
            (blockPrefix_succ blocks (m + 1)).symm

/-- Concrete restricted-law deferred-sampling theorem for an MD path. -/
theorem restrict_mdPath_uniform_eq_restrict_uniform
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype B] [DecidableEq B]
    (iv : C) (blocks : ℕ → B) (m : ℕ)
    (good : (Fin m → C) → Prop) [DecidablePred good]
    (goodFresh : ∀ values, good values →
      FreshAt (mdPathSchedule iv blocks) values) :
    (RandomSystems.Dist.fTransform
          (fun compression : C × B → C =>
            adaptiveRun (mdPathSchedule iv blocks) compression m)
          (RandomSystems.Dist.uniform ((C × B) → C))).restrict good =
      (RandomSystems.Dist.uniform (Fin m → C)).restrict good := by
  exact restrict_adaptiveRun_uniform_eq_restrict_uniform
    (mdPathSchedule iv blocks) m good goodFresh

end MDSimulator
end RandomSystemsModel
end SequenceHash
