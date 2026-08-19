import SequenceHash.RandomSystems.CommonCarrierGame
import SequenceHash.RandomSystems.OccupiedLink

/-!
# The occupied-link common carrier as a random-system game

This module connects the exact finite occupied-link calculation to the
pre-winning behavior machinery.  An arbitrary deterministic interpretation of
the pair `(hidden endpoint, visible answer)` may be used; data processing is
built in because all three carrier pieces are pushed through the same map.
-/

noncomputable section

open RandomSystems
open RandomSystems.CR18

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

universe u v w

variable {C : Type u} [Fintype C] [DecidableEq C] [Nonempty C]
variable {Q : Type v} {A : Type w}

/-- Interpret a finite occupied-link carrier as a PDS. -/
def occupiedLinkSystem (interpret : C × C → PFunDDS.DDS Q A)
    (law : RandomSystems.Dist (C × C)) : PFunPDS Q A :=
  RandomSystems.Dist.fTransform interpret law

/-- The real occupied-link game: common mass is not won and real excess is
won immediately. -/
def occupiedLinkRealGame (occupied : Finset C) (stored : C → C)
    (interpret : C × C → PFunDDS.DDS Q A) : PFunPDS Q (A × Bool) :=
  commonCarrierGame
    (occupiedLinkSystem interpret (occupiedLinkCommon occupied stored))
    (occupiedLinkSystem interpret (occupiedLinkRealResidual occupied stored))

/-- The ideal occupied-link game uses the same common mass and tags only the
ideal excess as won. -/
def occupiedLinkIdealGame (occupied : Finset C) (stored : C → C)
    (interpret : C × C → PFunDDS.DDS Q A) : PFunPDS Q (A × Bool) :=
  commonCarrierGame
    (occupiedLinkSystem interpret (occupiedLinkCommon occupied stored))
    (occupiedLinkSystem interpret (occupiedLinkIdealResidual occupied stored))

/-- Stripping the real game reconstructs the interpreted real link law. -/
theorem ignoreMBO_occupiedLinkRealGame (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    PFunPDS.ignoreMBO (occupiedLinkRealGame occupied stored interpret) =
      occupiedLinkSystem interpret (occupiedLinkReal occupied stored) := by
  rw [occupiedLinkRealGame, ignoreMBO_commonCarrierGame]
  unfold occupiedLinkSystem
  rw [← finiteFTransform_add, occupiedLinkCommon_add_realResidual]

/-- Stripping the ideal game reconstructs the interpreted ideal link law. -/
theorem ignoreMBO_occupiedLinkIdealGame (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    PFunPDS.ignoreMBO (occupiedLinkIdealGame occupied stored interpret) =
      occupiedLinkSystem interpret occupiedLinkIdeal := by
  rw [occupiedLinkIdealGame, ignoreMBO_commonCarrierGame]
  unfold occupiedLinkSystem
  rw [← finiteFTransform_add, occupiedLinkCommon_add_idealResidual]

omit [Nonempty C] in
/-- The two games have exactly the same pre-winning transcript mass. -/
theorem occupiedLinkGame_massYAfalseEq (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    MassYAfalseEq
      (occupiedLinkRealGame occupied stored interpret)
      (occupiedLinkIdealGame occupied stored interpret) := by
  exact commonCarrierGame_massYAfalseEq _ _ _

/-- The real-side game is an honest probability distribution. -/
theorem occupiedLinkRealGame_isProbDist (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    (occupiedLinkRealGame occupied stored interpret).isProbDist := by
  apply commonCarrierGame_isProbDist
  · exact (occupiedLinkCommon_nonNeg occupied stored).fTransform interpret
  · exact (occupiedLinkRealResidual_nonNeg occupied stored).fTransform interpret
  · unfold occupiedLinkSystem
    rw [Dist.weight_fTransform, Dist.weight_fTransform,
      ← finiteWeight_add, occupiedLinkCommon_add_realResidual,
      (occupiedLinkReal_isProbDist occupied stored).weight_eq]

/-- The ideal-side game is an honest probability distribution. -/
theorem occupiedLinkIdealGame_isProbDist (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    (occupiedLinkIdealGame occupied stored interpret).isProbDist := by
  apply commonCarrierGame_isProbDist
  · exact (occupiedLinkCommon_nonNeg occupied stored).fTransform interpret
  · exact (occupiedLinkIdealResidual_nonNeg occupied stored).fTransform interpret
  · unfold occupiedLinkSystem
    rw [Dist.weight_fTransform, Dist.weight_fTransform,
      ← finiteWeight_add, occupiedLinkCommon_add_idealResidual,
      occupiedLinkIdeal_isProbDist.weight_eq]

omit [Nonempty C] in
/-- Both occupied-link representatives are monotone games. -/
theorem occupiedLinkRealGame_monotoneMBO (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    MonotoneMBO (occupiedLinkRealGame occupied stored interpret) :=
  commonCarrierGame_monotoneMBO _ _

omit [Nonempty C] in
theorem occupiedLinkIdealGame_monotoneMBO (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    MonotoneMBO (occupiedLinkIdealGame occupied stored interpret) :=
  commonCarrierGame_monotoneMBO _ _

/-- The tagged residual on either side has exactly the sharp occupied-link
weight.  No union bound or triangle inequality occurs in this local step. -/
theorem occupiedLinkRealGame_residual_weight (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    (occupiedLinkSystem interpret
      (occupiedLinkRealResidual occupied stored)).weight =
        (occupied.card : ℝ) * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 := by
  rw [occupiedLinkSystem, Dist.weight_fTransform,
    occupiedLinkRealResidual_weight, occupiedLink_statDist]

theorem occupiedLinkIdealGame_residual_weight (occupied : Finset C)
    (stored : C → C) (interpret : C × C → PFunDDS.DDS Q A) :
    (occupiedLinkSystem interpret
      (occupiedLinkIdealResidual occupied stored)).weight =
        (occupied.card : ℝ) * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 := by
  rw [occupiedLinkSystem, Dist.weight_fTransform,
    occupiedLinkIdealResidual_weight, occupiedLink_statDist]

/-- Every adaptive winner pays at most the exact occupied-link residual.  The
statement is strategy-independent; all query ordering is hidden inside
`interpret` and the winner. -/
theorem occupiedLinkRealGame_winProb_le
    (occupied : Finset C) (stored : C → C)
    (interpret : C × C → PFunDDS.DDS Q A)
    (winner : RandomSystems.Dist (PFunDDS.Winner Q A))
    (winnerProbability : winner.isProbDist) :
    winProb winner (occupiedLinkRealGame occupied stored interpret) ≤
      (occupied.card : ℝ) * ((Fintype.card C : ℝ) - 1) /
        (Fintype.card C : ℝ) ^ 2 := by
  calc
    winProb winner (occupiedLinkRealGame occupied stored interpret) ≤
        (occupiedLinkSystem interpret
          (occupiedLinkRealResidual occupied stored)).weight :=
      winProb_commonCarrierGame_le_residual_weight winner _ _
        winnerProbability
        ((occupiedLinkRealResidual_nonNeg occupied stored).fTransform interpret)
    _ = (occupied.card : ℝ) * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 :=
      occupiedLinkRealGame_residual_weight occupied stored interpret

/-- Random-systems endpoint for one occupied-link replacement.  Once the
chosen interpretation is total for the queried round, the existing
pre-winning-equivalence chain turns the exact common carrier into a bound on
the ordinary distinguishing advantage. -/
theorem occupiedLink_advantage_le
    (occupied : Finset C) (stored : C → C)
    (interpret : C × C → PFunDDS.DDS Q A)
    (distinguisher : RandomSystems.Dist (PFunDDS.DDD Q A)) (i : ℕ)
    (distinguisherProbability : distinguisher.isProbDist)
    (queriesExactly : ∀ deterministic ∈ distinguisher.support,
      QueriesExactly (PFunDDS.ddToDDE deterministic) (i + 1))
    (realTotal : TotalUpTo
      (occupiedLinkRealGame occupied stored interpret) (i + 1))
    (idealTotal : TotalUpTo
      (occupiedLinkIdealGame occupied stored interpret) (i + 1)) :
    (advantage distinguisher
      (occupiedLinkSystem interpret (occupiedLinkReal occupied stored))
      (occupiedLinkSystem interpret occupiedLinkIdeal) : ℝ) ≤
        (occupied.card : ℝ) * ((Fintype.card C : ℝ) - 1) /
          (Fintype.card C : ℝ) ^ 2 := by
  let realGame := occupiedLinkRealGame occupied stored interpret
  let idealGame := occupiedLinkIdealGame occupied stored interpret
  have realProbability : realGame.isProbDist :=
    occupiedLinkRealGame_isProbDist occupied stored interpret
  have idealProbability : idealGame.isProbDist :=
    occupiedLinkIdealGame_isProbDist occupied stored interpret
  have beforeWinning : MassYAfalseEqAt realGame idealGame i :=
    (occupiedLinkGame_massYAfalseEq occupied stored interpret).at i
  have gameBound := advantage_le_winProb_of_massYAfalseEqAt
    distinguisher realGame idealGame i
    distinguisherProbability.nonNeg realProbability.nonNeg
    idealProbability.nonNeg
    (realProbability.weight_eq.trans idealProbability.weight_eq.symm)
    beforeWinning queriesExactly realTotal idealTotal
  rw [show PFunPDS.ignoreMBO realGame =
        occupiedLinkSystem interpret (occupiedLinkReal occupied stored) by
      exact ignoreMBO_occupiedLinkRealGame occupied stored interpret,
    show PFunPDS.ignoreMBO idealGame =
        occupiedLinkSystem interpret occupiedLinkIdeal by
      exact ignoreMBO_occupiedLinkIdealGame occupied stored interpret]
    at gameBound
  exact gameBound.trans
    (occupiedLinkRealGame_winProb_le occupied stored interpret
      (RandomSystems.Dist.fTransform PFunDDS.ddToDDE distinguisher)
      (RandomSystems.Dist.fTransform_isProbDist _ distinguisherProbability))

end MDSimulator
end RandomSystemsModel
end SequenceHash
