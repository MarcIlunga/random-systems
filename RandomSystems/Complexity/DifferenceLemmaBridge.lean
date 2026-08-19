/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.GameBased
import RandomSystems.Complexity.GameHop
import RandomSystems.Complexity.Tactics
import RandomSystems.RelateGameDistinguishing

/-!
# Difference-lemma bridge

CR18 Lemma 4.16 has a reduction-shaped conclusion:

`advantage D S⁻ T⁻ ≤ winProb (ddToDDE D) S`.

This file packages that shape as a costed reduction into a real-valued winning
problem.  The concrete CR18 proof obligations for Lemma 4.16 remain in the
local theorem that proves `DifferenceLemmaBound`; the complexity layer only
uses the resulting named hypothesis.
-/

namespace RandomSystems.CR18
namespace Complexity

open RandomSystems (Dist)

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-- A real-valued version of the winning-game problem, useful when a CR18
distinguishing bound compares signed `advantage : ℝ` to winning probability
coerced into `ℝ`. -/
@[reducible] def winningProblemReal (X : Type u) (Y : Type v) :
    Problem (WinningGame X Y) (WinnerSolver X Y) ℝ where
  perf := fun G W => (winProb W G : ℝ)

@[simp] theorem winningProblemReal_perf
    (G : WinningGame X Y) (W : WinnerSolver X Y) :
    (winningProblemReal X Y).perf G W = (winProb W G : ℝ) :=
  rfl

/-- The performance side of CR18 Lemma 4.16, stated as one named hypothesis. -/
abbrev DifferenceLemmaBound (S T : WinningGame X Y) : Prop :=
  ∀ D : DistinguisherSolver X Y,
    advantage D (PFunPDS.ignoreMBO S) (PFunPDS.ignoreMBO T)
      ≤ (winProb (Dist.fTransform PFunDDS.ddToDDE D) S : ℝ)

/-- The cost side condition for the `ddToDDE` solver transformer. -/
abbrev DifferenceLemmaCostBound
    {LabelD LabelW : Type*}
    (gammaD : DistinguisherSolver X Y → Cost LabelD)
    (gammaW : WinnerSolver X Y → Cost LabelW)
    (costMap : Cost LabelD → Cost LabelW) : Prop :=
  ∀ D : DistinguisherSolver X Y,
    gammaW (Dist.fTransform PFunDDS.ddToDDE D) ≤ costMap (gammaD D)

/-- The single hypothesis needed to turn a proved Difference-Lemma hop into a
costed reduction. -/
abbrev DifferenceLemmaReductionHyp
    {LabelD LabelW : Type*}
    (S T : WinningGame X Y)
    (gammaD : DistinguisherSolver X Y → Cost LabelD)
    (gammaW : WinnerSolver X Y → Cost LabelW)
    (costMap : Cost LabelD → Cost LabelW) : Prop :=
  DifferenceLemmaBound S T ∧ DifferenceLemmaCostBound gammaD gammaW costMap

/-- The costed-reduction conclusion corresponding to CR18 Lemma 4.16. -/
abbrev DifferenceLemmaCostedReduction
    {LabelD LabelW : Type*}
    (S T : WinningGame X Y)
    (gammaD : DistinguisherSolver X Y → Cost LabelD)
    (gammaW : WinnerSolver X Y → Cost LabelW)
    (costMap : Cost LabelD → Cost LabelW) : Prop :=
  @IsCostedReduction
    (DistinguishingGame X Y) (DistinguisherSolver X Y) ℝ
    (WinningGame X Y) (WinnerSolver X Y) ℝ
    _ (distinguishingProblem X Y) _ (winningProblemReal X Y)
    LabelD LabelW
    (PFunPDS.ignoreMBO S, PFunPDS.ignoreMBO T) S
    (_root_.id : ℝ → ℝ)
    (Dist.fTransform PFunDDS.ddToDDE)
    gammaD gammaW costMap

section DifferenceLemmaReduction

variable {LabelD LabelW : Type*} {S T : WinningGame X Y}
variable {gammaD : DistinguisherSolver X Y → Cost LabelD}
variable {gammaW : WinnerSolver X Y → Cost LabelW}
variable {costMap : Cost LabelD → Cost LabelW}

theorem differenceLemma_isCostedReduction
    (h : DifferenceLemmaReductionHyp S T gammaD gammaW costMap) :
    DifferenceLemmaCostedReduction S T gammaD gammaW costMap := by
  cr18_reduction_bound_from h with [DifferenceLemmaCostedReduction, distinguishingProblem,
    pfunDistinguishingProblem, winningProblemReal]

end DifferenceLemmaReduction

end

end Complexity
end RandomSystems.CR18
