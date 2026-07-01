/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.BoundedPerf
import NextGen.Complexity.GameBased

/-!
# Game-based costed reductions

These are game-facing abbreviations for the abstract costed-reduction interface.
They keep the concrete game objects and cost functions explicit, and install the
right CR18 `Problem` dictionaries locally.
-/

namespace RandomSystems.CR18
namespace Complexity

universe u v u' v' ℓ ℓ'

/-- Explicit predicate for a costed reduction between concrete winning games. -/
abbrev IsWinningGameReduction
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    {Label Label' : Type ℓ}
    (G : WinningGame X Y) (H : WinningGame X' Y')
    (tau : NNReal → NNReal)
    (rho : WinnerSolver X Y → WinnerSolver X' Y')
    (gammaG : WinnerSolver X Y → Cost Label)
    (gammaH : WinnerSolver X' Y' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  letI := winningProblem X Y
  letI := winningProblem X' Y'
  IsCostedReduction G H tau rho gammaG gammaH costMap

/-- Typeclass/law layer for verified reductions between concrete winning games. -/
abbrev VerifiedWinningGameReduction
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    {Label Label' : Type ℓ}
    (G : WinningGame X Y) (H : WinningGame X' Y')
    (tau : NNReal → NNReal)
    (rho : WinnerSolver X Y → WinnerSolver X' Y')
    (gammaG : WinnerSolver X Y → Cost Label)
    (gammaH : WinnerSolver X' Y' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  letI := winningProblem X Y
  letI := winningProblem X' Y'
  VerifiedCostedReduction G H tau rho gammaG gammaH costMap

/-- Explicit predicate for a costed reduction between concrete distinguishing games. -/
abbrev IsDistinguishingGameReduction
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    {Label Label' : Type ℓ'}
    (p : DistinguishingGame X Y) (q : DistinguishingGame X' Y')
    (tau : ℝ → ℝ)
    (rho : DistinguisherSolver X Y → DistinguisherSolver X' Y')
    (gammaP : DistinguisherSolver X Y → Cost Label)
    (gammaQ : DistinguisherSolver X' Y' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  letI := distinguishingProblem X Y
  letI := distinguishingProblem X' Y'
  IsCostedReduction p q tau rho gammaP gammaQ costMap

/-- Typeclass/law layer for verified reductions between concrete distinguishing games. -/
abbrev VerifiedDistinguishingGameReduction
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    {Label Label' : Type ℓ'}
    (p : DistinguishingGame X Y) (q : DistinguishingGame X' Y')
    (tau : ℝ → ℝ)
    (rho : DistinguisherSolver X Y → DistinguisherSolver X' Y')
    (gammaP : DistinguisherSolver X Y → Cost Label)
    (gammaQ : DistinguisherSolver X' Y' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  letI := distinguishingProblem X Y
  letI := distinguishingProblem X' Y'
  VerifiedCostedReduction p q tau rho gammaP gammaQ costMap

/-- Named hypothesis for the solver-class map induced by a verified winning
game reduction. -/
abbrev VerifiedWinningGameReductionClassMapHyp
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    {Label Label' : Type ℓ}
    (G : WinningGame X Y) (H : WinningGame X' Y')
    (tau : NNReal → NNReal)
    (rho : WinnerSolver X Y → WinnerSolver X' Y')
    (gammaG : WinnerSolver X Y → Cost Label)
    (gammaH : WinnerSolver X' Y' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  VerifiedWinningGameReduction G H tau rho gammaG gammaH costMap ∧ Monotone costMap

/-- Named goal for the solver-class map induced by a verified winning game
reduction. -/
abbrev VerifiedWinningGameReductionClassMapGoal
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    {Label Label' : Type ℓ}
    (rho : WinnerSolver X Y → WinnerSolver X' Y')
    (gammaG : WinnerSolver X Y → Cost Label)
    (gammaH : WinnerSolver X' Y' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  MapsSolverClasses rho gammaG gammaH costMap

/-- Named hypothesis for the solver-class map induced by a verified
distinguishing-game reduction. -/
abbrev VerifiedDistinguishingGameReductionClassMapHyp
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    {Label Label' : Type ℓ'}
    (p : DistinguishingGame X Y) (q : DistinguishingGame X' Y')
    (tau : ℝ → ℝ)
    (rho : DistinguisherSolver X Y → DistinguisherSolver X' Y')
    (gammaP : DistinguisherSolver X Y → Cost Label)
    (gammaQ : DistinguisherSolver X' Y' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  VerifiedDistinguishingGameReduction p q tau rho gammaP gammaQ costMap ∧ Monotone costMap

/-- Named goal for the solver-class map induced by a verified distinguishing
game reduction. -/
abbrev VerifiedDistinguishingGameReductionClassMapGoal
    {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
    {Label Label' : Type ℓ'}
    (rho : DistinguisherSolver X Y → DistinguisherSolver X' Y')
    (gammaP : DistinguisherSolver X Y → Cost Label)
    (gammaQ : DistinguisherSolver X' Y' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  MapsSolverClasses rho gammaP gammaQ costMap

section Winning

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  {Label Label' : Type ℓ}
  {G : WinningGame X Y} {H : WinningGame X' Y'}
  {tau : NNReal → NNReal}
  {rho : WinnerSolver X Y → WinnerSolver X' Y'}
  {gammaG : WinnerSolver X Y → Cost Label}
  {gammaH : WinnerSolver X' Y' → Cost Label'}
  {costMap : Cost Label → Cost Label'}

/-- A verified winning-game reduction maps every bounded winner class across
its cost map. -/
theorem VerifiedWinningGameReductionClassMapHyp.mapsSolverClasses
    (h : VerifiedWinningGameReductionClassMapHyp G H tau rho gammaG gammaH costMap) :
    VerifiedWinningGameReductionClassMapGoal rho gammaG gammaH costMap := by
  rcases h with ⟨hred, hcostMap⟩
  intro c W hW
  exact le_trans (hred.cost_le W) (hcostMap hW)

end Winning

section Distinguishing

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  {Label Label' : Type ℓ'}
  {p : DistinguishingGame X Y} {q : DistinguishingGame X' Y'}
  {tau : ℝ → ℝ}
  {rho : DistinguisherSolver X Y → DistinguisherSolver X' Y'}
  {gammaP : DistinguisherSolver X Y → Cost Label}
  {gammaQ : DistinguisherSolver X' Y' → Cost Label'}
  {costMap : Cost Label → Cost Label'}

/-- A verified distinguishing-game reduction maps every bounded distinguisher
class across its cost map. -/
theorem VerifiedDistinguishingGameReductionClassMapHyp.mapsSolverClasses
    (h : VerifiedDistinguishingGameReductionClassMapHyp p q tau rho gammaP gammaQ costMap) :
    VerifiedDistinguishingGameReductionClassMapGoal rho gammaP gammaQ costMap := by
  rcases h with ⟨hred, hcostMap⟩
  intro c D hD
  exact le_trans (hred.cost_le D) (hcostMap hD)

end Distinguishing

end Complexity
end RandomSystems.CR18
