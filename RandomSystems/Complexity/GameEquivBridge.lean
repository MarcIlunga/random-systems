/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.GameEquivalence
import RandomSystems.Complexity.GameBased
import RandomSystems.Complexity.GameHop

/-!
# Bridges from CR18 game equivalence to complexity hops

This file connects existing local CR18 game facts to the generic complexity
hop predicates.  It does not introduce a new game semantics: a bridge theorem
only repackages an equality or inequality of the already-defined performance
functions (`winProb` or `advantage`) as `PerfEq` or `PerfLe`.
-/

namespace RandomSystems.CR18
namespace Complexity

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-- Exact equality of winning-game performance functions. -/
abbrev WinningPerfEq (G H : WinningGame X Y) : Prop :=
  @PerfEq (WinningGame X Y) (WinnerSolver X Y) NNReal _
    (winningProblem X Y) G H

/-- Pointwise monotonicity of winning-game performance functions. -/
abbrev WinningPerfLe (G H : WinningGame X Y) : Prop :=
  @PerfLe (WinningGame X Y) (WinnerSolver X Y) NNReal _
    (winningProblem X Y) G H

/-- Exact equality of distinguishing-game performance functions. -/
abbrev DistinguishingPerfEq (p q : DistinguishingGame X Y) : Prop :=
  @PerfEq (DistinguishingGame X Y) (DistinguisherSolver X Y) ℝ _
    (distinguishingProblem X Y) p q

/-- Pointwise monotonicity of distinguishing-game performance functions. -/
abbrev DistinguishingPerfLe (p q : DistinguishingGame X Y) : Prop :=
  @PerfLe (DistinguishingGame X Y) (DistinguisherSolver X Y) ℝ _
    (distinguishingProblem X Y) p q

/-- Pointwise equality of winning probabilities.  This is the hypothesis a
concrete unobservable winning-game hop should prove. -/
abbrev WinningWinProbEq (G H : WinningGame X Y) : Prop :=
  ∀ W : WinnerSolver X Y, winProb W G = winProb W H

/-- Pointwise monotonicity of winning probabilities. -/
abbrev WinningWinProbLe (G H : WinningGame X Y) : Prop :=
  ∀ W : WinnerSolver X Y, winProb W G ≤ winProb W H

/-- Pointwise equality of distinguishing advantages. -/
abbrev DistinguishingAdvantageEq (p q : DistinguishingGame X Y) : Prop :=
  ∀ D : DistinguisherSolver X Y, advantage D p.1 p.2 = advantage D q.1 q.2

/-- Pointwise monotonicity of distinguishing advantages. -/
abbrev DistinguishingAdvantageLe (p q : DistinguishingGame X Y) : Prop :=
  ∀ D : DistinguisherSolver X Y, advantage D p.1 p.2 ≤ advantage D q.1 q.2

/-- Family-level law saying that winning probability is observable through CR18
pre-winning behavior.

This is a named hypothesis statement, not a semantic object.  A concrete
development can prove it once for a game family and then use
`ObservableGameEquiv` as the hop hypothesis. -/
abbrev WinProbPreWinningInvariant (X : Type u) (Y : Type v) : Prop :=
  ∀ W : WinnerSolver X Y, FactorsThroughPreWinning (fun G' => winProb W G')

/-- The single named hypothesis for turning CR18 `GameEquiv` into an
unobservable winning-game hop. -/
abbrev ObservableGameEquiv (G H : WinningGame X Y) : Prop :=
  WinProbPreWinningInvariant X Y ∧ GameEquiv G H

/-- Exact-cost identity reduction between two winning games. -/
abbrev WinningIdentityCostedReduction {Label : Type*}
    (G H : WinningGame X Y) (gamma : WinnerSolver X Y → Cost Label) : Prop :=
  @IsCostedReduction
    (WinningGame X Y) (WinnerSolver X Y) NNReal
    (WinningGame X Y) (WinnerSolver X Y) NNReal
    _ (winningProblem X Y) _ (winningProblem X Y)
    Label Label
    G H (_root_.id : NNReal → NNReal)
    (_root_.id : WinnerSolver X Y → WinnerSolver X Y)
    gamma gamma (CostMap.id : Cost Label → Cost Label)

theorem winningPerfEq_of_winProbEq
    {G H : WinningGame X Y}
    (h : WinningWinProbEq G H) :
    WinningPerfEq G H := by
  funext W
  simpa [WinningPerfEq, winningProblem, pfunWinningProblem] using h W

theorem winningPerfLe_of_winProbLe
    {G H : WinningGame X Y}
    (h : WinningWinProbLe G H) :
    WinningPerfLe G H := by
  intro W
  simpa [WinningPerfLe, winningProblem, pfunWinningProblem] using h W

theorem distinguishingPerfEq_of_advantageEq
    {p q : DistinguishingGame X Y}
    (h : DistinguishingAdvantageEq p q) :
    DistinguishingPerfEq p q := by
  funext D
  simpa [DistinguishingPerfEq, distinguishingProblem, pfunDistinguishingProblem] using h D

theorem distinguishingPerfLe_of_advantageLe
    {p q : DistinguishingGame X Y}
    (h : DistinguishingAdvantageLe p q) :
    DistinguishingPerfLe p q := by
  intro D
  simpa [DistinguishingPerfLe, distinguishingProblem, pfunDistinguishingProblem] using h D

/-- CR18 `GameEquiv`, plus the family-level observability invariant, is an
unobservable winning-game hop. -/
theorem gameEquiv_winningPerfEq
    {G H : WinningGame X Y}
    (h : ObservableGameEquiv G H) :
    WinningPerfEq G H := by
  apply winningPerfEq_of_winProbEq
  intro W
  exact gameEquiv_winFun_eq (h.1 W) h.2

/-- An observable `GameEquiv` hop is an exact-cost identity reduction in the
complexity layer. -/
theorem gameEquiv_winningCostedReduction
    {Label : Type*} {G H : WinningGame X Y}
    (h : ObservableGameEquiv G H)
    (gamma : WinnerSolver X Y → Cost Label) :
    WinningIdentityCostedReduction G H gamma := by
  exact @PerfEq.isCostedReduction
    (WinningGame X Y) (WinnerSolver X Y) NNReal
    _ (winningProblem X Y) G H Label
    (gameEquiv_winningPerfEq h) gamma

end

end Complexity
end RandomSystems.CR18
