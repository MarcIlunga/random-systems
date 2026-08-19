/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Distinguishing
import RandomSystems.Complexity.Bounded

/-!
# PFun problem adapters

These adapters expose the existing PFun game and distinguishing surfaces as
CR18 `Problem`s.  The problem objects remain products/functions already present
in the PFun layer; the only new data is the `Problem` dictionary connecting
those objects to their solver and performance functions.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

noncomputable section

universe u v

/-- A PFun distinguishing problem is a pair of systems `(S, T)`. -/
abbrev PFunDistProblem (X : Type u) (Y : Type v) : Type (max u v) :=
  PFunPDS X Y × PFunPDS X Y

/-- The solver type for PFun distinguishing problems. -/
abbrev PFunDistSolver (X : Type u) (Y : Type v) : Type (max u v) :=
  Dist (PFunDDS.DDD X Y)

/-- A PFun winning problem is just a game system. -/
abbrev PFunGameProblem (X : Type u) (Y : Type v) : Type (max u v) :=
  PFunPDS X (Y × Bool)

/-- The solver type for PFun game-winning problems. -/
abbrev PFunGameSolver (X : Type u) (Y : Type v) : Type (max u v) :=
  Dist (PFunDDS.Winner X Y)

/-- Problem dictionary for PFun distinguishing, with performance equal to the
existing signed distinguishing advantage. -/
@[reducible] def pfunDistinguishingProblem (X : Type u) (Y : Type v) :
    Problem (PFunDistProblem X Y) (PFunDistSolver X Y) ℝ where
  perf := fun p D => advantage D p.1 p.2

/-- Problem dictionary for PFun game winning, with performance equal to the
existing winning probability. -/
@[reducible] def pfunWinningProblem (X : Type u) (Y : Type v) :
    Problem (PFunGameProblem X Y) (PFunGameSolver X Y) ℝ where
  perf := fun G W => winProb W G

@[simp] theorem pfunDistinguishingProblem_perf
    {X : Type u} {Y : Type v} (p : PFunDistProblem X Y) (D : PFunDistSolver X Y) :
    (pfunDistinguishingProblem X Y).perf p D = advantage D p.1 p.2 :=
  rfl

@[simp] theorem pfunWinningProblem_perf
    {X : Type u} {Y : Type v} (G : PFunGameProblem X Y) (W : PFunGameSolver X Y) :
    (pfunWinningProblem X Y).perf G W = winProb W G :=
  rfl

end

end RandomSystems.CR18
