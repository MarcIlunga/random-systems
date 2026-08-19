/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18.AbstractProblem
import RandomSystems.Complexity.Cost

/-!
# Bounded solver classes

This file is the subtype layer for complexity support.  A cost function
`gamma : Solver -> Cost Label` refines the existing solver type; it does not
change the CR18 game/problem semantics.
-/

namespace RandomSystems.CR18
namespace Complexity

variable {Solver Label : Type*}

/-- The solver class at cost budget `c`: `Σ_c = {s | gamma s <= c}`.

This is an alias for CR18 §4.4.7's existing `complexityClass`. -/
abbrev SolverClass (gamma : Solver → Cost Label) (c : Cost Label) : Set Solver :=
  complexityClass gamma c

/-- A bounded solver is a raw solver bundled with membership in `SolverClass`.

This is Lean's subtype layer for resource-bounded adversaries. -/
abbrev BoundedSolver (gamma : Solver → Cost Label) (c : Cost Label) : Type _ :=
  {s : Solver // s ∈ SolverClass gamma c}

variable {Solver' Label' : Type*}

/-- A solver transformer preserves every budgeted solver class, after applying
the displayed cost map to the budget. -/
abbrev MapsSolverClasses (rho : Solver → Solver')
    (gamma : Solver → Cost Label) (gamma' : Solver' → Cost Label')
    (costMap : Cost Label → Cost Label') : Prop :=
  ∀ c, Set.MapsTo rho (SolverClass gamma c) (SolverClass gamma' (costMap c))

@[simp] theorem mem_solverClass (gamma : Solver → Cost Label) (c : Cost Label) (s : Solver) :
    s ∈ SolverClass gamma c ↔ gamma s ≤ c := Iff.rfl

@[simp] theorem boundedSolver_property (gamma : Solver → Cost Label) (c : Cost Label)
    (s : BoundedSolver gamma c) :
    gamma s.1 ≤ c :=
  s.2

/-- Coerce a bounded solver back to its raw solver. -/
def BoundedSolver.val {gamma : Solver → Cost Label} {c : Cost Label}
    (s : BoundedSolver gamma c) : Solver :=
  s.1

@[simp] theorem boundedSolver_val_mk (gamma : Solver → Cost Label) (c : Cost Label)
    (s : Solver) (h : gamma s ≤ c) :
    (BoundedSolver.val (⟨s, h⟩ : BoundedSolver gamma c)) = s := rfl

/-- Derived performance at a cost budget, reusing CR18 §4.4.7's `derivedPerf`. -/
abbrev costBoundedPerf {ProblemObject Perf : Type*} [PartialOrder Perf] [SupSet Perf]
    [Problem ProblemObject Solver Perf] (gamma : Solver → Cost Label)
    (p : ProblemObject) (c : Cost Label) : Perf :=
  derivedPerf gamma p c

end Complexity
end RandomSystems.CR18
