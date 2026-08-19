/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.BoundedPerf

/-!
# Asymptotic security wrappers

This file adds a thin security-parameter layer over the concrete, cost-indexed
`costBoundedPerf` API.  The objects remain families of existing problems,
budgets, and bounds; security is a named proposition over those inputs.
-/

namespace RandomSystems.CR18
namespace Complexity

noncomputable section

/-- Security parameters are natural numbers. -/
abbrev SecurityParameter :=
  Nat

/-- Eventual pointwise domination of two parameter-indexed families. -/
def EventuallyLe {A : Type*} [LE A] (f g : SecurityParameter → A) : Prop :=
  ∃ N, ∀ n, N ≤ n → f n ≤ g n

/-- A natural-valued family is polynomially bounded by one monomial.  This is
intentionally a simple envelope predicate; richer polynomial libraries can
bridge into this statement later. -/
def PolyBoundedNat (f : SecurityParameter → Nat) : Prop :=
  ∃ degree coeff : Nat, ∀ n, f n ≤ coeff * (n + 1) ^ degree

/-- A real-valued family is negligible if it is eventually below every inverse
monomial. -/
def Negligible (eps : SecurityParameter → ℝ) : Prop :=
  ∀ degree : Nat,
    EventuallyLe (fun n => |eps n|)
      (fun n => (1 : ℝ) / ((n + 1 : Nat) : ℝ) ^ degree)

/-- A cost family is coordinatewise bounded by a scalar natural-valued family. -/
def CostFamilyBoundedBy {Label : Type*}
    (budget : SecurityParameter → Cost Label) (bound : SecurityParameter → Nat) : Prop :=
  ∀ n coord, budget n coord ≤ bound n

/-- A cost family is polynomially bounded when all coordinates share one
polynomial natural envelope. -/
def PolyBoundedCost {Label : Type*} (budget : SecurityParameter → Cost Label) : Prop :=
  ∃ bound : SecurityParameter → Nat,
    PolyBoundedNat bound ∧ CostFamilyBoundedBy budget bound

/-- Security at one parameter, stated through the existing bounded-performance
operation. -/
abbrev SecureAt {ProblemObject Solver Perf Label : Type*}
    [PartialOrder Perf] [SupSet Perf] [Problem ProblemObject Solver Perf]
    (gamma : Solver → Cost Label)
    (problem : SecurityParameter → ProblemObject)
    (budget : SecurityParameter → Cost Label)
    (bound : SecurityParameter → Perf)
    (n : SecurityParameter) : Prop :=
  costBoundedPerf gamma (problem n) (budget n) ≤ bound n

/-- Uniform parameter-indexed security against a displayed cost budget. -/
abbrev SecureFamily {ProblemObject Solver Perf Label : Type*}
    [PartialOrder Perf] [SupSet Perf] [Problem ProblemObject Solver Perf]
    (gamma : Solver → Cost Label)
    (problem : SecurityParameter → ProblemObject)
    (budget : SecurityParameter → Cost Label)
    (bound : SecurityParameter → Perf) : Prop :=
  ∀ n, SecureAt gamma problem budget bound n

/-- Eventual parameter-indexed security against a displayed cost budget. -/
abbrev EventuallySecureFamily {ProblemObject Solver Perf Label : Type*}
    [PartialOrder Perf] [SupSet Perf] [Problem ProblemObject Solver Perf]
    (gamma : Solver → Cost Label)
    (problem : SecurityParameter → ProblemObject)
    (budget : SecurityParameter → Cost Label)
    (bound : SecurityParameter → Perf) : Prop :=
  EventuallyLe (fun n => costBoundedPerf gamma (problem n) (budget n)) bound

/-- Real-valued security with a negligible bound. -/
def NegligiblySecureFamily {ProblemObject Solver Label : Type*}
    [SupSet ℝ] [Problem ProblemObject Solver ℝ]
    (gamma : Solver → Cost Label)
    (problem : SecurityParameter → ProblemObject)
    (budget : SecurityParameter → Cost Label)
    (eps : SecurityParameter → ℝ) : Prop :=
  Negligible eps ∧ SecureFamily gamma problem budget eps

/-- Real-valued asymptotic security against polynomially bounded costs. -/
def PolyTimeNegligiblySecureFamily {ProblemObject Solver Label : Type*}
    [SupSet ℝ] [Problem ProblemObject Solver ℝ]
    (gamma : Solver → Cost Label)
    (problem : SecurityParameter → ProblemObject)
    (budget : SecurityParameter → Cost Label)
    (eps : SecurityParameter → ℝ) : Prop :=
  PolyBoundedCost budget ∧ NegligiblySecureFamily gamma problem budget eps

namespace EventuallyLe

variable {A : Type*} [Preorder A] {f g : SecurityParameter → A}

theorem of_forall (h : ∀ n, f n ≤ g n) :
    EventuallyLe f g :=
  ⟨0, fun n _ => h n⟩

theorem refl (f : SecurityParameter → A) :
    EventuallyLe f f :=
  of_forall fun _ => le_rfl

end EventuallyLe

namespace SecureFamily

variable {ProblemObject Solver Perf Label : Type*}
  [PartialOrder Perf] [SupSet Perf] [Problem ProblemObject Solver Perf]
  {gamma : Solver → Cost Label}
  {problem : SecurityParameter → ProblemObject}
  {budget : SecurityParameter → Cost Label}
  {bound : SecurityParameter → Perf}

/-- A uniform family security statement is also an eventual one. -/
theorem eventually (h : SecureFamily gamma problem budget bound) :
    EventuallySecureFamily gamma problem budget bound :=
  EventuallyLe.of_forall h

end SecureFamily

namespace NegligiblySecureFamily

variable {ProblemObject Solver Label : Type*}
  [SupSet ℝ] [Problem ProblemObject Solver ℝ]
  {gamma : Solver → Cost Label}
  {problem : SecurityParameter → ProblemObject}
  {budget : SecurityParameter → Cost Label}
  {eps : SecurityParameter → ℝ}

theorem negligible (h : NegligiblySecureFamily gamma problem budget eps) :
    Negligible eps :=
  h.1

theorem secureFamily (h : NegligiblySecureFamily gamma problem budget eps) :
    SecureFamily gamma problem budget eps :=
  h.2

theorem eventuallySecureFamily (h : NegligiblySecureFamily gamma problem budget eps) :
    EventuallySecureFamily gamma problem budget eps :=
  SecureFamily.eventually h.secureFamily

end NegligiblySecureFamily

namespace PolyTimeNegligiblySecureFamily

variable {ProblemObject Solver Label : Type*}
  [SupSet ℝ] [Problem ProblemObject Solver ℝ]
  {gamma : Solver → Cost Label}
  {problem : SecurityParameter → ProblemObject}
  {budget : SecurityParameter → Cost Label}
  {eps : SecurityParameter → ℝ}

theorem polyBoundedCost (h : PolyTimeNegligiblySecureFamily gamma problem budget eps) :
    PolyBoundedCost budget :=
  h.1

theorem negligiblySecureFamily (h : PolyTimeNegligiblySecureFamily gamma problem budget eps) :
    NegligiblySecureFamily gamma problem budget eps :=
  h.2

theorem eventuallySecureFamily (h : PolyTimeNegligiblySecureFamily gamma problem budget eps) :
    EventuallySecureFamily gamma problem budget eps :=
  h.negligiblySecureFamily.eventuallySecureFamily

end PolyTimeNegligiblySecureFamily

end

end Complexity
end RandomSystems.CR18
