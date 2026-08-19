/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.GameHop

/-!
# Game sequences

This file provides a small amount of sequence tooling for game-hopping proofs.
A sequence is just a function `Nat → P`; `StepsTo R games n` says that every
adjacent hop from game `0` through game `n` satisfies relation `R`.

The heterogeneous part of a game-based proof is still represented by explicit
`IsCostedReduction` hops and composed with `IsCostedReduction.comp`.  This file
handles the common homogeneous case where exact/unobservable changes happen
inside one problem family.
-/

namespace RandomSystems.CR18
namespace Complexity

variable {P : Type*}

/-- A game trace is a plain Nat-indexed function. -/
abbrev GameTrace (P : Type*) :=
  Nat → P

/-- `StepsTo R games n` means every adjacent step up to index `n` satisfies
relation `R`. -/
def StepsTo (R : P → P → Prop) (games : GameTrace P) : Nat → Prop
  | 0 => True
  | n + 1 => StepsTo R games n ∧ R (games n) (games (n + 1))

namespace StepsTo

variable {R R' : P → P → Prop} {games : GameTrace P} {n : Nat}

theorem zero : StepsTo R games 0 :=
  trivial

theorem succ (hprev : StepsTo R games n) (hstep : R (games n) (games (n + 1))) :
    StepsTo R games (n + 1) :=
  ⟨hprev, hstep⟩

theorem prev (h : StepsTo R games (n + 1)) :
    StepsTo R games n :=
  h.1

theorem step (h : StepsTo R games (n + 1)) :
    R (games n) (games (n + 1)) :=
  h.2

/-- A pointwise implication between hop relations lifts to complete prefixes. -/
theorem monoRel (himp : ∀ {a b}, R a b → R' a b)
    (h : StepsTo R games n) :
    StepsTo R' games n := by
  induction n with
  | zero =>
      exact trivial
  | succ n ih =>
      exact ⟨ih h.1, himp h.2⟩

/-- If a relation is reflexive and transitive, a prefix of adjacent steps gives
the endpoint relation. -/
theorem endpoint (hrefl : ∀ p, R p p)
    (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (h : StepsTo R games n) :
    R (games 0) (games n) := by
  induction n with
  | zero =>
      exact hrefl (games 0)
  | succ n ih =>
      exact htrans (ih h.1) h.2

end StepsTo

variable {Solver Perf : Type*} [PartialOrder Perf] [Problem P Solver Perf]

/-- Adjacent performance-monotone hops along a homogeneous game trace. -/
abbrev PerfLeStepsTo (games : GameTrace P) (n : Nat) : Prop :=
  StepsTo (fun p q => @PerfLe P Solver Perf _ _ p q) games n

/-- Adjacent exact-performance hops along a homogeneous game trace. -/
abbrev PerfEqStepsTo (games : GameTrace P) (n : Nat) : Prop :=
  StepsTo (fun p q => @PerfEq P Solver Perf _ _ p q) games n

/-- Adjacent unobservable hops along a homogeneous game trace. -/
abbrev UnobservableStepsTo (games : GameTrace P) (n : Nat) : Prop :=
  StepsTo (fun p q => @Unobservable P Solver Perf _ _ p q) games n

namespace PerfLeStepsTo

variable {games : GameTrace P} {n : Nat}

theorem endpoint
    (h : @RandomSystems.CR18.Complexity.PerfLeStepsTo P Solver Perf _ _ games n) :
    @PerfLe P Solver Perf _ _ (games 0) (games n) :=
  StepsTo.endpoint
    (R := fun p q => @PerfLe P Solver Perf _ _ p q)
    (fun _ => le_rfl)
    (fun hpq hqr => le_trans hpq hqr)
    h

/-- Collapse a homogeneous performance-monotone prefix into one exact-cost
endpoint reduction. -/
theorem endpoint_isCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.PerfLeStepsTo P Solver Perf _ _ games n)
    (gamma : Solver → Cost Label) :
    IsCostedReduction (games 0) (games n) (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) :=
  PerfLe.isCostedReduction (PerfLeStepsTo.endpoint h) gamma

/-- The final adjacent step of a performance-monotone prefix is itself an
exact-cost reduction. -/
theorem step_isCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.PerfLeStepsTo P Solver Perf _ _ games (n + 1))
    (gamma : Solver → Cost Label) :
    IsCostedReduction (games n) (games (n + 1)) (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) :=
  PerfLe.isCostedReduction (StepsTo.step h) gamma

end PerfLeStepsTo

namespace PerfEqStepsTo

variable {games : GameTrace P} {n : Nat}

theorem perfLeStepsTo
    (h : @RandomSystems.CR18.Complexity.PerfEqStepsTo P Solver Perf _ _ games n) :
    @RandomSystems.CR18.Complexity.PerfLeStepsTo P Solver Perf _ _ games n :=
  StepsTo.monoRel
    (R := fun p q => @PerfEq P Solver Perf _ _ p q)
    (R' := fun p q => @PerfLe P Solver Perf _ _ p q)
    (fun hstep => PerfEq.perfLe hstep)
    h

theorem endpoint
    (h : @RandomSystems.CR18.Complexity.PerfEqStepsTo P Solver Perf _ _ games n) :
    @PerfEq P Solver Perf _ _ (games 0) (games n) :=
  StepsTo.endpoint
    (R := fun p q => @PerfEq P Solver Perf _ _ p q)
    (fun _ => rfl)
    (fun hpq hqr => Eq.trans hpq hqr)
    h

theorem endpoint_isCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.PerfEqStepsTo P Solver Perf _ _ games n)
    (gamma : Solver → Cost Label) :
    IsCostedReduction (games 0) (games n) (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) :=
  PerfEq.isCostedReduction (PerfEqStepsTo.endpoint h) gamma

end PerfEqStepsTo

namespace UnobservableStepsTo

variable {games : GameTrace P} {n : Nat}

theorem perfEqStepsTo
    (h : @RandomSystems.CR18.Complexity.UnobservableStepsTo P Solver Perf _ _ games n) :
    @RandomSystems.CR18.Complexity.PerfEqStepsTo P Solver Perf _ _ games n :=
  by
    simpa [UnobservableStepsTo, PerfEqStepsTo, Unobservable] using h

theorem endpoint
    (h : @RandomSystems.CR18.Complexity.UnobservableStepsTo P Solver Perf _ _ games n) :
    @Unobservable P Solver Perf _ _ (games 0) (games n) :=
  PerfEqStepsTo.endpoint (UnobservableStepsTo.perfEqStepsTo h)

theorem endpoint_isCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.UnobservableStepsTo P Solver Perf _ _ games n)
    (gamma : Solver → Cost Label) :
    IsCostedReduction (games 0) (games n) (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) :=
  PerfEq.isCostedReduction (UnobservableStepsTo.endpoint h) gamma

end UnobservableStepsTo

end Complexity
end RandomSystems.CR18
