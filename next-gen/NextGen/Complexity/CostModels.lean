/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.Cost

/-!
# Cost-model constructors

A cost model is an explicit function from solvers to costs.  There is no
canonical cost model for a solver type, so this file provides constructors rather
than typeclass instances.
-/

namespace RandomSystems.CR18
namespace Complexity

/-- A cost model for a solver type. -/
abbrev CostModel (Solver Label : Type*) : Type _ :=
  Solver → Cost Label

namespace CostModel

variable {Solver Label : Type*}

/-- The zero-cost model. -/
def zero (Solver Label : Type*) : CostModel Solver Label :=
  fun _ => 0

@[simp] theorem zero_apply (s : Solver) :
    zero Solver Label s = (0 : Cost Label) := rfl

/-- A constant-cost model. -/
def const (c : Cost Label) : CostModel Solver Label :=
  fun _ => c

@[simp] theorem const_apply (c : Cost Label) (s : Solver) :
    const c s = c := rfl

/-- A cost model with intrinsic work and no labelled calls. -/
def intrinsic (work : Solver → Nat) : CostModel Solver Empty :=
  fun s => Cost.of (work s) Empty.elim

@[simp] theorem intrinsic_apply (work : Solver → Nat) (s : Solver) :
    Cost.intrinsic (intrinsic work s) = work s := rfl

/-- A labelled cost model from intrinsic work and per-label call counts. -/
def labelled (work : Solver → Nat) (calls : Solver → Label → Nat) : CostModel Solver Label :=
  fun s => Cost.of (work s) (calls s)

@[simp] theorem labelled_intrinsic (work : Solver → Nat) (calls : Solver → Label → Nat)
    (s : Solver) :
    Cost.intrinsic (labelled work calls s) = work s := rfl

@[simp] theorem labelled_calls (work : Solver → Nat) (calls : Solver → Label → Nat)
    (s : Solver) (l : Label) :
    Cost.calls (labelled work calls s) l = calls s l := rfl

end CostModel

end Complexity
end RandomSystems.CR18
