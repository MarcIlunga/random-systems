/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.CostMap
import RandomSystems.Complexity.Reduction

/-!
# Game-hop predicates

This file contains the small generic predicates used to talk about game hops at
the CR18 `Problem` level.  The predicates intentionally do not know what a game
is.  A concrete game-equivalence theorem should prove one of these predicates;
the complexity layer then turns that fact into a costed reduction fact.
-/

namespace RandomSystems.CR18
namespace Complexity

/-- Documentation tag for the main kinds of hops used in a game-based proof.

The tag carries no proof content.  The proof content remains in predicates such
as `PerfLe`, `PerfEq`, and `IsCostedReduction`. -/
inductive HopKind : Type
  | exact
  | unobservable
  | reduction
  | converter
  | badEvent
  | custom
  deriving DecidableEq, Repr

variable {P Solver Perf : Type*} [PartialOrder Perf] [Problem P Solver Perf]

/-- A zero-translation performance hop: every solver performs no better on `p`
than on `q`. -/
abbrev PerfLe (p q : P) : Prop :=
  (@Problem.perf P Solver Perf _ _ p) ≤ (@Problem.perf P Solver Perf _ _ q)

/-- Exact equality of the two performance functions.  This is the generic
form of an unobservable game change. -/
abbrev PerfEq (p q : P) : Prop :=
  (@Problem.perf P Solver Perf _ _ p) = (@Problem.perf P Solver Perf _ _ q)

/-- An unobservable hop is just exact equality of the observable performance
function.  Concrete game-equivalence lemmas should usually discharge this. -/
abbrev Unobservable (p q : P) : Prop :=
  @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p q

/-- Alias for a cross-problem costed reduction hop. -/
abbrev ReductionHop {P Sp Ωp Q Sq Ωq LabelP LabelQ : Type*}
    [PartialOrder Ωp] [Problem P Sp Ωp]
    [PartialOrder Ωq] [Problem Q Sq Ωq]
    (p : P) (q : Q)
    (tau : Ωp → Ωq) (rho : Sp → Sq)
    (gammaP : Sp → Cost LabelP) (gammaQ : Sq → Cost LabelQ)
    (costMap : Cost LabelP → Cost LabelQ) : Prop :=
  IsCostedReduction p q tau rho gammaP gammaQ costMap

/-- A converter hop is a reduction whose target problem is produced by applying
a plain transformation to the source problem. -/
abbrev ConverterHop {P Sp Ωp Q Sq Ωq LabelP LabelQ : Type*}
    [PartialOrder Ωp] [Problem P Sp Ωp]
    [PartialOrder Ωq] [Problem Q Sq Ωq]
    (convert : P → Q) (p : P)
    (tau : Ωp → Ωq) (rho : Sp → Sq)
    (gammaP : Sp → Cost LabelP) (gammaQ : Sq → Cost LabelQ)
    (costMap : Cost LabelP → Cost LabelQ) : Prop :=
  IsCostedReduction p (convert p) tau rho gammaP gammaQ costMap

namespace PerfLe

variable {p q r : P}

theorem refl (p : P) :
    @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ p p :=
  le_rfl

theorem trans
    (hpq : @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ p q)
    (hqr : @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ q r) :
    @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ p r :=
  le_trans hpq hqr

theorem of_eq
    (h : @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p q) :
    @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ p q := by
  intro s
  rw [h]

/-- A performance-monotone exact-cost hop is a costed reduction with identity
solver map, identity performance translation, and identity cost map. -/
theorem isCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ p q)
    (gamma : Solver → Cost Label) :
    IsCostedReduction p q (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) := by
  constructor
  · intro s
    exact h s
  · intro s
    exact le_rfl

/-- Typeclass/law form of `PerfLe.isCostedReduction`. -/
theorem verifiedCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ p q)
    (gamma : Solver → Cost Label) :
    VerifiedCostedReduction p q (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) where
  perf_le := fun s => h s
  cost_le := fun _ => le_rfl

end PerfLe

namespace PerfEq

variable {p q r : P}

theorem refl (p : P) :
    @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p p :=
  rfl

theorem symm
    (h : @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p q) :
    @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ q p :=
  Eq.symm h

theorem trans
    (hpq : @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p q)
    (hqr : @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ q r) :
    @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p r :=
  Eq.trans hpq hqr

theorem perfLe
    (h : @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p q) :
    @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ p q :=
  PerfLe.of_eq h

/-- Exact/unobservable hops are costed reductions with no performance or cost
loss. -/
theorem isCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p q)
    (gamma : Solver → Cost Label) :
    IsCostedReduction p q (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) :=
  PerfLe.isCostedReduction h.perfLe gamma

/-- Typeclass/law form of `PerfEq.isCostedReduction`. -/
theorem verifiedCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p q)
    (gamma : Solver → Cost Label) :
    VerifiedCostedReduction p q (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) :=
  PerfLe.verifiedCostedReduction h.perfLe gamma

end PerfEq

namespace Unobservable

variable {p q : P}

theorem perfEq
    (h : @RandomSystems.CR18.Complexity.Unobservable P Solver Perf _ _ p q) :
    @RandomSystems.CR18.Complexity.PerfEq P Solver Perf _ _ p q :=
  h

theorem perfLe
    (h : @RandomSystems.CR18.Complexity.Unobservable P Solver Perf _ _ p q) :
    @RandomSystems.CR18.Complexity.PerfLe P Solver Perf _ _ p q :=
  PerfEq.perfLe h

theorem isCostedReduction {Label : Type*}
    (h : @RandomSystems.CR18.Complexity.Unobservable P Solver Perf _ _ p q)
    (gamma : Solver → Cost Label) :
    IsCostedReduction p q (_root_.id : Perf → Perf)
      (_root_.id : Solver → Solver) gamma gamma
      (CostMap.id : Cost Label → Cost Label) :=
  PerfEq.isCostedReduction h gamma

end Unobservable

end Complexity
end RandomSystems.CR18
