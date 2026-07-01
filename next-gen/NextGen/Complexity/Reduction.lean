/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.Bounded

/-!
# Costed reductions

The abstract CR18 reduction is still the performance inequality
`tau o pbar <= qbar o rho`.  Complexity support adds a second inequality saying
that the same solver transformation `rho` maps the source cost to a target cost
bounded by `costMap`.

This file keeps the concrete data explicit.  `IsCostedReduction` is the direct
predicate over the functions involved, while `VerifiedCostedReduction` is the
thin typeclass/law layer for theorems that should read "any verified reduction
has property C".  The class packages the verification laws, not a canonical cost
model.
-/

namespace RandomSystems.CR18
namespace Complexity

variable {P Sp Ωp Q Sq Ωq : Type*}
  [PartialOrder Ωp] [Problem P Sp Ωp]
  [PartialOrder Ωq] [Problem Q Sq Ωq]
  {LabelP LabelQ : Type*}

/-- A CR18 reduction with an explicit cost side condition.

The first conjunct is the usual performance reduction.  The second conjunct
says that applying `rho` to a solver with source cost `gammaP s` produces a
target solver whose cost is bounded by `costMap (gammaP s)`. -/
def IsCostedReduction (p : P) (q : Q)
    (tau : Ωp → Ωq) (rho : Sp → Sq)
    (gammaP : Sp → Cost LabelP) (gammaQ : Sq → Cost LabelQ)
    (costMap : Cost LabelP → Cost LabelQ) : Prop :=
  (tau ∘ Problem.perf p ≤ Problem.perf q ∘ rho) ∧
    ∀ s, gammaQ (rho s) ≤ costMap (gammaP s)

/-- Typeclass form of `IsCostedReduction`.

Use this when the theorem is about *any verified reduction satisfying these
laws*.  The cost functions and reduction functions remain explicit parameters;
the class only records that the displayed functions have been verified. -/
class VerifiedCostedReduction (p : P) (q : Q)
    (tau : Ωp → Ωq) (rho : Sp → Sq)
    (gammaP : Sp → Cost LabelP) (gammaQ : Sq → Cost LabelQ)
    (costMap : Cost LabelP → Cost LabelQ) : Prop where
  /-- The usual CR18 performance-reduction inequality. -/
  perf_le : tau ∘ Problem.perf p ≤ Problem.perf q ∘ rho
  /-- The cost blow-up bound for the same solver transformation. -/
  cost_le : ∀ s, gammaQ (rho s) ≤ costMap (gammaP s)

/-- Named hypothesis for the solver-class map induced by an explicit costed
reduction. -/
abbrev CostedReductionClassMapHyp (p : P) (q : Q)
    (tau : Ωp → Ωq) (rho : Sp → Sq)
    (gammaP : Sp → Cost LabelP) (gammaQ : Sq → Cost LabelQ)
    (costMap : Cost LabelP → Cost LabelQ) : Prop :=
  IsCostedReduction p q tau rho gammaP gammaQ costMap ∧ Monotone costMap

/-- Named goal for the solver-class map induced by an explicit costed
reduction. -/
abbrev CostedReductionClassMapGoal
    (rho : Sp → Sq)
    (gammaP : Sp → Cost LabelP) (gammaQ : Sq → Cost LabelQ)
    (costMap : Cost LabelP → Cost LabelQ) : Prop :=
  MapsSolverClasses rho gammaP gammaQ costMap

/-- Named hypothesis for the solver-class map induced by a verified costed
reduction. -/
abbrev VerifiedCostedReductionClassMapHyp (p : P) (q : Q)
    (tau : Ωp → Ωq) (rho : Sp → Sq)
    (gammaP : Sp → Cost LabelP) (gammaQ : Sq → Cost LabelQ)
    (costMap : Cost LabelP → Cost LabelQ) : Prop :=
  VerifiedCostedReduction p q tau rho gammaP gammaQ costMap ∧ Monotone costMap

/-- Named goal for the solver-class map induced by a verified costed
reduction. -/
abbrev VerifiedCostedReductionClassMapGoal
    (rho : Sp → Sq)
    (gammaP : Sp → Cost LabelP) (gammaQ : Sq → Cost LabelQ)
    (costMap : Cost LabelP → Cost LabelQ) : Prop :=
  MapsSolverClasses rho gammaP gammaQ costMap

namespace CostedReductionClassMapHyp

variable {p : P} {q : Q}
  {tau : Ωp → Ωq} {rho : Sp → Sq}
  {gammaP : Sp → Cost LabelP} {gammaQ : Sq → Cost LabelQ}
  {costMap : Cost LabelP → Cost LabelQ}

/-- A monotone cost map sends every source solver class into the corresponding
target solver class. -/
theorem mapsSolverClasses
    (h : CostedReductionClassMapHyp p q tau rho gammaP gammaQ costMap) :
    CostedReductionClassMapGoal rho gammaP gammaQ costMap := by
  rcases h with ⟨hred, hcostMap⟩
  intro c s hs
  exact le_trans (hred.2 s) (hcostMap hs)

end CostedReductionClassMapHyp

namespace VerifiedCostedReductionClassMapHyp

variable {p : P} {q : Q}
  {tau : Ωp → Ωq} {rho : Sp → Sq}
  {gammaP : Sp → Cost LabelP} {gammaQ : Sq → Cost LabelQ}
  {costMap : Cost LabelP → Cost LabelQ}

/-- A verified reduction plus monotone cost map sends every source solver class
into the corresponding target solver class. -/
theorem mapsSolverClasses
    (h : VerifiedCostedReductionClassMapHyp p q tau rho gammaP gammaQ costMap) :
    VerifiedCostedReductionClassMapGoal rho gammaP gammaQ costMap := by
  rcases h with ⟨hred, hcostMap⟩
  intro c s hs
  exact le_trans (hred.cost_le s) (hcostMap hs)

end VerifiedCostedReductionClassMapHyp

namespace IsCostedReduction

variable {p : P} {q : Q}
  {tau : Ωp → Ωq} {rho : Sp → Sq}
  {gammaP : Sp → Cost LabelP} {gammaQ : Sq → Cost LabelQ}
  {costMap : Cost LabelP → Cost LabelQ}

theorem perf_le (h : IsCostedReduction p q tau rho gammaP gammaQ costMap) :
    tau ∘ Problem.perf p ≤ Problem.perf q ∘ rho :=
  h.1

theorem cost_le (h : IsCostedReduction p q tau rho gammaP gammaQ costMap) (s : Sp) :
    gammaQ (rho s) ≤ costMap (gammaP s) :=
  h.2 s

/-- The induced map on bounded solvers, still just the underlying function
`rho` plus the subtype proof. -/
def mapBoundedSolver (h : IsCostedReduction p q tau rho gammaP gammaQ costMap)
    (hcostMap : Monotone costMap) {c : Cost LabelP} :
    BoundedSolver gammaP c → BoundedSolver gammaQ (costMap c) :=
  let hclasses : MapsSolverClasses rho gammaP gammaQ costMap :=
    CostedReductionClassMapHyp.mapsSolverClasses
      (p := p) (q := q) (tau := tau) (rho := rho)
      (gammaP := gammaP) (gammaQ := gammaQ) (costMap := costMap) ⟨h, hcostMap⟩
  fun s => ⟨rho s.1, hclasses c s.2⟩

variable {R Sr Ωr LabelR : Type*}
  [PartialOrder Ωr] [Problem R Sr Ωr]
  {r : R}
  {tauPQ : Ωp → Ωq} {tauQR : Ωq → Ωr}
  {rhoPQ : Sp → Sq} {rhoQR : Sq → Sr}
  {gammaR : Sr → Cost LabelR}
  {costPQ : Cost LabelP → Cost LabelQ}
  {costQR : Cost LabelQ → Cost LabelR}

/-- Costed reductions compose: performance translations compose as in CR18
Lemma 4.5, and cost maps compose by the same monotonicity argument. -/
theorem comp
    (hPQ : IsCostedReduction p q tauPQ rhoPQ gammaP gammaQ costPQ)
    (hQR : IsCostedReduction q r tauQR rhoQR gammaQ gammaR costQR)
    (htauQR : Monotone tauQR) (hcostQR : Monotone costQR) :
    IsCostedReduction p r (tauQR ∘ tauPQ) (rhoQR ∘ rhoPQ)
      gammaP gammaR (costQR ∘ costPQ) := by
  constructor
  · intro s
    exact le_trans (htauQR (hPQ.perf_le s)) (hQR.perf_le (rhoPQ s))
  · intro s
    exact le_trans (hQR.cost_le (rhoPQ s)) (hcostQR (hPQ.cost_le s))

end IsCostedReduction

namespace VerifiedCostedReduction

variable {p : P} {q : Q}
  {tau : Ωp → Ωq} {rho : Sp → Sq}
  {gammaP : Sp → Cost LabelP} {gammaQ : Sq → Cost LabelQ}
  {costMap : Cost LabelP → Cost LabelQ}

/-- Forget the typeclass wrapper and recover the explicit predicate. -/
theorem isCostedReduction
    (h : VerifiedCostedReduction p q tau rho gammaP gammaQ costMap) :
    IsCostedReduction p q tau rho gammaP gammaQ costMap :=
  ⟨h.perf_le, h.cost_le⟩

/-- Verified-reduction bounded-solver map. -/
def mapBoundedSolver
    (h : VerifiedCostedReduction p q tau rho gammaP gammaQ costMap)
    (hcostMap : Monotone costMap) {c : Cost LabelP} :
    BoundedSolver gammaP c → BoundedSolver gammaQ (costMap c) :=
  let hclasses : MapsSolverClasses rho gammaP gammaQ costMap :=
    VerifiedCostedReductionClassMapHyp.mapsSolverClasses
      (p := p) (q := q) (tau := tau) (rho := rho)
      (gammaP := gammaP) (gammaQ := gammaQ) (costMap := costMap) ⟨h, hcostMap⟩
  fun s => ⟨rho s.1, hclasses c s.2⟩

variable {R Sr Ωr LabelR : Type*}
  [PartialOrder Ωr] [Problem R Sr Ωr]
  {r : R}
  {tauPQ : Ωp → Ωq} {tauQR : Ωq → Ωr}
  {rhoPQ : Sp → Sq} {rhoQR : Sq → Sr}
  {gammaR : Sr → Cost LabelR}
  {costPQ : Cost LabelP → Cost LabelQ}
  {costQR : Cost LabelQ → Cost LabelR}

/-- Composition theorem for verified costed reductions. -/
theorem comp
    (hPQ : VerifiedCostedReduction p q tauPQ rhoPQ gammaP gammaQ costPQ)
    (hQR : VerifiedCostedReduction q r tauQR rhoQR gammaQ gammaR costQR)
    (htauQR : Monotone tauQR) (hcostQR : Monotone costQR) :
    VerifiedCostedReduction p r (tauQR ∘ tauPQ) (rhoQR ∘ rhoPQ)
      gammaP gammaR (costQR ∘ costPQ) where
  perf_le := fun s => le_trans (htauQR (hPQ.perf_le s)) (hQR.perf_le (rhoPQ s))
  cost_le := fun s => le_trans (hQR.cost_le (rhoPQ s)) (hcostQR (hPQ.cost_le s))

end VerifiedCostedReduction

end Complexity
end RandomSystems.CR18
