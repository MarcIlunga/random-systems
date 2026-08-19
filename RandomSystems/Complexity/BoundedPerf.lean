/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.Reduction

/-!
# Bounded-performance transfer

These theorems are the derived-performance payoff of a costed reduction.  The
general theorem keeps the only non-order-theoretic requirement explicit: the
performance translation `tau` must move the source supremum below the supremum
of translated source performances.  The identity-translation theorem needs no
such hypothesis.
-/

namespace RandomSystems.CR18
namespace Complexity

noncomputable section

namespace IsCostedReduction

variable {P Sp Ωp Q Sq Ωq : Type*}
  [PartialOrder Ωp] [SupSet Ωp] [Problem P Sp Ωp]
  [CompleteLattice Ωq] [Problem Q Sq Ωq]
  {LabelP LabelQ : Type*}
  {p : P} {q : Q}
  {tau : Ωp → Ωq} {rho : Sp → Sq}
  {gammaP : Sp → Cost LabelP} {gammaQ : Sq → Cost LabelQ}
  {costMap : Cost LabelP → Cost LabelQ}

/-- A costed reduction transfers derived performance after translating the
source supremum, assuming exactly the displayed supremum-translation bound. -/
theorem translated_costBoundedPerf_le
    (h : IsCostedReduction p q tau rho gammaP gammaQ costMap)
    (hcostMap : Monotone costMap) {c : Cost LabelP}
    (hSup : tau (costBoundedPerf gammaP p c) ≤
      sSup (tau '' (Problem.perf p '' SolverClass gammaP c))) :
    tau (costBoundedPerf gammaP p c) ≤
      costBoundedPerf gammaQ q (costMap c) := by
  refine le_trans hSup ?_
  refine sSup_le ?_
  rintro y ⟨x, hx, rfl⟩
  rcases hx with ⟨s, hs, rfl⟩
  exact le_trans (h.perf_le s)
    (le_sSup ⟨rho s,
      CostedReductionClassMapHyp.mapsSolverClasses
        (p := p) (q := q) (tau := tau) (rho := rho)
        (gammaP := gammaP) (gammaQ := gammaQ) (costMap := costMap)
        ⟨h, hcostMap⟩ c hs, rfl⟩)

variable {Ω : Type*} [CompleteLattice Ω]
  {P' Sp' Q' Sq' : Type*}
  [Problem P' Sp' Ω] [Problem Q' Sq' Ω]
  {LabelP' LabelQ' : Type*}
  {p' : P'} {q' : Q'} {rho' : Sp' → Sq'}
  {gammaP' : Sp' → Cost LabelP'} {gammaQ' : Sq' → Cost LabelQ'}
  {costMap' : Cost LabelP' → Cost LabelQ'}

/-- Identity-performance reductions transfer bounded performance directly. -/
theorem costBoundedPerf_le
    (h : IsCostedReduction p' q' (_root_.id : Ω → Ω) rho' gammaP' gammaQ' costMap')
    (hcostMap : Monotone costMap') {c : Cost LabelP'} :
    costBoundedPerf (Solver := Sp') (Label := LabelP') (ProblemObject := P') (Perf := Ω)
        gammaP' p' c ≤
      costBoundedPerf (Solver := Sq') (Label := LabelQ') (ProblemObject := Q') (Perf := Ω)
        gammaQ' q' (costMap' c) := by
  unfold costBoundedPerf derivedPerf
  refine sSup_le ?_
  rintro y ⟨s, hs, rfl⟩
  exact le_trans (h.perf_le s)
    (le_sSup ⟨rho' s,
      CostedReductionClassMapHyp.mapsSolverClasses
        (p := p') (q := q') (tau := (_root_.id : Ω → Ω)) (rho := rho')
        (gammaP := gammaP') (gammaQ := gammaQ') (costMap := costMap')
        ⟨h, hcostMap⟩ c hs, rfl⟩)

/-- Named hypothesis for composing an identity-performance reduction with a
target bounded-performance theorem. -/
abbrev BoundTransferHyp
    (p : P') (q : Q') (rho : Sp' → Sq')
    (gammaP : Sp' → Cost LabelP') (gammaQ : Sq' → Cost LabelQ')
    (costMap : Cost LabelP' → Cost LabelQ')
    (c : Cost LabelP') (bound : Ω) : Prop :=
  IsCostedReduction p q (_root_.id : Ω → Ω) rho gammaP gammaQ costMap ∧
    Monotone costMap ∧
    costBoundedPerf (Solver := Sq') (Label := LabelQ') (ProblemObject := Q') (Perf := Ω)
      gammaQ q (costMap c) ≤ bound

/-- Named goal for the source bound obtained by composing a reduction with the
target bound. -/
abbrev BoundTransferGoal
    (p : P') (gammaP : Sp' → Cost LabelP') (c : Cost LabelP') (bound : Ω) : Prop :=
  costBoundedPerf (Solver := Sp') (Label := LabelP') (ProblemObject := P') (Perf := Ω)
    gammaP p c ≤ bound

namespace BoundTransferHyp

theorem bound
    {p : P'} {q : Q'} {rho : Sp' → Sq'}
    {gammaP : Sp' → Cost LabelP'} {gammaQ : Sq' → Cost LabelQ'}
    {costMap : Cost LabelP' → Cost LabelQ'}
    {c : Cost LabelP'} {bound : Ω}
    (h : BoundTransferHyp p q rho gammaP gammaQ costMap c bound) :
    BoundTransferGoal p gammaP c bound := by
  exact le_trans (IsCostedReduction.costBoundedPerf_le h.1 h.2.1) h.2.2

end BoundTransferHyp

end IsCostedReduction

namespace VerifiedCostedReduction

variable {P Sp Ωp Q Sq Ωq : Type*}
  [PartialOrder Ωp] [SupSet Ωp] [Problem P Sp Ωp]
  [CompleteLattice Ωq] [Problem Q Sq Ωq]
  {LabelP LabelQ : Type*}
  {p : P} {q : Q}
  {tau : Ωp → Ωq} {rho : Sp → Sq}
  {gammaP : Sp → Cost LabelP} {gammaQ : Sq → Cost LabelQ}
  {costMap : Cost LabelP → Cost LabelQ}

/-- Verified-reduction translated bounded-performance transfer. -/
theorem translated_costBoundedPerf_le
    (h : VerifiedCostedReduction p q tau rho gammaP gammaQ costMap)
    (hcostMap : Monotone costMap) {c : Cost LabelP}
    (hSup : tau (costBoundedPerf gammaP p c) ≤
      sSup (tau '' (Problem.perf p '' SolverClass gammaP c))) :
    tau (costBoundedPerf gammaP p c) ≤
      costBoundedPerf gammaQ q (costMap c) :=
  IsCostedReduction.translated_costBoundedPerf_le
    (VerifiedCostedReduction.isCostedReduction h)
    hcostMap hSup

variable {Ω : Type*} [CompleteLattice Ω]
  {P' Sp' Q' Sq' : Type*}
  [Problem P' Sp' Ω] [Problem Q' Sq' Ω]
  {LabelP' LabelQ' : Type*}
  {p' : P'} {q' : Q'} {rho' : Sp' → Sq'}
  {gammaP' : Sp' → Cost LabelP'} {gammaQ' : Sq' → Cost LabelQ'}
  {costMap' : Cost LabelP' → Cost LabelQ'}

/-- Verified-reduction bounded-performance transfer for
identity-performance reductions. -/
theorem costBoundedPerf_le
    (h : VerifiedCostedReduction p' q' (_root_.id : Ω → Ω) rho' gammaP' gammaQ' costMap')
    (hcostMap : Monotone costMap') {c : Cost LabelP'} :
    costBoundedPerf (Solver := Sp') (Label := LabelP') (ProblemObject := P') (Perf := Ω)
        gammaP' p' c ≤
      costBoundedPerf (Solver := Sq') (Label := LabelQ') (ProblemObject := Q') (Perf := Ω)
        gammaQ' q' (costMap' c) :=
  IsCostedReduction.costBoundedPerf_le
    (VerifiedCostedReduction.isCostedReduction h)
    hcostMap

/-- Named hypothesis for composing a verified identity-performance reduction
with a target bounded-performance theorem. -/
abbrev BoundTransferHyp
    (p : P') (q : Q') (rho : Sp' → Sq')
    (gammaP : Sp' → Cost LabelP') (gammaQ : Sq' → Cost LabelQ')
    (costMap : Cost LabelP' → Cost LabelQ')
    (c : Cost LabelP') (bound : Ω) : Prop :=
  VerifiedCostedReduction p q (_root_.id : Ω → Ω) rho gammaP gammaQ costMap ∧
    Monotone costMap ∧
    costBoundedPerf (Solver := Sq') (Label := LabelQ') (ProblemObject := Q') (Perf := Ω)
      gammaQ q (costMap c) ≤ bound

/-- Named goal for the source bound obtained by composing a verified reduction
with the target bound. -/
abbrev BoundTransferGoal
    (p : P') (gammaP : Sp' → Cost LabelP') (c : Cost LabelP') (bound : Ω) : Prop :=
  costBoundedPerf (Solver := Sp') (Label := LabelP') (ProblemObject := P') (Perf := Ω)
    gammaP p c ≤ bound

namespace BoundTransferHyp

theorem bound
    {p : P'} {q : Q'} {rho : Sp' → Sq'}
    {gammaP : Sp' → Cost LabelP'} {gammaQ : Sq' → Cost LabelQ'}
    {costMap : Cost LabelP' → Cost LabelQ'}
    {c : Cost LabelP'} {bound : Ω}
    (h : BoundTransferHyp p q rho gammaP gammaQ costMap c bound) :
    BoundTransferGoal p gammaP c bound := by
  exact le_trans (VerifiedCostedReduction.costBoundedPerf_le h.1 h.2.1) h.2.2

end BoundTransferHyp

end VerifiedCostedReduction

end

end Complexity
end RandomSystems.CR18
