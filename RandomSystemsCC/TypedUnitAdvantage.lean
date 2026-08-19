/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedUnitMetric
import RandomSystems.StrictContextAdvantage

/-!
# Typed one-interface distance versus CR18 advantage

This module composes two independent, reusable bridges:

1. every typed `Unit` experiment compiles exactly to a strict local test;
2. every strict accepting gap is bounded by CR18 maximal distinguishing
   advantage on normalized laws.

The resulting inequality is the source-aligned direction needed to transport
existing fixed-alphabet CR18 bounds into the selected typed AC metric.  It is
not stated as an equality: an unrestricted CR18 distinguisher observes
`s ↦ s⊥` rejection and may continue, whereas strict divergence blocks.
-/

namespace RandomSystemsCC.TypedUnitAdvantage

open RandomSystems.CR18
open RandomSystems.CR18.TypedResource

open scoped ENNReal

noncomputable section

universe c u v

variable {U : SignatureUniverse.{c, u, v}} [DecidableEq U.Code]
variable {boundary : Boundary U Unit}

/-- The complete typed one-interface contextual metric is bounded by CR18
maximal distinguishing advantage on the local fixed-alphabet views. -/
theorem contextualEDist_le_maxAdvantage
    (left right : DependentPDS U boundary)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist) :
    DependentPDS.contextualEDist left right ≤
      ENNReal.ofReal Δ(left.singleView, right.singleView) := by
  exact (DependentPDS.contextualEDist_le_maxEDist_singleView left right).trans
    (StrictContextAdvantage.maxEDist_le_maxAdvantage
      left.singleView right.singleView
      ((DependentPDS.singleView_is_probability_distribution_iff left).2
        leftProb)
      ((DependentPDS.singleView_is_probability_distribution_iff right).2
        rightProb))

/-- Normalized-law form of `contextualEDist_le_maxAdvantage`. -/
theorem contextualEDist_prob_le_maxAdvantage
    (left right : DependentPDS.Prob U boundary) :
    DependentPDS.contextualEDist left.val right.val ≤
      ENNReal.ofReal Δ(left.val.singleView, right.val.singleView) :=
  contextualEDist_le_maxAdvantage left.val right.val
    left.property right.property

/-- Quotient-facing form for displayed normalized representatives. -/
theorem edist_ofProb_le_maxAdvantage
    (left right : DependentPDS.Prob U boundary) :
    edist (DependentRandomSystem.ofProb left)
        (DependentRandomSystem.ofProb right) ≤
      ENNReal.ofReal Δ(left.val.singleView, right.val.singleView) := by
  rw [DependentRandomSystem.edist_of_prob]
  exact contextualEDist_prob_le_maxAdvantage left right

end

end RandomSystemsCC.TypedUnitAdvantage
