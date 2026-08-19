/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedFramingMetric
import RandomSystems.StrictContextAdvantage
import RandomSystems.StrictContextTotal

/-!
# Arbitrary-interface typed distance versus CR18 advantage

Metric full abstraction reduces every typed AC context to a strict test on
the flattened global law. Completing that strict test with rejecting verdict
`false` gives the source-aligned comparison with CR18 maximal distinguishing
advantage.

The unconditional result is an inequality. Equality with CR18's
observable-completion metric is stated only when both flattened laws are
total on nonempty histories; unrestricted CR18 distinguishers may otherwise
observe completion and continue, whereas the selected typed semantics uses
blocking divergence.
-/

namespace RandomSystemsCC.TypedFramingAdvantage

open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource
open scoped ENNReal

noncomputable section

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}}
variable [DecidableEq I] [DecidableEq U.Code]
variable {boundary : Boundary U I}

/-- The complete arbitrary-interface typed contextual metric is bounded by
CR18 maximal distinguishing advantage on the flattened global laws. -/
theorem contextual_edist_prob_le_max_advantage_flatten
    (left right : DependentPDS.Prob U boundary) :
    DependentPDS.contextualEDist left.val right.val ≤
      ENNReal.ofReal
        Δ(DependentPDS.flatten left.val, DependentPDS.flatten right.val) := by
  rw [DependentPDS.contextual_edist_eq_max_edist_flatten]
  exact StrictContextAdvantage.maxEDist_le_maxAdvantage
    (DependentPDS.flatten left.val) (DependentPDS.flatten right.val)
    ((DependentPDS.flatten_is_probability_distribution_iff left.val).2
      left.property)
    ((DependentPDS.flatten_is_probability_distribution_iff right.val).2
      right.property)

/-- Quotient-facing form of the source-aligned comparison. -/
theorem edist_of_prob_le_max_advantage_flatten
    (left right : DependentPDS.Prob U boundary) :
    edist (DependentRandomSystem.ofProb left)
        (DependentRandomSystem.ofProb right) ≤
      ENNReal.ofReal
        Δ(DependentPDS.flatten left.val, DependentPDS.flatten right.val) := by
  rw [DependentRandomSystem.edist_of_prob]
  exact contextual_edist_prob_le_max_advantage_flatten left right

/-- If both flattened supports are total, the typed metric and CR18 maximal
advantage agree exactly. -/
theorem contextual_edist_prob_eq_max_advantage_flatten_of_total
    (left right : DependentPDS.Prob U boundary)
    (leftTotal : CondEquiv.TotalOnNonempty (DependentPDS.flatten left.val))
    (rightTotal : CondEquiv.TotalOnNonempty (DependentPDS.flatten right.val)) :
    DependentPDS.contextualEDist left.val right.val =
      ENNReal.ofReal
        Δ(DependentPDS.flatten left.val, DependentPDS.flatten right.val) := by
  rw [DependentPDS.contextual_edist_eq_max_edist_flatten]
  exact StrictContextTotal.maxEDist_eq_ofReal_maxAdvantage_of_total
    (DependentPDS.flatten left.val) (DependentPDS.flatten right.val)
    ((DependentPDS.flatten_is_probability_distribution_iff left.val).2
      left.property)
    ((DependentPDS.flatten_is_probability_distribution_iff right.val).2
      right.property)
    leftTotal rightTotal

/-- Quotient-facing equality on support-total flattened laws. -/
theorem edist_of_prob_eq_max_advantage_flatten_of_total
    (left right : DependentPDS.Prob U boundary)
    (leftTotal : CondEquiv.TotalOnNonempty (DependentPDS.flatten left.val))
    (rightTotal : CondEquiv.TotalOnNonempty (DependentPDS.flatten right.val)) :
    edist (DependentRandomSystem.ofProb left)
        (DependentRandomSystem.ofProb right) =
      ENNReal.ofReal
        Δ(DependentPDS.flatten left.val, DependentPDS.flatten right.val) := by
  rw [DependentRandomSystem.edist_of_prob]
  exact contextual_edist_prob_eq_max_advantage_flatten_of_total
    left right leftTotal rightTotal

end

end RandomSystemsCC.TypedFramingAdvantage
