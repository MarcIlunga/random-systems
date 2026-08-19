/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.SoP.AdaptiveAdvantage

/-!
# SoP legacy/support boundary

This module keeps legacy SoP adaptive names build-checked during the migration.
The full adaptive name now routes to the law-level `SoP.advPRF` endpoint; the
old bounded-chooser name remains a representative compatibility wrapper over
the law-level bounded supremum.  This module is imported by `All`, not by the
curated future-promotion `Surface`.
-/

noncomputable section

open scoped NNReal

namespace RandomSystems
namespace HTechnique

/-- **Support boundary.** Legacy name for the law-level adaptive SoP transcript
advantage bound.  The paper-facing public PRF endpoint is `sop_advPRF_le` in
`SoPBoundary`. -/
theorem sop_adaptiveTranscriptAdvantage_bound
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    SoP.adaptiveTranscriptAdvantage (G := G) (q := q) ≤
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 : ℝ) := by
  exact SoP.adaptiveTranscriptAdvantage_bound h_bound

/-- **Support boundary.** Bounded-environment SoP transcript advantage bound,
restricted to old-style q-round deterministic choosers. -/
theorem sop_boundedAdaptiveTranscriptAdvantage_bound
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    SoP.boundedAdaptiveTranscriptAdvantage (G := G) (q := q) ≤
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 : ℝ) := by
  exact SoP.boundedAdaptiveTranscriptAdvantage_bound h_bound

end HTechnique
end RandomSystems
