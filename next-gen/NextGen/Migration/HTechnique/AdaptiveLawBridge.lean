/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.AdaptiveLawBridge
import NextGen.Migration.HTechnique.FixedQueryLaw

/-!
# Law-level adaptive transcript-law bridge compatibility layer

The generic law-level bridge now lives in `NextGen.AdaptiveLawBridge` under the
shared `RandomSystems.CR18` namespace.  This module preserves the migration
spelling while downstream imports are moved to the shared surface.

Migration note: this module is compatibility-only.  New proofs should import
and use the promoted `RandomSystems.CR18` declarations directly.
-/

noncomputable section

open scoped NNReal

namespace NextGen
namespace Migration
namespace HTechnique

universe u v

variable {X : Type u} {Y : Type v} {q : Nat}

/-- Compatibility wrapper for
`RandomSystems.CR18.transcriptLaw_ratio_of_fixedQuery_ratio_law`. -/
theorem transcriptLaw_ratio_of_fixedQuery_ratio_law
    (R I : ProbPDS X Y)
    (E : ProbPDE X Y)
    (eps : NNReal)
    (h_fixed : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      (1 - eps) *
          RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw I
            (fixedQueryDDE (Y := Y) xs) q t ≤
        RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw R
          (fixedQueryDDE (Y := Y) xs) q t)
    (t : TranscriptPrefix X Y q) :
    (1 - eps) * ProbPDS.transcriptLaw I E q t ≤
      ProbPDS.transcriptLaw R E q t := by
  exact RandomSystems.CR18.transcriptLaw_ratio_of_fixedQuery_ratio_law
    R I E eps h_fixed t

/-- Compatibility wrapper for
`RandomSystems.CR18.oneSided_hTechnique_law_experiment_of_fixedQuery_ratio`. -/
theorem oneSided_hTechnique_law_experiment_of_fixedQuery_ratio
    [FiniteTranscriptSpace X Y q]
    (R I : ProbPDS X Y)
    (E : ProbPDE X Y)
    (eps : NNReal)
    (hRtotal : R.KStepTotal q)
    (hItotal : I.KStepTotal q)
    (hEtotal : E.KQueryTotal q)
    (h_fixed : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      (1 - eps) *
          RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw I
            (fixedQueryDDE (Y := Y) xs) q t ≤
        RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw R
          (fixedQueryDDE (Y := Y) xs) q t) :
    RandomSystems.statDist
        (ProbPDS.transcriptDist (q := q) R E)
        (ProbPDS.transcriptDist (q := q) I E) ≤ eps := by
  exact RandomSystems.CR18.oneSided_hTechnique_law_experiment_of_fixedQuery_ratio
    R I E eps hRtotal hItotal hEtotal h_fixed

end HTechnique
end Migration
end NextGen
