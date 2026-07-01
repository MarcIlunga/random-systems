/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.FixedQuery
import NextGen.Migration.HTechnique.TranscriptLaw

/-!
# Adaptive transcript-law bridge

This module contains the generic CR18 bridge from fixed-query pointwise
transcript-law ratios to arbitrary-environment pointwise transcript-law ratios.

Source status:

* source-theorem bridge: CR18 Lemma 3.2 factors any transcript law into a system
  factor and an environment factor.  Therefore a one-sided lower bound proved
  for every fixed query vector transfers to every CR18 environment by multiplying
  both sides by the common environment factor.

Migration note: this module is compatibility-only.  New proofs should use the
law-level bridge in `AdaptiveLawBridge` or the promoted core CR18 theorem
directly; representative-shaped statements remain here only for legacy support.
-/

noncomputable section

open scoped NNReal

namespace NextGen
namespace Migration
namespace HTechnique

universe u v w z r

variable {X : Type u} {Y : Type v} {q : Nat}

/-- **Source-theorem bridge.** Fixed-query pointwise transcript-law ratios
transfer to arbitrary CR18 environments.  This is the migrated form of the
adaptive bridge used by the H-technique: the proof is just CR18 Lemma 3.2
(`transcriptLaw = systemFactor * environmentFactor`) plus the fixed-query
environment, not an application-specific argument. -/
theorem transcriptLaw_ratio_of_fixedQuery_ratio
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y)
    (E : PDERepresentative.{u, v, r} X Y)
    (eps : NNReal)
    (h_fixed : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      (1 - eps) *
          PDSRepresentative.transcriptLaw I
            (PDERepresentative.deterministic (fixedQueryEnvironment xs)) q t ≤
        PDSRepresentative.transcriptLaw R
          (PDERepresentative.deterministic (fixedQueryEnvironment xs)) q t)
    (t : TranscriptPrefix X Y q) :
    (1 - eps) *
        PDSRepresentative.transcriptLaw I E q t ≤
      PDSRepresentative.transcriptLaw R E q t := by
  rcases t with ⟨xv, yv⟩
  let xs : Fin q → X := functionOfVector xv
  have h_sys :
      (1 - eps) * RandomSystems.CR18.PFunPDE.transcriptSystemFactor I.prob I.rv xv yv ≤
        RandomSystems.CR18.PFunPDE.transcriptSystemFactor R.prob R.rv xv yv := by
    have hI :
        PDSRepresentative.transcriptLaw I
            (PDERepresentative.deterministic (fixedQueryEnvironment xs)) q (xv, yv) =
          RandomSystems.CR18.PFunPDE.transcriptSystemFactor I.prob I.rv xv yv := by
      simpa [PDSRepresentative.transcriptLaw, xs] using
        transcriptLaw_fixedQueryEnvironment_of_eq I.prob I.rv xs yv
    have hR :
        PDSRepresentative.transcriptLaw R
            (PDERepresentative.deterministic (fixedQueryEnvironment xs)) q (xv, yv) =
          RandomSystems.CR18.PFunPDE.transcriptSystemFactor R.prob R.rv xv yv := by
      simpa [PDSRepresentative.transcriptLaw, xs] using
        transcriptLaw_fixedQueryEnvironment_of_eq R.prob R.rv xs yv
    have h := h_fixed xs (xv, yv)
    rw [hI, hR] at h
    exact h
  change (1 - eps) *
        RandomSystems.CR18.PFunPDE.transcriptLaw I.prob E.prob I.rv E.rv q (xv, yv) ≤
      RandomSystems.CR18.PFunPDE.transcriptLaw R.prob E.prob R.rv E.rv q (xv, yv)
  cr18_transcript
  calc (1 - eps) *
        (RandomSystems.CR18.PFunPDE.transcriptSystemFactor I.prob I.rv xv yv *
          RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor E.prob E.rv xv yv)
      = ((1 - eps) * RandomSystems.CR18.PFunPDE.transcriptSystemFactor I.prob I.rv xv yv) *
          RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor E.prob E.rv xv yv := by rw [← mul_assoc]
    _ ≤ RandomSystems.CR18.PFunPDE.transcriptSystemFactor R.prob R.rv xv yv *
          RandomSystems.CR18.PFunPDE.transcriptEnvironmentFactor E.prob E.rv xv yv := by
        gcongr

/-- **Source-theorem bridge.** Fixed-query pointwise transcript-law ratios give
the one-sided H-technique bound for every CR18 environment.  This is the
statistical-distance packaging of `transcriptLaw_ratio_of_fixedQuery_ratio`;
the generic CR18 transcript-law normalization theorems supply the total-weight
and ideal-subdistribution side conditions from totality. -/
theorem oneSided_hTechnique_experiment_of_fixedQuery_ratio
    [FiniteTranscriptSpace X Y q]
    [DiscreteTranscriptSpace X Y q]
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y)
    (E : PDERepresentative.{u, v, r} X Y)
    (eps : NNReal)
    (hRtotal : R.KStepTotal q)
    (hItotal : I.KStepTotal q)
    (hEtotal : E.KQueryTotal q)
    (h_fixed : ∀ (xs : Fin q → X) (t : TranscriptPrefix X Y q),
      (1 - eps) *
          PDSRepresentative.transcriptLaw I
            (PDERepresentative.deterministic (fixedQueryEnvironment xs)) q t ≤
        PDSRepresentative.transcriptLaw R
          (PDERepresentative.deterministic (fixedQueryEnvironment xs)) q t) :
    RandomSystems.statDist
        (PDSRepresentative.transcriptDist (q := q) R E)
        (PDSRepresentative.transcriptDist (q := q) I E) ≤ eps := by
  have h_weight :
      (PDSRepresentative.transcriptDist (q := q) R E).weight =
      (PDSRepresentative.transcriptDist (q := q) I E).weight := by
    have hR :=
      RandomSystems.CR18.PFunPDE.transcriptLawDist_weight_eq_one_of_total
        R.prob E.prob R.rv E.rv hRtotal hEtotal
    have hI :=
      RandomSystems.CR18.PFunPDE.transcriptLawDist_weight_eq_one_of_total
        I.prob E.prob I.rv E.rv hItotal hEtotal
    simpa [PDSRepresentative.transcriptDist, PDSRepresentative.transcriptLaw] using hR.trans hI.symm
  exact TranscriptLawBridge.oneSided_hTechnique_experiment R I E eps
    h_weight
    (by
      simpa [PDSRepresentative.transcriptDist, PDSRepresentative.transcriptLaw] using
        RandomSystems.CR18.PFunPDE.transcriptLawDist_weight_le_one I.prob E.prob I.rv E.rv)
    (fun t => transcriptLaw_ratio_of_fixedQuery_ratio R I E eps h_fixed t)

end HTechnique
end Migration
end NextGen
