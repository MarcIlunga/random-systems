/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.TranscriptLawPublic
import RandomSystems.StatDist

/-!
# Transcript-law H-technique core bridge

This module contains the representative-free bridge from CR18 transcript laws to
the migrated H-technique density lemmas.

The statements here are candidates for upstreaming: they only mention transcript
laws and finite transcript-prefix distributions.  Representative/sample-space
adapters stay in `TranscriptLaw`.
-/

noncomputable section

open scoped NNReal

universe u v

namespace NextGen
namespace Migration
namespace HTechnique

namespace Density

/-- **Support lemma forced by formalization; candidate for upstream.** The
ratio-form H-technique applied to finite mass functions rather than explicit
`Dist` objects. -/
theorem hTechnique_ratio_massFunction {A : Type*} [Fintype A]
    (real ideal : A → NNReal)
    (B : A → Prop)
    (eps : NNReal)
    (h_weight :
      (RandomSystems.Dist.ofFiniteMassFunction real).weight =
        (RandomSystems.Dist.ofFiniteMassFunction ideal).weight)
    (h_ideal_le : (RandomSystems.Dist.ofFiniteMassFunction ideal).weight ≤ 1)
    (h_ratio : ∀ a, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist (RandomSystems.Dist.ofFiniteMassFunction real)
        (RandomSystems.Dist.ofFiniteMassFunction ideal) ≤
      RandomSystems.probBad (RandomSystems.Dist.ofFiniteMassFunction ideal) B + eps := by
  exact RandomSystems.hTechnique_ratio_massFunction real ideal B eps
    h_weight h_ideal_le h_ratio

/-- **Support lemma forced by formalization; candidate for upstream.** The
one-sided H-technique applied to finite mass functions rather than explicit
`Dist` objects. -/
theorem oneSided_hTechnique_massFunction {A : Type*} [Fintype A]
    (real ideal : A → NNReal)
    (eps : NNReal)
    (h_weight :
      (RandomSystems.Dist.ofFiniteMassFunction real).weight =
        (RandomSystems.Dist.ofFiniteMassFunction ideal).weight)
    (h_ideal_le : (RandomSystems.Dist.ofFiniteMassFunction ideal).weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist (RandomSystems.Dist.ofFiniteMassFunction real)
      (RandomSystems.Dist.ofFiniteMassFunction ideal) ≤ eps := by
  exact RandomSystems.oneSided_hTechnique_massFunction real ideal eps
    h_weight h_ideal_le h_lower

end Density

namespace TranscriptLawBridge

/-- The finite distribution represented by a transcript-law mass function. -/
abbrev dist {X : Type u} {Y : Type v} {k : ℕ}
    [FiniteTranscriptSpace X Y k]
    (law : RandomSystems.CR18.PFunPDE.TranscriptLaw X Y k) :
    RandomSystems.Dist (TranscriptPrefix X Y k) :=
  RandomSystems.CR18.PFunPDE.transcriptLawDist law

@[simp]
theorem dist_apply {X : Type u} {Y : Type v} {k : ℕ}
    [FiniteTranscriptSpace X Y k]
    (law : RandomSystems.CR18.PFunPDE.TranscriptLaw X Y k)
    (t : TranscriptPrefix X Y k) :
    dist law t = law t := by
  simp [dist]

/-- **Source-theorem bridge; candidate for upstream.** Ratio-form H-technique
for two CR18 transcript laws over the same transcript-prefix carrier. -/
theorem hTechnique_ratio {X : Type u} {Y : Type v} {k : ℕ}
    [FiniteTranscriptSpace X Y k]
    (real ideal : RandomSystems.CR18.PFunPDE.TranscriptLaw X Y k)
    (B : TranscriptPrefix X Y k → Prop)
    (eps : NNReal)
    (h_weight : (dist real).weight = (dist ideal).weight)
    (h_ideal_le : (dist ideal).weight ≤ 1)
    (h_ratio : ∀ t, ¬ B t → (1 - eps) * ideal t ≤ real t) :
    RandomSystems.statDist (dist real) (dist ideal) ≤
      RandomSystems.probBad (dist ideal) B + eps := by
  exact RandomSystems.hTechnique_ratio (dist real) (dist ideal) B eps
    h_weight h_ideal_le h_ratio

/-- **Source-theorem bridge; candidate for upstream.** One-sided H-technique for
two CR18 transcript laws over the same transcript-prefix carrier. -/
theorem oneSided_hTechnique {X : Type u} {Y : Type v} {k : ℕ}
    [FiniteTranscriptSpace X Y k]
    (real ideal : RandomSystems.CR18.PFunPDE.TranscriptLaw X Y k)
    (eps : NNReal)
    (h_weight : (dist real).weight = (dist ideal).weight)
    (h_ideal_le : (dist ideal).weight ≤ 1)
    (h_lower : ∀ t, (1 - eps) * ideal t ≤ real t) :
    RandomSystems.statDist (dist real) (dist ideal) ≤ eps := by
  exact RandomSystems.oneSided_hTechnique (dist real) (dist ideal) eps
    h_weight h_ideal_le h_lower

end TranscriptLawBridge

end HTechnique
end Migration
end NextGen
