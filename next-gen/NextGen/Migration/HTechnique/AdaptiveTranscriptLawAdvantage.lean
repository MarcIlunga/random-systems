/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.BoundedEnvironment
import NextGen.Migration.HTechnique.TranscriptLawPublic

/-!
# Law-level adaptive transcript advantage

This module contains the public, thesis-style adaptive transcript advantage on
the CR18 transcript-law surface.  It deliberately mentions only law-level PDS
objects and deterministic CR18 environments.  Representative-level adaptive
advantages live in `AdaptiveTranscriptAdvantage`.
-/

noncomputable section

open scoped NNReal

namespace NextGen
namespace Migration
namespace HTechnique

universe u v

variable {X : Type u} {Y : Type v} {q : Nat}

/-- Compatibility alias for core law-level transcript-adaptive advantage between
two CR18 probabilistic systems: the
supremum, over q-query-total deterministic environments, of the statistical
distance between their length-`q` deterministic transcript laws.

This is the paper-facing transcript-law object.  It takes only the two PDS laws;
sample spaces, random variables, and representative adapters do not appear in
the statement. -/
noncomputable abbrev adaptiveTranscriptLawAdvantage
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) : ℝ :=
  RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T

/-- **Support lemma forced by formalization; candidate for upstream.** The image
defining the law-level adaptive transcript advantage is bounded above by `1`.

This is the reusable side-condition for comparing a restricted environment
supremum with the full thesis-style supremum. -/
theorem adaptiveTranscriptLawAdvantage_image_bddAbove
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) :
    BddAbove ((fun E : QQueryEnvironment X Y q =>
      (RandomSystems.statDist
        (ProbPDS.deterministicTranscriptDist (q := q) S E.1)
        (ProbPDS.deterministicTranscriptDist (q := q) T E.1) : ℝ)) ''
      Set.univ) := by
  exact RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage_image_bddAbove
    (q := q) S T

/-- Compatibility wrapper for the core pointwise-bound theorem. -/
theorem adaptiveTranscriptLawAdvantage_le_of_pointwise
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y)
    (eps : NNReal)
    (h_pointwise : ∀ E : QQueryEnvironment X Y q,
        RandomSystems.statDist
          (ProbPDS.deterministicTranscriptDist (q := q) S E.1)
          (ProbPDS.deterministicTranscriptDist (q := q) T E.1) ≤ eps) :
    adaptiveTranscriptLawAdvantage (q := q) S T ≤ (eps : ℝ) := by
  exact RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise
    S T eps h_pointwise

/-- **Source-theorem bridge; candidate for upstream.** Law-level bounded-chooser
adaptive transcript advantage: the supremum restricted to deterministic
q-round choosers `choose_i : Y^i -> X`, embedded exactly as CR18 partial
environments by `RandomSystems.CR18.boundedDDE`.

This is the law-level counterpart of the old bounded `advantageAdaptive` index
set.  It takes only the two PDS laws; representatives and sample spaces are
construction details of compatibility adapters. -/
noncomputable abbrev boundedAdaptiveTranscriptLawAdvantage
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) : ℝ :=
  RandomSystems.CR18.PFunPDS.Prob.boundedAdaptiveTranscriptAdvantage (q := q) S T

/-- Compatibility alias for the core bounded-chooser supremum image-bound fact. -/
theorem boundedAdaptiveTranscriptLawAdvantage_image_bddAbove
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) :
    BddAbove ((fun choose : (i : Fin q) → (Fin i.1 → Y) → X =>
      (RandomSystems.statDist
        (ProbPDS.deterministicTranscriptDist (q := q) S
          (RandomSystems.CR18.boundedDDE choose))
        (ProbPDS.deterministicTranscriptDist (q := q) T
          (RandomSystems.CR18.boundedDDE choose)) : ℝ)) ''
      Set.univ) := by
  exact
    RandomSystems.CR18.PFunPDS.Prob.boundedAdaptiveTranscriptAdvantage_image_bddAbove
      (q := q) S T

/-- Compatibility alias for the core bounded-chooser supremum nonnegativity fact. -/
theorem boundedAdaptiveTranscriptLawAdvantage_nonneg
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) :
    0 ≤ boundedAdaptiveTranscriptLawAdvantage (q := q) S T := by
  exact RandomSystems.CR18.PFunPDS.Prob.boundedAdaptiveTranscriptAdvantage_nonneg
    (q := q) S T

/-- Compatibility alias for the core comparison from the bounded-chooser
sub-supremum to the full law-level CR18 q-query-total environment supremum. -/
theorem boundedAdaptiveTranscriptLawAdvantage_le_adaptiveTranscriptLawAdvantage
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) :
    boundedAdaptiveTranscriptLawAdvantage (q := q) S T ≤
      adaptiveTranscriptLawAdvantage (q := q) S T := by
  exact
    RandomSystems.CR18.PFunPDS.Prob.boundedAdaptiveTranscriptAdvantage_le_adaptiveTranscriptAdvantage
      (q := q) S T

end HTechnique
end Migration
end NextGen
