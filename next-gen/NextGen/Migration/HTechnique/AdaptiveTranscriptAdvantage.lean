/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.BoundedEnvironment
import NextGen.Migration.HTechnique.TranscriptLaw
import NextGen.Migration.HTechnique.AdaptiveTranscriptLawAdvantage

/-!
# Adaptive transcript advantage

This module packages the transcript-law form of adaptive advantage used by the
H-technique migration.

Source status:

* source-theorem bridge: CR18/Lanzenberger adaptive advantage is a supremum over
  compatible deterministic environments.  The public law-level supremum lives in
  `AdaptiveTranscriptLawAdvantage`; this file keeps the representative-shaped
  compatibility wrappers needed by legacy endpoints.

Migration note: this module is compatibility-only.  New theorems should be
stated on law-level `ProbPDS` objects and use `SecurityDefs.Adv` or
`adaptiveTranscriptLawAdvantage`; representatives should not appear in new
public theorem headers.

This is deliberately a transcript-law endpoint, not the final raw
`Δ([q]S,[q]T)` endpoint.  The exact old bounded `advantageAdaptive` bridge for
legacy representatives is supplied by `LegacyBoundedTranscript`; the remaining
main-surface migration step is the representative-level CR18/thesis advantage
notation and endpoint alias layer.
-/

noncomputable section

open scoped NNReal

namespace NextGen
namespace Migration
namespace HTechnique

universe u v w z

variable {X : Type u} {Y : Type v} {q : Nat}

/-- **Source-theorem bridge; candidate for upstream.** Transcript-law adaptive
advantage between two CR18 system representatives.  This is now only a
compatibility wrapper: it applies the law-level adaptive transcript advantage to
the two PDS laws induced by the representatives.

The theorem-facing inputs are the two represented systems.  The ambient sample
spaces, probability laws, and system-valued random variables are intentionally
kept inside `PDSRepresentative`. -/
noncomputable def adaptiveTranscriptAdvantage
    [FiniteTranscriptSpace X Y q]
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y) : ℝ :=
  adaptiveTranscriptLawAdvantage (q := q)
    (RandomSystems.Dist.PMF R.prob R.rv)
    (RandomSystems.Dist.PMF I.prob I.rv)

/-- **Source-theorem bridge; candidate for upstream.** A uniform pointwise bound
for every q-query-total deterministic environment bounds the corresponding
adaptive transcript supremum. -/
theorem adaptiveTranscriptAdvantage_le_of_pointwise
    [FiniteTranscriptSpace X Y q]
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y)
    (eps : NNReal)
    (h_pointwise : ∀ E : QQueryEnvironment X Y q,
        RandomSystems.statDist
          (PDSRepresentative.transcriptDist (q := q) R (PDERepresentative.ofDDE E.1))
          (PDSRepresentative.transcriptDist (q := q) I (PDERepresentative.ofDDE E.1)) ≤ eps) :
    adaptiveTranscriptAdvantage (q := q) R I ≤ (eps : ℝ) := by
  refine adaptiveTranscriptLawAdvantage_le_of_pointwise
    (q := q)
    (RandomSystems.Dist.PMF R.prob R.rv)
    (RandomSystems.Dist.PMF I.prob I.rv)
    eps ?_
  intro E
  simpa [PDSRepresentative.deterministicTranscriptDist_ofProbPDS_pmf] using
    h_pointwise E

/-- **Source-theorem bridge; candidate for upstream.** The bounded-environment
adaptive transcript advantage for representatives.  This is a compatibility
wrapper over the law-level bounded-chooser transcript advantage applied to the
two PDS laws induced by the representatives.

This is the migration-facing counterpart of the old bounded
`RandomSystems.advantageAdaptive` index set, but it remains stated on the
CR18 transcript-law surface. -/
noncomputable def boundedAdaptiveTranscriptAdvantage
    [FiniteTranscriptSpace X Y q]
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y) : ℝ :=
  boundedAdaptiveTranscriptLawAdvantage (q := q)
    (RandomSystems.Dist.PMF R.prob R.rv)
    (RandomSystems.Dist.PMF I.prob I.rv)

/-- **Support lemma forced by formalization; candidate for upstream.** The
bounded-chooser transcript advantage is nonnegative, including the empty
chooser-index case where the supremum is Mathlib's `sSup ∅ = 0`. -/
theorem boundedAdaptiveTranscriptAdvantage_nonneg
    [FiniteTranscriptSpace X Y q]
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y) :
    0 ≤ boundedAdaptiveTranscriptAdvantage (q := q) R I := by
  exact boundedAdaptiveTranscriptLawAdvantage_nonneg
    (q := q)
    (RandomSystems.Dist.PMF R.prob R.rv)
    (RandomSystems.Dist.PMF I.prob I.rv)

/-- **Source-theorem bridge; candidate for upstream.** The bounded-chooser
supremum is a sub-supremum of the CR18 q-query-total environment supremum. -/
theorem boundedAdaptiveTranscriptAdvantage_le_adaptiveTranscriptAdvantage
    [FiniteTranscriptSpace X Y q]
    (R : PDSRepresentative.{u, v, w} X Y)
    (I : PDSRepresentative.{u, v, z} X Y) :
    boundedAdaptiveTranscriptAdvantage (q := q) R I ≤
      adaptiveTranscriptAdvantage (q := q) R I := by
  exact boundedAdaptiveTranscriptLawAdvantage_le_adaptiveTranscriptLawAdvantage
    (q := q)
    (RandomSystems.Dist.PMF R.prob R.rv)
    (RandomSystems.Dist.PMF I.prob I.rv)

end HTechnique
end Migration
end NextGen
