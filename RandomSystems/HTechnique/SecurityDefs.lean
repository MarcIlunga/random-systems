/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.AdaptiveLawBridge
import RandomSystems.HTechnique.FixedQueryLaw
import RandomSystems.HTechnique.TranscriptLawPublic

/-!
# H-technique security definitions on the CR18 transcript surface

This module migrates the paper-facing advantage wrappers from the external
H-technique project to the CR18 transcript-law surface.

Source anchors:

* Lanzenberger thesis Def. 2.17 / Notation 2.19: a random system is represented
  by the equivalence class of PDS with the same transcript distributions, so
  `tr(S,e)` is notation for the transcript distribution of the system, not for
  the concrete representative.
* Lanzenberger thesis Def. 2.26: `Adv(S,T)` is the supremum, over compatible
  deterministic environments, of the statistical distance between
  `tr(S,e)` and `tr(T,e)`.

The migrated endpoint is this transcript-law `Adv` over law-level PDS objects,
plus the reusable bridge from the raw CR18 filtered distinguisher supremum
`Δ([q]S,[q]T)` into that transcript-law advantage. Representative-level
adapters remain available from support modules, but this security surface is
directly law-level.
-/

noncomputable section

open scoped RandomSystems.CR18

namespace RandomSystems
namespace HTechnique
namespace SecurityDefs

universe u v

variable {X : Type u} {Y : Type v} {q : Nat}

/-- **Source-theorem bridge.** Non-adaptive transcript advantage on the CR18
law-level surface: the supremum, over fixed query tuples, of the statistical
distance between the two fixed-query transcript laws.

This is the law-level version of the old H-technique `advN*` shape.  The
theorem-facing inputs are only the two PDS laws; fixed-query environments and
transcript distributions are constructed internally. -/
noncomputable def fixedQueryAdv
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) : ℝ :=
  sSup ((fun xs : Fin q → X =>
      (RandomSystems.statDist
        (ProbPDS.fixedQueryTranscriptDist S xs)
        (ProbPDS.fixedQueryTranscriptDist T xs) : ℝ)) ''
    Set.univ)

/-- **Source-theorem bridge.** A pointwise fixed-query transcript-distance
bound bounds the non-adaptive fixed-query advantage. -/
theorem fixedQueryAdv_le_of_pointwise
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y)
    (eps : NNReal)
    (h_pointwise : ∀ xs : Fin q → X,
        RandomSystems.statDist
          (ProbPDS.fixedQueryTranscriptDist S xs)
          (ProbPDS.fixedQueryTranscriptDist T xs) ≤ eps) :
    fixedQueryAdv (q := q) S T ≤ (eps : ℝ) := by
  unfold fixedQueryAdv
  exact RandomSystems.sSup_image_univ_le_of_forall _ (by positivity) (by
    intro xs
    exact_mod_cast h_pointwise xs)

/-- **Source-theorem bridge.** Thesis Def. 2.26 `Adv(S,T)` on the current CR18
transcript-law surface: the supremum, over compatible q-query-total
deterministic environments, of the statistical distance between the transcript
laws of the two law-level PDS objects.

The theorem-facing inputs are PDS laws; sample spaces, random variables, and
representative adapters do not leak into the public security definition.
The raw filtered CR18 distinguisher supremum is related to this object by
`filteredDelta_le_Adv` below. -/
noncomputable def Adv
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) : ℝ :=
  RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage (q := q) S T

/-- **Source-theorem bridge.** The fixed-query/non-adaptive transcript
advantage is bounded by thesis-style adaptive transcript `Adv`: each fixed
query tuple is the deterministic CR18 environment `fixedQueryDDE`. -/
theorem fixedQueryAdv_le_Adv
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y) :
    fixedQueryAdv (q := q) S T ≤ Adv (q := q) S T := by
  unfold fixedQueryAdv Adv
  refine RandomSystems.sSup_image_univ_le_sSup_image_univ_of_forall_exists _ _
    (RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage_image_bddAbove
      (q := q) S T) ?nonneg ?map
  · intro E
    exact RandomSystems.statDist_nonneg _ _
  · intro xs
    let E : QQueryEnvironment X Y q :=
      ⟨fixedQueryDDE (Y := Y) xs, by
        intro ys hlen
        refine ⟨xs ⟨ys.length, hlen⟩, ?_⟩
        simp [fixedQueryDDE, hlen]⟩
    refine ⟨E, ?_⟩
    simp [E, ProbPDS.fixedQueryTranscriptDist,
      RandomSystems.CR18.PFunPDS.Prob.fixedQueryTranscriptDist]

/-- **Source-theorem bridge.** A uniform pointwise transcript-distance bound for
every q-query-total deterministic environment bounds thesis-style `Adv(S,T)`. -/
theorem Adv_le_of_pointwise
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y)
    (eps : NNReal)
    (h_pointwise : ∀ E : QQueryEnvironment X Y q,
        RandomSystems.statDist
          (ProbPDS.deterministicTranscriptDist (q := q) S E.1)
          (ProbPDS.deterministicTranscriptDist (q := q) T E.1) ≤ eps) :
    Adv (q := q) S T ≤ (eps : ℝ) := by
  exact RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise
    S T eps h_pointwise

/-- **Source-theorem bridge.** The raw CR18 filtered distinguisher supremum is
bounded by thesis-style transcript-law `Adv` for the base PDS laws. The filtered
systems are constructed in the conclusion as Maurer's `[q]S` and `[q]T`; the
only extra premise is the existing CR18 finite-query normalization fact for the
base pair. -/
theorem filteredDelta_le_Adv
    [FiniteTranscriptSpace X Y q]
    (S T : ProbPDS X Y)
    (hS : S.KStepTotal q) (hT : T.KStepTotal q)
    (hNorm : RandomSystems.CR18.DeltaFilteredFiniteQueryNormalization q S.val T.val) :
    (Δ(⌈q⌉ S.val, ⌈q⌉ T.val) : ℝ) ≤ Adv (q := q) S T := by
  exact RandomSystems.CR18.maxAdvantage_filterQueries_le_adaptiveTranscriptAdvantage
    (q := q) S T hS hT hNorm

/-- **Source-theorem bridge.** Thesis-style adaptive PRF advantage for a CR18
law-level PDS: compare the construction with the ideal uniform random function,
and take the transcript-law supremum over q-query-total deterministic CR18
environments.

The only theorem-facing input is the construction PDS law `F`; the ideal URF law
is built in the statement. -/
noncomputable def advPRF
    [FiniteTranscriptSpace X Y q]
    [Fintype (X → Y)] [Nonempty (X → Y)]
    (F : ProbPDS X Y) : ℝ :=
  Adv (q := q) F (ProbPDS.urf (X := X) (Y := Y))

/-- **Source-theorem bridge.** PRF specialization of `Adv_le_of_pointwise`: a
uniform pointwise transcript-distance bound against the internally constructed
URF law bounds the paper-facing PRF advantage. -/
theorem advPRF_le_of_pointwise
    [FiniteTranscriptSpace X Y q]
    [Fintype (X → Y)] [Nonempty (X → Y)]
    (F : ProbPDS X Y)
    (eps : NNReal)
    (h_pointwise : ∀ E : QQueryEnvironment X Y q,
        RandomSystems.statDist
          (ProbPDS.deterministicTranscriptDist (q := q) F E.1)
          (ProbPDS.deterministicTranscriptDist (q := q)
            (ProbPDS.urf (X := X) (Y := Y)) E.1) ≤ eps) :
    advPRF (q := q) F ≤ (eps : ℝ) := by
  exact Adv_le_of_pointwise F (ProbPDS.urf (X := X) (Y := Y)) eps h_pointwise

/-- **Source-theorem bridge.** Thesis-style non-adaptive PRF advantage: compare
the construction with the internally constructed ideal URF over fixed-query
transcript laws. -/
noncomputable def advNPRF
    [FiniteTranscriptSpace X Y q]
    [Fintype (X → Y)] [Nonempty (X → Y)]
    (F : ProbPDS X Y) : ℝ :=
  fixedQueryAdv (q := q) F (ProbPDS.urf (X := X) (Y := Y))

/-- **Source-theorem bridge.** Non-adaptive PRF advantage is bounded by adaptive
PRF advantage because fixed-query environments are included among q-query-total
deterministic environments. -/
theorem advNPRF_le_advPRF
    [FiniteTranscriptSpace X Y q]
    [Fintype (X → Y)] [Nonempty (X → Y)]
    (F : ProbPDS X Y) :
    advNPRF (q := q) F ≤ advPRF (q := q) F := by
  exact fixedQueryAdv_le_Adv (q := q) F (ProbPDS.urf (X := X) (Y := Y))

/-- **Source-theorem bridge.** Thesis-style adaptive PRP advantage for a CR18
law-level PDS: compare the construction with the ideal uniform random
permutation, and take the transcript-law supremum over q-query-total
deterministic CR18 environments.

The only theorem-facing input is the construction PDS law `F`; the ideal URP
law is built in the statement. -/
noncomputable def advPRP
    [FiniteTranscriptSpace X X q]
    [Fintype X]
    (F : ProbPDS X X) : ℝ :=
  Adv (q := q) F (ProbPDS.urp (X := X))

/-- **Source-theorem bridge.** PRP specialization of `Adv_le_of_pointwise`: a
uniform pointwise transcript-distance bound against the internally constructed
URP law bounds the paper-facing PRP advantage. -/
theorem advPRP_le_of_pointwise
    [FiniteTranscriptSpace X X q]
    [Fintype X]
    (F : ProbPDS X X)
    (eps : NNReal)
    (h_pointwise : ∀ E : QQueryEnvironment X X q,
        RandomSystems.statDist
          (ProbPDS.deterministicTranscriptDist (q := q) F E.1)
          (ProbPDS.deterministicTranscriptDist (q := q)
            (ProbPDS.urp (X := X)) E.1) ≤ eps) :
    advPRP (q := q) F ≤ (eps : ℝ) := by
  exact Adv_le_of_pointwise F (ProbPDS.urp (X := X)) eps h_pointwise

/-- **Source-theorem bridge.** Thesis-style non-adaptive PRP advantage: compare
the construction with the internally constructed ideal URP over fixed-query
transcript laws. -/
noncomputable def advNPRP
    [FiniteTranscriptSpace X X q]
    [Fintype X]
    (F : ProbPDS X X) : ℝ :=
  fixedQueryAdv (q := q) F (ProbPDS.urp (X := X))

/-- **Source-theorem bridge.** Non-adaptive PRP advantage is bounded by adaptive
PRP advantage because fixed-query environments are included among q-query-total
deterministic environments. -/
theorem advNPRP_le_advPRP
    [FiniteTranscriptSpace X X q]
    [Fintype X]
    (F : ProbPDS X X) :
    advNPRP (q := q) F ≤ advPRP (q := q) F := by
  exact fixedQueryAdv_le_Adv (q := q) F (ProbPDS.urp (X := X))

end SecurityDefs
end HTechnique
end RandomSystems
