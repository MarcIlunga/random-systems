/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.FixedQueryLaw
import NextGen.Migration.HTechnique.SoP.VisibleLaw

/-!
# SoP fixed-input visible laws on CR18 transcript prefixes

This module connects the migrated fixed visible-output SoP law to the exact
`NextGen.PDS` CR18 transcript-prefix carrier
`PFunPDE.TranscriptPrefix X Y q = Vector X q × Vector Y q`.

Source status:

* source-theorem bridge: embed a fixed input tuple and a visible output tuple as
  the CR18 transcript prefix `(x^q, y^q)`;
* support lemma forced by formalization: lift any visible-output distribution
  to the transcript-prefix carrier by a common pushforward;
* source-theorem bridge: one-sided H-technique bounds proved on visible outputs
  transfer to the fixed-input CR18 transcript-prefix law.

The remaining SoP-specific layer is not an environment issue: it is to identify
the concrete real/ideal SoP system factors with the migrated visible-output
mass functions.  The generic fixed-query CR18 environment and transcript-law
reduction live in `NextGen.Migration.HTechnique.FixedQuery`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace NextGen
namespace Migration
namespace HTechnique
namespace SoP

variable {G : Type*} {q : Nat}

/-- **Source-theorem bridge.** Embed a fixed input tuple `xs` and a visible
output tuple `ys` as the CR18 transcript prefix `(x^q, y^q)`. -/
abbrev transcriptPrefixOfFixedInput (xs ys : Fin q → G) :
    TranscriptPrefix G G q :=
  fixedInputTranscriptPrefix xs ys

/-- **Support lemma forced by formalization; candidate for upstream.** Lift a
visible-output distribution to the fixed-input transcript-prefix carrier by the
exact embedding `ys ↦ (xs, ys)`. This is a deterministic pushforward, so it adds
no default value and no over-approximation. -/
abbrev liftVisibleDist [Fintype G] (xs : Fin q → G)
    (D : RandomSystems.Dist (Fin q → G)) :
    RandomSystems.Dist (TranscriptPrefix G G q) :=
  fixedInputLiftDist xs D

/-- **Source-theorem bridge.** The real fixed-input SoP visible law, lifted to
CR18 transcript prefixes. -/
abbrev liftedRealVisibleDist [AddGroup G] [Fintype G] (xs : Fin q → G) :
    RandomSystems.Dist (TranscriptPrefix G G q) :=
  liftVisibleDist xs (realVisibleDist (G := G) (q := q))

/-- **Source-theorem bridge.** The ideal fixed-input visible law, lifted to CR18
transcript prefixes. -/
abbrev liftedIdealVisibleDist [Fintype G] [Nonempty G] (xs : Fin q → G) :
    RandomSystems.Dist (TranscriptPrefix G G q) :=
  liftVisibleDist xs (idealVisibleDist (G := G) (q := q))

theorem liftedRealVisibleDist_weight [AddGroup G] [Fintype G]
    (xs : Fin q → G) (hq : q ≤ Fintype.card G) :
    (liftedRealVisibleDist (G := G) (q := q) xs).weight = 1 := by
  rw [liftedRealVisibleDist, fixedInputLiftDist_weight,
    realVisibleDist_weight (G := G) (q := q) hq]

theorem liftedIdealVisibleDist_weight [Fintype G] [Nonempty G]
    (xs : Fin q → G) :
    (liftedIdealVisibleDist (G := G) (q := q) xs).weight = 1 := by
  rw [liftedIdealVisibleDist, fixedInputLiftDist_weight,
    idealVisibleDist_weight (G := G) (q := q)]

/-- **Source-theorem bridge.** The lifted real and ideal fixed-input laws have
equal total mass. -/
theorem liftedVisibleDist_weight_eq_ideal [AddGroup G] [Fintype G] [Nonempty G]
    (xs : Fin q → G) (hq : q ≤ Fintype.card G) :
    (liftedRealVisibleDist (G := G) (q := q) xs).weight =
      (liftedIdealVisibleDist (G := G) (q := q) xs).weight := by
  rw [liftedRealVisibleDist_weight (G := G) (q := q) xs hq,
    liftedIdealVisibleDist_weight (G := G) (q := q) xs]

/-- **Source-theorem bridge.** A one-sided H-technique bound established for the
visible-output law transfers to the exact fixed-input CR18 transcript-prefix
law. -/
theorem liftedVisible_oneSided_hTechnique [AddGroup G] [Fintype G] [Nonempty G]
    (xs : Fin q → G) (eps : NNReal)
    (hq : q ≤ Fintype.card G)
    (h_lower : ∀ y,
      (1 - eps) * idealVisibleDist (G := G) (q := q) y ≤
        realVisibleDist (G := G) (q := q) y) :
    RandomSystems.statDist (liftedRealVisibleDist (G := G) (q := q) xs)
      (liftedIdealVisibleDist (G := G) (q := q) xs) ≤ eps := by
  classical
  refine RandomSystems.oneSided_hTechnique_fTransform
    (realVisibleDist (G := G) (q := q))
    (idealVisibleDist (G := G) (q := q))
    (transcriptPrefixOfFixedInput xs) eps ?_ ?_ h_lower
  · exact realVisibleDist_weight_eq_ideal (G := G) (q := q) hq
  · rw [idealVisibleDist_weight (G := G) (q := q)]

end SoP
end HTechnique
end Migration
end NextGen
