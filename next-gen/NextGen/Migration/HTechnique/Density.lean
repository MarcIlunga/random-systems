/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StatDist

/-!
# H-technique density lemmas

This module migrates the source-level, distribution-only H-technique facts from
`/Users/marcilunga/Documents/ToB/research/fv/h-technique`.

Source status:

* source theorem: Patarin/Jha-Nandi H-coefficient ratio bound;
* source theorem: expectation-method variant;
* source theorem: exact equality on good transcripts bounds distance by bad
  probability;
* source theorem: one-sided H-technique density ratio bound;
* support lemma forced by formalization: a pointwise one-sided ratio is
  preserved by a common pushforward.
* migration aliases for generic data-processing facts now owned by
  `RandomSystems.StatDist`.

Migration note: this module is compatibility-only.  New proofs should use
`RandomSystems.StatDist` directly for generic distribution-level H-technique
facts; transcript-law applications should use the law-level CR18 bridge modules.
-/

noncomputable section

open scoped BigOperators NNReal

namespace NextGen
namespace Migration
namespace HTechnique
namespace Density

/-- The mass of the bad event `B` under distribution `D`. -/
noncomputable def probBad {A : Type*}
    (D : RandomSystems.Dist A) (B : A → Prop) :
    NNReal :=
  RandomSystems.probBad D B

/-- **Extended H-technique**: if the real/ideal density ratio is at least
`1 - eps` on good points, then statistical distance is bounded by bad mass plus
`eps`. -/
theorem hTechnique_ratio {A : Type*} [Fintype A]
    (real ideal : RandomSystems.Dist A)
    (B : A → Prop)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist real ideal ≤ probBad ideal B + eps := by
  exact RandomSystems.hTechnique_ratio real ideal B eps h_weight h_ideal_le h_ratio

/-- Migration-facing alias for the generic `RandomSystems` data-processing
form of the ratio H-technique.  New proofs should prefer
`RandomSystems.hTechnique_ratio_fTransform` directly. -/
theorem hTechnique_ratio_fTransform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (real ideal : RandomSystems.Dist A) (f : A → B)
    (Bad : A → Prop)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ Bad a → (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist
        (RandomSystems.Dist.fTransform f real)
        (RandomSystems.Dist.fTransform f ideal) ≤
      probBad ideal Bad + eps := by
  exact RandomSystems.hTechnique_ratio_fTransform real ideal f Bad eps
    h_weight h_ideal_le h_ratio

/-- Migration-facing alias for terminal side-information removal by first
projection.  New proofs should prefer
`RandomSystems.hTechnique_ratio_project_fst` directly. -/
theorem hTechnique_ratio_project_fst {A Side : Type*}
    [Fintype A] [Fintype Side] [DecidableEq A]
    (realExt idealExt : RandomSystems.Dist (A × Side))
    (Bad : A × Side → Prop)
    (eps : NNReal)
    (h_weight : realExt.weight = idealExt.weight)
    (h_ideal_le : idealExt.weight ≤ 1)
    (h_ratio : ∀ a, ¬ Bad a → (1 - eps) * idealExt a ≤ realExt a) :
    RandomSystems.statDist
        (RandomSystems.Dist.fTransform (fun a : A × Side => a.1) realExt)
        (RandomSystems.Dist.fTransform (fun a : A × Side => a.1) idealExt) ≤
      probBad idealExt Bad + eps := by
  exact RandomSystems.hTechnique_ratio_project_fst realExt idealExt Bad eps
    h_weight h_ideal_le h_ratio

/-- **Expectation method**: the H-technique ratio bound with a point-dependent
error term. -/
theorem hTechnique_expectation {A : Type*} [Fintype A]
    (real ideal : RandomSystems.Dist A)
    (B : A → Prop) [DecidablePred B]
    (eps : A → NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ratio : ∀ a, ¬ B a → (1 - eps a) * ideal a ≤ real a) :
    RandomSystems.statDist real ideal ≤ probBad ideal B +
      ideal.sum (fun a w => if ¬ B a then w * eps a else 0) := by
  exact RandomSystems.hTechnique_expectation real ideal B eps h_weight h_ratio

/-- When real and ideal agree exactly on good points, statistical distance is
bounded by the ideal bad probability. -/
theorem hTechnique_eq_on_good {A : Type*} [Fintype A]
    (real ideal : RandomSystems.Dist A)
    (B : A → Prop)
    (h_weight : real.weight = ideal.weight)
    (h_eq : ∀ a, ¬ B a → real a = ideal a) :
    RandomSystems.statDist real ideal ≤ probBad ideal B := by
  exact RandomSystems.hTechnique_eq_on_good real ideal B h_weight h_eq

/-- **One-sided H-technique**: if `(1 - eps) * ideal(a) <= real(a)` for all
points, then `statDist real ideal <= eps`. -/
theorem oneSided_hTechnique {A : Type*} [Fintype A]
    (real ideal : RandomSystems.Dist A)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist real ideal ≤ eps := by
  exact RandomSystems.oneSided_hTechnique real ideal eps h_weight h_ideal_le h_lower

/-- **Support lemma forced by formalization; candidate for upstream.**
The one-sided H-technique is stable under a common deterministic
post-processing.  This is the generic CR18/thesis bridge used when a proof first
establishes a ratio on a compact visible carrier and then embeds it into a
transcript-prefix carrier. -/
theorem oneSided_hTechnique_fTransform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (real ideal : RandomSystems.Dist A) (f : A → B)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist (RandomSystems.Dist.fTransform f real)
      (RandomSystems.Dist.fTransform f ideal) ≤ eps := by
  exact RandomSystems.oneSided_hTechnique_fTransform real ideal f eps
    h_weight h_ideal_le h_lower

/-- One-sided H-technique with probability-distribution hypotheses. -/
theorem oneSided_hTechnique_proper {A : Type*} [Fintype A]
    (real ideal : RandomSystems.Dist A)
    (eps : NNReal)
    (h_real_proper : real.weight = 1)
    (h_ideal_proper : ideal.weight = 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    RandomSystems.statDist real ideal ≤ eps := by
  exact RandomSystems.oneSided_hTechnique_proper real ideal eps
    h_real_proper h_ideal_proper h_lower

end Density
end HTechnique
end Migration
end NextGen
