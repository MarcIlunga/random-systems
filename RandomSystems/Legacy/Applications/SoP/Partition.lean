/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.SoP.TV
import RandomSystems.Coupling

/-!
# SoP Partition Lemmas

This file starts the abstract partition layer used by the LM20/orbit proof.
The main theorem says that if two distributions have common conditionals on
classifier fibers, then their statistical distance is the statistical distance
between the classifier weights.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace SoP

variable {A Ω : Type*} [Fintype A] [Fintype Ω] [DecidableEq Ω]

/-- The fiber of a classifier label. -/
def classifierFiber (κ : A → Ω) (ω : Ω) : Finset A :=
  Finset.univ.filter (fun a : A => κ a = ω)

/-- The mass of one classifier fiber under a finite distribution. -/
def classifierWeight (X : Dist A) (κ : A → Ω) (ω : Ω) : Real :=
  ∑ a ∈ classifierFiber κ ω, X a

/-- The representative that samples a classifier label with the same block mass
as `X`, then samples uniformly inside the selected classifier fiber. -/
def classifierBlockUniform (X : Dist A) (κ : A → Ω) : Dist A :=
  Finsupp.equivFunOnFinite.invFun
    (fun a : A =>
      (Dist.fTransform κ X) (κ a) / ((classifierFiber κ (κ a)).card : Real))

omit [Fintype Ω] in
/-- Uniform conditional law on one classifier fiber, extended by zero outside
that fiber.  Empty fibers receive the zero function. -/
def classifierFiberUniform (κ : A → Ω) (ω : Ω) : A → Real :=
  fun a => if κ a = ω then 1 / ((classifierFiber κ ω).card : Real) else 0

omit [Fintype Ω] in
/-- Pointwise form of `classifierBlockUniform`. -/
theorem classifierBlockUniform_apply
    (X : Dist A) (κ : A → Ω) (a : A) :
    classifierBlockUniform X κ a =
      (Dist.fTransform κ X) (κ a) / ((classifierFiber κ (κ a)).card : Real) := by
  simp [classifierBlockUniform, Finsupp.equivFunOnFinite]

omit [Fintype Ω] in
/-- Block-uniformization preserves honesty. -/
theorem classifierBlockUniform_nonNeg
    {X : Dist A} (hX : X.NonNeg) (κ : A → Ω) :
    (classifierBlockUniform X κ).NonNeg := by
  intro a
  rw [classifierBlockUniform_apply]
  exact div_nonneg ((hX.fTransform κ) _) (by positivity)

omit [Fintype Ω] in
/-- Classifier fiber mass is the pointwise pushforward mass. -/
theorem classifierWeight_eq_fTransform
    (X : Dist A) (κ : A → Ω) (ω : Ω) :
    classifierWeight X κ ω = (Dist.fTransform κ X) ω := by
  rw [classifierWeight, classifierFiber, Dist.fTransform_apply_eq_sum]

omit [Fintype Ω] in
/-- On its own fiber, `classifierFiberUniform` is the reciprocal of the fiber
cardinality. -/
theorem classifierFiberUniform_apply_of_mem
    (κ : A → Ω) {ω : Ω} {a : A} (ha : a ∈ classifierFiber κ ω) :
    classifierFiberUniform κ ω a =
      1 / ((classifierFiber κ ω).card : Real) := by
  simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp [classifierFiberUniform, ha]

omit [Fintype Ω] in
/-- Off its fiber, `classifierFiberUniform` is zero. -/
theorem classifierFiberUniform_apply_of_not_mem
    (κ : A → Ω) {ω : Ω} {a : A} (ha : a ∉ classifierFiber κ ω) :
    classifierFiberUniform κ ω a = 0 := by
  simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha
  simp [classifierFiberUniform, ha]

omit [Fintype Ω] in
/-- The uniform conditional law on a nonempty classifier fiber has total mass
one. -/
theorem classifierFiberUniform_sum_of_nonempty
    (κ : A → Ω) {ω : Ω} (hω : (classifierFiber κ ω).Nonempty) :
    ∑ a ∈ classifierFiber κ ω, classifierFiberUniform κ ω a = 1 := by
  have hcard_ne : (((classifierFiber κ ω).card : Nat) : Real) ≠ 0 := by
    rcases hω with ⟨a, ha⟩
    have hcard_pos_nat : 0 < (classifierFiber κ ω).card :=
      Finset.card_pos.mpr ⟨a, ha⟩
    exact_mod_cast (Nat.ne_of_gt hcard_pos_nat)
  calc
    ∑ a ∈ classifierFiber κ ω, classifierFiberUniform κ ω a =
        ∑ _a ∈ classifierFiber κ ω,
          1 / ((classifierFiber κ ω).card : Real) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact classifierFiberUniform_apply_of_mem κ ha
    _ = ((classifierFiber κ ω).card : Real) *
        (1 / ((classifierFiber κ ω).card : Real)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
          field_simp [hcard_ne]

omit [Fintype Ω] in
/-- The fiber-uniform law has total mass one on nonempty fibers and zero on
empty fibers. -/
theorem classifierFiberUniform_sum_eq_indicator
    (κ : A → Ω) (ω : Ω) :
    ∑ a ∈ classifierFiber κ ω, classifierFiberUniform κ ω a =
      if (classifierFiber κ ω).Nonempty then 1 else 0 := by
  by_cases hω : (classifierFiber κ ω).Nonempty
  · simp [hω, classifierFiberUniform_sum_of_nonempty]
  · have hempty : classifierFiber κ ω = ∅ := Finset.not_nonempty_iff_eq_empty.mp hω
    simp [hempty]

omit [Fintype Ω] in
/-- Pointwise factorization of the block-uniform representative: sample a
classifier label with mass `(κ_*X)(κ a)`, then sample uniformly inside that
classifier fiber. -/
theorem classifierBlockUniform_factor_through_fiberUniform
    (X : Dist A) (κ : A → Ω) (a : A) :
    classifierBlockUniform X κ a =
      (Dist.fTransform κ X) (κ a) *
        classifierFiberUniform κ (κ a) a := by
  rw [classifierBlockUniform_apply]
  simp [classifierFiberUniform, div_eq_mul_inv, mul_comm]

omit [Fintype Ω] in
/-- If `X` is constant on classifier fibers, then it is exactly the
block-uniform representative obtained from its classifier masses. -/
theorem classifierBlockUniform_eq_of_constantFibers
    (X : Dist A) (κ : A → Ω)
    (hX : ∀ ⦃a b : A⦄, κ a = κ b → X a = X b) :
    classifierBlockUniform X κ = X := by
  ext a
  rw [classifierBlockUniform_apply]
  rw [← classifierWeight_eq_fTransform]
  unfold classifierWeight
  have hconst :
      ∀ b ∈ classifierFiber κ (κ a), X b = X a := by
    intro b hb
    simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact hX hb
  have hsum :
      ∑ b ∈ classifierFiber κ (κ a), X b =
        ((classifierFiber κ (κ a)).card : Real) * X a := by
    calc
      ∑ b ∈ classifierFiber κ (κ a), X b =
          ∑ _b ∈ classifierFiber κ (κ a), X a := by
            apply Finset.sum_congr rfl
            intro b hb
            exact hconst b hb
      _ = ((classifierFiber κ (κ a)).card : Real) * X a := by
            simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have ha_mem : a ∈ classifierFiber κ (κ a) := by
    simp [classifierFiber]
  have hcard_pos_nat : 0 < (classifierFiber κ (κ a)).card :=
    Finset.card_pos.mpr ⟨a, ha_mem⟩
  have hcard_ne : (((classifierFiber κ (κ a)).card : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcard_pos_nat)
  field_simp [hcard_ne]

omit [Fintype Ω] in
/-- `classifierBlockUniform` is constant on classifier fibers. -/
theorem classifierBlockUniform_constantOn_fibers
    (X : Dist A) (κ : A → Ω) :
    ∀ ⦃a b : A⦄, κ a = κ b →
      classifierBlockUniform X κ a = classifierBlockUniform X κ b := by
  intro a b hab
  rw [classifierBlockUniform_apply, classifierBlockUniform_apply, hab]

omit [Fintype Ω] in
/-- Every element lies in its own classifier fiber. -/
theorem mem_classifierFiber_self (κ : A → Ω) (a : A) :
    a ∈ classifierFiber κ (κ a) := by
  simp [classifierFiber]

omit [Fintype Ω] in
/-- A classifier fiber containing a named element has nonzero cardinality. -/
theorem classifierFiber_card_ne_zero_of_mem
    (κ : A → Ω) {ω : Ω} {a : A} (ha : a ∈ classifierFiber κ ω) :
    (((classifierFiber κ ω).card : Nat) : Real) ≠ 0 := by
  have hcard_pos_nat : 0 < (classifierFiber κ ω).card :=
    Finset.card_pos.mpr ⟨a, ha⟩
  exact_mod_cast (Nat.ne_of_gt hcard_pos_nat)

omit [Fintype Ω] in
/-- The block-uniform representative preserves classifier-label masses. -/
theorem classifierBlockUniform_fTransform
    (X : Dist A) (κ : A → Ω) :
    Dist.fTransform κ (classifierBlockUniform X κ) = Dist.fTransform κ X := by
  ext ω
  rw [Dist.fTransform_apply_eq_sum, Dist.fTransform_apply_eq_sum]
  have hNN :
      (∑ a ∈ classifierFiber κ ω, classifierBlockUniform X κ a) =
        ∑ a ∈ classifierFiber κ ω, X a := by
    by_cases hnonempty : (classifierFiber κ ω).Nonempty
    · calc
      ∑ a ∈ classifierFiber κ ω, classifierBlockUniform X κ a =
          ∑ _a ∈ classifierFiber κ ω,
            (Dist.fTransform κ X) ω / ((classifierFiber κ ω).card : Real) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [classifierBlockUniform_apply]
            simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha
            rw [ha]
      _ = ((classifierFiber κ ω).card : Real) *
            ((Dist.fTransform κ X) ω / ((classifierFiber κ ω).card : Real)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (Dist.fTransform κ X) ω := by
            have hcard_pos_nat : 0 < (classifierFiber κ ω).card :=
              Finset.card_pos.mpr hnonempty
            have hcard_ne : (((classifierFiber κ ω).card : Nat) : Real) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt hcard_pos_nat)
            field_simp [hcard_ne]
      _ = ∑ a ∈ classifierFiber κ ω, X a := by
            rw [← classifierWeight_eq_fTransform]
            rfl
    · have hempty : classifierFiber κ ω = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simp [hempty]
  exact hNN

omit [Fintype A] in
/-- On a finset where two real-valued functions are separately constant, the
positive-part difference commutes with summing over that finset. -/
private lemma sum_max_sub_eq_max_sum_sub_of_const_on_finset
    (S : Finset A) (f g : A → Real)
    (hf : ∀ ⦃a b : A⦄, a ∈ S → b ∈ S → f a = f b)
    (hg : ∀ ⦃a b : A⦄, a ∈ S → b ∈ S → g a = g b) :
    ∑ a ∈ S, max (f a - g a) 0 =
      max ((∑ a ∈ S, f a) - (∑ a ∈ S, g a)) 0 := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨a0, ha0⟩ := hS
    have hf0 : ∀ a ∈ S, f a = f a0 := by
      intro a ha
      exact hf ha ha0
    have hg0 : ∀ a ∈ S, g a = g a0 := by
      intro a ha
      exact hg ha ha0
    have hsumf : ∑ a ∈ S, f a = (S.card : Real) * f a0 := by
      calc
        ∑ a ∈ S, f a = ∑ _a ∈ S, f a0 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hf0 a ha
        _ = (S.card : Real) * f a0 := by
          simp [Finset.sum_const, nsmul_eq_mul]
    have hsumg : ∑ a ∈ S, g a = (S.card : Real) * g a0 := by
      calc
        ∑ a ∈ S, g a = ∑ _a ∈ S, g a0 := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hg0 a ha
        _ = (S.card : Real) * g a0 := by
          simp [Finset.sum_const, nsmul_eq_mul]
    calc
      ∑ a ∈ S, max (f a - g a) 0 =
          ∑ a ∈ S, max (f a0 - g a0) 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hf0 a ha, hg0 a ha]
      _ = (S.card : Real) * max (f a0 - g a0) 0 := by
        simp [Finset.sum_const]
      _ = max ((S.card : Real) * (f a0 - g a0)) 0 := by
        rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
      _ = max ((∑ a ∈ S, f a) - (∑ a ∈ S, g a)) 0 := by
        rw [hsumf, hsumg]
        congr 1
        ring
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty]

/--
If two finite distributions factor through the same conditional distribution on
each classifier fiber, then their `statDist` is the positive-part distance
between the classifier weights.

The normalization hypothesis is intentionally stated on every fiber.  In the
orbit application, `Ω` should be the type of nonempty blocks/orbits, so this is
the natural shape.
-/
theorem statDist_eq_sum_classifierWeights_of_commonConditionals
    (X Y : Dist A) (κ : A → Ω) (wX wY : Ω → Real) (D : Ω → A → NNReal)
    (hX : ∀ a : A, X a = wX (κ a) * D (κ a) a)
    (hY : ∀ a : A, Y a = wY (κ a) * D (κ a) a)
    (hD : ∀ ω : Ω, ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω), D ω a = 1) :
    statDist X Y = ∑ ω : Ω, max (wX ω - wY ω) 0 := by
  -- the signed carrier indexes `statDist` by `(X - Y).support`, not `univ`
  simp only [statDist_eq_sum_univ]
  rw [← Finset.sum_fiberwise Finset.univ κ
    (fun a => max (X a - Y a) 0)]
  apply Finset.sum_congr rfl
  intro ω _
  calc
    ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω), max (X a - Y a) 0
        = ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω),
            max (wX ω * D ω a - wY ω * D ω a) 0 := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
          simp [hX a, hY a, ha]
    _ = ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω),
            (max (wX ω - wY ω) 0 * D ω a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [← sub_mul]
          simpa using
            (max_mul_of_nonneg (wX ω - wY ω) 0
              (show 0 ≤ (D ω a : Real) by positivity)).symm
    _ = max (wX ω - wY ω) 0 *
          ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω), (D ω a : Real) := by
          rw [Finset.mul_sum]
    _ = max (wX ω - wY ω) 0 := by
          have hDreal :
              ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω), (D ω a : Real) = 1 := by
            exact_mod_cast hD ω
          rw [hDreal, mul_one]

/--
Pushforward form of `statDist_eq_sum_classifierWeights_of_commonConditionals`.
Here the classifier weights are the actual masses induced by `κ`.
-/
theorem statDist_eq_classifierStatDist_of_commonConditionals
    (X Y : Dist A) (κ : A → Ω) (D : Ω → A → NNReal)
    (hX : ∀ a : A, X a = (Dist.fTransform κ X) (κ a) * D (κ a) a)
    (hY : ∀ a : A, Y a = (Dist.fTransform κ Y) (κ a) * D (κ a) a)
    (hD : ∀ ω : Ω, ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω), D ω a = 1) :
    statDist X Y = statDist (Dist.fTransform κ X) (Dist.fTransform κ Y) := by
  rw [statDist_eq_sum_classifierWeights_of_commonConditionals
    (X := X) (Y := Y) (κ := κ)
    (wX := fun ω => (Dist.fTransform κ X) ω)
    (wY := fun ω => (Dist.fTransform κ Y) ω)
    (D := D) hX hY hD]
  simp [statDist_eq_sum_univ]

/--
Coupling form of `statDist_eq_classifierStatDist_of_commonConditionals`.

If two distributions share the same conditional law inside each classifier
fiber, then an optimal coupling of the classifier masses already achieves the
full statistical distance of the original distributions.  This is the abstract
LM20 block-coupling statement: first couple labels, and no additional
distinguishing mass remains inside a matched label.
-/
theorem exists_classifierMassCoupling_of_commonConditionals
    (X Y : Dist A) (κ : A → Ω) (D : Ω → A → NNReal)
    (hXnn : X.NonNeg) (hYnn : Y.NonNeg)
    (hX : ∀ a : A, X a = (Dist.fTransform κ X) (κ a) * D (κ a) a)
    (hY : ∀ a : A, Y a = (Dist.fTransform κ Y) (κ a) * D (κ a) a)
    (hD : ∀ ω : Ω, ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω), D ω a = 1)
    (hw : X.weight = Y.weight) :
    ∃ C : DistCoupling (Dist.fTransform κ X) (Dist.fTransform κ Y),
      statDist X Y = C.prDisagree := by
  have hweights :
      (Dist.fTransform κ X).weight = (Dist.fTransform κ Y).weight := by
    rw [Dist.weight_fTransform, Dist.weight_fTransform, hw]
  obtain ⟨C, hC⟩ := optimal_coupling_exists
    (hXnn.fTransform κ) (hYnn.fTransform κ) hweights
  refine ⟨C, ?_⟩
  rw [statDist_eq_classifierStatDist_of_commonConditionals
    (X := X) (Y := Y) (κ := κ) (D := D) hX hY hD]
  exact hC

/--
If both distributions are constant on classifier fibers, then the statistical
distance is exactly the statistical distance between the classifier
pushforwards.

This is the abstract finite-partition statement needed by the orbit proof: once
a classifier has fibers equal to the chosen orbit blocks, and both laws are
constant on those blocks, no transcript-level distinguishing mass remains
inside a block.
-/
theorem statDist_eq_classifierStatDist_of_constantFibers
    (X Y : Dist A) (κ : A → Ω)
    (hX : ∀ ⦃a b : A⦄, κ a = κ b → X a = X b)
    (hY : ∀ ⦃a b : A⦄, κ a = κ b → Y a = Y b) :
    statDist X Y = statDist (Dist.fTransform κ X) (Dist.fTransform κ Y) := by
  -- the signed carrier indexes `statDist` by `(X - Y).support`, not `univ`
  simp only [statDist_eq_sum_univ]
  rw [← Finset.sum_fiberwise Finset.univ κ
    (fun a => max (X a - Y a) 0)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Dist.fTransform_apply_eq_sum, Dist.fTransform_apply_eq_sum]
  exact sum_max_sub_eq_max_sum_sub_of_const_on_finset
    (Finset.univ.filter (fun a : A => κ a = ω)) X Y
    (by
      intro a b ha hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hX (ha.trans hb.symm))
    (by
      intro a b ha hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hY (ha.trans hb.symm))

/--
Coupling form of `statDist_eq_classifierStatDist_of_constantFibers`.

If both distributions are constant on classifier fibers, then an optimal
coupling of the pushed-forward classifier masses has failure probability equal
to the original statistical distance.
-/
theorem exists_classifierMassCoupling_of_constantFibers
    (X Y : Dist A) (κ : A → Ω)
    (hXnn : X.NonNeg) (hYnn : Y.NonNeg)
    (hX : ∀ ⦃a b : A⦄, κ a = κ b → X a = X b)
    (hY : ∀ ⦃a b : A⦄, κ a = κ b → Y a = Y b)
    (hw : X.weight = Y.weight) :
    ∃ C : DistCoupling (Dist.fTransform κ X) (Dist.fTransform κ Y),
      statDist X Y = C.prDisagree := by
  have hweights :
      (Dist.fTransform κ X).weight = (Dist.fTransform κ Y).weight := by
    rw [Dist.weight_fTransform, Dist.weight_fTransform, hw]
  obtain ⟨C, hC⟩ := optimal_coupling_exists
    (hXnn.fTransform κ) (hYnn.fTransform κ) hweights
  refine ⟨C, ?_⟩
  rw [statDist_eq_classifierStatDist_of_constantFibers (X := X) (Y := Y) (κ := κ) hX hY]
  exact hC

/-- The distance between block-uniform representatives is exactly the distance
between their classifier-label masses.  This is the direct equality behind the
LM20 block-coupling story: after conditioning on a matched block label, the
within-block conditional laws are identical. -/
theorem statDist_classifierBlockUniform_eq_classifierStatDist
    (X Y : Dist A) (κ : A → Ω) :
    statDist (classifierBlockUniform X κ) (classifierBlockUniform Y κ) =
      statDist
        (Dist.fTransform κ (classifierBlockUniform X κ))
        (Dist.fTransform κ (classifierBlockUniform Y κ)) := by
  exact statDist_eq_classifierStatDist_of_constantFibers
    (X := classifierBlockUniform X κ)
    (Y := classifierBlockUniform Y κ)
    (κ := κ)
    (classifierBlockUniform_constantOn_fibers X κ)
    (classifierBlockUniform_constantOn_fibers Y κ)

/-- Block-uniform representatives are separated exactly by the original
classifier-label masses. -/
theorem statDist_classifierBlockUniform_eq_originalClassifierStatDist
    (X Y : Dist A) (κ : A → Ω) :
    statDist (classifierBlockUniform X κ) (classifierBlockUniform Y κ) =
      statDist (Dist.fTransform κ X) (Dist.fTransform κ Y) := by
  rw [statDist_classifierBlockUniform_eq_classifierStatDist]
  rw [classifierBlockUniform_fTransform, classifierBlockUniform_fTransform]

/-- Block-uniform representatives have an optimal classifier-label coupling:
because both representatives are uniform inside each classifier block, all
distinguishing mass is already present at the classifier-label level.

This is the generic formal version of "couple block labels first; if labels
match, couple perfectly inside the block." -/
theorem exists_classifierMassCoupling_of_blockUniform
    (X Y : Dist A) (κ : A → Ω)
    (hXnn : X.NonNeg) (hYnn : Y.NonNeg)
    (hw : (classifierBlockUniform X κ).weight =
      (classifierBlockUniform Y κ).weight) :
    ∃ C : DistCoupling
        (Dist.fTransform κ (classifierBlockUniform X κ))
        (Dist.fTransform κ (classifierBlockUniform Y κ)),
      statDist (classifierBlockUniform X κ) (classifierBlockUniform Y κ) =
        C.prDisagree := by
  exact exists_classifierMassCoupling_of_constantFibers
    (X := classifierBlockUniform X κ)
    (Y := classifierBlockUniform Y κ)
    (κ := κ)
    (classifierBlockUniform_nonNeg hXnn κ)
    (classifierBlockUniform_nonNeg hYnn κ)
    (classifierBlockUniform_constantOn_fibers X κ)
    (classifierBlockUniform_constantOn_fibers Y κ)
    hw

private theorem fTransform_fst_pair_apply
    {B : Type*} [Fintype B] [DecidableEq A]
    (D : Dist (A × B)) (a : A) :
    (Dist.fTransform Prod.fst D) a = ∑ b : B, D (a, b) := by
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  trans (∑ p ∈ (Finset.univ : Finset (A × B)), if p.1 = a then D p else 0)
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp
  · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    conv_rhs =>
      rw [show (∑ b : B, D (a, b)) =
          ∑ p ∈ (Finset.univ : Finset B).map
              ⟨fun b => (a, b), fun b₁ b₂ h => by simpa using h⟩,
            D p from by rw [Finset.sum_map]; simp]
    congr 1
    ext ⟨x, y⟩
    simp [eq_comm]

private theorem fTransform_snd_pair_apply
    {B : Type*} [Fintype B] [DecidableEq A]
    (D : Dist (B × A)) (a : A) :
    (Dist.fTransform Prod.snd D) a = ∑ b : B, D (b, a) := by
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  trans (∑ p ∈ (Finset.univ : Finset (B × A)), if p.2 = a then D p else 0)
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    rw [Finsupp.notMem_support_iff.mp hp]
    simp
  · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    conv_rhs =>
      rw [show (∑ b : B, D (b, a)) =
          ∑ p ∈ (Finset.univ : Finset B).map
              ⟨fun b => (b, a), fun b₁ b₂ h => by simpa using h⟩,
            D p from by rw [Finset.sum_map]; simp]
    congr 1
    ext ⟨x, y⟩
    simp [eq_comm]

/-- Explicit label-first lift of a classifier-label coupling to pairs of
block-uniform representative samples.

The intended sampling procedure is:

* sample a pair of classifier labels from `C`;
* if the labels match, sample one element uniformly from the common fiber and
  return it on both sides;
* if the labels differ, sample independently and uniformly in the two fibers.

The later coupling theorems establish the marginals and failure probability of
this joint. -/
def labelFirstBlockCouplingJoint
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ))) :
    Dist (A × A) :=
  Finsupp.equivFunOnFinite.invFun
    (fun p : A × A =>
      if p.1 = p.2 then
        C.joint (κ p.1, κ p.2) / ((classifierFiber κ (κ p.1)).card : Real)
      else if κ p.1 = κ p.2 then
        0
      else
        C.joint (κ p.1, κ p.2) /
          (((classifierFiber κ (κ p.1)).card : Real) *
            ((classifierFiber κ (κ p.2)).card : Real)))

omit [Fintype Ω] in
theorem labelFirstBlockCouplingJoint_apply
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    (a b : A) :
    labelFirstBlockCouplingJoint X Y κ C (a, b) =
      if a = b then
        C.joint (κ a, κ b) / ((classifierFiber κ (κ a)).card : Real)
      else if κ a = κ b then
        0
      else
        C.joint (κ a, κ b) /
          (((classifierFiber κ (κ a)).card : Real) *
            ((classifierFiber κ (κ b)).card : Real)) := by
  simp [labelFirstBlockCouplingJoint, Finsupp.equivFunOnFinite]

omit [Fintype Ω] in
/-- The explicit label-first lift is an honest joint distribution. -/
theorem labelFirstBlockCouplingJoint_nonNeg
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ))) :
    (labelFirstBlockCouplingJoint X Y κ C).NonNeg := by
  rintro ⟨a, b⟩
  rw [labelFirstBlockCouplingJoint_apply]
  split_ifs
  · exact div_nonneg (C.nonneg _) (by positivity)
  · exact le_rfl
  · exact div_nonneg (C.nonneg _) (by positivity)

omit [Fintype Ω] in
/-- In the explicit label-first lift, matched labels are coupled perfectly:
there is no mass on different elements inside the same classifier fiber. -/
theorem labelFirstBlockCouplingJoint_eq_zero_of_same_label_ne
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    {a b : A} (hne : a ≠ b) (hκ : κ a = κ b) :
    labelFirstBlockCouplingJoint X Y κ C (a, b) = 0 := by
  rw [labelFirstBlockCouplingJoint_apply]
  simp [hne, hκ]

omit [Fintype Ω] in
/-- For fixed left sample `a`, the same-label part of the explicit
label-first lift is exactly the diagonal label-coupling mass spread uniformly
over the fiber. -/
theorem sum_labelFirstBlockCouplingJoint_same_label_right
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    (a : A) :
    ∑ b ∈ classifierFiber κ (κ a),
      labelFirstBlockCouplingJoint X Y κ C (a, b) =
        C.joint (κ a, κ a) / ((classifierFiber κ (κ a)).card : Real) := by
  rw [Finset.sum_eq_single a]
  · rw [labelFirstBlockCouplingJoint_apply]
    simp
  · intro b hb hba
    exact labelFirstBlockCouplingJoint_eq_zero_of_same_label_ne
      (X := X) (Y := Y) (κ := κ) C (Ne.symm hba)
      (by
        simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hb
        exact hb.symm)
  · intro ha
    exact False.elim (ha (mem_classifierFiber_self κ a))

omit [Fintype Ω] in
/-- Symmetric version of `sum_labelFirstBlockCouplingJoint_same_label_right`
for a fixed right sample. -/
theorem sum_labelFirstBlockCouplingJoint_same_label_left
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    (b : A) :
    ∑ a ∈ classifierFiber κ (κ b),
      labelFirstBlockCouplingJoint X Y κ C (a, b) =
        C.joint (κ b, κ b) / ((classifierFiber κ (κ b)).card : Real) := by
  rw [Finset.sum_eq_single b]
  · rw [labelFirstBlockCouplingJoint_apply]
    simp
  · intro a ha hab
    exact labelFirstBlockCouplingJoint_eq_zero_of_same_label_ne
      (X := X) (Y := Y) (κ := κ) C hab
      (by
        simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ha)
  · intro hb
    exact False.elim (hb (mem_classifierFiber_self κ b))

/-- A classifier-label coupling cannot put mass on a left label whose
underlying classifier fiber is empty. -/
theorem classifierMassCoupling_joint_eq_zero_of_left_empty
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    {ω ν : Ω} (hempty : classifierFiber κ ω = ∅) :
    C.joint (ω, ν) = 0 := by
  have hleftZero : (Dist.fTransform Prod.fst C.joint) ω = 0 := by
    rw [C.marginal_fst, classifierBlockUniform_fTransform,
      Dist.fTransform_apply_eq_sum]
    have hfilter : (Finset.univ.filter (fun a : A => κ a = ω)) = ∅ := by
      simpa [classifierFiber] using hempty
    simp [hfilter]
  rw [Dist.fTransform_apply_eq_sum] at hleftZero
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun p _ => C.nonneg p)).mp hleftZero (ω, ν) (by simp)

/-- A classifier-label coupling cannot put mass on a right label whose
underlying classifier fiber is empty. -/
theorem classifierMassCoupling_joint_eq_zero_of_right_empty
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    {ω ν : Ω} (hempty : classifierFiber κ ν = ∅) :
    C.joint (ω, ν) = 0 := by
  have hrightZero : (Dist.fTransform Prod.snd C.joint) ν = 0 := by
    rw [C.marginal_snd, classifierBlockUniform_fTransform,
      Dist.fTransform_apply_eq_sum]
    have hfilter : (Finset.univ.filter (fun a : A => κ a = ν)) = ∅ := by
      simpa [classifierFiber] using hempty
    simp [hfilter]
  rw [Dist.fTransform_apply_eq_sum] at hrightZero
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun p _ => C.nonneg p)).mp hrightZero (ω, ν) (by simp)

/-- For fixed left sample `a`, summing the explicit label-first lift over one
right classifier fiber gives the corresponding label-coupling mass divided by
the size of `a`'s own fiber. -/
theorem sum_labelFirstBlockCouplingJoint_right_fiber
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    (a : A) (ν : Ω) :
    ∑ b ∈ classifierFiber κ ν,
      labelFirstBlockCouplingJoint X Y κ C (a, b) =
        C.joint (κ a, ν) / ((classifierFiber κ (κ a)).card : Real) := by
  by_cases hν : ν = κ a
  · subst hν
    exact sum_labelFirstBlockCouplingJoint_same_label_right X Y κ C a
  · by_cases hnonempty : (classifierFiber κ ν).Nonempty
    · have hcard_a_ne :
        (((classifierFiber κ (κ a)).card : Nat) : Real) ≠ 0 :=
          classifierFiber_card_ne_zero_of_mem κ (mem_classifierFiber_self κ a)
      have hcard_ν_ne :
        (((classifierFiber κ ν).card : Nat) : Real) ≠ 0 := by
          rcases hnonempty with ⟨b, hb⟩
          exact classifierFiber_card_ne_zero_of_mem κ hb
      calc
        ∑ b ∈ classifierFiber κ ν,
            labelFirstBlockCouplingJoint X Y κ C (a, b) =
            ∑ _b ∈ classifierFiber κ ν,
              C.joint (κ a, ν) /
                (((classifierFiber κ (κ a)).card : Real) *
                  ((classifierFiber κ ν).card : Real)) := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [labelFirstBlockCouplingJoint_apply]
              have hbκ : κ b = ν := by
                simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hb
                exact hb
              have hab : a ≠ b := by
                intro hab
                apply hν
                rw [← hbκ, hab]
              have hκne : κ a ≠ κ b := by
                intro h
                apply hν
                rw [← hbκ, h]
              have hκaν : κ a ≠ ν := by
                intro h
                exact hν h.symm
              simp [hab, hκaν, hbκ]
        _ = ((classifierFiber κ ν).card : Real) *
              (C.joint (κ a, ν) /
                (((classifierFiber κ (κ a)).card : Real) *
                  ((classifierFiber κ ν).card : Real))) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ = C.joint (κ a, ν) /
              ((classifierFiber κ (κ a)).card : Real) := by
              field_simp [hcard_a_ne, hcard_ν_ne]
    · have hempty : classifierFiber κ ν = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      have hjoint : C.joint (κ a, ν) = 0 :=
        classifierMassCoupling_joint_eq_zero_of_right_empty
          (X := X) (Y := Y) (κ := κ) C hempty
      simp [hempty, hjoint]

/-- Symmetric version of `sum_labelFirstBlockCouplingJoint_right_fiber` for
fixed right sample `b`. -/
theorem sum_labelFirstBlockCouplingJoint_left_fiber
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    (ω : Ω) (b : A) :
    ∑ a ∈ classifierFiber κ ω,
      labelFirstBlockCouplingJoint X Y κ C (a, b) =
        C.joint (ω, κ b) / ((classifierFiber κ (κ b)).card : Real) := by
  by_cases hω : ω = κ b
  · subst hω
    exact sum_labelFirstBlockCouplingJoint_same_label_left X Y κ C b
  · by_cases hnonempty : (classifierFiber κ ω).Nonempty
    · have hcard_b_ne :
        (((classifierFiber κ (κ b)).card : Nat) : Real) ≠ 0 :=
          classifierFiber_card_ne_zero_of_mem κ (mem_classifierFiber_self κ b)
      have hcard_ω_ne :
        (((classifierFiber κ ω).card : Nat) : Real) ≠ 0 := by
          rcases hnonempty with ⟨a, ha⟩
          exact classifierFiber_card_ne_zero_of_mem κ ha
      calc
        ∑ a ∈ classifierFiber κ ω,
            labelFirstBlockCouplingJoint X Y κ C (a, b) =
            ∑ _a ∈ classifierFiber κ ω,
              C.joint (ω, κ b) /
                (((classifierFiber κ ω).card : Real) *
                  ((classifierFiber κ (κ b)).card : Real)) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [labelFirstBlockCouplingJoint_apply]
              have haκ : κ a = ω := by
                simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha
                exact ha
              have hab : a ≠ b := by
                intro hab
                apply hω
                rw [← haκ, hab]
              have hκne : κ a ≠ κ b := by
                intro h
                apply hω
                rw [← haκ, h]
              simp [hab, haκ, hω]
        _ = ((classifierFiber κ ω).card : Real) *
              (C.joint (ω, κ b) /
                (((classifierFiber κ ω).card : Real) *
                  ((classifierFiber κ (κ b)).card : Real))) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ = C.joint (ω, κ b) /
              ((classifierFiber κ (κ b)).card : Real) := by
              field_simp [hcard_b_ne, hcard_ω_ne]
    · have hempty : classifierFiber κ ω = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      have hjoint : C.joint (ω, κ b) = 0 :=
        classifierMassCoupling_joint_eq_zero_of_left_empty
          (X := X) (Y := Y) (κ := κ) C hempty
      simp [hempty, hjoint]

/-- The explicit label-first lifted joint has the real block-uniform
representative as its first marginal. -/
theorem labelFirstBlockCouplingJoint_marginal_fst
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ))) :
    Dist.fTransform Prod.fst (labelFirstBlockCouplingJoint X Y κ C) =
      classifierBlockUniform X κ := by
  ext a
  rw [fTransform_fst_pair_apply]
  rw [← Finset.sum_fiberwise Finset.univ κ
    (fun b => labelFirstBlockCouplingJoint X Y κ C (a, b))]
  have hNN :
      (∑ ν : Ω, ∑ b ∈ Finset.univ.filter (fun b : A => κ b = ν),
        labelFirstBlockCouplingJoint X Y κ C (a, b)) =
        classifierBlockUniform X κ a := by
    calc
    ∑ ν : Ω, ∑ b ∈ Finset.univ.filter (fun b : A => κ b = ν),
        labelFirstBlockCouplingJoint X Y κ C (a, b) =
        ∑ ν : Ω,
          C.joint (κ a, ν) / ((classifierFiber κ (κ a)).card : Real) := by
          apply Finset.sum_congr rfl
          intro ν _
          exact sum_labelFirstBlockCouplingJoint_right_fiber X Y κ C a ν
    _ = (∑ ν : Ω, C.joint (κ a, ν)) /
        ((classifierFiber κ (κ a)).card : Real) := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    _ = (Dist.fTransform Prod.fst C.joint) (κ a) /
        ((classifierFiber κ (κ a)).card : Real) := by
          rw [fTransform_fst_pair_apply]
    _ = (Dist.fTransform κ (classifierBlockUniform X κ)) (κ a) /
        ((classifierFiber κ (κ a)).card : Real) := by
          rw [C.marginal_fst]
    _ = classifierBlockUniform X κ a := by
          rw [classifierBlockUniform_apply, classifierBlockUniform_fTransform]
  exact hNN

/-- The explicit label-first lifted joint has the ideal block-uniform
representative as its second marginal. -/
theorem labelFirstBlockCouplingJoint_marginal_snd
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ))) :
    Dist.fTransform Prod.snd (labelFirstBlockCouplingJoint X Y κ C) =
      classifierBlockUniform Y κ := by
  ext b
  rw [fTransform_snd_pair_apply]
  rw [← Finset.sum_fiberwise Finset.univ κ
    (fun a => labelFirstBlockCouplingJoint X Y κ C (a, b))]
  have hNN :
      (∑ ω : Ω, ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω),
        labelFirstBlockCouplingJoint X Y κ C (a, b)) =
        classifierBlockUniform Y κ b := by
    calc
    ∑ ω : Ω, ∑ a ∈ Finset.univ.filter (fun a : A => κ a = ω),
        labelFirstBlockCouplingJoint X Y κ C (a, b) =
        ∑ ω : Ω,
          C.joint (ω, κ b) / ((classifierFiber κ (κ b)).card : Real) := by
          apply Finset.sum_congr rfl
          intro ω _
          exact sum_labelFirstBlockCouplingJoint_left_fiber X Y κ C ω b
    _ = (∑ ω : Ω, C.joint (ω, κ b)) /
        ((classifierFiber κ (κ b)).card : Real) := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    _ = (Dist.fTransform Prod.snd C.joint) (κ b) /
        ((classifierFiber κ (κ b)).card : Real) := by
          rw [fTransform_snd_pair_apply]
    _ = (Dist.fTransform κ (classifierBlockUniform Y κ)) (κ b) /
        ((classifierFiber κ (κ b)).card : Real) := by
          rw [C.marginal_snd]
    _ = classifierBlockUniform Y κ b := by
          rw [classifierBlockUniform_apply, classifierBlockUniform_fTransform]
  exact hNN

/-- The explicit label-first lift packaged as a coupling of the block-uniform
representatives. -/
def labelFirstBlockCoupling
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ))) :
    DistCoupling (classifierBlockUniform X κ) (classifierBlockUniform Y κ) where
  joint := labelFirstBlockCouplingJoint X Y κ C
  nonneg := labelFirstBlockCouplingJoint_nonNeg X Y κ C
  marginal_fst := labelFirstBlockCouplingJoint_marginal_fst X Y κ C
  marginal_snd := labelFirstBlockCouplingJoint_marginal_snd X Y κ C

omit [Fintype Ω] in
private theorem fTransform_pair_classifier_apply
    [DecidableEq A]
    (D : Dist (A × A)) (κ : A → Ω) (ω ν : Ω) :
    (Dist.fTransform (fun p : A × A => (κ p.1, κ p.2)) D) (ω, ν) =
      ∑ a ∈ classifierFiber κ ω, ∑ b ∈ classifierFiber κ ν, D (a, b) := by
  rw [Dist.fTransform_apply_eq_sum]
  have hfilter :
      (Finset.univ.filter
          (fun p : A × A => (κ p.1, κ p.2) = (ω, ν))) =
        (classifierFiber κ ω).product (classifierFiber κ ν) := by
    ext p
    rcases p with ⟨a, b⟩
    simp [classifierFiber]
  rw [hfilter]
  exact Finset.sum_product (s := classifierFiber κ ω)
    (t := classifierFiber κ ν) (f := fun p : A × A => D p)

/-- Summing the explicit label-first lift over one pair of classifier fibers
recovers exactly the corresponding label-coupling mass. -/
theorem sum_labelFirstBlockCouplingJoint_fibers
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)))
    (ω ν : Ω) :
    ∑ a ∈ classifierFiber κ ω, ∑ b ∈ classifierFiber κ ν,
      labelFirstBlockCouplingJoint X Y κ C (a, b) =
        C.joint (ω, ν) := by
  by_cases hnonempty : (classifierFiber κ ω).Nonempty
  · have hcard_ω_ne :
      (((classifierFiber κ ω).card : Nat) : Real) ≠ 0 := by
        rcases hnonempty with ⟨a, ha⟩
        exact classifierFiber_card_ne_zero_of_mem κ ha
    calc
      ∑ a ∈ classifierFiber κ ω, ∑ b ∈ classifierFiber κ ν,
          labelFirstBlockCouplingJoint X Y κ C (a, b) =
          ∑ _a ∈ classifierFiber κ ω,
            C.joint (ω, ν) / ((classifierFiber κ ω).card : Real) := by
            apply Finset.sum_congr rfl
            intro a ha
            have haκ : κ a = ω := by
              simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha
              exact ha
            rw [sum_labelFirstBlockCouplingJoint_right_fiber X Y κ C a ν, haκ]
      _ = ((classifierFiber κ ω).card : Real) *
            (C.joint (ω, ν) / ((classifierFiber κ ω).card : Real)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = C.joint (ω, ν) := by
            field_simp [hcard_ω_ne]
  · have hempty : classifierFiber κ ω = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hjoint : C.joint (ω, ν) = 0 :=
      classifierMassCoupling_joint_eq_zero_of_left_empty
        (X := X) (Y := Y) (κ := κ) C hempty
    simp [hempty, hjoint]

/-- Pushing the explicit label-first lifted joint through the pair of classifier
labels returns the original classifier-label coupling. -/
theorem labelFirstBlockCouplingJoint_fTransform_labels
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ))) :
    Dist.fTransform (fun p : A × A => (κ p.1, κ p.2))
        (labelFirstBlockCouplingJoint X Y κ C) = C.joint := by
  ext p
  rcases p with ⟨ω, ν⟩
  rw [fTransform_pair_classifier_apply]
  exact_mod_cast sum_labelFirstBlockCouplingJoint_fibers X Y κ C ω ν

private theorem sum_fTransform_pair_classifier_offdiag
    [DecidableEq A]
    (D : Dist (A × A)) (κ : A → Ω) :
    ∑ r ∈ (Finset.univ : Finset (Ω × Ω)).filter (fun r => r.1 ≠ r.2),
        (Dist.fTransform (fun p : A × A => (κ p.1, κ p.2)) D) r =
      ∑ p ∈ (Finset.univ : Finset (A × A)).filter
          (fun p => κ p.1 ≠ κ p.2), D p := by
  simp only [Finset.sum_filter]
  rw [← Finset.sum_fiberwise Finset.univ
    (fun p : A × A => (κ p.1, κ p.2))
    (fun p => if κ p.1 ≠ κ p.2 then D p else 0)]
  apply Finset.sum_congr rfl
  intro r _
  rw [Dist.fTransform_apply_eq_sum]
  by_cases hr : r.1 ≠ r.2
  · rw [if_pos hr]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hfst : κ p.1 = r.1 := congrArg Prod.fst hp
    have hsnd : κ p.2 = r.2 := congrArg Prod.snd hp
    have hpne : κ p.1 ≠ κ p.2 := by
      intro hsame
      apply hr
      rw [← hfst, ← hsnd]
      exact hsame
    simp [hpne]
  · rw [if_neg hr]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hsame : κ p.1 = κ p.2 := by
      have hfst : κ p.1 = r.1 := congrArg Prod.fst hp
      have hsnd : κ p.2 = r.2 := congrArg Prod.snd hp
      rw [hfst, hsnd]
      exact of_not_not hr
    simp [hsame]

omit [Fintype Ω] in
private theorem sum_labelFirstBlockCouplingJoint_offdiag_eq_offlabel
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ))) :
    ∑ p ∈ (Finset.univ : Finset (A × A)).filter (fun p => p.1 ≠ p.2),
        labelFirstBlockCouplingJoint X Y κ C p =
      ∑ p ∈ (Finset.univ : Finset (A × A)).filter
          (fun p => κ p.1 ≠ κ p.2),
        labelFirstBlockCouplingJoint X Y κ C p := by
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.1 = p.2
  · have hκsame : κ p.1 = κ p.2 := by rw [hp]
    rw [if_neg (by exact fun h => h hp),
      if_neg (by exact fun h => h hκsame)]
  · by_cases hκ : κ p.1 = κ p.2
    · rw [if_pos hp, if_neg (by simpa using hκ)]
      exact labelFirstBlockCouplingJoint_eq_zero_of_same_label_ne
        (X := X) (Y := Y) (κ := κ) C hp hκ
    · rw [if_pos hp, if_pos hκ]

/-- The explicit label-first lift disagrees exactly when the classifier-label
coupling disagrees.  Matched labels are coupled perfectly inside the common
fiber, and mismatched labels necessarily produce different samples. -/
theorem labelFirstBlockCoupling_prDisagree
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (C : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ))) :
    (labelFirstBlockCoupling X Y κ C).prDisagree = C.prDisagree := by
  simp only [DistCoupling.prDisagree, labelFirstBlockCoupling]
  calc
    ∑ p ∈ (Finset.univ : Finset (A × A)).filter (fun p => p.1 ≠ p.2),
        labelFirstBlockCouplingJoint X Y κ C p =
        ∑ p ∈ (Finset.univ : Finset (A × A)).filter
          (fun p => κ p.1 ≠ κ p.2),
          labelFirstBlockCouplingJoint X Y κ C p := by
          exact sum_labelFirstBlockCouplingJoint_offdiag_eq_offlabel X Y κ C
    _ = ∑ r ∈ (Finset.univ : Finset (Ω × Ω)).filter (fun r => r.1 ≠ r.2),
          (Dist.fTransform (fun p : A × A => (κ p.1, κ p.2))
            (labelFirstBlockCouplingJoint X Y κ C)) r := by
          exact (sum_fTransform_pair_classifier_offdiag
            (labelFirstBlockCouplingJoint X Y κ C) κ).symm
    _ = ∑ r ∈ (Finset.univ : Finset (Ω × Ω)).filter (fun r => r.1 ≠ r.2),
          C.joint r := by
          rw [labelFirstBlockCouplingJoint_fTransform_labels]

/-- Block-uniform representatives have both an optimal classifier-label
coupling and an optimal full coupling of the representatives, with the same
failure probability.

This is the LM20 endpoint needed before doing any orbit arithmetic: after the
representatives have been replaced by "sample a block, then sample uniformly
inside it", the distinguishing mass is exactly the block-label mismatch.  This
theorem uses the explicit label-first lift as the full representative coupling:
first maximally couple classifier labels, then couple perfectly inside matched
labels. -/
theorem exists_fullAndClassifierMassCouplings_of_blockUniform
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (hXnn : X.NonNeg) (hYnn : Y.NonNeg)
    (hw : (classifierBlockUniform X κ).weight =
      (classifierBlockUniform Y κ).weight) :
    ∃ CLabel : DistCoupling
        (Dist.fTransform κ (classifierBlockUniform X κ))
        (Dist.fTransform κ (classifierBlockUniform Y κ)),
      ∃ CFull : DistCoupling
          (classifierBlockUniform X κ) (classifierBlockUniform Y κ),
        statDist (classifierBlockUniform X κ) (classifierBlockUniform Y κ) =
          CFull.prDisagree ∧
        CFull.prDisagree = CLabel.prDisagree := by
  obtain ⟨CLabel, hLabel⟩ := exists_classifierMassCoupling_of_blockUniform
    (X := X) (Y := Y) (κ := κ) hXnn hYnn hw
  let CFull := labelFirstBlockCoupling X Y κ CLabel
  refine ⟨CLabel, CFull, ?_, ?_⟩
  · rw [labelFirstBlockCoupling_prDisagree]
    exact hLabel
  · exact labelFirstBlockCoupling_prDisagree X Y κ CLabel

/-- Block-uniform representatives have both an optimal coupling of the original
classifier-label masses and an optimal full coupling of the representatives.

This is the type-clean LM20 formulation: the labels are distributed as
`Dist.fTransform κ X` and `Dist.fTransform κ Y`, while the full samples are
drawn from the corresponding block-uniform representatives. -/
theorem exists_fullAndOriginalClassifierMassCouplings_of_blockUniform
    [DecidableEq A]
    (X Y : Dist A) (κ : A → Ω)
    (hXnn : X.NonNeg) (hYnn : Y.NonNeg)
    (hw : (Dist.fTransform κ X).weight = (Dist.fTransform κ Y).weight) :
    ∃ CLabel : DistCoupling (Dist.fTransform κ X) (Dist.fTransform κ Y),
      ∃ CFull : DistCoupling
          (classifierBlockUniform X κ) (classifierBlockUniform Y κ),
        statDist (classifierBlockUniform X κ) (classifierBlockUniform Y κ) =
          CFull.prDisagree ∧
        CFull.prDisagree = CLabel.prDisagree := by
  obtain ⟨CLabel, hLabel⟩ := optimal_coupling_exists
    (hXnn.fTransform κ) (hYnn.fTransform κ) hw
  let CLabelBlock : DistCoupling
      (Dist.fTransform κ (classifierBlockUniform X κ))
      (Dist.fTransform κ (classifierBlockUniform Y κ)) := {
    joint := CLabel.joint
    nonneg := CLabel.nonneg
    marginal_fst := by
      rw [classifierBlockUniform_fTransform]
      exact CLabel.marginal_fst
    marginal_snd := by
      rw [classifierBlockUniform_fTransform]
      exact CLabel.marginal_snd }
  let CFull := labelFirstBlockCoupling X Y κ CLabelBlock
  refine ⟨CLabel, CFull, ?_, ?_⟩
  · rw [labelFirstBlockCoupling_prDisagree]
    change statDist (classifierBlockUniform X κ) (classifierBlockUniform Y κ) =
      CLabel.prDisagree
    rw [statDist_classifierBlockUniform_eq_originalClassifierStatDist]
    exact hLabel
  · rw [labelFirstBlockCoupling_prDisagree]
    simp [CLabelBlock, DistCoupling.prDisagree]

/--
SoP-specific classifier collapse: any classifier whose fibers have constant
compatible hidden-state count gives an exact transcript-distance quotient.

This is more general than the affine-orbit theorem: affine-coordinate orbits are
one source of such classifiers, but the theorem only needs constancy of the real
transcript numerator `compatibleCountNNReal`.
-/
theorem visibleStatDist_eq_classifierStatDist_of_compatibleCount_constant
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z) :
    visibleStatDist (G := G) (q := q) =
      statDist
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))) := by
  unfold visibleStatDist
  exact statDist_eq_classifierStatDist_of_constantFibers
    (X := realVisibleDist (G := G) (q := q))
    (Y := idealVisibleDist (G := G) (q := q))
    (κ := κ)
    (by
      intro y z hyz
      rw [realVisibleDist_apply, realVisibleDist_apply]
      unfold realVisibleMass
      rw [hC hyz])
    (by
      intro y z hyz
      rw [idealVisibleDist_apply, idealVisibleDist_apply]
      simp [idealVisibleMass, Dist.uniform_apply])

/--
Coupling form of
`visibleStatDist_eq_classifierStatDist_of_compatibleCount_constant`.

This is the transcript-level LM20 block-coupling theorem for any SoP
classifier with constant compatible count on fibers.  It does not depend on
the affine-orbit construction; affine orbits are one way to supply `hC`.
-/
theorem exists_visibleClassifierMassCoupling_of_compatibleCount_constant
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z)
    (hw : (realVisibleDist (G := G) (q := q)).weight =
      (idealVisibleDist (G := G) (q := q)).weight) :
    ∃ C : DistCoupling
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))),
      visibleStatDist (G := G) (q := q) = C.prDisagree := by
  unfold visibleStatDist
  exact exists_classifierMassCoupling_of_constantFibers
    (X := realVisibleDist (G := G) (q := q))
    (Y := idealVisibleDist (G := G) (q := q))
    (κ := κ)
    (by
      intro y
      rw [realVisibleDist_apply]
      exact NNReal.coe_nonneg _)
    (by
      intro y
      rw [idealVisibleDist_apply]
      exact NNReal.coe_nonneg _)
    (by
      intro y z hyz
      rw [realVisibleDist_apply, realVisibleDist_apply]
      unfold realVisibleMass
      rw [hC hyz])
    (by
      intro y z hyz
      rw [idealVisibleDist_apply, idealVisibleDist_apply]
      simp [idealVisibleMass, Dist.uniform_apply])
    hw

/-- The real visible law is exactly the block-uniform representative of its
classifier masses whenever the compatible count is constant on classifier
fibers.  Equivalently: sample a block according to the real block mass, then
sample uniformly inside the block. -/
theorem realVisibleDist_eq_classifierBlockUniform_of_compatibleCount_constant
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z) :
    realVisibleDist (G := G) (q := q) =
      classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ := by
  symm
  exact classifierBlockUniform_eq_of_constantFibers
    (X := realVisibleDist (G := G) (q := q))
    (κ := κ)
    (by
      intro y z hyz
      rw [realVisibleDist_apply, realVisibleDist_apply]
      unfold realVisibleMass
      rw [hC hyz])

/-- The ideal visible law is always exactly the block-uniform representative of
its classifier masses.  Its block mass is just proportional to the classifier
fiber size. -/
theorem idealVisibleDist_eq_classifierBlockUniform
    {G : Type*} {q : Nat} [Fintype G] [DecidableEq G] [Nonempty G]
    {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) :
    idealVisibleDist (G := G) (q := q) =
      classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ := by
  symm
  exact classifierBlockUniform_eq_of_constantFibers
    (X := idealVisibleDist (G := G) (q := q))
    (κ := κ)
    (by
      intro y z _hyz
      rw [idealVisibleDist_apply, idealVisibleDist_apply]
      simp [idealVisibleMass, Dist.uniform_apply])

/-- Fiber-mass form of
`visibleStatDist_eq_classifierStatDist_of_compatibleCount_constant`. -/
theorem visibleStatDist_eq_sum_fiberMasses_of_compatibleCount_constant
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z) :
    (visibleStatDist (G := G) (q := q) : Real) =
      ∑ ω : Ω,
        max
          ((∑ y ∈ Finset.univ.filter (fun y : Fin q → G => κ y = ω),
              (realVisibleMass (G := G) (q := q) y : Real)) -
            (∑ y ∈ Finset.univ.filter (fun y : Fin q → G => κ y = ω),
              (idealVisibleMass (G := G) (q := q) y : Real))) 0 := by
  rw [visibleStatDist_eq_classifierStatDist_of_compatibleCount_constant
    (G := G) (q := q) κ hC]
  simp [statDist_eq_sum_univ, Dist.fTransform_apply_eq_sum, realVisibleDist_apply,
    idealVisibleDist_apply]

/-- The natural compatible count attached to a classifier fiber, using zero on
empty fibers.  For orbit classifiers every occupied fiber receives the common
compatible count of that orbit.

This `Nat` version is the right bridge to the rank/gain-graph expansion, which
is stated as an integer identity for `compatibleCountNat`. -/
def classifierCompatibleCountNat
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) (ω : Ω) : Nat :=
  if h : ∃ y : Fin q → G, κ y = ω then
    compatibleCountNat (G := G) (q := q) (Classical.choose h)
  else
    0

/-- The `NNReal` compatible count attached to a classifier fiber, using zero on
empty fibers.  This is the form used in transcript probability masses. -/
def classifierCompatibleCount
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) (ω : Ω) : NNReal :=
  (classifierCompatibleCountNat (G := G) (q := q) κ ω : NNReal)

/-- The probability-level fiber count is definitionally the `NNReal` cast of
the natural fiber count. -/
@[simp]
theorem classifierCompatibleCount_eq_coe_nat
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) (ω : Ω) :
    classifierCompatibleCount (G := G) (q := q) κ ω =
      (classifierCompatibleCountNat (G := G) (q := q) κ ω : NNReal) := by
  rfl

/-- On an occupied classifier fiber, the canonical natural compatible count is
the natural compatible count of any representative of that fiber. -/
theorem classifierCompatibleCountNat_eq_compatibleCountNat_of_mem
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNat (G := G) (q := q) y =
        compatibleCountNat (G := G) (q := q) z)
    {ω : Ω} {y : Fin q → G} (hy : κ y = ω) :
    classifierCompatibleCountNat (G := G) (q := q) κ ω =
      compatibleCountNat (G := G) (q := q) y := by
  unfold classifierCompatibleCountNat
  let h : ∃ z : Fin q → G, κ z = ω := ⟨y, hy⟩
  rw [dif_pos h]
  have hκ : κ (Classical.choose h) = κ y := by
    rw [Classical.choose_spec h, hy]
  exact hC hκ

/-- On an occupied classifier fiber, the canonical compatible count is the
compatible count of any representative of that fiber.

This is the bridge used by orbit-sum formulas: once an orbit label is known to
be occupied, external enumeration or the rank/gain-graph expansion may compute
`classifierCompatibleCount` by choosing any visible transcript in the orbit. -/
theorem classifierCompatibleCount_eq_compatibleCountNNReal_of_mem
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z)
    {ω : Ω} {y : Fin q → G} (hy : κ y = ω) :
    classifierCompatibleCount (G := G) (q := q) κ ω =
      compatibleCountNNReal (G := G) (q := q) y := by
  have hCNat : ∀ ⦃u v : Fin q → G⦄, κ u = κ v →
      compatibleCountNat (G := G) (q := q) u =
        compatibleCountNat (G := G) (q := q) v := by
    intro u v huv
    exact Nat.cast_inj.mp (by
      simpa [compatibleCountNNReal] using hC huv)
  rw [classifierCompatibleCount_eq_coe_nat]
  rw [classifierCompatibleCountNat_eq_compatibleCountNat_of_mem
    (G := G) (q := q) κ hCNat hy]
  simp [compatibleCountNNReal]

/-- If compatible counts are constant on classifier fibers, every visible tuple
has the compatible count assigned to its fiber. -/
theorem compatibleCountNNReal_eq_classifierCompatibleCount
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    {Ω : Type*} [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z)
    (y : Fin q → G) :
    compatibleCountNNReal (G := G) (q := q) y =
      classifierCompatibleCount (G := G) (q := q) κ (κ y) := by
  exact (classifierCompatibleCount_eq_compatibleCountNNReal_of_mem
    (G := G) (q := q) κ hC (ω := κ y) (y := y) rfl).symm

/-- Real visible classifier mass as fiber cardinality times the common
compatible count of the fiber. -/
theorem classifierWeight_realVisibleDist_eq_card_mul_classifierCompatibleCount
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z)
    (ω : Ω) :
    classifierWeight (realVisibleDist (G := G) (q := q)) κ ω =
      ((classifierFiber κ ω).card : Real) *
        ((classifierCompatibleCount (G := G) (q := q) κ ω : Real) /
          (realVisibleDenominator (G := G) q : Real)) := by
  unfold classifierWeight
  calc
    ∑ a ∈ classifierFiber κ ω, realVisibleDist (G := G) (q := q) a =
        ∑ a ∈ classifierFiber κ ω,
          ((classifierCompatibleCount (G := G) (q := q) κ ω : Real) /
            (realVisibleDenominator (G := G) q : Real)) := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [classifierFiber, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          rw [realVisibleDist_apply, realVisibleMass]
          rw [← classifierCompatibleCount_eq_compatibleCountNNReal_of_mem
            (G := G) (q := q) κ hC ha]
          exact NNReal.coe_div _ _
    _ = ((classifierFiber κ ω).card : Real) *
        ((classifierCompatibleCount (G := G) (q := q) κ ω : Real) /
          (realVisibleDenominator (G := G) q : Real)) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Ideal visible classifier mass as fiber cardinality times the uniform point
mass. -/
theorem classifierWeight_idealVisibleDist_eq_card_mul_uniformMass
    {G : Type*} {q : Nat} [Fintype G] [Nonempty G]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) (ω : Ω) :
    classifierWeight (idealVisibleDist (G := G) (q := q)) κ ω =
      ((classifierFiber κ ω).card : Real) *
        (1 / ((Fintype.card G ^ q : Nat) : Real)) := by
  unfold classifierWeight
  calc
    ∑ a ∈ classifierFiber κ ω, idealVisibleDist (G := G) (q := q) a =
        ∑ _a ∈ classifierFiber κ ω,
          (1 / ((Fintype.card G ^ q : Nat) : Real)) := by
          apply Finset.sum_congr rfl
          intro a _ha
          simp [idealVisibleDist_apply, idealVisibleMass, Dist.uniform_apply]
    _ = ((classifierFiber κ ω).card : Real) *
        (1 / ((Fintype.card G ^ q : Nat) : Real)) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- Explicit cardinality-times-count form of the exact classifier formula. -/
theorem visibleStatDist_eq_sum_card_countWeights_of_compatibleCount
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) (Cκ : Ω → NNReal)
    (hC : ∀ y : Fin q → G,
      compatibleCountNNReal (G := G) (q := q) y = Cκ (κ y)) :
    (visibleStatDist (G := G) (q := q) : Real) =
      ∑ ω : Ω,
        max
          ((((Finset.univ.filter (fun y : Fin q → G => κ y = ω)).card : Real) *
              ((Cκ ω : Real) / (realVisibleDenominator (G := G) q : Real))) -
            (((Finset.univ.filter (fun y : Fin q → G => κ y = ω)).card : Real) *
              (1 / ((Fintype.card G ^ q : Nat) : Real)))) 0 := by
  rw [visibleStatDist_eq_sum_fiberMasses_of_compatibleCount_constant
    (G := G) (q := q) κ
    (by
      intro y z hyz
      rw [hC y, hC z, hyz])]
  apply Finset.sum_congr rfl
  intro ω _
  have hreal :
      ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => κ y = ω),
          (realVisibleMass (G := G) (q := q) y : Real) =
        ((Finset.univ.filter (fun y : Fin q → G => κ y = ω)).card : Real) *
          ((Cκ ω : Real) / (realVisibleDenominator (G := G) q : Real)) := by
    calc
      ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => κ y = ω),
          (realVisibleMass (G := G) (q := q) y : Real)
          = ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => κ y = ω),
              ((Cκ ω : Real) / (realVisibleDenominator (G := G) q : Real)) := by
            apply Finset.sum_congr rfl
            intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            rw [realVisibleMass, hC y, hy]
            exact NNReal.coe_div _ _
      _ = (((Finset.univ.filter (fun y : Fin q → G => κ y = ω)).card : Real) *
            ((Cκ ω : Real) / (realVisibleDenominator (G := G) q : Real))) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  have hideal :
      ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => κ y = ω),
          (idealVisibleMass (G := G) (q := q) y : Real) =
        ((Finset.univ.filter (fun y : Fin q → G => κ y = ω)).card : Real) *
          (1 / ((Fintype.card G ^ q : Nat) : Real)) := by
    calc
      ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => κ y = ω),
          (idealVisibleMass (G := G) (q := q) y : Real)
          = ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => κ y = ω),
              (1 / ((Fintype.card G ^ q : Nat) : Real)) := by
            apply Finset.sum_congr rfl
            intro y _hy
            simp [idealVisibleMass, Dist.uniform_apply]
      _ = (((Finset.univ.filter (fun y : Fin q → G => κ y = ω)).card : Real) *
            (1 / ((Fintype.card G ^ q : Nat) : Real))) := by
            simp [Finset.sum_const, nsmul_eq_mul]
  rw [hreal, hideal]

/-- Exact classifier formula using the canonical compatible count attached to
each occupied classifier fiber. -/
theorem visibleStatDist_eq_sum_card_classifierCompatibleCount
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hC : ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z) :
    (visibleStatDist (G := G) (q := q) : Real) =
      ∑ ω : Ω,
        max
          ((((classifierFiber κ ω).card : Real) *
              ((classifierCompatibleCount (G := G) (q := q) κ ω : Real) /
                (realVisibleDenominator (G := G) q : Real))) -
            (((classifierFiber κ ω).card : Real) *
              (1 / ((Fintype.card G ^ q : Nat) : Real)))) 0 := by
  rw [visibleStatDist_eq_sum_card_countWeights_of_compatibleCount
    (G := G) (q := q) κ
    (classifierCompatibleCount (G := G) (q := q) κ)
    (compatibleCountNNReal_eq_classifierCompatibleCount (G := G) (q := q) κ hC)]
  rfl

end SoP
end Applications
end RandomSystems
