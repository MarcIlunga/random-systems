/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Applications.SoP.SmallQ
import RandomSystems.Applications.SoP.Partition
import RandomSystems.Coupling

/-!
# SoP Affine Invariance

This file starts the affine-type layer.  The first invariant is the reusable
linear/additive part: compatible hidden-state counts are preserved by additive
equivalences of the output group.  Global translations are already inherited
from the XoP combinatorics file.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace SoP

variable {G : Type*} {q : Nat} [AddGroup G]

/-- Apply an additive equivalence coordinatewise to a visible tuple. -/
def mapVisible (e : G ≃+ G) (y : Fin q → G) : Fin q → G :=
  fun i => e (y i)

/-- Reindex a visible tuple by a coordinate permutation. -/
def permVisible (σ : Equiv.Perm (Fin q)) (y : Fin q → G) : Fin q → G :=
  fun i => y (σ i)

/-- Apply a coordinate permutation, additive equivalence, and global translation
to a visible tuple. -/
def affineCoordVisible (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G)
    (y : Fin q → G) : Fin q → G :=
  fun i => e (y (σ i)) + t

/-- Additive equivalences preserve compatible hidden states. -/
theorem compatibleHiddenState_mapVisible (e : G ≃+ G) {y a : Fin q → G}
    (h : CompatibleHiddenState y a) :
    CompatibleHiddenState (mapVisible (q := q) e y) (fun i => e (a i)) := by
  rcases h with ⟨ha, hshift⟩
  constructor
  · intro i j hij
    exact ha (e.injective hij)
  · intro i j hij
    apply hshift
    apply e.injective
    simpa [CompatibleHiddenState, XoP.Combinatorics.shifted, mapVisible] using hij

/-- Coordinate permutations preserve compatible hidden states. -/
theorem compatibleHiddenState_permVisible (σ : Equiv.Perm (Fin q)) {y a : Fin q → G}
    (h : CompatibleHiddenState y a) :
    CompatibleHiddenState (permVisible (q := q) σ y) (fun i => a (σ i)) := by
  rcases h with ⟨ha, hshift⟩
  constructor
  · intro i j hij
    exact σ.injective (ha hij)
  · intro i j hij
    apply σ.injective
    apply hshift
    simpa [XoP.Combinatorics.shifted, permVisible] using hij

variable [Fintype G] [DecidableEq G]

/-- A distribution on visible tuples is affine-coordinate invariant if its
point mass is unchanged by coordinate permutations, additive equivalences, and
global translations of the visible tuple.  This is the predicate consumed by the
orbit/partition layer. -/
def AffineCoordInvariant (X : Dist (Fin q → G)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G),
    X (affineCoordVisible (q := q) σ e t y) = X y

/-- A classifier whose fibers are exactly affine-coordinate orbits.  The first
field says affine-coordinate moves stay inside a classifier fiber.  The second
field says every pair in the same classifier fiber is related by one such move. -/
structure AffineCoordOrbitClassifier (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω) : Prop where
  map_eq :
    ∀ (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G),
      κ (affineCoordVisible (q := q) σ e t y) = κ y
  exists_map_of_eq :
    ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      ∃ (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G),
        z = affineCoordVisible (q := q) σ e t y

omit [Fintype G] [DecidableEq G] in
/-- An affine-coordinate invariant distribution is constant on the fibers of
any affine-coordinate orbit classifier. -/
theorem AffineCoordInvariant.constantOn_orbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (X : Dist (Fin q → G)) (κ : (Fin q → G) → Ω)
    (hX : AffineCoordInvariant (G := G) (q := q) X)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∀ ⦃y z : Fin q → G⦄, κ y = κ z → X y = X z := by
  intro y z hyz
  rcases hκ.exists_map_of_eq hyz with ⟨σ, e, t, rfl⟩
  exact (hX σ e t y).symm

/-- Additive equivalences preserve compatible hidden-state counts. -/
theorem compatibleCountNat_mapVisible (e : G ≃+ G) (y : Fin q → G) :
    compatibleCountNat (G := G) (q := q) (mapVisible (q := q) e y) =
      compatibleCountNat (G := G) (q := q) y := by
  classical
  unfold compatibleCountNat XoP.Combinatorics.compatibleCountNat
  refine Finset.card_bij (fun a _ => fun i => e.symm (a i)) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have h := compatibleHiddenState_mapVisible (q := q) e.symm ha
    convert h using 1
    funext i
    simp [mapVisible]
  · intro a₁ ha₁ a₂ ha₂ h
    funext i
    apply e.symm.injective
    exact congr_fun h i
  · intro b hb
    refine ⟨fun i => e (b i), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact compatibleHiddenState_mapVisible (q := q) e hb
    · funext i
      simp

/-- Additive equivalences preserve compatible hidden-state counts as `NNReal`s. -/
theorem compatibleCountNNReal_mapVisible (e : G ≃+ G) (y : Fin q → G) :
    compatibleCountNNReal (G := G) (q := q) (mapVisible (q := q) e y) =
      compatibleCountNNReal (G := G) (q := q) y := by
  simpa [compatibleCountNNReal] using
    congrArg (fun n : Nat => (n : NNReal)) (compatibleCountNat_mapVisible (G := G) (q := q) e y)

/-- Coordinate permutations preserve compatible hidden-state counts. -/
theorem compatibleCountNat_permVisible (σ : Equiv.Perm (Fin q)) (y : Fin q → G) :
    compatibleCountNat (G := G) (q := q) (permVisible (q := q) σ y) =
      compatibleCountNat (G := G) (q := q) y := by
  classical
  unfold compatibleCountNat XoP.Combinatorics.compatibleCountNat
  refine Finset.card_bij (fun a _ => fun i => a (σ.symm i)) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have h := compatibleHiddenState_permVisible (q := q) σ.symm ha
    convert h using 1
    funext i
    simp [permVisible]
  · intro a₁ ha₁ a₂ ha₂ h
    funext i
    have h' := congr_fun h (σ i)
    simpa using h'
  · intro b hb
    refine ⟨fun i => b (σ i), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact compatibleHiddenState_permVisible (q := q) σ hb
    · funext i
      simp

/-- Coordinate permutations preserve compatible hidden-state counts as `NNReal`s. -/
theorem compatibleCountNNReal_permVisible (σ : Equiv.Perm (Fin q)) (y : Fin q → G) :
    compatibleCountNNReal (G := G) (q := q) (permVisible (q := q) σ y) =
      compatibleCountNNReal (G := G) (q := q) y := by
  simpa [compatibleCountNNReal] using
    congrArg (fun n : Nat => (n : NNReal)) (compatibleCountNat_permVisible (G := G) (q := q) σ y)

/-- Coordinate permutations preserve exact real visible mass. -/
theorem realVisibleMass_permVisible (σ : Equiv.Perm (Fin q)) (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) (permVisible (q := q) σ y) =
      realVisibleMass (G := G) (q := q) y := by
  unfold realVisibleMass
  rw [compatibleCountNNReal_permVisible]

/-- Coordinate permutations preserve the visible density ratio. -/
theorem visibleDensityRatio_permVisible (hq : q ≤ Fintype.card G)
    (σ : Equiv.Perm (Fin q)) (y : Fin q → G) :
    visibleDensityRatio (G := G) (q := q) hq (permVisible (q := q) σ y) =
      visibleDensityRatio (G := G) (q := q) hq y := by
  unfold visibleDensityRatio
  rw [compatibleCountNNReal_permVisible]

/-- Affine-coordinate transformations preserve compatible hidden-state counts. -/
theorem compatibleCountNat_affineCoordVisible
    (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G) :
    compatibleCountNat (G := G) (q := q) (affineCoordVisible (q := q) σ e t y) =
      compatibleCountNat (G := G) (q := q) y := by
  calc
    compatibleCountNat (G := G) (q := q) (affineCoordVisible (q := q) σ e t y)
        = compatibleCountNat (G := G) (q := q)
            (mapVisible (q := q) e (permVisible (q := q) σ y)) := by
          simpa [affineCoordVisible, mapVisible, permVisible] using
            compatibleCountNat_add_const (G := G) (q := q)
              (mapVisible (q := q) e (permVisible (q := q) σ y)) t
    _ = compatibleCountNat (G := G) (q := q) (permVisible (q := q) σ y) := by
          exact compatibleCountNat_mapVisible (G := G) (q := q) e (permVisible (q := q) σ y)
    _ = compatibleCountNat (G := G) (q := q) y := by
          exact compatibleCountNat_permVisible (G := G) (q := q) σ y

/-- Affine-coordinate transformations preserve compatible hidden-state counts
as `NNReal`s. -/
theorem compatibleCountNNReal_affineCoordVisible
    (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G) :
    compatibleCountNNReal (G := G) (q := q) (affineCoordVisible (q := q) σ e t y) =
      compatibleCountNNReal (G := G) (q := q) y := by
  simpa [compatibleCountNNReal] using
    congrArg (fun n : Nat => (n : NNReal))
      (compatibleCountNat_affineCoordVisible (G := G) (q := q) σ e t y)

/-- Natural compatible hidden-state counts are constant on the fibers of any
affine-coordinate orbit classifier.  This is the affine-orbit input needed by
the integer rank/gain-graph expansion. -/
theorem compatibleCountNat_constantOn_orbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNat (G := G) (q := q) y =
        compatibleCountNat (G := G) (q := q) z := by
  intro y z hyz
  rcases hκ.exists_map_of_eq hyz with ⟨σ, e, t, rfl⟩
  exact (compatibleCountNat_affineCoordVisible (G := G) (q := q) σ e t y).symm

/-- Compatible hidden-state counts are constant on the fibers of any
affine-coordinate orbit classifier. -/
theorem compatibleCountNNReal_constantOn_orbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
      compatibleCountNNReal (G := G) (q := q) y =
        compatibleCountNNReal (G := G) (q := q) z := by
  intro y z hyz
  simpa [compatibleCountNNReal] using
    congrArg (fun n : Nat => (n : NNReal))
      (compatibleCountNat_constantOn_orbitClassifier (G := G) (q := q) κ hκ hyz)

/-- On an occupied affine-coordinate orbit classifier fiber, the natural
compatible count attached to the fiber is computed by any representative
transcript in that orbit. -/
theorem classifierCompatibleCountNat_eq_compatibleCountNat_of_affineCoordOrbitClassifier_mem
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ)
    {ω : Ω} {y : Fin q → G} (hy : κ y = ω) :
    classifierCompatibleCountNat (G := G) (q := q) κ ω =
      compatibleCountNat (G := G) (q := q) y :=
  classifierCompatibleCountNat_eq_compatibleCountNat_of_mem
    (G := G) (q := q) κ
    (compatibleCountNat_constantOn_orbitClassifier (G := G) (q := q) κ hκ)
    hy

/-- On an occupied affine-coordinate orbit classifier fiber, the natural
compatible count attached to the fiber has the same rank-zero/rank-one/tail
expansion as any representative transcript in that orbit.

This is the formal handoff from the LM20 orbit-block numerator \(C_\omega\) to
the gain-graph/rank expansion. -/
theorem classifierCompatibleCountNat_eq_rankZero_add_rankOne_add_tail_of_affineCoordOrbitClassifier_mem
    {H : Type*} {r : Nat} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin r → H) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := H) (q := r) Ω κ)
    {ω : Ω} {y : Fin r → H} (hy : κ y = ω) (hr : 0 < r) :
    (classifierCompatibleCountNat (G := H) (q := r) κ ω : ℤ) =
      ((Fintype.card H) ^ r : ℤ) +
      ((Fintype.card H) ^ (r - 1) : ℤ) *
        ∑ p : PairIndex r, (-2 + (if y p.1.2 = y p.1.1 then 1 else 0) : ℤ) +
      collisionSubfamilyRankTailBeyondOneInt (G := H) (q := r) y hr := by
  rw [classifierCompatibleCountNat_eq_compatibleCountNat_of_affineCoordOrbitClassifier_mem
    (G := H) (q := r) κ hκ hy]
  exact compatibleCountNat_eq_rankZero_add_rankOne_add_tail
    (G := H) (q := r) y hr

/-- Affine-coordinate transformations preserve exact real visible mass. -/
theorem realVisibleMass_affineCoordVisible
    (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) (affineCoordVisible (q := q) σ e t y) =
      realVisibleMass (G := G) (q := q) y := by
  unfold realVisibleMass
  rw [compatibleCountNNReal_affineCoordVisible]

/-- Affine-coordinate transformations preserve the visible density ratio. -/
theorem visibleDensityRatio_affineCoordVisible (hq : q ≤ Fintype.card G)
    (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G) :
    visibleDensityRatio (G := G) (q := q) hq (affineCoordVisible (q := q) σ e t y) =
      visibleDensityRatio (G := G) (q := q) hq y := by
  unfold visibleDensityRatio
  rw [compatibleCountNNReal_affineCoordVisible]

omit [DecidableEq G] in
/-- Affine-coordinate transformations preserve ideal visible mass. -/
theorem idealVisibleMass_affineCoordVisible [Nonempty G]
    (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G) :
    idealVisibleMass (G := G) (q := q) (affineCoordVisible (q := q) σ e t y) =
      idealVisibleMass (G := G) (q := q) y := by
  simp [idealVisibleMass, Dist.uniform_apply]

/-- Affine-coordinate transformations preserve the pointwise real visible
distribution. -/
theorem realVisibleDist_affineCoordVisible
    (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G) :
    realVisibleDist (G := G) (q := q) (affineCoordVisible (q := q) σ e t y) =
      realVisibleDist (G := G) (q := q) y := by
  rw [realVisibleDist_apply, realVisibleDist_apply, realVisibleMass_affineCoordVisible]

omit [DecidableEq G] in
/-- Affine-coordinate transformations preserve the pointwise ideal visible
distribution. -/
theorem idealVisibleDist_affineCoordVisible [Nonempty G]
    (σ : Equiv.Perm (Fin q)) (e : G ≃+ G) (t : G) (y : Fin q → G) :
    idealVisibleDist (G := G) (q := q) (affineCoordVisible (q := q) σ e t y) =
      idealVisibleDist (G := G) (q := q) y := by
  rw [idealVisibleDist_apply, idealVisibleDist_apply, idealVisibleMass_affineCoordVisible]

/-- The real visible transcript distribution is affine-coordinate invariant. -/
theorem realVisibleDist_affineCoordInvariant :
    AffineCoordInvariant (G := G) (q := q) (realVisibleDist (G := G) (q := q)) := by
  intro σ e t y
  exact realVisibleDist_affineCoordVisible (G := G) (q := q) σ e t y

omit [DecidableEq G] in
/-- The ideal visible transcript distribution is affine-coordinate invariant. -/
theorem idealVisibleDist_affineCoordInvariant [Nonempty G] :
    AffineCoordInvariant (G := G) (q := q) (idealVisibleDist (G := G) (q := q)) := by
  intro σ e t y
  exact idealVisibleDist_affineCoordVisible (G := G) (q := q) σ e t y

/-- For any classifier whose fibers are exactly affine-coordinate orbits, the
visible transcript distance is exactly the distance between the induced
classifier-label distributions. -/
theorem visibleStatDist_eq_classifierStatDist_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    visibleStatDist (G := G) (q := q) =
      statDist
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))) := by
  exact visibleStatDist_eq_classifierStatDist_of_compatibleCount_constant
    (G := G) (q := q) κ
    (compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ)

/-- For an affine-coordinate orbit classifier, the visible transcript distance
is exactly the positive-part distance between real and ideal orbit masses. -/
theorem visibleStatDist_eq_sum_classifierWeights_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    visibleStatDist (G := G) (q := q) =
      ∑ ω : Ω,
        (classifierWeight (realVisibleDist (G := G) (q := q)) κ ω -
          classifierWeight (idealVisibleDist (G := G) (q := q)) κ ω) := by
  rw [visibleStatDist_eq_sum_fiberMasses_of_compatibleCount_constant
    (G := G) (q := q) κ
    (compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ)]
  rfl

/-- Real affine-orbit block mass as orbit cardinality times the common
compatible count of the orbit. -/
theorem classifierWeight_realVisibleDist_eq_card_mul_classifierCompatibleCount_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ)
    (ω : Ω) :
    classifierWeight (realVisibleDist (G := G) (q := q)) κ ω =
      ((classifierFiber κ ω).card : NNReal) *
        (classifierCompatibleCount (G := G) (q := q) κ ω /
          realVisibleDenominator (G := G) q) := by
  exact classifierWeight_realVisibleDist_eq_card_mul_classifierCompatibleCount
    (G := G) (q := q) κ
    (compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ)
    ω

omit [AddGroup G] [DecidableEq G] in
/-- Ideal affine-orbit block mass as orbit cardinality times uniform point
mass. -/
theorem classifierWeight_idealVisibleDist_eq_card_mul_uniformMass_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (κ : (Fin q → G) → Ω) (ω : Ω) :
    classifierWeight (idealVisibleDist (G := G) (q := q)) κ ω =
      ((classifierFiber κ ω).card : NNReal) *
        (1 / ((Fintype.card G ^ q : Nat) : NNReal)) := by
  exact classifierWeight_idealVisibleDist_eq_card_mul_uniformMass
    (G := G) (q := q) κ ω

/-- Cardinality-times-compatible-count form for affine-coordinate orbit
classifiers.  This is the finite orbit-sum identity in a form ready for
external orbit enumeration or later closed-form estimates. -/
theorem visibleStatDist_eq_sum_card_classifierCompatibleCount_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    visibleStatDist (G := G) (q := q) =
      ∑ ω : Ω,
        ((((classifierFiber κ ω).card : NNReal) *
            (classifierCompatibleCount (G := G) (q := q) κ ω /
              realVisibleDenominator (G := G) q)) -
          (((classifierFiber κ ω).card : NNReal) *
            (1 / ((Fintype.card G ^ q : Nat) : NNReal)))) := by
  exact visibleStatDist_eq_sum_card_classifierCompatibleCount
    (G := G) (q := q) κ
    (compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ)

/-- Exact injective-input XoP advantage as distance between affine-orbit
classifier masses.  This is the theorem-facing endpoint of the transcript
orbit identity. -/
theorem xop_advantageOn_injective_eq_classifierStatDist_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    advantageOn (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q))
        (XoP.InjectiveInputs (X := G) (q := q)) =
      statDist
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))) := by
  rw [XoP.Model.xop_advantageOn_injective_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact visibleStatDist_eq_classifierStatDist_of_affineCoordOrbitClassifier
    (G := G) (q := q) κ hκ

/-- Exact injective-input XoP advantage as the positive-part sum of real minus
ideal affine-orbit block masses. -/
theorem xop_advantageOn_injective_eq_sum_classifierWeights_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    advantageOn (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q))
        (XoP.InjectiveInputs (X := G) (q := q)) =
      ∑ ω : Ω,
        (classifierWeight (realVisibleDist (G := G) (q := q)) κ ω -
          classifierWeight (idealVisibleDist (G := G) (q := q)) κ ω) := by
  rw [XoP.Model.xop_advantageOn_injective_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact visibleStatDist_eq_sum_classifierWeights_of_affineCoordOrbitClassifier
    (G := G) (q := q) κ hκ

/-- Exact injective-input XoP advantage as the finite affine-orbit
cardinality-times-compatible-count sum. -/
theorem xop_advantageOn_injective_eq_sum_card_classifierCompatibleCount_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    advantageOn (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q))
        (XoP.InjectiveInputs (X := G) (q := q)) =
      ∑ ω : Ω,
        ((((classifierFiber κ ω).card : NNReal) *
            (classifierCompatibleCount (G := G) (q := q) κ ω /
              realVisibleDenominator (G := G) q)) -
          (((classifierFiber κ ω).card : NNReal) *
            (1 / ((Fintype.card G ^ q : Nat) : NNReal)))) := by
  rw [XoP.Model.xop_advantageOn_injective_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact visibleStatDist_eq_sum_card_classifierCompatibleCount_of_affineCoordOrbitClassifier
    (G := G) (q := q) κ hκ

/-- Exact unrestricted adaptive XoP advantage as distance between affine-orbit
classifier masses. -/
theorem xop_adaptiveAdvantage_eq_classifierStatDist_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) =
      statDist
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))) := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact visibleStatDist_eq_classifierStatDist_of_affineCoordOrbitClassifier
    (G := G) (q := q) κ hκ

/-- Exact unrestricted adaptive XoP advantage as the positive-part sum of real
minus ideal affine-orbit block masses. -/
theorem xop_adaptiveAdvantage_eq_sum_classifierWeights_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) =
      ∑ ω : Ω,
        (classifierWeight (realVisibleDist (G := G) (q := q)) κ ω -
          classifierWeight (idealVisibleDist (G := G) (q := q)) κ ω) := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact visibleStatDist_eq_sum_classifierWeights_of_affineCoordOrbitClassifier
    (G := G) (q := q) κ hκ

/-- Exact unrestricted adaptive XoP advantage as the finite affine-orbit
cardinality-times-compatible-count sum. -/
theorem xop_adaptiveAdvantage_eq_sum_card_classifierCompatibleCount_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) =
      ∑ ω : Ω,
        ((((classifierFiber κ ω).card : NNReal) *
            (classifierCompatibleCount (G := G) (q := q) κ ω /
              realVisibleDenominator (G := G) q)) -
          (((classifierFiber κ ω).card : NNReal) *
            (1 / ((Fintype.card G ^ q : Nat) : NNReal)))) := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact visibleStatDist_eq_sum_card_classifierCompatibleCount_of_affineCoordOrbitClassifier
    (G := G) (q := q) κ hκ

/-- Affine-coordinate orbit classifiers produce honest LM20 representatives for
both XoP and URF.

The representatives are not the natural eager systems.  They sample a
classifier/orbit block with the natural real or ideal block mass, sample
uniformly inside that visible-output block, then replay the sampled output tape
as a deterministic system. -/
theorem xop_equivAdaptive_blockUniformRepresentatives_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    PDS.equivAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (PDS.ofPositionTapeDist (q := q) (X := G)
          (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)) ∧
      PDS.equivAdaptive (XoP.Model.xopIdealPDS (G := G) (q := q))
        (PDS.ofPositionTapeDist (q := q) (X := G)
          (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)) := by
  constructor
  · exact XoP.Model.xopReal_equivAdaptive_positionTape_blockUniform
      (G := G) (q := q) κ
      (compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ)
      hq
  · exact XoP.Model.xopIdeal_equivAdaptive_positionTape_blockUniform
      (G := G) (q := q) κ

/-- There is an optimal coupling of the actual visible transcript laws whose
failure probability is exactly the restricted injective-input XoP advantage.

This is the transcript-level LM20 coupling statement.  It is deliberately
weaker than a full PDS representative lift: the coupling lives over visible
output tuples, not over deterministic discrete systems. -/
theorem exists_visibleTranscriptCoupling_xop_advantageOn_injective [Nonempty G]
    (hq : q ≤ Fintype.card G) :
    ∃ C : DistCoupling (realVisibleDist (G := G) (q := q))
        (idealVisibleDist (G := G) (q := q)),
      advantageOn (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q))
        (XoP.InjectiveInputs (X := G) (q := q)) = C.prDisagree := by
  classical
  have hweights : (realVisibleDist (G := G) (q := q)).weight =
      (idealVisibleDist (G := G) (q := q)).weight := by
    rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
        (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
    have hreal : (realVisibleDist (G := G) (q := q)).weight = 1 := by
      rw [← XoP.Model.real_xop_outputDist_eq_sop_realVisibleDist
        (G := G) (q := q) emb emb.injective hq]
      rw [Dist.weight_fTransform]
      exact XoP.Model.xopReal_isProbPDS (G := G) (q := q)
    have hideal : (idealVisibleDist (G := G) (q := q)).weight = 1 := by
      exact Dist.weight_uniform
    rw [hreal, hideal]
  obtain ⟨C, hC⟩ := optimal_coupling_exists
    (realVisibleDist (G := G) (q := q))
    (idealVisibleDist (G := G) (q := q)) hweights
  refine ⟨C, ?_⟩
  rw [XoP.Model.xop_advantageOn_injective_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact hC

/-- The optimal visible transcript coupling can be read at affine-orbit
granularity: for any affine-coordinate orbit classifier, its disagreement
probability is the statistical distance between real and ideal orbit-label
masses.

This is the precise transcript-level statement behind the informal phrase
"failure equals orbit mismatch." -/
theorem exists_visibleTranscriptCoupling_xop_advantageOn_injective_of_affineCoordOrbitClassifier
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ C : DistCoupling (realVisibleDist (G := G) (q := q))
        (idealVisibleDist (G := G) (q := q)),
      C.prDisagree =
        statDist
          (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
          (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))) ∧
      advantageOn (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q))
        (XoP.InjectiveInputs (X := G) (q := q)) = C.prDisagree := by
  classical
  obtain ⟨C, hC⟩ := exists_visibleTranscriptCoupling_xop_advantageOn_injective
    (G := G) (q := q) hq
  refine ⟨C, ?_, hC⟩
  rw [← hC]
  exact xop_advantageOn_injective_eq_classifierStatDist_of_affineCoordOrbitClassifier
    (G := G) (q := q) hq κ hκ

/-- There is an optimal coupling of the affine-orbit classifier masses whose
failure probability is exactly the restricted injective-input XoP advantage.

This is the transcript/orbit-level LM20 coupling statement: couple the orbit
labels optimally.  A later PDS-lift theorem must turn this classifier-level
coupling into honest representatives over deterministic systems. -/
theorem exists_orbitMassCoupling_xop_advantageOn_injective
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ C : DistCoupling
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))),
      advantageOn (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q))
        (XoP.InjectiveInputs (X := G) (q := q)) = C.prDisagree := by
  classical
  have hweights :
      (Dist.fTransform κ (realVisibleDist (G := G) (q := q))).weight =
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))).weight := by
    rw [Dist.weight_fTransform, Dist.weight_fTransform]
    rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
        (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
    have hreal : (realVisibleDist (G := G) (q := q)).weight = 1 := by
      rw [← XoP.Model.real_xop_outputDist_eq_sop_realVisibleDist
        (G := G) (q := q) emb emb.injective hq]
      rw [Dist.weight_fTransform]
      exact XoP.Model.xopReal_isProbPDS (G := G) (q := q)
    have hideal : (idealVisibleDist (G := G) (q := q)).weight = 1 := by
      exact Dist.weight_uniform
    rw [hreal, hideal]
  obtain ⟨C, hC⟩ := exists_visibleClassifierMassCoupling_of_compatibleCount_constant
    (G := G) (q := q) κ
    (compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ)
    (by
      rw [Dist.weight_fTransform, Dist.weight_fTransform] at hweights
      exact hweights)
  refine ⟨C, ?_⟩
  rw [XoP.Model.xop_advantageOn_injective_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact hC

/-- There is an optimal coupling of the affine-orbit classifier masses whose
failure probability is exactly the unrestricted adaptive XoP advantage. -/
theorem exists_orbitMassCoupling_xop_adaptiveAdvantage
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ C : DistCoupling
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))),
      advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) = C.prDisagree := by
  classical
  have hweights :
      (Dist.fTransform κ (realVisibleDist (G := G) (q := q))).weight =
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))).weight := by
    rw [Dist.weight_fTransform, Dist.weight_fTransform]
    rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
        (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
    have hreal : (realVisibleDist (G := G) (q := q)).weight = 1 := by
      rw [← XoP.Model.real_xop_outputDist_eq_sop_realVisibleDist
        (G := G) (q := q) emb emb.injective hq]
      rw [Dist.weight_fTransform]
      exact XoP.Model.xopReal_isProbPDS (G := G) (q := q)
    have hideal : (idealVisibleDist (G := G) (q := q)).weight = 1 := by
      exact Dist.weight_uniform
    rw [hreal, hideal]
  obtain ⟨C, hC⟩ := exists_visibleClassifierMassCoupling_of_compatibleCount_constant
    (G := G) (q := q) κ
    (compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ)
    (by
      rw [Dist.weight_fTransform, Dist.weight_fTransform] at hweights
      exact hweights)
  refine ⟨C, ?_⟩
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  exact hC

/-- LM20-native endpoint: affine-coordinate orbit classifiers give honest
block-uniform representatives and an optimal classifier-label coupling whose
failure probability is the unrestricted adaptive XoP advantage.

The representatives sample an affine/output block and then sample uniformly
inside it.  The coupling lives on the representatives' classifier labels; the
generic `classifierBlockUniform` theorem proves that matching labels leave no
additional within-block statistical distance. -/
theorem exists_blockUniformRepresentativeOrbitCoupling_xop_adaptiveAdvantage
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ C : DistCoupling
        (Dist.fTransform κ
          (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ))
        (Dist.fTransform κ
          (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)),
      PDS.equivAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (PDS.ofPositionTapeDist (q := q) (X := G)
          (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)) ∧
      PDS.equivAdaptive (XoP.Model.xopIdealPDS (G := G) (q := q))
        (PDS.ofPositionTapeDist (q := q) (X := G)
          (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)) ∧
      advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) = C.prDisagree := by
  classical
  have hCconst :
      ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
        compatibleCountNNReal (G := G) (q := q) y =
          compatibleCountNNReal (G := G) (q := q) z :=
    compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ
  have hrealBlock :
      realVisibleDist (G := G) (q := q) =
        classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ :=
    realVisibleDist_eq_classifierBlockUniform_of_compatibleCount_constant
      (G := G) (q := q) κ hCconst
  have hidealBlock :
      idealVisibleDist (G := G) (q := q) =
        classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ :=
    idealVisibleDist_eq_classifierBlockUniform (G := G) (q := q) κ
  have hweightsVisible : (realVisibleDist (G := G) (q := q)).weight =
      (idealVisibleDist (G := G) (q := q)).weight := by
    rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
        (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
    have hreal : (realVisibleDist (G := G) (q := q)).weight = 1 := by
      rw [← XoP.Model.real_xop_outputDist_eq_sop_realVisibleDist
        (G := G) (q := q) emb emb.injective hq]
      rw [Dist.weight_fTransform]
      exact XoP.Model.xopReal_isProbPDS (G := G) (q := q)
    have hideal : (idealVisibleDist (G := G) (q := q)).weight = 1 := by
      exact Dist.weight_uniform
    rw [hreal, hideal]
  have hweightsBlock :
      (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ).weight =
        (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ).weight := by
    rw [← hrealBlock, ← hidealBlock]
    exact hweightsVisible
  obtain ⟨C, hCoupling⟩ := exists_classifierMassCoupling_of_blockUniform
    (X := realVisibleDist (G := G) (q := q))
    (Y := idealVisibleDist (G := G) (q := q))
    (κ := κ)
    hweightsBlock
  obtain ⟨hRealRep, hIdealRep⟩ :=
    xop_equivAdaptive_blockUniformRepresentatives_of_affineCoordOrbitClassifier
      (G := G) (q := q) hq κ hκ
  refine ⟨C, hRealRep, hIdealRep, ?_⟩
  rw [← hCoupling]
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist
    (G := G) (q := q) hq]
  unfold visibleStatDist
  exact congrArg₂ statDist hrealBlock hidealBlock

/-- Stronger LM20-native endpoint: affine-coordinate orbit classifiers give
honest block-uniform representatives, an optimal classifier-label coupling, and
an optimal full coupling of the block-uniform representatives.  Both couplings
have failure probability equal to the unrestricted adaptive XoP advantage.

This theorem is the formal "representatives first, coupling second" statement.
The remaining gain-graph/rank work is only for evaluating the common
block-label mismatch. -/
theorem exists_fullBlockUniformRepresentativeOrbitCoupling_xop_adaptiveAdvantage
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ CLabel : DistCoupling
        (Dist.fTransform κ
          (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ))
        (Dist.fTransform κ
          (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)),
      ∃ CFull : DistCoupling
          (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)
          (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ),
        PDS.equivAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)) ∧
        PDS.equivAdaptive (XoP.Model.xopIdealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)) ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) = CLabel.prDisagree ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) = CFull.prDisagree ∧
        CFull.prDisagree = CLabel.prDisagree := by
  classical
  have hCconst :
      ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
        compatibleCountNNReal (G := G) (q := q) y =
          compatibleCountNNReal (G := G) (q := q) z :=
    compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ
  have hrealBlock :
      realVisibleDist (G := G) (q := q) =
        classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ :=
    realVisibleDist_eq_classifierBlockUniform_of_compatibleCount_constant
      (G := G) (q := q) κ hCconst
  have hidealBlock :
      idealVisibleDist (G := G) (q := q) =
        classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ :=
    idealVisibleDist_eq_classifierBlockUniform (G := G) (q := q) κ
  have hweightsVisible : (realVisibleDist (G := G) (q := q)).weight =
      (idealVisibleDist (G := G) (q := q)).weight := by
    rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
        (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
    have hreal : (realVisibleDist (G := G) (q := q)).weight = 1 := by
      rw [← XoP.Model.real_xop_outputDist_eq_sop_realVisibleDist
        (G := G) (q := q) emb emb.injective hq]
      rw [Dist.weight_fTransform]
      exact XoP.Model.xopReal_isProbPDS (G := G) (q := q)
    have hideal : (idealVisibleDist (G := G) (q := q)).weight = 1 := by
      exact Dist.weight_uniform
    rw [hreal, hideal]
  have hweightsBlock :
      (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ).weight =
        (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ).weight := by
    rw [← hrealBlock, ← hidealBlock]
    exact hweightsVisible
  obtain ⟨CLabel, CFull, hFull, hFullLabel⟩ :=
    exists_fullAndClassifierMassCouplings_of_blockUniform
      (X := realVisibleDist (G := G) (q := q))
      (Y := idealVisibleDist (G := G) (q := q))
      (κ := κ)
      hweightsBlock
  obtain ⟨hRealRep, hIdealRep⟩ :=
    xop_equivAdaptive_blockUniformRepresentatives_of_affineCoordOrbitClassifier
      (G := G) (q := q) hq κ hκ
  have hAdvStat :
      advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) =
        statDist
          (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)
          (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ) := by
    rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist
      (G := G) (q := q) hq]
    unfold visibleStatDist
    exact congrArg₂ statDist hrealBlock hidealBlock
  refine ⟨CLabel, CFull, hRealRep, hIdealRep, ?_, ?_, hFullLabel⟩
  · rw [hAdvStat, hFull, hFullLabel]
  · rw [hAdvStat, hFull]

/-- Fully lifted LM20 endpoint: affine-coordinate orbit classifiers give
honest equivalent position-tape PDS representatives and a coupling of those
representative PDS distributions over deterministic systems.

This is the system-level version of
`exists_fullBlockUniformRepresentativeOrbitCoupling_xop_adaptiveAdvantage`.
The output-tape coupling is pushed through `DDS.ofPositionTape`; the hypothesis
`q ≤ |G|` supplies an injective fixed input sequence, so this pushforward
preserves the disagreement probability. -/
theorem exists_positionTapePDSRepresentativeOrbitCoupling_xop_adaptiveAdvantage
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ CLabel : DistCoupling
        (Dist.fTransform κ
          (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ))
        (Dist.fTransform κ
          (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)),
      ∃ CPDS : DistCoupling
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)).dist
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)).dist,
        PDS.equivAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)) ∧
        PDS.equivAdaptive (XoP.Model.xopIdealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)) ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) = CLabel.prDisagree ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) = CPDS.prDisagree ∧
        CPDS.prDisagree = CLabel.prDisagree := by
  classical
  obtain ⟨CLabel, CFull, hRealRep, hIdealRep, hAdvLabel, hAdvFull, hFullLabel⟩ :=
    exists_fullBlockUniformRepresentativeOrbitCoupling_xop_adaptiveAdvantage
      (G := G) (q := q) hq κ hκ
  rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
      (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
  let CPDS : DistCoupling
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)).dist
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)).dist :=
    PDS.positionTapeDistCoupling (q := q) (X := G) CFull
  have hCPDSFull : CPDS.prDisagree = CFull.prDisagree := by
    exact PDS.positionTapeDistCoupling_prDisagree_of_injective_inputs
      (q := q) (X := G) CFull emb emb.injective
  refine ⟨CLabel, CPDS, hRealRep, hIdealRep, hAdvLabel, ?_, ?_⟩
  · rw [hCPDSFull, hAdvFull]
  · rw [hCPDSFull, hFullLabel]

/-- Fully lifted LM20 endpoint with the classifier-label coupling stated over
the original real and ideal orbit masses.

This is the cleanest current formal statement of the LM20 proof shape.  The
representative PDSs are block-uniform position-tape systems, equivalent to the
natural XoP and URF PDSs.  The label coupling is an optimal coupling of the
original orbit/block weights
`Dist.fTransform κ realVisibleDist` and `Dist.fTransform κ idealVisibleDist`.
The full representative coupling is obtained by first using that label
coupling and then coupling perfectly inside matching blocks. -/
theorem exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ CLabel : DistCoupling
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))),
      ∃ CPDS : DistCoupling
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)).dist
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)).dist,
        PDS.equivAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)) ∧
        PDS.equivAdaptive (XoP.Model.xopIdealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)) ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) = CLabel.prDisagree ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) = CPDS.prDisagree ∧
        CPDS.prDisagree = CLabel.prDisagree := by
  classical
  have hCconst :
      ∀ ⦃y z : Fin q → G⦄, κ y = κ z →
        compatibleCountNNReal (G := G) (q := q) y =
          compatibleCountNNReal (G := G) (q := q) z :=
    compatibleCountNNReal_constantOn_orbitClassifier (G := G) (q := q) κ hκ
  have hrealBlock :
      realVisibleDist (G := G) (q := q) =
        classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ :=
    realVisibleDist_eq_classifierBlockUniform_of_compatibleCount_constant
      (G := G) (q := q) κ hCconst
  have hidealBlock :
      idealVisibleDist (G := G) (q := q) =
        classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ :=
    idealVisibleDist_eq_classifierBlockUniform (G := G) (q := q) κ
  have hweightsVisible : (realVisibleDist (G := G) (q := q)).weight =
      (idealVisibleDist (G := G) (q := q)).weight := by
    rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
        (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
    have hreal : (realVisibleDist (G := G) (q := q)).weight = 1 := by
      rw [← XoP.Model.real_xop_outputDist_eq_sop_realVisibleDist
        (G := G) (q := q) emb emb.injective hq]
      rw [Dist.weight_fTransform]
      exact XoP.Model.xopReal_isProbPDS (G := G) (q := q)
    have hideal : (idealVisibleDist (G := G) (q := q)).weight = 1 := by
      exact Dist.weight_uniform
    rw [hreal, hideal]
  have hweightsLabel :
      (Dist.fTransform κ (realVisibleDist (G := G) (q := q))).weight =
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))).weight := by
    rw [Dist.weight_fTransform, Dist.weight_fTransform]
    exact hweightsVisible
  obtain ⟨CLabel, CFull, hFull, hFullLabel⟩ :=
    exists_fullAndOriginalClassifierMassCouplings_of_blockUniform
      (X := realVisibleDist (G := G) (q := q))
      (Y := idealVisibleDist (G := G) (q := q))
      (κ := κ)
      hweightsLabel
  obtain ⟨hRealRep, hIdealRep⟩ :=
    xop_equivAdaptive_blockUniformRepresentatives_of_affineCoordOrbitClassifier
      (G := G) (q := q) hq κ hκ
  have hAdvStat :
      advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) =
        statDist
          (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)
          (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ) := by
    rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist
      (G := G) (q := q) hq]
    unfold visibleStatDist
    exact congrArg₂ statDist hrealBlock hidealBlock
  rcases Function.Embedding.nonempty_of_card_le (α := Fin q) (β := G)
      (by simpa [Fintype.card_fin] using hq) with ⟨emb⟩
  let CPDS : DistCoupling
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)).dist
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)).dist :=
    PDS.positionTapeDistCoupling (q := q) (X := G) CFull
  have hCPDSFull : CPDS.prDisagree = CFull.prDisagree := by
    exact PDS.positionTapeDistCoupling_prDisagree_of_injective_inputs
      (q := q) (X := G) CFull emb emb.injective
  refine ⟨CLabel, CPDS, hRealRep, hIdealRep, ?_, ?_, ?_⟩
  · rw [hAdvStat, hFull, hFullLabel]
  · rw [hCPDSFull]
    rw [hAdvStat, hFull]
  · rw [hCPDSFull, hFullLabel]

/-- Fully lifted LM20 endpoint with the exact orbit/block mass discrepancy
included in the statement.

This theorem packages the whole proof shape:

* replace the natural XoP and URF PDSs by block-uniform position-tape
  representatives;
* optimally couple the original affine-orbit label masses;
* lift that label coupling to a full representative-PDS coupling;
* the label-coupling failure probability, the representative-coupling failure
  probability, and the original adaptive advantage are all the same number,
  namely the statistical distance between the original orbit/block masses. -/
theorem exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage_with_labelStatDist
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ CLabel : DistCoupling
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))),
      ∃ CPDS : DistCoupling
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)).dist
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)).dist,
        PDS.equivAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)) ∧
        PDS.equivAdaptive (XoP.Model.xopIdealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)) ∧
        statDist
          (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
          (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))) = CLabel.prDisagree ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) =
          statDist
            (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
            (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))) ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) = CPDS.prDisagree ∧
        CPDS.prDisagree = CLabel.prDisagree := by
  obtain ⟨CLabel, CPDS, hRealRep, hIdealRep, hAdvLabel, hAdvPDS, hPDSLabel⟩ :=
    exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage
      (G := G) (q := q) hq κ hκ
  have hAdvStat :=
    xop_adaptiveAdvantage_eq_classifierStatDist_of_affineCoordOrbitClassifier
      (G := G) (q := q) hq κ hκ
  refine ⟨CLabel, CPDS, hRealRep, hIdealRep, ?_, hAdvStat, hAdvPDS, hPDSLabel⟩
  rw [← hAdvStat, hAdvLabel]

/-- Fully lifted LM20 endpoint with the orbit/block mass discrepancy written as
the positive-part sum of real minus ideal orbit masses.

This is the most explicit current endpoint: the natural PDSs are replaced by
equivalent block-uniform position-tape representatives, the representatives are
coupled by first coupling orbit labels and then matching inside equal labels,
and the failure probability is exactly the explicit orbit-mass discrepancy. -/
theorem exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage_with_blockMassSum
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ CLabel : DistCoupling
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))),
      ∃ CPDS : DistCoupling
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)).dist
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)).dist,
        PDS.equivAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)) ∧
        PDS.equivAdaptive (XoP.Model.xopIdealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)) ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) =
          ∑ ω : Ω,
            (classifierWeight (realVisibleDist (G := G) (q := q)) κ ω -
              classifierWeight (idealVisibleDist (G := G) (q := q)) κ ω) ∧
        CPDS.prDisagree =
          ∑ ω : Ω,
            (classifierWeight (realVisibleDist (G := G) (q := q)) κ ω -
              classifierWeight (idealVisibleDist (G := G) (q := q)) κ ω) ∧
        CLabel.prDisagree =
          ∑ ω : Ω,
            (classifierWeight (realVisibleDist (G := G) (q := q)) κ ω -
              classifierWeight (idealVisibleDist (G := G) (q := q)) κ ω) ∧
        CPDS.prDisagree = CLabel.prDisagree := by
  obtain ⟨CLabel, CPDS, hRealRep, hIdealRep, hLabelStat, hAdvStat, hAdvPDS, hPDSLabel⟩ :=
    exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage_with_labelStatDist
      (G := G) (q := q) hq κ hκ
  have hAdvSum :=
    xop_adaptiveAdvantage_eq_sum_classifierWeights_of_affineCoordOrbitClassifier
      (G := G) (q := q) hq κ hκ
  refine ⟨CLabel, CPDS, hRealRep, hIdealRep, hAdvSum, ?_, ?_, hPDSLabel⟩
  · rw [← hAdvSum, hAdvPDS]
  · rw [← hAdvSum, hAdvStat, hLabelStat]

/-- Fully lifted LM20 endpoint with the representative-coupling failure written
as the finite cardinality-times-compatible-count orbit sum.

This is the direct handoff from the LM20 representative/coupling layer to the
gain-graph/rank layer: after this theorem, bounding the XoP advantage is exactly
bounding the displayed sum, whose only nontrivial orbit-dependent term is the
compatible count \(C_\omega\). -/
theorem exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage_with_cardCompatibleCountSum
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty G]
    (hq : q ≤ Fintype.card G)
    (κ : (Fin q → G) → Ω)
    (hκ : AffineCoordOrbitClassifier (G := G) (q := q) Ω κ) :
    ∃ CLabel : DistCoupling
        (Dist.fTransform κ (realVisibleDist (G := G) (q := q)))
        (Dist.fTransform κ (idealVisibleDist (G := G) (q := q))),
      ∃ CPDS : DistCoupling
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)).dist
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)).dist,
        PDS.equivAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (realVisibleDist (G := G) (q := q)) κ)) ∧
        PDS.equivAdaptive (XoP.Model.xopIdealPDS (G := G) (q := q))
          (PDS.ofPositionTapeDist (q := q) (X := G)
            (classifierBlockUniform (idealVisibleDist (G := G) (q := q)) κ)) ∧
        advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
          (XoP.Model.xopIdealPDS (G := G) (q := q)) =
          ∑ ω : Ω,
            ((((classifierFiber κ ω).card : NNReal) *
                (classifierCompatibleCount (G := G) (q := q) κ ω /
                  realVisibleDenominator (G := G) q)) -
              (((classifierFiber κ ω).card : NNReal) *
                (1 / ((Fintype.card G ^ q : Nat) : NNReal)))) ∧
        CPDS.prDisagree =
          ∑ ω : Ω,
            ((((classifierFiber κ ω).card : NNReal) *
                (classifierCompatibleCount (G := G) (q := q) κ ω /
                  realVisibleDenominator (G := G) q)) -
              (((classifierFiber κ ω).card : NNReal) *
                (1 / ((Fintype.card G ^ q : Nat) : NNReal)))) ∧
        CLabel.prDisagree =
          ∑ ω : Ω,
            ((((classifierFiber κ ω).card : NNReal) *
                (classifierCompatibleCount (G := G) (q := q) κ ω /
                  realVisibleDenominator (G := G) q)) -
              (((classifierFiber κ ω).card : NNReal) *
                (1 / ((Fintype.card G ^ q : Nat) : NNReal)))) ∧
        CPDS.prDisagree = CLabel.prDisagree := by
  obtain ⟨CLabel, CPDS, hRealRep, hIdealRep, hAdvMass, hPDSMass, hLabelMass, hPDSLabel⟩ :=
    exists_positionTapePDSRepresentativeOriginalOrbitCoupling_xop_adaptiveAdvantage_with_blockMassSum
      (G := G) (q := q) hq κ hκ
  have hAdvCard :=
    xop_adaptiveAdvantage_eq_sum_card_classifierCompatibleCount_of_affineCoordOrbitClassifier
      (G := G) (q := q) hq κ hκ
  refine ⟨CLabel, CPDS, hRealRep, hIdealRep, hAdvCard, ?_, ?_, hPDSLabel⟩
  · rw [← hAdvCard, hPDSMass, hAdvMass]
  · rw [← hAdvCard, hLabelMass, hAdvMass]

end SoP
end Applications
end RandomSystems
