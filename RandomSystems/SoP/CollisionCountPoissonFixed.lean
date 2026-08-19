/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.CollisionCountPoisson
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Fixed-rate Poisson limit for the collision-count proxy

This file closes the birthday-scale interpolation at every fixed finite
Poisson rate.  The proof uses the planted-collision representative itself.
Planting one edge gives the exact size-biased collision law.  Except when a
third coordinate meets one of the planted endpoints, the collision count goes
up by exactly one.  This gives an approximate Poisson recurrence for every
fixed atom, starting from the exact birthday-product zero atom.

Only finitely many atoms are needed for the mean absolute deviation: for a
fixed center `r`, its lower half is cut off at `floor r`, while the first
moment supplies the upper half.  This also avoids any separate uniform-
integrability argument and handles integer rates without a boundary case.
-/

noncomputable section

open scoped BigOperators NNReal
open Filter

namespace RandomSystems.SoP.CollisionCountPoissonFixed

open ProbabilityTheory
open RandomSystems.SoP.CollisionStein
open RandomSystems.SoP.CollisionCountNormal
open RandomSystems.SoP.CollisionCountPoisson
open RandomSystems.SoP.XORFourier

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem uniformAverage_finset_sum_over_finite
    {A I : Type*} [Fintype A]
    (s : Finset I) (f : I → A → Real) :
    uniformAverage A (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, uniformAverage A (f i) := by
  unfold uniformAverage average
  rw [Finset.sum_comm, Finset.sum_div]

/-- Closed Poisson mean-absolute-deviation target.  The equality with the
infinite-series definition is proved in `XORCollisionAsymptotics.lean`. -/
def fixedPoissonMAD (r : NNReal) : Real :=
  2 * (r : Real) * poissonPMFReal r ⌊(r : Real)⌋₊

theorem poissonPMFReal_succ_recurrence (r : NNReal) (k : Nat) :
    ((k + 1 : Nat) : Real) * poissonPMFReal r (k + 1) =
      (r : Real) * poissonPMFReal r k := by
  unfold poissonPMFReal
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have hk : (k : Real) + 1 ≠ 0 := by positivity
  field_simp [hk]

/-- Replace the right endpoint of `e` by the color at its left endpoint. -/
def plantCollision {G : Type*} [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) : Fin q → G :=
  Function.update y (edgeRight e) (y (edgeLeft e))

@[simp]
theorem plantCollision_right {G : Type*} [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) :
    plantCollision e y (edgeRight e) = y (edgeLeft e) := by
  simp [plantCollision]

theorem plantCollision_of_ne {G : Type*} [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) {i : Fin q}
    (hi : i ≠ edgeRight e) :
    plantCollision e y i = y i := by
  simp [plantCollision, hi]

@[simp]
theorem edgeIndicator_plantCollision_self
    (G : Type*) [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) :
    edgeIndicator G e (plantCollision e y) = 1 := by
  unfold edgeIndicator
  rw [plantCollision_right, plantCollision_of_ne e y (edgeLeft_ne_right e)]
  simp

theorem edgeIndicator_nonneg
    (G : Type*) [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) :
    0 ≤ edgeIndicator G e y := by
  unfold edgeIndicator
  split_ifs <;> norm_num

theorem abs_edgeIndicator
    (G : Type*) [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) :
    |edgeIndicator G e y| = edgeIndicator G e y :=
  abs_of_nonneg (edgeIndicator_nonneg G e y)

/-- Conditioning a uniform coloring on one edge being monochromatic is the
same as planting that collision.  This is the exact finite size-bias engine. -/
theorem uniformAverage_edgeIndicator_mul_eq_inv_mul_planted
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) (F : (Fin q → G) → Real) :
    uniformAverage (Fin q → G) (fun y => edgeIndicator G e y * F y) =
      (1 / (Fintype.card G : Real)) *
        uniformAverage (Fin q → G) (fun y => F (plantCollision e y)) := by
  let P : (Fin q → G) → Real := fun y => F (plantCollision e y)
  have hPinv : ∀ (r : {k : Fin q // k ≠ edgeRight e} → G) (a b : G),
      P ((removeCoordEquiv G (edgeRight e)).symm (a, r)) =
        P ((removeCoordEquiv G (edgeRight e)).symm (b, r)) := by
    intro r a b
    unfold P
    congr 1
    funext i
    by_cases hi : i = edgeRight e
    · subst i
      simp [plantCollision, removeCoordEquiv_apply_ne,
        edgeLeft_ne_right e]
    · simp [plantCollision, hi, removeCoordEquiv_apply_ne]
  have hcenter := uniformAverage_centered_eq_mul_of_removeCoord_invariant
    G (edgeLeft_ne_right e).symm P hPinv
  have hpoint : (fun y : Fin q → G => edgeIndicator G e y * F y) =
      (fun y => edgeIndicator G e y * P y) := by
    funext y
    by_cases h : y (edgeRight e) = y (edgeLeft e)
    · have hp : plantCollision e y = y := by
        funext i
        by_cases hi : i = edgeRight e
        · subst i
          simp [plantCollision, h]
        · simp [plantCollision, hi]
      simp [edgeIndicator, h, P, hp]
    · simp [edgeIndicator, h]
  rw [hpoint]
  unfold centeredEdge at hcenter
  change uniformAverage (Fin q → G) (fun y =>
      (edgeIndicator G e y - 1 / (Fintype.card G : Real)) * P y) = 0 at hcenter
  rw [show (fun y : Fin q → G =>
      (edgeIndicator G e y - 1 / (Fintype.card G : Real)) * P y) =
      (fun y => edgeIndicator G e y * P y -
        (1 / (Fintype.card G : Real)) * P y) by
      funext y
      ring,
    uniformAverage_sub, uniformAverage_const_mul] at hcenter
  linarith

/-- An edge outside the dependency neighborhood is unchanged by planting `e`. -/
theorem edgeIndicator_plantCollision_eq_of_not_adjacent
    (G : Type*) [DecidableEq G] {q : Nat}
    {e f : Edge q} (hf : ¬EdgeAdjacent e f) (y : Fin q → G) :
    edgeIndicator G f (plantCollision e y) = edgeIndicator G f y := by
  have hleft : edgeLeft f ≠ edgeRight e := by
    intro h
    apply hf
    left
    exact Or.inr h
  have hright : edgeRight f ≠ edgeRight e := by
    intro h
    apply hf
    right
    exact Or.inr h
  unfold edgeIndicator
  rw [plantCollision_of_ne e y hright, plantCollision_of_ne e y hleft]

/-- Every other edge still has collision probability `1/N` after one edge is
planted.  This follows immediately from the exact two-edge moment. -/
theorem uniformAverage_edgeIndicator_plantCollision_of_ne
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} {e f : Edge q} (hef : e ≠ f) :
    uniformAverage (Fin q → G)
        (fun y => edgeIndicator G f (plantCollision e y)) =
      collisionProbability G := by
  have hcond := uniformAverage_edgeIndicator_mul_eq_inv_mul_planted
    G e (fun y => edgeIndicator G f y)
  have hpair := uniformAverage_edgeIndicator_mul_of_ne G hef
  rw [hpair] at hcond
  have hp : 0 < collisionProbability G := by
    unfold collisionProbability
    positivity
  exact mul_left_cancel₀ hp.ne' (by
    calc
      collisionProbability G *
          uniformAverage (Fin q → G)
            (fun y => edgeIndicator G f (plantCollision e y)) =
        collisionProbability G ^ 2 := hcond.symm
      _ = collisionProbability G * collisionProbability G := by ring)

private theorem collisionCount_split_local_outside
    (G : Type*) [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) :
    collisionCount G q y =
      ∑ f ∈ outsideEdges e, edgeIndicator G f y +
        ∑ f ∈ localEdges e, edgeIndicator G f y := by
  unfold collisionCount outsideEdges localEdges
  rw [add_comm, Finset.sum_filter_add_sum_filter_not]

private theorem sum_localEdges_eq_self_add_neighbors
    (G : Type*) [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) :
    ∑ f ∈ localEdges e, edgeIndicator G f y =
      edgeIndicator G e y +
        ∑ f ∈ neighborEdges e, edgeIndicator G f y := by
  unfold neighborEdges
  have he : e ∈ localEdges e := by simp [edgeAdjacent_refl]
  rw [← Finset.sum_erase_add _ _ he]
  ring

/-- Exact local expression for the failure of planting to add precisely one
collision. -/
theorem collisionCount_plantCollision_sub_eq
    (G : Type*) [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) :
    collisionCount G q (plantCollision e y) - collisionCount G q y - 1 =
      -edgeIndicator G e y +
        ∑ f ∈ neighborEdges e,
          (edgeIndicator G f (plantCollision e y) - edgeIndicator G f y) := by
  have hout :
      (∑ f ∈ outsideEdges e,
          edgeIndicator G f (plantCollision e y)) =
        ∑ f ∈ outsideEdges e, edgeIndicator G f y := by
    apply Finset.sum_congr rfl
    intro f hf
    exact edgeIndicator_plantCollision_eq_of_not_adjacent
      G (mem_outsideEdges.mp hf) y
  rw [collisionCount_split_local_outside G e,
    collisionCount_split_local_outside G e,
    sum_localEdges_eq_self_add_neighbors G e,
    sum_localEdges_eq_self_add_neighbors G e,
    edgeIndicator_plantCollision_self, hout,
    Finset.sum_sub_distrib]
  ring

/-- Pointwise local-dependence bound for the planted collision. -/
theorem abs_collisionCount_plantCollision_sub_le
    (G : Type*) [DecidableEq G] {q : Nat}
    (e : Edge q) (y : Fin q → G) :
    |collisionCount G q (plantCollision e y) - collisionCount G q y - 1| ≤
      edgeIndicator G e y +
        ∑ f ∈ neighborEdges e,
          (edgeIndicator G f (plantCollision e y) + edgeIndicator G f y) := by
  rw [collisionCount_plantCollision_sub_eq]
  calc
    |-edgeIndicator G e y +
        ∑ f ∈ neighborEdges e,
          (edgeIndicator G f (plantCollision e y) - edgeIndicator G f y)| ≤
      |-edgeIndicator G e y| +
        |∑ f ∈ neighborEdges e,
          (edgeIndicator G f (plantCollision e y) - edgeIndicator G f y)| :=
        abs_add_le _ _
    _ ≤ |-edgeIndicator G e y| +
        ∑ f ∈ neighborEdges e,
          |edgeIndicator G f (plantCollision e y) - edgeIndicator G f y| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ edgeIndicator G e y +
        ∑ f ∈ neighborEdges e,
          (edgeIndicator G f (plantCollision e y) + edgeIndicator G f y) := by
      rw [abs_neg, abs_edgeIndicator]
      gcongr with f hf
      calc
        |edgeIndicator G f (plantCollision e y) - edgeIndicator G f y| ≤
            |edgeIndicator G f (plantCollision e y)| +
              |edgeIndicator G f y| := abs_sub _ _
        _ = _ := by rw [abs_edgeIndicator, abs_edgeIndicator]

/-- Averaged planting error.  The intentionally simple `4q` neighborhood
bound is enough for every fixed birthday rate. -/
theorem uniformAverage_abs_collisionCount_plantCollision_sub_le
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (e : Edge q) :
    uniformAverage (Fin q → G) (fun y =>
        |collisionCount G q (plantCollision e y) - collisionCount G q y - 1|) ≤
      (1 + 8 * (q : Real)) / (Fintype.card G : Real) := by
  calc
    uniformAverage (Fin q → G) (fun y =>
        |collisionCount G q (plantCollision e y) - collisionCount G q y - 1|) ≤
      uniformAverage (Fin q → G) (fun y =>
        edgeIndicator G e y +
          ∑ f ∈ neighborEdges e,
            (edgeIndicator G f (plantCollision e y) + edgeIndicator G f y)) := by
      exact uniformAverage_mono (abs_collisionCount_plantCollision_sub_le G e)
    _ = collisionProbability G +
        2 * ((neighborEdges e).card : Real) * collisionProbability G := by
      rw [uniformAverage_add, uniformAverage_edgeIndicator,
        uniformAverage_finset_sum_over]
      congr 1
      calc
        ∑ f ∈ neighborEdges e,
            uniformAverage (Fin q → G) (fun y =>
              edgeIndicator G f (plantCollision e y) + edgeIndicator G f y) =
          ∑ _f ∈ neighborEdges e,
            (collisionProbability G + collisionProbability G) := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [uniformAverage_add,
              uniformAverage_edgeIndicator_plantCollision_of_ne G
                (Finset.ne_of_mem_erase hf).symm,
              uniformAverage_edgeIndicator]
        _ = 2 * ((neighborEdges e).card : Real) * collisionProbability G := by
          simp [Finset.sum_const, nsmul_eq_mul]
          ring
    _ ≤ collisionProbability G +
        2 * (4 * (q : Real)) * collisionProbability G := by
      have hcard : ((neighborEdges e).card : Real) ≤ 4 * (q : Real) := by
        exact_mod_cast card_neighborEdges_le_four_mul e
      gcongr
      exact collisionProbability_nonneg G
    _ = (1 + 8 * (q : Real)) / (Fintype.card G : Real) := by
      unfold collisionProbability
      ring

/-- Probability mass of one collision-count atom under a uniform coloring. -/
def collisionAtom (N q k : Nat) : Real :=
  uniformAverage (Fin q → Fin N) (fun y =>
    if collisionCountNat (Fin N) q y = k then 1 else 0)

theorem collisionAtom_nonneg {N q k : Nat} (hN : 0 < N) :
    0 ≤ collisionAtom N q k := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  unfold collisionAtom
  calc
    0 = uniformAverage (Fin q → Fin N) (fun _y => 0) := by
      rw [uniformAverage_const]
    _ ≤ _ := uniformAverage_mono (by
      intro y
      split_ifs <;> norm_num)

/-- Exact size-bias identity before normalizing by the number of edges. -/
theorem uniformAverage_collisionCount_mul_eq_planted_sum
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (F : (Fin q → G) → Real) :
    uniformAverage (Fin q → G) (fun y => collisionCount G q y * F y) =
      (1 / (Fintype.card G : Real)) *
        ∑ e : Edge q,
          uniformAverage (Fin q → G) (fun y => F (plantCollision e y)) := by
  calc
    uniformAverage (Fin q → G) (fun y => collisionCount G q y * F y) =
      uniformAverage (Fin q → G) (fun y =>
        ∑ e : Edge q, edgeIndicator G e y * F y) := by
          apply uniformAverage_congr
          intro y
          unfold collisionCount
          rw [Finset.sum_mul]
    _ = ∑ e : Edge q,
        uniformAverage (Fin q → G) (fun y => edgeIndicator G e y * F y) := by
          rw [uniformAverage_finset_sum]
    _ = ∑ e : Edge q,
        (1 / (Fintype.card G : Real)) *
          uniformAverage (Fin q → G) (fun y => F (plantCollision e y)) := by
          apply Finset.sum_congr rfl
          intro e _he
          exact uniformAverage_edgeIndicator_mul_eq_inv_mul_planted G e F
    _ = (1 / (Fintype.card G : Real)) *
        ∑ e : Edge q,
          uniformAverage (Fin q → G) (fun y => F (plantCollision e y)) := by
          rw [Finset.mul_sum]

/-- Atomwise form of the exact size-bias identity. -/
theorem collisionAtom_sizeBias
    {N q : Nat} (hN : 0 < N) (k : Nat) :
    (k : Real) * collisionAtom N q k =
      (1 / (N : Real)) *
        ∑ e : Edge q,
          uniformAverage (Fin q → Fin N) (fun y =>
            if collisionCountNat (Fin N) q (plantCollision e y) = k then 1 else 0) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have h := uniformAverage_collisionCount_mul_eq_planted_sum
    (Fin N) (q := q) (fun y =>
      if collisionCountNat (Fin N) q y = k then 1 else 0)
  simp only [Fintype.card_fin] at h
  rw [← h]
  unfold collisionAtom
  rw [← uniformAverage_const_mul]
  apply uniformAverage_congr
  intro y
  rw [collisionCount_eq_natCast]
  by_cases hy : collisionCountNat (Fin N) q y = k
  · simp [hy]
  · simp [hy]

/-- The zero atom is the exact birthday product. -/
theorem collisionAtom_zero_eq_birthdayProduct
    {N q : Nat} (hN : 0 < N) :
    collisionAtom N q 0 = birthdayProduct N q := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  calc
    collisionAtom N q 0 = collisionFreeProbability (Fin N) q := by
      unfold collisionAtom collisionFreeProbability
      apply uniformAverage_congr
      intro y
      by_cases hy : Function.Injective y
      · rw [collisionCountNat_eq_zero_of_injective (Fin N) hy]
        simp [hy]
      · have hpos := one_le_collisionCountNat_of_not_injective (Fin N) hy
        have hne : collisionCountNat (Fin N) q y ≠ 0 := by omega
        simp [hy, hne]
    _ = birthdayProduct N q := by
      simpa using collisionFreeProbability_eq_birthdayProduct (Fin N) q

/-- Changing the count by an integer amount changes any adjacent atom
indicator by at most the absolute count error. -/
theorem one_le_abs_natCast_sub_of_ne
    {a b : Nat} (hab : a ≠ b) :
    (1 : Real) ≤ |(a : Real) - (b : Real)| := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rw [abs_of_nonpos]
    · have hgap : (a : Real) + 1 ≤ (b : Real) := by
        exact_mod_cast hablt
      linarith
    · have hle : (a : Real) ≤ (b : Real) := Nat.cast_le.mpr hablt.le
      linarith
  · rw [abs_of_nonneg]
    · have hgap : (b : Real) + 1 ≤ (a : Real) := by
        exact_mod_cast hbalt
      linarith
    · have hle : (b : Real) ≤ (a : Real) := Nat.cast_le.mpr hbalt.le
      linarith

theorem abs_shifted_atomIndicator_sub_le
    (a b k : Nat) :
    |(if a = k + 1 then 1 else 0 : Real) -
        (if b = k then 1 else 0 : Real)| ≤
      |(a : Real) - (b : Real) - 1| := by
  by_cases ha : a = k + 1 <;> by_cases hb : b = k
  · subst a
    subst b
    norm_num
  · subst a
    simp only [if_neg hb, sub_zero]
    have hgap := one_le_abs_natCast_sub_of_ne (a := k) (b := b) (Ne.symm hb)
    convert hgap using 1 <;> push_cast <;> ring
  · subst b
    simp only [if_neg ha, zero_sub, abs_neg]
    have hgap := one_le_abs_natCast_sub_of_ne (a := a) (b := k + 1) ha
    convert hgap using 1 <;> push_cast <;> ring
  · simp [ha, hb]

/-- One planted edge shifts every fixed collision atom by one, up to the
local third-coordinate planting error. -/
theorem abs_planted_atom_sub_collisionAtom_le
    {N q : Nat} (hN : 0 < N) (e : Edge q) (k : Nat) :
    |uniformAverage (Fin q → Fin N) (fun y =>
        if collisionCountNat (Fin N) q (plantCollision e y) = k + 1 then 1 else 0) -
      collisionAtom N q k| ≤
      (1 + 8 * (q : Real)) / (N : Real) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  unfold collisionAtom
  rw [← uniformAverage_sub]
  calc
    |uniformAverage (Fin q → Fin N) (fun y =>
        (if collisionCountNat (Fin N) q (plantCollision e y) = k + 1 then 1 else 0) -
          (if collisionCountNat (Fin N) q y = k then 1 else 0))| ≤
      uniformAverage (Fin q → Fin N) (fun y =>
        |(if collisionCountNat (Fin N) q (plantCollision e y) = k + 1 then 1 else 0) -
          (if collisionCountNat (Fin N) q y = k then 1 else 0)|) := by
            exact abs_uniformAverage_le_uniformAverage_abs _
    _ ≤ uniformAverage (Fin q → Fin N) (fun y =>
        |collisionCount (Fin N) q (plantCollision e y) -
          collisionCount (Fin N) q y - 1|) := by
            apply uniformAverage_mono
            intro y
            rw [collisionCount_eq_natCast, collisionCount_eq_natCast]
            exact abs_shifted_atomIndicator_sub_le _ _ k
    _ ≤ (1 + 8 * (q : Real)) / (N : Real) := by
      simpa using uniformAverage_abs_collisionCount_plantCollision_sub_le
        (Fin N) e

/-- Finite approximate Poisson recurrence for every collision-count atom. -/
theorem abs_collisionAtom_succ_recurrence_le
    {N q : Nat} (hN : 0 < N) (k : Nat) :
    |((k + 1 : Nat) : Real) * collisionAtom N q (k + 1) -
        birthdayRate N q * collisionAtom N q k| ≤
      birthdayRate N q * ((1 + 8 * (q : Real)) / (N : Real)) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hsize := collisionAtom_sizeBias (q := q) hN (k + 1)
  have hNR : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  have hrewrite :
      ((k + 1 : Nat) : Real) * collisionAtom N q (k + 1) -
          birthdayRate N q * collisionAtom N q k =
        (1 / (N : Real)) * ∑ e : Edge q,
          (uniformAverage (Fin q → Fin N) (fun y =>
              if collisionCountNat (Fin N) q (plantCollision e y) = k + 1
              then 1 else 0) - collisionAtom N q k) := by
    rw [hsize]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold birthdayRate edgeCount
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (by positivity :
    0 ≤ (1 / (N : Real)))]
  calc
    (1 / (N : Real)) *
        |∑ e : Edge q,
          (uniformAverage (Fin q → Fin N) (fun y =>
              if collisionCountNat (Fin N) q (plantCollision e y) = k + 1
              then 1 else 0) - collisionAtom N q k)| ≤
      (1 / (N : Real)) *
        ∑ e : Edge q,
          |uniformAverage (Fin q → Fin N) (fun y =>
              if collisionCountNat (Fin N) q (plantCollision e y) = k + 1
              then 1 else 0) - collisionAtom N q k| := by
            gcongr
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 / (N : Real)) *
        ∑ _e : Edge q,
          ((1 + 8 * (q : Real)) / (N : Real)) := by
            gcongr with e
            exact abs_planted_atom_sub_collisionAtom_le hN e k
    _ = birthdayRate N q * ((1 + 8 * (q : Real)) / (N : Real)) := by
      unfold birthdayRate edgeCount
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hNR]

/-- The finite recurrence error vanishes throughout every fixed birthday-rate
window. -/
theorem tendsto_collisionAtom_recurrenceError_zero
    (N q : Nat → Nat) (r : Real)
    (hN : Tendsto N atTop atTop)
    (hrate : Tendsto (fun t => birthdayRate (N t) (q t))
      atTop (nhds r))
    (hsmall : Tendsto (fun t => (q t : Real) / (N t : Real))
      atTop (nhds 0)) :
    Tendsto (fun t => birthdayRate (N t) (q t) *
        ((1 + 8 * (q t : Real)) / (N t : Real)))
      atTop (nhds 0) := by
  have hNreal : Tendsto (fun t => (N t : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hinv : Tendsto (fun t => (1 : Real) / (N t : Real))
      atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hNreal
  have heps : Tendsto (fun t =>
      (1 + 8 * (q t : Real)) / (N t : Real)) atTop (nhds 0) := by
    have h8 : Tendsto (fun _t : Nat => (8 : Real)) atTop (nhds 8) :=
      tendsto_const_nhds
    have height : Tendsto (fun t => (8 : Real) *
        ((q t : Real) / (N t : Real))) atTop (nhds 0) :=
      by simpa using h8.mul hsmall
    have hadd := hinv.add height
    convert hadd using 1
    · funext t
      ring
    · ring
  simpa using hrate.mul heps

/-- Every fixed collision-count atom converges to its Poisson atom.  The proof
is induction along the planted-collision size-bias recurrence. -/
theorem tendsto_collisionAtom_poissonPMFReal
    (N q : Nat → Nat) (r : NNReal) (k : Nat)
    (hN : Tendsto N atTop atTop)
    (h2q : ∀ᶠ t in atTop, 2 * q t ≤ N t)
    (hrate : Tendsto (fun t => birthdayRate (N t) (q t))
      atTop (nhds (r : Real)))
    (hsmall : Tendsto (fun t => (q t : Real) / (N t : Real))
      atTop (nhds 0)) :
    Tendsto (fun t => collisionAtom (N t) (q t) k)
      atTop (nhds (poissonPMFReal r k)) := by
  have hNpos : ∀ᶠ t in atTop, 0 < N t := by
    have hge : ∀ᶠ t in atTop, 1 ≤ N t :=
      hN (eventually_ge_atTop 1)
    filter_upwards [hge] with t ht
    omega
  have herr := tendsto_collisionAtom_recurrenceError_zero
    N q (r : Real) hN hrate hsmall
  induction k with
  | zero =>
      have hprod := tendsto_birthdayProduct_exp_neg
        N q (r : Real) hN h2q hrate hsmall
      have hatom : Tendsto (fun t => collisionAtom (N t) (q t) 0)
          atTop (nhds (Real.exp (-(r : Real)))) := by
        apply hprod.congr'
        filter_upwards [hNpos] with t hNt
        exact (collisionAtom_zero_eq_birthdayProduct hNt).symm
      simpa [poissonPMFReal] using hatom
  | succ k ih =>
      let residual : Nat → Real := fun t =>
        (((k + 1 : Nat) : Real) * collisionAtom (N t) (q t) (k + 1) -
          birthdayRate (N t) (q t) * collisionAtom (N t) (q t) k)
      have habs : Tendsto (fun t => |residual t|) atTop (nhds 0) := by
        apply squeeze_zero'
        · exact Eventually.of_forall (fun t => abs_nonneg _)
        · filter_upwards [hNpos] with t hNt
          exact abs_collisionAtom_succ_recurrence_le hNt k
        · exact herr
      have hres : Tendsto residual atTop (nhds 0) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        simpa [Real.norm_eq_abs, residual] using habs
      have hscaled : Tendsto (fun t =>
          (((k + 1 : Nat) : Real) * collisionAtom (N t) (q t) (k + 1)))
          atTop (nhds (((k + 1 : Nat) : Real) * poissonPMFReal r (k + 1))) := by
        have hsum := hres.add (hrate.mul ih)
        convert hsum using 1
        · funext t
          dsimp [residual]
          ring
        · rw [zero_add, poissonPMFReal_succ_recurrence]
      have hcoef : (((k + 1 : Nat) : Real)) ≠ 0 := by positivity
      convert hscaled.div_const (((k + 1 : Nat) : Real)) using 1
      · funext t
        field_simp [hcoef]
      · field_simp [hcoef]

theorem abs_sub_eq_sub_add_two_mul_max_sub (x r : Real) :
    |x - r| = (x - r) + 2 * max (r - x) 0 := by
  rcases le_total x r with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr h), max_eq_right (sub_nonpos.mpr h)]
    ring

/-- A lower deficiency is a finite sum of atom indicators once the cutoff is
strictly above the center. -/
theorem max_sub_natCast_eq_sum_atomIndicators
    {r : Real} {m : Nat} (hr : r < (m + 1 : Nat)) (a : Nat) :
    max (r - (a : Real)) 0 =
      ∑ k ∈ Finset.range (m + 1),
        max (r - (k : Real)) 0 * (if a = k then 1 else 0 : Real) := by
  by_cases ha : a < m + 1
  · rw [Finset.sum_eq_single a]
    · simp
    · intro k hk hka
      simp [Ne.symm hka]
    · simp [ha]
  · have hma : m + 1 ≤ a := Nat.le_of_not_gt ha
    have hra : r ≤ (a : Real) := by
      have hcast : ((m + 1 : Nat) : Real) ≤ (a : Real) := by
        exact_mod_cast hma
      exact hr.le.trans hcast
    rw [max_eq_right (sub_nonpos.mpr hra)]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hka : a ≠ k := by
      have hkm : k < m + 1 := Finset.mem_range.mp hk
      omega
    simp [hka]

/-- Exact finite lower-tail formula for the collision-count mean absolute
deviation.  The `max` makes the formula stable when the center crosses an
integer. -/
theorem finiteCollisionMAD_eq_sum_max_collisionAtom
    {N q m : Nat} (hN : 0 < N)
    (hcut : birthdayRate N q < (m + 1 : Nat)) :
    finiteCollisionMAD N q =
      2 * ∑ k ∈ Finset.range (m + 1),
        max (birthdayRate N q - (k : Real)) 0 * collisionAtom N q k := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hmean : collisionMean (Fin N) q = birthdayRate N q := by
    simp [collisionMean, birthdayRate]
  unfold finiteCollisionMAD
  rw [show (fun y : Fin q → Fin N =>
      |centeredCollisionCount (Fin N) q y|) =
      (fun y => centeredCollisionCount (Fin N) q y +
        2 * max (birthdayRate N q - collisionCount (Fin N) q y) 0) by
      funext y
      unfold centeredCollisionCount
      rw [hmean]
      exact abs_sub_eq_sub_add_two_mul_max_sub _ _]
  rw [uniformAverage_add,
    uniformAverage_centeredCollisionCount_eq_zero (Fin N) q,
    zero_add]
  calc
    uniformAverage (Fin q → Fin N) (fun y =>
        2 * max (birthdayRate N q - collisionCount (Fin N) q y) 0) =
      2 * uniformAverage (Fin q → Fin N) (fun y =>
        max (birthdayRate N q - collisionCount (Fin N) q y) 0) := by
          rw [uniformAverage_const_mul]
    _ = 2 * uniformAverage (Fin q → Fin N) (fun y =>
        ∑ k ∈ Finset.range (m + 1),
          max (birthdayRate N q - (k : Real)) 0 *
            (if collisionCountNat (Fin N) q y = k then 1 else 0 : Real)) := by
          congr 1
          apply uniformAverage_congr
          intro y
          rw [collisionCount_eq_natCast]
          exact max_sub_natCast_eq_sum_atomIndicators hcut _
    _ = 2 * ∑ k ∈ Finset.range (m + 1),
        uniformAverage (Fin q → Fin N) (fun y =>
          max (birthdayRate N q - (k : Real)) 0 *
            (if collisionCountNat (Fin N) q y = k then 1 else 0 : Real)) := by
          rw [uniformAverage_finset_sum_over_finite (Finset.range (m + 1))]
    _ = 2 * ∑ k ∈ Finset.range (m + 1),
        max (birthdayRate N q - (k : Real)) 0 * collisionAtom N q k := by
          congr 1
          apply Finset.sum_congr rfl
          intro k _hk
          rw [uniformAverage_const_mul]
          rfl

/-- Finite Poisson lower-deficiency telescope. -/
theorem poisson_lower_deficiency_sum (r : NNReal) (m : Nat) :
    (∑ k ∈ Finset.range (m + 1),
      ((r : Real) - (k : Real)) * poissonPMFReal r k) =
      (r : Real) * poissonPMFReal r m := by
  calc
    (∑ k ∈ Finset.range (m + 1),
        ((r : Real) - (k : Real)) * poissonPMFReal r k) =
      (r : Real) *
          (∑ k ∈ Finset.range (m + 1), poissonPMFReal r k) -
        ∑ k ∈ Finset.range (m + 1),
          (k : Real) * poissonPMFReal r k := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (r : Real) *
          ((∑ k ∈ Finset.range m, poissonPMFReal r k) +
            poissonPMFReal r m) -
        ((∑ k ∈ Finset.range m,
            ((k + 1 : Nat) : Real) * poissonPMFReal r (k + 1)) + 0) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      norm_num
    _ = (r : Real) *
          ((∑ k ∈ Finset.range m, poissonPMFReal r k) +
            poissonPMFReal r m) -
        ∑ k ∈ Finset.range m,
          (r : Real) * poissonPMFReal r k := by
      simp only [add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro k _hk
      exact poissonPMFReal_succ_recurrence r k
    _ = (r : Real) * poissonPMFReal r m := by
      rw [← Finset.mul_sum]
      ring

theorem sum_max_poisson_floor_eq (r : NNReal) :
    ∑ k ∈ Finset.range (⌊(r : Real)⌋₊ + 1),
        max ((r : Real) - (k : Real)) 0 * poissonPMFReal r k =
      (r : Real) * poissonPMFReal r ⌊(r : Real)⌋₊ := by
  rw [show (∑ k ∈ Finset.range (⌊(r : Real)⌋₊ + 1),
      max ((r : Real) - (k : Real)) 0 * poissonPMFReal r k) =
      ∑ k ∈ Finset.range (⌊(r : Real)⌋₊ + 1),
        ((r : Real) - (k : Real)) * poissonPMFReal r k by
    apply Finset.sum_congr rfl
    intro k hk
    rw [max_eq_left]
    have hkNat : k ≤ ⌊(r : Real)⌋₊ := by simpa using hk
    have hfloor : (⌊(r : Real)⌋₊ : Real) ≤ (r : Real) :=
      Nat.floor_le (show 0 ≤ (r : Real) by positivity)
    exact sub_nonneg.mpr ((Nat.cast_le.mpr hkNat).trans hfloor)]
  exact poisson_lower_deficiency_sum r ⌊(r : Real)⌋₊

/-- Full fixed-rate Poisson interpolation for the collision-count MAD.  This
includes every rate at least one and strengthens the earlier subunit theorem. -/
theorem tendsto_finiteCollisionMAD_fixedPoisson
    (N q : Nat → Nat) (r : NNReal)
    (hN : Tendsto N atTop atTop)
    (h2q : ∀ᶠ t in atTop, 2 * q t ≤ N t)
    (hrate : Tendsto (fun t => birthdayRate (N t) (q t))
      atTop (nhds (r : Real)))
    (hsmall : Tendsto (fun t => (q t : Real) / (N t : Real))
      atTop (nhds 0)) :
    Tendsto (fun t => finiteCollisionMAD (N t) (q t))
      atTop (nhds (fixedPoissonMAD r)) := by
  let m : Nat := ⌊(r : Real)⌋₊
  have hrCut : (r : Real) < ((m + 1 : Nat) : Real) := by
    dsimp [m]
    simpa using Nat.lt_floor_add_one (r : Real)
  have hcut : ∀ᶠ t in atTop,
      birthdayRate (N t) (q t) < ((m + 1 : Nat) : Real) :=
    hrate (Iio_mem_nhds hrCut)
  have hNpos : ∀ᶠ t in atTop, 0 < N t := by
    have hge : ∀ᶠ t in atTop, 1 ≤ N t :=
      hN (eventually_ge_atTop 1)
    filter_upwards [hge] with t ht
    omega
  have hzero : Tendsto (fun _t : Nat => (0 : Real)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hsum : Tendsto (fun t =>
      ∑ k ∈ Finset.range (m + 1),
        max (birthdayRate (N t) (q t) - (k : Real)) 0 *
          collisionAtom (N t) (q t) k) atTop
      (nhds (∑ k ∈ Finset.range (m + 1),
        max ((r : Real) - (k : Real)) 0 * poissonPMFReal r k)) := by
    apply tendsto_finset_sum
    intro k hk
    have hmax : Tendsto (fun t =>
        max (birthdayRate (N t) (q t) - (k : Real)) 0) atTop
        (nhds (max ((r : Real) - (k : Real)) 0)) :=
      (hrate.sub_const (k : Real)).max hzero
    exact hmax.mul (tendsto_collisionAtom_poissonPMFReal
      N q r k hN h2q hrate hsmall)
  have htwo : Tendsto (fun _t : Nat => (2 : Real)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hscaled := htwo.mul hsum
  have htarget :
      2 * (∑ k ∈ Finset.range (m + 1),
        max ((r : Real) - (k : Real)) 0 * poissonPMFReal r k) =
        fixedPoissonMAD r := by
    dsimp [m]
    rw [sum_max_poisson_floor_eq]
    unfold fixedPoissonMAD
    ring
  have hlimit : Tendsto (fun t =>
      2 * ∑ k ∈ Finset.range (m + 1),
        max (birthdayRate (N t) (q t) - (k : Real)) 0 *
          collisionAtom (N t) (q t) k)
      atTop (nhds (fixedPoissonMAD r)) := by
    rw [← htarget]
    exact hscaled
  apply hlimit.congr'
  filter_upwards [hNpos, hcut] with t hNt hcutT
  exact (finiteCollisionMAD_eq_sum_max_collisionAtom hNt hcutT).symm

/-- The fixed-rate limiting constant after multiplying the collision-proxy
advantage by the alphabet size. -/
def fixedPoissonAdvantageConstant (r : NNReal) : Real :=
  (r : Real) * poissonPMFReal r ⌊(r : Real)⌋₊

theorem fixedPoissonAdvantageConstant_eq_half_mul_fixedPoissonMAD
    (r : NNReal) :
    fixedPoissonAdvantageConstant r = (1 / 2 : Real) * fixedPoissonMAD r := by
  unfold fixedPoissonAdvantageConstant fixedPoissonMAD
  ring

/-- Sharp fixed-rate interpolation for the finite collision proxy.  At every
fixed Poisson rate `r`, its advantage is asymptotic to
`r * Pr[Poisson(r) = floor r] / N`. -/
theorem tendsto_card_mul_finiteCollisionProxyAdvantage_fixedPoisson
    (N q : Nat → Nat) (r : NNReal)
    (hN : Tendsto N atTop atTop)
    (h2q : ∀ᶠ t in atTop, 2 * q t ≤ N t)
    (hrate : Tendsto (fun t => birthdayRate (N t) (q t))
      atTop (nhds (r : Real)))
    (hsmall : Tendsto (fun t => (q t : Real) / (N t : Real))
      atTop (nhds 0)) :
    Tendsto (fun t => (N t : Real) *
        finiteCollisionProxyAdvantage (N t) (q t))
      atTop (nhds (fixedPoissonAdvantageConstant r)) := by
  have hmad := tendsto_finiteCollisionMAD_fixedPoisson
    N q r hN h2q hrate hsmall
  have hNtwo : ∀ᶠ t in atTop, 2 ≤ N t :=
    hN (eventually_ge_atTop 2)
  have hsub : Tendsto (fun t => N t - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hN
  have hsubReal : Tendsto (fun t => ((N t - 1 : Nat) : Real))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hsub
  have hinv : Tendsto (fun t => (1 : Real) / ((N t - 1 : Nat) : Real))
      atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hsubReal
  have hratio : Tendsto
      (fun t => (N t : Real) / ((N t - 1 : Nat) : Real))
      atTop (nhds 1) := by
    have hadd := (tendsto_const_nhds :
      Tendsto (fun _t : Nat => (1 : Real)) atTop (nhds 1)).add hinv
    have hadd' : Tendsto
        (fun t => (1 : Real) + 1 / ((N t - 1 : Nat) : Real))
        atTop (nhds 1) := by simpa using hadd
    apply hadd'.congr'
    filter_upwards [hNtwo] with t hNt
    rw [Nat.cast_sub (by omega : 1 ≤ N t)]
    have hden : (N t : Real) - 1 ≠ 0 := by
      have hNtReal : (2 : Real) ≤ (N t : Real) := by exact_mod_cast hNt
      linarith
    field_simp [hden]
    ring
  have hhalf : Tendsto (fun _t : Nat => (1 / 2 : Real))
      atTop (nhds (1 / 2 : Real)) := tendsto_const_nhds
  have hcoef := hhalf.mul (hratio.pow 2)
  have hproduct := hcoef.mul hmad
  rw [fixedPoissonAdvantageConstant_eq_half_mul_fixedPoissonMAD]
  have hproduct' : Tendsto (fun t =>
      (1 / 2 : Real) *
        ((N t : Real) / ((N t - 1 : Nat) : Real)) ^ 2 *
          finiteCollisionMAD (N t) (q t))
      atTop (nhds ((1 / 2 : Real) * fixedPoissonMAD r)) := by
    simpa using hproduct
  apply hproduct'.congr'
  filter_upwards [hNtwo] with t hNt
  unfold finiteCollisionProxyAdvantage
  have hden : ((N t - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt hNt)
  field_simp [hden]

end RandomSystems.SoP.CollisionCountPoissonFixed
