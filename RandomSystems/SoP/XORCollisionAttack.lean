/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORSignedDegreeThree

/-!
# Explicit matching collision attack for the signed degree-three SoP bound

A nonadaptive distinguisher queries a fixed fresh schedule and returns
"real" exactly when two visible answers collide.  This module proves that its
signed acceptance gap differs from the degree-three main term by at most the
same level-four tail used in the upper bound.  Thus the closed certificate is
two-sided for a concrete elementary test, not only for an abstract optimal
distinguisher.
-/

noncomputable section
open scoped BigOperators

namespace RandomSystems.SoP.XORSignedDegreeThree

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORSignedTruncation
open RandomSystems.Applications.SoP
open RandomSystems.Applications.XoP.ANOVA

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem abs_average_indicator_le_half_average_abs_of_average_eq_zero
    {A : Type*} [Fintype A] [Nonempty A]
    (p : A → Prop) [DecidablePred p] (f : A → Real)
    (hmean : average A f = 0) :
    |average A (fun x => if p x then f x else 0)| ≤
      (1 / 2 : Real) * average A (fun x => |f x|) := by
  let fp : A → Real := fun x => if p x then f x else 0
  let fn : A → Real := fun x => if p x then 0 else f x
  have hsplit : (fun x => f x) = (fun x => fp x + fn x) := by
    funext x
    by_cases hx : p x <;> simp [fp, fn, hx]
  have hmeansplit : average A fp + average A fn = 0 := by
    rw [← average_add, ← hsplit]
    exact hmean
  have habsEq : |average A fp| = |average A fn| := by
    have hneg : average A fn = -average A fp := by linarith
    rw [hneg, abs_neg]
  have hp : |average A fp| ≤ average A (fun x => |fp x|) := by
    unfold average
    rw [abs_div]
    have hcard : 0 ≤ (Fintype.card A : Real) := by positivity
    rw [abs_of_nonneg hcard]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcard
  have hn : |average A fn| ≤ average A (fun x => |fn x|) := by
    unfold average
    rw [abs_div]
    have hcard : 0 ≤ (Fintype.card A : Real) := by positivity
    rw [abs_of_nonneg hcard]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcard
  have hparts :
      average A (fun x => |fp x|) + average A (fun x => |fn x|) =
        average A (fun x => |f x|) := by
    rw [← average_add]
    congr 1
    funext x
    by_cases hx : p x <;> simp [fp, fn, hx]
  have htwice :
      2 * |average A (fun x => if p x then f x else 0)| ≤
        average A (fun x => |f x|) := by
    dsimp [fp] at hp habsEq
    rw [← hparts]
    nlinarith
  linarith

theorem average_signed_tail_density_eq_zero
    {n q r : Nat} (hr : 2 ≤ r) (hq : q ≤ 2 ^ n) :
    average (BitMatrix q n) (signedTailDensity n q r) = 0 := by
  have hfull : average (BitMatrix q n)
      (visibleDensityErrorReal (G := XorSpace n) (q := q)) = 0 := by
    simpa [average, uniformAverage] using
      (uniformAverage_xopError_eq_zero
        (G := XorSpace n) (q := q) (by simpa [card_xorSpace] using hq))
  have hpoint :
      visibleDensityErrorReal (G := XorSpace n) (q := q) =
        (fun y => signedTruncationDensity n q r y +
          signedTailDensity n q r y) := by
    funext y
    exact visible_density_error_real_eq_signed_truncation_add_tail hr hq y
  rw [hpoint, average_add,
    average_signed_truncation_density_eq_zero] at hfull
  simpa using hfull

/-- Signed acceptance gap of the concrete test that makes `q` fixed fresh
queries and answers "real" exactly when two visible answers collide. -/
def visibleCollisionDecision {n q : Nat} (y : BitMatrix q n) : Bool :=
  decide (¬Function.Injective y)

@[simp]
theorem visible_collision_decision_eq_true_iff
    {n q : Nat} (y : BitMatrix q n) :
    visibleCollisionDecision y = true ↔ ¬Function.Injective y := by
  simp [visibleCollisionDecision]

def visibleCollisionTestGap (n q : Nat) : Real :=
  average (BitMatrix q n) (fun y =>
    if Function.Injective y then 0
    else visibleDensityErrorReal (G := XorSpace n) (q := q) y)

theorem average_signed_truncation_four_on_collision_eq_main_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    average (BitMatrix q n) (fun y =>
      if Function.Injective y then 0
      else signedTruncationDensity n q 4 y) =
        signedDegreeThreeMain n q := by
  have hN6 : 6 ≤ 2 ^ n := by
    have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have hq : q ≤ 2 ^ n := by omega
  obtain ⟨hneg, hpos⟩ :=
    signed_degree_three_sign_conditions_of_sparse hN6 h2q h2pairs
  have hhalf := half_average_abs_eq_neg_average_on
    (fun y : BitMatrix q n => Function.Injective y)
    (signedTruncationDensity n q 4)
    (average_signed_truncation_density_eq_zero n q 4)
    (signed_truncation_density_four_nonpos_of_injective (by omega) hq hneg)
    (signed_truncation_density_four_nonneg_of_not_injective (by omega) hq hpos)
  have hinj :
      -average (BitMatrix q n) (fun y =>
        if Function.Injective y then signedTruncationDensity n q 4 y else 0) =
          signedDegreeThreeMain n q := by
    calc
      -average (BitMatrix q n) (fun y =>
          if Function.Injective y then signedTruncationDensity n q 4 y else 0) =
          signedTruncationAdvantage n q 4 := by
        symm
        exact hhalf
      _ = signedDegreeThreeMain n q :=
        signed_truncation_advantage_four_eq_signed_degree_three_main
          (by omega) hq hneg hpos
  have hsplit :
      average (BitMatrix q n) (signedTruncationDensity n q 4) =
        average (BitMatrix q n) (fun y =>
          if Function.Injective y then signedTruncationDensity n q 4 y else 0) +
        average (BitMatrix q n) (fun y =>
          if Function.Injective y then 0 else signedTruncationDensity n q 4 y) := by
    rw [← average_add]
    congr 1
    funext y
    by_cases hy : Function.Injective y <;> simp [hy]
  rw [average_signed_truncation_density_eq_zero] at hsplit
  linarith

theorem visible_collision_test_gap_eq_main_add_tail_event_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    visibleCollisionTestGap n q =
      signedDegreeThreeMain n q +
        average (BitMatrix q n) (fun y =>
          if Function.Injective y then 0 else signedTailDensity n q 4 y) := by
  have hq : q ≤ 2 ^ n := by omega
  unfold visibleCollisionTestGap
  have hpoint :
      (fun y : BitMatrix q n =>
        if Function.Injective y then 0
        else visibleDensityErrorReal (G := XorSpace n) (q := q) y) =
      (fun y =>
        (if Function.Injective y then 0 else signedTruncationDensity n q 4 y) +
        (if Function.Injective y then 0 else signedTailDensity n q 4 y)) := by
    funext y
    by_cases hy : Function.Injective y
    · simp [hy]
    · simp only [hy, ↓reduceIte]
      exact visible_density_error_real_eq_signed_truncation_add_tail
        (by omega) hq y
  rw [hpoint, average_add,
    average_signed_truncation_four_on_collision_eq_main_sparse
      hn h2q h2pairs]

theorem abs_visible_collision_test_gap_sub_main_le_error_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    |visibleCollisionTestGap n q - signedDegreeThreeMain n q| ≤
      signedDegreeThreeError n q := by
  rw [visible_collision_test_gap_eq_main_add_tail_event_sparse
    hn h2q h2pairs]
  ring_nf
  calc
    |average (BitMatrix q n) (fun y =>
        if Function.Injective y then 0 else signedTailDensity n q 4 y)| ≤
        (1 / 2 : Real) * average (BitMatrix q n)
          (fun y => |signedTailDensity n q 4 y|) := by
      have hevent :
          (fun y : BitMatrix q n =>
            if ¬Function.Injective y then signedTailDensity n q 4 y else 0) =
          (fun y =>
            if Function.Injective y then 0 else signedTailDensity n q 4 y) := by
        funext y
        by_cases hy : Function.Injective y <;> simp [hy]
      rw [← hevent]
      exact abs_average_indicator_le_half_average_abs_of_average_eq_zero
        (fun y : BitMatrix q n => ¬Function.Injective y)
        (signedTailDensity n q 4)
        (average_signed_tail_density_eq_zero (by omega) (by omega))
    _ = signedTailAdvantage n q 4 := rfl
    _ ≤ signedTailErrorBound n q 4 :=
      signed_tail_advantage_le_error_bound hn h2q (by omega) (by omega)
    _ = signedDegreeThreeError n q :=
      signed_tail_error_bound_four_eq_signed_degree_three_error n q

theorem visible_mass_sub_eq_density_error_div_card
    {n q : Nat} (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    (realVisibleDist (G := XorSpace n) (q := q) y : Real) -
        (idealVisibleDist (G := XorSpace n) (q := q) y : Real) =
      visibleDensityErrorReal (G := XorSpace n) (q := q) y /
        (Fintype.card (BitMatrix q n) : Real) := by
  rw [realVisibleDist_apply, idealVisibleDist_apply,
    realVisibleMass_eq, idealVisibleMass_eq]
  unfold visibleDensityErrorReal visibleDensityRatioReal
  have hcardTape : Fintype.card (BitMatrix q n) = (2 ^ n) ^ q := by
    simp [BitMatrix]
  rw [hcardTape]
  simp only [NNReal.coe_div,
    Nat.cast_pow, card_xorSpace, Nat.cast_mul]
  have hN : (0 : Real) < 2 ^ n := by positivity
  have hpow : (0 : Real) < ((2 ^ n : Nat) : Real) ^ q := by positivity
  have hdescNat : 0 < (2 ^ n).descFactorial q :=
    Nat.descFactorial_pos.mpr hq
  have hdesc : (0 : Real) < ((2 ^ n).descFactorial q : Nat) := by
    exact_mod_cast hdescNat
  field_simp [hpow.ne', hdesc.ne']
  norm_num [Nat.cast_pow]
  ring

theorem visible_collision_test_gap_eq_visible_mass_gap
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    visibleCollisionTestGap n q =
      (realVisibleDist (G := XorSpace n) (q := q)).mass
          (fun y => ¬Function.Injective y) -
        (idealVisibleDist (G := XorSpace n) (q := q)).mass
          (fun y => ¬Function.Injective y) := by
  unfold visibleCollisionTestGap average
  rw [Dist.mass_eq_sum, Dist.mass_eq_sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  rw [show
      (∑ y : BitMatrix q n,
          if Function.Injective y then 0
          else visibleDensityErrorReal (G := XorSpace n) (q := q) y) /
          (Fintype.card (BitMatrix q n) : Real) =
        ∑ y : BitMatrix q n,
          (if Function.Injective y then 0
          else visibleDensityErrorReal (G := XorSpace n) (q := q) y) /
            (Fintype.card (BitMatrix q n) : Real) by
      rw [Finset.sum_div]]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hinj : Function.Injective y
  · simp [hinj]
  · simp only [hinj, ↓reduceIte, not_false_eq_true]
    exact (visible_mass_sub_eq_density_error_div_card hq y).symm

/-- The concrete collision decision is a legitimate nonadaptive test inside
the adaptive advantage.  A fresh fixed schedule exposes exactly the two
visible tape laws used in this mass gap. -/
theorem visible_collision_test_gap_le_adaptive_advantage
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    visibleCollisionTestGap n q ≤
      RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (RandomSystems.SoP.xop (XorSpace n))
          (RandomSystems.SoP.urf (XorSpace n)) := by
  rw [visible_collision_test_gap_eq_visible_mass_gap hq,
    RandomSystems.SoP.adv_prf_eq_visible_stat_dist_of_le_card]
  · exact RandomSystems.mass_sub_mass_le_statDist
      (realVisibleDist (G := XorSpace n) (q := q))
      (idealVisibleDist (G := XorSpace n) (q := q))
      (fun y => ¬Function.Injective y)
  · simpa [card_xorSpace] using hq

/-- Matching operational lower bound: the elementary collision test reaches
the signed main term up to exactly the same certified tail as the upper
bound. -/
theorem signed_degree_three_main_sub_error_le_collision_test_gap_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    signedDegreeThreeMain n q - signedDegreeThreeError n q ≤
      visibleCollisionTestGap n q := by
  have h := (abs_le.mp
    (abs_visible_collision_test_gap_sub_main_le_error_sparse
      hn h2q h2pairs)).1
  linarith

theorem signed_degree_three_main_sub_error_le_adaptive_advantage_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    signedDegreeThreeMain n q - signedDegreeThreeError n q ≤
      RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (RandomSystems.SoP.xop (XorSpace n))
          (RandomSystems.SoP.urf (XorSpace n)) := by
  exact le_trans
    (signed_degree_three_main_sub_error_le_collision_test_gap_sparse
      hn h2q h2pairs)
    (visible_collision_test_gap_le_adaptive_advantage (by omega))

end RandomSystems.SoP.XORSignedDegreeThree

