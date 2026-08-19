/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.XoPAnalytic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# XoP ANOVA Scaffold

This file starts XOP-DAG-10.  The goal is to expose the finite-product
Hoeffding/ANOVA objects used by the visible analytic proof, while keeping the
signed decomposition over `ℝ` separate from the nonnegative `NNReal`
probability/counting bridge.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace XoP
namespace ANOVA

open Combinatorics

variable {G : Type*} {q : Nat}

/-- The full coordinate set for a `q`-query visible tuple. -/
def coordinates (q : Nat) : Finset (Fin q) :=
  Finset.univ

/-- Restrict a visible tuple to a finite coordinate set. -/
def restrictTuple (S : Finset (Fin q)) (y : Fin q → G) :
    { i : Fin q // i ∈ S } → G :=
  fun i => y i.1

/-- Uniform finite average of a real-valued function. -/
def uniformAverage (α : Type*) [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x : α, f x) / (Fintype.card α : ℝ)

/-- Fiberwise conditional average over full visible tuples with fixed
coordinates on `S`. -/
def conditionalAverage [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ)
    (z : { i : Fin q // i ∈ S } → G) : ℝ :=
  uniformAverage { y : Fin q → G // restrictTuple S y = z } (fun y => f y.1)

/-- Conditional expectation/projection onto coordinates in `S`. -/
def project [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) : (Fin q → G) → ℝ :=
  fun y => conditionalAverage S f (restrictTuple S y)

/-- Hoeffding/ANOVA component indexed by `S`, written by explicit finite
subset-lattice Möbius inversion. -/
def anovaComponent [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) : (Fin q → G) → ℝ :=
  fun y => ∑ T ∈ S.powerset,
    ((-1 : ℝ) ^ (S.card - T.card)) * project T f y

/-- Visible-product `L¹` norm under the uniform law. -/
def visibleL1 [Fintype G] (f : (Fin q → G) → ℝ) : ℝ :=
  uniformAverage (Fin q → G) (fun y => |f y|)

/-- Correct XoP visible-count normalizer `(N)_q^2 / N^q`, as an `NNReal`. -/
def visibleNormalizerNNReal [Fintype G] : NNReal :=
  (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) : NNReal) /
    (((Fintype.card G ^ q : Nat) : NNReal))

/-- Real-valued reciprocal slack associated with the XoP visible-count
normalizer.  Scalar activity estimates use this factor before it is bounded by
a query-regime-specific constant. -/
def visibleNormalizerSlackReal (G : Type*) [Fintype G] (q : Nat) : ℝ :=
  (Fintype.card G : ℝ) ^ q / (visibleNormalizerNNReal (G := G) (q := q) : ℝ)

theorem visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq
    [Fintype G] [Nonempty G] (hq : q ≤ Fintype.card G) :
    visibleNormalizerSlackReal G q =
      ((Fintype.card G : ℝ) ^ (2 * q)) /
        (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) : ℝ) := by
  unfold visibleNormalizerSlackReal visibleNormalizerNNReal
  let N : ℝ := Fintype.card G
  let D : ℝ := ((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := G)
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hD_pos : 0 < D := by
    dsimp [D]
    have hdesc_pos : 0 < (Fintype.card G).descFactorial q := Nat.descFactorial_pos.mpr hq
    exact_mod_cast Nat.mul_pos hdesc_pos hdesc_pos
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hpow_cast : (((Fintype.card G ^ q : Nat) : NNReal) : ℝ) = N ^ q := by
    dsimp [N]
    norm_num
  have hD_cast :
      ((((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          NNReal) : ℝ) = D := by
    rfl
  rw [NNReal.coe_div]
  rw [hpow_cast, hD_cast]
  rw [show (Fintype.card G : ℝ) = N by rfl]
  rw [show (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
      ℝ) = D by rfl]
  field_simp [hN_ne, hD_ne]
  rw [← pow_mul]
  congr 1
  omega

/-- Convert an ordinary falling-factorial lower bound into a normalizer-slack
bound.  Later analytic work can prove the premise using whatever query regime
is appropriate. -/
theorem visibleNormalizerSlackReal_le_of_pow_le_const_mul_descFactorial_sq
    [Fintype G] [Nonempty G] {C : ℝ} (hq : q ≤ Fintype.card G)
    (hbound : ((Fintype.card G : ℝ) ^ (2 * q)) ≤
      C * (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) : ℝ)) :
    visibleNormalizerSlackReal G q ≤ C := by
  rw [visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq (G := G) (q := q) hq]
  let D : ℝ := ((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat)
  have hD_pos : 0 < D := by
    dsimp [D]
    have hdesc_pos : 0 < (Fintype.card G).descFactorial q := Nat.descFactorial_pos.mpr hq
    exact_mod_cast Nat.mul_pos hdesc_pos hdesc_pos
  have hbound' : ((Fintype.card G : ℝ) ^ (2 * q)) ≤ C * D := by
    simpa [D] using hbound
  exact (div_le_iff₀ hD_pos).mpr (by simpa [mul_comm] using hbound')

/-- Under the small-query regime `q(q-1) ≤ N`, the domain has enough points to
support `q` distinct queries.  This is the arithmetic side condition needed by
falling-factorial normalizer estimates. -/
theorem query_le_of_queryPair_le_card (N q : Nat)
    (hN : 0 < N) (hsmall : q * (q - 1) ≤ N) :
    q ≤ N := by
  cases q with
  | zero => omega
  | succ q =>
      cases q with
      | zero => omega
      | succ q =>
          have hqle : q.succ.succ ≤ q.succ.succ * (q.succ.succ - 1) :=
            Nat.le_mul_of_pos_right _ (by omega)
          exact le_trans hqle hsmall

/-- The falling-factorial ratio `(N)_q / N^q` dominates the first-order
inclusion-exclusion lower bound. -/
theorem descFactorial_div_pow_ge_one_sub_sum (N q : Nat)
    (hN : 0 < N) (hq : q ≤ N) :
    1 - (∑ i ∈ Finset.range q, (i : ℝ) / (N : ℝ)) ≤
      ((N.descFactorial q : Nat) : ℝ) / (N : ℝ) ^ q := by
  have hprod : 1 - (∑ i ∈ Finset.range q, (i : ℝ) / (N : ℝ)) ≤
      ∏ i ∈ Finset.range q, (1 - (i : ℝ) / (N : ℝ)) := by
    refine RandomSystems.CR18.Counting.one_sub_sum_le_prod_one_sub (Finset.range q)
      (fun i : Nat => (i : ℝ) / (N : ℝ)) ?_ ?_
    · intro i hi
      positivity
    · intro i hi
      rw [Finset.mem_range] at hi
      have hiN : i ≤ N := le_trans hi.le hq
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      exact (div_le_one hNreal).mpr (by exact_mod_cast hiN)
  have hprod_eq : (∏ i ∈ Finset.range q, (1 - (i : ℝ) / (N : ℝ))) =
      ((N.descFactorial q : Nat) : ℝ) / (N : ℝ) ^ q := by
    rw [RandomSystems.CR18.Counting.cast_descFactorial_eq_prod hq,
      RandomSystems.CR18.Counting.prod_sub_div_pow_eq N q hN]
  exact hprod.trans_eq hprod_eq

/-- In the regime `q(q-1) ≤ N`, the first-order collision sum is at most
`1/2`. -/
theorem sum_range_div_card_le_half_of_queryPair_le_card (N q : Nat)
    (hN : 0 < N) (hsmall : q * (q - 1) ≤ N) :
    (∑ i ∈ Finset.range q, (i : ℝ) / (N : ℝ)) ≤ (1 / 2 : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have htwosum_nat : (∑ i ∈ Finset.range q, i) * 2 = q * (q - 1) :=
    Finset.sum_range_id_mul_two q
  have hsum_div_eq : (∑ i ∈ Finset.range q, (i : ℝ) / (N : ℝ)) =
      ((∑ i ∈ Finset.range q, i : Nat) : ℝ) / (N : ℝ) := by
    simp [div_eq_mul_inv, Finset.sum_mul]
  rw [hsum_div_eq]
  have hnum_le : ((∑ i ∈ Finset.range q, i : Nat) : ℝ) * 2 ≤ (N : ℝ) := by
    calc
      ((∑ i ∈ Finset.range q, i : Nat) : ℝ) * 2 =
          (((∑ i ∈ Finset.range q, i : Nat) * 2 : Nat) : ℝ) := by norm_num
      _ = ((q * (q - 1) : Nat) : ℝ) := by rw [htwosum_nat]
      _ ≤ (N : ℝ) := by exact_mod_cast hsmall
  exact (div_le_iff₀ hNreal).mpr (by linarith)

/-- Small-query falling-factorial lower bound, stated in the direction needed
for the visible-normalizer slack. -/
theorem pow_le_two_mul_descFactorial_of_queryPair_le_card (N q : Nat)
    (hN : 0 < N) (hsmall : q * (q - 1) ≤ N) :
    (N : ℝ) ^ q ≤ 2 * ((N.descFactorial q : Nat) : ℝ) := by
  have hq : q ≤ N := query_le_of_queryPair_le_card N q hN hsmall
  have hlower := descFactorial_div_pow_ge_one_sub_sum N q hN hq
  have hsum := sum_range_div_card_le_half_of_queryPair_le_card N q hN hsmall
  have hhalf : (1 / 2 : ℝ) ≤
      ((N.descFactorial q : Nat) : ℝ) / (N : ℝ) ^ q := by
    linarith
  have hpow_pos : 0 < (N : ℝ) ^ q := pow_pos (by exact_mod_cast hN) q
  have hmul : (1 / 2 : ℝ) * (N : ℝ) ^ q ≤
      ((N.descFactorial q : Nat) : ℝ) := by
    exact (le_div_iff₀ hpow_pos).mp hhalf
  nlinarith

/-- Adapter from the one-sided falling-factorial lower bound
`N^q ≤ 2 (N)_q` to the squared visible-normalizer slack bound. -/
theorem visibleNormalizerSlackReal_le_four_of_pow_le_two_descFactorial
    (G : Type*) [Fintype G] [Nonempty G] (q : Nat)
    (hq : q ≤ Fintype.card G)
    (hpow : (Fintype.card G : ℝ) ^ q ≤
      2 * (((Fintype.card G).descFactorial q : Nat) : ℝ)) :
    visibleNormalizerSlackReal G q ≤ 4 := by
  refine visibleNormalizerSlackReal_le_of_pow_le_const_mul_descFactorial_sq
    (G := G) (q := q) (C := 4) hq ?_
  let D : ℝ := (((Fintype.card G).descFactorial q : Nat) : ℝ)
  have hD_nonneg : 0 ≤ D := by dsimp [D]; positivity
  have hpow_nonneg : 0 ≤ (Fintype.card G : ℝ) ^ q := by positivity
  have hpow' : (Fintype.card G : ℝ) ^ q ≤ 2 * D := by
    simpa [D] using hpow
  calc
    (Fintype.card G : ℝ) ^ (2 * q) =
        ((Fintype.card G : ℝ) ^ q) ^ 2 := by ring
    _ ≤ (2 * D) ^ 2 := by nlinarith
    _ = 4 *
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ) := by
      dsimp [D]
      norm_num [pow_two]
      ring

/-- Concrete small-query normalizer slack bound for the certified
normalized-Ursell scalar endpoint. -/
theorem visibleNormalizerSlackReal_le_four_of_queryPair_le_card
    (G : Type*) [Fintype G] [Nonempty G] (q : Nat)
    (hsmall : q * (q - 1) ≤ Fintype.card G) :
    visibleNormalizerSlackReal G q ≤ 4 := by
  have hN : 0 < Fintype.card G := Fintype.card_pos (α := G)
  have hq : q ≤ Fintype.card G :=
    query_le_of_queryPair_le_card (Fintype.card G) q hN hsmall
  have hpow :=
    pow_le_two_mul_descFactorial_of_queryPair_le_card (Fintype.card G) q hN hsmall
  exact visibleNormalizerSlackReal_le_four_of_pow_le_two_descFactorial G q hq hpow

theorem visibleNormalizerNNReal_ne_zero [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) :
    visibleNormalizerNNReal (G := G) (q := q) ≠ 0 := by
  exact (compatibleExpectationNormalizer (G := G) (q := q) hq).value_ne_zero

theorem uniformAverage_eq_of_forall {α : Type*} [Fintype α] [Nonempty α]
    (u : α → ℝ) (c : ℝ) (h : ∀ x, u x = c) :
    uniformAverage α u = c := by
  have hsum : (∑ x : α, u x) = (Fintype.card α : ℝ) * c := by
    trans ∑ _x : α, c
    · exact Finset.sum_congr rfl (fun x _ => h x)
    · simp [Finset.sum_const, nsmul_eq_mul]
  have hcard_ne : (Fintype.card α : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  simp only [uniformAverage]
  rw [hsum]
  exact mul_div_cancel_left₀ c hcard_ne

theorem uniformAverage_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage α (fun x => f x + g x) = uniformAverage α f + uniformAverage α g := by
  simp [uniformAverage, Finset.sum_add_distrib, add_div]

theorem uniformAverage_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage α (fun x => f x - g x) = uniformAverage α f - uniformAverage α g := by
  simp only [uniformAverage]
  rw [Finset.sum_sub_distrib, sub_div]

@[simp]
theorem uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage α (fun _ => c) = c := by
  exact uniformAverage_eq_of_forall (fun _ : α => c) c (fun _ => rfl)

theorem sum_powerset_neg_one_pow_card_real {α : Type*} [DecidableEq α] (x : Finset α) :
    (∑ m ∈ x.powerset, (-1 : ℝ) ^ m.card) = if x = ∅ then 1 else 0 := by
  have hz := Finset.sum_powerset_neg_one_pow_card (x := x)
  exact_mod_cast hz

theorem sum_powerset_neg_one_pow_card_real_of_nonempty {α : Type*} [DecidableEq α]
    {x : Finset α} (hx : x.Nonempty) :
    (∑ m ∈ x.powerset, (-1 : ℝ) ^ m.card) = 0 := by
  rw [sum_powerset_neg_one_pow_card_real, if_neg]
  exact Finset.nonempty_iff_ne_empty.mp hx

theorem sum_supersets_neg_one_card_sub {α : Type*} [DecidableEq α]
    {T U : Finset α} (hTU : T ⊆ U) :
    (∑ S ∈ U.powerset.filter (fun S => T ⊆ S), (-1 : ℝ) ^ (S.card - T.card)) =
      ∑ R ∈ (U \ T).powerset, (-1 : ℝ) ^ R.card := by
  refine Finset.sum_bij' (s := U.powerset.filter (fun S => T ⊆ S))
    (t := (U \ T).powerset)
    (fun S _ => S \ T) (fun R _ => T ∪ R) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    exact Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff hS.1 (fun x hx => hx))
  · intro R hR
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro x hx
      simp only [Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hTU hx
      · exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hR) hx)).1
    · intro x hx
      exact Finset.mem_union_left _ hx
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    exact Finset.union_sdiff_of_subset hS.2
  · intro R hR
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro hx
      exact hx.1.resolve_left hx.2
    · intro hx
      exact ⟨Or.inr hx, (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hR) hx)).2⟩
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    have hcard : (S \ T).card = S.card - T.card := Finset.card_sdiff_of_subset hS.2
    rw [hcard]

theorem sum_supersets_neg_one_card_sub_eval {α : Type*} [DecidableEq α]
    {T U : Finset α} (hTU : T ⊆ U) :
    (∑ S ∈ U.powerset.filter (fun S => T ⊆ S), (-1 : ℝ) ^ (S.card - T.card)) =
      if T = U then 1 else 0 := by
  rw [sum_supersets_neg_one_card_sub hTU, sum_powerset_neg_one_pow_card_real]
  by_cases h : T = U
  · subst h
    simp
  · have hne : U \ T ≠ ∅ := by
      intro hempty
      apply h
      exact le_antisymm hTU (Finset.sdiff_eq_empty_iff_subset.mp hempty)
    simp [h, hne]

theorem sum_powerset_swap {α : Type*} [DecidableEq α] (U : Finset α)
    (F : Finset α → Finset α → ℝ) :
    (∑ S ∈ U.powerset, ∑ T ∈ S.powerset, F T S) =
      ∑ T ∈ U.powerset, ∑ S ∈ U.powerset.filter (fun S => T ⊆ S), F T S := by
  calc
    (∑ S ∈ U.powerset, ∑ T ∈ S.powerset, F T S)
        = ∑ S ∈ U.powerset, ∑ T ∈ U.powerset.filter (fun T => T ⊆ S), F T S := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext T
          simp only [Finset.mem_filter, Finset.mem_powerset]
          constructor
          · intro hTS
            exact ⟨hTS.trans (Finset.mem_powerset.mp hS), hTS⟩
          · intro h
            exact h.2
    _ = ∑ S ∈ U.powerset, ∑ T ∈ U.powerset, if T ⊆ S then F T S else 0 := by
          refine Finset.sum_congr rfl ?_
          intro S _
          rw [Finset.sum_filter]
    _ = ∑ T ∈ U.powerset, ∑ S ∈ U.powerset, if T ⊆ S then F T S else 0 := by
          exact Finset.sum_comm
    _ = ∑ T ∈ U.powerset, ∑ S ∈ U.powerset.filter (fun S => T ⊆ S), F T S := by
          refine Finset.sum_congr rfl ?_
          intro T _
          rw [Finset.sum_filter]

/-- The normalized compatible-count density ratio, viewed over `ℝ` for signed
ANOVA terms. -/
def visibleDensityRatioReal [AddGroup G] [Fintype G] (y : Fin q → G) : ℝ :=
  (((compatibleCountNNReal y /
        ((((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
            NNReal) /
          (((Fintype.card G ^ q : Nat) : NNReal)))) : NNReal) : ℝ)

theorem visibleDensityRatioReal_eq [AddGroup G] [Fintype G] (y : Fin q → G) :
    visibleDensityRatioReal y =
      ((compatibleCountNNReal y / visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ) := by
  rfl

theorem uniformAverage_visibleDensityRatioReal_eq_one [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) :
    uniformAverage (Fin q → G) (visibleDensityRatioReal (G := G) (q := q)) = 1 := by
  have hnorm_ne : ((visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hcard_ne : (Fintype.card (Fin q → G) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin q → G) ≠ 0)
  have hsumNN := idealCompatibleExpectation_eq_descFactorial_sq_div_pow (G := G) (q := q)
  have hsumR :
      (∑ y : Fin q → G, ((compatibleCountNNReal y : NNReal) : ℝ)) /
          (Fintype.card (Fin q → G) : ℝ) =
        ((visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ) := by
    exact_mod_cast hsumNN
  have hsum_div :
      (∑ x : Fin q → G, ((compatibleCountNNReal x : NNReal) : ℝ) /
        ((visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ)) =
      (∑ x : Fin q → G, ((compatibleCountNNReal x : NNReal) : ℝ)) /
        ((visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ) := by
    simp [div_eq_mul_inv, Finset.sum_mul]
  unfold uniformAverage
  simp only [visibleDensityRatioReal_eq, NNReal.coe_div]
  rw [hsum_div]
  calc
    ((∑ x : Fin q → G, ((compatibleCountNNReal x : NNReal) : ℝ)) /
        ((visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ)) /
        (Fintype.card (Fin q → G) : ℝ)
        = ((∑ x : Fin q → G, ((compatibleCountNNReal x : NNReal) : ℝ)) /
            (Fintype.card (Fin q → G) : ℝ)) /
            ((visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ) := by
          field_simp [hnorm_ne, hcard_ne]
    _ = 1 := by
      rw [hsumR]
      exact div_self hnorm_ne

/-- Real-valued visible density error `R - 1`. -/
def visibleDensityErrorReal [AddGroup G] [Fintype G] (y : Fin q → G) : ℝ :=
  visibleDensityRatioReal y - 1

/-- XoP visible density error, named for the ANOVA proof path. -/
abbrev xopError [AddGroup G] [Fintype G] : (Fin q → G) → ℝ :=
  visibleDensityErrorReal

theorem uniformAverage_xopError_eq_zero [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) :
    uniformAverage (Fin q → G) (xopError (G := G) (q := q)) = 0 := by
  unfold xopError visibleDensityErrorReal
  rw [uniformAverage_sub, uniformAverage_visibleDensityRatioReal_eq_one (G := G) (q := q) hq]
  simp

@[simp]
theorem project_apply [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) (y : Fin q → G) :
    project S f y = conditionalAverage S f (restrictTuple S y) :=
  rfl

@[simp]
theorem restrictTuple_coordinates_eq_iff [DecidableEq G]
    (y y' : Fin q → G) :
    restrictTuple (coordinates q) y' = restrictTuple (coordinates q) y ↔ y' = y := by
  constructor
  · intro h
    funext i
    have hi : i ∈ coordinates q := by
      simp [coordinates]
    have hcoord := congrFun h ⟨i, hi⟩
    simpa [restrictTuple] using hcoord
  · intro h
    simp [h]

theorem project_eq_of_restrictTuple_eq [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} {f : (Fin q → G) → ℝ} {y y' : Fin q → G}
    (h : restrictTuple S y' = restrictTuple S y) :
    project S f y' = project S f y := by
  simp [project, h]

theorem project_of_restrict [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (g : ({ i : Fin q // i ∈ S } → G) → ℝ)
    (y : Fin q → G) :
    project S (fun y' => g (restrictTuple S y')) y = g (restrictTuple S y) := by
  let α := { y' : Fin q → G // restrictTuple S y' = restrictTuple S y }
  haveI : Nonempty α := ⟨⟨y, rfl⟩⟩
  simp only [project, conditionalAverage]
  refine uniformAverage_eq_of_forall (α := α)
    (fun x => g (restrictTuple S x.1)) (g (restrictTuple S y)) ?_
  intro x
  simp [x.2]

theorem project_eq_self_of_restrict_invariant [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ)
    (h : ∀ {y y' : Fin q → G}, restrictTuple S y = restrictTuple S y' → f y = f y') :
    project S f = f := by
  funext y
  let α := { y' : Fin q → G // restrictTuple S y' = restrictTuple S y }
  haveI : Nonempty α := ⟨⟨y, rfl⟩⟩
  simp only [project, conditionalAverage]
  refine uniformAverage_eq_of_forall (α := α)
    (fun x => f x.1) (f y) ?_
  intro x
  exact h x.2

theorem project_eq_self_of_restrict_invariant_of_subset [Fintype G] [DecidableEq G]
    [Nonempty G] {U T : Finset (Fin q)} (hUT : U ⊆ T) (f : (Fin q → G) → ℝ)
    (hinv : ∀ {y y' : Fin q → G}, restrictTuple U y = restrictTuple U y' → f y = f y') :
    project T f = f := by
  apply project_eq_self_of_restrict_invariant
  intro y y' hT
  apply hinv
  funext i
  have hcoord := congrFun hT ⟨i.1, hUT i.2⟩
  simpa [restrictTuple] using hcoord

@[simp]
theorem project_idempotent_apply [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) (y : Fin q → G) :
    project S (project S f) y = project S f y := by
  simpa [project] using
    project_of_restrict (G := G) (q := q) S
      (fun z => conditionalAverage S f z) y

theorem project_idempotent [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) :
    project S (project S f) = project S f := by
  funext y
  exact project_idempotent_apply S f y

@[simp]
theorem conditionalAverage_const [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (c : ℝ) (z : { i : Fin q // i ∈ S } → G) :
    conditionalAverage S (fun _ : Fin q → G => c) z = c := by
  let y0 : Fin q → G := fun i =>
    if h : i ∈ S then z ⟨i, h⟩ else Classical.choice inferInstance
  have hy0 : restrictTuple S y0 = z := by
    funext i
    simp [restrictTuple, y0, i.2]
  let fiber := { y : Fin q → G // restrictTuple S y = z }
  haveI : Nonempty fiber := ⟨⟨y0, hy0⟩⟩
  simp [conditionalAverage, fiber]

@[simp]
theorem project_const [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (c : ℝ) :
    project S (fun _ : Fin q → G => c) = fun _ => c := by
  funext y
  simp [project]

theorem project_add [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f g : (Fin q → G) → ℝ) :
    project S (fun y => f y + g y) = fun y => project S f y + project S g y := by
  funext y
  simp [project, conditionalAverage, uniformAverage_add]

theorem project_sub [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f g : (Fin q → G) → ℝ) :
    project S (fun y => f y - g y) = fun y => project S f y - project S g y := by
  funext y
  simp [project, conditionalAverage, uniformAverage_sub]

/-- Add the same group element to every visible coordinate.  This is the
symmetry used to prove singleton visible marginals without opening a fresh
falling-factorial counting branch. -/
def addConstTuple [Add G] (y : Fin q → G) (t : G) : Fin q → G :=
  fun i => y i + t

theorem restrictTuple_singleton_eq_iff [DecidableEq G]
    (i : Fin q) (y z : Fin q → G) :
    restrictTuple ({i} : Finset (Fin q)) z = restrictTuple ({i} : Finset (Fin q)) y ↔
      z i = y i := by
  constructor
  · intro h
    have hcoord := congrFun h ⟨i, by simp⟩
    simpa [restrictTuple] using hcoord
  · intro h
    funext j
    have hji : (j : Fin q) = i := Finset.mem_singleton.mp j.2
    change z (j : Fin q) = y (j : Fin q)
    rw [hji]
    exact h

private def singletonFiberTranslateEquiv [AddGroup G] [DecidableEq G]
    (i : Fin q) (y y' : Fin q → G) :
    { z : Fin q → G //
        restrictTuple ({i} : Finset (Fin q)) z = restrictTuple ({i} : Finset (Fin q)) y } ≃
      { z : Fin q → G //
        restrictTuple ({i} : Finset (Fin q)) z = restrictTuple ({i} : Finset (Fin q)) y' } where
  toFun z := ⟨addConstTuple z.1 (-y i + y' i), by
    rw [restrictTuple_singleton_eq_iff]
    rw [addConstTuple]
    have hz : z.1 i = y i := (restrictTuple_singleton_eq_iff i y z.1).mp z.2
    rw [hz]
    simp⟩
  invFun z := ⟨addConstTuple z.1 (-y' i + y i), by
    rw [restrictTuple_singleton_eq_iff]
    rw [addConstTuple]
    have hz : z.1 i = y' i := (restrictTuple_singleton_eq_iff i y' z.1).mp z.2
    rw [hz]
    simp⟩
  left_inv z := by
    apply Subtype.ext
    funext j
    simp [addConstTuple, add_assoc]
  right_inv z := by
    apply Subtype.ext
    funext j
    simp [addConstTuple, add_assoc]

private theorem singleton_project_eq_of_addConst_invariant [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G]
    (i : Fin q) (f : (Fin q → G) → ℝ)
    (hinv : ∀ y t, f (addConstTuple y t) = f y) (y y' : Fin q → G) :
    project ({i} : Finset (Fin q)) f y = project ({i} : Finset (Fin q)) f y' := by
  let fiberY := { z : Fin q → G //
    restrictTuple ({i} : Finset (Fin q)) z = restrictTuple ({i} : Finset (Fin q)) y }
  let fiberY' := { z : Fin q → G //
    restrictTuple ({i} : Finset (Fin q)) z = restrictTuple ({i} : Finset (Fin q)) y' }
  let e : fiberY ≃ fiberY' := singletonFiberTranslateEquiv (G := G) (q := q) i y y'
  have hsum : (∑ z : fiberY, f z.1) = ∑ z : fiberY', f z.1 := by
    calc
      (∑ z : fiberY, f z.1)
          = ∑ z : fiberY', f ((e.symm z).1) := by
              exact Fintype.sum_equiv e
                (fun z : fiberY => f z.1)
                (fun z : fiberY' => f ((e.symm z).1))
                (by intro z; simp)
      _ = ∑ z : fiberY', f z.1 := by
          refine Finset.sum_congr rfl ?_
          intro z _
          change f (addConstTuple z.1 (-y' i + y i)) = f z.1
          exact hinv z.1 (-y' i + y i)
  have hcard : Fintype.card fiberY = Fintype.card fiberY' := Fintype.card_congr e
  simp only [project, conditionalAverage, uniformAverage]
  change (∑ z : fiberY, f z.1) / (Fintype.card fiberY : ℝ) =
    (∑ z : fiberY', f z.1) / (Fintype.card fiberY' : ℝ)
  rw [hsum, hcard]

@[simp]
theorem conditionalAverage_empty [Fintype G] [DecidableEq G] [Nonempty G]
    (f : (Fin q → G) → ℝ)
    (z : { i : Fin q // i ∈ (∅ : Finset (Fin q)) } → G) :
    conditionalAverage (∅ : Finset (Fin q)) f z = uniformAverage (Fin q → G) f := by
  let fiber := { y : Fin q → G // restrictTuple (∅ : Finset (Fin q)) y = z }
  let e : fiber ≃ (Fin q → G) :=
    { toFun := fun y => y.1
      invFun := fun y => ⟨y, by
        funext i
        cases i with
        | mk val prop =>
          simp at prop⟩
      left_inv := by
        intro y
        rfl
      right_inv := by
        intro y
        rfl }
  have hsum : (∑ y : fiber, f y.1) = ∑ y : Fin q → G, f y :=
    Fintype.sum_equiv e
      (fun y : fiber => f y.1) (fun y : Fin q → G => f y) (by intro y; rfl)
  have hcard : Fintype.card fiber = Fintype.card (Fin q → G) :=
    Fintype.card_congr e
  simp [conditionalAverage, uniformAverage, fiber, hsum, hcard]

@[simp]
theorem project_empty [Fintype G] [DecidableEq G] [Nonempty G]
    (f : (Fin q → G) → ℝ) :
    project (∅ : Finset (Fin q)) f = fun _ => uniformAverage (Fin q → G) f := by
  funext y
  simp [project]

@[simp]
theorem project_full [Fintype G] [DecidableEq G] [Nonempty G]
    (f : (Fin q → G) → ℝ) :
    project (coordinates q) f = f := by
  funext y
  let fiber :=
    { y' : Fin q → G // restrictTuple (coordinates q) y' = restrictTuple (coordinates q) y }
  let witness : fiber := ⟨y, rfl⟩
  have hsub : Subsingleton fiber := by
    refine ⟨fun a b => ?_⟩
    apply Subtype.ext
    have ha : a.1 = y :=
      (restrictTuple_coordinates_eq_iff (G := G) (q := q) y a.1).1 a.2
    have hb : b.1 = y :=
      (restrictTuple_coordinates_eq_iff (G := G) (q := q) y b.1).1 b.2
    exact ha.trans hb.symm
  letI : Subsingleton fiber := hsub
  have hsum : (∑ x : fiber, f x.1) = f y := by
    rw [Fintype.sum_eq_single witness]
    intro x hx
    exact False.elim (hx (Subsingleton.elim x witness))
  simp [project, conditionalAverage, uniformAverage, fiber, hsum]

private def extendTuple [Nonempty G] (S : Finset (Fin q))
    (z : { i : Fin q // i ∈ S } → G) : Fin q → G :=
  fun i => if h : i ∈ S then z ⟨i, h⟩ else Classical.choice inferInstance

@[simp]
private theorem restrictTuple_extendTuple [Nonempty G]
    (S : Finset (Fin q)) (z : { i : Fin q // i ∈ S } → G) :
    restrictTuple S (extendTuple S z) = z := by
  funext i
  simp [restrictTuple, extendTuple, i.2]

private theorem conditionalAverage_fiber_card_mul [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ)
    (z : { i : Fin q // i ∈ S } → G) :
    (Fintype.card { y : Fin q → G // restrictTuple S y = z } : ℝ) *
        conditionalAverage S f z =
      ∑ y : { y : Fin q → G // restrictTuple S y = z }, f y.1 := by
  let fiber := { y : Fin q → G // restrictTuple S y = z }
  haveI : Nonempty fiber := ⟨⟨extendTuple S z, restrictTuple_extendTuple S z⟩⟩
  have hcard_ne : (Fintype.card fiber : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card fiber ≠ 0)
  simp only [conditionalAverage, uniformAverage]
  change (Fintype.card fiber : ℝ) *
      ((∑ y : fiber, f y.1) / (Fintype.card fiber : ℝ)) =
    ∑ y : fiber, f y.1
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ (∑ y : fiber, f y.1) hcard_ne

private theorem sum_project_fiber [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ)
    (z : { i : Fin q // i ∈ S } → G) :
    (∑ y ∈ Finset.univ.filter (fun y : Fin q → G => restrictTuple S y = z),
        conditionalAverage S f (restrictTuple S y)) =
      ∑ y : { y : Fin q → G // restrictTuple S y = z }, f y.1 := by
  calc
    (∑ y ∈ Finset.univ.filter (fun y : Fin q → G => restrictTuple S y = z),
        conditionalAverage S f (restrictTuple S y))
        = ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => restrictTuple S y = z),
            conditionalAverage S f z := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
              rw [hy]
    _ = ∑ y : { y : Fin q → G // restrictTuple S y = z },
          conditionalAverage S f z := by
            rw [Finset.sum_subtype]
            intro y
            simp
    _ = (Fintype.card { y : Fin q → G // restrictTuple S y = z } : ℝ) *
          conditionalAverage S f z := by
            simp [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ y : { y : Fin q → G // restrictTuple S y = z }, f y.1 := by
          exact conditionalAverage_fiber_card_mul S f z

theorem uniformAverage_project [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) :
    uniformAverage (Fin q → G) (project S f) = uniformAverage (Fin q → G) f := by
  simp only [uniformAverage, project]
  congr 1
  calc
    (∑ y : Fin q → G, conditionalAverage S f (restrictTuple S y))
        = ∑ z : ({ i : Fin q // i ∈ S } → G),
            ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => restrictTuple S y = z),
              conditionalAverage S f (restrictTuple S y) := by
                rw [Finset.sum_fiberwise]
    _ = ∑ z : ({ i : Fin q // i ∈ S } → G),
          ∑ y : { y : Fin q → G // restrictTuple S y = z }, f y.1 := by
            refine Finset.sum_congr rfl ?_
            intro z _
            exact sum_project_fiber S f z
    _ = ∑ z : ({ i : Fin q // i ∈ S } → G),
          ∑ y ∈ Finset.univ.filter (fun y : Fin q → G => restrictTuple S y = z),
            f y := by
          refine Finset.sum_congr rfl ?_
          intro z _
          symm
          rw [Finset.sum_subtype]
          intro y
          simp
    _ = ∑ y : Fin q → G, f y := by
          rw [Finset.sum_fiberwise]

theorem project_singleton_eq_uniformAverage_of_addConst_invariant [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G]
    (i : Fin q) (f : (Fin q → G) → ℝ)
    (hinv : ∀ y t, f (addConstTuple y t) = f y) :
    project ({i} : Finset (Fin q)) f = fun _ => uniformAverage (Fin q → G) f := by
  let y0 : Fin q → G := fun _ => Classical.choice (inferInstance : Nonempty G)
  have hconst : ∀ y, project ({i} : Finset (Fin q)) f y =
      project ({i} : Finset (Fin q)) f y0 := by
    intro y
    exact singleton_project_eq_of_addConst_invariant (G := G) (q := q) i f hinv y y0
  have havg : uniformAverage (Fin q → G) (project ({i} : Finset (Fin q)) f) =
      project ({i} : Finset (Fin q)) f y0 := by
    exact uniformAverage_eq_of_forall (project ({i} : Finset (Fin q)) f)
      (project ({i} : Finset (Fin q)) f y0) hconst
  have hprojavg := uniformAverage_project (G := G) (q := q) ({i} : Finset (Fin q)) f
  funext y
  calc
    project ({i} : Finset (Fin q)) f y = project ({i} : Finset (Fin q)) f y0 := hconst y
    _ = uniformAverage (Fin q → G) (project ({i} : Finset (Fin q)) f) := havg.symm
    _ = uniformAverage (Fin q → G) f := hprojavg

theorem visibleDensityRatioReal_addConst [AddGroup G] [Fintype G]
    (y : Fin q → G) (t : G) :
    visibleDensityRatioReal (G := G) (q := q) (addConstTuple y t) =
      visibleDensityRatioReal (G := G) (q := q) y := by
  rw [visibleDensityRatioReal_eq, visibleDensityRatioReal_eq]
  change (((Combinatorics.compatibleCountNNReal (G := G) (q := q) (fun i => y i + t) /
      visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ)) =
    (((Combinatorics.compatibleCountNNReal (G := G) (q := q) y /
      visibleNormalizerNNReal (G := G) (q := q) : NNReal) : ℝ))
  rw [Combinatorics.compatibleCountNNReal_add_const]

theorem project_singleton_visibleDensityRatioReal_eq_one
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (hq : q ≤ Fintype.card G) (i : Fin q) :
    project ({i} : Finset (Fin q)) (visibleDensityRatioReal (G := G) (q := q)) =
      fun _ => 1 := by
  rw [project_singleton_eq_uniformAverage_of_addConst_invariant]
  · funext y
    exact uniformAverage_visibleDensityRatioReal_eq_one (G := G) (q := q) hq
  · intro y t
    exact visibleDensityRatioReal_addConst (G := G) (q := q) y t

def restrictTupleOfSubset {S T : Finset (Fin q)} (hST : S ⊆ T)
    (z : { i : Fin q // i ∈ T } → G) : { i : Fin q // i ∈ S } → G :=
  fun i => z ⟨i.1, hST i.2⟩

@[simp]
theorem restrictTupleOfSubset_restrictTuple {S T : Finset (Fin q)} (hST : S ⊆ T)
    (y : Fin q → G) :
    restrictTupleOfSubset (G := G) hST (restrictTuple T y) = restrictTuple S y := by
  rfl

private abbrev compatibleTFiber {S T : Finset (Fin q)} (hST : S ⊆ T)
    (zS : { i : Fin q // i ∈ S } → G) : Type _ :=
  { zT : ({ i : Fin q // i ∈ T } → G) //
      restrictTupleOfSubset (G := G) hST zT = zS }

private def sFiberToCompatibleT {S T : Finset (Fin q)} (hST : S ⊆ T)
    (zS : { i : Fin q // i ∈ S } → G)
    (y : { y : Fin q → G // restrictTuple S y = zS }) :
    compatibleTFiber (G := G) hST zS :=
  ⟨restrictTuple T y.1, by
    simpa [compatibleTFiber, restrictTupleOfSubset_restrictTuple] using y.2⟩

private def compatibleFiberEqEquiv {S T : Finset (Fin q)} (hST : S ⊆ T)
    (zS : { i : Fin q // i ∈ S } → G)
    (zT : compatibleTFiber (G := G) hST zS) :
    { y : { y : Fin q → G // restrictTuple S y = zS } //
        sFiberToCompatibleT (G := G) hST zS y = zT } ≃
      { y : { y : Fin q → G // restrictTuple S y = zS } //
        restrictTuple T y.1 = zT.1 } where
  toFun y := ⟨y.1, congrArg Subtype.val y.2⟩
  invFun y := ⟨y.1, by
    apply Subtype.ext
    exact y.2⟩
  left_inv := by
    intro y
    apply Subtype.ext
    rfl
  right_inv := by
    intro y
    apply Subtype.ext
    rfl

def subsetFiberFiberEquiv {S T : Finset (Fin q)} (hST : S ⊆ T)
    (zS : { i : Fin q // i ∈ S } → G) (zT : { i : Fin q // i ∈ T } → G)
    (hcompat : restrictTupleOfSubset (G := G) hST zT = zS) :
    { y : { y : Fin q → G // restrictTuple S y = zS } //
        restrictTuple T y.1 = zT } ≃
      { y : Fin q → G // restrictTuple T y = zT } where
  toFun y := ⟨y.1.1, y.2⟩
  invFun y := ⟨⟨y.1, by
      have h := congrArg (restrictTupleOfSubset (G := G) hST) y.2
      simpa [restrictTupleOfSubset_restrictTuple, hcompat] using h⟩, y.2⟩
  left_inv := by
    intro y
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv := by
    intro y
    apply Subtype.ext
    rfl

private theorem sum_project_compatibleFiber [Fintype G] [DecidableEq G] [Nonempty G]
    {S T : Finset (Fin q)} (hST : S ⊆ T) (f : (Fin q → G) → ℝ)
    (zS : { i : Fin q // i ∈ S } → G) (zT : { i : Fin q // i ∈ T } → G)
    (hcompat : restrictTupleOfSubset (G := G) hST zT = zS) :
    (∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
        restrictTuple T y.1 = zT }, project T f y.1.1) =
      ∑ y : { y : Fin q → G // restrictTuple T y = zT }, f y.1 := by
  classical
  calc
    (∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
        restrictTuple T y.1 = zT }, project T f y.1.1)
        = ∑ y : { y : Fin q → G // restrictTuple T y = zT }, project T f y.1 := by
          exact Fintype.sum_equiv (subsetFiberFiberEquiv (G := G) hST zS zT hcompat)
            (fun y : { y : { y : Fin q → G // restrictTuple S y = zS } //
              restrictTuple T y.1 = zT } => project T f y.1.1)
            (fun y : { y : Fin q → G // restrictTuple T y = zT } => project T f y.1)
            (by intro y; rfl)
    _ = ∑ y : { y : Fin q → G // restrictTuple T y = zT },
          conditionalAverage T f zT := by
          refine Finset.sum_congr rfl ?_
          intro y _
          simp [project, y.2]
    _ = ∑ y : { y : Fin q → G // restrictTuple T y = zT }, f y.1 := by
          symm
          calc
            (∑ y : { y : Fin q → G // restrictTuple T y = zT }, f y.1)
                = (Fintype.card { y : Fin q → G // restrictTuple T y = zT } : ℝ) *
                    conditionalAverage T f zT := by
                    exact (conditionalAverage_fiber_card_mul T f zT).symm
            _ = ∑ y : { y : Fin q → G // restrictTuple T y = zT },
                  conditionalAverage T f zT := by
                    simp [Finset.sum_const, nsmul_eq_mul]

private theorem sum_project_compatibleTFiber [Fintype G] [DecidableEq G] [Nonempty G]
    {S T : Finset (Fin q)} (hST : S ⊆ T) (f : (Fin q → G) → ℝ)
    (zS : { i : Fin q // i ∈ S } → G) (zT : compatibleTFiber (G := G) hST zS) :
    (∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
        sFiberToCompatibleT (G := G) hST zS y = zT }, project T f y.1.1) =
      ∑ y : { y : Fin q → G // restrictTuple T y = zT.1 }, f y.1 := by
  classical
  calc
    (∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
        sFiberToCompatibleT (G := G) hST zS y = zT }, project T f y.1.1)
        = ∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
            restrictTuple T y.1 = zT.1 }, project T f y.1.1 := by
          exact Fintype.sum_equiv (compatibleFiberEqEquiv (G := G) hST zS zT)
            (fun y : { y : { y : Fin q → G // restrictTuple S y = zS } //
              sFiberToCompatibleT (G := G) hST zS y = zT } => project T f y.1.1)
            (fun y : { y : { y : Fin q → G // restrictTuple S y = zS } //
              restrictTuple T y.1 = zT.1 } => project T f y.1.1)
            (by intro y; rfl)
    _ = ∑ y : { y : Fin q → G // restrictTuple T y = zT.1 }, f y.1 := by
          exact sum_project_compatibleFiber (G := G) hST f zS zT.1 zT.2

private theorem sum_fiber_compatibleTFiber [Fintype G] [DecidableEq G]
    {S T : Finset (Fin q)} (hST : S ⊆ T) (f : (Fin q → G) → ℝ)
    (zS : { i : Fin q // i ∈ S } → G) (zT : compatibleTFiber (G := G) hST zS) :
    (∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
        sFiberToCompatibleT (G := G) hST zS y = zT }, f y.1.1) =
      ∑ y : { y : Fin q → G // restrictTuple T y = zT.1 }, f y.1 := by
  classical
  calc
    (∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
        sFiberToCompatibleT (G := G) hST zS y = zT }, f y.1.1)
        = ∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
            restrictTuple T y.1 = zT.1 }, f y.1.1 := by
          exact Fintype.sum_equiv (compatibleFiberEqEquiv (G := G) hST zS zT)
            (fun y : { y : { y : Fin q → G // restrictTuple S y = zS } //
              sFiberToCompatibleT (G := G) hST zS y = zT } => f y.1.1)
            (fun y : { y : { y : Fin q → G // restrictTuple S y = zS } //
              restrictTuple T y.1 = zT.1 } => f y.1.1)
            (by intro y; rfl)
    _ = ∑ y : { y : Fin q → G // restrictTuple T y = zT.1 }, f y.1 := by
          exact Fintype.sum_equiv (subsetFiberFiberEquiv (G := G) hST zS zT.1 zT.2)
            (fun y : { y : { y : Fin q → G // restrictTuple S y = zS } //
              restrictTuple T y.1 = zT.1 } => f y.1.1)
            (fun y : { y : Fin q → G // restrictTuple T y = zT.1 } => f y.1)
            (by intro y; rfl)

theorem sum_project_fiber_of_subset [Fintype G] [DecidableEq G] [Nonempty G]
    {S T : Finset (Fin q)} (hST : S ⊆ T) (f : (Fin q → G) → ℝ)
    (zS : { i : Fin q // i ∈ S } → G) :
    (∑ y : { y : Fin q → G // restrictTuple S y = zS }, project T f y.1) =
      ∑ y : { y : Fin q → G // restrictTuple S y = zS }, f y.1 := by
  classical
  calc
    (∑ y : { y : Fin q → G // restrictTuple S y = zS }, project T f y.1)
        = ∑ zT : compatibleTFiber (G := G) hST zS,
            ∑ y ∈ Finset.univ.filter
                (fun y : { y : Fin q → G // restrictTuple S y = zS } =>
                  sFiberToCompatibleT (G := G) hST zS y = zT),
              project T f y.1 := by
              rw [Finset.sum_fiberwise]
    _ = ∑ zT : compatibleTFiber (G := G) hST zS,
          ∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
              sFiberToCompatibleT (G := G) hST zS y = zT }, project T f y.1.1 := by
          refine Finset.sum_congr rfl ?_
          intro zT _
          rw [Finset.sum_subtype]
          intro y
          simp
    _ = ∑ zT : compatibleTFiber (G := G) hST zS,
          ∑ y : { y : Fin q → G // restrictTuple T y = zT.1 }, f y.1 := by
          refine Finset.sum_congr rfl ?_
          intro zT _
          exact sum_project_compatibleTFiber (G := G) hST f zS zT
    _ = ∑ zT : compatibleTFiber (G := G) hST zS,
          ∑ y : { y : { y : Fin q → G // restrictTuple S y = zS } //
              sFiberToCompatibleT (G := G) hST zS y = zT }, f y.1.1 := by
          refine Finset.sum_congr rfl ?_
          intro zT _
          exact (sum_fiber_compatibleTFiber (G := G) hST f zS zT).symm
    _ = ∑ zT : compatibleTFiber (G := G) hST zS,
          ∑ y ∈ Finset.univ.filter
                (fun y : { y : Fin q → G // restrictTuple S y = zS } =>
                  sFiberToCompatibleT (G := G) hST zS y = zT),
              f y.1 := by
          refine Finset.sum_congr rfl ?_
          intro zT _
          symm
          rw [Finset.sum_subtype]
          intro y
          simp
    _ = ∑ y : { y : Fin q → G // restrictTuple S y = zS }, f y.1 := by
          exact Finset.sum_fiberwise (s := Finset.univ)
            (g := fun y : { y : Fin q → G // restrictTuple S y = zS } =>
              sFiberToCompatibleT (G := G) hST zS y)
            (f := fun y : { y : Fin q → G // restrictTuple S y = zS } => f y.1)

theorem conditionalAverage_project_of_subset [Fintype G] [DecidableEq G] [Nonempty G]
    {S T : Finset (Fin q)} (hST : S ⊆ T) (f : (Fin q → G) → ℝ)
    (zS : { i : Fin q // i ∈ S } → G) :
    conditionalAverage S (project T f) zS = conditionalAverage S f zS := by
  let fiber := { y : Fin q → G // restrictTuple S y = zS }
  haveI : Nonempty fiber := ⟨⟨extendTuple S zS, restrictTuple_extendTuple S zS⟩⟩
  simp only [conditionalAverage, uniformAverage]
  rw [sum_project_fiber_of_subset (G := G) hST f zS]

theorem project_project_of_subset [Fintype G] [DecidableEq G] [Nonempty G]
    {S T : Finset (Fin q)} (hST : S ⊆ T) (f : (Fin q → G) → ℝ) :
    project S (project T f) = project S f := by
  funext y
  exact conditionalAverage_project_of_subset (G := G) hST f (restrictTuple S y)

theorem uniformAverage_const_mul {α : Type*} [Fintype α]
    (c : ℝ) (f : α → ℝ) :
    uniformAverage α (fun x => c * f x) = c * uniformAverage α f := by
  simp only [uniformAverage]
  rw [← Finset.mul_sum, mul_div_assoc]

theorem uniformAverage_finset_sum {α β : Type*} [Fintype α]
    (s : Finset β) (F : β → α → ℝ) :
    uniformAverage α (fun x => ∑ b ∈ s, F b x) =
      ∑ b ∈ s, uniformAverage α (F b) := by
  simp only [uniformAverage]
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]

theorem project_finset_sum {ι : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (A : Finset ι) (g : ι → (Fin q → G) → ℝ) :
    project S (fun y => ∑ i ∈ A, g i y) = fun y => ∑ i ∈ A, project S (g i) y := by
  funext y
  simp [project, conditionalAverage, uniformAverage_finset_sum]

theorem project_const_mul [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (c : ℝ) (f : (Fin q → G) → ℝ) :
    project S (fun y => c * f y) = fun y => c * project S f y := by
  funext y
  simp [project, conditionalAverage, uniformAverage_const_mul]

/-- Finite Boolean-lattice Möbius reconstruction, with the signs written in
the same orientation as `anovaComponent`. -/
private theorem finset_mobius_reconstruction {α : Type*} [DecidableEq α]
    (U : Finset α) (a : Finset α → ℝ) :
    (∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
      ((-1 : ℝ) ^ (S.card - T.card)) * a T) = a U := by
  classical
  induction U using Finset.induction generalizing a with
  | empty =>
      simp
  | insert x U hx ih =>
      rw [Finset.sum_powerset_insert hx]
      rw [ih a]
      have hinner (S : Finset α) (hS : S ∈ U.powerset) :
          (∑ T ∈ (insert x S).powerset,
              (-1 : ℝ) ^ ((insert x S).card - T.card) * a T) =
            (∑ T ∈ S.powerset,
                (-1 : ℝ) ^ ((insert x S).card - T.card) * a T) +
              ∑ T ∈ S.powerset,
                (-1 : ℝ) ^ ((insert x S).card - (insert x T).card) *
                  a (insert x T) := by
        have hxS : x ∉ S := fun h => hx ((Finset.mem_powerset.mp hS) h)
        rw [Finset.sum_powerset_insert hxS
          (fun T => (-1 : ℝ) ^ ((insert x S).card - T.card) * a T)]
      have hsecond :
          (∑ S ∈ U.powerset, ∑ T ∈ (insert x S).powerset,
              (-1 : ℝ) ^ ((insert x S).card - T.card) * a T) =
            ∑ S ∈ U.powerset,
              ((∑ T ∈ S.powerset,
                  (-1 : ℝ) ^ ((insert x S).card - T.card) * a T) +
                ∑ T ∈ S.powerset,
                  (-1 : ℝ) ^ ((insert x S).card - (insert x T).card) *
                    a (insert x T)) := by
        refine Finset.sum_congr rfl ?_
        intro S hS
        exact hinner S hS
      rw [hsecond, Finset.sum_add_distrib]
      have hneg (S : Finset α) (hS : S ∈ U.powerset) :
          (∑ T ∈ S.powerset,
              (-1 : ℝ) ^ ((insert x S).card - T.card) * a T) =
            -∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * a T := by
        have hxS : x ∉ S := fun h => hx ((Finset.mem_powerset.mp hS) h)
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl ?_
        intro T hT
        have hcard : (insert x S).card - T.card = (S.card - T.card) + 1 := by
          have hTS : T ⊆ S := Finset.mem_powerset.mp hT
          have hle : T.card ≤ S.card := Finset.card_le_card hTS
          rw [Finset.card_insert_of_notMem hxS]
          omega
        rw [hcard]
        ring
      have hnegTotal :
          (∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
              (-1 : ℝ) ^ ((insert x S).card - T.card) * a T) = -a U := by
        calc
          (∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
              (-1 : ℝ) ^ ((insert x S).card - T.card) * a T)
              = ∑ S ∈ U.powerset,
                  -∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * a T := by
                    refine Finset.sum_congr rfl ?_
                    intro S hS
                    exact hneg S hS
          _ = - (∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
                  (-1 : ℝ) ^ (S.card - T.card) * a T) := by
                    rw [Finset.sum_neg_distrib]
          _ = -a U := by rw [ih a]
      have hnew (S : Finset α) (hS : S ∈ U.powerset) :
          (∑ T ∈ S.powerset,
              (-1 : ℝ) ^ ((insert x S).card - (insert x T).card) *
                a (insert x T)) =
            ∑ T ∈ S.powerset,
              (-1 : ℝ) ^ (S.card - T.card) * a (insert x T) := by
        have hxS : x ∉ S := fun h => hx ((Finset.mem_powerset.mp hS) h)
        refine Finset.sum_congr rfl ?_
        intro T hT
        have hcard : (insert x S).card - (insert x T).card = S.card - T.card := by
          have hTS : T ⊆ S := Finset.mem_powerset.mp hT
          have hxT : x ∉ T := fun hxT => hxS (hTS hxT)
          have hle : T.card ≤ S.card := Finset.card_le_card hTS
          rw [Finset.card_insert_of_notMem hxS, Finset.card_insert_of_notMem hxT]
          omega
        rw [hcard]
      have hnewTotal :
          (∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
              (-1 : ℝ) ^ ((insert x S).card - (insert x T).card) *
                a (insert x T)) = a (insert x U) := by
        calc
          (∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
              (-1 : ℝ) ^ ((insert x S).card - (insert x T).card) *
                a (insert x T))
              = ∑ S ∈ U.powerset, ∑ T ∈ S.powerset,
                  (-1 : ℝ) ^ (S.card - T.card) *
                    (fun T => a (insert x T)) T := by
                    refine Finset.sum_congr rfl ?_
                    intro S hS
                    exact hnew S hS
          _ = a (insert x U) := by rw [ih (fun T => a (insert x T))]
      rw [hnegTotal, hnewTotal]
      ring

theorem anovaComponent_empty [Fintype G] [DecidableEq G] [Nonempty G]
    (f : (Fin q → G) → ℝ) :
    anovaComponent (∅ : Finset (Fin q)) f = project (∅ : Finset (Fin q)) f := by
  funext y
  simp [anovaComponent]

@[simp]
theorem anovaComponent_empty_apply [Fintype G] [DecidableEq G] [Nonempty G]
    (f : (Fin q → G) → ℝ) (y : Fin q → G) :
    anovaComponent (∅ : Finset (Fin q)) f y = uniformAverage (Fin q → G) f := by
  simp [anovaComponent_empty]

theorem visibleL1_anovaComponent_empty_xopError [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] (hq : q ≤ Fintype.card G) :
    visibleL1 (anovaComponent (∅ : Finset (Fin q)) (xopError (G := G) (q := q))) = 0 := by
  have hcomponent :
      anovaComponent (∅ : Finset (Fin q)) (xopError (G := G) (q := q)) =
        fun _ : Fin q → G => 0 := by
    funext y
    rw [anovaComponent_empty_apply, uniformAverage_xopError_eq_zero (G := G) (q := q) hq]
  rw [hcomponent]
  simp [visibleL1, uniformAverage]

theorem anovaComponent_singleton [Fintype G] [DecidableEq G] [Nonempty G]
    (i : Fin q) (f : (Fin q → G) → ℝ) :
    anovaComponent ({i} : Finset (Fin q)) f =
      fun y => project ({i} : Finset (Fin q)) f y - project (∅ : Finset (Fin q)) f y := by
  funext y
  have hp : ({i} : Finset (Fin q)).powerset = ({∅, {i}} : Finset (Finset (Fin q))) := by
    ext T
    simp [Finset.subset_singleton_iff]
  simp [anovaComponent, hp]
  ring_nf

/-- If the one-coordinate marginal of the XoP density ratio is uniform, then
the corresponding singleton ANOVA component of `xopError` vanishes.  The
remaining theorem-forced leaf is the marginal/counting proof of `hproject`. -/
theorem anovaComponent_singleton_xopError_eq_zero_of_project_density_eq_one
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (i : Fin q)
    (hproject :
      project ({i} : Finset (Fin q)) (visibleDensityRatioReal (G := G) (q := q)) =
        fun _ => 1) :
    anovaComponent ({i} : Finset (Fin q)) (xopError (G := G) (q := q)) =
      fun _ => 0 := by
  rw [anovaComponent_singleton]
  have hprojError : project ({i} : Finset (Fin q)) (xopError (G := G) (q := q)) =
      fun _ => 0 := by
    unfold xopError visibleDensityErrorReal
    rw [project_sub, hproject, project_const]
    ext z
    ring
  have hmeanDensity : uniformAverage (Fin q → G) (visibleDensityRatioReal (G := G) (q := q)) =
      1 := by
    rw [← uniformAverage_project (G := G) ({i} : Finset (Fin q))
      (visibleDensityRatioReal (G := G) (q := q))]
    rw [hproject]
    exact uniformAverage_const 1
  have hprojEmpty : project (∅ : Finset (Fin q)) (xopError (G := G) (q := q)) =
      fun _ => 0 := by
    rw [project_empty]
    unfold xopError visibleDensityErrorReal
    rw [uniformAverage_sub, hmeanDensity, uniformAverage_const]
    ext z
    ring
  rw [hprojError, hprojEmpty]
  ext y
  ring

/-- `L¹` form of singleton-component vanishing from the one-coordinate density
marginal. -/
theorem visibleL1_anovaComponent_singleton_xopError_of_project_density_eq_one
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (i : Fin q)
    (hproject :
      project ({i} : Finset (Fin q)) (visibleDensityRatioReal (G := G) (q := q)) =
        fun _ => 1) :
    visibleL1 (anovaComponent ({i} : Finset (Fin q)) (xopError (G := G) (q := q))) = 0 := by
  rw [anovaComponent_singleton_xopError_eq_zero_of_project_density_eq_one
    (G := G) (q := q) i hproject]
  simp [visibleL1, uniformAverage]

theorem uniformAverage_anovaComponent_eq_zero_of_nonempty [Fintype G] [DecidableEq G]
    [Nonempty G] {S : Finset (Fin q)} (f : (Fin q → G) → ℝ) (hS : S.Nonempty) :
    uniformAverage (Fin q → G) (anovaComponent S f) = 0 := by
  calc
    uniformAverage (Fin q → G) (anovaComponent S f)
        = uniformAverage (Fin q → G)
            (fun y => ∑ T ∈ S.powerset,
              (-1 : ℝ) ^ (S.card - T.card) * project T f y) := by
              rfl
    _ = ∑ T ∈ S.powerset,
        uniformAverage (Fin q → G)
          (fun y => (-1 : ℝ) ^ (S.card - T.card) * project T f y) := by
          exact uniformAverage_finset_sum S.powerset
            (fun T y => (-1 : ℝ) ^ (S.card - T.card) * project T f y)
    _ = ∑ T ∈ S.powerset,
            (-1 : ℝ) ^ (S.card - T.card) * uniformAverage (Fin q → G) f := by
              refine Finset.sum_congr rfl ?_
              intro T _
              rw [uniformAverage_const_mul, uniformAverage_project]
    _ = (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) *
          uniformAverage (Fin q → G) f := by
            rw [Finset.sum_mul]
    _ = 0 := by
      have hsum : (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) = 0 := by
        calc
          (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card))
              = ∑ R ∈ S.powerset, (-1 : ℝ) ^ R.card := by
                  refine Finset.sum_bij' (s := S.powerset) (t := S.powerset)
                    (fun T _ => S \ T) (fun R _ => S \ R) ?_ ?_ ?_ ?_ ?_
                  · intro T hT
                    exact Finset.mem_powerset.mpr (fun _ hx => (Finset.mem_sdiff.mp hx).1)
                  · intro R hR
                    exact Finset.mem_powerset.mpr (fun _ hx => (Finset.mem_sdiff.mp hx).1)
                  · intro T hT
                    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT)
                  · intro R hR
                    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hR)
                  · intro T hT
                    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
                    have hcard : (S \ T).card = S.card - T.card :=
                      Finset.card_sdiff_of_subset hTS
                    rw [hcard]
          _ = 0 := by
              exact sum_powerset_neg_one_pow_card_real_of_nonempty hS
      rw [hsum, zero_mul]

theorem anovaComponent_const_of_nonempty [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (hS : S.Nonempty) (c : ℝ) :
    anovaComponent S (fun _ : Fin q → G => c) = fun _ => 0 := by
  funext y
  unfold anovaComponent
  calc
    (∑ T ∈ S.powerset,
        (-1 : ℝ) ^ (S.card - T.card) * project T (fun _ : Fin q → G => c) y)
        = (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) * c := by
          simp [Finset.sum_mul]
    _ = 0 := by
      have hsum : (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) = 0 := by
        calc
          (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card))
              = ∑ R ∈ S.powerset, (-1 : ℝ) ^ R.card := by
                  refine Finset.sum_bij' (s := S.powerset) (t := S.powerset)
                    (fun T _ => S \ T) (fun R _ => S \ R) ?_ ?_ ?_ ?_ ?_
                  · intro T hT
                    exact Finset.mem_powerset.mpr (fun _ hx => (Finset.mem_sdiff.mp hx).1)
                  · intro R hR
                    exact Finset.mem_powerset.mpr (fun _ hx => (Finset.mem_sdiff.mp hx).1)
                  · intro T hT
                    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT)
                  · intro R hR
                    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hR)
                  · intro T hT
                    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
                    have hcard : (S \ T).card = S.card - T.card :=
                      Finset.card_sdiff_of_subset hTS
                    rw [hcard]
          _ = 0 := by
              exact sum_powerset_neg_one_pow_card_real_of_nonempty hS
      rw [hsum, zero_mul]

theorem anovaComponent_sub_const_of_nonempty [Fintype G] [DecidableEq G] [Nonempty G]
    {S : Finset (Fin q)} (hS : S.Nonempty) (f : (Fin q → G) → ℝ) (c : ℝ) :
    anovaComponent S (fun y => f y - c) = anovaComponent S f := by
  have hsub : (fun y : Fin q → G => f y - c) =
      fun y => f y - (fun _ : Fin q → G => c) y := by
    rfl
  rw [hsub]
  funext y
  unfold anovaComponent
  simp_rw [project_sub]
  simp_rw [project_const]
  calc
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * (project T f y - c))
        = (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * project T f y) -
            (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) * c := by
          simp [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * project T f y := by
      have hsum : (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card)) = 0 := by
        calc
          (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card))
              = ∑ R ∈ S.powerset, (-1 : ℝ) ^ R.card := by
                  refine Finset.sum_bij' (s := S.powerset) (t := S.powerset)
                    (fun T _ => S \ T) (fun R _ => S \ R) ?_ ?_ ?_ ?_ ?_
                  · intro T hT
                    exact Finset.mem_powerset.mpr (fun _ hx => (Finset.mem_sdiff.mp hx).1)
                  · intro R hR
                    exact Finset.mem_powerset.mpr (fun _ hx => (Finset.mem_sdiff.mp hx).1)
                  · intro T hT
                    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hT)
                  · intro R hR
                    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hR)
                  · intro T hT
                    have hTS : T ⊆ S := Finset.mem_powerset.mp hT
                    have hcard : (S \ T).card = S.card - T.card :=
                      Finset.card_sdiff_of_subset hTS
                    rw [hcard]
          _ = 0 := by
              exact sum_powerset_neg_one_pow_card_real_of_nonempty hS
      simp [hsum]

theorem anovaComponent_finset_sum {ι : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (A : Finset ι) (g : ι → (Fin q → G) → ℝ) :
    anovaComponent S (fun y => ∑ i ∈ A, g i y) =
      fun y => ∑ i ∈ A, anovaComponent S (g i) y := by
  funext y
  unfold anovaComponent
  simp_rw [project_finset_sum]
  calc
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) *
        (∑ i ∈ A, project T (g i) y))
        = ∑ T ∈ S.powerset, ∑ i ∈ A,
            (-1 : ℝ) ^ (S.card - T.card) * project T (g i) y := by
          simp [Finset.mul_sum]
    _ = ∑ i ∈ A, ∑ T ∈ S.powerset,
            (-1 : ℝ) ^ (S.card - T.card) * project T (g i) y := by
          rw [Finset.sum_comm]

theorem anovaComponent_fintype_sum {ι : Type*} [Fintype ι]
    [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (g : ι → (Fin q → G) → ℝ) :
    anovaComponent S (fun y => ∑ i : ι, g i y) =
      fun y => ∑ i : ι, anovaComponent S (g i) y := by
  simpa using anovaComponent_finset_sum (G := G) (q := q) S (Finset.univ : Finset ι) g

theorem anovaComponent_const_mul [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (c : ℝ) (f : (Fin q → G) → ℝ) :
    anovaComponent S (fun y => c * f y) = fun y => c * anovaComponent S f y := by
  funext y
  unfold anovaComponent
  simp_rw [project_const_mul]
  calc
    (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * (c * project T f y)) =
      ∑ T ∈ S.powerset, c * ((-1 : ℝ) ^ (S.card - T.card) * project T f y) := by
        refine Finset.sum_congr rfl ?_
        intro T _hT
        ring
    _ = c * ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * project T f y := by
        rw [Finset.mul_sum]

/-- Boolean-lattice cancellation for a coordinate whose addition does not
change any projection appearing in an ANOVA component.

This is the purely algebraic half of the off-support argument.  The remaining
probabilistic/product-space obligation is to prove the hypothesis for functions
that are independent of `x`. -/
theorem anovaComponent_eq_zero_of_insert_project_eq [Fintype G] [DecidableEq G]
    [Nonempty G] {S : Finset (Fin q)} {x : Fin q} (hxS : x ∈ S)
    (f : (Fin q → G) → ℝ)
    (hirr : ∀ T ∈ (S.erase x).powerset,
      project (insert x T) f = project T f) :
    anovaComponent S f = fun _ => 0 := by
  funext y
  classical
  have hxErase : x ∉ S.erase x := Finset.notMem_erase x S
  have hS : insert x (S.erase x) = S := Finset.insert_erase hxS
  rw [← hS]
  unfold anovaComponent
  rw [Finset.sum_powerset_insert hxErase]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero ?_
  intro T hT
  have hTsub : T ⊆ S.erase x := Finset.mem_powerset.mp hT
  have hxT : x ∉ T := fun hxT => hxErase (hTsub hxT)
  have hcardLeft :
      (insert x (S.erase x)).card - T.card = (S.erase x).card - T.card + 1 := by
    rw [Finset.card_insert_of_notMem hxErase]
    have hle : T.card ≤ (S.erase x).card := Finset.card_le_card hTsub
    omega
  have hcardRight :
      (insert x (S.erase x)).card - (insert x T).card = (S.erase x).card - T.card := by
    rw [Finset.card_insert_of_notMem hxErase, Finset.card_insert_of_notMem hxT]
    have hle : T.card ≤ (S.erase x).card := Finset.card_le_card hTsub
    omega
  have hproj : project (insert x T) f y = project T f y := congrFun (hirr T hT) y
  rw [hcardLeft, hcardRight, hproj]
  rw [pow_succ]
  ring

/-- A function depends only on the coordinates in `U`. -/
def RestrictInvariant [Fintype G] [DecidableEq G] [Nonempty G]
    (U : Finset (Fin q)) (f : (Fin q → G) → ℝ) : Prop :=
  ∀ {y y' : Fin q → G}, restrictTuple U y = restrictTuple U y' → f y = f y'

/-- Product-space projection irrelevance for coordinates outside the support of
a function.

This is the named probabilistic leaf needed for off-support ANOVA vanishing. It
is expected to follow from the uniform product structure of `(Fin q → G)`;
keeping it explicit prevents the Mayer layer from silently assuming an
independence theorem that has not yet been proved. -/
def ProjectionIrrelevance [Fintype G] [DecidableEq G] [Nonempty G] : Prop :=
  ∀ (U T : Finset (Fin q)) (x : Fin q) (f : (Fin q → G) → ℝ),
    RestrictInvariant U f →
      x ∉ U →
        x ∉ T →
          project (insert x T) f = project T f

private theorem restrictTuple_update_of_notMem [Fintype G] [DecidableEq G]
    {T : Finset (Fin q)} {x : Fin q} (hxT : x ∉ T)
    (y : Fin q → G) (a : G) :
    restrictTuple T (Function.update y x a) = restrictTuple T y := by
  funext i
  have hne : i.1 ≠ x := by
    intro hix
    exact hxT (by simpa [hix] using i.2)
  simp [restrictTuple, Function.update, hne]

private theorem restrictTuple_insert_eq_of_base_and_x [Fintype G] [DecidableEq G]
    {T : Finset (Fin q)} {x : Fin q} {y z : Fin q → G}
    (hT : restrictTuple T z = restrictTuple T y) (hx : z x = y x) :
    restrictTuple (insert x T) z = restrictTuple (insert x T) y := by
  funext i
  by_cases hix : i.1 = x
  · simpa [restrictTuple, hix] using hx
  · have hiT : i.1 ∈ T := by
      have hi := i.2
      simp only [Finset.mem_insert] at hi
      exact hi.resolve_left hix
    have hcoord := congrFun hT ⟨i.1, hiT⟩
    simpa [restrictTuple] using hcoord

private theorem restrictTuple_insert_update_to_base [Fintype G] [DecidableEq G]
    {T : Finset (Fin q)} {x : Fin q} (hxT : x ∉ T)
    (y z : Fin q → G) (hT : restrictTuple T z = restrictTuple T y) :
    restrictTuple (insert x T) (Function.update z x (y x)) =
      restrictTuple (insert x T) y := by
  apply restrictTuple_insert_eq_of_base_and_x
  · rw [restrictTuple_update_of_notMem hxT]
    exact hT
  · simp

private theorem update_eq_self_of_x_eq [DecidableEq (Fin q)]
    {y : Fin q → G} {x : Fin q} (a : G) (hx : y x = a) :
    Function.update y x a = y := by
  funext i
  by_cases hix : i = x
  · subst hix
    simp [Function.update, hx]
  · simp [Function.update, hix]

private def insertFiberEquiv [Fintype G] [DecidableEq G]
    {T : Finset (Fin q)} {x : Fin q} (hxT : x ∉ T) (y : Fin q → G) :
    { z : Fin q → G // restrictTuple T z = restrictTuple T y } ≃
      G × { z : Fin q → G //
        restrictTuple (insert x T) z = restrictTuple (insert x T) y } where
  toFun z :=
    (z.1 x,
      ⟨Function.update z.1 x (y x),
        restrictTuple_insert_update_to_base (G := G) (q := q) hxT y z.1 z.2⟩)
  invFun p :=
    ⟨Function.update p.2.1 x p.1,
      by
        rw [restrictTuple_update_of_notMem hxT]
        have hsub : T ⊆ insert x T := Finset.subset_insert x T
        have h := congrArg (restrictTupleOfSubset (G := G) hsub) p.2.2
        simpa [restrictTupleOfSubset_restrictTuple] using h⟩
  left_inv := by
    intro z
    apply Subtype.ext
    funext i
    by_cases hix : i = x
    · subst hix
      simp [Function.update]
    · simp [Function.update, hix]
  right_inv := by
    intro p
    cases p with
    | mk gx z =>
        apply Prod.ext
        · simp [Function.update]
        · apply Subtype.ext
          have hx : z.1 x = y x := by
            have hcoord := congrFun z.2 ⟨x, Finset.mem_insert_self x T⟩
            simpa [restrictTuple] using hcoord
          funext i
          by_cases hix : i = x
          · subst hix
            simp [Function.update, hx]
          · simp [Function.update, hix]

private theorem restrictInvariant_update_of_notMem [Fintype G] [DecidableEq G]
    [Nonempty G] {U : Finset (Fin q)} {x : Fin q} (hxU : x ∉ U)
    {f : (Fin q → G) → ℝ} (hinv : RestrictInvariant U f)
    (y : Fin q → G) (a : G) :
    f (Function.update y x a) = f y := by
  exact hinv (restrictTuple_update_of_notMem (G := G) (q := q) hxU y a)

private theorem sum_fiber_eq_card_mul_insert_fiber [Fintype G] [DecidableEq G]
    [Nonempty G] {U T : Finset (Fin q)} {x : Fin q}
    (hxU : x ∉ U) (hxT : x ∉ T)
    {f : (Fin q → G) → ℝ} (hinv : RestrictInvariant U f) (y : Fin q → G) :
    (∑ z : { z : Fin q → G // restrictTuple T z = restrictTuple T y }, f z.1) =
      (Fintype.card G : ℝ) *
        ∑ z : { z : Fin q → G //
            restrictTuple (insert x T) z = restrictTuple (insert x T) y }, f z.1 := by
  let fiberT := { z : Fin q → G // restrictTuple T z = restrictTuple T y }
  let fiberIx := { z : Fin q → G //
    restrictTuple (insert x T) z = restrictTuple (insert x T) y }
  let e : fiberT ≃ G × fiberIx := insertFiberEquiv (G := G) (q := q) hxT y
  calc
    (∑ z : fiberT, f z.1)
        = ∑ p : G × fiberIx, f ((e.symm p).1) := by
            exact Fintype.sum_equiv e
              (fun z : fiberT => f z.1)
              (fun p : G × fiberIx => f ((e.symm p).1))
              (by intro z; simp)
    _ = ∑ p : G × fiberIx, f p.2.1 := by
          refine Finset.sum_congr rfl ?_
          intro p _
          exact restrictInvariant_update_of_notMem (G := G) (q := q)
            hxU hinv p.2.1 p.1
    _ = ∑ g : G, ∑ z : fiberIx, f z.1 := by
          rw [Fintype.sum_prod_type]
    _ = (Fintype.card G : ℝ) * ∑ z : fiberIx, f z.1 := by
          simp [Finset.sum_const, nsmul_eq_mul]

private theorem card_fiber_eq_card_mul_insert_fiber [Fintype G] [DecidableEq G]
    {T : Finset (Fin q)} {x : Fin q} (hxT : x ∉ T) (y : Fin q → G) :
    (Fintype.card { z : Fin q → G // restrictTuple T z = restrictTuple T y } : ℝ) =
      (Fintype.card G : ℝ) *
        (Fintype.card { z : Fin q → G //
          restrictTuple (insert x T) z = restrictTuple (insert x T) y } : ℝ) := by
  let fiberT := { z : Fin q → G // restrictTuple T z = restrictTuple T y }
  let fiberIx := { z : Fin q → G //
    restrictTuple (insert x T) z = restrictTuple (insert x T) y }
  have hcardNat : Fintype.card fiberT = Fintype.card (G × fiberIx) :=
    Fintype.card_congr (insertFiberEquiv (G := G) (q := q) hxT y)
  rw [Fintype.card_prod] at hcardNat
  exact_mod_cast hcardNat

theorem project_insert_eq_project_of_restrictInvariant [Fintype G] [DecidableEq G]
    [Nonempty G] {U T : Finset (Fin q)} {x : Fin q}
    (hxU : x ∉ U) (hxT : x ∉ T)
    (f : (Fin q → G) → ℝ) (hinv : RestrictInvariant U f) :
    project (insert x T) f = project T f := by
  funext y
  let fiberT := { z : Fin q → G // restrictTuple T z = restrictTuple T y }
  let fiberIx := { z : Fin q → G //
    restrictTuple (insert x T) z = restrictTuple (insert x T) y }
  haveI : Nonempty fiberT := ⟨⟨y, rfl⟩⟩
  haveI : Nonempty fiberIx := ⟨⟨y, rfl⟩⟩
  have hsum := sum_fiber_eq_card_mul_insert_fiber
    (G := G) (q := q) hxU hxT hinv y
  have hcard := card_fiber_eq_card_mul_insert_fiber
    (G := G) (q := q) hxT y
  have hG : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  have hIx : (Fintype.card fiberIx : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card fiberIx ≠ 0)
  simp only [project, conditionalAverage, uniformAverage]
  change (∑ z : fiberIx, f z.1) / (Fintype.card fiberIx : ℝ) =
    (∑ z : fiberT, f z.1) / (Fintype.card fiberT : ℝ)
  rw [hsum, hcard]
  field_simp [hG, hIx]
  simp [fiberIx]
  ring

theorem projectionIrrelevance [Fintype G] [DecidableEq G] [Nonempty G] :
    ProjectionIrrelevance (G := G) (q := q) := by
  intro U T x f hinv hxU hxT
  exact project_insert_eq_project_of_restrictInvariant
    (G := G) (q := q) hxU hxT f hinv

/-- If a function depends only on `U`, and the ANOVA support `S` asks for at
least one coordinate outside `U`, then the `S`-component vanishes, assuming the
product-space projection irrelevance leaf. -/
theorem anovaComponent_eq_zero_of_restrict_invariant_of_not_subset [Fintype G]
    [DecidableEq G] [Nonempty G] (hproj : ProjectionIrrelevance (G := G) (q := q))
    {S U : Finset (Fin q)} (f : (Fin q → G) → ℝ)
    (hinv : RestrictInvariant U f) (hnot : ¬ S ⊆ U) :
    anovaComponent S f = fun _ => 0 := by
  rcases Finset.not_subset.mp hnot with ⟨x, hxS, hxU⟩
  refine anovaComponent_eq_zero_of_insert_project_eq (G := G) (q := q) hxS f ?_
  intro T hT
  have hTsub : T ⊆ S.erase x := Finset.mem_powerset.mp hT
  have hxT : x ∉ T := fun hxT => Finset.notMem_erase x S (hTsub hxT)
  exact hproj U T x f hinv hxU hxT

theorem anovaComponent_reconstruction_apply [Fintype G] [DecidableEq G] [Nonempty G]
    (f : (Fin q → G) → ℝ) (y : Fin q → G) :
    ∑ S ∈ (coordinates q).powerset, anovaComponent S f y = f y := by
  calc
    ∑ S ∈ (coordinates q).powerset, anovaComponent S f y
        = ∑ S ∈ (coordinates q).powerset, ∑ T ∈ S.powerset,
            (-1 : ℝ) ^ (S.card - T.card) * project T f y := by
          rfl
    _ = project (coordinates q) f y := by
          exact finset_mobius_reconstruction (coordinates q) (fun T => project T f y)
    _ = f y := by
          exact congrFun (project_full (G := G) (q := q) f) y

theorem anovaComponent_reconstruction [Fintype G] [DecidableEq G] [Nonempty G]
    (f : (Fin q → G) → ℝ) :
    (fun y => ∑ S ∈ (coordinates q).powerset, anovaComponent S f y) = f := by
  funext y
  exact anovaComponent_reconstruction_apply f y

theorem visibleL1_nonneg [Fintype G] (f : (Fin q → G) → ℝ) :
    0 ≤ visibleL1 f := by
  unfold visibleL1 uniformAverage
  exact div_nonneg (Finset.sum_nonneg (fun y _ => abs_nonneg (f y))) (Nat.cast_nonneg _)

@[simp]
theorem visibleL1_zero [Fintype G] :
    visibleL1 (G := G) (q := q) (fun _ : Fin q → G => 0) = 0 := by
  simp [visibleL1, uniformAverage]

theorem visibleL1_sum_le {ι : Type*} [Fintype G]
    (A : Finset ι) (g : ι → (Fin q → G) → ℝ) :
    visibleL1 (fun y => ∑ i ∈ A, g i y) ≤ ∑ i ∈ A, visibleL1 (g i) := by
  unfold visibleL1 uniformAverage
  calc
    (∑ y : Fin q → G, |∑ i ∈ A, g i y|) / (Fintype.card (Fin q → G) : ℝ)
        ≤ (∑ y : Fin q → G, ∑ i ∈ A, |g i y|) /
            (Fintype.card (Fin q → G) : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ ?_
          · exact Finset.sum_le_sum
              (fun y _ => Finset.abs_sum_le_sum_abs (fun i => g i y) A)
          · exact Nat.cast_nonneg _
    _ = (∑ i ∈ A, ∑ y : Fin q → G, |g i y|) /
            (Fintype.card (Fin q → G) : ℝ) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ A, (∑ y : Fin q → G, |g i y|) /
            (Fintype.card (Fin q → G) : ℝ) := by
          simp [div_eq_mul_inv, Finset.sum_mul]

/-- Pointwise Jensen bound for a finite conditional average. -/
theorem abs_project_le_project_abs [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) (y : Fin q → G) :
    |project S f y| ≤ project S (fun y => |f y|) y := by
  let fiber := { y' : Fin q → G // restrictTuple S y' = restrictTuple S y }
  haveI : Nonempty fiber := ⟨⟨y, rfl⟩⟩
  simp only [project, conditionalAverage, uniformAverage]
  change |(∑ y' : fiber, f y'.1) / (Fintype.card fiber : ℝ)| ≤
    (∑ y' : fiber, |f y'.1|) / (Fintype.card fiber : ℝ)
  have hcard_nonneg : 0 ≤ (Fintype.card fiber : ℝ) := Nat.cast_nonneg _
  rw [abs_div, abs_of_nonneg hcard_nonneg]
  exact div_le_div_of_nonneg_right
    (Finset.abs_sum_le_sum_abs (fun y' : fiber => f y'.1) Finset.univ)
    hcard_nonneg

/-- Conditional projection is an `L¹` contraction under the uniform product
measure. -/
theorem visibleL1_project_le [Fintype G] [DecidableEq G] [Nonempty G]
    (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) :
    visibleL1 (project S f) ≤ visibleL1 f := by
  calc
    visibleL1 (project S f)
        ≤ uniformAverage (Fin q → G) (project S (fun y => |f y|)) := by
          unfold visibleL1 uniformAverage
          exact div_le_div_of_nonneg_right
            (Finset.sum_le_sum (fun y _ => abs_project_le_project_abs S f y))
            (Nat.cast_nonneg _)
    _ = visibleL1 f := by
          rw [uniformAverage_project]
          rfl

/-- Scaling a function scales its visible `L¹` norm by the absolute scalar. -/
theorem visibleL1_const_mul [Fintype G] (c : ℝ) (f : (Fin q → G) → ℝ) :
    visibleL1 (fun y => c * f y) = |c| * visibleL1 f := by
  unfold visibleL1 uniformAverage
  simp [abs_mul]
  rw [← Finset.mul_sum]
  ring

/-- A crude but reusable `L¹` bound for one ANOVA component.  The sharp XoP
estimate must improve the right-hand side, but this lemma is the generic
triangle/projection-contraction leaf needed to expose the remaining termwise
budget as a bound on the underlying factorized Mayer term. -/
theorem visibleL1_anovaComponent_le_card_powerset_mul_visibleL1 [Fintype G]
    [DecidableEq G] [Nonempty G] (S : Finset (Fin q)) (f : (Fin q → G) → ℝ) :
    visibleL1 (anovaComponent S f) ≤ (S.powerset.card : ℝ) * visibleL1 f := by
  unfold anovaComponent
  refine le_trans
    (visibleL1_sum_le (G := G) (q := q) S.powerset
      (fun T y => ((-1 : ℝ) ^ (S.card - T.card)) * project T f y))
    (by
      calc
        (∑ T ∈ S.powerset,
            visibleL1 (fun y => (-1 : ℝ) ^ (S.card - T.card) * project T f y))
            ≤ ∑ _T ∈ S.powerset, visibleL1 f := by
              refine Finset.sum_le_sum ?_
              intro T hT
              rw [visibleL1_const_mul]
              simp
              exact visibleL1_project_le T f
        _ = (S.powerset.card : ℝ) * visibleL1 f := by
              simp [Finset.sum_const, nsmul_eq_mul])

theorem visibleL1_anova_sum_bound [Fintype G] [DecidableEq G] [Nonempty G]
    (f : (Fin q → G) → ℝ) :
    visibleL1 f ≤ ∑ S ∈ (coordinates q).powerset, visibleL1 (anovaComponent S f) := by
  calc
    visibleL1 f =
        visibleL1 (fun y => ∑ S ∈ (coordinates q).powerset, anovaComponent S f y) := by
          congr
          exact (anovaComponent_reconstruction f).symm
    _ ≤ ∑ S ∈ (coordinates q).powerset, visibleL1 (anovaComponent S f) := by
          exact visibleL1_sum_le (G := G) ((coordinates q).powerset)
            (fun S => anovaComponent S f)

theorem xopError_anova_reconstruction_apply [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] (y : Fin q → G) :
    (∑ S ∈ (coordinates q).powerset, anovaComponent S (xopError (G := G) (q := q)) y) =
      xopError (G := G) (q := q) y := by
  exact anovaComponent_reconstruction_apply (xopError (G := G) (q := q)) y

theorem xopError_anova_reconstruction [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] :
    (fun y : Fin q → G =>
      ∑ S ∈ (coordinates q).powerset, anovaComponent S (xopError (G := G) (q := q)) y) =
      xopError (G := G) (q := q) := by
  exact anovaComponent_reconstruction (xopError (G := G) (q := q))

theorem visibleL1_xopError_anova_sum_bound [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] :
    visibleL1 (xopError (G := G) (q := q)) ≤
      ∑ S ∈ (coordinates q).powerset,
        visibleL1 (anovaComponent S (xopError (G := G) (q := q))) := by
  exact visibleL1_anova_sum_bound (xopError (G := G) (q := q))

theorem max_mul_inv_sub_inv_le_abs_sub_div (d c : ℝ) (hc : 0 ≤ c) :
    max (d * (1 / c) - 1 / c) 0 ≤ |d - 1| / c := by
  by_cases hc0 : c = 0
  · subst hc0
    simp
  · have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hinv_nonneg : 0 ≤ 1 / c := by
      positivity
    have h1 : d * (1 / c) - 1 / c = (d - 1) * (1 / c) := by
      ring
    rw [h1]
    have hle : (d - 1) * (1 / c) ≤ |(d - 1) * (1 / c)| := le_abs_self _
    have hzero : (0 : ℝ) ≤ |(d - 1) * (1 / c)| := abs_nonneg _
    have hmax : max ((d - 1) * (1 / c)) 0 ≤ |(d - 1) * (1 / c)| :=
      max_le hle hzero
    calc
      max ((d - 1) * (1 / c)) 0 ≤ |(d - 1) * (1 / c)| := hmax
      _ = |d - 1| / c := by
        rw [abs_mul, abs_of_nonneg hinv_nonneg]
        ring

theorem pureVisiblePositiveError_toReal_le_visibleL1_xopError [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] :
    ((Analytic.pureVisiblePositiveError (G := G) q : NNReal) : ℝ) ≤
      visibleL1 (xopError (G := G) (q := q)) := by
  unfold Analytic.pureVisiblePositiveError visibleL1 uniformAverage xopError
    visibleDensityErrorReal visibleDensityRatioReal
  simp only [NNReal.coe_sum, NNReal.coe_sub_def, NNReal.coe_mul, NNReal.coe_div,
    RandomSystems.Dist.uniform_apply]
  let c : ℝ := Fintype.card (Fin q → G)
  let D : (Fin q → G) → ℝ := fun x =>
    ↑(compatibleCountNNReal x) /
      (↑↑((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q) /
        ↑↑(Fintype.card G ^ q))
  change (∑ x, max (D x * (1 / c) - 1 / c) 0) ≤ (∑ x, |D x - 1|) / c
  calc
    (∑ x, max (D x * (1 / c) - 1 / c) 0) ≤ ∑ x, |D x - 1| / c := by
      refine Finset.sum_le_sum ?_
      intro x _
      exact max_mul_inv_sub_inv_le_abs_sub_div (D x) c (Nat.cast_nonneg _)
    _ = (∑ x, |D x - 1|) / c := by
      simp [div_eq_mul_inv, Finset.sum_mul]

theorem pureVisiblePositiveError_le_of_visibleL1_xopError_le [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {ε : NNReal}
    (hL1 : visibleL1 (xopError (G := G) (q := q)) ≤ (ε : ℝ)) :
    Analytic.pureVisiblePositiveError (G := G) q ≤ ε := by
  rw [← NNReal.coe_le_coe]
  exact le_trans pureVisiblePositiveError_toReal_le_visibleL1_xopError hL1

theorem pureVisiblePositiveError_le_of_anova_l1_sum_le [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {ε : NNReal}
    (hcomponents :
      (∑ S ∈ (coordinates q).powerset,
        visibleL1 (anovaComponent S (xopError (G := G) (q := q)))) ≤ (ε : ℝ)) :
    Analytic.pureVisiblePositiveError (G := G) q ≤ ε := by
  apply pureVisiblePositiveError_le_of_visibleL1_xopError_le
  exact le_trans visibleL1_xopError_anova_sum_bound hcomponents

/-- The component-level analytic obligation left by the ANOVA bridge. -/
def XoPComponentL1Bound [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (ε : NNReal) : Prop :=
  (∑ S ∈ (coordinates q).powerset,
    visibleL1 (anovaComponent S (xopError (G := G) (q := q)))) ≤ (ε : ℝ)

theorem pureVisiblePositiveError_le_of_componentL1Bound [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] {ε : NNReal}
    (h : XoPComponentL1Bound (G := G) (q := q) ε) :
    Analytic.pureVisiblePositiveError (G := G) q ≤ ε := by
  exact pureVisiblePositiveError_le_of_anova_l1_sum_le h

theorem xop_advantageOn_injective_of_componentL1Bound [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (ε : NNReal)
    (h : XoPComponentL1Bound (G := G) (q := q) ε) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  refine Analytic.xop_advantageOn_injective_of_pureVisiblePositiveError
    (G := G) (q := q) ε ?_
  intro _hq
  exact pureVisiblePositiveError_le_of_componentL1Bound h

/-- Per-component activity estimate expected from pair-Mayer/rank analysis. -/
def ComponentActivityBound [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (activity : Nat → ℝ) : Prop :=
  ∀ S ∈ (coordinates q).powerset,
    visibleL1 (anovaComponent S (xopError (G := G) (q := q))) ≤ activity S.card

theorem componentL1Bound_of_activity_sum [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] {ε : NNReal} {activity : Nat → ℝ}
    (hactivity : ComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ S ∈ (coordinates q).powerset, activity S.card) ≤ (ε : ℝ)) :
    XoPComponentL1Bound (G := G) (q := q) ε := by
  dsimp [XoPComponentL1Bound]
  exact le_trans (Finset.sum_le_sum (fun S hS => hactivity S hS)) hsum

theorem xop_advantageOn_injective_of_activity_sum [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] (ε : NNReal) {activity : Nat → ℝ}
    (hactivity : ComponentActivityBound (G := G) (q := q) activity)
    (hsum : (∑ S ∈ (coordinates q).powerset, activity S.card) ≤ (ε : ℝ)) :
    advantageOn (Model.xopRealPDS (G := G) (q := q)) (Model.xopIdealPDS (G := G) (q := q))
      (InjectiveInputs (X := G) (q := q)) ≤ ε := by
  exact xop_advantageOn_injective_of_componentL1Bound ε
    (componentL1Bound_of_activity_sum (G := G) (q := q) hactivity hsum)

end ANOVA
end XoP
end Applications
end RandomSystems
