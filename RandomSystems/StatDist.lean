/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist
import Mathlib.Algebra.Order.Sub.Basic

/-!
# Statistical Distance

Lean 4 formalization of Definition 3, Lemma 2, Lemma 3 from
Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `statDist X Y` — statistical distance `δ(X, Y)`

## Main Results

* `statDist_self` — `δ(X, X) = 0` (proved)
* `statDist_symm_of_eq_weight` — `δ(X, Y) = δ(Y, X)` when `|X| = |Y|`
* `statDist_triangle` — triangle inequality
* `statDist_partition` — Lemma 2: partition of statistical distance
* `statDist_fTransform_le` — Lemma 3: data processing inequality
* `statDist_eq_mass_on_zero_support` — when Y=0 on S and X≤Y on Sᶜ, statDist = ∑_S X
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

/-! ### Supremum helpers for advantage definitions -/

/-- If an index type is empty, then the image of `Set.univ` under any function
out of it is empty. -/
theorem image_univ_eq_empty_of_not_nonempty {ι : Type*} {α : Type*}
    (f : ι → α) (hι : ¬ Nonempty ι) :
    f '' Set.univ = (∅ : Set α) := by
  ext x
  constructor
  · rintro ⟨i, _hi, rfl⟩
    exact (hι ⟨i⟩).elim
  · intro hx
    simp at hx

/-- A pointwise upper bound on an `sSup` image over `Set.univ` also covers the
empty-index case when the upper bound is nonnegative. -/
theorem sSup_image_univ_le_of_forall {ι : Type*} (f : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ i, f i ≤ a) :
    sSup (f '' Set.univ) ≤ a := by
  by_cases hι : Nonempty ι
  · refine csSup_le ?nonempty ?upper
    · rcases hι with ⟨i⟩
      exact ⟨f i, ⟨i, Set.mem_univ i, rfl⟩⟩
    · rintro b ⟨i, _hi, rfl⟩
      exact h i
  · rw [image_univ_eq_empty_of_not_nonempty f hι, Real.sSup_empty]
    exact ha

/-- The `sSup` of a nonnegative image over `Set.univ` is nonnegative, with
`sSup ∅ = 0` covering the empty-index case. -/
theorem sSup_image_univ_nonneg_of_forall {ι : Type*} (f : ι → ℝ)
    (hbdd : BddAbove (f '' Set.univ)) (h : ∀ i, 0 ≤ f i) :
    0 ≤ sSup (f '' Set.univ) := by
  by_cases hι : Nonempty ι
  · rcases hι with ⟨i⟩
    exact le_trans (h i) (le_csSup hbdd ⟨i, Set.mem_univ i, rfl⟩)
  · rw [image_univ_eq_empty_of_not_nonempty f hι, Real.sSup_empty]

/-- A supremum indexed by `ι` is bounded by a supremum indexed by `κ` when every
left value appears on the right. The nonnegativity premise handles the case
where the left index type is empty. -/
theorem sSup_image_univ_le_sSup_image_univ_of_forall_exists
    {ι : Type*} {κ : Type*} (f : ι → ℝ) (g : κ → ℝ)
    (hg_bdd : BddAbove (g '' Set.univ))
    (hg_nonneg : ∀ k, 0 ≤ g k)
    (hmap : ∀ i, ∃ k, f i = g k) :
    sSup (f '' Set.univ) ≤ sSup (g '' Set.univ) := by
  by_cases hι : Nonempty ι
  · refine csSup_le ?nonempty ?upper
    · rcases hι with ⟨i⟩
      exact ⟨f i, ⟨i, Set.mem_univ i, rfl⟩⟩
    · rintro b ⟨i, _hi, rfl⟩
      rcases hmap i with ⟨k, hk⟩
      rw [hk]
      exact le_csSup hg_bdd ⟨k, Set.mem_univ k, rfl⟩
  · rw [image_univ_eq_empty_of_not_nonempty f hι, Real.sSup_empty]
    exact sSup_image_univ_nonneg_of_forall g hg_bdd hg_nonneg

/-- A finite `NNReal` supremum coerced to `ℝ` is bounded by any nonnegative
real upper bound on its elements. -/
theorem coe_finset_sup_le {ι : Type*} (s : Finset ι) (f : ι → NNReal) {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ i ∈ s, (f i : ℝ) ≤ a) :
    ((s.sup f : NNReal) : ℝ) ≤ a := by
  let aNN : NNReal := ⟨a, ha⟩
  have hNN : s.sup f ≤ aNN := by
    apply Finset.sup_le
    intro i hi
    exact NNReal.coe_le_coe.mp (h i hi)
  exact NNReal.coe_le_coe.mp hNN

/-- Statistical distance between two distributions.

Paper Definition 3:
  `δ(X, Y) := ∑_{a} max(0, X(a) - Y(a))`

Since `NNReal` subtraction truncates negative values to 0, this is simply:
  `δ(X, Y) = ∑_{a} (X(a) - Y(a))`

where the NNReal subtraction `a - b = max(0, a - b)`. -/
def statDist {A : Type*} [Fintype A] (X Y : Dist A) : NNReal :=
  ∑ a : A, (X a - Y a)

/-- `δ(X, X) = 0`. Immediate because `a - a = 0` for `NNReal`. -/
theorem statDist_self {A : Type*} [Fintype A] (X : Dist A) :
    statDist X X = 0 := by
  simp [statDist, tsub_self]

/-- `δ(X, Y) = δ(Y, X)` when `|X| = |Y|`.

Paper: For distributions of equal weight,
  δ(X,Y) = (1/2) ∑_a |X(a) - Y(a)| = δ(Y,X). -/
theorem statDist_symm_of_eq_weight {A : Type*} [Fintype A]
    (X Y : Dist A) (h : X.weight = Y.weight) :
    statDist X Y = statDist Y X := by
  simp only [statDist]
  have hL : ∀ a : A, X a - Y a = X a - min (X a) (Y a) :=
    fun a => tsub_eq_tsub_min (X a) (Y a)
  have hR : ∀ a : A, Y a - X a = Y a - min (Y a) (X a) :=
    fun a => tsub_eq_tsub_min (Y a) (X a)
  simp_rw [hL, hR]
  rw [Finset.sum_tsub_distrib _ (fun a _ => min_le_left (X a) (Y a))]
  rw [Finset.sum_tsub_distrib _ (fun a _ => min_le_left (Y a) (X a))]
  have hw : ∑ x : A, X x = ∑ x : A, Y x := by
    rw [← Dist.weight_eq_sum X, ← Dist.weight_eq_sum Y]; exact h
  rw [hw]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => min_comm (X a) (Y a))

/-- Triangle inequality for statistical distance.

`δ(X, Z) ≤ δ(X, Y) + δ(Y, Z)`. -/
theorem statDist_triangle {A : Type*} [Fintype A]
    (X Y Z : Dist A) :
    statDist X Z ≤ statDist X Y + statDist Y Z := by
  simp only [statDist]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  exact tsub_le_tsub_add_tsub

/-- Statistical distance is bounded by total weight.

`δ(X, Y) ≤ |X|`. -/
theorem statDist_le_weight {A : Type*} [Fintype A]
    (X Y : Dist A) :
    statDist X Y ≤ X.weight := by
  rw [statDist, Dist.weight_eq_sum]
  apply Finset.sum_le_sum
  intro a _
  exact tsub_le_self

/-- **Support lemma forced by the CR18/thesis advantage bridge; candidate for upstream.**
For any event, the one-sided gap between its masses is bounded by statistical distance. -/
theorem mass_tsub_mass_le_statDist {A : Type*} [Fintype A]
    (X Y : Dist A) (P : A → Prop) :
    X.mass P - Y.mass P ≤ statDist X Y := by
  classical
  rw [tsub_le_iff_right]
  rw [Dist.mass_eq_sum, Dist.mass_eq_sum, statDist]
  calc
    (∑ a : A, if P a then X a else 0)
        ≤ (∑ a : A, if P a then Y a else 0) + ∑ a : A, (X a - Y a) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro a _
          by_cases hp : P a
          · simpa [hp] using (le_add_tsub : X a ≤ Y a + (X a - Y a))
          · simp [hp]
    _ = ∑ a : A, (X a - Y a) + ∑ a : A, if P a then Y a else 0 := by
          rw [add_comm]

/-- **Support lemma forced by the CR18/thesis advantage bridge; candidate for upstream.**
Real-valued form of `mass_tsub_mass_le_statDist`, convenient for signed CR18 advantages. -/
theorem mass_sub_mass_le_statDist {A : Type*} [Fintype A]
    (X Y : Dist A) (P : A → Prop) :
    ((X.mass P : ℝ) - (Y.mass P : ℝ)) ≤ (statDist X Y : ℝ) := by
  calc
    ((X.mass P : ℝ) - (Y.mass P : ℝ))
        ≤ ((X.mass P - Y.mass P : NNReal) : ℝ) := by
          rw [NNReal.coe_sub_def]
          exact le_max_left _ _
    _ ≤ (statDist X Y : ℝ) := by
          exact_mod_cast mass_tsub_mass_le_statDist X Y P

/-- If every pointwise deficit `X a - Y a` is bounded by a charge function,
then statistical distance is bounded by the total charge. -/
theorem statDist_le_sum_of_forall_tsub_le {A : Type*} [Fintype A]
    (X Y : Dist A) (charge : A → NNReal)
    (h : ∀ a, X a - Y a ≤ charge a) :
    statDist X Y ≤ ∑ a, charge a := by
  rw [statDist]
  exact Finset.sum_le_sum (fun a _ => h a)

/-- A one-sided ratio lower bound controls the truncated pointwise deficit. -/
theorem tsub_le_mul_of_one_sub_mul_le {a b eps : NNReal}
    (h_lower : (1 - eps) * b ≤ a) :
    b - a ≤ eps * b := by
  by_cases h_eps : eps ≤ 1
  · suffices h : b - (1 - eps) * b = eps * b by
      calc b - a ≤ b - (1 - eps) * b := tsub_le_tsub_left h_lower _
        _ = eps * b := h
    apply tsub_eq_of_eq_add
    rw [← add_mul, add_comm, tsub_add_cancel_of_le h_eps, one_mul]
  · have h_one_lt_eps : (1 : NNReal) < eps := lt_of_not_ge h_eps
    calc b - a ≤ b := tsub_le_self
      _ = b * 1 := (mul_one b).symm
      _ ≤ b * eps := mul_le_mul_of_nonneg_left (le_of_lt h_one_lt_eps) (zero_le b)
      _ = eps * b := mul_comm b eps

/-- One-sided density lower bound for statistical distance.

If `real` and `ideal` have equal total weight, `ideal` is a subdistribution,
and `(1 - eps) * ideal a <= real a` pointwise, then
`statDist real ideal <= eps`.  This is the distribution-level core of the
one-sided H-technique. -/
theorem statDist_le_of_one_sub_mul_le {A : Type*} [Fintype A]
    (real ideal : Dist A)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ eps := by
  rw [statDist_symm_of_eq_weight real ideal h_weight]
  refine le_trans
    (statDist_le_sum_of_forall_tsub_le ideal real (fun a => eps * ideal a)
      (fun a => tsub_le_mul_of_one_sub_mul_le (h_lower a))) ?_
  calc ∑ a, eps * ideal a
    _ = eps * ∑ a, ideal a := by rw [← Finset.mul_sum]
    _ = eps * ideal.weight := by rw [← Dist.weight_eq_sum ideal]
    _ ≤ eps * 1 := mul_le_mul_of_nonneg_left h_ideal_le (zero_le eps)
    _ = eps := mul_one eps

/-! ### Distribution-level H-technique bounds -/

/-- The mass of the bad event `B` under distribution `D`. -/
noncomputable def probBad {A : Type*}
    (D : Dist A) (B : A → Prop) :
    NNReal :=
  D.mass B

/-- UPSTREAM-CANDIDATE: adding deterministic terminal side information does
not change the mass of a bad event that ignores that terminal component. -/
@[simp]
theorem probBad_const_pair {A U : Type*}
    (D : Dist A) (B : A → Prop) (u : U) :
    probBad (Dist.fTransform (fun a : A => (a, u)) D)
        (fun p : A × U => B p.1) =
      probBad D B := by
  unfold probBad
  rw [Dist.mass_fTransform]

/-- UPSTREAM-CANDIDATE: `probBad` is the finite-carrier predicate mass. -/
theorem probBad_eq_evalPred {A : Type*} [Fintype A] (D : Dist A) (B : A → Prop) :
    probBad D B = D.evalPred B := by
  unfold probBad Dist.evalPred
  rw [Dist.mass_eq_sum, Finset.sum_filter]

/-- UPSTREAM-CANDIDATE: finite union bound for `probBad` events decomposed into
per-index predicates. -/
theorem probBad_iUnion_le {A ι : Type*} [Fintype A] [Fintype ι]
    (D : Dist A) (B : A → Prop) (P : ι → A → Prop) [∀ p, DecidablePred (P p)]
    (hB : ∀ a, B a → ∃ p, P p a) :
    probBad D B ≤ ∑ p, D.evalPred (P p) := by
  rw [probBad_eq_evalPred]
  refine le_trans ?_ (Dist.evalPred_iUnion_le D P)
  apply Finset.sum_le_sum_of_subset
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  exact hB a ha

/-- Extended H-technique: if the real/ideal density ratio is at least
`1 - eps` on good points, then statistical distance is bounded by bad mass plus
`eps`. -/
theorem hTechnique_ratio {A : Type*} [Fintype A]
    (real ideal : Dist A)
    (B : A → Prop)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ probBad ideal B + eps := by
  classical
  rw [statDist_symm_of_eq_weight real ideal h_weight]
  let charge : A → NNReal := fun a => (if B a then ideal a else 0) + eps * ideal a
  have h_term_bound : ∀ a, ideal a - real a ≤ charge a := by
    intro a
    by_cases h_bad : B a
    · simp only [charge, h_bad, if_true]
      exact le_add_right tsub_le_self
    · simp only [charge, h_bad, if_false, zero_add]
      exact tsub_le_mul_of_one_sub_mul_le (h_ratio a h_bad)
  have h_eps_weight_le : eps * ideal.weight ≤ eps := by
    calc eps * ideal.weight ≤ eps * 1 :=
        mul_le_mul_of_nonneg_left h_ideal_le (zero_le eps)
      _ = eps := mul_one eps
  refine le_trans (statDist_le_sum_of_forall_tsub_le ideal real charge h_term_bound) ?_
  calc ∑ a, charge a
    _ = (∑ a, if B a then ideal a else 0) + ∑ a, eps * ideal a := by
        simp only [charge]
        rw [Finset.sum_add_distrib]
    _ = (∑ a, if B a then ideal a else 0) + eps * ∑ a, ideal a := by
        rw [← Finset.mul_sum]
    _ = probBad ideal B + eps * ideal.weight := by
        rw [probBad, Dist.mass_eq_sum, ← Dist.weight_eq_sum ideal]
    _ ≤ probBad ideal B + eps :=
        add_le_add_right h_eps_weight_le _

/-- Expectation-method H-technique bound with a point-dependent error term. -/
theorem hTechnique_expectation {A : Type*} [Fintype A]
    (real ideal : Dist A)
    (B : A → Prop) [DecidablePred B]
    (eps : A → NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ratio : ∀ a, ¬ B a → (1 - eps a) * ideal a ≤ real a) :
    statDist real ideal ≤ probBad ideal B +
      ideal.sum (fun a w => if ¬ B a then w * eps a else 0) := by
  classical
  rw [statDist_symm_of_eq_weight real ideal h_weight]
  let charge : A → NNReal :=
    fun a => (if B a then ideal a else 0) + if ¬ B a then ideal a * eps a else 0
  have h_term_bound : ∀ a, ideal a - real a ≤ charge a := by
    intro a
    by_cases h_bad : B a
    · simp only [charge, h_bad, if_true, not_true_eq_false, if_false, add_zero]
      exact tsub_le_self
    · simp only [charge, h_bad, if_false, not_false_eq_true, if_true, zero_add]
      simpa [mul_comm] using tsub_le_mul_of_one_sub_mul_le (h_ratio a h_bad)
  refine le_trans (statDist_le_sum_of_forall_tsub_le ideal real charge h_term_bound) ?_
  have hsum :
      ideal.sum (fun a w => if ¬ B a then w * eps a else 0) =
        ∑ a, if ¬ B a then ideal a * eps a else 0 := by
    exact Finsupp.sum_fintype _ _ (fun a => by by_cases h : B a <;> simp [h])
  calc ∑ a, charge a
    _ = (∑ a, if B a then ideal a else 0) +
          ∑ a, if ¬ B a then ideal a * eps a else 0 := by
        simp only [charge]
        rw [Finset.sum_add_distrib]
    _ = probBad ideal B + ideal.sum (fun a w => if ¬ B a then w * eps a else 0) := by
        rw [probBad, Dist.mass_eq_sum, hsum]
        congr 1
        apply Finset.sum_congr rfl
        intro a _ha
        by_cases h : B a <;> simp [h]
    _ ≤ probBad ideal B + ideal.sum (fun a w => if ¬ B a then w * eps a else 0) := le_rfl

/-- When real and ideal agree exactly on good points, statistical distance is
bounded by the ideal bad probability. -/
theorem hTechnique_eq_on_good {A : Type*} [Fintype A]
    (real ideal : Dist A)
    (B : A → Prop)
    (h_weight : real.weight = ideal.weight)
    (h_eq : ∀ a, ¬ B a → real a = ideal a) :
    statDist real ideal ≤ probBad ideal B := by
  classical
  rw [statDist_symm_of_eq_weight real ideal h_weight]
  refine le_trans
    (statDist_le_sum_of_forall_tsub_le ideal real (fun a => if B a then ideal a else 0) ?_) ?_
  · intro a
    by_cases h_bad : B a
    · simp [h_bad]
    · simp [h_bad, h_eq a h_bad]
  · rw [probBad, Dist.mass_eq_sum]

/-- One-sided H-technique: if `(1 - eps) * ideal(a) <= real(a)` for all points,
then `statDist real ideal <= eps`. -/
theorem oneSided_hTechnique {A : Type*} [Fintype A]
    (real ideal : Dist A)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ eps := by
  exact statDist_le_of_one_sub_mul_le real ideal eps h_weight h_ideal_le h_lower

/-- The one-sided H-technique is stable under a common deterministic
post-processing. -/
theorem oneSided_hTechnique_fTransform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (real ideal : Dist A) (f : A → B)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist (Dist.fTransform f real) (Dist.fTransform f ideal) ≤ eps := by
  refine oneSided_hTechnique (Dist.fTransform f real)
    (Dist.fTransform f ideal) eps ?_ ?_ ?_
  · rw [Dist.weight_fTransform, Dist.weight_fTransform, h_weight]
  · rwa [Dist.weight_fTransform]
  · intro b
    exact Dist.mul_fTransform_le_fTransform_of_forall_mul_le
      ideal real f (1 - eps) h_lower b

/-- One-sided H-technique with probability-distribution hypotheses. -/
theorem oneSided_hTechnique_proper {A : Type*} [Fintype A]
    (real ideal : Dist A)
    (eps : NNReal)
    (h_real_proper : real.weight = 1)
    (h_ideal_proper : ideal.weight = 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ eps := by
  exact oneSided_hTechnique real ideal eps
    (by rw [h_real_proper, h_ideal_proper]) (by rw [h_ideal_proper]) h_lower

/-- Ratio-form H-technique applied to finite mass functions rather than
explicit `Dist` objects. -/
theorem hTechnique_ratio_massFunction {A : Type*} [Fintype A]
    (real ideal : A → NNReal)
    (B : A → Prop)
    (eps : NNReal)
    (h_weight :
      (Dist.ofFiniteMassFunction real).weight =
        (Dist.ofFiniteMassFunction ideal).weight)
    (h_ideal_le : (Dist.ofFiniteMassFunction ideal).weight ≤ 1)
    (h_ratio : ∀ a, ¬ B a → (1 - eps) * ideal a ≤ real a) :
    statDist (Dist.ofFiniteMassFunction real)
        (Dist.ofFiniteMassFunction ideal) ≤
      probBad (Dist.ofFiniteMassFunction ideal) B + eps := by
  exact hTechnique_ratio (Dist.ofFiniteMassFunction real)
    (Dist.ofFiniteMassFunction ideal) B eps h_weight h_ideal_le (by
      intro a ha
      simpa using h_ratio a ha)

/-- One-sided H-technique applied to finite mass functions rather than explicit
`Dist` objects. -/
theorem oneSided_hTechnique_massFunction {A : Type*} [Fintype A]
    (real ideal : A → NNReal)
    (eps : NNReal)
    (h_weight :
      (Dist.ofFiniteMassFunction real).weight =
        (Dist.ofFiniteMassFunction ideal).weight)
    (h_ideal_le : (Dist.ofFiniteMassFunction ideal).weight ≤ 1)
    (h_lower : ∀ a, (1 - eps) * ideal a ≤ real a) :
    statDist (Dist.ofFiniteMassFunction real)
      (Dist.ofFiniteMassFunction ideal) ≤ eps := by
  exact oneSided_hTechnique (Dist.ofFiniteMassFunction real)
    (Dist.ofFiniteMassFunction ideal) eps h_weight h_ideal_le (by
      intro a
      simpa using h_lower a)

/-- Lemma 2 (Partition of statistical distance).

For any partition {Aⱼ} of A:
  δ(X, Y) = ∑_j δ(X_j, Y_j)
where X_j, Y_j are X, Y restricted to Aⱼ. -/
theorem statDist_partition {A : Type*} [Fintype A] {n : ℕ}
    (X Y : Dist A) (P : A → Fin n) :
    statDist X Y = ∑ j : Fin n, ∑ a ∈ Finset.univ.filter (fun a => P a = j), (X a - Y a) := by
  simp only [statDist]
  exact (Finset.sum_fiberwise Finset.univ P _).symm

/-- Pointwise evaluation of `Finsupp.mapDomain` as a finite fiber sum.

This is the stable fiber-sum form needed by the statistical-distance
data-processing proof. -/
theorem mapDomain_apply_eq_sum {A B : Type*} [DecidableEq B] [Fintype A]
    (f : A → B) (X : A →₀ NNReal) (b : B) :
    Finsupp.mapDomain f X b = ∑ a ∈ Finset.univ.filter (fun a => f a = b), X a := by
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  rw [← Finset.sum_filter (p := fun x => f x = b)]
  apply Finset.sum_subset
  · exact Finset.filter_subset_filter _ (Finset.subset_univ _)
  · intro a ha1 ha2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha1
    simp only [Finset.mem_filter, not_and] at ha2
    exact Finsupp.notMem_support_iff.mp (by tauto)

/-- Lemma 3 (Data processing inequality).

For any function f : A → B:
  δ(f(X), f(Y)) ≤ δ(X, Y).

Applying a function can only decrease statistical distance.

Paper proof (Appendix A): δ(f(X), f(Y)) = ∑_b max(0, ∑_{f(a)=b} (X(a) - Y(a)))
  ≤ ∑_b ∑_{f(a)=b} max(0, X(a) - Y(a)) = ∑_a max(0, X(a) - Y(a)) = δ(X,Y). -/
theorem statDist_fTransform_le {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (X Y : Dist A) (f : A → B) :
    statDist (Dist.fTransform f X) (Dist.fTransform f Y) ≤ statDist X Y := by
  simp only [statDist]
  have hfX : Dist.fTransform f X = Finsupp.mapDomain f X := by
    simp [Dist.fTransform, Finsupp.mapDomain]
  have hfY : Dist.fTransform f Y = Finsupp.mapDomain f Y := by
    simp [Dist.fTransform, Finsupp.mapDomain]
  rw [hfX, hfY]
  rw [show ∑ a : A, (X a - Y a) =
      ∑ b : B, ∑ a ∈ Finset.univ.filter (fun a => f a = b), (X a - Y a)
    from (Finset.sum_fiberwise Finset.univ f _).symm]
  apply Finset.sum_le_sum
  intro b _
  rw [mapDomain_apply_eq_sum f X b, mapDomain_apply_eq_sum f Y b]
  rw [tsub_le_iff_right, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  exact le_tsub_add

/-- Exact-on-good H-technique bounds are stable under common deterministic
post-processing.

This is the exact-agreement version of `hTechnique_ratio_fTransform`: prove
that real and ideal agree on good points of a richer finite law, then apply a
projection or any other deterministic map. -/
theorem hTechnique_eq_on_good_fTransform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (real ideal : Dist A) (f : A → B)
    (Bad : A → Prop)
    (h_weight : real.weight = ideal.weight)
    (h_eq : ∀ a, ¬ Bad a → real a = ideal a) :
    statDist (Dist.fTransform f real) (Dist.fTransform f ideal) ≤
      probBad ideal Bad := by
  exact le_trans
    (statDist_fTransform_le real ideal f)
    (hTechnique_eq_on_good real ideal Bad h_weight h_eq)

/-- Ratio-form H-technique bounds are stable under common deterministic
post-processing.

This is the generic data-processing step used by extended-transcript
arguments: prove the H-coefficient ratio on the richer finite law, then apply a
projection or any other deterministic map. -/
theorem hTechnique_ratio_fTransform {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq B]
    (real ideal : Dist A) (f : A → B)
    (Bad : A → Prop)
    (eps : NNReal)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ Bad a → (1 - eps) * ideal a ≤ real a) :
    statDist (Dist.fTransform f real) (Dist.fTransform f ideal) ≤
      probBad ideal Bad + eps := by
  exact le_trans
    (statDist_fTransform_le real ideal f)
    (hTechnique_ratio real ideal Bad eps h_weight h_ideal_le h_ratio)

/-- First-projection specialization of `hTechnique_ratio_fTransform`.

This is the distribution-level form of terminal side-information removal: prove
the H-coefficient ratio on a law over `A × Side`, then forget `Side`. -/
theorem hTechnique_ratio_project_fst {A Side : Type*}
    [Fintype A] [Fintype Side] [DecidableEq A]
    (realExt idealExt : Dist (A × Side))
    (Bad : A × Side → Prop)
    (eps : NNReal)
    (h_weight : realExt.weight = idealExt.weight)
    (h_ideal_le : idealExt.weight ≤ 1)
    (h_ratio : ∀ a, ¬ Bad a → (1 - eps) * idealExt a ≤ realExt a) :
    statDist
        (Dist.fTransform (fun a : A × Side => a.1) realExt)
        (Dist.fTransform (fun a : A × Side => a.1) idealExt) ≤
      probBad idealExt Bad + eps := by
  exact hTechnique_ratio_fTransform realExt idealExt (fun a : A × Side => a.1)
    Bad eps h_weight h_ideal_le h_ratio

/-- If Y = 0 on S and X ≤ Y pointwise on Sᶜ, then statDist(X, Y) = ∑_{S} X(a).

This is the core pattern for "zero on bad, dominated on good" arguments in
switching-style proofs (e.g., PRP/PRF switching, CBC-MAC). -/
theorem statDist_eq_mass_on_zero_support {A : Type*} [Fintype A] [DecidableEq A]
    (X Y : Dist A) (S : Finset A)
    (h_zero : ∀ a ∈ S, Y a = 0)
    (h_le : ∀ a ∉ S, X a ≤ Y a) :
    statDist X Y = ∑ a ∈ S, X a := by
  simp only [statDist]
  rw [show ∑ a : A, (X a - Y a) =
      ∑ a ∈ S, (X a - Y a) + ∑ a ∈ Sᶜ, (X a - Y a) from by
    rw [← Finset.sum_union disjoint_compl_right, Finset.union_compl]]
  have h_on_S : ∑ a ∈ S, (X a - Y a) = ∑ a ∈ S, X a := by
    apply Finset.sum_congr rfl
    intro a ha; rw [h_zero a ha, tsub_zero]
  have h_on_Sc : ∑ a ∈ Sᶜ, (X a - Y a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    exact tsub_eq_zero_of_le (h_le a (Finset.mem_compl.mp ha))
  rw [h_on_S, h_on_Sc, add_zero]

/-- For an injective function, fTransform at the image point gives the original value.

  (f(X))(f(a)) = X(a) -/
theorem fTransform_injective_apply {A B : Type*} [Fintype A] [DecidableEq B]
    (X : Dist A) (f : A → B) (hf : Function.Injective f) (a : A) :
    (Dist.fTransform f X) (f a) = X a := by
  exact Dist.fTransform_injective_apply X f hf a

/-- Lemma 3+ (Data processing equality for injective functions).

For any injective function f : A → B:
  δ(f(X), f(Y)) = δ(X, Y).

An injective function preserves statistical distance exactly (not just ≤). -/
theorem statDist_fTransform_injective {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (X Y : Dist A) (f : A → B) (hf : Function.Injective f) :
    statDist (Dist.fTransform f X) (Dist.fTransform f Y) = statDist X Y := by
  apply le_antisymm
  · exact statDist_fTransform_le X Y f
  · simp only [statDist]
    rw [show ∑ a : A, (X a - Y a) =
        ∑ a : A, ((Dist.fTransform f X) (f a) - (Dist.fTransform f Y) (f a)) from by
      congr 1; ext a; rw [fTransform_injective_apply X f hf, fTransform_injective_apply Y f hf]]
    calc ∑ a : A, ((Dist.fTransform f X) (f a) - (Dist.fTransform f Y) (f a))
        = ∑ b ∈ Finset.univ.image f, ((Dist.fTransform f X) b - (Dist.fTransform f Y) b) := by
          rw [Finset.sum_image (fun a _ b _ h => hf h)]
      _ ≤ ∑ b : B, ((Dist.fTransform f X) b - (Dist.fTransform f Y) b) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro b _ _; exact zero_le _

/-- UPSTREAM-CANDIDATE: adding a deterministic terminal component preserves
statistical distance exactly.

This is the conservative-extension test for terminal side-information
arguments: when the side-information variable is constant, the extended law is
isometric to the original law. -/
theorem statDist_fTransform_const_pair {A U : Type*} [Fintype A] [Fintype U]
    (X Y : Dist A) (u : U) :
    statDist
        (Dist.fTransform (fun a : A => (a, u)) X)
        (Dist.fTransform (fun a : A => (a, u)) Y) =
      statDist X Y := by
  classical
  exact statDist_fTransform_injective X Y (fun a : A => (a, u))
    (fun _ _ h => congrArg Prod.fst h)

/-- UPSTREAM-CANDIDATE: adding deterministic terminal side information and
then projecting it away recovers the original statistical distance.

This is the conservative-extension regression for extended H-technique
arguments: when the terminal side-information variable is constant, the
projected extended law is exactly the original law. -/
theorem statDist_project_const_pair {A U : Type*} [Fintype A] [Fintype U]
    (X Y : Dist A) (u : U) :
    statDist
        (Dist.fTransform (fun p : A × U => p.1)
          (Dist.fTransform (fun a : A => (a, u)) X))
        (Dist.fTransform (fun p : A × U => p.1)
          (Dist.fTransform (fun a : A => (a, u)) Y)) =
      statDist X Y := by
  rw [Dist.fTransform_fst_const_pair, Dist.fTransform_fst_const_pair]

/-- Statistical distance between product distributions with a shared left factor.

If `U` is a distribution on `A` and `X,Y` are distributions on `B`, then:

`δ(U × X, U × Y) = |U| * δ(X, Y)`.

In particular, if `U` is a probability distribution (`|U| = 1`), then taking an
independent product with `U` does not change statistical distance. -/
theorem statDist_prod_left {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    [DecidableEq A] [DecidableEq B]
    (U : Dist A) (X Y : Dist B) :
    statDist (Dist.prod U X) (Dist.prod U Y) = U.weight * statDist X Y := by
  classical
  -- Expand both `statDist`s and the shared weight `|U| = ∑ U`, then match the
  -- product distributions summand-by-summand (`prod_apply`, `mul_tsub`).
  simp only [statDist, Fintype.sum_prod_type]
  rw [Dist.weight_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Dist.prod_apply, Dist.prod_apply, mul_tsub]

end RandomSystems
