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
  have hw : ∑ x : A, X x = ∑ x : A, Y x := h
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
  apply Finset.sum_le_sum
  intro a _
  exact tsub_le_self

/-- Lemma 2 (Partition of statistical distance).

For any partition {Aⱼ} of A:
  δ(X, Y) = ∑_j δ(X_j, Y_j)
where X_j, Y_j are X, Y restricted to Aⱼ. -/
theorem statDist_partition {A : Type*} [Fintype A] {n : ℕ}
    (X Y : Dist A) (P : A → Fin n) :
    statDist X Y = ∑ j : Fin n, ∑ a ∈ Finset.univ.filter (fun a => P a = j), (X a - Y a) := by
  simp only [statDist]
  exact (Finset.sum_fiberwise Finset.univ P _).symm

/-- Lemma 3 (Data processing inequality).

For any function f : A → B:
  δ(f(X), f(Y)) ≤ δ(X, Y).

Applying a function can only decrease statistical distance. -/
private lemma mapDomain_apply_eq_sum {A B : Type*} [DecidableEq B] [Fintype A]
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
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba; simp [hf.ne hba]
  · intro ha; simp [Finsupp.notMem_support_iff.mp ha]

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

/-- Statistical distance between product distributions with a shared left factor.

If `U` is a distribution on `A` and `X,Y` are distributions on `B`, then:

`δ(U × X, U × Y) = |U| * δ(X, Y)`.

In particular, if `U` is a probability distribution (`|U| = 1`), then taking an
independent product with `U` does not change statistical distance. -/
theorem statDist_prod_left {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (U : Dist A) (X Y : Dist B) :
    statDist (Dist.prod U X) (Dist.prod U Y) = U.weight * statDist X Y := by
  classical
  -- Expand δ as a double sum and factor out the shared left component `U`.
  simp [statDist, Dist.weight, Dist.prod_apply, Fintype.sum_prod_type, ← mul_tsub,
    Finset.mul_sum, Finset.sum_mul]
  -- The remaining goal is just commutativity of double sums.
  simpa using
    (Finset.sum_comm :
      (∑ a : A, ∑ b : B, U a * (X b - Y b)) = ∑ b : B, ∑ a : A, U a * (X b - Y b))

end RandomSystems
