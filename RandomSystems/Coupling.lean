/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StatDist

/-!
# Coupling Lemma

Lean 4 formalization of Lemma 4 from Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `DistCoupling X Y` — a coupling of distributions X and Y
* `coupling_bound` — the coupling lemma: δ(X, Y) ≤ Pr(X ≠ Y)
* `optimal_coupling_exists` — existence of an optimal coupling achieving equality

## Design Notes

A coupling of distributions X over A and Y over A is a joint
distribution Z over A × A such that:
  - marginal₁(Z) = X
  - marginal₂(Z) = Y

The coupling lemma states δ(X, Y) ≤ Pr_{(a,b)~Z}(a ≠ b).
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- A coupling of two distributions over `A`: a joint distribution
over `A × A` whose marginals are the given distributions.

Paper Lemma 4 setup: "Let Z be a joint distribution on A × A with
marginals X and Y." -/
structure DistCoupling (X Y : Dist A) where
  /-- The joint distribution over A × A. -/
  joint : Dist (A × A)
  /-- First marginal equals X. -/
  marginal_fst : Dist.fTransform Prod.fst joint = X
  /-- Second marginal equals Y. -/
  marginal_snd : Dist.fTransform Prod.snd joint = Y

/-- The probability of disagreement in a coupling.
  Pr(X ≠ Y) := ∑_{(a,b) : a ≠ b} Z(a, b) -/
def DistCoupling.prDisagree {X Y : Dist A} (C : DistCoupling X Y) : NNReal :=
  ∑ p ∈ (Finset.univ : Finset (A × A)).filter (fun p => p.1 ≠ p.2),
    C.joint p

-- Helper: fTransform Prod.fst evaluates to ∑ over second component
private lemma fTransform_fst_eval
    (joint : Dist (A × A)) (a : A) :
    (Dist.fTransform Prod.fst joint) a = ∑ b : A, joint (a, b) := by
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  trans (∑ p ∈ (Finset.univ : Finset (A × A)), if p.1 = a then joint p else 0)
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp; rw [Finsupp.notMem_support_iff.mp hp]; simp
  · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    conv_rhs => rw [show (∑ b : A, joint (a, b)) =
        ∑ p ∈ (Finset.univ : Finset A).map ⟨fun b => (a, b), fun b1 b2 h => by simpa using h⟩,
          joint p from by rw [Finset.sum_map]; simp]
    congr 1; ext ⟨x, y⟩; simp [eq_comm]

-- Helper: fTransform Prod.snd evaluates to ∑ over first component
private lemma fTransform_snd_eval
    (joint : Dist (A × A)) (a : A) :
    (Dist.fTransform Prod.snd joint) a = ∑ b : A, joint (b, a) := by
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.single_apply]
  trans (∑ p ∈ (Finset.univ : Finset (A × A)), if p.2 = a then joint p else 0)
  · apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp; rw [Finsupp.notMem_support_iff.mp hp]; simp
  · simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    conv_rhs => rw [show (∑ b : A, joint (b, a)) =
        ∑ p ∈ (Finset.univ : Finset A).map ⟨fun b => (b, a), fun b1 b2 h => by simpa using h⟩,
          joint p from by rw [Finset.sum_map]; simp]
    congr 1; ext ⟨x, y⟩; simp [eq_comm]

/-- **Coupling Lemma** (Paper Lemma 4).

For any coupling Z of X and Y:
  δ(X, Y) ≤ Pr_{Z}(X ≠ Y)

Proof: X(a) = ∑_b Z(a,b), Y(a) = ∑_b Z(b,a).
  X(a) - Y(a) ≤ ∑_b Z(a,b) - Z(a,a) = ∑_{b≠a} Z(a,b).
  Sum over a gives Pr(X ≠ Y). -/
theorem coupling_bound {X Y : Dist A} (C : DistCoupling X Y) :
    statDist X Y ≤ C.prDisagree := by
  simp only [statDist, DistCoupling.prDisagree]
  have hX : ∀ a, X a = ∑ b, C.joint (a, b) := by
    intro a
    have := fTransform_fst_eval C.joint a
    rw [C.marginal_fst] at this; exact this
  have hY : ∀ a, Y a = ∑ b, C.joint (b, a) := by
    intro a
    have := fTransform_snd_eval C.joint a
    rw [C.marginal_snd] at this; exact this
  -- Pointwise: X a - Y a ≤ ∑_{b≠a} joint(a,b)
  have h_pw : ∀ a, X a - Y a ≤
      ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), C.joint (a, b) := by
    intro a
    rw [hX, hY]
    calc ∑ b : A, C.joint (a, b) - ∑ b : A, C.joint (b, a)
        ≤ ∑ b : A, C.joint (a, b) - C.joint (a, a) :=
          tsub_le_tsub_left
            (Finset.single_le_sum (fun b _ => zero_le _) (Finset.mem_univ a)) _
      _ = ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), C.joint (a, b) := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_tsub_cancel_left]
          congr 1; ext b; simp [Finset.mem_erase]
  -- Sum over a and rearrange
  calc ∑ a, (X a - Y a)
      ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => b ≠ a), C.joint (a, b) :=
        Finset.sum_le_sum (fun a _ => h_pw a)
    _ = ∑ p ∈ Finset.univ.filter (fun p : A × A => p.1 ≠ p.2), C.joint p := by
        simp only [Finset.sum_filter]
        rw [← Finset.sum_product']
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
        congr 1; ext ⟨a, b⟩; simp [ne_comm]

/-- The joint distribution for the optimal coupling.

joint(a, b) = min(X(a), Y(a))  if a = b
            = (X(a) - Y(a)) * (Y(b) - X(b)) / W  otherwise
where W = statDist X Y. -/
private def optimalJoint (X Y : Dist A) : Dist (A × A) :=
  Finsupp.equivFunOnFinite.invFun (fun ⟨a, b⟩ =>
    if a = b then min (X a) (Y a)
    else (X a - Y a) * (Y b - X b) / statDist X Y)

private lemma optimalJoint_eval (X Y : Dist A) (a b : A) :
    optimalJoint X Y (a, b) =
      if a = b then min (X a) (Y a)
      else (X a - Y a) * (Y b - X b) / statDist X Y := by
  simp [optimalJoint, Finsupp.equivFunOnFinite]

-- NNReal: (a - b) * (b - a) = 0
private lemma tsub_mul_tsub_self (a b : NNReal) : (a - b) * (b - a) = 0 := by
  rcases le_total a b with h | h
  · simp [tsub_eq_zero_of_le h]
  · simp [tsub_eq_zero_of_le h]

-- NNReal: min(a,b) + (a - b) = a
private lemma min_add_tsub (a b : NNReal) : min a b + (a - b) = a := by
  rcases le_total a b with h | h
  · simp [min_eq_left h, tsub_eq_zero_of_le h]
  · simp [min_eq_right h, add_tsub_cancel_of_le h]

omit [DecidableEq A] in
/-- Sum of (X a - Y a) over all a equals sum of (Y a - X a) when weights are equal. -/
private lemma statDist_symm_eq (X Y : Dist A) (hw : X.weight = Y.weight) :
    ∑ a : A, (X a - Y a) = ∑ a : A, (Y a - X a) := by
  have := statDist_symm_of_eq_weight X Y hw
  simp only [statDist] at this
  exact this

omit [DecidableEq A] in
/-- The sum ∑_b (X a - Y a) * (Y b - X b) / W over all b equals (X a - Y a). -/
private lemma sum_off_diag_eq (X Y : Dist A) (hw : X.weight = Y.weight) (a : A) :
    ∑ b : A, (X a - Y a) * (Y b - X b) / statDist X Y = X a - Y a := by
  by_cases hW : statDist X Y = 0
  · -- W = 0 → each X a - Y a = 0
    have h0 : X a - Y a = 0 :=
      Finset.sum_eq_zero_iff.mp hW a (Finset.mem_univ a)
    simp [h0]
  · -- Use a / b = a * b⁻¹ to factor out the inverse
    simp_rw [div_eq_mul_inv, mul_assoc]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have hsum : ∑ b : A, (Y b - X b) = statDist X Y :=
      (statDist_symm_eq X Y hw).symm
    rw [hsum, mul_inv_cancel₀ hW, mul_one]

/-- Sum over b of optimalJoint(a, b) = X(a). -/
private lemma optimal_marginal_fst (X Y : Dist A) (hw : X.weight = Y.weight) (a : A) :
    ∑ b : A, optimalJoint X Y (a, b) = X a := by
  simp_rw [optimalJoint_eval]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  simp only [ite_true]
  have h_off : ∀ b ∈ Finset.univ.erase a,
      (if a = b then min (X a) (Y a) else (X a - Y a) * (Y b - X b) / statDist X Y) =
      (X a - Y a) * (Y b - X b) / statDist X Y := by
    intro b hb; exact if_neg (Ne.symm (Finset.ne_of_mem_erase hb))
  rw [Finset.sum_congr rfl h_off]
  -- Add back diagonal off-diag term (which is 0) to get full sum
  have h_diag_zero : (X a - Y a) * (Y a - X a) / statDist X Y = 0 := by
    rw [tsub_mul_tsub_self]; simp
  rw [show ∑ b ∈ Finset.univ.erase a, (X a - Y a) * (Y b - X b) / statDist X Y =
      ∑ b : A, (X a - Y a) * (Y b - X b) / statDist X Y from by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a), h_diag_zero, add_zero]]
  rw [sum_off_diag_eq X Y hw a]
  exact min_add_tsub (X a) (Y a)

/-- Sum over a of optimalJoint(a, b) = Y(b). -/
private lemma optimal_marginal_snd (X Y : Dist A) (hw : X.weight = Y.weight) (b : A) :
    ∑ a : A, optimalJoint X Y (a, b) = Y b := by
  simp_rw [optimalJoint_eval]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  simp only [ite_true, min_comm (X b) (Y b)]
  have h_off : ∀ a ∈ Finset.univ.erase b,
      (if a = b then min (X a) (Y a) else (X a - Y a) * (Y b - X b) / statDist X Y) =
      (X a - Y a) * (Y b - X b) / statDist X Y := by
    intro a ha; exact if_neg (Finset.ne_of_mem_erase ha)
  rw [Finset.sum_congr rfl h_off]
  have h_diag_zero : (X b - Y b) * (Y b - X b) / statDist X Y = 0 := by
    rw [tsub_mul_tsub_self]; simp
  -- Add back diagonal term to get full sum, then factor
  rw [show ∑ a ∈ Finset.univ.erase b, (X a - Y a) * (Y b - X b) / statDist X Y =
      ∑ a : A, (X a - Y a) * (Y b - X b) / statDist X Y from by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b), h_diag_zero, add_zero]]
  -- Factor out (Y b - X b) / W from the sum
  by_cases hW : statDist X Y = 0
  · -- W = 0 → X = Y pointwise
    have hXY : ∀ a, X a = Y a := by
      intro a
      apply le_antisymm
      · exact tsub_eq_zero_iff_le.mp (Finset.sum_eq_zero_iff.mp hW a (Finset.mem_univ a))
      · have hW' : ∑ a : A, (Y a - X a) = 0 := by
          rw [← statDist_symm_eq X Y hw]; exact hW
        exact tsub_eq_zero_iff_le.mp (Finset.sum_eq_zero_iff.mp hW' a (Finset.mem_univ a))
    simp only [hXY, tsub_self, mul_zero, zero_div, Finset.sum_const_zero, min_self, add_zero]
  · -- Factor: ∑_a (X a - Y a) * (Y b - X b) / W = (Y b - X b) * W / W = Y b - X b
    simp_rw [div_eq_mul_inv, mul_comm (X _ - Y _) (Y b - X b), mul_assoc]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have hsum : ∑ a : A, (X a - Y a) = statDist X Y := rfl
    rw [hsum, mul_inv_cancel₀ hW, mul_one]
    exact min_add_tsub (Y b) (X b)

/-- The prDisagree of the optimal coupling equals statDist. -/
private lemma optimal_prDisagree (X Y : Dist A) (hw : X.weight = Y.weight) :
    ∑ p ∈ (Finset.univ : Finset (A × A)).filter (fun p => p.1 ≠ p.2),
      optimalJoint X Y p = statDist X Y := by
  by_cases hW : statDist X Y = 0
  · -- W = 0: all off-diagonal terms are 0
    rw [hW]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hp
    rw [optimalJoint_eval]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rw [if_neg hp]
    have : X a - Y a = 0 := Finset.sum_eq_zero_iff.mp hW a (Finset.mem_univ a)
    simp [this]
  · -- W ≠ 0: factor the sum as W * W / W = W
    -- Each off-diagonal entry is (X a - Y a) * (Y b - X b) / W
    have h_eval : ∀ p ∈ (Finset.univ : Finset (A × A)).filter (fun p => p.1 ≠ p.2),
        optimalJoint X Y p = (X p.1 - Y p.1) * (Y p.2 - X p.2) / statDist X Y := by
      intro ⟨a, b⟩ hp
      rw [optimalJoint_eval]
      exact if_neg (Finset.mem_filter.mp hp).2
    rw [Finset.sum_congr rfl h_eval]
    -- Off-diagonal sum = full sum (diagonal contributes 0)
    have h_off_eq_full :
        ∑ p ∈ Finset.univ.filter (fun p : A × A => p.1 ≠ p.2),
          (X p.1 - Y p.1) * (Y p.2 - X p.2) / statDist X Y =
        ∑ p : A × A, (X p.1 - Y p.1) * (Y p.2 - X p.2) / statDist X Y := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl; intro ⟨a, b⟩ _
      split_ifs with h
      · rfl
      · simp only [ne_eq, not_not] at h; subst h
        simp [tsub_mul_tsub_self]
    rw [h_off_eq_full]
    -- ∑ (a,b), f(a)*g(b)/W = (∑ f) * (∑ g) / W = W*W/W = W
    -- First, pull the /W out of the sum
    rw [show ∑ p : A × A, (X p.1 - Y p.1) * (Y p.2 - X p.2) / statDist X Y =
        (∑ p : A × A, (X p.1 - Y p.1) * (Y p.2 - X p.2)) / statDist X Y from by
      simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]]
    -- Factor numerator: ∑ (a,b), f(a)*g(b) = (∑ f) * (∑ g)
    rw [show ∑ p : A × A, (X p.1 - Y p.1) * (Y p.2 - X p.2) =
        (∑ a : A, (X a - Y a)) * (∑ b : A, (Y b - X b)) from by
      rw [Fintype.sum_prod_type]; simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul]]
    have hsum1 : ∑ a : A, (X a - Y a) = statDist X Y := rfl
    have hsum2 : ∑ b : A, (Y b - X b) = statDist X Y :=
      (statDist_symm_eq X Y hw).symm
    rw [hsum2, hsum1, mul_div_assoc, div_self hW, mul_one]

/-- **Optimal coupling existence** (Paper Lemma 4, converse direction).

For distributions X, Y with equal weight, there exists a coupling Z with
  δ(X, Y) = Pr_{Z}(X ≠ Y)

Equal weight is necessary since a coupling forces marginals to share mass. -/
theorem optimal_coupling_exists (X Y : Dist A) (hw : X.weight = Y.weight) :
    ∃ C : DistCoupling X Y, statDist X Y = C.prDisagree := by
  refine ⟨⟨optimalJoint X Y, ?_, ?_⟩, ?_⟩
  · -- marginal_fst
    exact Finsupp.ext (fun a => by rw [fTransform_fst_eval]; exact optimal_marginal_fst X Y hw a)
  · -- marginal_snd
    exact Finsupp.ext (fun b => by rw [fTransform_snd_eval]; exact optimal_marginal_snd X Y hw b)
  · -- prDisagree = statDist
    exact (optimal_prDisagree X Y hw).symm

end RandomSystems
