/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic
import RandomSystems.Counting

/-!
# H-technique counting lemmas

This is the first dependency-free slice migrated from the external
`/Users/marcilunga/Documents/ToB/research/fv/h-technique` project.

Source status:

* source theorem: Jha-Nandi Proposition 8.1 counting core for the
  sum-of-permutations application.

The file intentionally has no dependency on the old `RandomSystems.*` surface
and no dependency on the external `HTechnique` package.  Generic product,
falling-factorial, cubic query-bound arithmetic, function-fiber, and
permutation-fiber counting facts live in `RandomSystems.CR18.Counting` and are
used directly rather than re-aliased here.
-/

open scoped BigOperators

namespace RandomSystems
namespace HTechnique
namespace Counting

/-! ## SoP ratio-counting core -/

/-- **Support lemma forced by formalization; Jha-Nandi Proposition 8.1
counting core.**  The normalized SoP fiber lower bound dominates
`(1 - q^3/size^2) / size^q`. -/
lemma sop_ratio_counting_bound {size q : ℕ} (h_pos : 0 < size) (h_cube : q ^ 3 ≤ size ^ 2) :
    (1 - (q : NNReal) ^ 3 / ((size : NNReal)) ^ 2) * (1 / (size : NNReal) ^ q) ≤
      (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : NNReal)
        / ((size.factorial : NNReal) ^ 2) := by
  have hq_le : q ≤ size := RandomSystems.CR18.Counting.q_le_of_cube_le_sq h_cube
  have hstep : 2 * (q - 1) ≤ size :=
    RandomSystems.CR18.Counting.two_mul_pred_le_of_cube_sq h_pos h_cube
  have h_nonneg : ∀ k < q, 0 ≤ ((k : ℝ) / ((size : ℝ) - k)) ^ 2 := by
    intro k hk
    positivity
  have h_le_one : ∀ k < q, ((k : ℝ) / ((size : ℝ) - k)) ^ 2 ≤ 1 := by
    intro k hk
    have hk_le_pred : k ≤ q - 1 := Nat.le_pred_of_lt hk
    have h2k : 2 * k ≤ size := le_trans (Nat.mul_le_mul_left _ hk_le_pred) hstep
    have hk_size : k < size := lt_of_lt_of_le hk hq_le
    have hk_real : (k : ℝ) < size := by
      exact_mod_cast hk_size
    have hsk_pos : (0 : ℝ) < (size : ℝ) - k := by
      linarith
    have h2k_real : (2 : ℝ) * k ≤ size := by
      exact_mod_cast h2k
    have h_div_le : (k : ℝ) / ((size : ℝ) - k) ≤ 1 := by
      rw [div_le_one hsk_pos]
      nlinarith
    have h_div_nonneg : 0 ≤ (k : ℝ) / ((size : ℝ) - k) := by positivity
    nlinarith
  have h_chain :=
    RandomSystems.CR18.Counting.chain_product_lower_bound
      (fun k => ((k : ℝ) / ((size : ℝ) - k)) ^ 2)
      h_nonneg h_le_one
  have hNq1 : (size : ℝ) ^ 2 ≤ 3 * (((size : ℝ) - q + 1) ^ 2) := by
    cases q with
    | zero =>
        simp
        nlinarith [show (0 : ℝ) ≤ size by positivity]
    | succ m =>
        have hfive : 5 * m ≤ 2 * size :=
          RandomSystems.CR18.Counting.five_mul_le_two_of_cube (size := size) (k := m) h_cube
        have hgap : (size : ℝ) ^ 2 ≤ 3 * ((size : ℝ) - m) ^ 2 :=
          RandomSystems.CR18.Counting.gap_sq_bound_of_five_mul (size := size) (k := m) hfive
        have hs : ((size : ℝ) - Nat.succ m + 1) = (size : ℝ) - m := by
          have hm : ((Nat.succ m : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
          rw [hm]
          ring
        rw [hs]
        exact hgap
  have hterm :
      ∀ k ∈ Finset.range q,
        ((k : ℝ) / ((size : ℝ) - k)) ^ 2 ≤ (3 : ℝ) * (k : ℝ) ^ 2 / (size : ℝ) ^ 2 := by
    intro k hk
    have hk_lt : k < q := Finset.mem_range.mp hk
    have hkq_real : (k : ℝ) + 1 ≤ q := by
      exact_mod_cast Nat.succ_le_of_lt hk_lt
    have hq_real : (q : ℝ) ≤ size := by
      exact_mod_cast hq_le
    have hk_den_real : ((size : ℝ) - q + 1) ≤ (size : ℝ) - k := by
      nlinarith
    have hgap_pos : (0 : ℝ) < (size : ℝ) - q + 1 := by
      nlinarith
    have hk_size : k < size := lt_of_lt_of_le hk_lt hq_le
    have hk_real : (k : ℝ) < size := by
      exact_mod_cast hk_size
    have hsk_pos : (0 : ℝ) < (size : ℝ) - k := by
      linarith
    have hgap_nonneg : 0 ≤ (size : ℝ) - q + 1 := by linarith
    have hsk_nonneg : 0 ≤ (size : ℝ) - k := by linarith
    have h_sq : (((size : ℝ) - q + 1) ^ 2) ≤ ((size : ℝ) - k) ^ 2 := by
      exact (sq_le_sq₀ hgap_nonneg hsk_nonneg).2 hk_den_real
    have hgap_sq_pos : (0 : ℝ) < (((size : ℝ) - q + 1) ^ 2) := by
      nlinarith
    have h_inv_sq : (1 : ℝ) / (((size : ℝ) - k) ^ 2) ≤ 1 / (((size : ℝ) - q + 1) ^ 2) := by
      exact one_div_le_one_div_of_le hgap_sq_pos h_sq
    have hsize_sq_pos : (0 : ℝ) < (size : ℝ) ^ 2 := by
      have hsize_pos_real : (0 : ℝ) < size := by
        exact_mod_cast h_pos
      nlinarith
    have h_bound : 1 / (((size : ℝ) - q + 1) ^ 2) ≤ 3 / (size : ℝ) ^ 2 := by
      have h_div : (size : ℝ) ^ 2 / (((size : ℝ) - q + 1) ^ 2) ≤ 3 := by
        rw [div_le_iff₀ hgap_sq_pos]
        nlinarith [hNq1]
      rw [le_div_iff₀ hsize_sq_pos]
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h_div
    have h_inv : (1 : ℝ) / (((size : ℝ) - k) ^ 2) ≤ 3 / (size : ℝ) ^ 2 := le_trans h_inv_sq h_bound
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) ^ 2 := by positivity
    have h_eq :
        ((k : ℝ) / ((size : ℝ) - k)) ^ 2
          = (k : ℝ) ^ 2 * ((1 : ℝ) / (((size : ℝ) - k) ^ 2)) := by
      have hsk_ne : (size : ℝ) - k ≠ 0 := by linarith
      field_simp [hsk_ne]
    rw [h_eq]
    have hmul := mul_le_mul_of_nonneg_left h_inv hk_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have h_sum_bound :
      ∑ k ∈ Finset.range q, ((k : ℝ) / ((size : ℝ) - k)) ^ 2 ≤ (q : ℝ) ^ 3 / (size : ℝ) ^ 2 := by
    have hscaled :
        (3 * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2) * (1 / (size : ℝ) ^ 2)
          ≤ (q : ℝ) ^ 3 * (1 / (size : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (RandomSystems.CR18.Counting.three_sum_sq_le_cube q) (by positivity)
    calc
      ∑ k ∈ Finset.range q, ((k : ℝ) / ((size : ℝ) - k)) ^ 2
          ≤ ∑ k ∈ Finset.range q, (3 : ℝ) * (k : ℝ) ^ 2 / (size : ℝ) ^ 2 := by
              exact Finset.sum_le_sum hterm
      _ = (3 / (size : ℝ) ^ 2) * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k hk
            ring
      _ = (3 * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2) * (1 / (size : ℝ) ^ 2) := by
            ring
      _ ≤ (q : ℝ) ^ 3 * (1 / (size : ℝ) ^ 2) := hscaled
      _ = (q : ℝ) ^ 3 / (size : ℝ) ^ 2 := by
            simp [div_eq_mul_inv]
  have h_prod :
      (1 : ℝ) - (q : ℝ) ^ 3 / (size : ℝ) ^ 2 ≤
        ∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2) := by
    linarith [h_chain, h_sum_bound]
  have h_ident :
      (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : ℝ)
        / ((size.factorial : ℝ) ^ 2)
      = (1 / (size : ℝ) ^ q) * ∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2) := by
    have h_fact :
        (((size - q).factorial : ℝ) * ∏ k ∈ Finset.range q, ((size : ℝ) - k))
          = (size.factorial : ℝ) := by
      have h_nat : (size - q).factorial * ∏ k ∈ Finset.range q, (size - k) = size.factorial := by
        rw [← Nat.descFactorial_eq_prod_range, Nat.factorial_mul_descFactorial hq_le]
      norm_num [Finset.prod_range_natCast_sub] at h_nat ⊢
      exact_mod_cast h_nat
    have h_prod_pos : (0 : ℝ) < ((size - q).factorial : ℝ) := by positivity
    calc
      (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : ℝ)
          / ((size.factorial : ℝ) ^ 2)
        = ((((size - q).factorial : ℝ) ^ 2) * ∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ))
            / ((size.factorial : ℝ) ^ 2) := by
              norm_num [Nat.cast_mul, Nat.cast_pow]
      _ = ((((size - q).factorial : ℝ) ^ 2) * ∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ))
            / ((((size - q).factorial : ℝ) * ∏ k ∈ Finset.range q, ((size : ℝ) - k)) ^ 2) := by
              rw [h_fact]
      _ = (∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ)) / (∏ k ∈ Finset.range q, ((size : ℝ) - k)) ^ 2 := by
            field_simp [h_prod_pos.ne']
      _ = (∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ))
            / (∏ k ∈ Finset.range q, (((size : ℝ) - k) ^ 2)) := by
            rw [← Finset.prod_pow]
      _ = ∏ k ∈ Finset.range q, (((size - 2 * k : ℕ) : ℝ) / (((size : ℝ) - k) ^ 2)) := by
            rw [← Finset.prod_div_distrib]
      _ = ∏ k ∈ Finset.range q, ((1 / (size : ℝ)) * (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2)) := by
            refine Finset.prod_congr rfl ?_
            intro k hk
            have hk_lt : k < q := Finset.mem_range.mp hk
            have hk_le_pred : k ≤ q - 1 := Nat.le_pred_of_lt hk_lt
            have h2k : 2 * k ≤ size := le_trans (Nat.mul_le_mul_left _ hk_le_pred) hstep
            have hk_size : k < size := lt_of_lt_of_le hk_lt hq_le
            have hsize_pos_nat : 0 < size := lt_of_le_of_lt (Nat.zero_le _) hk_size
            have hsize_ne : (size : ℝ) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt hsize_pos_nat)
            have hk_real : (k : ℝ) < size := by
              exact_mod_cast hk_size
            have hsk_ne : (size : ℝ) - k ≠ 0 := by
              linarith
            rw [Nat.cast_sub h2k]
            field_simp [hsize_ne, hsk_ne]
            norm_num
            ring
      _ = (∏ k ∈ Finset.range q, (1 / (size : ℝ))) *
            ∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2) := by
            rw [Finset.prod_mul_distrib]
      _ = (1 / (size : ℝ) ^ q) * ∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2) := by
            simp [Finset.prod_const]
  have h_real :
      (1 - (q : ℝ) ^ 3 / (size : ℝ) ^ 2) * (1 / (size : ℝ) ^ q) ≤
        (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : ℝ)
          / ((size.factorial : ℝ) ^ 2) := by
    calc
      (1 - (q : ℝ) ^ 3 / (size : ℝ) ^ 2) * (1 / (size : ℝ) ^ q)
          ≤ (∏ k ∈ Finset.range q, (1 - ((k : ℝ) / ((size : ℝ) - k)) ^ 2)) * (1 / (size : ℝ) ^ q) := by
              have hNq_nonneg : 0 ≤ (1 / (size : ℝ) ^ q) := by positivity
              gcongr
      _ = (((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : ℝ)
            / ((size.factorial : ℝ) ^ 2) := by
            rw [h_ident, mul_comm]
  have h_frac_le_one : (q : NNReal) ^ 3 / ((size : NNReal) ^ 2) ≤ 1 := by
    rw [div_le_one₀ (by positivity : (0 : NNReal) < (size : NNReal) ^ 2)]
    exact_mod_cast h_cube
  have h_prod_eq :
      ∏ k ∈ Finset.range q, (((size : NNReal) - 2 * k : NNReal) : ℝ)
        = ∏ k ∈ Finset.range q, ((size - 2 * k : ℕ) : ℝ) := by
    refine Finset.prod_congr rfl ?_
    intro k hk
    have hk_lt : k < q := Finset.mem_range.mp hk
    have hk_le_pred : k ≤ q - 1 := Nat.le_pred_of_lt hk_lt
    have h2k : 2 * k ≤ size := le_trans (Nat.mul_le_mul_left _ hk_le_pred) hstep
    have h2k_nn : (2 * k : NNReal) ≤ size := by
      exact_mod_cast h2k
    rw [NNReal.coe_sub h2k_nn]
    norm_num [Nat.cast_sub h2k]
  have h_goal_real :
      (((1 - (q : NNReal) ^ 3 / ((size : NNReal)) ^ 2) * (1 / (size : NNReal) ^ q) : NNReal) : ℝ)
        ≤ (((((((size - q).factorial) ^ 2 * ∏ k ∈ Finset.range q, (size - 2 * k)) : ℕ) : NNReal)
          / ((size.factorial : NNReal) ^ 2) : NNReal) : ℝ) := by
    simpa [NNReal.coe_mul, NNReal.coe_sub h_frac_le_one, NNReal.coe_div, NNReal.coe_pow,
      Nat.cast_mul, Nat.cast_pow, h_prod_eq] using h_real
  exact_mod_cast h_goal_real

end Counting
end HTechnique
end RandomSystems
