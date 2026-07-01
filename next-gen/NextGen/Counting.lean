/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Tactic

/-!
# Shared finite-counting lemmas

This module contains application-independent counting facts used by the CR18
switching proof and by the migrated H-technique/SoP proof.
-/

namespace RandomSystems
namespace CR18
namespace Counting

/-! ## Product and birthday arithmetic -/

/-- Weierstrass product inequality: `prod_i (1 - a_i) >= 1 - sum_i a_i`
when all `a_i in [0, 1]`. -/
theorem prod_one_sub_ge_one_sub_sum {n : ℕ} (a : Fin n → ℝ)
    (h_nonneg : ∀ i, 0 ≤ a i) (h_le_one : ∀ i, a i ≤ 1) :
    ∏ i, (1 - a i) ≥ 1 - ∑ i, a i := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    set b := fun i : Fin m => a (Fin.castSucc i)
    have h_ih := ih b (fun i => h_nonneg _) (fun i => h_le_one _)
    have h_sum_nonneg : 0 ≤ ∑ i : Fin m, b i :=
      Finset.sum_nonneg (fun i _ => h_nonneg _)
    nlinarith [h_nonneg (Fin.last m), h_le_one (Fin.last m),
               mul_nonneg h_sum_nonneg (h_nonneg (Fin.last m))]

/-- If `0 <= f(k) <= 1` for all `k < q`, then
`prod_{k<q} (1 - f(k)) >= 1 - sum_{k<q} f(k)`. -/
theorem chain_product_lower_bound {q : ℕ} (f : ℕ → ℝ)
    (h_nonneg : ∀ k < q, 0 ≤ f k) (h_le_one : ∀ k < q, f k ≤ 1) :
    ∏ k ∈ Finset.range q, (1 - f k) ≥ 1 - ∑ k ∈ Finset.range q, f k := by
  rw [← Fin.prod_univ_eq_prod_range, ← Fin.sum_univ_eq_sum_range]
  exact prod_one_sub_ge_one_sub_sum _
    (fun i => h_nonneg i.val i.isLt)
    (fun i => h_le_one i.val i.isLt)

/-- Closed form for `(0 + ... + (q-1)) / N`. -/
lemma sum_div_range (N q : ℕ) (h_N_pos : (0 : ℝ) < N) :
    ∑ k ∈ Finset.range q, ((k : ℝ) / N) = (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
  induction q with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; field_simp; ring

/-- Falling factorial lower bound:
`(N)_q >= N^q * (1 - q(q-1)/(2N))`. -/
theorem falling_factorial_lower_bound {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    (∏ k ∈ Finset.range q, ((N : ℝ) - k)) ≥
      (N : ℝ) ^ q * (1 - (q : ℝ) * ((q : ℝ) - 1) / (2 * N)) := by
  have h_N_pos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  have h_factor : ∏ k ∈ Finset.range q, ((N : ℝ) - k) =
      (N : ℝ) ^ q * ∏ k ∈ Finset.range q, (1 - (k : ℝ) / N) := by
    conv_lhs =>
      arg 2
      ext k
      rw [show (N : ℝ) - (k : ℝ) = (N : ℝ) * (1 - (k : ℝ) / N) from by
        field_simp]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [h_factor]
  have h_chain := chain_product_lower_bound (fun k => (k : ℝ) / N)
    (fun k _ => div_nonneg (Nat.cast_nonneg k) (le_of_lt h_N_pos))
    (fun k hk => by
      rw [div_le_one h_N_pos]
      exact_mod_cast (Nat.lt_of_lt_of_le hk h_le).le)
  rw [sum_div_range N q h_N_pos] at h_chain
  exact mul_le_mul_of_nonneg_left (GE.ge.le h_chain) (pow_nonneg (le_of_lt h_N_pos) q)

/-- Birthday bound: `1 - (N)_q / N^q <= q(q-1)/(2N)`. -/
theorem birthday_bound {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N) :
    1 - (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q ≤
      (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
  have h_N_pos : (0 : ℝ) < N := Nat.cast_pos.mpr h_pos
  have h_Nq_pos : (0 : ℝ) < (N : ℝ) ^ q := pow_pos h_N_pos q
  have h_ffact := falling_factorial_lower_bound h_le h_pos
  have h_div : (∏ k ∈ Finset.range q, ((N : ℝ) - k)) / (N : ℝ) ^ q ≥
      1 - (q : ℝ) * ((q : ℝ) - 1) / (2 * N) := by
    rw [ge_iff_le, le_div_iff₀ h_Nq_pos]
    linarith
  linarith

/-! ## Switching-ratio arithmetic -/

/-- **UPSTREAM-CANDIDATE.** The ideal/real mass ratio as a falling factorial:
`(N-q)!/N! = (N)_q⁻¹`, stated in `NNReal` for PRP/PRF switching proofs. -/
theorem factorial_ratio_eq_descFactorial_inv {N q : ℕ} (h_le : q ≤ N) :
    ((N - q).factorial : NNReal) / (N.factorial : NNReal)
      = ((N.descFactorial q : NNReal))⁻¹ := by
  have hN : (N.factorial : NNReal)
      = ((N - q).factorial : NNReal) * (N.descFactorial q : NNReal) := by
    rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial h_le]
  rw [hN, div_mul_eq_div_div, div_self (by exact_mod_cast (N - q).factorial_pos.ne'), one_div]

/-- **UPSTREAM-CANDIDATE.** The generic PRP/PRF switching numeric ratio:
`(1-ε)·((N-q)!/N!) ≤ 1/N^q` with birthday slack
`ε = q(q-1)/(2N)`.  This is the lightweight arithmetic core used by both the
CR18 switching lemma and HCTR2's concrete switching step. -/
theorem switching_ratio_le {N q : ℕ} (h_le : q ≤ N) (h_pos : 0 < N)
    (h_eps : (((q * (q - 1) : ℕ) : NNReal)) / (((2 * N : ℕ)) : NNReal) ≤ 1) :
    (1 - (((q * (q - 1) : ℕ) : NNReal)) / (((2 * N : ℕ)) : NNReal))
        * (((N - q).factorial : NNReal) / (N.factorial : NNReal))
      ≤ 1 / (N : NNReal) ^ q := by
  rw [factorial_ratio_eq_descFactorial_inv h_le, ← one_div, mul_one_div,
    div_le_div_iff₀ (by exact_mod_cast Nat.descFactorial_pos.mpr h_le)
      (pow_pos (by exact_mod_cast h_pos) q), one_mul, ← NNReal.coe_le_coe]
  have hdesc : ((N.descFactorial q : NNReal) : ℝ) = ∏ k ∈ Finset.range q, ((N : ℝ) - k) := by
    rw [NNReal.coe_natCast, Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun k hk => ?_)
    rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hk) h_le))]
  have heps : ((q * (q - 1) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ)
      = (q : ℝ) * ((q : ℝ) - 1) / (2 * (N : ℝ)) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; norm_num
    · rw [Nat.cast_mul, Nat.cast_sub hq, Nat.cast_mul]
      push_cast
      ring
  rw [hdesc, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_sub h_eps,
    NNReal.coe_one, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast, heps]
  have hfall := falling_factorial_lower_bound h_le h_pos
  nlinarith [hfall]

/-! ## Cubic query-bound arithmetic -/

/-- `3 * sum_{k=0}^{q-1} k^2 <= q^3`.  This is the coarse cubic estimate used
by ratio-counting proofs. -/
lemma three_sum_sq_le_cube (q : ℕ) :
    3 * ∑ k ∈ Finset.range q, (k : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
  induction q with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add]
      have h_cube_expand :
          ((m : ℝ) + 1) ^ 3 = (m : ℝ) ^ 3 + 3 * (m : ℝ) ^ 2 + 3 * (m : ℝ) + 1 := by
        ring
      push_cast at h_cube_expand ⊢
      nlinarith [sq_nonneg (m : ℝ)]

/-- The cubic paper-side condition `q^3 <= size^2` implies `q <= size`. -/
lemma q_le_of_cube_le_sq {size q : ℕ} (h_cube : q ^ 3 ≤ size ^ 2) :
    q ≤ size := by
  by_cases hq0 : q = 0
  · omega
  · have hq_one : 1 ≤ q := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hq0)
    have hq2_real : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
      have hq_real : (1 : ℝ) ≤ q := by
        exact_mod_cast hq_one
      nlinarith
    have h_cube_real : (q : ℝ) ^ 3 ≤ (size : ℝ) ^ 2 := by
      exact_mod_cast h_cube
    have hq2_le : (q : ℝ) ^ 2 ≤ (size : ℝ) ^ 2 := le_trans hq2_real h_cube_real
    have hq_nonneg : (0 : ℝ) ≤ q := by positivity
    have hsize_nonneg : (0 : ℝ) ≤ size := by positivity
    exact_mod_cast (sq_le_sq₀ hq_nonneg hsize_nonneg).mp hq2_le

/-- Under the cubic paper-side condition, the largest queried index is small
enough for denominator estimates in ratio-counting proofs. -/
lemma two_mul_pred_le_of_cube_sq {size q : ℕ}
    (h_pos : 0 < size) (h_cube : q ^ 3 ≤ size ^ 2) :
    2 * (q - 1) ≤ size := by
  by_contra hbad
  have hbad_nat : size + 2 < 2 * q := by
    omega
  have hbad_real : (size : ℝ) + 2 < 2 * q := by
    exact_mod_cast hbad_nat
  have h_cube_lt : ((size : ℝ) + 2) ^ 3 < (2 * q) ^ 3 := by
    exact pow_lt_pow_left₀ hbad_real (by positivity) (by decide : (3 : ℕ) ≠ 0)
  have h_cube_gt : (((size : ℝ) + 2) ^ 3) / 8 < (q : ℝ) ^ 3 := by
    nlinarith [h_cube_lt]
  have h_poly : (size : ℝ) ^ 2 < (((size : ℝ) + 2) ^ 3) / 8 := by
    nlinarith [show (0 : ℝ) < size by exact_mod_cast h_pos]
  have h_cube_real : (q : ℝ) ^ 3 ≤ (size : ℝ) ^ 2 := by
    exact_mod_cast h_cube
  linarith

lemma twentyfive_sq_lt_four_cube (k : ℕ) :
    (25 : ℝ) * k ^ 2 < 4 * ((k + 1 : ℕ) : ℝ) ^ 3 := by
  by_cases hk : k < 4
  · interval_cases k <;> norm_num
  · have hk4 : (4 : ℝ) ≤ k := by
      exact_mod_cast Nat.le_of_not_lt hk
    have h_cast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
      exact_mod_cast (show (k + 1 : ℕ) = k + 1 by rfl)
    rw [h_cast]
    nlinarith [hk4]

lemma five_mul_le_two_of_cube {size k : ℕ} (h : (k + 1) ^ 3 ≤ size ^ 2) :
    5 * k ≤ 2 * size := by
  by_contra hbad
  have hbad_nat : 2 * size + 1 ≤ 5 * k := Nat.succ_le_of_lt (lt_of_not_ge hbad)
  have hbad_real : (2 : ℝ) * size + 1 ≤ 5 * k := by
    exact_mod_cast hbad_nat
  have h1 : (4 : ℝ) * size ^ 2 < (25 : ℝ) * k ^ 2 := by
    nlinarith
  have h2 : (25 : ℝ) * k ^ 2 < 4 * ((k + 1 : ℕ) : ℝ) ^ 3 :=
    twentyfive_sq_lt_four_cube k
  have h3 : (4 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 3 ≤ (4 : ℝ) * size ^ 2 := by
    gcongr
    exact_mod_cast h
  linarith

lemma gap_sq_bound_of_five_mul {size k : ℕ} (h : 5 * k ≤ 2 * size) :
    (size : ℝ) ^ 2 ≤ 3 * ((size : ℝ) - k) ^ 2 := by
  have h_real : (5 : ℝ) * k ≤ 2 * size := by
    exact_mod_cast h
  nlinarith [h_real, show (0 : ℝ) ≤ k by positivity, show (0 : ℝ) ≤ size by positivity]

/-! ## Function fibers -/

/-- The number of functions agreeing with a prescribed map on a finite input
subset.

This is the shared finite-set function-fiber count used by transcript
normalization arguments. -/
theorem card_function_fiber_finset {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (S : Finset X) (g : S → Y) :
    (Finset.univ.filter (fun f : X → Y => ∀ x : S, f x.1 = g x)).card =
      Fintype.card Y ^ (Fintype.card X - S.card) := by
  classical
  rw [show Fintype.card Y ^ (Fintype.card X - S.card) = Fintype.card (↥Sᶜ → Y) from by
    rw [Fintype.card_fun, Fintype.card_coe, Finset.card_compl]]
  refine Finset.card_bij (fun f _ => fun ⟨x, hx⟩ => f x) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
    ext x
    by_cases hx : x ∈ S
    · rw [hf₁ ⟨x, hx⟩, hf₂ ⟨x, hx⟩]
    · exact congr_fun h ⟨x, Finset.mem_compl.mpr hx⟩
  · intro h _
    refine Exists.intro
      (fun x => if hx : x ∈ S then g ⟨x, hx⟩ else h ⟨x, Finset.mem_compl.mpr hx⟩) ?_
    refine Exists.intro ?_ ?_
    · rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ _
      · intro x
        simp [x.2]
    · ext x
      simp [Finset.mem_compl.mp x.2]

/-- The number of functions matching a prescribed output tuple on an injective
input tuple is `|Y|^(|X|-q)`. -/
theorem card_function_fiber_multipoint {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    {q : ℕ} (xs : Fin q → X) (ys : Fin q → Y)
    (hxs : Function.Injective xs) :
    ((Finset.univ : Finset (X → Y)).filter
        (fun f : X → Y => (fun i : Fin q => f (xs i)) = ys)).card =
      Fintype.card Y ^ (Fintype.card X - q) := by
  classical
  set S : Finset X := Finset.univ.image xs
  have hS_card : S.card = q := by
    rw [Finset.card_image_of_injective _ hxs, Finset.card_fin]
  let C : Finset X := Finset.univ \ S
  rw [show Fintype.card Y ^ (Fintype.card X - q) = Fintype.card (C → Y) from by
    have hC_card : C.card = Fintype.card X - S.card := by
      exact Finset.card_sdiff_of_subset (by intro x _; exact Finset.mem_univ x)
    rw [Fintype.card_fun, Fintype.card_coe, hC_card, hS_card]]
  refine Finset.card_bij (fun f _ => fun ⟨x, hx⟩ => f x)
    (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
    ext x
    by_cases hx : x ∈ S
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [congr_fun hf₁ i, congr_fun hf₂ i]
    · exact congr_fun h ⟨x, by simp [C, hx]⟩
  · intro g _
    have h_ext : ∀ x ∈ S, ∃! i : Fin q, xs i = x := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl, fun j hj => hxs hj⟩
    refine ⟨fun x =>
        if hx : x ∈ S then ys ((h_ext x hx).choose)
        else g ⟨x, by simp [C, hx]⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext i
      have h_mem : xs i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      show dite (xs i ∈ S) _ _ = ys i
      rw [dif_pos h_mem]
      have hcs := (h_ext (xs i) h_mem).choose_spec
      congr 1
      exact hxs hcs.1
    · ext ⟨x, hx⟩
      show dite (x ∈ S) _ _ = g ⟨x, hx⟩
      rw [dif_neg ((Finset.mem_sdiff.mp hx).2)]

/-- The number of functions that are injective on a finite set of inputs.

A function injective on `S` is equivalently an embedding `S ↪ Y` plus arbitrary
values on `Sᶜ`. -/
theorem card_function_injOn_finset {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (S : Finset X)
    [DecidablePred (fun f : X → Y => Set.InjOn f (fun x => x ∈ S))] :
    ((Finset.univ : Finset (X → Y)).filter (fun f => Set.InjOn f (fun x => x ∈ S))).card =
      (Fintype.card Y).descFactorial S.card * Fintype.card Y ^ (Fintype.card X - S.card) := by
  classical
  have e : {f : X → Y // Set.InjOn f (fun x => x ∈ S)} ≃ (S ↪ Y) × (↥Sᶜ → Y) :=
    { toFun := fun f =>
        (⟨fun x : S => f.1 x.1, by
          intro x y hxy
          exact Subtype.ext (f.2 x.2 y.2 hxy)⟩,
         fun x : ↥Sᶜ => f.1 x.1)
      invFun := fun p =>
        ⟨fun x => if hx : x ∈ S then p.1 ⟨x, hx⟩ else p.2 ⟨x, Finset.mem_compl.mpr hx⟩, by
          intro x hx y hy hxy
          change x ∈ S at hx
          change y ∈ S at hy
          dsimp at hxy
          rw [dif_pos hx, dif_pos hy] at hxy
          exact congr_arg Subtype.val (p.1.injective hxy)⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext x
        by_cases hx : x ∈ S <;> simp [hx]
      right_inv := by
        intro p
        rcases p with ⟨emb, comp⟩
        ext x
        · simp
        · simp [Finset.mem_compl.mp x.2] }
  rw [← Fintype.card_subtype (p := fun f : X → Y => Set.InjOn f (fun x => x ∈ S))]
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_coe]
  rw [Fintype.card_fun, Fintype.card_coe, Finset.card_compl]

/-! ## Permutation fibers -/

/-- The number of permutations extending a prescribed injective finite
assignment is `(|X|-q)!`.

This is the shared permutation-fiber count used by PRP/URP transcript arguments
and by the H-technique SoP system law. -/
theorem card_perm_fiber {X : Type*} [Fintype X] [DecidableEq X] {q : ℕ}
    (inputs : Fin q → X) (h_inj : Function.Injective inputs)
    (ys : Fin q → X) (h_ys_inj : Function.Injective ys)
    (h_q_le : q ≤ Fintype.card X) :
    ((Finset.univ : Finset (Equiv.Perm X)).filter
      (fun π => ∀ i, π (inputs i) = ys i)).card =
    (Fintype.card X - q).factorial := by
  classical
  set S := Finset.univ.image inputs with hS_def
  have hS_card : S.card = q := by
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_fin]
  have h_desc_pos : 0 < (Fintype.card X).descFactorial q :=
    Nat.descFactorial_pos.mpr h_q_le
  suffices h_prod : ((Finset.univ : Finset (Equiv.Perm X)).filter
      (fun π => ∀ i, π (inputs i) = ys i)).card *
      (Fintype.card X).descFactorial q = (Fintype.card X).factorial by
    have h_eq := Nat.factorial_mul_descFactorial h_q_le
    exact Nat.eq_of_mul_eq_mul_right h_desc_pos (h_prod.trans h_eq.symm)
  set Φ : Equiv.Perm X → (Fin q ↪ X) :=
    fun π => ⟨fun i => π (inputs i), (π.injective.comp h_inj)⟩
  set injTuples := (Finset.univ : Finset (Fin q ↪ X))
  have h_partition : (Finset.univ : Finset (Equiv.Perm X)).card =
      ∑ z ∈ injTuples, (Finset.univ.filter (fun π => Φ π = z)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  set ys_emb : Fin q ↪ X := ⟨ys, h_ys_inj⟩
  have h_fiber_eq : ∀ z ∈ injTuples,
      (Finset.univ.filter (fun π => Φ π = z)).card =
      (Finset.univ.filter (fun π => Φ π = ys_emb)).card := by
    intro z _
    have h_pt : MulAction.IsPretransitive (Equiv.Perm X) (Fin q ↪ X) :=
      Equiv.Perm.isMultiplyPretransitive X q
    obtain ⟨τ, hτ⟩ := h_pt.exists_smul_eq ys_emb z
    have hτ_app : ∀ i, τ (ys i) = z i := fun i => congr_fun (congr_arg (↑·) hτ) i
    apply Finset.card_bij'
      (fun π _ => τ⁻¹ * π)
      (fun σ _ => τ * σ)
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      ext i
      show τ⁻¹ (π (inputs i)) = ys i
      have : π (inputs i) = z i := congr_fun (congr_arg (↑·) hπ) i
      rw [this, ← hτ_app i]
      simp
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      ext i
      show τ (σ (inputs i)) = z i
      have : σ (inputs i) = ys i := congr_fun (congr_arg (↑·) hσ) i
      rw [this, hτ_app i]
    · intro π _
      simp
    · intro σ _
      simp
  have h_fiber_match : (Finset.univ.filter (fun π : Equiv.Perm X =>
        ∀ i, π (inputs i) = ys i)) =
      (Finset.univ.filter (fun π => Φ π = ys_emb)) := by
    ext π
    simp [Finset.mem_filter, Φ, ys_emb, Function.Embedding.ext_iff]
  have h_inj_card : injTuples.card = (Fintype.card X).descFactorial q := by
    simp only [injTuples, Finset.card_univ]
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
  rw [h_fiber_match]
  have h_sum_eq : ∑ z ∈ injTuples,
      (Finset.univ.filter (fun π => Φ π = z)).card =
      (Finset.univ.filter (fun π => Φ π = ys_emb)).card * injTuples.card := by
    rw [Finset.sum_const_nat (fun z hz => h_fiber_eq z hz), mul_comm]
  have h_card_perm : (Finset.univ : Finset (Equiv.Perm X)).card =
      Fintype.card (Equiv.Perm X) :=
    Finset.card_univ
  rw [mul_comm]
  calc (Fintype.card X).descFactorial q *
        (Finset.univ.filter (fun π => Φ π = ys_emb)).card
      = injTuples.card * (Finset.univ.filter (fun π => Φ π = ys_emb)).card := by
          rw [h_inj_card]
    _ = (Finset.univ.filter (fun π => Φ π = ys_emb)).card * injTuples.card := by
          rw [mul_comm]
    _ = ∑ z ∈ injTuples, (Finset.univ.filter (fun π => Φ π = z)).card := h_sum_eq.symm
    _ = (Finset.univ : Finset (Equiv.Perm X)).card := h_partition.symm
    _ = Fintype.card (Equiv.Perm X) := h_card_perm
    _ = (Fintype.card X).factorial := Fintype.card_perm

/-- The permutation fiber count over an actual finite input set, rather than an
injective tuple. The queried set is `S`; the prescribed outputs are an embedding
`S ↪ X`. -/
theorem card_perm_fiber_finset {X : Type*} [Fintype X] [DecidableEq X]
    (S : Finset X) (g : S ↪ X) :
    ((Finset.univ : Finset (Equiv.Perm X)).filter (fun π => ∀ x : S, π x.1 = g x)).card =
      (Fintype.card X - S.card).factorial := by
  classical
  let eS := (Fintype.equivFin S).symm
  let inputs : Fin (Fintype.card S) → X := fun i => (eS i).1
  let ys : Fin (Fintype.card S) → X := fun i => g (eS i)
  have hinputs : Function.Injective inputs := by
    intro i j hij
    have hsub : eS i = eS j := Subtype.ext hij
    exact eS.injective hsub
  have hys : Function.Injective ys := by
    intro i j hij
    exact eS.injective (g.injective hij)
  have hle : Fintype.card S ≤ Fintype.card X :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hbase := card_perm_fiber inputs hinputs ys hys hle
  have hfilter : ((Finset.univ : Finset (Equiv.Perm X)).filter
        (fun π => ∀ i, π (inputs i) = ys i)) =
      ((Finset.univ : Finset (Equiv.Perm X)).filter (fun π => ∀ x : S, π x.1 = g x)) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h x
      let i := Fintype.equivFin S x
      have hi : eS i = x := by
        dsimp [eS, i]
        simp
      simpa [inputs, ys, hi] using h i
    · intro h i
      exact h (eS i)
  rw [← hfilter]
  simpa [Fintype.card_coe] using hbase

end Counting
end CR18
end RandomSystems
