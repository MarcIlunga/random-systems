import RandomSystems.Dist
import RandomSystems.Counting

/-!
# Multi-point evaluation of a uniform random function

This file provides the basic counting lemma used throughout the repo:
evaluating a uniform random function at `n` distinct points yields a uniform
output vector.

This is the shared owner of the distribution-level fact.  The pure fiber
count is owned by `RandomSystems.CR18.Counting.card_function_fiber_multipoint`
(Mathlib-only) and re-exposed here under the historical name;
`RandomSystems.CR18.uniformFunction_eval_uniform` in
`RandomSystems.FunctionEvaluator` is an alias of `eval_nonces_uniform`.

Neither lemma needs `[Nonempty X]`: for `n = 0` the output vector space is
already inhabited, and for `n > 0` the tuple `nonces : Fin n → X` supplies an
input.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Instances

/-! ## Fiber cardinality for fixing values at multiple distinct points -/

/-- Multi-point function fixing cardinality: the number of functions `X → Y`
that agree with a target vector `ys` at `n` distinct points is `|Y|^(|X| - n)`.
Alias of the owner `RandomSystems.CR18.Counting.card_function_fiber_multipoint`. -/
theorem card_fiber_multipoint
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    {n : ℕ} (nonces : Fin n → X) (ys : Fin n → Y) (h_inj : Function.Injective nonces) :
    (Finset.univ.filter (fun f : X → Y => (fun i => f (nonces i)) = ys)).card
      = Fintype.card Y ^ (Fintype.card X - n) :=
  RandomSystems.CR18.Counting.card_function_fiber_multipoint nonces ys h_inj

/-! ## Uniformity of evaluation at distinct points -/

/-- Evaluating a uniform random function at `n` distinct points produces the
uniform distribution on output vectors `Fin n → Y`. -/
theorem eval_nonces_uniform
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {n : ℕ} (nonces : Fin n → X) (h_inj : Function.Injective nonces) :
    Dist.fTransform (fun f : X → Y => fun i => f (nonces i))
      (Dist.uniform (X → Y)) = Dist.uniform (Fin n → Y) := by
  classical
  ext ys
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply, Dist.uniform]
  have h_supp : (Finsupp.equivFunOnFinite.invFun
      (fun _ : X → Y => (1 : ℝ) / (Fintype.card (X → Y) : ℝ))).support = Finset.univ := by
    ext s
    simp [Finsupp.equivFunOnFinite]
  rw [h_supp, ← Finset.sum_filter]
  simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [card_fiber_multipoint (X := X) (Y := Y) nonces ys h_inj, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin]
  simp only [Nat.cast_pow]
  have hY : (Fintype.card Y : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Y)).ne'
  have hn : n ≤ Fintype.card X :=
    Fintype.card_fin n ▸ Fintype.card_le_of_injective nonces h_inj
  field_simp
  rw [← pow_add, Nat.sub_add_cancel hn]

end RandomSystems.Instances
