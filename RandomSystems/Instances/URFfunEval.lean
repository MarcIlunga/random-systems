import RandomSystems.Dist

/-!
# Multi-point evaluation of a uniform random function

This file provides the basic counting lemma used throughout the repo:
evaluating a uniform random function at `n` distinct points yields a uniform
output vector.

This is a shared, non-private version of the helper lemmas that were previously
duplicated (privately) in `CTRMode.lean` and `CBCMAC.lean`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Instances

/-! ## Fiber cardinality for fixing values at multiple distinct points -/

/-- Multi-point function fixing cardinality: the number of functions `X → Y`
that agree with a target vector `ys` at `n` distinct points is `|Y|^(|X| - n)`. -/
theorem card_fiber_multipoint
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y]
    {n : ℕ} (nonces : Fin n → X) (ys : Fin n → Y) (h_inj : Function.Injective nonces) :
    (Finset.univ.filter (fun f : X → Y => (fun i => f (nonces i)) = ys)).card
      = Fintype.card Y ^ (Fintype.card X - n) := by
  classical
  set S : Finset X := Finset.univ.image nonces
  have hS_card : S.card = n := by
    rw [Finset.card_image_of_injective _ h_inj, Finset.card_fin]
  -- Functions are determined by their values on `S` (fixed by `ys`) and an arbitrary
  -- extension on the complement `Sᶜ`.
  rw [show Fintype.card Y ^ (Fintype.card X - n) = Fintype.card (↥Sᶜ → Y) from by
    rw [Fintype.card_fun, Fintype.card_coe, Finset.card_compl, hS_card]]
  refine Finset.card_bij (fun f _ => fun ⟨x, hx⟩ => f x) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro f₁ hf₁ f₂ hf₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf₁ hf₂
    ext x
    by_cases hx : x ∈ S
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [congr_fun hf₁ i, congr_fun hf₂ i]
    · exact congr_fun h ⟨x, Finset.mem_compl.mpr hx⟩
  · intro g _
    have h_ext : ∀ x ∈ S, ∃! i : Fin n, nonces i = x := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl, fun j hj => h_inj hj⟩
    refine ⟨fun x =>
        if hx : x ∈ S then ys ((h_ext x hx).choose)
        else g ⟨x, Finset.mem_compl.mpr hx⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      ext i
      have h_mem : nonces i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
      show dite (nonces i ∈ S) _ _ = ys i
      rw [dif_pos h_mem]
      have hcs := (h_ext (nonces i) h_mem).choose_spec
      congr 1
      exact h_inj hcs.1
    · ext ⟨x, hx⟩
      show dite (x ∈ S) _ _ = g ⟨x, hx⟩
      rw [dif_neg (Finset.mem_compl.mp hx)]

/-! ## Uniformity of evaluation at distinct points -/

/-- Evaluating a uniform random function at `n` distinct points produces the
uniform distribution on output vectors `Fin n → Y`. -/
theorem eval_nonces_uniform
    {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {n : ℕ} (nonces : Fin n → X) (h_inj : Function.Injective nonces) :
    Dist.fTransform (fun f : X → Y => fun i => f (nonces i))
      (Dist.uniform (X → Y)) = Dist.uniform (Fin n → Y) := by
  classical
  ext ys
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply, Dist.uniform]
  have h_supp : (Finsupp.equivFunOnFinite.invFun
      (fun _ : X → Y => (1 : NNReal) / (Fintype.card (X → Y) : NNReal))).support = Finset.univ := by
    ext s
    simp [Finsupp.equivFunOnFinite]
  rw [h_supp, ← Finset.sum_filter]
  simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  congr 1
  · rw [card_fiber_multipoint (X := X) (Y := Y) nonces ys h_inj, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin]
    simp only [Nat.cast_pow]
    have hY : (Fintype.card Y : NNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := Y)).ne'
    have hn : n ≤ Fintype.card X :=
      Fintype.card_fin n ▸ Fintype.card_le_of_injective nonces h_inj
    rw [show (Fintype.card Y : NNReal) ^ Fintype.card X =
        (Fintype.card Y : NNReal) ^ (Fintype.card X - n) * (Fintype.card Y : NNReal) ^ n from by
      rw [← pow_add, Nat.sub_add_cancel hn]]
    rw [div_mul_eq_div_div, div_self (pow_ne_zero _ hY), one_div]

end RandomSystems.Instances

