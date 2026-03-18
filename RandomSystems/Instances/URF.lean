/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.PDS

/-!
# Uniform Random Function (URF) / Uniform Random DDS

Paper Example 5 / Definition 15 (Maurer02 / Lanzenberger-Maurer20):
the *uniform random function* is uniform over all functions `X → Y`.

This file contains two related objects:

* `URF` — uniform over **all** `(X,Y)`-DDS of query bound `q`. For `q = 1`,
  this coincides with the uniform random function (`DDS X Y 1 ≃ (X → Y)`), but
  for `q > 1` it is *strictly more general* because a DDS may depend on the full
  query prefix (i.e., can be history-dependent / stateful).
* `URFfun` — uniform over functions `X → Y`, embedded as a stateless DDS via
  `DDS.ofFunq`. This matches the “random function / random oracle” notion used
  in the CBC-MAC papers.

## Main Definitions

* `URF` — uniform over all DDS (a “uniform random DDS”)
* `URFfun` — uniform over all functions `X → Y` (a consistent function oracle)
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Instances

variable {X Y : Type*} {q : ℕ} [Fintype X] [DecidableEq X] [Fintype Y]
variable [Fintype (DDS X Y q)]

/-- The Uniform Random Function: uniform distribution over all DDS.

This assigns mass `1 / |DDS X Y q|` to every deterministic system. -/
def URF [Nonempty (DDS X Y q)] : PDS X Y q where
  dist := Dist.uniform (DDS X Y q)

/-! ### Uniform random function (consistent oracle) as a PDS -/

/-- A random function oracle drawn from an arbitrary distribution on functions.

This samples `f : X → Y` according to `Df` and answers each query with `f x`
(consistently across repeated inputs). -/
def URFfunOf [DecidableEq Y] (Df : Dist (X → Y)) : PDS X Y q where
  dist := Dist.fTransform (fun f : X → Y => DDS.ofFunq (q := q) f) Df

/-- Uniform random function (URF): pick `f : X → Y` uniformly and answer each
query with `f` applied to the current input (consistently across repeated
queries). Formally this is the pushforward of `uniform (X → Y)` along
`DDS.ofFunq`. -/
def URFfun [DecidableEq Y] [Nonempty Y] : PDS X Y q where
  dist := (URFfunOf (X := X) (Y := Y) (q := q) (Dist.uniform (X → Y))).dist

omit [Fintype X] [DecidableEq X] [Fintype Y] in
/-- URF is a probability PDS (weight = 1) when the DDS type is nonempty. -/
theorem URF_isProbPDS [Nonempty (DDS X Y q)] :
    (URF (X := X) (Y := Y) (q := q)).isProbPDS := by
  unfold PDS.isProbPDS Dist.isProbDist URF Dist.weight
  simp [Dist.uniform]

/-- Evaluating a single-query URF at any input produces the uniform
distribution on outputs.

`fTransform (firstQuery · x₀) (uniform DDS) = uniform Y`

Proof: fiber counting shows `|{s | firstQuery s x₀ = y}| = |Y|^(|X|-1)`,
and `|DDS X Y 1| = |Y|^|X|`, giving ratio `1/|Y|`. -/
theorem URF_eval_eq_uniform [DecidableEq Y] [Nonempty (DDS X Y 1)] [Nonempty Y] (x₀ : X) :
    Dist.fTransform (fun s : DDS X Y 1 => s.firstQuery Nat.zero_lt_one x₀)
      (Dist.uniform (DDS X Y 1)) = Dist.uniform Y := by
  ext y
  simp only [Dist.fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply, Dist.uniform]
  have h_supp : (Finsupp.equivFunOnFinite.invFun
    (fun _ : DDS X Y 1 => (1 : NNReal) / (Fintype.card (DDS X Y 1) : NNReal))).support
    = Finset.univ := by
    ext s; simp_all [Finsupp.equivFunOnFinite]
  rw [h_supp, ← Finset.sum_filter]
  simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk, Finset.sum_const, nsmul_eq_mul,
    mul_one_div]
  have h_fiber_card : (Finset.univ.filter
      (fun s : DDS X Y 1 => s.firstQuery Nat.zero_lt_one x₀ = y)).card =
      Fintype.card Y ^ (Fintype.card X - 1) := by
    rw [show (Finset.univ.filter
        (fun s : DDS X Y 1 => s.firstQuery Nat.zero_lt_one x₀ = y)).card =
        (Finset.univ.filter (fun f : X → Y => f x₀ = y)).card from by
      apply Finset.card_bij (fun s _ => dds1Equiv X Y s)
      · intro s hs; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢; exact hs
      · intro s₁ _ s₂ _ h; exact (dds1Equiv X Y).injective h
      · intro f hf; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
        refine ⟨(dds1Equiv X Y).symm f, ?_, (dds1Equiv X Y).apply_symm_apply f⟩
        simp only [dds1Equiv]; exact hf]
    have h := Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset Y) x₀
      (Finset.mem_univ y)
    rw [Fintype.piFinset_univ, Finset.card_univ] at h; exact h
  have h_total_card : Fintype.card (DDS X Y 1) = Fintype.card Y ^ Fintype.card X := by
    exact Fintype.card_congr (dds1Equiv X Y) ▸ Fintype.card_fun
  rw [h_fiber_card, h_total_card]
  haveI : Nonempty X := ⟨x₀⟩
  have h_pos : 0 < Fintype.card Y := Fintype.card_pos
  have h_card : Fintype.card Y ^ Fintype.card X =
      Fintype.card Y ^ (Fintype.card X - 1) * Fintype.card Y := by
    rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos]
  rw [h_card, Nat.cast_mul, div_mul_eq_div_div,
    div_self (show (↑(Fintype.card Y ^ (Fintype.card X - 1)) : NNReal) ≠ 0 from by
      exact_mod_cast pow_ne_zero _ h_pos.ne'), one_div]

end RandomSystems.Instances
