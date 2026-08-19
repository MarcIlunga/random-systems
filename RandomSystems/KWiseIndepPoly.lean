/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DistCond
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# `k`-wise independence from polynomial evaluation (CR18 §6.1.2, p. 124)

Cramer–Renner, *Cryptography — Lecture Notes* (2018), §6.1.2, printed page 124:

> Given `k` uniformly random values in `{0,1}^m` (for some `m`) one can
> construct `2^m` values that appear perfectly random as long as one sees at
> most `k` of them. … Such a construction can be achieved by letting the `k`
> random values be the coefficients `a₀, …, a_{k-1}` of a polynomial
> `a(x) = a_{k-1}x^{k-1} + ⋯ + a₁x + a₀` over `GF(2^m)`, and considering the
> `2^m` values `a(x)` for all `x ∈ GF(2^m)`.  … The proof that this works is
> left as an exercise.

That exercise is `kIndepRV_polyEval` below, in the form the source states it —
a resource construction `U_{km} → [k]·R_{m,m}` — but over an arbitrary finite
field, `GF(2^m)` being the case the notes use.

The mathematical content is one bijection: for `k` **distinct** evaluation
points, the coefficient-to-values map `a ↦ (a(x₁), …, a(x_k))` is a bijection
of `F^k` (`bijective_polyEval`), because a nonzero polynomial of degree `< k`
cannot vanish at `k` distinct points.  Uniform pushes forward to uniform along
a bijection (`Dist.fTransform_bijection_uniform`), which gives the joint law at
`k` points; `Dist.mass_forall_mem_erase_eq_sum` marginalizes it down to every
smaller set of points, which is what turns "uniform at exactly `k` points" into
`k`-wise independence in the sense of `Dist.kIndepRV`.

The bound `k ≤ |F|` is necessary and appears as a hypothesis: with fewer than
`k` points in the field there is no `k`-element set of evaluation points to
extend to.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems

namespace KWise

open Polynomial

/-- Evaluation of the polynomial with coefficient vector `a : Fin k → F` at a
point: `a(x) = ∑_{j<k} aⱼ·xʲ` (CR18 §6.1.2). -/
def polyEval {F : Type*} [Semiring F] {k : ℕ} (a : Fin k → F) (x : F) : F :=
  ∑ j : Fin k, a j * x ^ (j : ℕ)

/-- The coefficient vector `a` as a mathlib `Polynomial`, used only to import
the root count. -/
private def polyOf {F : Type*} [CommRing F] {k : ℕ} (a : Fin k → F) : F[X] :=
  ∑ j : Fin k, C (a j) * X ^ (j : ℕ)

private theorem eval_polyOf {F : Type*} [CommRing F] {k : ℕ} (a : Fin k → F) (x : F) :
    (polyOf a).eval x = polyEval a x := by
  simp [polyOf, polyEval, Polynomial.eval_finset_sum]

private theorem natDegree_polyOf_le {F : Type*} [CommRing F] {k : ℕ} (a : Fin k → F) :
    (polyOf a).natDegree ≤ k - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact le_trans (Polynomial.natDegree_C_mul_le _ _)
    (le_trans (Polynomial.natDegree_X_pow_le _) (Nat.le_sub_one_of_lt j.isLt))

private theorem coeff_polyOf {F : Type*} [CommRing F] {k : ℕ} (a : Fin k → F) (j : Fin k) :
    (polyOf a).coeff (j : ℕ) = a j := by
  rw [polyOf, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hij (Fin.val_injective h).symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **The coefficient-to-values map is injective** at `k` distinct evaluation
points: two polynomials of degree `< k` agreeing at `k` distinct points are
equal.  (mathlib:
`Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`.) -/
theorem injective_polyEval {F : Type*} [Field F] {k : ℕ} {xs : Fin k → F}
    (hxs : Function.Injective xs) :
    Function.Injective (fun a : Fin k → F => fun j => polyEval a (xs j)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro a b _
    funext j
    exact j.elim0
  intro a b hab
  have hzero : polyOf a - polyOf b = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hxs (fun j => ?_) ?_
    · rw [Polynomial.eval_sub, eval_polyOf, eval_polyOf, sub_eq_zero]
      exact congrFun hab j
    · rw [Fintype.card_fin]
      exact lt_of_le_of_lt
        (le_trans (Polynomial.natDegree_sub_le _ _)
          (max_le (natDegree_polyOf_le a) (natDegree_polyOf_le b)))
        (Nat.sub_lt hk Nat.one_pos)
  funext j
  have h := congrArg (fun q : F[X] => q.coeff (j : ℕ)) (sub_eq_zero.mp hzero)
  simpa only [coeff_polyOf] using h

/-- **The coefficient-to-values map is a bijection** at `k` distinct evaluation
points — the whole content of the CR18 §6.1.2 exercise.  Injectivity plus
finiteness of `F^k`. -/
theorem bijective_polyEval {F : Type*} [Field F] [Fintype F] {k : ℕ} {xs : Fin k → F}
    (hxs : Function.Injective xs) :
    Function.Bijective (fun a : Fin k → F => fun j => polyEval a (xs j)) :=
  Finite.injective_iff_bijective.mp (injective_polyEval hxs)

/-- The joint law at `k` distinct points is uniform on `F^k`: every value
vector is hit with probability `|F|^{-k}`. -/
theorem mass_forall_polyEval_eq {F : Type*} [Field F] [Fintype F] {k : ℕ}
    {xs : Fin k → F} (hxs : Function.Injective xs) (ys : Fin k → F) :
    (Dist.uniform (Fin k → F)).mass (fun a => ∀ j, polyEval a (xs j) = ys j)
      = (1 / (Fintype.card F : ℝ)) ^ k := by
  classical
  rw [Dist.mass_congr _ (Q := fun a : Fin k → F => (fun j => polyEval a (xs j)) = ys)
      (fun _ => funext_iff.symm),
    Dist.mass_preimage_eq_fTransform_apply,
    Dist.fTransform_bijection_uniform _ (bijective_polyEval hxs),
    Dist.uniform_apply, Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [one_div_pow]

/-- The joint law at *any* `k`-element set of points is uniform: the `Finset`
form of `mass_forall_polyEval_eq`, obtained by enumerating the set. -/
theorem mass_forall_mem_polyEval_eq_of_card {F : Type*} [Field F] [Fintype F]
    {k : ℕ} {t : Finset F} (ht : t.card = k) (c : F → F) :
    (Dist.uniform (Fin k → F)).mass (fun a => ∀ z ∈ t, polyEval a z = c z)
      = (1 / (Fintype.card F : ℝ)) ^ t.card := by
  subst ht
  set e : Fin t.card ≃ (t : Finset F) := t.equivFin.symm
  have hxs : Function.Injective (fun j => ((e j : (t : Finset F)) : F)) :=
    Subtype.coe_injective.comp e.injective
  rw [Dist.mass_congr _
      (Q := fun a : Fin t.card → F => ∀ j, polyEval a ((e j : (t : Finset F)) : F)
        = c ((e j : (t : Finset F)) : F))
      (fun a => ⟨fun h j => h _ (e j).2, fun h z hz => by
        have := h (e.symm ⟨z, hz⟩)
        rwa [Equiv.apply_symm_apply] at this⟩),
    mass_forall_polyEval_eq hxs]

/-- **The joint law at any at-most-`k` set of points is uniform.**  The
`k`-point case (`mass_forall_mem_polyEval_eq_of_card`) marginalized down by
`Dist.mass_forall_mem_erase_eq_sum`: each deleted point multiplies the mass by
`|F|`, which is exactly one factor of `|F|^{-1}` removed.

`k ≤ |F|` is the source's implicit hypothesis (`k ≤ 2^m`): it is what lets a
set of at most `k` evaluation points be completed to exactly `k` distinct
points, where `bijective_polyEval` applies. -/
theorem mass_forall_mem_polyEval_eq {F : Type*} [Field F] [Fintype F] {k : ℕ}
    (hk : k ≤ Fintype.card F) {s : Finset F} (hs : s.card ≤ k) (c : F → F) :
    (Dist.uniform (Fin k → F)).mass (fun a => ∀ z ∈ s, polyEval a z = c z)
      = (1 / (Fintype.card F : ℝ)) ^ s.card := by
  classical
  have hcard : (Fintype.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set P : Finset F → Prop := fun u => ∀ c' : F → F,
    (Dist.uniform (Fin k → F)).mass (fun a => ∀ z ∈ u, polyEval a z = c' z)
      = (1 / (Fintype.card F : ℝ)) ^ u.card
  have hstep : ∀ (t : Finset F) (j : F), j ∈ t → P t → P (t.erase j) := by
    intro t j hjt hPt c'
    rw [Dist.mass_forall_mem_erase_eq_sum (A := fun _ : F => F)
        (Dist.uniform (Fin k → F)) (fun z a => polyEval a z) t hjt c',
      Finset.sum_congr rfl (fun v _ => hPt (Function.update c' j v)),
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.card_erase_of_mem hjt]
    have h1 : t.card = t.card - 1 + 1 :=
      (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨j, hjt⟩)).symm
    rw [h1, pow_succ, Nat.add_sub_cancel]
    field_simp
  obtain ⟨t, hst, htc⟩ := Finset.exists_superset_card_eq hs hk
  exact Finset.forall_subset_of_forall_erase (P := P) hstep hst
    (fun c' => mass_forall_mem_polyEval_eq_of_card htc c') c

/-- **Every single evaluation is uniform** — CR18's "values that appear
perfectly random".  Needs one evaluation point to be available, i.e. `1 ≤ k`. -/
theorem mass_polyEval_eq {F : Type*} [Field F] [Fintype F] {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ Fintype.card F) (z v : F) :
    (Dist.uniform (Fin k → F)).mass (fun a => polyEval a z = v)
      = 1 / (Fintype.card F : ℝ) := by
  classical
  have h := mass_forall_mem_polyEval_eq hk (s := {z})
    (by rw [Finset.card_singleton]; exact hk1) (fun _ => v)
  rw [Finset.card_singleton, pow_one] at h
  rw [← h]
  exact Dist.mass_congr _ fun a => by simp

/-- **The CR18 §6.1.2 construction is `k`-wise independent**: with the `k`
coefficients drawn uniformly from `F`, the `|F|` evaluations `(a(z))_{z ∈ F}`
are `k`-wise independent — and, by `mass_polyEval_eq`, each one is uniform.
This is the exercise the notes leave open, in the source's own resource
shape `U_{km} → [k]·R_{m,m}`. -/
theorem kIndepRV_polyEval {F : Type*} [Field F] [Fintype F] {k : ℕ}
    (hk : k ≤ Fintype.card F) :
    Dist.kIndepRV (A := fun _ : F => F) k
      ⟨Dist.uniform (Fin k → F), Dist.uniform_isProbDist⟩
      (fun z a => polyEval a z) := by
  classical
  intro s hs c
  rw [mass_forall_mem_polyEval_eq hk hs c, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun z hz => ?_
  exact (mass_polyEval_eq (le_trans (Finset.card_pos.mpr ⟨z, hz⟩) hs) hk z (c z)).symm

end KWise

end RandomSystems
