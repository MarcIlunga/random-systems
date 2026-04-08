/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite Distributions

Lean 4 formalization of Definitions 1, 2, 4 from Lanzenberger-Maurer (TCC 2020).

A distribution over a type `A` is a finitely supported function `A → ℝ≥0`.
We use Mathlib's `Finsupp` to get `support`, `sum`, algebraic operations for free.

## Main Definitions

* `Dist A` — type alias for `A →₀ NNReal`
* `Dist.weight` — total mass `|X| := ∑ a, X(a)`
* `Dist.isProbDist` — weight = 1
* `Dist.uniform` — uniform distribution over a `Fintype`
* `Dist.marginal` — marginal distribution (Definition 2)
* `Dist.fTransform` — f-transformation (Definition 4)

## Design Notes

- Sub-distributions (weight ≤ 1) arise naturally in the proof of Theorem 1.
- `NNReal` (not `ENNReal`) since everything is finite; cleaner arithmetic.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

/-- A finite distribution over `A`: a finitely supported function `A → ℝ≥0`.

Paper Definition 1: "A distribution X : A → ℝ≥0 with finite support."
We do NOT require weight = 1 (sub-distributions appear in Theorem 1 proof). -/
abbrev Dist (A : Type*) := A →₀ NNReal

namespace Dist

variable {A : Type*} {B : Type*}

/-- The weight (total mass) of a distribution.
Paper: `|X| := ∑_{a ∈ A} X(a)`. -/
def weight [Fintype A] (X : Dist A) : NNReal :=
  ∑ a : A, X a

/-- A distribution is a probability distribution if its weight is 1. -/
def isProbDist [Fintype A] (X : Dist A) : Prop := X.weight = 1

/-- Evaluate a distribution on a subset.
Paper: `X(B) := ∑_{a ∈ B} X(a)`. -/
def evalSet (X : Dist A) (B : Finset A) : NNReal :=
  ∑ a ∈ B, X a

/-- Evaluate a distribution on a predicate: the total mass of elements satisfying `P`.

`evalPred X P = ∑_{a : P(a)} X(a)`

This is the named def that `Pr[P(x) | x ←$ D]` notation will expand to.
Equivalent to `evalSet X (Finset.univ.filter P)` but takes a predicate directly. -/
def evalPred [Fintype A] (X : Dist A) (P : A → Prop) [DecidablePred P] : NNReal :=
  ∑ a ∈ Finset.univ.filter P, X a

@[simp]
theorem evalPred_eq_evalSet [Fintype A] (X : Dist A) (P : A → Prop) [DecidablePred P] :
    X.evalPred P = X.evalSet (Finset.univ.filter P) := by
  rfl

theorem evalPred_le_weight [Fintype A] (X : Dist A) (P : A → Prop) [DecidablePred P] :
    X.evalPred P ≤ X.weight := by
  apply Finset.sum_le_sum_of_subset
  exact Finset.filter_subset _ _

/-- The zero distribution: all mass is 0. -/
def zero' (A : Type*) : Dist A := 0

/-- The uniform distribution over a finite nonempty type.
`uniform A` assigns mass `1 / |A|` to each element. -/
def uniform (A : Type*) [Fintype A] [Nonempty A] : Dist A :=
  Finsupp.equivFunOnFinite.invFun (fun _ => (1 : NNReal) / (Fintype.card A : NNReal))

/-! ### Uniform distribution lemmas -/

/-- Pointwise evaluation of the uniform distribution. -/
theorem uniform_apply [Fintype A] [Nonempty A] (a : A) :
    (uniform A) a = 1 / (Fintype.card A : NNReal) := by
  simp [uniform, Finsupp.equivFunOnFinite]

/-- The uniform distribution has weight 1. -/
theorem weight_uniform [Fintype A] [Nonempty A] :
    (uniform A).weight = 1 := by
  simp only [weight]
  have h_card_pos : (0 : NNReal) < (Fintype.card A : NNReal) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [Finset.sum_congr rfl (fun a _ => uniform_apply a)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀]
  exact_mod_cast h_card_pos.ne'

/-- The uniform distribution is a probability distribution. -/
theorem uniform_isProbDist [Fintype A] [Nonempty A] :
    (uniform A).isProbDist := weight_uniform

/-- The marginal distribution obtained by projecting onto the first component.

Paper Definition 2: Given a joint distribution X_{A×B}, the marginal X_A is
  X_A(a) := ∑_{b ∈ B} X_{A×B}(a, b). -/
def marginal [Fintype B] (X : Dist (A × B)) : Dist A :=
  X.sum (fun ⟨a, _⟩ w => Finsupp.single a w)

/-- The f-transformation of a distribution.

Paper Definition 4: Given a distribution X over A and f : A → B,
  (f(X))(b) := ∑_{a : f(a) = b} X(a).

This is the pushforward measure in the discrete case. -/
def fTransform [DecidableEq B] (f : A → B) (X : Dist A) : Dist B :=
  X.sum (fun a w => Finsupp.single (f a) w)

/-! ### Evaluating `fTransform` -/

/-- Fiber-sum form of `fTransform` evaluation.

`(fTransform f X) b` is the total mass of all `a` such that `f a = b`. -/
theorem fTransform_apply_eq_sum {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (X : Dist A) (b : B) :
    (fTransform f X) b =
      ∑ a ∈ (Finset.univ : Finset A).filter (fun a => f a = b), X a := by
  classical
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply]
  rw [← Finset.sum_filter (p := fun a => f a = b)]
  apply Finset.sum_subset
  · exact Finset.filter_subset_filter _ (Finset.subset_univ _)
  · intro a ha1 ha2
    have hfa : f a = b := (Finset.mem_filter.mp ha1).2
    have ha_supp : a ∉ X.support := by
      intro ha_supp
      apply ha2
      exact Finset.mem_filter.mpr ⟨ha_supp, hfa⟩
    exact Finsupp.notMem_support_iff.mp ha_supp

/-- Pushforward of a uniform distribution evaluated at a point equals
the fiber cardinality divided by the total cardinality.

`(fTransform f (uniform A)) b = |{a : f a = b}| / |A|` -/
theorem fTransform_uniform_apply [Fintype A] [DecidableEq B] [Nonempty A]
    (f : A → B) (b : B) :
    (fTransform f (uniform A)) b =
      ((Finset.univ.filter (fun a => f a = b)).card : NNReal)
        / (Fintype.card A : NNReal) := by
  classical
  rw [fTransform_apply_eq_sum]
  simp only [uniform_apply, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-! ### Independent product distributions -/

/-- Independent product of two (sub-)distributions.

`prod X Y` is the distribution on `A × B` obtained by sampling `a ~ X` and
`b ~ Y` independently and returning `(a,b)`. The weight is `|X| * |Y|`. -/
def prod [DecidableEq A] [DecidableEq B] (X : Dist A) (Y : Dist B) : Dist (A × B) :=
  X.sum (fun a wa => Y.sum (fun b wb => Finsupp.single (a, b) (wa * wb)))

theorem prod_apply [DecidableEq A] [DecidableEq B] (X : Dist A) (Y : Dist B) (a : A) (b : B) :
    prod X Y (a, b) = X a * Y b := by
  classical
  -- Push evaluation inside the nested sums and discharge each sum via `Finsupp.sum_eq_single`.
  simp [prod, Finsupp.sum_apply]
  let g : A → NNReal → NNReal :=
    fun a' wa => Y.sum (fun b' wb => (Finsupp.single (a', b') (wa * wb)) (a, b))
  change X.sum g = X a * Y b
  have hX : X.sum g = g a (X a) := by
    refine Finsupp.sum_eq_single a (f := X) (g := g) ?_ ?_
    · intro a' _hne0 hne
      simp [g, hne]
    · intro _
      simp [g]
  have hY : Y.sum (fun b' wb => if b' = b then X a * wb else 0) = X a * Y b := by
    simpa using
      (Finsupp.sum_eq_single b (f := Y)
        (g := fun b' wb => if b' = b then X a * wb else 0)
        (h₀ := by
          intro b' _hne0 hne
          simp [hne])
        (h₁ := by
          intro _
          simp))
  calc
    X.sum g = g a (X a) := hX
    _ = Y.sum (fun b' wb => if b' = b then X a * wb else 0) := by
      simp [g, Finsupp.single_apply]
    _ = X a * Y b := hY

theorem weight_prod [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (X : Dist A) (Y : Dist B) :
    (prod X Y).weight = X.weight * Y.weight := by
  classical
  -- Expand weight of the product distribution into a double sum and use `sum_mul_sum`.
  simp [weight, prod_apply, Fintype.sum_prod_type, Fintype.sum_mul_sum]

theorem prod_uniform (A B : Type*) [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    prod (uniform A) (uniform B) = uniform (A × B) := by
  classical
  ext p
  rcases p with ⟨a, b⟩
  -- Both sides assign constant mass `1/|A| * 1/|B| = 1/|A×B|` to each pair.
  simp [prod_apply, uniform, Fintype.card_prod, div_eq_mul_inv, mul_comm]

-- Basic properties

/-- Weight of the zero distribution is 0. -/
theorem weight_zero [Fintype A] : (zero' A).weight = 0 := by
  simp [weight, zero']

/-- The weight equals the Finsupp.sum with identity. -/
theorem weight_eq_finsupp_sum [Fintype A] (X : Dist A) :
    X.weight = X.sum (fun _ w => w) := by
  simp only [weight, Finsupp.sum]
  rw [← Finset.sum_subset (Finset.subset_univ X.support)]
  intro a _ ha
  exact Finsupp.notMem_support_iff.mp ha

/-- The f-transformation preserves weight.

  |f(X)| = |X|

Since fTransform just redistributes mass across bins without
creating or destroying any. -/
theorem weight_fTransform [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (X : Dist A) :
    (fTransform f X).weight = X.weight := by
  rw [weight_eq_finsupp_sum, weight_eq_finsupp_sum]
  show (Finsupp.mapDomain f X).sum (fun _ w => w) = X.sum (fun _ w => w)
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

/-- The f-transformation of the uniform distribution through a bijection
is the uniform distribution.

If `f : A → A` is a bijection, then the pushforward of the uniform
distribution through `f` is still uniform: each element receives mass
`1/|A|` because bijectivity means each preimage is a singleton.

This is a core ingredient in OTP-style arguments: if `k` is uniform
and `m ↦ m + k` is a bijection, then `m + k` is uniform. -/
theorem fTransform_bijection_uniform
    [Fintype A] [DecidableEq A] [Nonempty A]
    (f : A → A) (hf : Function.Bijective f) :
    fTransform f (uniform A) = uniform A := by
  have h_eq : fTransform f (uniform A) = Finsupp.mapDomain f (uniform A) := by
    simp [fTransform, Finsupp.mapDomain]
  rw [h_eq]; ext b
  obtain ⟨a, rfl⟩ := hf.surjective b
  rw [Finsupp.mapDomain_apply hf.injective]
  simp [uniform, Finsupp.equivFunOnFinite]

/-- Composing two f-transformations equals the f-transformation of the composition.

This is the pushforward functoriality law: `f_*(g_*(X)) = (f ∘ g)_*(X)`. -/
theorem fTransform_comp {C : Type*} [DecidableEq B] [DecidableEq C]
    (g : B → C) (f : A → B) (X : Dist A) :
    fTransform g (fTransform f X) = fTransform (g ∘ f) X := by
  show Finsupp.mapDomain g (Finsupp.mapDomain f X) = Finsupp.mapDomain (g ∘ f) X
  rw [Finsupp.mapDomain_comp]

/-- An equivalence pushes the uniform distribution to uniform.

Generalizes `fTransform_bijection_uniform` to maps between different types:
if `e : A ≃ B` is an equivalence, then the pushforward of `uniform A`
through `e` is `uniform B`. -/
theorem fTransform_equiv_uniform {A' B' : Type*} [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B'] [Nonempty A'] [Nonempty B']
    (e : A' ≃ B') :
    fTransform e (uniform A') = uniform B' := by
  ext b
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply, uniform]
  have h_supp : (Finsupp.equivFunOnFinite.invFun
    (fun _ : A' => (1 : NNReal) / (Fintype.card A' : NNReal))).support = Finset.univ := by
    ext s; simp [Finsupp.equivFunOnFinite]
  rw [h_supp, ← Finset.sum_filter]
  simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have h_filter : (Finset.univ.filter (fun a => e a = b)).card = 1 := by
    rw [show (Finset.univ.filter (fun a => e a = b)) = {e.symm b} from by
      ext a; simp [e.apply_eq_iff_eq_symm_apply]]
    exact Finset.card_singleton _
  rw [h_filter, Nat.cast_one, one_div, one_div]
  have h_card : Fintype.card A' = Fintype.card B' := Fintype.card_congr e
  rw [show (Fintype.card A' : NNReal) = (Fintype.card B' : NNReal) from by exact_mod_cast h_card]

/-- Projecting a uniform product distribution to the first component gives uniform.

If `(a, b)` is drawn uniformly from `A × B`, then `a` alone is uniform over `A`.
This is the discrete marginal-of-uniform-is-uniform fact. -/
theorem fTransform_fst_uniform (A' B' : Type*) [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B'] [Nonempty A'] [Nonempty B'] :
    fTransform Prod.fst (uniform (A' × B')) = uniform A' := by
  ext a
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply, uniform]
  have h_supp : (Finsupp.equivFunOnFinite.invFun
    (fun _ : A' × B' => (1 : NNReal) / (Fintype.card (A' × B') : NNReal))).support = Finset.univ := by
    ext s; simp [Finsupp.equivFunOnFinite]
  rw [h_supp, ← Finset.sum_filter]
  simp only [Finsupp.equivFunOnFinite, Finsupp.coe_mk, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have h_filter : (Finset.univ.filter (fun p : A' × B' => p.1 = a)).card = Fintype.card B' := by
    have : (Finset.univ.filter (fun p : A' × B' => p.1 = a)) =
      (Finset.univ : Finset B').map ⟨fun b => (a, b), fun b₁ b₂ h => by simpa using h⟩ := by
      ext ⟨a', b⟩; simp [eq_comm]
    rw [this, Finset.card_map, Finset.card_univ]
  rw [h_filter, Fintype.card_prod, Nat.cast_mul, mul_comm]
  congr 1
  rw [div_mul_eq_div_div, div_self, one_div]
  exact_mod_cast Fintype.card_pos (α := B').ne'

/-- Projecting a uniform product distribution to the second component gives uniform.

If `(a, b)` is drawn uniformly from `A × B`, then `b` alone is uniform over `B`. -/
theorem fTransform_snd_uniform (A' B' : Type*) [Fintype A'] [DecidableEq A']
    [Fintype B'] [DecidableEq B'] [Nonempty A'] [Nonempty B'] :
    fTransform Prod.snd (uniform (A' × B')) = uniform B' := by
  classical
  -- `snd = fst ∘ swap`
  have hsnd : (Prod.snd : A' × B' → B') = Prod.fst ∘ (Equiv.prodComm A' B') := by
    rfl
  calc
    fTransform (Prod.snd : A' × B' → B') (uniform (A' × B'))
        = fTransform (Prod.fst : B' × A' → B')
            (fTransform (Equiv.prodComm A' B') (uniform (A' × B'))) := by
            simp [hsnd, fTransform_comp]
    _ = fTransform (Prod.fst : B' × A' → B') (uniform (B' × A')) := by
            rw [fTransform_equiv_uniform (Equiv.prodComm A' B')]
    _ = uniform B' := by
            simpa using (fTransform_fst_uniform (A' := B') (B' := A'))

end Dist

end RandomSystems
