/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Part
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
* `Dist.mass` — mass of an event/predicate, summed over finite support
* `Dist.massSet` — mass of a set, summed over finite support
* `Dist.cond` — partial conditional probability of one event given another
* `Dist.condPMF` — conditional law of a random variable given an event
* `Dist.RV` — a random variable as a function from samples to values
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

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {A : Type*} {B : Type*} {Ω : Type*} {C : Type*}
variable [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
variable [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C]

/-- The weight (total mass) of a distribution.
Paper: `|X| := ∑_{a ∈ A} X(a)`. -/
def weight (X : Dist A) : NNReal :=
  X.sum fun _ w => w

omit [Nonempty A] in
/-- On a finite carrier, support-based weight is the ordinary sum over all
points.  (Needs `Fintype A` but not `Nonempty A` — the latter is a section-variable leak.) -/
theorem weight_eq_sum (X : Dist A) :
    X.weight = ∑ a : A, X a := by
  simpa [weight] using
    (Finsupp.sum_fintype (f := X) (g := fun _ w => w) (h := by intro _; rfl))

omit [Nonempty A] in
/-- A mass function on a finite carrier as a finite-support distribution. -/
def ofFiniteMassFunction (law : A → NNReal) : Dist A :=
  Finsupp.onFinset Finset.univ law (by intro a _; exact Finset.mem_univ a)

omit [Nonempty A] in
@[simp]
theorem ofFiniteMassFunction_apply (law : A → NNReal) (a : A) :
    ofFiniteMassFunction law a = law a := by
  simp [ofFiniteMassFunction]

omit [Nonempty A] in
/-- The total weight of a finite mass function as a distribution is the sum of
its masses over the carrier. -/
theorem weight_ofFiniteMassFunction (law : A → NNReal) :
    (ofFiniteMassFunction law).weight = ∑ a : A, law a := by
  simp [weight_eq_sum, ofFiniteMassFunction]

/-- A distribution over `Part Y` splits its weight into the `⊥`/`none` mass plus the
sum of the defined-output (`some y`) masses — every `Part` value is `none` or
`some y` (`Part.eq_none_or_eq_some`, here via `Part.equivOption`). -/
theorem weight_eq_none_add_sum_some {Y : Type*} [Fintype Y] (D : Dist (Part Y)) :
    D.weight = D Part.none + ∑ y : Y, D (Part.some y) := by
  haveI : Nonempty (Part Y) := ⟨Part.none⟩
  haveI : Fintype (Part Y) := Fintype.ofEquiv (Option Y) Part.equivOption.symm
  rw [weight_eq_sum, ← Equiv.sum_comp Part.equivOption.symm (fun a => D a), Fintype.sum_option]
  rfl

/-- A distribution is a probability distribution if its weight is 1. -/
def isProbDist (X : Dist A) : Prop := X.weight = 1

/-- Probability distributions are distributions with total mass one. -/
abbrev ProbDist (A : Type*) := {X : Dist A // X.isProbDist}

/-- Probability distributions evaluate like their underlying mass functions. -/
instance : CoeFun (ProbDist A) (fun _ => A → NNReal) where
  coe X := X.val

/-- Represent a probability law by its finite support subtype.

This is useful when a downstream side condition should range over exactly the
samples that can occur under the law, without requiring the whole ambient
carrier to be finite or relevant. -/
noncomputable def supportProbDist {A : Type*} (D : ProbDist A) :
    ProbDist {a : A // a ∈ D.val.support} :=
  ⟨ofFiniteMassFunction (fun a : {a : A // a ∈ D.val.support} => D.val a.1), by
    rw [isProbDist, weight_ofFiniteMassFunction]
    rw [← D.property]
    unfold weight
    rw [Finsupp.sum]
    exact Finset.sum_attach D.val.support (fun a => D.val a)⟩

@[simp]
theorem supportProbDist_apply {A : Type*} (D : ProbDist A)
    (a : {a : A // a ∈ D.val.support}) :
    supportProbDist D a = D.val a.1 := by
  rfl

/-- Evaluate a distribution on a subset.
Paper: `X(B) := ∑_{a ∈ B} X(a)`. -/
def evalSet (X : Dist A) (B : Finset A) : NNReal :=
  ∑ a ∈ B, X a

/-- Event mass of a distribution, summed over its finite support.

This is the support-based form of CR18/LM20 Definition 1 notation
`X(A) := ∑_{a ∈ A} X(a)`. Unlike `evalPred`, it does not require
`Fintype A`; the finite support is already carried by `Dist A = A →₀ ℝ≥0`. -/
noncomputable def mass (X : Dist A) (P : A → Prop) : NNReal :=
  X.sum fun a w => if P a then w else 0

/-- Mass of a set under a distribution, using the finite support of the
distribution. This is the direct formalization of the overloaded paper notation
`X(A)` for `A ⊆ 𝓐`. -/
noncomputable def massSet (X : Dist A) (E : Set A) : NNReal :=
  X.mass fun a => a ∈ E

/-- Restrict a distribution to an event, dropping all mass outside it. -/
noncomputable def restrict {A : Type*} (X : Dist A) (P : A → Prop) : Dist A :=
  Finsupp.filter P X

@[simp]
theorem restrict_apply {A : Type*} (X : Dist A) (P : A → Prop) (a : A) :
    X.restrict P a = if P a then X a else 0 := by
  simp [restrict, Finsupp.filter_apply]

/-- The mass of `P` after restricting to `Q` is the mass of `P ∩ Q`. -/
theorem mass_restrict {A : Type*} (X : Dist A) (P Q : A → Prop) :
    (X.restrict Q).mass P = X.mass (fun a => P a ∧ Q a) := by
  unfold restrict mass Finsupp.sum
  simp only [Finsupp.support_filter, Finsupp.filter_apply]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hP : P a <;> by_cases hQ : Q a <;> simp [hP, hQ]

theorem mass_true {A : Type*} (X : Dist A) :
    X.mass (fun _ => True) = X.weight := by
  unfold mass weight
  simp

/-- Mass depends only on the event up to logical equivalence. -/
theorem mass_congr {A : Type*} (X : Dist A) {P Q : A → Prop} (h : ∀ a, P a ↔ Q a) :
    X.mass P = X.mass Q := by
  unfold mass
  congr 1
  funext a w
  simp only [h a]

open scoped Classical in
/-- An event and its complement partition the total mass: `X(P) + X(¬P) = |X|`. -/
theorem mass_add_compl {A : Type*} (X : Dist A) (P : A → Prop) :
    X.mass P + X.mass (fun a => ¬ P a) = X.weight := by
  unfold mass weight Finsupp.sum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by by_cases h : P a <;> simp [h]

/-- The mass of an event never exceeds the total mass: `X(P) ≤ |X|`. -/
theorem mass_le_weight {A : Type*} (X : Dist A) (P : A → Prop) :
    X.mass P ≤ X.weight := by
  rw [← mass_add_compl X P]; exact le_self_add

omit [Fintype A] [Nonempty A] in
/-- Candidate for upstream: a finite pairwise-disjoint family of events has
total mass at most the distribution weight. This is the finite-support
subdistribution form of the elementary disjoint-union bound, with no
`Fintype` assumption on the sample space. -/
theorem sum_mass_le_weight_of_pairwise_disjoint {A ι : Type*} [Fintype ι]
    (X : Dist A) (E : ι → A → Prop)
    (hdisj : ∀ i j, i ≠ j → ∀ a, E i a → E j a → False) :
    (∑ i : ι, X.mass (E i)) ≤ X.weight := by
  classical
  unfold mass weight Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum ?_
  intro a _ha
  by_cases h : ∃ i : ι, E i a
  · rcases h with ⟨i0, hi0⟩
    have hunique : ∀ j : ι, E j a → j = i0 := by
      intro j hj
      by_contra hne
      exact hdisj j i0 hne a hj hi0
    have hsum : (∑ i : ι, if E i a then X a else 0) = X a := by
      rw [Finset.sum_eq_single i0]
      · simp [hi0]
      · intro j _ hji
        have hnot : ¬ E j a := by
          intro hj
          exact hji (hunique j hj)
        simp [hnot]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ i0))
    rw [hsum]
  · have hnone : ∀ i : ι, ¬ E i a := by
      intro i hi
      exact h ⟨i, hi⟩
    simp [hnone]

omit [Fintype A] [Nonempty A] in
/-- Candidate for upstream: a finite pairwise-disjoint family of events that
covers the sample space has total mass exactly equal to the distribution
weight. This is the finite-support subdistribution form of a disjoint
partition. -/
theorem sum_mass_eq_weight_of_pairwise_disjoint_of_cover {A ι : Type*} [Fintype ι]
    (X : Dist A) (E : ι → A → Prop)
    (hdisj : ∀ i j, i ≠ j → ∀ a, E i a → E j a → False)
    (hcover : ∀ a, ∃ i, E i a) :
    (∑ i : ι, X.mass (E i)) = X.weight := by
  classical
  unfold mass weight Finsupp.sum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rcases hcover a with ⟨i0, hi0⟩
  have hunique : ∀ j : ι, E j a → j = i0 := by
    intro j hj
    by_contra hne
    exact hdisj j i0 hne a hj hi0
  rw [Finset.sum_eq_single i0]
  · simp [hi0]
  · intro j _ hji
    have hnot : ¬ E j a := by
      intro hj
      exact hji (hunique j hj)
    simp [hnot]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ i0))

/-- Under a probability distribution every event has mass at most one. -/
theorem mass_le_one {A : Type*} {X : Dist A} (hX : X.isProbDist) (P : A → Prop) :
    X.mass P ≤ 1 := by rw [← hX]; exact mass_le_weight X P

/-- Restricting to an event leaves exactly the mass of that event. -/
theorem weight_restrict {A : Type*} (X : Dist A) (P : A → Prop) :
    (X.restrict P).weight = X.mass P := by
  rw [← mass_true (X.restrict P), mass_restrict]
  simp

/-- Partial conditional probability/mass.

`X.cond P Q` is defined exactly when the conditioning event `Q` has nonzero
mass, and then equals `X(P ∧ Q) / X(Q)`. This is the generic distribution-level
operation used by CR18 behavior kernels. -/
noncomputable def cond (X : Dist A) (P Q : A → Prop) : Part NNReal :=
  ⟨X.mass Q ≠ 0, fun _ => X.mass (fun a => P a ∧ Q a) / X.mass Q⟩

/-- The value of a conditional probability is the ratio of masses. -/
theorem cond_get {A : Type*} (X : Dist A) (P Q : A → Prop) (h : (X.cond P Q).Dom) :
    (X.cond P Q).get h = X.mass (fun a => P a ∧ Q a) / X.mass Q := rfl

def condEvent (X: Dist A) (P Q: Set A): Part NNReal :=
  X.cond (fun a => a ∈ P) (fun a => a ∈ Q)

end Dist

namespace CryptoNotation

/-- Event-mass notation:
- `Pr[φ(x) | x ←$ D]` expands to `Dist.mass D (fun x => φ x)`.

This follows CR18/LM20 Definition 1: distributions are finite-support mass
functions, and event probability/mass is obtained by summing the weights in the
event over that support. -/
scoped syntax "Pr[" term " | " Lean.Parser.Term.funBinder " ←$ " term "]" : term
scoped macro_rules
  | `(Pr[$body | $b:funBinder ←$ $D]) =>
      `(RandomSystems.Dist.mass $D (fun $b => $body))

/-- Conditional event-mass notation:
- `Pr[φ(x) | x ←$ D, ψ(x)]` expands to
  `Dist.cond D (fun x => φ x) (fun x => ψ x)`.

The result is partial, undefined exactly when the conditioning event has mass
zero. -/
scoped syntax "Pr[" term " | " Lean.Parser.Term.funBinder " ←$ " term ", " term "]" : term
scoped macro_rules
  | `(Pr[$body | $b:funBinder ←$ $D, $cond]) =>
      `(RandomSystems.Dist.cond $D (fun $b => $body) (fun $b => $cond))

end CryptoNotation

namespace Dist

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

variable {A : Type*} {B : Type*} {Ω : Type*} {C : Type*}
variable [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
variable [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C]

/-- Evaluate a distribution on a predicate: the total mass of elements satisfying `P`.

`evalPred X P = ∑_{a : P(a)} X(a)`

This is the older finite-carrier predicate evaluator, equivalent to
`evalSet X (Finset.univ.filter P)`. Prefer `mass` when the finite support of
the distribution itself should supply the finiteness, as in CR18. -/
def evalPred (X : Dist A) (P : A → Prop) : NNReal :=
  ∑ a ∈ Finset.univ.filter P, X a

@[simp]
theorem evalPred_eq_evalSet (X : Dist A) (P : A → Prop) :
    X.evalPred P = X.evalSet (Finset.univ.filter P) := by
  rfl

theorem evalPred_le_weight (X : Dist A) (P : A → Prop) :
    X.evalPred P ≤ X.weight := by
  rw [weight_eq_sum]
  unfold evalPred
  apply Finset.sum_le_sum_of_subset
  exact Finset.filter_subset _ _

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
  [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C] in
/-- UPSTREAM-CANDIDATE: finite union bound for predicate mass. -/
theorem evalPred_iUnion_le {A ι : Type*} [Fintype A] [Fintype ι]
    (X : Dist A) (P : ι → A → Prop) [∀ p, DecidablePred (P p)] :
    X.evalPred (fun a => ∃ p, P p a) ≤ ∑ p, X.evalPred (P p) := by
  simp only [Dist.evalPred, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : ∃ p, P p a
  · rw [if_pos ha]
    obtain ⟨p₀, hp₀⟩ := ha
    have hbound :
        (if P p₀ a then X a else (0 : NNReal))
          ≤ ∑ x, if P x a then X a else 0 :=
      Finset.single_le_sum (f := fun p => if P p a then X a else 0)
        (fun _ _ => zero_le _) (Finset.mem_univ p₀)
    refine le_trans (le_of_eq (if_pos hp₀).symm) (le_trans hbound (le_of_eq ?_))
    exact Finset.sum_congr rfl (fun x _ => by congr 1)
  · rw [if_neg ha]
    exact zero_le _

/-- The zero distribution: all mass is 0. -/
def zero' (A : Type*) : Dist A := 0

/-- The uniform distribution over a finite nonempty type.
`uniform A` assigns mass `1 / |A|` to each element. -/
def uniform (A : Type*) [Fintype A] [Nonempty A] : Dist A :=
  Finsupp.equivFunOnFinite.invFun (fun _ => (1 : NNReal) / (Fintype.card A : NNReal))

/-! ### Uniform distribution lemmas -/

/-- Pointwise evaluation of the uniform distribution. -/
theorem uniform_apply (a : A) :
    (uniform A) a = 1 / (Fintype.card A : NNReal) := by
  simp [uniform, Finsupp.equivFunOnFinite]

omit [Fintype B] [Nonempty B] [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C] in
/-- UPSTREAM-CANDIDATE: counting form of predicate mass over a uniform distribution. -/
theorem evalPred_uniform (P : A → Prop) [DecidablePred P] :
    (uniform A).evalPred P =
      ((Finset.univ.filter P).card : NNReal) / (Fintype.card A : NNReal) := by
  unfold evalPred
  rw [Finset.sum_congr rfl (fun a _ => uniform_apply a), Finset.sum_const,
    nsmul_eq_mul, mul_one_div]
  congr 3
  exact Finset.filter_congr_decidable _ P _

omit [Fintype B] [Nonempty B] [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C] in
/-- UPSTREAM-CANDIDATE: uniform predicate mass bound from a fiber-cardinality bound. -/
theorem evalPred_uniform_le
    (P : A → Prop) [DecidablePred P] {d : ℕ} (hd : 0 < d)
    (hcard : d * (Finset.univ.filter P).card ≤ Fintype.card A) :
    (uniform A).evalPred P ≤ 1 / (d : NNReal) := by
  rw [evalPred_uniform]
  rw [div_le_div_iff₀ (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast hd)]
  rw [one_mul]
  calc ((Finset.univ.filter P).card : NNReal) * (d : NNReal)
      = ((d * (Finset.univ.filter P).card : ℕ) : NNReal) := by push_cast; ring
    _ ≤ (Fintype.card A : NNReal) := by exact_mod_cast hcard

/-- The uniform distribution has weight 1. -/
theorem weight_uniform :
    (uniform A).weight = 1 := by
  rw [weight_eq_sum]
  have h_card_pos : (0 : NNReal) < (Fintype.card A : NNReal) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [Finset.sum_congr rfl (fun a _ => uniform_apply a)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀]
  exact_mod_cast h_card_pos.ne'

/-- The uniform distribution is a probability distribution. -/
theorem uniform_isProbDist :
    (uniform A).isProbDist := weight_uniform

/-- The unique probability distribution on a one-point sample space. -/
def unitProbDist : ProbDist PUnit :=
  ⟨uniform PUnit, uniform_isProbDist⟩

/-- The marginal distribution obtained by projecting onto the first component.

Paper Definition 2: Given a joint distribution X_{A×B}, the marginal X_A is
  X_A(a) := ∑_{b ∈ B} X_{A×B}(a, b). -/
def marginal (X : Dist (A × B)) : Dist A :=
  X.sum (fun ⟨a, _⟩ w => Finsupp.single a w)

/-- The marginal of a distribution over a finite product, projected to one
coordinate.

For a family of alphabets `X : ι → Type*`, a point of the product is a function
`x : (i : ι) → X i`. The marginal at `j : ι` is the pushforward by evaluation
at `j`, i.e. `x ↦ x j`. -/
def marginalAt {ι : Type*} {X : ι → Type*}
    (F : Dist ((i : ι) → X i)) (j : ι) : Dist (X j) :=
  F.sum (fun x w => Finsupp.single (x j) w)

/-- Pointwise form of `marginalAt`: the mass at `xj` is the mass of the fiber
of product points whose `j`-th coordinate equals `xj`. -/
theorem marginalAt_apply {ι : Type*} {X : ι → Type*}
    (F : Dist ((i : ι) → X i)) (j : ι) (xj : X j) :
    marginalAt F j xj = F.mass (fun x => x j = xj) := by
  unfold marginalAt mass
  simp only [Finsupp.sum_apply, Finsupp.single_apply]

/-- The f-transformation of a distribution.

Paper Definition 4: Given a distribution X over A and f : A → B,
  (f(X))(b) := ∑_{a : f(a) = b} X(a).

This is the pushforward measure in the discrete case. -/
def fTransform (f : A → B) (X : Dist A) : Dist B :=
  X.sum (fun a w => Finsupp.single (f a) w)

/-- Pointwise evaluation of a pushforward is the mass of the fiber. -/
theorem fTransform_apply_eq_mass {A B : Type*}
    (f : A → B) (X : Dist A) (b : B) :
    fTransform f X b = X.mass (fun a => f a = b) := by
  unfold fTransform mass
  simp only [Finsupp.sum_apply, Finsupp.single_apply]

/-- Fiber mass is pointwise evaluation of the pushforward. -/
theorem mass_preimage_eq_fTransform_apply {A B : Type*}
    (f : A → B) (X : Dist A) (b : B) :
    X.mass (fun a => f a = b) = fTransform f X b :=
  (fTransform_apply_eq_mass f X b).symm

/-- Evaluating a pushforward at an image point of an injective map recovers the
original mass. -/
theorem fTransform_injective_apply {A B : Type*}
    (X : Dist A) (f : A → B) (hf : Function.Injective f) (a : A) :
    fTransform f X (f a) = X a := by
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ hne
    simp [hf.ne hne]
  · intro ha
    simp [Finsupp.notMem_support_iff.mp ha]

/-- Evaluating a pushforward away from the image of the map gives zero mass. -/
theorem fTransform_apply_of_forall_ne {A B : Type*}
    (X : Dist A) (f : A → B) (b : B) (h : ∀ a, f a ≠ b) :
    fTransform f X b = 0 := by
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro a _
  simp [h a]

/-- Candidate for upstream: every support element of a pushforward has a
support witness in the source distribution. -/
theorem mem_support_fTransform {A B : Type*} (f : A → B) (X : Dist A) {b : B}
    (hb : b ∈ (fTransform f X).support) : ∃ a ∈ X.support, f a = b := by
  classical
  have hsub : (fTransform f X).support ⊆ X.support.image f := Finsupp.mapDomain_support
  simpa [fTransform] using hsub hb

/-- Event mass under a pushforward is event mass of the preimage. -/
theorem mass_fTransform {A B : Type*}
    (f : A → B) (X : Dist A) (P : B → Prop) :
    (fTransform f X).mass P = X.mass (fun a => P (f a)) := by
  unfold fTransform mass
  show (Finsupp.mapDomain f X).sum (fun b w => if P b then w else 0) =
      X.sum (fun a w => if P (f a) then w else 0)
  rw [Finsupp.sum_mapDomain_index
    (fun b => by by_cases hb : P b <;> simp [hb])
    (fun b m₁ m₂ => by by_cases hb : P b <;> simp [hb])]

/-- Pushforward preserves total mass. -/
theorem weight_fTransform {A B : Type*}
    (f : A → B) (X : Dist A) :
    (fTransform f X).weight = X.weight := by
  unfold weight
  show (Finsupp.mapDomain f X).sum (fun _ w => w) = X.sum (fun _ w => w)
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]

/-- Pushforward preserves total probability mass. -/
theorem fTransform_isProbDist {A B : Type*} (f : A → B) {X : Dist A}
    (hX : X.isProbDist) : (fTransform f X).isProbDist := by
  unfold isProbDist
  rw [weight_fTransform]
  exact hX

/-- `isProbDist` normalizes through pushforward. -/
@[simp] theorem isProbDist_fTransform {A B : Type*} (f : A → B) (X : Dist A) :
    (fTransform f X).isProbDist ↔ X.isProbDist := by
  unfold isProbDist
  rw [weight_fTransform]

/-- Dividing every mass by `c` divides the total mass by `c`. -/
theorem weight_mapRange_div {A : Type*} (X : Dist A) (c : NNReal) :
    weight (Finsupp.mapRange (fun w => w / c) (by simp) X : Dist A) =
      X.weight / c := by
  unfold weight
  rw [Finsupp.sum_mapRange_index]
  · unfold Finsupp.sum
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    exact div_eq_mul_inv (X a) c
  · intro a
    simp

/-! ### Random variables -/

/-- A random variable is a function from a sample space to a value space.

This is intentionally only an abbreviation, matching Mathlib's discipline:
random variables are functions; distributions over their values are obtained
by pushforward. -/
abbrev RV : Type _ :=
  Ω → A

/-- The probability mass function induced by a random variable.

`PMF p X` is the low-level Lean form of the paper notation `P_X`: the
ambient random experiment has mass function `p` on outcomes `ω`, and
`P_X(a) = ∑_{ω : X ω = a} p(ω)`.

Paper-facing notation below suppresses `p`, matching Maurer's convention that
probabilities are taken in the current random experiment. -/
def PMF (p : ProbDist Ω) (X : RV (Ω := Ω) (A := A)) : ProbDist A :=
  ⟨fTransform X p.val, by
    change (fTransform X p.val).weight = 1
    unfold fTransform weight
    show (Finsupp.mapDomain X p.val).sum (fun _ w => w) = 1
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact p.property⟩

/-- Paper-facing PMF notation in the current random experiment.

The notation intentionally omits the low-level experiment mass `p`, following
CR18/Maurer notation. In Lean, it expands using the ambient variable named
`p : ProbDist Ω`. -/
syntax "ℙ⟦" term "⟧" : term
syntax "ℙ⟦" term "⟧[" term "]" : term
macro "ℙ⟦" X:term "⟧" : term => do
  let p := Lean.mkIdent `p
  `(RandomSystems.Dist.PMF $p $X)
macro "ℙ⟦" X:term "⟧[" x:term "]" : term => do
  let p := Lean.mkIdent `p
  `(RandomSystems.Dist.PMF $p $X $x)

/-- Pointwise form of the PMF definition:
`P_X(a) = ∑_{ω : X ω = a} p(ω)`. -/
theorem PMF_apply {Ω A : Type*}
    (p : ProbDist Ω) (X : RV (Ω := Ω) (A := A)) (a : A) :
    ℙ⟦X⟧[a] = p.val.mass (fun ω => X ω = a) := by
  unfold PMF fTransform mass
  simp only [Finsupp.sum_apply, Finsupp.single_apply]

/-! ### Function-valued random variables

A *function-valued* random variable is a random variable whose values are
themselves functions, `X : RV Ω (A → B)`. Equivalently — and this is its entire
content — it is an `A`-indexed family of ordinary random variables `(X a)ₐ`
(a stochastic process indexed by `A`); see `RV.funEquiv`.

The single new operation is *evaluation*: applying `X` at a point `a : A` yields
an ordinary `B`-valued random variable `X.eval a`. Evaluation is a deterministic
map on the value space (`evₐ : (A → B) → B`, `f ↦ f a`), so the law of `X.eval a`
is automatically the pushforward of `X`'s law along `evₐ` (`mass_eval`) — no new
probabilistic machinery, only `fTransform`. Partial functions are the special
case `B := Part B'` (`A →. B' = A → Part B'`). -/

/-- Evaluation of a function-valued random variable at a point: the `B`-valued
random variable `ω ↦ X ω a`. (Maurer: "`X` is a function-valued random variable,
hence `X(a)` is a `B`-valued random variable".) -/
def RV.eval {Ω A B : Type*} (X : RV (Ω := Ω) (A := A → B)) (a : A) :
    RV (Ω := Ω) (A := B) :=
  fun ω => X ω a

/-- Evaluation is the deterministic image of `X` under `evₐ : (A → B) → B`,
`f ↦ f a`; this is what makes the law of an evaluation a pushforward of `X`'s. -/
theorem RV.eval_eq_comp {Ω A B : Type*} (X : RV (Ω := Ω) (A := A → B)) (a : A) :
    X.eval a = (fun f : A → B => f a) ∘ X :=
  rfl

/-- A function-valued random variable viewed as the `A`-indexed family of
ordinary random variables `(X a)ₐ` obtained by evaluating at each point. Forward
map of `RV.funEquiv`. -/
def RV.curry {Ω A B : Type*} (X : RV (Ω := Ω) (A := A → B)) :
    A → RV (Ω := Ω) (A := B) :=
  fun a => X.eval a

/-- Assemble an `A`-indexed family of random variables into a single
function-valued random variable. Inverse of `RV.curry`. -/
def RV.uncurry {Ω A B : Type*} (F : A → RV (Ω := Ω) (A := B)) :
    RV (Ω := Ω) (A := A → B) :=
  fun ω a => F a ω

/-- A function-valued random variable is exactly an `A`-indexed family of
ordinary random variables: `RV Ω (A → B) ≃ (A → RV Ω B)`. The two views carry
the same data; evaluation picks out one member of the family. -/
def RV.funEquiv {Ω A B : Type*} :
    RV (Ω := Ω) (A := A → B) ≃ (A → RV (Ω := Ω) (A := B)) where
  toFun := RV.curry
  invFun := RV.uncurry
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The law of an evaluation is the pushforward of `X`'s law along `evₐ`: its mass
at `b` is the total mass of the functions sending `a` to `b`, i.e. the fiber sum
`∑_{f : f a = b} ℙ⟦X⟧ f`, supplied automatically by `fTransform`. For a single
input this is Maurer's channel behavior `p^C_{Y|X}(b, a) = Pr^C[C(a) = b]`. -/
theorem mass_eval {Ω A B : Type*}
    (p : ProbDist Ω) (X : RV (Ω := Ω) (A := A → B)) (a : A) (b : B) :
    ℙ⟦X.eval a⟧[b] = (ℙ⟦X⟧).val.mass (fun f => f a = b) := by
  rw [PMF_apply]
  show p.val.mass (fun ω => X ω a = b) = (fTransform X p.val).mass (fun f => f a = b)
  rw [mass_fTransform]

/-- Conditional law of a random variable given an event on the sample space.

`condPMF p X E` is undefined exactly when `p(E) = 0`. When it is defined, its
mass at `a` is `Pr[X = a ∧ E] / Pr[E]`. -/
noncomputable def condPMF {Ω A : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (E : Ω → Prop) : Part (ProbDist A) :=
  ⟨p.val.mass E ≠ 0,
    fun hE =>
      ⟨Finsupp.mapRange (fun w => w / p.val.mass E) (by simp)
        (fTransform X (p.val.restrict E)), by
          unfold isProbDist
          rw [weight_mapRange_div, weight_fTransform, weight_restrict]
          exact div_self hE⟩⟩

theorem condPMF_apply {Ω A : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (E : Ω → Prop)
    (hE : p.val.mass E ≠ 0) (a : A) :
    (condPMF p X E).get hE a =
      p.val.mass (fun ω => X ω = a ∧ E ω) / p.val.mass E := by
  unfold condPMF
  rw [Finsupp.mapRange_apply, fTransform_apply_eq_mass, mass_restrict]

/-- Conditional probability function of `X` given `Y`.

This is the paper-facing object `p_{X|Y}`: a partial function of two arguments
`(a, b)`, undefined exactly when `Pr[Y = b] = 0`. -/
noncomputable def condPMFOf {Ω A B : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B)) :
    A → B → Part NNReal :=
  fun a b =>
    ⟨p.val.mass (fun ω => Y ω = b) ≠ 0,
      fun _ => p.val.mass (fun ω => X ω = a ∧ Y ω = b) /
        p.val.mass (fun ω => Y ω = b)⟩

/-- Paper-facing conditional PMF notation in the current random experiment.

`ℙ⟦X | Y⟧` is the partial function `(x, y) ↦ P_{X|Y}(x, y)`;
`ℙ⟦X | Y⟧[x, y]` is its partial value at `(x, y)`.

The notation intentionally omits the low-level experiment mass `p`, following
CR18/Maurer notation. In Lean, it expands using the ambient variable named
`p : ProbDist Ω`. -/
syntax "ℙ⟦" term " | " term "⟧" : term
syntax "ℙ⟦" term " | " term "⟧[" term ", " term "]" : term
macro "ℙ⟦" X:term " | " Y:term "⟧" : term => do
  let p := Lean.mkIdent `p
  `(RandomSystems.Dist.condPMFOf $p $X $Y)
macro "ℙ⟦" X:term " | " Y:term "⟧[" x:term ", " y:term "]" : term => do
  let p := Lean.mkIdent `p
  `(RandomSystems.Dist.condPMFOf $p $X $Y $x $y)

theorem condPMFOf_apply {Ω A B : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B)) (b : B)
    (hb : p.val.mass (fun ω => Y ω = b) ≠ 0) (a : A) :
    (ℙ⟦X | Y⟧[a, b]).get hb =
      p.val.mass (fun ω => X ω = a ∧ Y ω = b) /
        p.val.mass (fun ω => Y ω = b) := rfl

/-- The fixed-`b` slice of `p_{X|Y}` as a probability distribution over `A`. -/
noncomputable def condPMFOfDist {Ω A B : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B)) (b : B)
    (hb : p.val.mass (fun ω => Y ω = b) ≠ 0) : ProbDist A :=
  (condPMF p X (fun ω => Y ω = b)).get hb

theorem condPMFOfDist_apply {Ω A B : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B)) (b : B)
    (hb : p.val.mass (fun ω => Y ω = b) ≠ 0) (a : A) :
    condPMFOfDist p X Y b hb a = (ℙ⟦X | Y⟧[a, b]).get hb := by
  change ((condPMF p X (fun ω => Y ω = b)).get hb) a =
    (ℙ⟦X | Y⟧[a, b]).get hb
  rw [condPMF_apply, condPMFOf_apply]

theorem condPMF_isProbDist {Ω A : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (E : Ω → Prop)
    (hE : p.val.mass E ≠ 0) :
    ((condPMF p X E).get hE).val.isProbDist :=
  ((condPMF p X E).get hE).property

theorem condPMFOf_isProbDist {Ω A B : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B)) (b : B)
    (hb : p.val.mass (fun ω => Y ω = b) ≠ 0) :
    (condPMFOfDist p X Y b hb).val.isProbDist :=
  (condPMFOfDist p X Y b hb).property

/-- **Law transport for conditional PMFs.** A conditional PMF of two
*deterministic images* `g ∘ S`, `h ∘ S` of a random variable `S` depends only on
the law of `S`: it equals the conditional PMF of `g`, `h` computed in the
experiment whose sample space is the value space of `S` under the pushforward law
`ℙ⟦S⟧`. This is the engine behind "behavior is computed from the distribution over
deterministic systems": every observable is a deterministic image of `S`, so it
factors through `ℙ⟦S⟧`. -/
theorem condPMFOf_comp {Ω A B C : Type*} (p : ProbDist Ω)
    (S : RV (Ω := Ω) (A := C)) (g : C → A) (h : C → B) :
    condPMFOf p (fun ω => g (S ω)) (fun ω => h (S ω)) = condPMFOf (PMF p S) g h := by
  funext a b
  have e : (PMF p S).val = fTransform S p.val := rfl
  refine Part.ext' ?_ ?_
  · simp only [condPMFOf, e, mass_fTransform]
  · intro _ _
    simp only [condPMFOf, e, mass_fTransform]

/-! ### Statistical independence of random variables (CR18 Appendix A, Def A.6)

CR18 **Definition A.6**: random variables `X, Y` are *statistically independent*
iff the joint distribution factors into the marginals,
`P_{XY}(x,y) = P_X(x)·P_Y(y)`; a family `X₁,…,Xₙ` is (mutually) independent iff the
joint factors completely, `P_{X₁…Xₙ}(x₁,…,xₙ) = ∏ᵢ P_{Xᵢ}(xᵢ)`. A PMF value
`P_X(x) = Pr[X=x]` (Def A.4) is `p.val.mass (X · = x)`; the marginals of a product
distribution are `mass_prod_fst`/`mass_prod_snd` (Def A.4); the conditional
distribution `P_{X|Y}` (Def A.5) is `condPMFOf`. -/

/-- **CR18 Definition A.6, two-variable case.** `X` and `Y` are *statistically
independent* w.r.t. the experiment `p`: the joint law factors as the product of the
marginals, `Pr[X=a ∧ Y=b] = Pr[X=a]·Pr[Y=b]` for all `a, b`. (This is the `n = 2`
instance of `iIndepRV`.) -/
def IndepRV {Ω A B : Type*} (p : ProbDist Ω) (X : RV (Ω := Ω) (A := A))
    (Y : RV (Ω := Ω) (A := B)) : Prop :=
  ∀ a b, p.val.mass (fun ω => X ω = a ∧ Y ω = b)
    = p.val.mass (fun ω => X ω = a) * p.val.mass (fun ω => Y ω = b)

/-- **CR18 Definition A.6, general (list/family) case.** A finite family of random
variables `X i` is *mutually statistically independent* w.r.t. `p` iff every joint
event factors into the product of the marginals:
`Pr[∀ i, Xᵢ = aᵢ] = ∏ᵢ Pr[Xᵢ = aᵢ]`, for every value tuple `a : ∀ i, A i`. The
two-variable `IndepRV` is the `n = 2` instance. This is the faithful statement of
"the URF's outputs at distinct inputs are independent" (CR18 Eq. 3.1). -/
def iIndepRV {Ω : Type*} {ι : Type*} [Fintype ι] {A : ι → Type*}
    (p : ProbDist Ω) (X : ∀ i, RV (Ω := Ω) (A := A i)) : Prop :=
  ∀ a : ∀ i, A i, p.val.mass (fun ω => ∀ i, X i ω = a i)
    = ∏ i, p.val.mass (fun ω => X i ω = a i)

/-- For **independent** `X` and `Y`, conditioning `X` on `Y` returns the marginal:
`Pr[X=a | Y=b] = Pr[X=a]` (when `Pr[Y=b] ≠ 0`). This is the engine behind "a fresh
input gets a uniform output": the new output is independent of the history. -/
theorem condPMFOf_get_of_indep {Ω A B : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B)) (h : IndepRV p X Y) (a : A) (b : B)
    (hb : p.val.mass (fun ω => Y ω = b) ≠ 0) :
    (condPMFOf p X Y a b).get hb = p.val.mass (fun ω => X ω = a) := by
  rw [condPMFOf_apply, h a b, mul_div_assoc, div_self hb, mul_one]

/-! ### Conditional chain rule

The telescoping identity `Pr[⋀ⱼ Aⱼ] = ∏ⱼ Pr[Aⱼ | ⋀_{k<j} Aₖ]` (CR18 Eq. 3.2,
the probabilistic chain rule). The mathematical content is a generic NNReal
telescope; the probability layer only supplies `Pr[⋀_{k<0} Aₖ] = 1`. -/

/-- Pure NNReal telescope: `∏_{j<i+1} P(j+1)/P(j) = P(i+1)` when `P 0 = 1` and
every intermediate `P j` is nonzero. -/
theorem prod_div_eq_of_zero_one (P : ℕ → NNReal) (hP0 : P 0 = 1) :
    ∀ i, (∀ j, j ≤ i → P j ≠ 0) →
      ∏ j ∈ Finset.range (i + 1), P (j + 1) / P j = P (i + 1) := by
  intro i
  induction i with
  | zero => intro _; rw [Finset.prod_range_one, hP0, div_one]
  | succ i ih =>
      intro hpos
      rw [Finset.prod_range_succ, ih (fun j hj => hpos j (Nat.le_succ_of_le hj)),
        ← mul_div_assoc, mul_div_cancel_left₀ _ (hpos (i + 1) (le_refl _))]

/-- Conditional chain rule on a probability distribution (CR18 Eq. 3.2): the mass
of the nested conjunction `⋀_{k<i+1} Aₖ` telescopes into the product of one-step
conditional masses `mass(⋀_{k<j+1} Aₖ) / mass(⋀_{k<j} Aₖ)`. Every conditioning
prefix must have nonzero mass. -/
theorem mass_biForall_lt_eq_prod {Ω : Type*} (p : ProbDist Ω)
    (A : ℕ → Ω → Prop) (i : ℕ)
    (hpos : ∀ j, j ≤ i → p.val.mass (fun ω => ∀ k, k < j → A k ω) ≠ 0) :
    p.val.mass (fun ω => ∀ k, k < i + 1 → A k ω) =
      ∏ j ∈ Finset.range (i + 1),
        p.val.mass (fun ω => ∀ k, k < j + 1 → A k ω) /
          p.val.mass (fun ω => ∀ k, k < j → A k ω) := by
  have hP0 : p.val.mass (fun ω => ∀ k, k < 0 → A k ω) = 1 := by
    have hTrue : (fun ω : Ω => ∀ k, k < 0 → A k ω) = fun _ => True := by
      funext ω; exact eq_true (fun k hk => absurd hk (Nat.not_lt_zero k))
    rw [hTrue, mass_true]; exact p.property
  exact (prod_div_eq_of_zero_one
    (fun m => p.val.mass (fun ω => ∀ k, k < m → A k ω)) hP0 i hpos).symm

/-- The PMF of a coordinate random variable is the corresponding marginal of
the joint PMF. -/
theorem PMF_coord_apply {Ω : Type*} {ι : Type*} {X : ι → Type*}
    [Fintype ι] [∀ i : ι, Fintype (X i)] [∀ i : ι, Nonempty (X i)]
    (p : ProbDist Ω) (Z : RV (Ω := Ω) (A := (i : ι) → X i))
    (j : ι) (xj : X j) :
    PMF p (fun ω => Z ω j) xj = marginalAt (PMF p Z).val j xj := by
  change fTransform (fun ω => Z ω j) p.val xj =
    marginalAt (fTransform Z p.val) j xj
  rw [marginalAt_apply, fTransform_apply_eq_mass, mass_fTransform]

/-- Distribution-level form of `PMF_coord_apply`. -/
theorem PMF_coord_eq_marginalAt {Ω : Type*} {ι : Type*} {X : ι → Type*}
    [Fintype ι] [∀ i : ι, Fintype (X i)] [∀ i : ι, Nonempty (X i)]
    (p : ProbDist Ω) (Z : RV (Ω := Ω) (A := (i : ι) → X i))
    (j : ι) :
    (PMF p (fun ω => Z ω j)).val = marginalAt (PMF p Z).val j := by
  apply Finsupp.ext
  intro xj
  exact PMF_coord_apply p Z j xj

/-! ### Evaluating `fTransform` -/

omit [Nonempty A] [Fintype B] [Nonempty B] in
/-- Fiber-sum form of `fTransform` evaluation.

`(fTransform f X) b` is the total mass of all `a` such that `f a = b`. -/
theorem fTransform_apply_eq_sum
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

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- A pointwise multiplicative lower bound is preserved by pushing both
distributions forward through the same deterministic map. -/
theorem mul_fTransform_le_fTransform_of_forall_mul_le
    (X Y : Dist A) (f : A → B) (c : NNReal)
    (h : ∀ a, c * X a ≤ Y a) (b : B) :
    c * fTransform f X b ≤ fTransform f Y b := by
  rw [fTransform_apply_eq_mass, fTransform_apply_eq_mass]
  unfold mass
  have hX :
      Finsupp.sum X (fun a w => if f a = b then w else 0) =
        ∑ a ∈ X.support ∪ Y.support, if f a = b then X a else 0 := by
    unfold Finsupp.sum
    apply Finset.sum_subset (Finset.subset_union_left)
    intro a _ ha
    have hnot : a ∉ X.support := ha
    by_cases hfb : f a = b
    · simp [hfb, Finsupp.notMem_support_iff.mp hnot]
    · simp [hfb]
  have hY :
      Finsupp.sum Y (fun a w => if f a = b then w else 0) =
        ∑ a ∈ X.support ∪ Y.support, if f a = b then Y a else 0 := by
    unfold Finsupp.sum
    apply Finset.sum_subset (Finset.subset_union_right)
    intro a _ ha
    have hnot : a ∉ Y.support := ha
    by_cases hfb : f a = b
    · simp [hfb, Finsupp.notMem_support_iff.mp hnot]
    · simp [hfb]
  rw [hX, hY]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : f a = b
  · simpa [ha] using h a
  · simp [ha]

/-- Pushforward of a uniform distribution evaluated at a point equals
the fiber cardinality divided by the total cardinality.

`(fTransform f (uniform A)) b = |{a : f a = b}| / |A|` -/
theorem fTransform_uniform_apply
    (f : A → B) (b : B) :
    (fTransform f (uniform A)) b =
      ((Finset.univ.filter (fun a => f a = b)).card : NNReal)
        / (Fintype.card A : NNReal) := by
  classical
  rw [fTransform_apply_eq_sum]
  simp only [uniform_apply, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- If every fiber of `f : A -> B` has the cardinality expected for a uniform
map, pushing the uniform distribution on `A` forward along `f` gives the
uniform distribution on `B`. -/
theorem fTransform_uniform_eq_uniform_of_card_fiber_mul
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (f : A → B)
    (hfiber : ∀ b : B,
      ((Finset.univ.filter (fun a : A => f a = b)).card) * Fintype.card B =
        Fintype.card A) :
    fTransform f (uniform A) = uniform B := by
  classical
  ext b
  rw [fTransform_uniform_apply, uniform_apply]
  let c : NNReal := ((Finset.univ.filter (fun a : A => f a = b)).card : NNReal)
  let d : NNReal := (Fintype.card B : NNReal)
  have hcardA : (Fintype.card A : NNReal) = c * d := by
    dsimp [c, d]
    exact_mod_cast (hfiber b).symm
  have hc_ne : c ≠ 0 := by
    dsimp [c]
    have hfiber_pos : 0 < (Finset.univ.filter (fun a : A => f a = b)).card := by
      by_contra hnot
      have hzero : (Finset.univ.filter (fun a : A => f a = b)).card = 0 := by omega
      have hA_zero : Fintype.card A = 0 := by
        rw [← hfiber b]
        simp [hzero]
      exact (Fintype.card_pos (α := A)).ne' hA_zero
    exact_mod_cast (Nat.ne_of_gt hfiber_pos)
  rw [hcardA]
  simp [NNReal.coe_div]
  have hcr : (c : ℝ) ≠ 0 := by exact_mod_cast hc_ne
  have hdr : (d : ℝ) ≠ 0 := by
    dsimp [d]
    exact_mod_cast (Fintype.card_pos (α := B)).ne'
  field_simp [hcr, hdr]
  simp [c, d]

/-- Summing against a pushforward distribution pulls the summand back. -/
theorem fTransform_sum_mul
    (X : Dist A) (f : A → B) (g : B → NNReal) :
    (∑ b : B, (fTransform f X) b * g b) = ∑ a : A, X a * g (f a) := by
  classical
  simp only [fTransform, Finsupp.sum, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.single_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul]
  trans ∑ x ∈ X.support, X x * g (f x)
  · apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single (f a)]
    · simp
    · intro b _ hb
      simp [hb.symm]
    · intro h
      exact False.elim (h (Finset.mem_univ (f a)))
  · rw [← Finset.sum_subset (Finset.subset_univ X.support)]
    intro a _ ha
    simp [Finsupp.notMem_support_iff.mp ha]

/-- Evaluating a predicate after a pushforward is the same as evaluating the
pulled-back predicate before the pushforward. -/
theorem evalPred_fTransform
    (X : Dist A) (f : A → B) (P : B → Prop) :
    (fTransform f X).evalPred P = X.evalPred (fun a => P (f a)) := by
  classical
  unfold evalPred
  calc
    ∑ b ∈ Finset.univ.filter P, (fTransform f X) b =
        ∑ b : B, (fTransform f X) b * if P b then (1 : NNReal) else 0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro b _
          by_cases h : P b <;> simp [h]
    _ = ∑ a : A, X a * if P (f a) then (1 : NNReal) else 0 := by
          exact fTransform_sum_mul X f (fun b => if P b then (1 : NNReal) else 0)
    _ = ∑ a ∈ Finset.univ.filter (fun a => P (f a)), X a := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro a _
          by_cases h : P (f a) <;> simp [h]

omit [Nonempty B] [Fintype Ω] [Nonempty Ω] [Fintype C] [Nonempty C] in
/-- UPSTREAM-CANDIDATE: uniform pushforward predicate mass bound. -/
theorem evalPred_fTransform_uniform_le
    [DecidableEq B] (f : A → B) (P : B → Prop) [DecidablePred P]
    {d : ℕ} (hd : 0 < d)
    (hcard : d * (Finset.univ.filter (fun a => P (f a))).card ≤ Fintype.card A) :
    (fTransform f (uniform A)).evalPred P ≤ 1 / (d : NNReal) := by
  haveI : Nonempty B := ⟨f (Classical.arbitrary A)⟩
  rw [evalPred_fTransform]
  exact evalPred_uniform_le (fun a => P (f a)) hd hcard

/-! ### Independent product distributions -/

/-- Independent product of two (sub-)distributions.

`prod X Y` is the distribution on `A × B` obtained by sampling `a ~ X` and
`b ~ Y` independently and returning `(a,b)`. The weight is `|X| * |Y|`. -/
def prod (X : Dist A) (Y : Dist B) : Dist (A × B) :=
  X.sum (fun a wa => Y.sum (fun b wb => Finsupp.single (a, b) (wa * wb)))

-- Independent products and `iidPow` are all support-based: no `Fintype`/`Nonempty` on the
-- carriers. (Theorems would otherwise inherit them from the section `variable`s; `omit` sheds them
-- for the whole block, restored at `end` for the `Fintype`-using lemmas below, e.g. `mass_eq_sum`.)
section
omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

theorem prod_apply (X : Dist A) (Y : Dist B) (a : A) (b : B) :
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

/-- The mass of an arbitrary event under an independent product as an iterated
finite-support sum.  The rectangle case is `mass_prod_and`; this unrestricted
form is useful when the event couples the two coordinates. -/
theorem mass_prod_eq_double_sum (X : Dist A) (Y : Dist B) (R : A × B → Prop) :
    (prod X Y).mass R =
      X.sum fun a wa => Y.sum fun b wb => if R (a, b) then wa * wb else 0 := by
  classical
  have key : ∀ p : A × B, prod X Y p = X p.1 * Y p.2 := fun p => prod_apply X Y p.1 p.2
  have hsub : (prod X Y).support ⊆ X.support ×ˢ Y.support := fun p hp =>
    have hne : X p.1 * Y p.2 ≠ 0 := key p ▸ Finsupp.mem_support_iff.mp hp
    Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne),
       Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)⟩
  rw [mass, Finsupp.sum,
    Finset.sum_subset hsub fun p _ hp => by
      rw [show prod X Y p = 0 by simpa using hp]; simp,
    Finset.sum_product]
  simp only [Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [key (a, b)]

/-- Candidate for upstream: integrating an arbitrary event over a product with
the one-point probability distribution is exactly the event mass at the unique
right coordinate. -/
theorem mass_prod_unitProbDist_right (P : Dist A) (R : A × PUnit → Prop) :
    (prod P unitProbDist.val).mass R = P.mass (fun a => R (a, PUnit.unit)) := by
  rw [mass_prod_eq_double_sum]
  unfold mass
  apply Finsupp.sum_congr
  intro a _
  rw [Finsupp.sum]
  rw [Finset.sum_eq_single PUnit.unit]
  · simp [unitProbDist, uniform, Finsupp.equivFunOnFinite]
  · intro b _ hne
    cases b
    exact False.elim (hne rfl)
  · intro hnot
    exact False.elim (hnot (by simp [unitProbDist, uniform, Finsupp.equivFunOnFinite]))

theorem weight_prod (X : Dist A) (Y : Dist B) :
    (prod X Y).weight = X.weight * Y.weight := by
  classical
  -- Support-based, so **no `Fintype` on the carriers**: sum the product mass over the finite
  -- `X.support ×ˢ Y.support` and split the double sum.
  have key : ∀ p : A × B, prod X Y p = X p.1 * Y p.2 := fun p => prod_apply X Y p.1 p.2
  have hsub : (prod X Y).support ⊆ X.support ×ˢ Y.support := fun p hp =>
    have hne : X p.1 * Y p.2 ≠ 0 := key p ▸ Finsupp.mem_support_iff.mp hp
    Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne),
       Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)⟩
  calc (prod X Y).weight
      = ∑ p ∈ X.support ×ˢ Y.support, prod X Y p := by
        rw [weight, Finsupp.sum]
        exact Finset.sum_subset hsub fun p _ hp => by simpa using hp
    _ = ∑ p ∈ X.support ×ˢ Y.support, X p.1 * Y p.2 := Finset.sum_congr rfl fun p _ => key p
    _ = ∑ a ∈ X.support, ∑ b ∈ Y.support, X a * Y b := by rw [Finset.sum_product]
    _ = X.weight * Y.weight := by rw [← Finset.sum_mul_sum]; simp only [weight, Finsupp.sum]

/-- The product of two probability distributions is a probability distribution. -/
theorem prod_isProbDist (X : Dist A) (Y : Dist B)
    (hX : X.isProbDist) (hY : Y.isProbDist) : (prod X Y).isProbDist := by
  rw [isProbDist, weight_prod, hX, hY, mul_one]

/-- The product of two probability distributions, as a `ProbDist` (CR18 Appendix A:
the joint distribution of two **independently selected** random variables). -/
noncomputable def prodProbDist (P : ProbDist A) (Q : ProbDist B) : ProbDist (A × B) :=
  ⟨prod P.val Q.val, prod_isProbDist P.val Q.val P.property Q.property⟩

@[simp] theorem prodProbDist_val (P : ProbDist A) (Q : ProbDist B) :
    (prodProbDist P Q).val = prod P.val Q.val := rfl

/-- CR18 **Definition 4.9** (finite part). The **q-fold i.i.d. power** `X^q` of a distribution:
`q` *independent* copies with *identical* marginal `X`, as one distribution over the `q`-tuples
`Fin q → A`. Its mass is the product of marginals `X^q(f) = ∏ i, X (f i)` — which is exactly
"the copies are independent" (product law) *and* "each has the same marginal `X`" (every factor is
`X`). (Maurer's countable power `⟨X⟩ = X^∞` is deliberately *not* formalized: by fn 24, `X^∞` is
uncountable and leaves the realm of discrete probability. No `Fintype A` is needed — the finite
support carries everything.) -/
noncomputable def iidPow (X : Dist A) (q : ℕ) : Dist (Fin q → A) :=
  Finsupp.onFinset (Fintype.piFinset fun _ => X.support) (fun f => ∏ i, X (f i))
    (fun _ h0 => Fintype.mem_piFinset.mpr fun i =>
      Finsupp.mem_support_iff.mpr fun hi => h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi))

/-- The defining property of `X^q`: its mass is the product of the marginals (independence +
identical marginal `X`). -/
@[simp] theorem iidPow_apply (X : Dist A) (q : ℕ) (f : Fin q → A) :
    iidPow X q f = ∏ i, X (f i) := by rw [iidPow]; exact Finsupp.onFinset_apply

/-- The weight of `X^q` is the `q`-th power of the weight: `|X^q| = |X|^q`. -/
theorem iidPow_weight (X : Dist A) (q : ℕ) : (iidPow X q).weight = X.weight ^ q := by
  have hsub : (iidPow X q).support ⊆ Fintype.piFinset fun _ : Fin q => X.support :=
    fun f hf => Fintype.mem_piFinset.mpr fun i => Finsupp.mem_support_iff.mpr fun hi =>
      (iidPow_apply X q f ▸ Finsupp.mem_support_iff.mp hf) (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hX : ∀ _ : Fin q, ∑ a ∈ X.support, X a = X.weight := fun _ => by rw [weight, Finsupp.sum]
  calc (iidPow X q).weight
      = ∑ f ∈ Fintype.piFinset fun _ : Fin q => X.support, iidPow X q f := by
        rw [weight, Finsupp.sum]
        exact Finset.sum_subset hsub fun f _ hf => by simpa using hf
    _ = ∑ f ∈ Fintype.piFinset fun _ : Fin q => X.support, ∏ i, X (f i) := by simp_rw [iidPow_apply]
    _ = ∏ _i : Fin q, ∑ a ∈ X.support, X a := (Finset.prod_univ_sum _ _).symm
    _ = X.weight ^ q := by
        rw [Finset.prod_congr rfl fun i _ => hX i, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

/-- `X^q` is a probability distribution whenever `X` is (CR18 Def 4.9: `X^q` is again a random
variable) — the n-ary analogue of `prod_isProbDist`. -/
theorem iidPow_isProbDist {X : Dist A} (hX : X.isProbDist) (q : ℕ) : (iidPow X q).isProbDist := by
  rw [isProbDist, iidPow_weight, hX, one_pow]

/-- CR18 **Definition 4.10** (finite part). The **q-fold clone power** `X^[q]` of a distribution:
`q` *clones* `X₁ = ⋯ = X_q` — the *same* value in every coordinate — each with marginal `X`. It is
the pushforward (`fTransform`) of `X` along the **diagonal** `a ↦ (a,…,a)`, hence supported on the
constant tuples with the constant-`a` tuple carrying mass `X a` (`clonePow_apply`). Contrast `iidPow`
(independent copies): clones are *fully correlated*. (Example 4.11: clones of a uniform bit put mass
½ on each of `(0,…,0)` and `(1,…,1)`. The countable version is omitted, as for Def 4.9 fn 24.) -/
def clonePow (X : Dist A) (q : ℕ) : Dist (Fin q → A) :=
  fTransform (fun a _ => a) X

/-- `X^[q]` is supported on constant tuples: its mass at `g` is the `X`-mass of the values whose
clone tuple is `g` (so `0` unless `g` is constant, and `X a` at the constant-`a` tuple). -/
@[simp] theorem clonePow_apply (X : Dist A) (q : ℕ) (g : Fin q → A) :
    clonePow X q g = X.mass (fun a => (fun _ => a) = g) := fTransform_apply_eq_mass _ X g

/-- Cloning preserves total mass: `|X^[q]| = |X|`. -/
theorem clonePow_weight (X : Dist A) (q : ℕ) : (clonePow X q).weight = X.weight :=
  weight_fTransform _ X

/-- `X^[q]` is a probability distribution whenever `X` is. -/
theorem clonePow_isProbDist {X : Dist A} (hX : X.isProbDist) (q : ℕ) : (clonePow X q).isProbDist := by
  rw [isProbDist, clonePow_weight, hX]

end

omit [Nonempty A] in
/-- `mass` as a `Fintype` sum: `X.mass P = ∑ a, (if P a then X a else 0)`. -/
theorem mass_eq_sum (X : Dist A) (P : A → Prop) :
    X.mass P = ∑ a, if P a then X a else 0 := by
  rw [Dist.mass]
  exact Finsupp.sum_fintype _ _ (fun _ => by simp only [ite_self])

/-- Candidate for upstream: event mass is unchanged by replacing a probability
law with its finite-support subtype representation, as long as the event only
depends on the underlying sample. -/
theorem supportProbDist_mass_preimage {A : Type*} (D : ProbDist A)
    (P : A → Prop) :
    (supportProbDist D).val.mass (fun a => P a.1) = D.val.mass P := by
  classical
  rw [mass_eq_sum]
  simp only [supportProbDist_apply]
  unfold mass Finsupp.sum
  exact Finset.sum_attach D.val.support (fun a => if P a then D.val a else 0)

/-- Uniform event mass as a cardinality ratio. -/
theorem uniform_mass_eq_card_filter (P : A → Prop) [DecidablePred P] :
    (uniform A).mass P =
      (((Finset.univ : Finset A).filter P).card : NNReal) /
        (Fintype.card A : NNReal) := by
  rw [mass_eq_sum]
  simp_rw [uniform_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- **The uniform distribution has full support**: an event has nonzero mass iff it
is satisfiable. The engine behind "the conditioning history of a URF has nonzero
probability iff it is realizable by some function" (CR18 Def 3.18 partiality). -/
theorem uniform_mass_ne_zero_iff (P : A → Prop) :
    (uniform A).mass P ≠ 0 ↔ ∃ a, P a := by
  rw [mass_eq_sum, Ne, Finset.sum_eq_zero_iff]
  push Not
  constructor
  · rintro ⟨a, -, ha⟩
    exact ⟨a, by by_contra hPa; simp [hPa] at ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, Finset.mem_univ a, ?_⟩
    rw [if_pos ha, uniform_apply, one_div]
    simp [Fintype.card_ne_zero]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] in
/-- **Independence of the two coordinates of a product distribution**: under
`prod P Q`, the first coordinate and any predicate on the second are independent —
the joint mass factors as the product of the marginals.

`Fintype`-free: summed over the finite support `P.support ×ˢ Q.support`, not the whole type, so it
applies to the `DDS`/`DDE` carriers (which must **not** be `Fintype`). This is what lets the
transcript distribution / Lemma 3.2 (`transcriptDist`) drop its `[Fintype Ω]`. -/
theorem mass_prod_and (P : Dist A) (Q : Dist B) (R₁ : A → Prop) (R₂ : B → Prop) :
    (prod P Q).mass (fun ab => R₁ ab.1 ∧ R₂ ab.2) = P.mass R₁ * Q.mass R₂ := by
  classical
  have key : ∀ p : A × B, prod P Q p = P p.1 * Q p.2 := fun p => prod_apply P Q p.1 p.2
  have hsub : (prod P Q).support ⊆ P.support ×ˢ Q.support := fun p hp =>
    have hne : P p.1 * Q p.2 ≠ 0 := key p ▸ Finsupp.mem_support_iff.mp hp
    Finset.mem_product.mpr
      ⟨Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hne),
       Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)⟩
  have hPmass : P.mass R₁ = ∑ a ∈ P.support, (if R₁ a then P a else 0) := rfl
  have hQmass : Q.mass R₂ = ∑ b ∈ Q.support, (if R₂ b then Q b else 0) := rfl
  have hmass : (prod P Q).mass (fun ab => R₁ ab.1 ∧ R₂ ab.2)
      = ∑ p ∈ (prod P Q).support, (if R₁ p.1 ∧ R₂ p.2 then prod P Q p else 0) := by
    rw [mass, Finsupp.sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : R₁ p.1 ∧ R₂ p.2 <;> simp [h]
  rw [hmass, hPmass, hQmass]
  calc ∑ p ∈ (prod P Q).support, (if R₁ p.1 ∧ R₂ p.2 then prod P Q p else 0)
      = ∑ p ∈ P.support ×ˢ Q.support, (if R₁ p.1 ∧ R₂ p.2 then prod P Q p else 0) := by
        refine Finset.sum_subset hsub fun p _ hp => ?_
        rw [show prod P Q p = 0 by simpa using hp]; simp
    _ = ∑ a ∈ P.support, ∑ b ∈ Q.support, (if R₁ a ∧ R₂ b then P a * Q b else 0) := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [key (a, b)]
    _ = (∑ a ∈ P.support, (if R₁ a then P a else 0))
          * (∑ b ∈ Q.support, (if R₂ b then Q b else 0)) := by
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h1 : R₁ a <;> by_cases h2 : R₂ b <;> simp [h1, h2]

/-- The mass of the singleton event `· = a` is just the weight `X a`. -/
theorem mass_singleton (X : Dist A) (a : A) : X.mass (fun b => b = a) = X a := by
  rw [mass_eq_sum]; simp [Finset.sum_ite_eq']

/-- **CR18 Def A.4 marginal** on the first coordinate of a product distribution:
`P_X(x) = ∑_y P_{XY}(x,y)`, here `(prod P Q).mass (R ∘ fst) = P.mass R · weight Q`. -/
theorem mass_prod_fst (P : Dist A) (Q : Dist B) (R : A → Prop) :
    (prod P Q).mass (fun ab => R ab.1) = P.mass R * Q.weight := by
  rw [show (fun ab : A × B => R ab.1) = (fun ab => R ab.1 ∧ (fun _ : B => True) ab.2) from by
        funext; simp,
     mass_prod_and P Q R (fun _ => True), mass_true]

/-- **CR18 Def A.4 marginal** on the second coordinate of a product distribution. -/
theorem mass_prod_snd (P : Dist A) (Q : Dist B) (R : B → Prop) :
    (prod P Q).mass (fun ab => R ab.2) = P.weight * Q.mass R := by
  rw [show (fun ab : A × B => R ab.2) = (fun ab => (fun _ : A => True) ab.1 ∧ R ab.2) from by
        funext; simp,
     mass_prod_and P Q (fun _ => True) R, mass_true]

/-- **CR18 Def A.6 realized by a product distribution.** The two coordinate
projections of `prodProbDist P Q` are statistically independent — the canonical
source of independence (two **independently selected** coordinates). The joint mass
factors via `mass_prod_and`; the marginals via `mass_prod_fst`/`mass_prod_snd`. -/
theorem indepRV_prodProbDist (P : ProbDist A) (Q : ProbDist B) :
    IndepRV (prodProbDist P Q) (fun ab => ab.1) (fun ab => ab.2) := by
  intro a b
  show (prod P.val Q.val).mass (fun ab => ab.1 = a ∧ ab.2 = b)
    = (prod P.val Q.val).mass (fun ab => ab.1 = a)
      * (prod P.val Q.val).mass (fun ab => ab.2 = b)
  rw [mass_prod_and P.val Q.val (fun u => u = a) (fun v => v = b),
      mass_prod_fst P.val Q.val (fun u => u = a),
      mass_prod_snd P.val Q.val (fun v => v = b),
      show Q.val.weight = 1 from Q.property, show P.val.weight = 1 from P.property,
      mul_one, one_mul]

theorem prod_uniform :
    prod (uniform A) (uniform B) = uniform (A × B) := by
  classical
  ext p
  rcases p with ⟨a, b⟩
  -- Both sides assign constant mass `1/|A| * 1/|B| = 1/|A×B|` to each pair.
  simp [prod_apply, uniform, Fintype.card_prod, div_eq_mul_inv, mul_comm]

-- Basic properties

/-- Weight of the zero distribution is 0. -/
theorem weight_zero : (zero' A).weight = 0 := by
  simp [weight, zero']

omit [Fintype A] [Nonempty A] in
/-- The weight equals the Finsupp.sum with identity.  (`rfl`; needs no `Fintype`/`Nonempty` — those
are section-variable leaks, omitted so callers over arbitrary carriers, e.g. `Dist gs.Game`, can use
it without spurious `Nonempty` obligations.) -/
theorem weight_eq_finsupp_sum (X : Dist A) :
    X.weight = X.sum (fun _ w => w) := by
  rfl

/-- The f-transformation of the uniform distribution through a bijection
is the uniform distribution.

If `f : A → A` is a bijection, then the pushforward of the uniform
distribution through `f` is still uniform: each element receives mass
`1/|A|` because bijectivity means each preimage is a singleton.

This is a core ingredient in OTP-style arguments: if `k` is uniform
and `m ↦ m + k` is a bijection, then `m + k` is uniform. -/
theorem fTransform_bijection_uniform
    (f : A → A) (hf : Function.Bijective f) :
    fTransform f (uniform A) = uniform A := by
  have h_eq : fTransform f (uniform A) = Finsupp.mapDomain f (uniform A) := by
    simp [fTransform, Finsupp.mapDomain]
  rw [h_eq]; ext b
  obtain ⟨a, rfl⟩ := hf.surjective b
  rw [Finsupp.mapDomain_apply hf.injective]
  simp [uniform, Finsupp.equivFunOnFinite]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- Composing two f-transformations equals the f-transformation of the composition.

This is the pushforward functoriality law: `f_*(g_*(X)) = (f ∘ g)_*(X)`. -/
theorem fTransform_comp
    (g : B → C) (f : A → B) (X : Dist A) :
    fTransform g (fTransform f X) = fTransform (g ∘ f) X := by
  show Finsupp.mapDomain g (Finsupp.mapDomain f X) = Finsupp.mapDomain (g ∘ f) X
  rw [Finsupp.mapDomain_comp]

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- UPSTREAM-CANDIDATE: pushing a distribution forward by the identity map
does not change it. -/
@[simp]
theorem fTransform_id {A : Type*} (X : Dist A) :
    fTransform id X = X := by
  ext a
  simpa using fTransform_injective_apply X id Function.injective_id a

omit [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C] in
/-- UPSTREAM-CANDIDATE: adding a deterministic terminal component and then
forgetting it by first projection recovers the original distribution.

This is the distribution-level conservative-extension law used by extended
transcript arguments: constant terminal side information carries no observable
mass once projected away. -/
@[simp]
theorem fTransform_fst_const_pair {A U : Type*} (X : Dist A) (u : U) :
    fTransform (fun p : A × U => p.1) (fTransform (fun a : A => (a, u)) X) = X := by
  rw [fTransform_comp]
  change fTransform id X = X
  exact fTransform_id X

section ProductUniform

variable {A' B' : Type*}
variable [Fintype A'] [Nonempty A'] [Fintype B'] [Nonempty B']

/-- An equivalence pushes the uniform distribution to uniform.

Generalizes `fTransform_bijection_uniform` to maps between different types:
if `e : A ≃ B` is an equivalence, then the pushforward of `uniform A`
through `e` is `uniform B`. -/
theorem fTransform_equiv_uniform (e : A' ≃ B') :
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

variable (A' B')

/-- Projecting a uniform product distribution to the first component gives uniform.

If `(a, b)` is drawn uniformly from `A × B`, then `a` alone is uniform over `A`.
This is the discrete marginal-of-uniform-is-uniform fact. -/
theorem fTransform_fst_uniform :
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
theorem fTransform_snd_uniform :
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

/-- UPSTREAM-CANDIDATE: mapping a function of the second coordinate over an
independent uniform product is the same as mapping it over the second uniform
marginal. -/
theorem fTransform_map_snd_prod_uniform {C' : Type*} (f : B' → C') :
    fTransform (fun p : A' × B' => f p.2)
        (prod (uniform A') (uniform B')) =
      fTransform f (uniform B') := by
  rw [prod_uniform]
  change fTransform (f ∘ (Prod.snd : A' × B' → B')) (uniform (A' × B')) =
    fTransform f (uniform B')
  rw [← fTransform_comp]
  rw [fTransform_snd_uniform]

/-- UPSTREAM-CANDIDATE: function-valued form of
`fTransform_map_snd_prod_uniform`, useful for fixed-query output-vector laws. -/
theorem fTransform_map_snd_prod_uniform_pi {ι C' : Type*} (f : B' → ι → C') :
    fTransform (fun p : A' × B' => fun i : ι => f p.2 i)
        (prod (uniform A') (uniform B')) =
      fTransform (fun b : B' => fun i : ι => f b i) (uniform B') := by
  exact fTransform_map_snd_prod_uniform
    (A' := A') (B' := B') (f := fun b : B' => fun i : ι => f b i)

omit [Fintype B'] [Nonempty B'] in
/-- UPSTREAM-CANDIDATE: fixed-query output-vector form of
`fTransform_map_snd_prod_uniform`, where the second uniform coordinate is a
function sampled independently of an ignored first coordinate. -/
theorem fTransform_eval_snd_prod_uniform {D' ι C' : Type*}
    [Fintype (D' → C')] [Nonempty (D' → C')] (xs : ι → D') :
    fTransform
        (fun p : A' × (D' → C') => fun i : ι => p.2 (xs i))
        (prod (uniform A') (uniform (D' → C'))) =
      fTransform
        (fun f : D' → C' => fun i : ι => f (xs i))
        (uniform (D' → C')) := by
  exact fTransform_map_snd_prod_uniform
    (A' := A') (B' := D' → C')
    (f := fun f : D' → C' => fun i : ι => f (xs i))

omit [Fintype B'] [Nonempty B'] in
/-- UPSTREAM-CANDIDATE: projecting an extended fixed-query output-vector law
`(output, side)` drops the independent side coordinate when the output depends
only on the sampled function coordinate. -/
theorem fTransform_fst_pair_eval_snd_prod_uniform {D' ι C' : Type*}
    [Fintype (D' → C')] [Nonempty (D' → C')] (xs : ι → D') :
    fTransform Prod.fst
        (fTransform
          (fun p : A' × (D' → C') => (fun i : ι => p.2 (xs i), p.1))
          (prod (uniform A') (uniform (D' → C')))) =
      fTransform
        (fun f : D' → C' => fun i : ι => f (xs i))
        (uniform (D' → C')) := by
  rw [fTransform_comp]
  change fTransform
      (fun p : A' × (D' → C') => fun i : ι => p.2 (xs i))
      (prod (uniform A') (uniform (D' → C'))) =
    fTransform
      (fun f : D' → C' => fun i : ι => f (xs i))
      (uniform (D' → C'))
  rw [fTransform_eval_snd_prod_uniform]

end ProductUniform

end Dist

end RandomSystems
