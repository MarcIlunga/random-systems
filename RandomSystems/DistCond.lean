/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist

/-!
# Conditional probability and independence (tower level L1, `DESIGN.md` §12)

`RandomSystems.Dist` carries conditioning (`Dist.cond`, `Dist.condPMF`,
`Dist.condPMFOf`) and two independence notions (`Dist.IndepRV`,
`Dist.iIndepRV`) but none of the *laws* every source uses.  This module adds
them:

* **the multiplication rule** `X(P ∧ Q) = X(P | Q)·X(Q)` (`condProb_mul_mass`);
* **Bayes' rule** (`condProb_eq_condProb_mul_mass_div_mass`, and its
  division-free form `condProb_mul_mass_eq_condProb_mul_mass`);
* **the law of total probability** over a finite partition
  (`mass_eq_sum_mass_and`, `mass_eq_sum_condProb_mul_mass`, and the
  complement form `mass_eq_condProb_mul_mass_add_condProb_mul_mass_not`);
* **the chain rule** — the event form (`mass_biForall_lt_eq_prod_condProb`),
  the input/output-interleaved form of a random-system transcript
  (`mass_biForall_lt_eq_prod_condProb_mul_condProb`) and the conditional form
  `p_{Y^n|X^n} = ∏_j p_{Y_j | X^j Y^{j-1}}` of MPR07 eq. (1)
  (`condProb_biForall_lt_eq_prod_condProb`);
* **conditional independence** (`CondIndepRV`), **independence on a finite
  index set** (`iIndepRVOn`), **`k`-wise independence** (`kIndepRV`) and
  **pairwise independence** (`PairwiseIndepRV`), with the bridges between them
  and to the existing `iIndepRV`.

## Total conditioning, and why (`Dist.cond` is `Part`-valued)

`Dist.cond X P Q : Part ℝ` is undefined exactly on the null conditioning
event.  A `Part`-valued factor cannot appear under a `∏` — the body of a
`Finset.prod` may not depend on the membership proof that would discharge its
domain — which is why `Dist.mass_biForall_lt_eq_prod` spells its chain rule
with a raw quotient of masses, and pays for it with a positivity hypothesis on
every prefix.  `Dist.condProb` is that quotient, named: a *total* operation
whose value on a null conditioning event is `0` (Lean's `x / 0 = 0`), matching
mathlib's total `ProbabilityTheory.cond` (`μ[|s] = (μ s)⁻¹ • μ.restrict s`,
junk when `μ s ∈ {0, ∞}`).  `condProb_eq_cond_get` identifies the two wherever
`Dist.cond` is defined, so no convention is forked; and because
`X(P ∧ Q) = 0` whenever `X(Q) = 0` on a non-negative distribution, the
multiplication rule and *both* chain rules hold with **no** positivity
hypothesis at all — strictly stronger than the `Part`-shaped statements.

## Hypothesis discipline (`DESIGN.md` §12)

Each statement carries the weakest of signed / `Dist.NonNeg` /
`Dist.isProbDist` at which it is true:

* **signed**: the multiplication rule *given* `X(Q) ≠ 0`, Bayes' rule given
  `X(P) ≠ 0`, the partition form of total probability, and the marginalization
  identity `mass_forall_mem_erase_eq_sum`;
* **`NonNeg`**: the hypothesis-free multiplication rule and the
  hypothesis-free forms of Bayes and of total probability — non-negativity is
  exactly what makes a null conditioning event harmless, since `mass_mono`
  then forces `X(P ∧ Q) = 0` there;
* **`isProbDist`**: the chain rules, whose base case is `X(True) = 1`, and
  everything stated for `ProbDist`-indexed random variables.

## Sources

Maurer–Pietrzak–Renner, *Indistinguishability Amplification* (CRYPTO 2007),
eq. (1); Maurer–Pietrzak, *Composition of Random Systems* (TCC 2004) §2.1;
Cramer–Renner, *Cryptography — Lecture Notes* (2018), Appendix A (Def. A.4–A.6)
and §6.1.2.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems

namespace Dist

/-! ## Total conditional probability -/

/-- Conditional probability of `P` given `Q`, as a **total** real-valued
operation: `X(P ∧ Q) / X(Q)`, with Lean's `x / 0 = 0` supplying the value on a
null conditioning event.

This is the value of the `Part`-valued `Dist.cond` wherever that is defined
(`condProb_eq_cond_get`); the total form is the one that can appear under a `∏`
(see the chain rules below), and it mirrors mathlib's total
`ProbabilityTheory.cond`. -/
def condProb {A : Type*} (X : Dist A) (P Q : A → Prop) : ℝ :=
  X.mass (fun a => P a ∧ Q a) / X.mass Q

/-- `Dist.cond` is defined exactly off the null conditioning event. -/
theorem cond_dom_iff {A : Type*} (X : Dist A) (P Q : A → Prop) :
    (X.cond P Q).Dom ↔ X.mass Q ≠ 0 := Iff.rfl

/-- The total `condProb` agrees with the partial `Dist.cond` wherever the
latter is defined. -/
theorem condProb_eq_cond_get {A : Type*} (X : Dist A) (P Q : A → Prop)
    (h : (X.cond P Q).Dom) :
    X.condProb P Q = (X.cond P Q).get h := rfl

/-- On a null conditioning event the total conditional probability is `0`. -/
@[simp]
theorem condProb_of_mass_eq_zero {A : Type*} (X : Dist A) (P Q : A → Prop)
    (hQ : X.mass Q = 0) : X.condProb P Q = 0 := by
  simp [condProb, hQ]

/-- Conditional probability under a non-negative distribution is non-negative.
`NonNeg` layer. -/
theorem condProb_nonneg {A : Type*} {X : Dist A} (hX : X.NonNeg) (P Q : A → Prop) :
    0 ≤ X.condProb P Q :=
  div_nonneg (hX.mass_nonneg _) (hX.mass_nonneg _)

/-- Conditional probability under a non-negative distribution is at most one —
including on a null conditioning event, where it is `0`.  `NonNeg` layer. -/
theorem condProb_le_one {A : Type*} {X : Dist A} (hX : X.NonNeg) (P Q : A → Prop) :
    X.condProb P Q ≤ 1 := by
  rcases eq_or_lt_of_le (hX.mass_nonneg Q) with h | h
  · simp [condProb, ← h]
  · exact (div_le_one h).mpr (mass_mono hX fun a ha => ha.2)

/-! ## The multiplication rule and Bayes' rule -/

/-- **Multiplication rule**, signed layer: `X(P | Q)·X(Q) = X(P ∧ Q)` whenever
the conditioning event is not null.  (mathlib: `cond_mul_eq_inter`.) -/
theorem condProb_mul_mass_of_ne_zero {A : Type*} (X : Dist A) (P Q : A → Prop)
    (hQ : X.mass Q ≠ 0) :
    X.condProb P Q * X.mass Q = X.mass (fun a => P a ∧ Q a) :=
  div_mul_cancel₀ _ hQ

/-- **Multiplication rule**, `NonNeg` layer: `X(P | Q)·X(Q) = X(P ∧ Q)` with
*no* side condition.  On a null conditioning event both sides vanish, because
`X(P ∧ Q) ≤ X(Q) = 0` and `X(P ∧ Q) ≥ 0`.  This hypothesis-freedom is what
propagates into the chain rules below. -/
theorem condProb_mul_mass {A : Type*} {X : Dist A} (hX : X.NonNeg) (P Q : A → Prop) :
    X.condProb P Q * X.mass Q = X.mass (fun a => P a ∧ Q a) := by
  by_cases hQ : X.mass Q = 0
  · have h0 : X.mass (fun a => P a ∧ Q a) = 0 :=
      le_antisymm (hQ ▸ mass_mono hX fun a ha => ha.2) (hX.mass_nonneg _)
    simp [condProb, hQ, h0]
  · exact condProb_mul_mass_of_ne_zero X P Q hQ

/-- **Bayes' rule**, signed layer: `X(P | Q) = X(Q | P)·X(P) / X(Q)`, valid as
soon as the *hypothesis* event `P` is not null.  (mathlib:
`ProbabilityTheory.cond_eq_inv_mul_cond_mul`.) -/
theorem condProb_eq_condProb_mul_mass_div_mass {A : Type*} (X : Dist A)
    (P Q : A → Prop) (hP : X.mass P ≠ 0) :
    X.condProb P Q = X.condProb Q P * X.mass P / X.mass Q := by
  rw [condProb_mul_mass_of_ne_zero X Q P hP,
    mass_congr X (P := fun a => Q a ∧ P a) (Q := fun a => P a ∧ Q a) (fun _ => and_comm)]
  rfl

/-- **Bayes' rule, division-free**, `NonNeg` layer:
`X(P | Q)·X(Q) = X(Q | P)·X(P)`, with no side condition — both sides are
`X(P ∧ Q)`. -/
theorem condProb_mul_mass_eq_condProb_mul_mass {A : Type*} {X : Dist A}
    (hX : X.NonNeg) (P Q : A → Prop) :
    X.condProb P Q * X.mass Q = X.condProb Q P * X.mass P := by
  rw [condProb_mul_mass hX, condProb_mul_mass hX]
  exact mass_congr X fun _ => and_comm

/-! ## The law of total probability -/

/-- **Law of total probability, partition form.**  Signed layer: over a finite
pairwise-disjoint family of events covering the sample space, every event mass
splits as the sum of its intersections with the blocks.  The disjointness and
covering conventions are those of
`Dist.sum_mass_eq_weight_of_pairwise_disjoint_of_cover`. -/
theorem mass_eq_sum_mass_and {A ι : Type*} [Fintype ι] (X : Dist A) (P : A → Prop)
    (B : ι → A → Prop) (hdisj : ∀ i j, i ≠ j → ∀ a, B i a → B j a → False)
    (hcover : ∀ a, ∃ i, B i a) :
    X.mass P = ∑ i, X.mass (fun a => P a ∧ B i a) := by
  have h := sum_mass_eq_weight_of_pairwise_disjoint_of_cover (X.restrict P) B hdisj hcover
  rw [weight_restrict] at h
  rw [← h]
  exact Finset.sum_congr rfl fun i _ => by
    rw [mass_restrict]
    exact mass_congr X fun _ => and_comm

/-- **Law of total probability**, `NonNeg` layer: `X(P) = ∑ᵢ X(P | Bᵢ)·X(Bᵢ)`
over a finite partition, with no positivity hypothesis on the blocks — a null
block contributes `0`. -/
theorem mass_eq_sum_condProb_mul_mass {A ι : Type*} [Fintype ι] {X : Dist A}
    (hX : X.NonNeg) (P : A → Prop) (B : ι → A → Prop)
    (hdisj : ∀ i j, i ≠ j → ∀ a, B i a → B j a → False) (hcover : ∀ a, ∃ i, B i a) :
    X.mass P = ∑ i, X.condProb P (B i) * X.mass (B i) := by
  rw [mass_eq_sum_mass_and X P B hdisj hcover]
  exact Finset.sum_congr rfl fun i _ => (condProb_mul_mass hX P (B i)).symm

/-- **Law of total probability, two-block form**:
`X(P) = X(P|Q)·X(Q) + X(P|¬Q)·X(¬Q)`.  `NonNeg` layer.  (mathlib:
`ProbabilityTheory.cond_add_cond_compl_eq`.) -/
theorem mass_eq_condProb_mul_mass_add_condProb_mul_mass_not {A : Type*} {X : Dist A}
    (hX : X.NonNeg) (P Q : A → Prop) :
    X.mass P = X.condProb P Q * X.mass Q
      + X.condProb P (fun a => ¬ Q a) * X.mass (fun a => ¬ Q a) := by
  rw [condProb_mul_mass hX, condProb_mul_mass hX,
    mass_congr X (P := fun a => P a ∧ Q a) (Q := fun a => Q a ∧ P a) (fun _ => and_comm),
    mass_congr X (P := fun a => P a ∧ ¬ Q a) (Q := fun a => ¬ Q a ∧ P a) (fun _ => and_comm),
    ← mass_restrict X Q P, ← mass_restrict X (fun a => ¬ Q a) P,
    mass_add_compl (X.restrict P) Q, weight_restrict]

/-! ## The chain rule -/

/-- **Chain rule, event form** (CR18 eq. 3.2): the mass of a nested
conjunction is the product of the one-step conditional probabilities,

`X(⋀_{k<n} Eₖ) = ∏_{j<n} X(Eⱼ | ⋀_{k<j} Eₖ)`.

`isProbDist` layer — `NonNeg` for the multiplication rule, `weight = 1` for
the empty prefix.  Unlike `Dist.mass_biForall_lt_eq_prod`, which spells the
factors as raw quotients, this form needs **no** positivity hypothesis on the
prefixes: a null prefix makes both sides `0`. -/
theorem mass_biForall_lt_eq_prod_condProb {A : Type*} {X : Dist A}
    (hX : X.isProbDist) (E : ℕ → A → Prop) (n : ℕ) :
    X.mass (fun a => ∀ k, k < n → E k a)
      = ∏ j ∈ Finset.range n, X.condProb (E j) (fun a => ∀ k, k < j → E k a) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_zero, mass_congr X (Q := fun _ => True) (fun a => by simp),
        mass_true]
      exact hX.weight_eq
  | succ n ih =>
      rw [Finset.prod_range_succ, ← ih, mul_comm, condProb_mul_mass hX.nonNeg]
      refine mass_congr X fun a => ⟨fun h => ⟨h n (Nat.lt_succ_self n),
        fun k hk => h k (Nat.lt_succ_of_lt hk)⟩, ?_⟩
      rintro ⟨hn, h⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
      · exact h k hk'
      · exact hn

/-- **Chain rule for a random-system transcript** (MauPie04 §2.1): the
probability of an input/output transcript factors into the alternating product
of one-step conditional probabilities,

`Pr[X^n = x^n, Y^n = y^n]
  = ∏_{j<n} Pr[Xⱼ = xⱼ | X^{j-1}Y^{j-1}] · Pr[Yⱼ = yⱼ | X^jY^{j-1}]`.

The `Y`-factors are the system's own conditional distributions
`p^S_{Yⱼ|X^jY^{j-1}}`; the `X`-factors belong to whatever chooses the inputs.
No positivity hypothesis (see `condProb_mul_mass`).  The prefix convention is
that of `Dist.mass_biForall_lt_eq_prod`; the current input is written *first*
in the `Y`-factor's conditioning event, so that the two applications of the
multiplication rule compose without reassociating. -/
theorem mass_biForall_lt_eq_prod_condProb_mul_condProb {Ω 𝒳 𝒴 : Type*}
    (p : ProbDist Ω) (Xv : ℕ → RV (Ω := Ω) (A := 𝒳)) (Yv : ℕ → RV (Ω := Ω) (A := 𝒴))
    (x : ℕ → 𝒳) (y : ℕ → 𝒴) (n : ℕ) :
    p.val.mass (fun ω => ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)
      = ∏ j ∈ Finset.range n,
          p.val.condProb (fun ω => Xv j ω = x j)
              (fun ω => ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k)
            * p.val.condProb (fun ω => Yv j ω = y j)
              (fun ω => Xv j ω = x j ∧ ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k) := by
  induction n with
  | zero =>
      rw [Finset.prod_range_zero,
        mass_congr p.val (Q := fun _ => True) (fun ω => by simp), mass_true]
      exact p.property.weight_eq
  | succ n ih =>
      have hstep : p.val.mass (fun ω => ∀ k, k < n + 1 → Xv k ω = x k ∧ Yv k ω = y k)
          = p.val.condProb (fun ω => Yv n ω = y n)
                (fun ω => Xv n ω = x n ∧ ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)
              * (p.val.condProb (fun ω => Xv n ω = x n)
                  (fun ω => ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)
                * p.val.mass (fun ω => ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)) := by
        rw [condProb_mul_mass p.property.nonNeg, condProb_mul_mass p.property.nonNeg]
        refine mass_congr p.val fun ω => ⟨fun h => ⟨(h n (Nat.lt_succ_self n)).2,
          (h n (Nat.lt_succ_self n)).1, fun k hk => h k (Nat.lt_succ_of_lt hk)⟩, ?_⟩
        rintro ⟨hy, hx, h⟩ k hk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
        · exact h k hk'
        · exact ⟨hx, hy⟩
      rw [Finset.prod_range_succ, ← ih, hstep]
      ring

/-- **The defining identity of a random system** (MPR07 eq. (1)):

`p_{Y^n|X^n}(y^n, x^n) = ∏_{j<n} p_{Yⱼ|X^jY^{j-1}}(yⱼ, x^j y^{j-1})`.

The identity is *not* unconditional in a general random experiment: dividing
the transcript chain rule
(`mass_biForall_lt_eq_prod_condProb_mul_condProb`) by the input chain rule
cancels the input factors only under `hfree`, which says the `j`-th input is
chosen without feedback from the past outputs.  That is exactly the regime in
which Maurer's `p^S_{Y^i|X^i}` is a property of the system alone.  `hx` says
the conditioning input transcript is possible; without it the left-hand side is
the junk value `0`. -/
theorem condProb_biForall_lt_eq_prod_condProb {Ω 𝒳 𝒴 : Type*}
    (p : ProbDist Ω) (Xv : ℕ → RV (Ω := Ω) (A := 𝒳)) (Yv : ℕ → RV (Ω := Ω) (A := 𝒴))
    (x : ℕ → 𝒳) (y : ℕ → 𝒴) (n : ℕ)
    (hfree : ∀ j ∈ Finset.range n,
      p.val.condProb (fun ω => Xv j ω = x j)
          (fun ω => ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k)
        = p.val.condProb (fun ω => Xv j ω = x j) (fun ω => ∀ k, k < j → Xv k ω = x k))
    (hx : p.val.mass (fun ω => ∀ k, k < n → Xv k ω = x k) ≠ 0) :
    p.val.condProb (fun ω => ∀ k, k < n → Yv k ω = y k)
        (fun ω => ∀ k, k < n → Xv k ω = x k)
      = ∏ j ∈ Finset.range n,
          p.val.condProb (fun ω => Yv j ω = y j)
            (fun ω => Xv j ω = x j ∧ ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k) := by
  have hjoint :
      p.val.mass (fun ω => (∀ k, k < n → Yv k ω = y k) ∧ ∀ k, k < n → Xv k ω = x k)
        = p.val.mass (fun ω => ∀ k, k < n → Xv k ω = x k)
          * ∏ j ∈ Finset.range n,
              p.val.condProb (fun ω => Yv j ω = y j)
                (fun ω => Xv j ω = x j ∧ ∀ k, k < j → Xv k ω = x k ∧ Yv k ω = y k) := by
    rw [mass_congr p.val (Q := fun ω => ∀ k, k < n → Xv k ω = x k ∧ Yv k ω = y k)
        (fun ω => ⟨fun h k hk => ⟨h.2 k hk, h.1 k hk⟩,
          fun h => ⟨fun k hk => (h k hk).2, fun k hk => (h k hk).1⟩⟩),
      mass_biForall_lt_eq_prod_condProb_mul_condProb p Xv Yv x y n,
      Finset.prod_mul_distrib, Finset.prod_congr rfl hfree,
      ← mass_biForall_lt_eq_prod_condProb p.property (fun k ω => Xv k ω = x k) n]
  rw [condProb, hjoint, mul_comm, mul_div_assoc, div_self hx, mul_one]

/-! ## Conditional independence -/

/-- **Conditional independence** of two random variables given a third:
`Pr[X = a ∧ Y = b | Z = c] = Pr[X = a | Z = c]·Pr[Y = b | Z = c]` for all
values.  Stated with the total `condProb`, so no positivity hypothesis on the
conditioning event is needed: on a null `Z = c` all three factors are `0`.
(mathlib's measure-theoretic counterpart is
`ProbabilityTheory.CondIndepFun`.) -/
def CondIndepRV {Ω A B C : Type*} (p : ProbDist Ω) (X : RV (Ω := Ω) (A := A))
    (Y : RV (Ω := Ω) (A := B)) (Z : RV (Ω := Ω) (A := C)) : Prop :=
  ∀ a b c, p.val.condProb (fun ω => X ω = a ∧ Y ω = b) (fun ω => Z ω = c)
    = p.val.condProb (fun ω => X ω = a) (fun ω => Z ω = c)
      * p.val.condProb (fun ω => Y ω = b) (fun ω => Z ω = c)

/-- **Division-free characterization of conditional independence**:
`Pr[X=a ∧ Y=b ∧ Z=c]·Pr[Z=c] = Pr[X=a ∧ Z=c]·Pr[Y=b ∧ Z=c]`.  This is the
form to check in applications — it never divides — and it is *equivalent* to
`CondIndepRV`, null conditioning included, because there all the masses
involved vanish. -/
theorem condIndepRV_iff_mass_mul_mass {Ω A B C : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B)) (Z : RV (Ω := Ω) (A := C)) :
    CondIndepRV p X Y Z ↔ ∀ a b c,
      p.val.mass (fun ω => (X ω = a ∧ Y ω = b) ∧ Z ω = c)
          * p.val.mass (fun ω => Z ω = c)
        = p.val.mass (fun ω => X ω = a ∧ Z ω = c)
          * p.val.mass (fun ω => Y ω = b ∧ Z ω = c) := by
  constructor
  · intro h a b c
    rw [← condProb_mul_mass p.property.nonNeg (fun ω => X ω = a ∧ Y ω = b)
        (fun ω => Z ω = c),
      ← condProb_mul_mass p.property.nonNeg (fun ω => X ω = a) (fun ω => Z ω = c),
      ← condProb_mul_mass p.property.nonNeg (fun ω => Y ω = b) (fun ω => Z ω = c),
      h a b c]
    ring
  · intro h a b c
    rcases eq_or_ne (p.val.mass fun ω => Z ω = c) 0 with h0 | h0
    · simp [condProb, h0]
    · rw [condProb, condProb, condProb, div_mul_div_comm, ← h a b c,
        mul_div_mul_right _ _ h0]

/-- **Conditioning on nothing is not conditioning**: conditional independence
given a constant random variable is ordinary independence.  The anchor that
pins `CondIndepRV` to `Dist.IndepRV`. -/
theorem condIndepRV_unit_iff_indepRV {Ω A B : Type*} (p : ProbDist Ω)
    (X : RV (Ω := Ω) (A := A)) (Y : RV (Ω := Ω) (A := B)) :
    CondIndepRV p X Y (fun _ => PUnit.unit) ↔ IndepRV p X Y := by
  have hcp : ∀ (P : Ω → Prop) (c : PUnit),
      p.val.condProb P (fun _ => (PUnit.unit : PUnit) = c) = p.val.mass P := by
    intro P c
    have hone : p.val.mass (fun _ => (PUnit.unit : PUnit) = c) = 1 := by
      rw [mass_congr p.val (Q := fun _ => True) (fun _ => by simp), mass_true]
      exact p.property.weight_eq
    rw [condProb, hone, div_one]
    exact mass_congr p.val fun _ => by simp
  constructor
  · intro h a b
    have hab := h a b PUnit.unit
    rwa [hcp, hcp, hcp] at hab
  · intro h a b _
    rw [hcp, hcp, hcp]
    exact h a b

/-! ## Independence on a finite index set; `k`-wise and pairwise independence -/

/-- **Independence of the family `X` on a finite index set `s`**: the joint law
of the coordinates in `s` factors into their marginals,
`Pr[∀ i ∈ s, Xᵢ = aᵢ] = ∏_{i ∈ s} Pr[Xᵢ = aᵢ]`.

This is the `Finset`-graded form of `Dist.iIndepRV`, which states only the
full-tuple case.  It is the form `k`-wise independence needs: below the full
index set there is no full-tuple statement to grade. -/
def iIndepRVOn {Ω ι : Type*} {A : ι → Type*} (s : Finset ι) (p : ProbDist Ω)
    (X : ∀ i, RV (Ω := Ω) (A := A i)) : Prop :=
  ∀ a : ∀ i, A i, p.val.mass (fun ω => ∀ i ∈ s, X i ω = a i)
    = ∏ i ∈ s, p.val.mass (fun ω => X i ω = a i)

/-- **`k`-wise independence** (CR18 §6.1.2): every at-most-`k`-element
sub-family has a factoring joint law.  `kIndepRV (Fintype.card ι)` is mutual
independence (`kIndepRV_card_iff_iIndepRV`) and `kIndepRV 2` is pairwise
independence (`kIndepRV_two_iff_pairwiseIndepRV`). -/
def kIndepRV {Ω ι : Type*} {A : ι → Type*} (k : ℕ) (p : ProbDist Ω)
    (X : ∀ i, RV (Ω := Ω) (A := A i)) : Prop :=
  ∀ s : Finset ι, s.card ≤ k → iIndepRVOn s p X

/-- **Pairwise independence**: any two distinct members of the family are
independent.  Strictly weaker than `Dist.iIndepRV`, and already enough for
additivity of variance (`Dist.variance_sum_of_pairwiseIndepRV` in
`RandomSystems.DistIndepMeasure`). -/
def PairwiseIndepRV {Ω ι : Type*} {A : ι → Type*} (p : ProbDist Ω)
    (X : ∀ i, RV (Ω := Ω) (A := A i)) : Prop :=
  Pairwise fun i j => IndepRV p (X i) (X j)

/-- Independence on the full index set of a `Fintype` is exactly the tree's
`Dist.iIndepRV`. -/
theorem iIndepRVOn_univ_iff_iIndepRV {Ω ι : Type*} [Fintype ι] {A : ι → Type*}
    (p : ProbDist Ω) (X : ∀ i, RV (Ω := Ω) (A := A i)) :
    iIndepRVOn Finset.univ p X ↔ iIndepRV p X := by
  simp [iIndepRVOn, iIndepRV]

/-- A sample space carrying a probability distribution is nonempty. -/
theorem nonempty_of_isProbDist {Ω : Type*} {D : Dist Ω} (hD : D.isProbDist) :
    Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h0 : D.weight = 0 := Finset.sum_eq_zero fun a _ => isEmptyElim a
  rw [hD.weight_eq] at h0
  exact one_ne_zero h0

/-- **Marginalization.**  Signed layer: summing the joint over all values of a
single coordinate `j ∈ t` deletes that coordinate from the conjunction.  This
is the law of total probability for the partition of the sample space by the
value of `X j`, and it is the engine behind every "independence descends to
sub-families" statement below. -/
theorem mass_forall_mem_erase_eq_sum {Ω ι : Type*} {A : ι → Type*} [DecidableEq ι]
    (D : Dist Ω) (X : ∀ i, RV (Ω := Ω) (A := A i)) (t : Finset ι) {j : ι}
    [Fintype (A j)] (hj : j ∈ t) (a : ∀ i, A i) :
    D.mass (fun ω => ∀ i ∈ t.erase j, X i ω = a i)
      = ∑ v : A j, D.mass (fun ω => ∀ i ∈ t, X i ω = Function.update a j v i) := by
  rw [mass_eq_sum_mass_and D (fun ω => ∀ i ∈ t.erase j, X i ω = a i)
    (fun v ω => X j ω = v) (fun v v' hvv' ω hv hv' => hvv' (hv ▸ hv'))
    (fun ω => ⟨X j ω, rfl⟩)]
  refine Finset.sum_congr rfl fun v _ => mass_congr D fun ω => ⟨?_, ?_⟩
  · rintro ⟨hrest, hjv⟩ i hi
    rcases eq_or_ne i j with rfl | hij
    · rw [Function.update_self]; exact hjv
    · rw [Function.update_of_ne hij]
      exact hrest i (Finset.mem_erase.mpr ⟨hij, hi⟩)
  · intro h
    refine ⟨fun i hi => ?_, ?_⟩
    · have hij := (Finset.mem_erase.mp hi).1
      rw [← Function.update_of_ne hij v a]
      exact h i (Finset.mem_erase.mp hi).2
    · rw [← Function.update_self j v a]
      exact h j hj

/-- A predicate on finite sets that survives deleting a single element
survives passing to an arbitrary subset.

UPSTREAM-CANDIDATE: pure `Finset` combinatorics, independent of everything in
this library. -/
theorem _root_.Finset.forall_subset_of_forall_erase {ι : Type*} [DecidableEq ι]
    {P : Finset ι → Prop} (hstep : ∀ (t : Finset ι) (j : ι), j ∈ t → P t → P (t.erase j))
    {s t : Finset ι} (hst : s ⊆ t) (ht : P t) : P s := by
  have key : ∀ n (t s : Finset ι), t.card = n → s ⊆ t → P t → P s := by
    intro n
    induction n with
    | zero =>
        intro t s htc hs hP
        obtain rfl : t = ∅ := Finset.card_eq_zero.mp htc
        obtain rfl : s = ∅ := Finset.subset_empty.mp hs
        exact hP
    | succ n ih =>
        intro t s htc hs hP
        by_cases hts : s = t
        · subst hts; exact hP
        · obtain ⟨j, hjt, hjs⟩ :=
            Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hs, hts⟩)
          refine ih (t.erase j) s ?_ (Finset.subset_erase.mpr ⟨hs, hjs⟩) (hstep t j hjt hP)
          rw [Finset.card_erase_of_mem hjt, htc]
          omega
  exact key t.card t s rfl hst ht

/-- Independence on a finite index set survives deleting an index. -/
theorem iIndepRVOn.erase {Ω ι : Type*} {A : ι → Type*} [DecidableEq ι]
    [∀ i, Fintype (A i)] {p : ProbDist Ω} {X : ∀ i, RV (Ω := Ω) (A := A i)}
    {t : Finset ι} {j : ι} (hj : j ∈ t) (h : iIndepRVOn t p X) :
    iIndepRVOn (t.erase j) p X := by
  intro a
  rw [mass_forall_mem_erase_eq_sum p.val X t hj a]
  have hstep : ∀ v : A j,
      p.val.mass (fun ω => ∀ i ∈ t, X i ω = Function.update a j v i)
        = p.val.mass (fun ω => X j ω = v)
          * ∏ i ∈ t.erase j, p.val.mass (fun ω => X i ω = a i) := by
    intro v
    rw [h (Function.update a j v), ← Finset.mul_prod_erase t _ hj, Function.update_self]
    exact congrArg _ (Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hi).1])
  rw [Finset.sum_congr rfl (fun v _ => hstep v), ← Finset.sum_mul,
    sum_mass_eq_weight_of_pairwise_disjoint_of_cover p.val (fun v ω => X j ω = v)
      (fun v v' hvv' ω hv hv' => hvv' (hv ▸ hv')) (fun ω => ⟨X j ω, rfl⟩),
    p.property.weight_eq, one_mul]

/-- Independence on a finite index set descends to every subset — the
marginalization closure that makes the full-tuple `Dist.iIndepRV` equivalent to
the subset-closed notion on finite value spaces. -/
theorem iIndepRVOn.subset {Ω ι : Type*} {A : ι → Type*} [DecidableEq ι]
    [∀ i, Fintype (A i)] {p : ProbDist Ω} {X : ∀ i, RV (Ω := Ω) (A := A i)}
    {s t : Finset ι} (hst : s ⊆ t) (h : iIndepRVOn t p X) :
    iIndepRVOn s p X :=
  Finset.forall_subset_of_forall_erase (P := fun u => iIndepRVOn u p X)
    (fun _ _ hj hu => hu.erase hj) hst h

/-- Mutual independence implies `k`-wise independence, for every `k`. -/
theorem iIndepRV.kIndepRV {Ω ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] {p : ProbDist Ω} {X : ∀ i, RV (Ω := Ω) (A := A i)}
    (h : iIndepRV p X) (k : ℕ) : kIndepRV k p X :=
  fun _ _ => iIndepRVOn.subset (Finset.subset_univ _)
    ((iIndepRVOn_univ_iff_iIndepRV p X).mpr h)

/-- **`iIndepRV` is the top of the `k`-wise ladder**: on a finite index set with
finite value spaces, `k`-wise independence at `k = |ι|` is exactly the
full-tuple factorization `Dist.iIndepRV`.  This is why the tree's `iIndepRV`
may stay the primitive notion of mutual independence even though mathlib's
`iIndepFun` is subset-closed by definition. -/
theorem kIndepRV_card_iff_iIndepRV {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (p : ProbDist Ω)
    (X : ∀ i, RV (Ω := Ω) (A := A i)) :
    kIndepRV (Fintype.card ι) p X ↔ iIndepRV p X := by
  constructor
  · intro h
    exact (iIndepRVOn_univ_iff_iIndepRV p X).mp
      (h Finset.univ (le_of_eq Finset.card_univ))
  · intro h
    exact h.kIndepRV _

/-- `k`-wise independence weakens as `k` decreases. -/
theorem kIndepRV.mono {Ω ι : Type*} {A : ι → Type*} {p : ProbDist Ω}
    {X : ∀ i, RV (Ω := Ω) (A := A i)} {k k' : ℕ} (hk : k ≤ k')
    (h : kIndepRV k' p X) : kIndepRV k p X :=
  fun s hs => h s (hs.trans hk)

/-- **Pairwise independence is `2`-wise independence.**  The forward direction
instantiates the `Finset` form at `{i, j}`; the reverse handles the cardinality
`0` and `1` cases, where the claim is the normalization `X(True) = 1` and a
tautology. -/
theorem kIndepRV_two_iff_pairwiseIndepRV {Ω ι : Type*} [DecidableEq ι]
    {A : ι → Type*} (p : ProbDist Ω) (X : ∀ i, RV (Ω := Ω) (A := A i)) :
    kIndepRV 2 p X ↔ PairwiseIndepRV p X := by
  constructor
  · intro h i j hij u v
    obtain ⟨ω₀⟩ := nonempty_of_isProbDist p.property
    have hai : Function.update (Function.update (fun l => X l ω₀) i u) j v i = u := by
      rw [Function.update_of_ne hij, Function.update_self]
    have haj : Function.update (Function.update (fun l => X l ω₀) i u) j v j = v :=
      Function.update_self _ _ _
    have hs := h {i, j} (le_of_eq (Finset.card_pair hij))
      (Function.update (Function.update (fun l => X l ω₀) i u) j v)
    rw [Finset.prod_pair hij, hai, haj] at hs
    rw [← hs]
    exact mass_congr p.val fun ω => by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hu, hv⟩ l hl
        rcases hl with rfl | rfl
        · rw [hai]; exact hu
        · rw [haj]; exact hv
      · intro hl
        exact ⟨hai ▸ hl i (Or.inl rfl), haj ▸ hl j (Or.inr rfl)⟩
  · intro h s hs a
    have hcard : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
    rcases hcard with h0 | h1 | h2
    · obtain rfl : s = ∅ := Finset.card_eq_zero.mp h0
      rw [Finset.prod_empty, mass_congr p.val (Q := fun _ => True) (fun ω => by simp),
        mass_true]
      exact p.property.weight_eq
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
      rw [Finset.prod_singleton]
      exact mass_congr p.val fun ω => by simp
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp h2
      rw [Finset.prod_pair hij, ← h hij (a i) (a j)]
      exact mass_congr p.val fun ω => by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hl
          exact ⟨hl i (Or.inl rfl), hl j (Or.inr rfl)⟩
        · rintro ⟨hu, hv⟩ l hl
          rcases hl with rfl | rfl
          · exact hu
          · exact hv

/-- Mutual independence implies pairwise independence. -/
theorem iIndepRV.pairwiseIndepRV {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] {p : ProbDist Ω}
    {X : ∀ i, RV (Ω := Ω) (A := A i)} (h : iIndepRV p X) : PairwiseIndepRV p X :=
  (kIndepRV_two_iff_pairwiseIndepRV p X).mp (h.kIndepRV 2)

end Dist

end RandomSystems
