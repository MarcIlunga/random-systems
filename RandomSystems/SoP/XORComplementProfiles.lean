/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORComplementSparse
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Fintype
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Profile symmetries and finite hyperplane cuts for the XOR SoP complement tail

This file supplies the exact symmetry layer for the sole analytic term left by
`XORComplementSparse`.  Injection coefficients and row multiplicities are
invariant under row permutations.  Three-quarter separation is also invariant
under global character shifts, so the unquotiented separated fourth moment is
exactly `2^n` times its anchored counterpart.

The final section proves a finite Walsh second-moment identity.  Consequently
every three-quarter-separated profile has a character hyperplane with a
constant fraction of its rows on both sides.  This is the elementary entry
point for a nested card-pairing proof.  It is not, by itself, the still-open
aggregate fourth-moment estimate: applying a pointwise pairing bound before
summing masks loses the cancellations needed for that estimate.
-/

noncomputable section
open scoped BigOperators

namespace RandomSystems.SoP.XORComplement

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCoefficient
open RandomSystems.SoP.XORCore

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def permuteRows {n q : Nat} (sigma : Equiv.Perm (Fin q))
    (a : BitMatrix q n) : BitMatrix q n :=
  fun i => a (sigma i)

def embeddingPrecompEquiv {G : Type*} {q : Nat}
    (sigma : Equiv.Perm (Fin q)) :
    (Fin q ↪ G) ≃ (Fin q ↪ G) where
  toFun e := sigma.symm.toEmbedding.trans e
  invFun e := sigma.toEmbedding.trans e
  left_inv e := by
    ext i
    simp
  right_inv e := by
    ext i
    simp

theorem checkerProduct_permuteRows {n q : Nat}
    (sigma : Equiv.Perm (Fin q)) (a : BitMatrix q n)
    (e : Fin q ↪ XorSpace n) :
    checkerProduct (permuteRows sigma a) e =
      checkerProduct a (embeddingPrecompEquiv sigma e) := by
  unfold checkerProduct permuteRows embeddingPrecompEquiv
  simpa using (Equiv.prod_comp sigma
    (fun i => vectorWalsh (a i) (e (sigma.symm i))))

theorem fourier_injectionDensity_permuteRows {n q : Nat}
    (hq : q ≤ 2 ^ n) (sigma : Equiv.Perm (Fin q))
    (a : BitMatrix q n) :
    fourier (injectionDensity n q) (permuteRows sigma a) =
      fourier (injectionDensity n q) a := by
  rw [fourier_injectionDensity_eq_average_checkerProduct hq]
  rw [fourier_injectionDensity_eq_average_checkerProduct hq]
  unfold average
  rw [show (∑ e : Fin q ↪ XorSpace n,
      checkerProduct (permuteRows sigma a) e) =
      ∑ e : Fin q ↪ XorSpace n, checkerProduct a e by
    calc
      _ = ∑ e : Fin q ↪ XorSpace n,
          checkerProduct a (embeddingPrecompEquiv sigma e) := by
            apply Finset.sum_congr rfl
            intro e _he
            exact checkerProduct_permuteRows sigma a e
      _ = _ := by
        simpa using (Equiv.sum_comp (embeddingPrecompEquiv sigma)
          (checkerProduct a))
  ]

/-! ## The exact row-sum cancellation

Translating every card of a uniform injection is a permutation of the sample
space.  The checker product picks up the character of the XOR of all mask
rows.  Averaging that identity over translations kills every mask whose row
XOR is nonzero.  This is the first cancellation used by both the sparse and
minor-arc analyses.
-/

def embeddingTranslateEquiv {n q : Nat} (v : XorSpace n) :
    (Fin q ↪ XorSpace n) ≃ (Fin q ↪ XorSpace n) where
  toFun e := e.trans (Equiv.addRight v).toEmbedding
  invFun e := e.trans (Equiv.addRight (-v)).toEmbedding
  left_inv e := by
    ext i j
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
    exact congrFun (add_neg_cancel_right (e i) v) j
  right_inv e := by
    ext i j
    simp only [Function.Embedding.trans_apply, Equiv.toEmbedding_apply]
    exact congrFun (neg_add_cancel_right (e i) v) j

theorem prod_vectorWalsh_eq_maskRowSum {n q : Nat}
    (a : BitMatrix q n) (v : XorSpace n) :
    (∏ i : Fin q, vectorWalsh (a i) v) =
      vectorWalsh (maskRowSum a) v := by
  unfold maskRowSum
  induction (Finset.univ : Finset (Fin q)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        vectorWalsh_add_left, ih]

theorem checkerProduct_embeddingTranslateEquiv {n q : Nat}
    (a : BitMatrix q n) (v : XorSpace n) (e : Fin q ↪ XorSpace n) :
    checkerProduct a (embeddingTranslateEquiv v e) =
      vectorWalsh (maskRowSum a) v * checkerProduct a e := by
  unfold checkerProduct embeddingTranslateEquiv
  change (∏ i : Fin q, vectorWalsh (a i) (e i + v)) = _
  simp_rw [vectorWalsh_add_right]
  rw [Finset.prod_mul_distrib, prod_vectorWalsh_eq_maskRowSum]
  ring

theorem checkerCorrelation_eq_maskRowSum_sign_mul {n q : Nat}
    (a : BitMatrix q n) (v : XorSpace n) :
    checkerCorrelation a =
      vectorWalsh (maskRowSum a) v * checkerCorrelation a := by
  unfold checkerCorrelation average
  have hsum :
      (∑ e : Fin q ↪ XorSpace n,
          checkerProduct a (embeddingTranslateEquiv v e)) =
        ∑ e : Fin q ↪ XorSpace n, checkerProduct a e := by
    simpa using (Equiv.sum_comp (embeddingTranslateEquiv v)
      (checkerProduct a))
  rw [show
      (∑ e : Fin q ↪ XorSpace n,
          checkerProduct a (embeddingTranslateEquiv v e)) =
        vectorWalsh (maskRowSum a) v *
          ∑ e : Fin q ↪ XorSpace n, checkerProduct a e by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _he
    exact checkerProduct_embeddingTranslateEquiv a v e]
    at hsum
  calc
    (∑ e : Fin q ↪ XorSpace n, checkerProduct a e) /
          (Fintype.card (Fin q ↪ XorSpace n) : Real) =
        (vectorWalsh (maskRowSum a) v *
          ∑ e : Fin q ↪ XorSpace n, checkerProduct a e) /
            (Fintype.card (Fin q ↪ XorSpace n) : Real) := by rw [hsum]
    _ = vectorWalsh (maskRowSum a) v *
        ((∑ e : Fin q ↪ XorSpace n, checkerProduct a e) /
          (Fintype.card (Fin q ↪ XorSpace n) : Real)) := by ring

theorem checkerCorrelation_eq_zero_of_maskRowSum_ne_zero {n q : Nat}
    (a : BitMatrix q n) (hsum : maskRowSum a ≠ 0) :
    checkerCorrelation a = 0 := by
  let c := checkerCorrelation a
  have hv (v : XorSpace n) : c = vectorWalsh (maskRowSum a) v * c :=
    checkerCorrelation_eq_maskRowSum_sign_mul a v
  have hsumEq := congrArg (fun f : XorSpace n → Real => ∑ v, f v)
    (funext hv)
  dsimp [c] at hsumEq ⊢
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsumEq
  rw [← Finset.sum_mul, sum_vectorWalsh, if_neg hsum] at hsumEq
  norm_num at hsumEq
  exact hsumEq

theorem fourier_injectionDensity_eq_zero_of_maskRowSum_ne_zero
    {n q : Nat} (hq : q ≤ 2 ^ n) (a : BitMatrix q n)
    (hsum : maskRowSum a ≠ 0) :
    fourier (injectionDensity n q) a = 0 := by
  rw [fourier_injectionDensity_eq_average_checkerProduct hq]
  exact checkerCorrelation_eq_zero_of_maskRowSum_ne_zero a hsum

theorem rowMultiplicity_permuteRows {n q : Nat}
    (sigma : Equiv.Perm (Fin q)) (a : BitMatrix q n)
    (beta : XorSpace n) :
    rowMultiplicity (permuteRows sigma a) beta = rowMultiplicity a beta := by
  unfold rowMultiplicity permuteRows
  refine Finset.card_bij (fun i _hi => sigma i) ?_ ?_ ?_
  · intro i hi
    simpa using hi
  · intro i hi j hj hij
    exact sigma.injective hij
  · intro j hj
    refine ⟨sigma.symm j, ?_, by simp⟩
    simpa using hj

theorem threeQuarterSeparated_permuteRows_iff {n q : Nat}
    (sigma : Equiv.Perm (Fin q)) (a : BitMatrix q n) :
    IsThreeQuarterSeparated (permuteRows sigma a) ↔
      IsThreeQuarterSeparated a := by
  unfold IsThreeQuarterSeparated
  simp_rw [rowMultiplicity_permuteRows]

/-! ## Exact row profiles

The analytic sum depends on a mask only through the multiset of its rows.
We expose that quotient as `Sym` rather than introducing a bespoke entropy
carrier.  A profile is therefore literally a multiset of the prescribed
cardinality, and its multiplicity function is Mathlib's `Multiset.count`.
-/

/-- The multiset of row characters of a mask. -/
def rowMultiset {n q : Nat} (a : BitMatrix q n) : Multiset (XorSpace n) :=
  (Finset.univ : Finset (Fin q)).1.map a

@[simp]
theorem card_rowMultiset {n q : Nat} (a : BitMatrix q n) :
    (rowMultiset a).card = q := by
  simp [rowMultiset]

theorem count_rowMultiset {n q : Nat} (a : BitMatrix q n)
    (beta : XorSpace n) :
    (rowMultiset a).count beta = rowMultiplicity a beta := by
  unfold rowMultiset rowMultiplicity
  rw [Multiset.count_map]
  change
    ((Finset.univ : Finset (Fin q)).1.filter (fun i => beta = a i)).card =
      ((Finset.univ : Finset (Fin q)).filter (fun i => a i = beta)).card
  change
    ((Finset.univ : Finset (Fin q)).1.filter (fun i => beta = a i)).card =
      ((Finset.univ : Finset (Fin q)).1.filter (fun i => a i = beta)).card
  congr 1
  exact Multiset.filter_congr (fun _i _hi => eq_comm)

/-- The exact row-permutation quotient of a mask. -/
def rowSym {n q : Nat} (a : BitMatrix q n) : Sym (XorSpace n) q :=
  ⟨rowMultiset a, card_rowMultiset a⟩

@[simp]
theorem rowSym_val {n q : Nat} (a : BitMatrix q n) :
    (rowSym a : Multiset (XorSpace n)) = rowMultiset a := rfl

/-- A canonical-by-choice enumeration of a row profile.  Nothing analytic
depends on which enumeration `Fintype.equivOfCardEq` selects. -/
def rowSymRepresentative {n q : Nat} (s : Sym (XorSpace n) q) :
    BitMatrix q n :=
  let e : Fin q ≃ (s.1 : Multiset (XorSpace n)) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Multiset.card_coe]
      exact s.2.symm)
  fun i => (e i : XorSpace n)

theorem rowMultiset_rowSymRepresentative {n q : Nat}
    (s : Sym (XorSpace n) q) :
    rowMultiset (rowSymRepresentative s) = s.1 := by
  let e : Fin q ≃ (s.1 : Multiset (XorSpace n)) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Multiset.card_coe]
      exact s.2.symm)
  change
    (Finset.univ : Finset (Fin q)).1.map
      (fun i => ((e i : (s.1 : Multiset (XorSpace n))) : XorSpace n)) = s.1
  calc
    (Finset.univ : Finset (Fin q)).1.map
        (fun i => ((e i : (s.1 : Multiset (XorSpace n))) : XorSpace n)) =
      ((Finset.univ : Finset (Fin q)).map e.toEmbedding).1.map
        (fun x : (s.1 : Multiset (XorSpace n)) => (x : XorSpace n)) := by
          rw [Finset.map_val, Multiset.map_map]
          rfl
    _ = (Finset.univ : Finset (s.1 : Multiset (XorSpace n))).1.map
        (fun x : (s.1 : Multiset (XorSpace n)) => (x : XorSpace n)) := by
          rw [Finset.univ_map_equiv_to_embedding]
    _ = s.1 := Multiset.map_univ_coe s.1

@[simp]
theorem rowSym_rowSymRepresentative {n q : Nat}
    (s : Sym (XorSpace n) q) :
    rowSym (rowSymRepresentative s) = s := by
  apply Subtype.ext
  exact rowMultiset_rowSymRepresentative s

theorem rowSym_surjective {n q : Nat} :
    Function.Surjective (rowSym : BitMatrix q n → Sym (XorSpace n) q) := by
  intro s
  exact ⟨rowSymRepresentative s, rowSym_rowSymRepresentative s⟩

/-- Two enumerations of the same row multiset differ by a row permutation. -/
theorem exists_rowPerm_of_rowSym_eq {n q : Nat}
    {a b : BitMatrix q n} (h : rowSym a = rowSym b) :
    ∃ sigma : Equiv.Perm (Fin q), permuteRows sigma a = b := by
  have hmult (beta : XorSpace n) :
      rowMultiplicity a beta = rowMultiplicity b beta := by
    rw [← count_rowMultiset, ← count_rowMultiset]
    exact congrArg (fun s : Sym (XorSpace n) q => s.1.count beta) h
  let E : ∀ beta : XorSpace n,
      {i : Fin q // b i = beta} ≃ {i : Fin q // a i = beta} :=
    fun beta => Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      simpa [rowMultiplicity] using (hmult beta).symm)
  let sigma : Equiv.Perm (Fin q) :=
    (Equiv.sigmaFiberEquiv b).symm |>.trans
      ((Equiv.sigmaCongr (Equiv.refl _) E).trans
        (Equiv.sigmaFiberEquiv a))
  refine ⟨sigma, ?_⟩
  funext i
  change a (sigma i) = b i
  change a ((E (b i) ⟨i, rfl⟩).1) = b i
  exact (E (b i) ⟨i, rfl⟩).2

/-- Full injection coefficients are functions of the row multiset, not of
its enumeration. -/
theorem fourier_injectionDensity_eq_of_rowSym_eq {n q : Nat}
    (hq : q ≤ 2 ^ n) {a b : BitMatrix q n} (h : rowSym a = rowSym b) :
    fourier (injectionDensity n q) a =
      fourier (injectionDensity n q) b := by
  obtain ⟨sigma, hsigma⟩ := exists_rowPerm_of_rowSym_eq h
  rw [← hsigma]
  exact (fourier_injectionDensity_permuteRows hq sigma a).symm

theorem rowSym_permuteRows {n q : Nat}
    (sigma : Equiv.Perm (Fin q)) (a : BitMatrix q n) :
    rowSym (permuteRows sigma a) = rowSym a := by
  apply Subtype.ext
  apply Multiset.ext.mpr
  intro beta
  change (rowMultiset (permuteRows sigma a)).count beta =
    (rowMultiset a).count beta
  rw [count_rowMultiset, count_rowMultiset,
    rowMultiplicity_permuteRows]

/-! The semantic profile fiber is the usual multinomial orbit.  We prove
this through the domain-permutation action and orbit-stabilizer, using
Mathlib's exact description of the stabilizer as the product of the
permutation groups of the equal-row fibers. -/

theorem rowSym_eq_iff_mem_domOrbit {n q : Nat}
    (a b : BitMatrix q n) :
    rowSym b = rowSym a ↔
      b ∈ MulAction.orbit ((Equiv.Perm (Fin q))ᵈᵐᵃ) a := by
  constructor
  · intro h
    obtain ⟨sigma, hsigma⟩ := exists_rowPerm_of_rowSym_eq h.symm
    rw [MulAction.mem_orbit_iff]
    refine ⟨DomMulAct.mk sigma, ?_⟩
    rw [← hsigma]
    funext i
    simp [DomMulAct.smul_apply, permuteRows]
  · intro h
    rw [MulAction.mem_orbit_iff] at h
    obtain ⟨g, rfl⟩ := h
    have hact : g • a = permuteRows (DomMulAct.mk.symm g) a := by
      funext i
      simp [DomMulAct.smul_apply, permuteRows]
    rw [hact, rowSym_permuteRows]

noncomputable def rowSymFiberEquivOrbit {n q : Nat}
    (a : BitMatrix q n) :
    {b : BitMatrix q n // rowSym b = rowSym a} ≃
      MulAction.orbit ((Equiv.Perm (Fin q))ᵈᵐᵃ) a :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun b => rowSym_eq_iff_mem_domOrbit a b)

noncomputable instance domRowPermFintype (q : Nat) :
    Fintype ((Equiv.Perm (Fin q))ᵈᵐᵃ) :=
  Fintype.ofEquiv (Equiv.Perm (Fin q)) DomMulAct.mk

theorem card_domStabilizer_eq_prod_rowMultiplicity_factorial
    {n q : Nat} (a : BitMatrix q n) :
    Fintype.card (MulAction.stabilizer
        ((Equiv.Perm (Fin q))ᵈᵐᵃ) a) =
      ∏ beta : XorSpace n, (rowMultiplicity a beta).factorial := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr MulOpposite.opEquiv,
    Nat.card_congr (DomMulAct.stabilizerMulEquiv a).toEquiv,
    Nat.card_pi]
  apply Finset.prod_congr rfl
  intro beta _hbeta
  rw [Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_subtype]
  rfl

theorem card_domRowPermGroup_eq_factorial (q : Nat) :
    Fintype.card ((Equiv.Perm (Fin q))ᵈᵐᵃ) = q.factorial := by
  calc
    Fintype.card ((Equiv.Perm (Fin q))ᵈᵐᵃ) =
        Fintype.card (Equiv.Perm (Fin q)) :=
      Fintype.card_congr DomMulAct.mk.symm
    _ = q.factorial := by
      rw [Fintype.card_perm, Fintype.card_fin]

theorem card_rowSym_fiber_mul_prod_factorial {n q : Nat}
    (s : Sym (XorSpace n) q) :
    ((Finset.univ : Finset (BitMatrix q n)).filter
        (fun a => rowSym a = s)).card *
        (∏ beta : XorSpace n, (s.1.count beta).factorial) =
      q.factorial := by
  let a : BitMatrix q n := rowSymRepresentative s
  have ha : rowSym a = s := rowSym_rowSymRepresentative s
  have hfiber :
      ((Finset.univ : Finset (BitMatrix q n)).filter
          (fun b => rowSym b = s)).card =
        Fintype.card
          (MulAction.orbit ((Equiv.Perm (Fin q))ᵈᵐᵃ) a) := by
    calc
      ((Finset.univ : Finset (BitMatrix q n)).filter
          (fun b => rowSym b = s)).card =
        Fintype.card {b : BitMatrix q n // rowSym b = s} := by
          rw [Fintype.card_subtype]
      _ = Fintype.card {b : BitMatrix q n // rowSym b = rowSym a} := by
          rw [ha]
      _ = Fintype.card
          (MulAction.orbit ((Equiv.Perm (Fin q))ᵈᵐᵃ) a) :=
        Fintype.card_congr (rowSymFiberEquivOrbit a)
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    ((Equiv.Perm (Fin q))ᵈᵐᵃ) a
  rw [card_domStabilizer_eq_prod_rowMultiplicity_factorial,
    card_domRowPermGroup_eq_factorial] at horbit
  rw [hfiber]
  rw [show (∏ beta : XorSpace n, (s.1.count beta).factorial) =
      ∏ beta : XorSpace n, (rowMultiplicity a beta).factorial by
    apply Finset.prod_congr rfl
    intro beta _hbeta
    rw [← count_rowMultiset]
    rw [rowMultiset_rowSymRepresentative]]
  exact horbit

theorem countPerms_eq_factorial_div_prod_count
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (m : Multiset alpha) :
    m.countPerms = m.card.factorial /
      ∏ x : alpha, (m.count x).factorial := by
  unfold Multiset.countPerms
  have hsupp : m.toFinsupp.support ⊆ (Finset.univ : Finset alpha) := by
    exact Finset.subset_univ _
  rw [Finsupp.multinomial_eq_of_support_subset hsupp]
  unfold Nat.multinomial
  simp only [Multiset.toFinsupp_apply]
  rw [Multiset.sum_count_eq_card (by simp)]

/-- Exact identification of a row-profile fiber with its standard
multinomial coefficient. -/
theorem card_rowSym_fiber_eq_countPerms {n q : Nat}
    (s : Sym (XorSpace n) q) :
    ((Finset.univ : Finset (BitMatrix q n)).filter
        (fun a => rowSym a = s)).card = s.1.countPerms := by
  rw [countPerms_eq_factorial_div_prod_count, s.2]
  exact Nat.eq_div_of_mul_eq_left (by positivity)
    (card_rowSym_fiber_mul_prod_factorial s)

/-- Three-quarter separation stated entirely on a row profile. -/
def IsThreeQuarterSeparatedProfile {n q : Nat}
    (s : Sym (XorSpace n) q) : Prop :=
  ∀ beta : XorSpace n, 4 * (s.1.count beta) ≤ 3 * q

theorem isThreeQuarterSeparatedProfile_rowSym_iff {n q : Nat}
    (a : BitMatrix q n) :
    IsThreeQuarterSeparatedProfile (rowSym a) ↔
      IsThreeQuarterSeparated a := by
  unfold IsThreeQuarterSeparatedProfile IsThreeQuarterSeparated
  change (∀ beta : XorSpace n,
      4 * (rowMultiset a).count beta ≤ 3 * q) ↔ _
  simp_rw [count_rowMultiset]

theorem rowMultiplicity_add_constantMask {n q : Nat}
    (a : BitMatrix q n) (gamma beta : XorSpace n) :
    rowMultiplicity (a + constantMask gamma) beta =
      rowMultiplicity a (beta + gamma) := by
  unfold rowMultiplicity constantMask
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply]
  constructor
  · intro h
    have h' := congrArg (fun z : XorSpace n => z + gamma) h
    simpa [add_assoc] using h'
  · intro h
    have h' := congrArg (fun z : XorSpace n => z + gamma) h
    simpa [add_assoc] using h'

theorem threeQuarterSeparated_add_constantMask_iff {n q : Nat}
    (a : BitMatrix q n) (gamma : XorSpace n) :
    IsThreeQuarterSeparated (a + constantMask gamma) ↔
      IsThreeQuarterSeparated a := by
  constructor
  · intro h beta
    have hb := h (beta + gamma)
    rw [rowMultiplicity_add_constantMask] at hb
    simpa [add_assoc] using hb
  · intro h beta
    rw [rowMultiplicity_add_constantMask]
    exact h (beta + gamma)

/-- The separated contribution before taking the global-character quotient. -/
def separatedFullFourthTail (n : Nat) : Real :=
  ∑ a : BitMatrix (2 ^ n) n,
    if IsThreeQuarterSeparated a ∧ ¬ IsFullProxyMode a then
      fourier (injectionDensity n (2 ^ n)) a ^ 4
    else 0

/-- Exact orbit accounting for the separated tail.  Each anchored mask stands
for precisely `2^n` global character shifts, with no analytic loss. -/
theorem separatedFullFourthTail_eq_card_mul_anchored (n : Nat) :
    separatedFullFourthTail n =
      ((2 ^ n : Nat) : Real) * separatedAnchoredFourthTail n := by
  unfold separatedFullFourthTail separatedAnchoredFourthTail
  apply sum_global_shift_invariant_eq_card_mul_sum_anchored
  intro a gamma
  rw [threeQuarterSeparated_add_constantMask_iff,
    isFullProxyMode_add_constantMask_iff]
  have hsq := fourier_injection_density_sq_add_constant_mask_full a gamma
  by_cases h : IsThreeQuarterSeparated a ∧ ¬ IsFullProxyMode a
  · simp only [h.1, h.2, not_false_eq_true, and_self, if_true]
    calc
      fourier (injectionDensity n (2 ^ n))
          (a + constantMask gamma) ^ 4 =
          (fourier (injectionDensity n (2 ^ n))
            (a + constantMask gamma) ^ 2) ^ 2 := by ring
      _ = (fourier (injectionDensity n (2 ^ n)) a ^ 2) ^ 2 := by rw [hsq]
      _ = fourier (injectionDensity n (2 ^ n)) a ^ 4 := by ring
  · simp [h]

/-! ## Hyperplane profiles

The following identities are the finite Walsh form of the elementary
"choose a balanced cut" argument.  They deliberately avoid probability
spaces: every average is a literal finite sum.
-/

/-- Signed imbalance of the rows of `a` across the character hyperplane
selected by `v`. -/
def rowWalshSum {n q : Nat} (a : BitMatrix q n) (v : XorSpace n) : Real :=
  ∑ i : Fin q, vectorWalsh (a i) v

/-- Orthogonality for one-word Walsh characters, in probability
normalization. -/
theorem average_vectorWalsh_mul {n : Nat} (alpha beta : XorSpace n) :
    average (XorSpace n)
        (fun v => vectorWalsh alpha v * vectorWalsh beta v) =
      if alpha = beta then 1 else 0 := by
  rw [show (fun v => vectorWalsh alpha v * vectorWalsh beta v) =
      vectorWalsh (alpha + beta) by
    funext v
    exact (vectorWalsh_add_left alpha beta v).symm]
  unfold average
  rw [sum_vectorWalsh]
  have hcard : (Fintype.card (XorSpace n) : Real) = (2 ^ n : Nat) := by
    norm_num [card_xorSpace]
  rw [hcard]
  have hN : ((2 ^ n : Nat) : Real) ≠ 0 := by positivity
  by_cases h : alpha = beta
  · subst beta
    simp
  · have hab : alpha + beta ≠ 0 := by
      simpa [xorSpace_add_eq_zero_iff_eq] using h
    simp [h, hab]

/-- Exact second moment of all row-hyperplane imbalances.  The right side is
the number of ordered pairs of equal rows, grouped by their first endpoint. -/
theorem average_rowWalshSum_sq {n q : Nat} (a : BitMatrix q n) :
    average (XorSpace n) (fun v => rowWalshSum a v ^ 2) =
      ∑ i : Fin q, (rowMultiplicity a (a i) : Real) := by
  calc
    average (XorSpace n) (fun v => rowWalshSum a v ^ 2) =
        average (XorSpace n) (fun v =>
          ∑ i : Fin q, ∑ j : Fin q,
            vectorWalsh (a i) v * vectorWalsh (a j) v) := by
      apply congrArg (average (XorSpace n))
      funext v
      unfold rowWalshSum
      rw [pow_two, Fintype.sum_mul_sum]
    _ = ∑ i : Fin q, ∑ j : Fin q,
          average (XorSpace n)
            (fun v => vectorWalsh (a i) v * vectorWalsh (a j) v) := by
      rw [average_fintype_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [average_fintype_sum]
    _ = ∑ i : Fin q, ∑ j : Fin q,
          if a i = a j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      rw [average_vectorWalsh_mul]
    _ = ∑ i : Fin q, (rowMultiplicity a (a i) : Real) := by
      apply Finset.sum_congr rfl
      intro i _hi
      unfold rowMultiplicity
      simpa only [eq_comm] using
        (Finset.sum_boole (R := Real) (fun j : Fin q => a j = a i)
          (Finset.univ : Finset (Fin q)))

/-- A three-quarter-separated profile has at most three quarters of all
ordered equal-row pairs.  The integral form keeps all rounding exact. -/
theorem four_mul_sum_rowMultiplicity_le_of_threeQuarterSeparated
    {n q : Nat} {a : BitMatrix q n} (hsep : IsThreeQuarterSeparated a) :
    4 * ∑ i : Fin q, rowMultiplicity a (a i) ≤ 3 * q * q := by
  calc
    4 * ∑ i : Fin q, rowMultiplicity a (a i) =
        ∑ i : Fin q, 4 * rowMultiplicity a (a i) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _i : Fin q, 3 * q := by
      exact Finset.sum_le_sum fun i _hi => hsep (a i)
    _ = 3 * q * q := by
      simp [Finset.sum_const]
      ring

/-- Every three-quarter-separated row profile admits a Walsh hyperplane whose
two sides have squared imbalance at most three quarters of the maximum. -/
theorem exists_hyperplane_with_small_imbalance
    {n q : Nat} {a : BitMatrix q n} (hsep : IsThreeQuarterSeparated a) :
    ∃ v : XorSpace n,
      4 * rowWalshSum a v ^ 2 ≤ 3 * (q : Real) ^ 2 := by
  have hprofileNat :=
    four_mul_sum_rowMultiplicity_le_of_threeQuarterSeparated hsep
  have hprofile :
      4 * (∑ i : Fin q, (rowMultiplicity a (a i) : Real)) ≤
        3 * (q : Real) ^ 2 := by
    have hcast :
        4 * (∑ i : Fin q, (rowMultiplicity a (a i) : Real)) ≤
          3 * (q : Real) * (q : Real) := by
      exact_mod_cast hprofileNat
    nlinarith
  have havg := average_rowWalshSum_sq a
  unfold average at havg
  rw [card_xorSpace] at havg
  have hN : ((2 ^ n : Nat) : Real) ≠ 0 := by positivity
  have hsum :
      (∑ v : XorSpace n, rowWalshSum a v ^ 2) =
        ((2 ^ n : Nat) : Real) *
          ∑ i : Fin q, (rowMultiplicity a (a i) : Real) := by
    apply (div_eq_iff hN).mp at havg
    nlinarith
  have hsumLe :
      (∑ v : XorSpace n, 4 * rowWalshSum a v ^ 2) ≤
        ∑ _v : XorSpace n, 3 * (q : Real) ^ 2 := by
    rw [← Finset.mul_sum, hsum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_xorSpace]
    have hNnonneg : (0 : Real) ≤ ((2 ^ n : Nat) : Real) := by positivity
    nlinarith
  obtain ⟨v, _hv, hv⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (XorSpace n)))
    (f := fun v => 4 * rowWalshSum a v ^ 2)
    (g := fun _v => 3 * (q : Real) ^ 2)
    Finset.univ_nonempty hsumLe
  exact ⟨v, hv⟩

/-- Number of rows on the negative side of the Walsh hyperplane `v`. -/
def hyperplaneWeight {n q : Nat} (a : BitMatrix q n) (v : XorSpace n) : Nat :=
  ((Finset.univ : Finset (Fin q)).filter
    (fun i => vectorDot (a i) v ≠ 0)).card

theorem hyperplaneWeight_le_rows {n q : Nat}
    (a : BitMatrix q n) (v : XorSpace n) :
    hyperplaneWeight a v ≤ q := by
  unfold hyperplaneWeight
  simpa using Finset.card_le_card
    (Finset.filter_subset (fun i : Fin q => vectorDot (a i) v ≠ 0)
      (Finset.univ : Finset (Fin q)))

/-- The Walsh imbalance is exactly `positive rows - negative rows`. -/
theorem rowWalshSum_eq_rows_sub_two_mul_weight {n q : Nat}
    (a : BitMatrix q n) (v : XorSpace n) :
    rowWalshSum a v =
      (q : Real) - 2 * (hyperplaneWeight a v : Real) := by
  unfold rowWalshSum hyperplaneWeight vectorWalsh bitSign
  calc
    (∑ i : Fin q, if vectorDot (a i) v = 0 then (1 : Real) else -1) =
        ∑ i : Fin q,
          (1 - 2 * if vectorDot (a i) v ≠ 0 then (1 : Real) else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : vectorDot (a i) v = 0 <;> norm_num [h]
    _ = (q : Real) - 2 *
        (((Finset.univ : Finset (Fin q)).filter
          (fun i => vectorDot (a i) v ≠ 0)).card : Real) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [← Finset.mul_sum]
      rw [show (∑ i : Fin q,
          if vectorDot (a i) v ≠ 0 then (1 : Real) else 0) =
          (((Finset.univ : Finset (Fin q)).filter
            (fun i => vectorDot (a i) v ≠ 0)).card : Real) by
        simpa using
          (Finset.sum_boole (R := Real)
            (fun i : Fin q => vectorDot (a i) v ≠ 0)
            (Finset.univ : Finset (Fin q))) ]
      ring

/-- A separated profile has a hyperplane cut with a constant fraction of the
rows on both sides.  The product form avoids all floor and ceiling choices. -/
theorem exists_hyperplane_with_large_cross_product
    {n q : Nat} {a : BitMatrix q n} (hsep : IsThreeQuarterSeparated a) :
    ∃ v : XorSpace n,
      (q : Real) ^ 2 ≤
        16 * (hyperplaneWeight a v : Real) *
          ((q : Real) - hyperplaneWeight a v) := by
  obtain ⟨v, hv⟩ := exists_hyperplane_with_small_imbalance hsep
  refine ⟨v, ?_⟩
  rw [rowWalshSum_eq_rows_sub_two_mul_weight] at hv
  nlinarith [sq_nonneg
    ((q : Real) - 2 * (hyperplaneWeight a v : Real))]

/-! ## Exact cubic-mass reduction

Eberhard's final minor-arc step is an interpolation rather than a pointwise
fourth-moment sum: one copy of a coefficient is bounded pointwise, while the
other three copies stay inside the global cubic mass.  This matters because
summing a pointwise fourth-power estimate profile by profile loses too much.
-/

/-- The unnormalized cubic Fourier mass of the full injection density. -/
def fullInjectionCubicMass (n : Nat) : Real :=
  ∑ a : BitMatrix (2 ^ n) n,
    |fourier (injectionDensity n (2 ^ n)) a| ^ 3

/-- Cubic mass after choosing one representative from every global-character
shift orbit. -/
def anchoredInjectionCubicMass (n : Nat) : Real :=
  ∑ b : AnchoredMask n,
    |fourier (injectionDensity n (2 ^ n)) b.1| ^ 3

/-- The cubic mass of precisely the separated quotient profiles.  Bounding
this smaller object suffices; no major-arc estimate is logically required. -/
def separatedAnchoredCubicMass (n : Nat) : Real :=
  ∑ b : AnchoredMask n,
    if IsThreeQuarterSeparated b.1 ∧ ¬ IsFullProxyMode b.1 then
      |fourier (injectionDensity n (2 ^ n)) b.1| ^ 3
    else 0

theorem abs_fourier_injection_density_add_constant_mask_full
    {n : Nat} (a : BitMatrix (2 ^ n) n) (gamma : XorSpace n) :
    |fourier (injectionDensity n (2 ^ n))
        (a + constantMask gamma)| =
      |fourier (injectionDensity n (2 ^ n)) a| := by
  have hsq := fourier_injection_density_sq_add_constant_mask_full a gamma
  nlinarith [sq_abs
    (fourier (injectionDensity n (2 ^ n)) (a + constantMask gamma)),
    sq_abs (fourier (injectionDensity n (2 ^ n)) a),
    abs_nonneg (fourier (injectionDensity n (2 ^ n))
      (a + constantMask gamma)),
    abs_nonneg (fourier (injectionDensity n (2 ^ n)) a)]

/-- The separated cubic contribution before taking the global-character
quotient. -/
def separatedFullCubicMass (n : Nat) : Real :=
  ∑ a : BitMatrix (2 ^ n) n,
    if IsThreeQuarterSeparated a ∧ ¬ IsFullProxyMode a then
      |fourier (injectionDensity n (2 ^ n)) a| ^ 3
    else 0

/-- Exact orbit accounting for the separated cubic mass. -/
theorem separatedFullCubicMass_eq_card_mul_anchored (n : Nat) :
    separatedFullCubicMass n =
      ((2 ^ n : Nat) : Real) * separatedAnchoredCubicMass n := by
  unfold separatedFullCubicMass separatedAnchoredCubicMass
  apply sum_global_shift_invariant_eq_card_mul_sum_anchored
  intro a gamma
  rw [threeQuarterSeparated_add_constantMask_iff,
    isFullProxyMode_add_constantMask_iff,
    abs_fourier_injection_density_add_constant_mask_full]

/-- A deliberately larger high-entropy sum obtained by forgetting only the
proxy-mode deletion.  It is the exact object controlled by the source's
profile-counting theorem. -/
def highEntropyFullCubicMass (n : Nat) : Real :=
  ∑ a : BitMatrix (2 ^ n) n,
    if IsThreeQuarterSeparated a then
      |fourier (injectionDensity n (2 ^ n)) a| ^ 3
    else 0

theorem separatedFullCubicMass_le_highEntropyFullCubicMass (n : Nat) :
    separatedFullCubicMass n ≤ highEntropyFullCubicMass n := by
  unfold separatedFullCubicMass highEntropyFullCubicMass
  apply Finset.sum_le_sum
  intro a _ha
  by_cases hsep : IsThreeQuarterSeparated a
  · rw [if_pos hsep]
    by_cases hproxy : IsFullProxyMode a
    · simp [hsep, hproxy]
    · simp [hsep, hproxy]
  · simp [hsep]

/-- Cubic mass of one exact row-multiset fiber. -/
def rowProfileCubicContribution (n : Nat)
    (s : Sym (XorSpace n) (2 ^ n)) : Real :=
  ∑ a ∈ (Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
      (fun a => rowSym a = s),
    |fourier (injectionDensity n (2 ^ n)) a| ^ 3

/-- High-entropy cubic mass written as a sum over exact multiplicity
profiles. -/
def highEntropyProfileCubicMass (n : Nat) : Real :=
  ∑ s : Sym (XorSpace n) (2 ^ n),
    if IsThreeQuarterSeparatedProfile s then
      rowProfileCubicContribution n s
    else 0

/-- Exact profile reindexing.  No estimate, asymptotic notation, or orbit
cardinality formula is hidden in this identity. -/
theorem highEntropyFullCubicMass_eq_profileCubicMass (n : Nat) :
    highEntropyFullCubicMass n = highEntropyProfileCubicMass n := by
  unfold highEntropyFullCubicMass highEntropyProfileCubicMass
  rw [← Finset.sum_fiberwise
    (s := (Finset.univ : Finset (BitMatrix (2 ^ n) n)))
    (g := rowSym)
    (f := fun a => if IsThreeQuarterSeparated a then
      |fourier (injectionDensity n (2 ^ n)) a| ^ 3 else 0)]
  apply Finset.sum_congr rfl
  intro s _hs
  unfold rowProfileCubicContribution
  by_cases hprofile : IsThreeQuarterSeparatedProfile s
  · rw [if_pos hprofile]
    apply Finset.sum_congr rfl
    intro a ha
    have has : rowSym a = s := (Finset.mem_filter.mp ha).2
    have hsep : IsThreeQuarterSeparated a := by
      rw [← isThreeQuarterSeparatedProfile_rowSym_iff]
      simpa [has] using hprofile
    rw [if_pos hsep]
  · rw [if_neg hprofile]
    apply Finset.sum_eq_zero
    intro a ha
    have has : rowSym a = s := (Finset.mem_filter.mp ha).2
    have hnsep : ¬ IsThreeQuarterSeparated a := by
      intro hsep
      apply hprofile
      rw [← has]
      exact isThreeQuarterSeparatedProfile_rowSym_iff a |>.2 hsep
    rw [if_neg hnsep]

/-- Cardinality of one exact row-profile fiber.  This semantic definition is
the multinomial orbit size; keeping it as a fiber cardinal avoids importing a
second, hand-rolled profile encoding into the analytic statements. -/
def rowProfileOrbitSize (n : Nat)
    (s : Sym (XorSpace n) (2 ^ n)) : Nat :=
  ((Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
    (fun a => rowSym a = s)).card

theorem rowProfileOrbitSize_eq_countPerms (n : Nat)
    (s : Sym (XorSpace n) (2 ^ n)) :
    rowProfileOrbitSize n s = s.1.countPerms := by
  exact card_rowSym_fiber_eq_countPerms s

theorem rowProfileOrbitSize_pos (n : Nat)
    (s : Sym (XorSpace n) (2 ^ n)) :
    0 < rowProfileOrbitSize n s := by
  unfold rowProfileOrbitSize
  rw [Finset.card_pos]
  exact ⟨rowSymRepresentative s, by simp⟩

/-- Exact multinomial-orbit factorization, stated with the semantic orbit
cardinality.  The coefficient is evaluated at the canonical profile
enumeration, but row-permutation invariance makes that choice immaterial. -/
theorem rowProfileCubicContribution_eq_orbit_mul (n : Nat)
    (s : Sym (XorSpace n) (2 ^ n)) :
    rowProfileCubicContribution n s =
      (rowProfileOrbitSize n s : Real) *
        |fourier (injectionDensity n (2 ^ n))
          (rowSymRepresentative s)| ^ 3 := by
  unfold rowProfileCubicContribution rowProfileOrbitSize
  calc
    (∑ a ∈ (Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
        (fun a => rowSym a = s),
        |fourier (injectionDensity n (2 ^ n)) a| ^ 3) =
      ∑ _a ∈ (Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
        (fun a => rowSym a = s),
        |fourier (injectionDensity n (2 ^ n))
          (rowSymRepresentative s)| ^ 3 := by
            apply Finset.sum_congr rfl
            intro a ha
            have has : rowSym a = s := (Finset.mem_filter.mp ha).2
            have hcoeff := fourier_injectionDensity_eq_of_rowSym_eq
              (le_refl (2 ^ n))
              (has.trans (rowSym_rowSymRepresentative s).symm)
            rw [hcoeff]
    _ = (((Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
        (fun a => rowSym a = s)).card : Real) *
          |fourier (injectionDensity n (2 ^ n))
            (rowSymRepresentative s)| ^ 3 := by
              simp [Finset.sum_const, nsmul_eq_mul]

/-- Source-facing form of the exact profile factorization. -/
theorem rowProfileCubicContribution_eq_countPerms_mul (n : Nat)
    (s : Sym (XorSpace n) (2 ^ n)) :
    rowProfileCubicContribution n s =
      (s.1.countPerms : Real) *
        |fourier (injectionDensity n (2 ^ n))
          (rowSymRepresentative s)| ^ 3 := by
  rw [rowProfileCubicContribution_eq_orbit_mul,
    rowProfileOrbitSize_eq_countPerms]

/-- A pointwise estimate on one profile factors out with its exact orbit
cardinality. -/
theorem rowProfileCubicContribution_le_orbit_mul
    {n : Nat} {s : Sym (XorSpace n) (2 ^ n)} {B : Real}
    (hpoint : ∀ a : BitMatrix (2 ^ n) n, rowSym a = s →
      |fourier (injectionDensity n (2 ^ n)) a| ^ 3 ≤ B) :
    rowProfileCubicContribution n s ≤
      (rowProfileOrbitSize n s : Real) * B := by
  unfold rowProfileCubicContribution rowProfileOrbitSize
  calc
    (∑ a ∈ (Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
        (fun a => rowSym a = s),
        |fourier (injectionDensity n (2 ^ n)) a| ^ 3) ≤
      ∑ _a ∈ (Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
        (fun a => rowSym a = s), B := by
          apply Finset.sum_le_sum
          intro a ha
          exact hpoint a (Finset.mem_filter.mp ha).2
    _ = (((Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
        (fun a => rowSym a = s)).card : Real) * B := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- The exact bridge from a full high-entropy estimate back to the sole
anchored obligation. -/
theorem separatedAnchoredCubicMass_le_highEntropy_div (n : Nat) :
    separatedAnchoredCubicMass n ≤
      highEntropyFullCubicMass n / ((2 ^ n : Nat) : Real) := by
  have hfull := separatedFullCubicMass_le_highEntropyFullCubicMass n
  rw [separatedFullCubicMass_eq_card_mul_anchored] at hfull
  have hN : (0 : Real) < ((2 ^ n : Nat) : Real) := by positivity
  exact (le_div_iff₀ hN).2 (by simpa [mul_comm] using hfull)

/-- Exact cubic orbit accounting; as for the fourth moment, the full sum has
exactly `2^n` equal copies of every anchored coefficient. -/
theorem fullInjectionCubicMass_eq_card_mul_anchored (n : Nat) :
    fullInjectionCubicMass n =
      ((2 ^ n : Nat) : Real) * anchoredInjectionCubicMass n := by
  unfold fullInjectionCubicMass anchoredInjectionCubicMass
  apply sum_global_shift_invariant_eq_card_mul_sum_anchored
  intro a gamma
  rw [abs_fourier_injection_density_add_constant_mask_full]

@[simp]
theorem abs_vectorWalsh (n : Nat) (a x : XorSpace n) :
    |vectorWalsh a x| = 1 := by
  exact abs_bitSign _

@[simp]
theorem abs_checkerProduct {n q : Nat} (a : BitMatrix q n)
    (e : Fin q ↪ XorSpace n) :
    |checkerProduct a e| = 1 := by
  unfold checkerProduct
  induction (Finset.univ : Finset (Fin q)) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, abs_mul, ih, abs_vectorWalsh]
      norm_num

/-- Every normalized injection coefficient lies in the unit interval in
absolute value: it is an average of checkerboard signs. -/
theorem abs_checkerCorrelation_le_one {n q : Nat}
    (hq : q ≤ 2 ^ n) (a : BitMatrix q n) :
    |checkerCorrelation a| ≤ 1 := by
  unfold checkerCorrelation average
  have hnonempty : Nonempty (Fin q ↪ XorSpace n) :=
    Function.Embedding.nonempty_of_card_le (by simpa [card_xorSpace] using hq)
  have hcard : (0 : Real) <
      (Fintype.card (Fin q ↪ XorSpace n) : Real) := by
    exact_mod_cast Fintype.card_pos
  rw [abs_div, abs_of_pos hcard]
  calc
    |∑ e : Fin q ↪ XorSpace n, checkerProduct a e| /
          (Fintype.card (Fin q ↪ XorSpace n) : Real) ≤
        (∑ e : Fin q ↪ XorSpace n, |checkerProduct a e|) /
          (Fintype.card (Fin q ↪ XorSpace n) : Real) := by
      exact div_le_div_of_nonneg_right
        (Finset.abs_sum_le_sum_abs _ _) hcard.le
    _ = 1 := by
      simp only [abs_checkerProduct, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      exact div_self hcard.ne'

theorem abs_fourier_injectionDensity_le_one {n q : Nat}
    (hq : q ≤ 2 ^ n) (a : BitMatrix q n) :
    |fourier (injectionDensity n q) a| ≤ 1 := by
  rw [fourier_injectionDensity_eq_average_checkerProduct hq]
  exact abs_checkerCorrelation_le_one hq a

/-- The separated fourth moment is at most a pointwise coefficient bound
times the global cubic mass.  This is the exact finite interpolation used in
the minor-arc argument; no asymptotic constant is hidden here. -/
theorem separatedFullFourthTail_le_pointwise_mul_cubic
    {n : Nat} {A : Real} (hA : 0 ≤ A)
    (hpoint : ∀ a : BitMatrix (2 ^ n) n,
      IsThreeQuarterSeparated a ∧ ¬ IsFullProxyMode a →
        |fourier (injectionDensity n (2 ^ n)) a| ≤ A) :
    separatedFullFourthTail n ≤ A * fullInjectionCubicMass n := by
  unfold separatedFullFourthTail fullInjectionCubicMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _ha
  let c : Real := fourier (injectionDensity n (2 ^ n)) a
  by_cases hsep : IsThreeQuarterSeparated a ∧ ¬ IsFullProxyMode a
  · rw [if_pos hsep]
    have hc := hpoint a hsep
    calc
      c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ = (|c| ^ 2) ^ 2 := by rw [sq_abs]
      _ = |c| * |c| ^ 3 := by ring
      _ ≤ A * |c| ^ 3 := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  · rw [if_neg hsep]
    exact mul_nonneg hA (by positivity)

/-- Orbit quotient plus cubic interpolation.  Compared with the
unquotiented estimate, the anchored tail gains the exact factor `1 / 2^n`. -/
theorem separatedAnchoredFourthTail_le_of_pointwise_cubic
    {n : Nat} {A C : Real} (hA : 0 ≤ A)
    (hpoint : ∀ a : BitMatrix (2 ^ n) n,
      IsThreeQuarterSeparated a ∧ ¬ IsFullProxyMode a →
        |fourier (injectionDensity n (2 ^ n)) a| ≤ A)
    (hcubic : fullInjectionCubicMass n ≤ C) :
    separatedAnchoredFourthTail n ≤
      A * C / ((2 ^ n : Nat) : Real) := by
  have hfull := separatedFullFourthTail_le_pointwise_mul_cubic hA hpoint
  have hAC : separatedFullFourthTail n ≤ A * C :=
    hfull.trans (mul_le_mul_of_nonneg_left hcubic hA)
  rw [separatedFullFourthTail_eq_card_mul_anchored] at hAC
  have hN : (0 : Real) < ((2 ^ n : Nat) : Real) := by positivity
  exact (le_div_iff₀ hN).2 (by simpa [mul_comm] using hAC)

/-- Quotient-native form of the same interpolation.  It avoids introducing
and then cancelling the common orbit factor. -/
theorem separatedAnchoredFourthTail_le_pointwise_mul_anchoredCubic
    {n : Nat} {A : Real} (hA : 0 ≤ A)
    (hpoint : ∀ b : AnchoredMask n,
      IsThreeQuarterSeparated b.1 ∧ ¬ IsFullProxyMode b.1 →
        |fourier (injectionDensity n (2 ^ n)) b.1| ≤ A) :
    separatedAnchoredFourthTail n ≤
      A * anchoredInjectionCubicMass n := by
  unfold separatedAnchoredFourthTail anchoredInjectionCubicMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _hb
  let c : Real := fourier (injectionDensity n (2 ^ n)) b.1
  by_cases hsep : IsThreeQuarterSeparated b.1 ∧ ¬ IsFullProxyMode b.1
  · rw [if_pos hsep]
    have hc := hpoint b hsep
    calc
      c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ = (|c| ^ 2) ^ 2 := by rw [sq_abs]
      _ = |c| * |c| ^ 3 := by ring
      _ ≤ A * |c| ^ 3 := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  · rw [if_neg hsep]
    exact mul_nonneg hA (by positivity)

/-- Tight restricted interpolation.  This form shows that the high-query
proof needs only a separated cubic estimate, not Eberhard's stronger global
cubic theorem. -/
theorem separatedAnchoredFourthTail_le_pointwise_mul_separatedCubic
    {n : Nat} {A : Real}
    (hpoint : ∀ b : AnchoredMask n,
      IsThreeQuarterSeparated b.1 ∧ ¬ IsFullProxyMode b.1 →
        |fourier (injectionDensity n (2 ^ n)) b.1| ≤ A) :
    separatedAnchoredFourthTail n ≤
      A * separatedAnchoredCubicMass n := by
  unfold separatedAnchoredFourthTail separatedAnchoredCubicMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _hb
  let c : Real := fourier (injectionDensity n (2 ^ n)) b.1
  by_cases hsep : IsThreeQuarterSeparated b.1 ∧ ¬ IsFullProxyMode b.1
  · rw [if_pos hsep, if_pos hsep]
    have hc := hpoint b hsep
    calc
      c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ = (|c| ^ 2) ^ 2 := by rw [sq_abs]
      _ = |c| * |c| ^ 3 := by ring
      _ ≤ A * |c| ^ 3 := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
  · simp [hsep]

/-- The fourth-moment target is already bounded by the separated cubic mass.
Thus a direct high-entropy cubic estimate is a one-obligation route to the
remaining tail, bypassing the stronger global cubic theorem. -/
theorem separatedAnchoredFourthTail_le_separatedAnchoredCubicMass
    (n : Nat) :
    separatedAnchoredFourthTail n ≤ separatedAnchoredCubicMass n := by
  have h := separatedAnchoredFourthTail_le_pointwise_mul_separatedCubic
    (n := n) (A := 1) (fun b _hsep =>
      abs_fourier_injectionDensity_le_one (le_refl (2 ^ n)) b.1)
  simpa using h

/-- Constant-preserving specialization of the previous theorem.  A
`pointwiseConstant / N^3` minor-arc estimate and a
`cubicConstant * N` global cubic estimate leave only
`pointwiseConstant * cubicConstant / N^3` in the quotient. -/
theorem separatedAnchoredFourthTail_le_scaled_cubic
    {n : Nat} {pointwiseConstant cubicConstant : Real}
    (hpointwiseConstant : 0 ≤ pointwiseConstant)
    (hpoint : ∀ a : BitMatrix (2 ^ n) n,
      IsThreeQuarterSeparated a ∧ ¬ IsFullProxyMode a →
        |fourier (injectionDensity n (2 ^ n)) a| ≤
          pointwiseConstant / (((2 ^ n : Nat) : Real) ^ 3))
    (hcubic : fullInjectionCubicMass n ≤
      cubicConstant * ((2 ^ n : Nat) : Real)) :
    separatedAnchoredFourthTail n ≤
      pointwiseConstant * cubicConstant /
        (((2 ^ n : Nat) : Real) ^ 3) := by
  have hN : ((2 ^ n : Nat) : Real) ≠ 0 := by positivity
  have hA : 0 ≤
      pointwiseConstant / (((2 ^ n : Nat) : Real) ^ 3) := by positivity
  have h := separatedAnchoredFourthTail_le_of_pointwise_cubic
    hA hpoint hcubic
  calc
    separatedAnchoredFourthTail n ≤
        (pointwiseConstant / (((2 ^ n : Nat) : Real) ^ 3)) *
          (cubicConstant * ((2 ^ n : Nat) : Real)) /
            ((2 ^ n : Nat) : Real) := h
    _ = pointwiseConstant * cubicConstant /
          (((2 ^ n : Nat) : Real) ^ 3) := by field_simp

/-! ## The single remaining analytic input

These consumer lemmas make the boundary explicit: closing any finite bound on
`separatedAnchoredFourthTail` immediately closes the entire full-deck signed
residual.  No representative or conditioning statement remains below this
point.
-/

/-- The already-closed contribution of quotient profiles having a row value
of multiplicity greater than three quarters. -/
def quotientSparseEnergyBound (n : Nat) : Real :=
  16 * (((2 ^ n).choose 3 : Nat) : Real) /
      ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
        (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
    (580 / 3 : Real) / (((2 ^ n : Nat) : Real) ^ 2)

theorem deepMajorityCoverEnergy_le_quotientSparseEnergyBound
    {n : Nat} (hn : 10 ≤ n) :
    deepMajorityCoverEnergy n ≤ quotientSparseEnergyBound n := by
  exact deepMajorityCoverEnergy_le hn

/-- A bound for the separated profiles is the only input needed to bound the
complete quotient fourth moment. -/
theorem anchoredInjectionFourthTail_le_of_separated
    {n : Nat} (hn : 10 ≤ n) {B : Real}
    (hseparated : separatedAnchoredFourthTail n ≤ B) :
    anchoredInjectionFourthTail n ≤
      quotientSparseEnergyBound n + B := by
  exact (anchoredInjectionFourthTail_le_deepMajority_add_separated n).trans
    (add_le_add (deepMajorityCoverEnergy_le_quotientSparseEnergyBound hn)
      hseparated)

/-- Operational full-deck residual endpoint, conditional only on the named
separated-profile estimate. -/
theorem fullResidualAdvantage_le_of_separated
    {n : Nat} (hn : 10 ≤ n) {B : Real}
    (hseparated : separatedAnchoredFourthTail n ≤ B) :
    fullResidualAdvantage n ≤
      (1 / 2 : Real) * Real.sqrt (quotientSparseEnergyBound n + B) := by
  apply full_residual_advantage_le_of_anchored_energy
  rw [anchoredResidualEnergy_eq_injectionFourthTail (by omega)]
  exact anchoredInjectionFourthTail_le_of_separated hn hseparated

/-- Operational endpoint in the exact normalization of Eberhard's two
minor-arc inputs.  Supplying the two constants closes the full-deck residual
without any further representative, orbit, or norm argument. -/
theorem fullResidualAdvantage_le_of_pointwise_cubic
    {n : Nat} (hn : 10 ≤ n)
    {pointwiseConstant cubicConstant : Real}
    (hpointwiseConstant : 0 ≤ pointwiseConstant)
    (hpoint : ∀ a : BitMatrix (2 ^ n) n,
      IsThreeQuarterSeparated a ∧ ¬ IsFullProxyMode a →
        |fourier (injectionDensity n (2 ^ n)) a| ≤
          pointwiseConstant / (((2 ^ n : Nat) : Real) ^ 3))
    (hcubic : fullInjectionCubicMass n ≤
      cubicConstant * ((2 ^ n : Nat) : Real)) :
    fullResidualAdvantage n ≤
      (1 / 2 : Real) * Real.sqrt
        (quotientSparseEnergyBound n +
          pointwiseConstant * cubicConstant /
            (((2 ^ n : Nat) : Real) ^ 3)) := by
  apply fullResidualAdvantage_le_of_separated hn
  exact separatedAnchoredFourthTail_le_scaled_cubic
    hpointwiseConstant hpoint hcubic

/-- Most constrained operational endpoint: a bound on only the separated
anchored cubic mass closes the full residual.  This avoids both a separate
pointwise theorem and a global cubic-mass theorem. -/
theorem fullResidualAdvantage_le_of_separated_cubic
    {n : Nat} (hn : 10 ≤ n) {B : Real}
    (hcubic : separatedAnchoredCubicMass n ≤ B) :
    fullResidualAdvantage n ≤
      (1 / 2 : Real) * Real.sqrt (quotientSparseEnergyBound n + B) := by
  apply fullResidualAdvantage_le_of_separated hn
  exact separatedAnchoredFourthTail_le_separatedAnchoredCubicMass n |>.trans
    hcubic

end RandomSystems.SoP.XORComplement
