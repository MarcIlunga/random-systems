/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORSignedDegreeThree
import RandomSystems.SoP.XORCoefficient

/-!
# Exact signed degree-four truncation for XOR SoP

This module exposes and classifies the exact four-row checkerboard
coefficient, then retains that signed Fourier level before taking the L1 norm.
The classification has one genuinely new branch: four distinct masks can form
an affine parallelogram, witnessed by their XOR being zero.  Thus degree four
is not determined by visible collision multiplicities alone.

The retained certificate is still fully finite and operational.  Its center is
the exact half-L1 norm of levels two through four, and its closed uncertainty
radius starts at level five.  Relative to the degree-three certificate, the
medium-level energy coefficient contracts from 1152/7 to 144/7.
-/

noncomputable section
open scoped BigOperators

namespace RandomSystems.SoP.XORSignedDegreeFour

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.XORTail
open RandomSystems.SoP.XORCoefficient
open RandomSystems.SoP.XORSignedTruncation
open RandomSystems.SoP.XORSignedDegreeThree

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def fourMask {n : Nat} (a b c d : XorSpace n) : BitMatrix 4 n :=
  ![a, b, c, d]

@[simp]
theorem walsh_four_mask {n : Nat} (a b c d : XorSpace n)
    (x : BitMatrix 4 n) :
    walsh (fourMask a b c d) x =
      vectorWalsh a (x 0) * vectorWalsh b (x 1) *
        vectorWalsh c (x 2) * vectorWalsh d (x 3) := by
  have hdot : dot (fourMask a b c d) x =
      vectorDot a (x 0) + vectorDot b (x 1) +
        vectorDot c (x 2) + vectorDot d (x 3) := by
    unfold dot
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [fourMask, vectorDot]
    abel
  unfold walsh
  rw [hdot]
  simp [vectorWalsh, bitSign_add]

theorem checker_correlation_three_first
    {n : Nat} (hN : 3 ≤ 2 ^ n) (x c d : XorSpace n)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    checkerCorrelation (threeMask x c d) =
      if x = 0 then
        if c = d then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
      else if x + c + d = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real))
      else 0 := by
  have hcorr : checkerCorrelation (threeMask x c d) =
      fourier (injectionDensity n 3) (threeMask x c d) := by
    symm
    exact fourier_injectionDensity_eq_average_checkerProduct hN
      (threeMask x c d)
  rw [hcorr]
  by_cases hx : x = 0
  · rw [if_pos hx]
    subst x
    have hlevel : level (threeMask 0 c d) = 2 := by
      have hsupp : rowSupport (threeMask 0 c d) =
          (Finset.univ : Finset (Fin 3)).erase 0 := by
        ext i
        fin_cases i <;> simp [rowSupport, threeMask, hc, hd]
      unfold level
      rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ 0)]
      simp
    rw [fourier_injectionDensity_of_level_eq_two hN
      (threeMask 0 c d) hlevel]
    have heq : supportRowsEqual (threeMask 0 c d) ↔ c = d := by
      constructor
      · intro h
        exact h 1 (by simp [rowSupport, threeMask, hc])
          2 (by simp [rowSupport, threeMask, hd])
      · intro h
        subst d
        intro i hi j hj
        fin_cases i <;> fin_cases j <;>
          simp [rowSupport, threeMask, hc] at hi hj ⊢
    simp only [heq]
  · rw [if_neg hx]
    have hlevel : level (threeMask x c d) = 3 := by
      have hsupp : rowSupport (threeMask x c d) = Finset.univ := by
        ext i
        fin_cases i <;> simp [rowSupport, threeMask, hx, hc, hd]
      unfold level
      rw [hsupp]
      simp
    rw [fourier_injectionDensity_of_level_eq_three hN
      (threeMask x c d) hlevel]
    have hsum : maskRowSum (threeMask x c d) = x + c + d := by
      unfold maskRowSum
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
        Fin.sum_univ_zero]
      simp [threeMask]
      abel
    rw [hsum]

theorem checker_correlation_three_middle
    {n : Nat} (hN : 3 ≤ 2 ^ n) (a x d : XorSpace n)
    (ha : a ≠ 0) (hd : d ≠ 0) :
    checkerCorrelation (threeMask a x d) =
      if x = 0 then
        if a = d then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
      else if a + x + d = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real))
      else 0 := by
  have hcorr : checkerCorrelation (threeMask a x d) =
      fourier (injectionDensity n 3) (threeMask a x d) := by
    symm
    exact fourier_injectionDensity_eq_average_checkerProduct hN
      (threeMask a x d)
  rw [hcorr]
  by_cases hx : x = 0
  · rw [if_pos hx]
    subst x
    have hlevel : level (threeMask a 0 d) = 2 := by
      have hsupp : rowSupport (threeMask a 0 d) =
          (Finset.univ : Finset (Fin 3)).erase 1 := by
        ext i
        fin_cases i <;> simp [rowSupport, threeMask, ha, hd]
      unfold level
      rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ 1)]
      simp
    rw [fourier_injectionDensity_of_level_eq_two hN
      (threeMask a 0 d) hlevel]
    have heq : supportRowsEqual (threeMask a 0 d) ↔ a = d := by
      constructor
      · intro h
        exact h 0 (by simp [rowSupport, threeMask, ha])
          2 (by simp [rowSupport, threeMask, hd])
      · intro h
        subst d
        intro i hi j hj
        fin_cases i <;> fin_cases j <;>
          simp [rowSupport, threeMask, ha] at hi hj ⊢
    simp only [heq]
  · rw [if_neg hx]
    have hlevel : level (threeMask a x d) = 3 := by
      have hsupp : rowSupport (threeMask a x d) = Finset.univ := by
        ext i
        fin_cases i <;> simp [rowSupport, threeMask, ha, hx, hd]
      unfold level
      rw [hsupp]
      simp
    rw [fourier_injectionDensity_of_level_eq_three hN
      (threeMask a x d) hlevel]
    have hsum : maskRowSum (threeMask a x d) = a + x + d := by
      unfold maskRowSum
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
        Fin.sum_univ_zero]
      simp [threeMask]
      abel
    rw [hsum]

theorem checker_correlation_three_last
    {n : Nat} (hN : 3 ≤ 2 ^ n) (a b x : XorSpace n)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    checkerCorrelation (threeMask a b x) =
      if x = 0 then
        if a = b then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
      else if a + b + x = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real))
      else 0 := by
  have hcorr : checkerCorrelation (threeMask a b x) =
      fourier (injectionDensity n 3) (threeMask a b x) := by
    symm
    exact fourier_injectionDensity_eq_average_checkerProduct hN
      (threeMask a b x)
  rw [hcorr]
  by_cases hx : x = 0
  · rw [if_pos hx]
    subst x
    have hlevel : level (threeMask a b 0) = 2 := by
      have hsupp : rowSupport (threeMask a b 0) =
          (Finset.univ : Finset (Fin 3)).erase 2 := by
        ext i
        fin_cases i <;> simp [rowSupport, threeMask, ha, hb]
      unfold level
      rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ 2)]
      simp
    rw [fourier_injectionDensity_of_level_eq_two hN
      (threeMask a b 0) hlevel]
    have heq : supportRowsEqual (threeMask a b 0) ↔ a = b := by
      constructor
      · intro h
        exact h 0 (by simp [rowSupport, threeMask, ha])
          1 (by simp [rowSupport, threeMask, hb])
      · intro h
        subst b
        intro i hi j hj
        fin_cases i <;> fin_cases j <;>
          simp [rowSupport, threeMask, ha] at hi hj ⊢
    simp only [heq]
  · rw [if_neg hx]
    have hlevel : level (threeMask a b x) = 3 := by
      have hsupp : rowSupport (threeMask a b x) = Finset.univ := by
        ext i
        fin_cases i <;> simp [rowSupport, threeMask, ha, hb, hx]
      unfold level
      rw [hsupp]
      simp
    rw [fourier_injectionDensity_of_level_eq_three hN
      (threeMask a b x) hlevel]
    have hsum : maskRowSum (threeMask a b x) = a + b + x := by
      unfold maskRowSum
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
        Fin.sum_univ_zero]
      simp [threeMask]
      abel
    rw [hsum]

@[simp]
theorem merge_head_four_mask_zero {n : Nat} (a b c d : XorSpace n) :
    mergeHead (fourMask a b c d) (0 : Fin 3) = threeMask (a + b) c d := by
  funext i j
  fin_cases i <;> simp [mergeHead, tailMask, fourMask, threeMask]

@[simp]
theorem merge_head_four_mask_one {n : Nat} (a b c d : XorSpace n) :
    mergeHead (fourMask a b c d) (1 : Fin 3) = threeMask b (a + c) d := by
  funext i j
  fin_cases i <;> simp [mergeHead, tailMask, fourMask, threeMask]

@[simp]
theorem merge_head_four_mask_two {n : Nat} (a b c d : XorSpace n) :
    mergeHead (fourMask a b c d) (2 : Fin 3) = threeMask b c (a + d) := by
  funext i j
  fin_cases i <;> simp [mergeHead, tailMask, fourMask, threeMask]

def fourCoefficient {n : Nat} (a b c d : XorSpace n) : Real :=
  -(1 / (((2 ^ n - 3 : Nat) : Real))) *
    ((if a = b then
        if c = d then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
      else if a + b + c + d = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real))
      else 0) +
    (if a = c then
        if b = d then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
      else if a + b + c + d = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real))
      else 0) +
    (if a = d then
        if b = c then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
      else if a + b + c + d = 0 then
        2 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real))
      else 0))

theorem checker_correlation_four_mask_eq_four_coefficient
    {n : Nat} (hN : 4 ≤ 2 ^ n) (a b c d : XorSpace n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    checkerCorrelation (fourMask a b c d) = fourCoefficient a b c d := by
  rw [checkerCorrelation_succ_eq (k := 3) hN (fourMask a b c d) (by
    simpa [fourMask] using ha)]
  rw [Fin.sum_univ_three, merge_head_four_mask_zero,
    merge_head_four_mask_one, merge_head_four_mask_two]
  rw [checker_correlation_three_first (by omega) (a + b) c d hc hd,
    checker_correlation_three_middle (by omega) b (a + c) d hb hd,
    checker_correlation_three_last (by omega) b c (a + d) hb hc]
  have hsum2 : b + (a + c) + d = a + b + c + d := by abel
  have hsum3 : b + c + (a + d) = a + b + c + d := by abel
  rw [hsum2, hsum3]
  unfold fourCoefficient
  simp only [xorSpace_add_eq_zero_iff_eq]

def fourAllEqual {n : Nat} (a b c d : XorSpace n) : Prop :=
  a = b ∧ a = c ∧ a = d

def fourPairPaired {n : Nat} (a b c d : XorSpace n) : Prop :=
  (a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem four_coefficient_eq_pattern
    {n : Nat} (hN : 4 ≤ 2 ^ n) (a b c d : XorSpace n) :
    fourCoefficient a b c d =
      if fourAllEqual a b c d then
        3 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 3 : Nat) : Real))
      else if fourPairPaired a b c d then
        (((2 ^ n : Nat) : Real) - 6) /
          (((2 ^ n - 1 : Nat) : Real) *
            ((2 ^ n - 2 : Nat) : Real) *
            ((2 ^ n - 3 : Nat) : Real))
      else if a + b + c + d = 0 then
        -6 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real) *
          ((2 ^ n - 3 : Nat) : Real))
      else 0 := by
  have hN1 : ((2 ^ n - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : 2 ^ n - 1 ≠ 0)
  have hN2 : ((2 ^ n - 2 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : 2 ^ n - 2 ≠ 0)
  have hN3 : ((2 ^ n - 3 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : 2 ^ n - 3 ≠ 0)
  have hcast1 : ((2 ^ n - 1 : Nat) : Real) = (2 ^ n : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ n)]
    norm_num
  have hcast2 : ((2 ^ n - 2 : Nat) : Real) = (2 ^ n : Real) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ n)]
    norm_num
  have hcast3 : ((2 ^ n - 3 : Nat) : Real) = (2 ^ n : Real) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ 2 ^ n)]
    norm_num
  by_cases hall : fourAllEqual a b c d
  · rcases hall with ⟨hab, hac, had⟩
    subst b
    subst c
    subst d
    simp [fourCoefficient, fourAllEqual, hcast1, hcast3]
    field_simp [hN1, hN3]
    ring
  · rw [if_neg hall]
    by_cases hpair : fourPairPaired a b c d
    · rw [if_pos hpair]
      rcases hpair with hp | hp | hp
      · rcases hp with ⟨hab, hcd⟩
        subst b
        subst d
        have hac : a ≠ c := by
          intro h
          apply hall
          simp [fourAllEqual, h]
        simp [fourCoefficient, hac, xorSpace_add_self_eq_zero]
        field_simp [hN1, hN2, hN3]
        rw [hcast2]
        ring
      · rcases hp with ⟨hac, hbd⟩
        subst c
        subst d
        have hab : a ≠ b := by
          intro h
          apply hall
          simp [fourAllEqual, h]
        have hsum : a + b + a + b = 0 := by
          calc
            a + b + a + b = (a + a) + (b + b) := by abel
            _ = 0 := by simp
        simp [fourCoefficient, hab, hsum]
        field_simp [hN1, hN2, hN3]
        rw [hcast2]
        ring
      · rcases hp with ⟨had, hbc⟩
        subst d
        subst c
        have hab : a ≠ b := by
          intro h
          apply hall
          simp [fourAllEqual, h]
        have hsum : a + b + b + a = 0 := by
          calc
            a + b + b + a = (a + a) + (b + b) := by abel
            _ = 0 := by simp
        simp [fourCoefficient, hab, hsum]
        field_simp [hN1, hN2, hN3]
        rw [hcast2]
        ring
    · rw [if_neg hpair]
      by_cases hsum : a + b + c + d = 0
      · rw [if_pos hsum]
        have hab : a ≠ b := by
          intro hab
          apply hpair
          left
          refine ⟨hab, ?_⟩
          subst b
          have hcd0 : c + d = 0 := by
            simpa [xorSpace_add_self_eq_zero, add_assoc] using hsum
          exact (xorSpace_add_eq_zero_iff_eq c d).mp hcd0
        have hac : a ≠ c := by
          intro hac
          apply hpair
          right; left
          refine ⟨hac, ?_⟩
          subst c
          have hreorder : a + b + a + d = b + d := by
            calc
              a + b + a + d = (a + a) + (b + d) := by abel
              _ = b + d := by rw [xorSpace_add_self_eq_zero]; simp
          rw [hreorder] at hsum
          exact (xorSpace_add_eq_zero_iff_eq b d).mp hsum
        have had : a ≠ d := by
          intro had
          apply hpair
          right; right
          refine ⟨had, ?_⟩
          subst d
          have hreorder : a + b + c + a = b + c := by
            calc
              a + b + c + a = (a + a) + (b + c) := by abel
              _ = b + c := by rw [xorSpace_add_self_eq_zero]; simp
          rw [hreorder] at hsum
          exact (xorSpace_add_eq_zero_iff_eq b c).mp hsum
        simp [fourCoefficient, hab, hac, had, hsum]
        field_simp [hN1, hN2, hN3]
        ring
      · rw [if_neg hsum]
        have hfirst :
            (if a = b then
              if c = d then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
            else if a + b + c + d = 0 then
              2 / (((2 ^ n - 1 : Nat) : Real) *
                ((2 ^ n - 2 : Nat) : Real))
            else 0) = 0 := by
          by_cases hab : a = b
          · have hcd : c ≠ d := by
              intro hcd
              exact hpair (Or.inl ⟨hab, hcd⟩)
            simp [hab, hcd]
          · simp [hab, hsum]
        have hsecond :
            (if a = c then
              if b = d then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
            else if a + b + c + d = 0 then
              2 / (((2 ^ n - 1 : Nat) : Real) *
                ((2 ^ n - 2 : Nat) : Real))
            else 0) = 0 := by
          by_cases hac : a = c
          · have hbd : b ≠ d := by
              intro hbd
              exact hpair (Or.inr (Or.inl ⟨hac, hbd⟩))
            simp [hac, hbd]
          · simp [hac, hsum]
        have hthird :
            (if a = d then
              if b = c then -(1 / (((2 ^ n - 1 : Nat) : Real))) else 0
            else if a + b + c + d = 0 then
              2 / (((2 ^ n - 1 : Nat) : Real) *
                ((2 ^ n - 2 : Nat) : Real))
            else 0) = 0 := by
          by_cases had : a = d
          · have hbc : b ≠ c := by
              intro hbc
              exact hpair (Or.inr (Or.inr ⟨had, hbc⟩))
            simp [had, hbc]
          · simp [had, hsum]
        unfold fourCoefficient
        rw [hfirst, hsecond, hthird]
        ring

/-- Exact four-row Fourier coefficient.  Besides equality patterns, the
all-distinct branch detects affine parallelograms through `a+b+c+d=0`. -/
theorem fourier_injectionDensity_four_mask_eq_pattern
    {n : Nat} (hN : 4 ≤ 2 ^ n) (a b c d : XorSpace n)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    fourier (injectionDensity n 4) (fourMask a b c d) =
      if fourAllEqual a b c d then
        3 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 3 : Nat) : Real))
      else if fourPairPaired a b c d then
        (((2 ^ n : Nat) : Real) - 6) /
          (((2 ^ n - 1 : Nat) : Real) *
            ((2 ^ n - 2 : Nat) : Real) *
            ((2 ^ n - 3 : Nat) : Real))
      else if a + b + c + d = 0 then
        -6 / (((2 ^ n - 1 : Nat) : Real) *
          ((2 ^ n - 2 : Nat) : Real) *
          ((2 ^ n - 3 : Nat) : Real))
      else 0 := by
  rw [fourier_injectionDensity_eq_average_checkerProduct hN]
  change checkerCorrelation (fourMask a b c d) = _
  rw [checker_correlation_four_mask_eq_four_coefficient hN a b c d
      ha hb hc hd,
    four_coefficient_eq_pattern hN a b c d]

/-- Exact signed density contributed by row level four. -/
def levelFourDensity (n q : Nat) : BitMatrix q n → Real :=
  spectralPart (fun a : BitMatrix q n => level a = 4)
    (convolution (injectionDensity n q) (injectionDensity n q))

/-- Retaining level four means adding its signed contribution before taking
the absolute value; no triangle inequality is spent between levels. -/
theorem signed_truncation_density_five_eq_four_plus_level_four
    {n q : Nat} (y : BitMatrix q n) :
    signedTruncationDensity n q 5 y =
      signedTruncationDensity n q 4 y + levelFourDensity n q y := by
  unfold signedTruncationDensity levelFourDensity spectralPart
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h4 : level a = 4
  · simp [h4]
  · by_cases hrange : 2 ≤ level a ∧ level a < 4
    · have hrange5 : 2 ≤ level a ∧ level a < 5 := by omega
      simp [h4, hrange, hrange5]
    · have hnotrange5 : ¬(2 ≤ level a ∧ level a < 5) := by omega
      simp [h4, hrange, hnotrange5]

/-- Half-L1 norm of the exact signed levels two through four. -/
def signedDegreeFourAdvantage (n q : Nat) : Real :=
  signedTruncationAdvantage n q 5

/-- Closed radius for the unretained level-five-and-higher tail. -/
def signedDegreeFourError (n q : Nat) : Real :=
  (1 / 2 : Real) * Real.sqrt
    ((144 / 7 : Real) * (q : Real) ^ 4 /
        (((2 ^ n : Nat) : Real) ^ 6) +
      8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8))

@[simp]
theorem signed_tail_error_bound_five_eq_signed_degree_four_error
    (n q : Nat) :
    signedTailErrorBound n q 5 = signedDegreeFourError n q := by
  unfold signedTailErrorBound signedTailEnergyBound signedDegreeFourError
  norm_num
  ring

/-- Retaining the exact fourth level contracts the geometric part of the
certified uncertainty radius by another factor of eight in energy. -/
theorem signed_degree_four_error_le_signed_degree_three_error
    (n q : Nat) :
    signedDegreeFourError n q ≤ signedDegreeThreeError n q := by
  unfold signedDegreeFourError signedDegreeThreeError
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  have hx : 0 ≤ (q : Real) ^ 4 /
      (((2 ^ n : Nat) : Real) ^ 6) := by positivity
  have hcoeff : (144 / 7 : Real) ≤ 1152 / 7 := by norm_num
  have hmul := mul_le_mul_of_nonneg_right hcoeff hx
  calc
    (144 / 7 : Real) * (q : Real) ^ 4 /
          (((2 ^ n : Nat) : Real) ^ 6) +
        8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8) =
      (144 / 7 : Real) *
          ((q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6)) +
        8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8) := by ring
    _ ≤ (1152 / 7 : Real) *
          ((q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6)) +
        8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8) :=
      add_le_add hmul (le_refl _)
    _ = (1152 / 7 : Real) * (q : Real) ^ 4 /
          (((2 ^ n : Nat) : Real) ^ 6) +
        8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8) := by ring

/-- Fully operational two-sided certificate after the exact degree-four
coefficient has been retained. -/
theorem abs_advantage_sub_signed_degree_four_advantage_le_error
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    |RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        signedDegreeFourAdvantage n q| ≤
      signedDegreeFourError n q := by
  unfold signedDegreeFourAdvantage
  rw [← signed_tail_error_bound_five_eq_signed_degree_four_error]
  exact abs_advantage_sub_signed_truncation_advantage_le_error_bound
    (r := 5) hn h2q (by omega) (by omega)

/-- One-sided form of the retained-degree-four certificate. -/
theorem adaptive_transcript_advantage_le_signed_degree_four_add_error
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
      signedDegreeFourAdvantage n q + signedDegreeFourError n q := by
  unfold signedDegreeFourAdvantage
  rw [← signed_tail_error_bound_five_eq_signed_degree_four_error]
  exact adaptive_transcript_advantage_le_signed_truncation_add_error_bound
    (r := 5) hn h2q (by omega) (by omega)

end RandomSystems.SoP.XORSignedDegreeFour
