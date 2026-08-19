/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORComplementMultiplicity
import RandomSystems.SoP.XORPascal

/-!
# Explicit sparse quotient tail beyond the half-domain barrier

The full-deck quotient spectrum is split at multiplicity `3N/4`.  A character
value occurring more often than that can be translated to zero, leaving
support below `N/4`.  The normalized Pascal bounds then give a geometric tail
with no asymptotic notation:

* levels through `4n+1` contribute at most `192/N^2`;
* all remaining levels below `N/4` contribute at most `4/(3N^2)`;
* level three is retained exactly.

Consequently the whole deep-majority contribution is bounded by the exact
level-three energy plus `(580/3)/N^2`.  What remains is a single separated
minor-arc sum: no row value has multiplicity greater than `3N/4`.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORComplement

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.XORTail
open RandomSystems.SoP.XORPascal
open RandomSystems.SoP.XORBounds
open RandomSystems.SoP.XORCoefficient

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem fullDomainLevelEnergy_le_fullSecondEnergy {n k : Nat}
    (hhalf : 2 * k ≤ 2 ^ n) :
    injectionLevelEnergy n (2 ^ n) k ≤ fullSecondEnergy n k := by
  have h := injectionLevelEnergy_le_choose_ratio_mul_fullSecondEnergy
    (n := n) (q := 2 ^ n) (k := k) (le_refl _) hhalf
  have hk : k ≤ 2 ^ n := by omega
  have hchoose : (((2 ^ n).choose k : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  convert h using 1
  field_simp [hchoose]

theorem descFactorial_quarter_lower {N k : Nat} (hk : 4 * k ≤ N) :
    (((3 : Real) * (N : Real) / 4) ^ k) ≤
      ((N.descFactorial k : Nat) : Real) := by
  have hbaseNat : 3 * N ≤ 4 * (N + 1 - k) := by omega
  have hbase : (3 : Real) * (N : Real) / 4 ≤
      ((N + 1 - k : Nat) : Real) := by
    have hbaseR : (3 : Real) * (N : Real) ≤
        4 * ((N + 1 - k : Nat) : Real) := by exact_mod_cast hbaseNat
    linarith
  calc
    ((3 : Real) * (N : Real) / 4) ^ k ≤
        (((N + 1 - k : Nat) : Real)) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ ((N.descFactorial k : Nat) : Real) := by
      exact_mod_cast N.pow_sub_le_descFactorial k

theorem fullSecondEnergy_even_le_four_ninths {n m : Nat}
    (hquarter : 4 * (2 * m) ≤ 2 ^ n) :
    fullSecondEnergy n (2 * m) ≤ (4 / 9 : Real) ^ m := by
  let N : Nat := 2 ^ n
  have hpas := fullSecondEnergy_even_le (n := n) (m := m) (by omega)
  have hden := descFactorial_quarter_lower (N := N) (k := 2 * m)
    (by simpa [N] using hquarter)
  have hNpos : 0 < (N : Real) := by dsimp [N]; positivity
  have hbasePos : 0 < ((3 : Real) * (N : Real) / 4) ^ (2 * m) := by
    positivity
  have hnum :
      (((N : Real) * ((2 * m - 1 : Nat) : Real)) ^ m) ≤
        (((N : Real) * ((N : Real) / 4)) ^ m) := by
    gcongr
    have hmNat : 4 * (2 * m - 1) ≤ N := by omega
    have hmR : 4 * ((2 * m - 1 : Nat) : Real) ≤ (N : Real) := by
      exact_mod_cast hmNat
    linarith
  calc
    fullSecondEnergy n (2 * m) ≤
        (((N : Real) * ((2 * m - 1 : Nat) : Real)) ^ m) /
          ((N.descFactorial (2 * m) : Nat) : Real) := by
      simpa [N] using hpas
    _ ≤ (((N : Real) * ((2 * m - 1 : Nat) : Real)) ^ m) /
          (((3 : Real) * (N : Real) / 4) ^ (2 * m)) :=
      div_le_div_of_nonneg_left (by positivity) hbasePos hden
    _ ≤ (((N : Real) * ((N : Real) / 4)) ^ m) /
          (((3 : Real) * (N : Real) / 4) ^ (2 * m)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (4 / 9 : Real) ^ m := by
      rw [pow_mul]
      rw [← div_pow]
      congr 1
      field_simp [hNpos.ne']
      ring

theorem fullSecondEnergy_odd_le_four_ninths {n m : Nat}
    (hquarter : 4 * (2 * m + 1) ≤ 2 ^ n) :
    fullSecondEnergy n (2 * m + 1) ≤
      (1 / 3 : Real) * (4 / 9 : Real) ^ m := by
  let N : Nat := 2 ^ n
  have hpas := fullSecondEnergy_odd_le (n := n) (m := m) (by omega)
  have hden := descFactorial_quarter_lower (N := N) (k := 2 * m + 1)
    (by simpa [N] using hquarter)
  have hNpos : 0 < (N : Real) := by dsimp [N]; positivity
  have hbasePos : 0 < ((3 : Real) * (N : Real) / 4) ^ (2 * m + 1) := by
    positivity
  have hmNat : 4 * (2 * m) ≤ N := by omega
  have hmR : ((2 * m : Nat) : Real) ≤ (N : Real) / 4 := by
    have : 4 * ((2 * m : Nat) : Real) ≤ (N : Real) := by exact_mod_cast hmNat
    linarith
  have hnum :
      ((((N : Real) * ((2 * m : Nat) : Real)) ^ m) *
          ((2 * m : Nat) : Real)) ≤
        (((N : Real) * ((N : Real) / 4)) ^ m) *
          ((N : Real) / 4) := by
    gcongr
  calc
    fullSecondEnergy n (2 * m + 1) ≤
        (((N : Real) * ((2 * m : Nat) : Real)) ^ m *
          ((2 * m : Nat) : Real)) /
          ((N.descFactorial (2 * m + 1) : Nat) : Real) := by
      simpa [N] using hpas
    _ ≤ (((N : Real) * ((2 * m : Nat) : Real)) ^ m *
          ((2 * m : Nat) : Real)) /
          (((3 : Real) * (N : Real) / 4) ^ (2 * m + 1)) :=
      div_le_div_of_nonneg_left (by positivity) hbasePos hden
    _ ≤ ((((N : Real) * ((N : Real) / 4)) ^ m) *
          ((N : Real) / 4)) /
          (((3 : Real) * (N : Real) / 4) ^ (2 * m + 1)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (1 / 3 : Real) * (4 / 9 : Real) ^ m := by
      rw [pow_add, pow_mul]
      have hbase : (3 * (N : Real) / 4) ≠ 0 := by positivity
      calc
        ((N : Real) * ((N : Real) / 4)) ^ m * ((N : Real) / 4) /
              (((3 * (N : Real) / 4) ^ 2) ^ m *
                (3 * (N : Real) / 4) ^ 1) =
            ((((N : Real) * ((N : Real) / 4)) /
                ((3 * (N : Real) / 4) ^ 2)) ^ m) *
              (((N : Real) / 4) / (3 * (N : Real) / 4)) := by
            rw [div_pow]
            field_simp [hbase]
            rw [← mul_pow]
            congr 1
            ring
        _ = (4 / 9 : Real) ^ m * (1 / 3 : Real) := by
          congr 1
          · field_simp [hNpos.ne']
            ring
          · field_simp [hNpos.ne']
        _ = (1 / 3 : Real) * (4 / 9 : Real) ^ m := by ring

theorem fullSecondEnergy_le_two_thirds_pow {n k : Nat}
    (hquarter : 4 * k ≤ 2 ^ n) :
    fullSecondEnergy n k ≤ (2 / 3 : Real) ^ k := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [pow_mul]
    norm_num
    exact fullSecondEnergy_even_le_four_ninths
      (n := n) (m := m) hquarter
  · have h := fullSecondEnergy_odd_le_four_ninths
      (n := n) (m := m) hquarter
    calc
      fullSecondEnergy n (2 * m + 1) ≤
          (1 / 3 : Real) * (4 / 9 : Real) ^ m := h
      _ ≤ (2 / 3 : Real) ^ (2 * m + 1) := by
        rw [pow_add, pow_mul]
        norm_num
        nlinarith [pow_nonneg (show (0 : Real) ≤ 4 / 9 by norm_num) m]

theorem sum_Icc_two_thirds_pow_le_three_mul_pow (a b : Nat) :
    (∑ k ∈ Finset.Icc a b, (2 / 3 : Real) ^ k) ≤
      3 * (2 / 3 : Real) ^ a := by
  have hsum :
      (∑ i ∈ Finset.range (b + 1 - a), (2 / 3 : Real) ^ i) ≤ 3 := by
    rw [geom_sum_eq (by norm_num : (2 / 3 : Real) ≠ 1)]
    have hp : 0 ≤ (2 / 3 : Real) ^ (b + 1 - a) := by positivity
    rw [show
      (((2 / 3 : Real) ^ (b + 1 - a)) - 1) /
          ((2 / 3 : Real) - 1) =
        3 * (1 - (2 / 3 : Real) ^ (b + 1 - a)) by ring]
    linarith
  calc
    (∑ k ∈ Finset.Icc a b, (2 / 3 : Real) ^ k) =
        (2 / 3 : Real) ^ a *
          ∑ i ∈ Finset.range (b + 1 - a), (2 / 3 : Real) ^ i := by
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_eq_sum_range]
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ (2 / 3 : Real) ^ a * 3 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 3 * (2 / 3 : Real) ^ a := by ring

theorem sum_Icc_quarter_pow_sub_four_le (b : Nat) :
    (∑ k ∈ Finset.Icc 4 b, (1 / 4 : Real) ^ (k - 4)) ≤ 4 / 3 := by
  calc
    (∑ k ∈ Finset.Icc 4 b, (1 / 4 : Real) ^ (k - 4)) =
        ∑ i ∈ Finset.range (b + 1 - 4), (1 / 4 : Real) ^ i := by
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    _ = (((1 / 4 : Real) ^ (b + 1 - 4)) - 1) /
          ((1 / 4 : Real) - 1) := geom_sum_eq (by norm_num) _
    _ ≤ 4 / 3 := by
      have hp : 0 ≤ (1 / 4 : Real) ^ (b + 1 - 4) := by positivity
      rw [show
        (((1 / 4 : Real) ^ (b + 1 - 4)) - 1) /
            ((1 / 4 : Real) - 1) =
          (4 / 3 : Real) *
            (1 - (1 / 4 : Real) ^ (b + 1 - 4)) by ring]
      linarith

theorem fullDomainMediumLevelEnergy_le {n : Nat} (hn : 10 ≤ n) :
    (∑ k ∈ Finset.Icc 4 (4 * n + 1),
        injectionLevelEnergy n (2 ^ n) k) ≤
      192 / (((2 ^ n : Nat) : Real) ^ 2) := by
  let N : Nat := 2 ^ n
  have hNlarge : 100 * n ≤ N := by
    simpa [N] using hundred_mul_le_two_pow hn
  let C : Real := 144 / ((N : Real) ^ 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (∑ k ∈ Finset.Icc 4 (4 * n + 1),
        injectionLevelEnergy n (2 ^ n) k) ≤
        ∑ k ∈ Finset.Icc 4 (4 * n + 1),
          C * (1 / 4 : Real) ^ (k - 4) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkmem := Finset.mem_Icc.mp hk
      have hkhalf : 2 * k ≤ 2 ^ n := by
        dsimp [N] at hNlarge
        omega
      exact (fullDomainLevelEnergy_le_fullSecondEnergy hkhalf).trans
        (by simpa [C, N] using
          (fullSecondEnergy_le_geometric hn hkmem.1 hkmem.2))
    _ = C * (∑ k ∈ Finset.Icc 4 (4 * n + 1),
          (1 / 4 : Real) ^ (k - 4)) := by rw [Finset.mul_sum]
    _ ≤ C * (4 / 3 : Real) :=
      mul_le_mul_of_nonneg_left
        (sum_Icc_quarter_pow_sub_four_le _) hC
    _ = 192 / (((2 ^ n : Nat) : Real) ^ 2) := by
      dsimp [C, N]
      ring

theorem three_mul_two_thirds_pow_four_n_add_two_le {n : Nat} :
    3 * (2 / 3 : Real) ^ (4 * n + 2) ≤
      4 / (3 * (((2 ^ n : Nat) : Real) ^ 2)) := by
  have hp : (16 / 81 : Real) ^ n ≤ (1 / 4 : Real) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hN : ((2 : Real) ^ n) ^ 2 = (4 : Real) ^ n := by
    calc
      ((2 : Real) ^ n) ^ 2 = (2 : Real) ^ (n * 2) := by rw [pow_mul]
      _ = (2 : Real) ^ (2 * n) := by rw [Nat.mul_comm]
      _ = ((2 : Real) ^ 2) ^ n := by rw [pow_mul]
      _ = (4 : Real) ^ n := by norm_num
  norm_num [Nat.cast_pow]
  rw [show 4 * n + 2 = 4 * n + 2 by rfl, pow_add, pow_mul]
  norm_num
  rw [hN]
  have hfour : (1 / 4 : Real) ^ n = 1 / (4 : Real) ^ n := by
    simp [one_div, inv_pow]
  calc
    3 * ((16 / 81 : Real) ^ n * (4 / 9 : Real)) =
        (4 / 3 : Real) * (16 / 81 : Real) ^ n := by ring
    _ ≤ (4 / 3 : Real) * (1 / 4 : Real) ^ n :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = 4 / (3 * (4 : Real) ^ n) := by rw [hfour]; ring

theorem fullDomainQuarterHighTail_le {n b : Nat} :
    (∑ k ∈ Finset.Icc (4 * n + 2) b,
        if 4 * k ≤ 2 ^ n then injectionLevelEnergy n (2 ^ n) k else 0) ≤
      4 / (3 * (((2 ^ n : Nat) : Real) ^ 2)) := by
  calc
    (∑ k ∈ Finset.Icc (4 * n + 2) b,
        if 4 * k ≤ 2 ^ n then injectionLevelEnergy n (2 ^ n) k else 0) ≤
        ∑ k ∈ Finset.Icc (4 * n + 2) b, (2 / 3 : Real) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      by_cases hquarter : 4 * k ≤ 2 ^ n
      · rw [if_pos hquarter]
        exact (fullDomainLevelEnergy_le_fullSecondEnergy
          (n := n) (k := k) (by omega)).trans
            (fullSecondEnergy_le_two_thirds_pow hquarter)
      · rw [if_neg hquarter]
        positivity
    _ ≤ 3 * (2 / 3 : Real) ^ (4 * n + 2) :=
      sum_Icc_two_thirds_pow_le_three_mul_pow _ _
    _ ≤ 4 / (3 * (((2 ^ n : Nat) : Real) ^ 2)) :=
      three_mul_two_thirds_pow_four_n_add_two_le

/-! ## Three-quarter profile split -/

def IsThreeQuarterSeparated {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∀ beta : XorSpace n, 4 * rowMultiplicity a beta ≤ 3 * q

def HasDeepMajority {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∃ beta : XorSpace n, 3 * q < 4 * rowMultiplicity a beta

theorem not_threeQuarterSeparated_iff_deepMajority {n q : Nat}
    (a : BitMatrix q n) :
    ¬ IsThreeQuarterSeparated a ↔ HasDeepMajority a := by
  unfold IsThreeQuarterSeparated HasDeepMajority
  push Not
  rfl

def deepMajorityCoverEnergy (n : Nat) : Real :=
  ∑ beta : XorSpace n,
    ∑ b : AnchoredMask n,
      if 3 * 2 ^ n < 4 * rowMultiplicity b.1 beta ∧
          ¬ IsFullProxyMode b.1 then
        fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
      else 0

def separatedAnchoredFourthTail (n : Nat) : Real :=
  ∑ b : AnchoredMask n,
    if IsThreeQuarterSeparated b.1 ∧ ¬ IsFullProxyMode b.1 then
      fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
    else 0

theorem anchoredInjectionFourthTail_le_deepMajority_add_separated (n : Nat) :
    anchoredInjectionFourthTail n ≤
      deepMajorityCoverEnergy n + separatedAnchoredFourthTail n := by
  unfold anchoredInjectionFourthTail deepMajorityCoverEnergy
    separatedAnchoredFourthTail
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _hb
  by_cases hp : IsFullProxyMode b.1
  · simp [hp]
  · by_cases hsep : IsThreeQuarterSeparated b.1
    · simp only [hp, not_false_eq_true, hsep, true_and, if_true]
      exact le_add_of_nonneg_left (by positivity)
    · obtain ⟨beta, hbeta⟩ :=
        (not_threeQuarterSeparated_iff_deepMajority b.1).mp hsep
      simp only [hp, not_false_eq_true, hsep, if_false, add_zero, and_true]
      have hmem : beta ∈ (Finset.univ : Finset (XorSpace n)) :=
        Finset.mem_univ _
      have hs := Finset.single_le_sum
        (s := (Finset.univ : Finset (XorSpace n)))
        (f := fun gamma =>
          if 3 * 2 ^ n < 4 * rowMultiplicity b.1 gamma then
            fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
          else 0)
        (fun gamma _hgamma => by positivity) hmem
      simpa [hbeta] using hs

def deepLowFullFourthTail (n : Nat) : Real :=
  ∑ a : BitMatrix (2 ^ n) n,
    if 4 * level a < 2 ^ n ∧ ¬ IsFullProxyMode a then
      fourier (injectionDensity n (2 ^ n)) a ^ 4
    else 0

theorem deepMajorityCoverEnergy_eq_deepLowFullFourthTail (n : Nat) :
    deepMajorityCoverEnergy n = deepLowFullFourthTail n := by
  unfold deepMajorityCoverEnergy deepLowFullFourthTail
  calc
    (∑ beta : XorSpace n,
        ∑ b : AnchoredMask n,
          if 3 * 2 ^ n < 4 * rowMultiplicity b.1 beta ∧
              ¬ IsFullProxyMode b.1 then
            fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
          else 0) =
        ∑ z : XorSpace n × AnchoredMask n,
          if 3 * 2 ^ n < 4 * rowMultiplicity z.2.1 z.1 ∧
              ¬ IsFullProxyMode z.2.1 then
            fourier (injectionDensity n (2 ^ n)) z.2.1 ^ 4
          else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : BitMatrix (2 ^ n) n,
          if 4 * level a < 2 ^ n ∧ ¬ IsFullProxyMode a then
            fourier (injectionDensity n (2 ^ n)) a ^ 4
          else 0 := by
      apply Fintype.sum_equiv (globalShiftOrbitEquiv n)
      rintro ⟨beta, b⟩
      change
        (if 3 * 2 ^ n < 4 * rowMultiplicity b.1 beta ∧
            ¬ IsFullProxyMode b.1 then
          fourier (injectionDensity n (2 ^ n)) b.1 ^ 4
        else 0) =
          if 4 * level (b.1 + constantMask beta) < 2 ^ n ∧
              ¬ IsFullProxyMode (b.1 + constantMask beta) then
            fourier (injectionDensity n (2 ^ n))
              (b.1 + constantMask beta) ^ 4
          else 0
      rw [level_add_constantMask, isFullProxyMode_add_constantMask_iff]
      have hcoef := fourier_injection_density_sq_add_constant_mask_full b.1 beta
      have hmult : rowMultiplicity b.1 beta ≤ 2 ^ n := by
        unfold rowMultiplicity
        simpa using Finset.card_le_card
          (Finset.filter_subset (fun i : Fin (2 ^ n) => b.1 i = beta)
            (Finset.univ : Finset (Fin (2 ^ n))))
      by_cases hmajor : 3 * 2 ^ n < 4 * rowMultiplicity b.1 beta
      · have hlevel : 4 * (2 ^ n - rowMultiplicity b.1 beta) < 2 ^ n := by
          omega
        by_cases hp : IsFullProxyMode b.1
        · simp [hmajor, hlevel, hp]
        · simp only [hmajor, hlevel, hp, not_false_eq_true, and_self, if_true]
          nlinarith [sq_nonneg (fourier (injectionDensity n (2 ^ n))
            (b.1 + constantMask beta))]
      · have hlevel :
          ¬ 4 * (2 ^ n - rowMultiplicity b.1 beta) < 2 ^ n := by omega
        simp [hmajor, hlevel]

def deepLowLevelFourthTail (n : Nat) : Real :=
  ∑ a : BitMatrix (2 ^ n) n,
    if 3 ≤ level a ∧ 4 * level a < 2 ^ n then
      fourier (injectionDensity n (2 ^ n)) a ^ 4
    else 0

theorem deepLowFullFourthTail_le_deepLowLevelFourthTail (n : Nat) :
    deepLowFullFourthTail n ≤ deepLowLevelFourthTail n := by
  unfold deepLowFullFourthTail deepLowLevelFourthTail
  apply Finset.sum_le_sum
  intro a _ha
  by_cases hlow : 4 * level a < 2 ^ n
  · by_cases hp : IsFullProxyMode a
    · by_cases h3 : 3 ≤ level a
      · simp [hp, h3, hlow]
        positivity
      · simp [hp, h3, hlow]
    · by_cases h3 : 3 ≤ level a
      · simp [hlow, hp, h3]
      · have hz := fourier_full_eq_zero_of_level_lt_three_of_not_proxy
          a (by omega) hp
        simp [hlow, hp, h3, hz]
  · simp [hlow]

theorem deepLowLevelFourthTail_eq_Icc (n : Nat) :
    deepLowLevelFourthTail n =
      ∑ k ∈ Finset.Icc 3 (2 ^ n),
        if 4 * k < 2 ^ n then injectionLevelEnergy n (2 ^ n) k else 0 := by
  calc
    deepLowLevelFourthTail n =
        ∑ a : BitMatrix (2 ^ n) n,
          if 3 ≤ level a ∧ 4 * level a < 2 ^ n then
            fourier (injectionDensity n (2 ^ n)) a ^ 4 else 0 := by
      rfl
    _ = ∑ k ∈ Finset.range (2 ^ n + 1),
          ∑ a ∈ (Finset.univ : Finset (BitMatrix (2 ^ n) n)).filter
              (fun a => level a = k),
            if 3 ≤ level a ∧ 4 * level a < 2 ^ n then
              fourier (injectionDensity n (2 ^ n)) a ^ 4 else 0 :=
      sum_eq_sum_levels _
    _ = ∑ k ∈ Finset.range (2 ^ n + 1),
          if 3 ≤ k ∧ 4 * k < 2 ^ n then
            injectionLevelEnergy n (2 ^ n) k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hcond : 3 ≤ k ∧ 4 * k < 2 ^ n
      · rw [if_pos hcond]
        unfold injectionLevelEnergy
        apply Finset.sum_congr rfl
        intro a ha
        have hlevel : level a = k := by simpa using ha
        rw [hlevel, if_pos hcond]
      · rw [if_neg hcond]
        apply Finset.sum_eq_zero
        intro a ha
        have hlevel : level a = k := by simpa using ha
        rw [hlevel, if_neg hcond]
    _ = ∑ k ∈ Finset.Icc 3 (2 ^ n),
          if 4 * k < 2 ^ n then injectionLevelEnergy n (2 ^ n) k else 0 := by
      calc
        (∑ k ∈ Finset.range (2 ^ n + 1),
            if 3 ≤ k ∧ 4 * k < 2 ^ n then
              injectionLevelEnergy n (2 ^ n) k else 0) =
            ∑ k ∈ (Finset.range (2 ^ n + 1)).filter
                (fun k => 3 ≤ k ∧ 4 * k < 2 ^ n),
              injectionLevelEnergy n (2 ^ n) k := by
          rw [Finset.sum_filter]
        _ = ∑ k ∈ (Finset.Icc 3 (2 ^ n)).filter
                (fun k => 4 * k < 2 ^ n),
              injectionLevelEnergy n (2 ^ n) k := by
          congr 1
          ext k
          simp [Finset.mem_Icc]
          omega
        _ = ∑ k ∈ Finset.Icc 3 (2 ^ n),
              if 4 * k < 2 ^ n then
                injectionLevelEnergy n (2 ^ n) k else 0 := by
          rw [Finset.sum_filter]

theorem deepLowLevelFourthTail_le {n : Nat} (hn : 10 ≤ n) :
    deepLowLevelFourthTail n ≤
      16 * (((2 ^ n).choose 3 : Nat) : Real) /
          ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
            (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
        (580 / 3 : Real) / (((2 ^ n : Nat) : Real) ^ 2) := by
  let N : Nat := 2 ^ n
  let f : Nat → Real := fun k =>
    if 4 * k < N then injectionLevelEnergy n N k else 0
  have hNlarge : 100 * n ≤ N := by
    simpa [N] using hundred_mul_le_two_pow hn
  have hN3 : 3 ≤ N := by omega
  have hL3 : 3 ≤ 4 * n + 1 := by omega
  have hLN : 4 * n + 1 ≤ N := by omega
  have hthree : f 3 = injectionLevelEnergy n N 3 := by
    unfold f
    rw [if_pos (by omega)]
  have hmedium :
      (∑ k ∈ Finset.Icc 4 (min N (4 * n + 1)), f k) =
        ∑ k ∈ Finset.Icc 4 (4 * n + 1),
          injectionLevelEnergy n N k := by
    rw [min_eq_right hLN]
    apply Finset.sum_congr rfl
    intro k hk
    unfold f
    rw [if_pos]
    have hkmem := Finset.mem_Icc.mp hk
    omega
  have hhigh :
      (∑ k ∈ Finset.Icc (4 * n + 2) N, f k) ≤
        4 / (3 * ((N : Real) ^ 2)) := by
    calc
      (∑ k ∈ Finset.Icc (4 * n + 2) N, f k) ≤
          ∑ k ∈ Finset.Icc (4 * n + 2) N,
            if 4 * k ≤ N then injectionLevelEnergy n N k else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        unfold f
        by_cases hlt : 4 * k < N
        · rw [if_pos hlt, if_pos hlt.le]
        · rw [if_neg hlt]
          by_cases hle : 4 * k ≤ N
          · rw [if_pos hle]
            unfold injectionLevelEnergy
            positivity
          · rw [if_neg hle]
      _ ≤ 4 / (3 * ((N : Real) ^ 2)) := by
        simpa [N] using fullDomainQuarterHighTail_le (n := n) (b := N)
  rw [deepLowLevelFourthTail_eq_Icc]
  change (∑ k ∈ Finset.Icc 3 N, f k) ≤ _
  rw [sum_Icc_three_split f hN3 hL3, hthree, hmedium]
  rw [injectionLevelEnergy_three_eq hN3 (le_refl N)]
  have hmed := fullDomainMediumLevelEnergy_le hn
  change
    16 * (N.choose 3 : Real) /
          (((((N - 1 : Nat) : Real)) ^ 3) *
            ((((N - 2 : Nat) : Real)) ^ 3)) +
        (∑ k ∈ Finset.Icc 4 (4 * n + 1), injectionLevelEnergy n N k) +
        (∑ k ∈ Finset.Icc (4 * n + 2) N, f k) ≤ _
  have hsum := add_le_add hmed hhigh
  dsimp [N] at hsum ⊢
  calc
    16 * ((2 ^ n).choose 3 : Real) /
          (((((2 ^ n - 1 : Nat) : Real)) ^ 3) *
            ((((2 ^ n - 2 : Nat) : Real)) ^ 3)) +
        (∑ k ∈ Finset.Icc 4 (4 * n + 1),
          injectionLevelEnergy n (2 ^ n) k) +
        (∑ k ∈ Finset.Icc (4 * n + 2) (2 ^ n), f k) ≤
      16 * ((2 ^ n).choose 3 : Real) /
          (((((2 ^ n - 1 : Nat) : Real)) ^ 3) *
            ((((2 ^ n - 2 : Nat) : Real)) ^ 3)) +
        (192 / (((2 ^ n : Nat) : Real) ^ 2) +
          4 / (3 * (((2 ^ n : Nat) : Real) ^ 2))) := by linarith
    _ = 16 * ((2 ^ n).choose 3 : Real) /
          (((((2 ^ n - 1 : Nat) : Real)) ^ 3) *
            ((((2 ^ n - 2 : Nat) : Real)) ^ 3)) +
        (580 / 3 : Real) / (((2 ^ n : Nat) : Real) ^ 2) := by ring

theorem deepMajorityCoverEnergy_le {n : Nat} (hn : 10 ≤ n) :
    deepMajorityCoverEnergy n ≤
      16 * (((2 ^ n).choose 3 : Nat) : Real) /
          ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
            (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
        (580 / 3 : Real) / (((2 ^ n : Nat) : Real) ^ 2) := by
  rw [deepMajorityCoverEnergy_eq_deepLowFullFourthTail]
  exact (deepLowFullFourthTail_le_deepLowLevelFourthTail n).trans
    (deepLowLevelFourthTail_le hn)

end RandomSystems.SoP.XORComplement
