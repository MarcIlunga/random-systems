/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORBounds

/-!
# Signed low-level representatives for XOR SoP

The collision proxy keeps only row level two and takes an absolute value
before the higher levels are recombined with it.  This file retains an
arbitrary initial interval of row levels as one signed representative.  All
retained modes are added pointwise before the `L1` norm is taken.

For cutoff `r`, the visible likelihood error is split exactly as

```text
levels 2,...,r-1 + levels r,...,q.
```

The first summand is the signed truncation certificate.  The second has an
exact squared-energy expression.  In the finite range used by the XOR proof,
each increment of `r` removes one more geometric layer and contracts the
medium-level energy envelope by a factor `1/8`.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORSignedTruncation

open RandomSystems.CR18
open RandomSystems.Applications.XoP.ANOVA
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.XORTail
open RandomSystems.SoP.XORBounds
open RandomSystems.SoP.CollisionProxy

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The exact signed likelihood contribution from row levels `2,...,r-1`. -/
def signedTruncationDensity (n q r : Nat) : BitMatrix q n → Real :=
  spectralPart
    (fun a : BitMatrix q n => 2 ≤ level a ∧ level a < r)
    (convolution (injectionDensity n q) (injectionDensity n q))

/-- Half the uniform `L1` norm after all retained levels have been combined. -/
def signedTruncationAdvantage (n q r : Nat) : Real :=
  (1 / 2 : Real) *
    average (BitMatrix q n) (fun y => |signedTruncationDensity n q r y|)

/-- The exact unretained likelihood contribution from row level `r` onward. -/
def signedTailDensity (n q r : Nat) : BitMatrix q n → Real :=
  levelGePart r
    (convolution (injectionDensity n q) (injectionDensity n q))

/-- Half the uniform `L1` cost of the unretained signed tail. -/
def signedTailAdvantage (n q r : Nat) : Real :=
  (1 / 2 : Real) *
    average (BitMatrix q n) (fun y => |signedTailDensity n q r y|)

/-- Exact squared `L2` energy from row level `r` onward. -/
def signedTailEnergy (n q r : Nat) : Real :=
  ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
      (fun a => r ≤ level a),
    (XORFourier.fourier (injectionDensity n q) a) ^ 4

/-- Fourier inversion split into the constant, singleton, retained, and tail
selectors. -/
theorem spectral_partition_zero_one_range_ge
    {n q r : Nat} (hr : 2 ≤ r)
    (f : BitMatrix q n → Real) (y : BitMatrix q n) :
    spectralPart (fun a => level a = 0) f y +
        spectralPart (fun a => level a = 1) f y +
        spectralPart (fun a => 2 ≤ level a ∧ level a < r) f y +
        levelGePart r f y = f y := by
  rw [← fourier_inversion f y]
  unfold levelGePart spectralPart
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h0 : level a = 0
  · have hr0 : r ≠ 0 := by omega
    simp [h0, hr0]
  · by_cases h1 : level a = 1
    · have hr1 : ¬r ≤ 1 := by omega
      simp [h1, hr1]
    · by_cases htail : r ≤ level a
      · have hnotRange : ¬(2 ≤ level a ∧ level a < r) := by omega
        simp [h0, h1, htail, hnotRange]
      · have h2 : 2 ≤ level a := by omega
        have hlt : level a < r := by omega
        simp [h0, h1, htail, h2, hlt]

/-- Pointwise exactness of the signed truncation: no triangle inequality is
used between retained levels. -/
theorem visible_density_error_real_eq_signed_truncation_add_tail
    {n q r : Nat} (hr : 2 ≤ r) (hq : q ≤ 2 ^ n)
    (y : BitMatrix q n) :
    visibleDensityErrorReal (G := XorSpace n) (q := q) y =
      signedTruncationDensity n q r y + signedTailDensity n q r y := by
  have hpartition := spectral_partition_zero_one_range_ge
    (n := n) (q := q) hr
    (convolution (injectionDensity n q) (injectionDensity n q)) y
  rw [levelZeroSpectrum_eq_one hq y, levelOneSpectrum_eq_zero hq y] at hpartition
  rw [visibleDensityErrorReal,
    visibleDensityRatioReal_eq_convolution_injectionDensity hq]
  dsimp [signedTruncationDensity, signedTailDensity]
  linarith

/-- Exact two-sided comparison between the true advantage and any signed
truncation certificate. -/
theorem abs_advantage_sub_signed_truncation_advantage_le_tail
    {n q r : Nat} (hr : 2 ≤ r) (hq : q ≤ 2 ^ n) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        signedTruncationAdvantage n q r| ≤
      signedTailAdvantage n q r := by
  rw [advantage_eq_half_uniformL1 (G := XorSpace n) q (by
    simpa [card_xorSpace] using hq)]
  unfold signedTruncationAdvantage signedTailAdvantage
  let f : BitMatrix q n → Real :=
    visibleDensityErrorReal (G := XorSpace n) (q := q)
  let g : BitMatrix q n → Real := signedTruncationDensity n q r
  have hreverse := abs_uniformL1_sub_uniformL1_le f g
  have hhalf : (0 : Real) ≤ 1 / 2 := by norm_num
  calc
    |(1 / 2 : Real) * average (BitMatrix q n) (fun y => |f y|) -
        (1 / 2 : Real) * average (BitMatrix q n) (fun y => |g y|)| =
      (1 / 2 : Real) *
        |average (BitMatrix q n) (fun y => |f y|) -
          average (BitMatrix q n) (fun y => |g y|)| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hhalf]
    _ ≤ (1 / 2 : Real) *
        average (BitMatrix q n) (fun y => |f y - g y|) :=
      mul_le_mul_of_nonneg_left hreverse hhalf
    _ = (1 / 2 : Real) *
        average (BitMatrix q n) (fun y => |signedTailDensity n q r y|) := by
      congr 2
      funext y
      congr 1
      dsimp [f, g]
      rw [visible_density_error_real_eq_signed_truncation_add_tail hr hq y]
      ring

/-- Parseval gives the exact energy of the unretained signed tail. -/
theorem average_signed_tail_density_sq_eq_energy
    (n q r : Nat) :
    average (BitMatrix q n) (fun y => (signedTailDensity n q r y) ^ 2) =
      signedTailEnergy n q r := by
  unfold signedTailDensity signedTailEnergy levelGePart
  rw [parseval_selected_convolution_sq]
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _ha
    rfl

/-- Cauchy--Schwarz is applied only after all unretained levels have been
combined. -/
theorem signed_tail_advantage_le_half_sqrt_energy
    (n q r : Nat) :
    signedTailAdvantage n q r ≤
      (1 / 2 : Real) * Real.sqrt (signedTailEnergy n q r) := by
  have hcauchy := uniformAverage_abs_le_sqrt_uniformAverage_sq
    (fun y : BitMatrix q n => signedTailDensity n q r y)
  unfold signedTailAdvantage
  calc
    (1 / 2 : Real) *
        average (BitMatrix q n) (fun y => |signedTailDensity n q r y|) ≤
      (1 / 2 : Real) * Real.sqrt
        (average (BitMatrix q n)
          (fun y => (signedTailDensity n q r y) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcauchy (by norm_num)
    _ = (1 / 2 : Real) * Real.sqrt (signedTailEnergy n q r) := by
      rw [average_signed_tail_density_sq_eq_energy]

/-- The signed tail energy partitioned by its exact row level. -/
theorem signed_tail_energy_eq_sum_levels (n q r : Nat) :
    signedTailEnergy n q r =
      ∑ k ∈ Finset.Icc r q, injectionLevelEnergy n q k := by
  calc
    signedTailEnergy n q r =
        ∑ a : BitMatrix q n,
          if r ≤ level a then
            (XORFourier.fourier (injectionDensity n q) a) ^ 4 else 0 := by
      unfold signedTailEnergy
      rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range (q + 1),
          ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
              (fun a => level a = k),
            if r ≤ level a then
              (XORFourier.fourier (injectionDensity n q) a) ^ 4 else 0 :=
      sum_eq_sum_levels _
    _ = ∑ k ∈ Finset.range (q + 1),
          if r ≤ k then injectionLevelEnergy n q k else 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases hrk : r ≤ k
      · rw [if_pos hrk]
        unfold injectionLevelEnergy
        apply Finset.sum_congr rfl
        intro a ha
        have hlevel : level a = k := by simpa using ha
        rw [hlevel, if_pos hrk]
      · rw [if_neg hrk]
        apply Finset.sum_eq_zero
        intro a ha
        have hlevel : level a = k := by simpa using ha
        rw [hlevel, if_neg hrk]
    _ = ∑ k ∈ Finset.Icc r q, injectionLevelEnergy n q k := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext k
        simp [Finset.mem_Icc, and_comm]
      · intro k _hk
        rfl

/-- A finite shifted geometric tail, retaining the exact starting level. -/
theorem sum_icc_pow_sub_four_from_le {r b : Nat} (hr4 : 4 ≤ r) :
    (∑ k ∈ Finset.Icc r b, (1 / 8 : Real) ^ (k - 4)) ≤
      (8 / 7 : Real) * (1 / 8 : Real) ^ (r - 4) := by
  let m : Nat := b + 1 - r
  have hgeom :
      (∑ i ∈ Finset.range m, (1 / 8 : Real) ^ i) ≤ 8 / 7 := by
    rw [geom_sum_eq (by norm_num : (1 / 8 : Real) ≠ 1)]
    have hp : 0 ≤ (1 / 8 : Real) ^ m := by positivity
    rw [show
      (((1 / 8 : Real) ^ m) - 1) / ((1 / 8 : Real) - 1) =
        (8 / 7 : Real) * (1 - (1 / 8 : Real) ^ m) by ring]
    linarith
  calc
    (∑ k ∈ Finset.Icc r b, (1 / 8 : Real) ^ (k - 4)) =
        ∑ i ∈ Finset.range m,
          (1 / 8 : Real) ^ ((r - 4) + i) := by
      dsimp [m]
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      have hi : i < b + 1 - r := Finset.mem_range.mp hi
      omega
    _ = (1 / 8 : Real) ^ (r - 4) *
        ∑ i ∈ Finset.range m, (1 / 8 : Real) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [pow_add]
    _ ≤ (1 / 8 : Real) ^ (r - 4) * (8 / 7 : Real) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = (8 / 7 : Real) * (1 / 8 : Real) ^ (r - 4) := by ring

/-- Split a row-level tail at an arbitrary last medium level. -/
theorem sum_icc_cutoff_split (f : Nat → Real) {q r L : Nat}
    (hrL : r ≤ L + 1) :
    (∑ k ∈ Finset.Icc r q, f k) =
      (∑ k ∈ Finset.Icc r (min q L), f k) +
        ∑ k ∈ Finset.Icc (L + 1) q, f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.Ico_add_one_right_eq_Icc]
  by_cases hqL : q ≤ L
  · rw [min_eq_left hqL]
    have hempty : Finset.Ico (L + 1) (q + 1) = ∅ :=
      Finset.Ico_eq_empty (by omega)
    rw [hempty]
    simp
  · have hLq : L < q := by omega
    rw [min_eq_right hLq.le]
    exact (Finset.sum_Ico_consecutive f hrL (by omega)).symm

/-- Medium-level energy after retaining every level below `r`.  Each extra
retained level contributes an exact factor `1/8` to this envelope. -/
theorem medium_level_energy_from_le {n q r : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) (hr4 : 4 ≤ r) :
    (∑ k ∈ Finset.Icc r (min q (4 * n + 1)),
        injectionLevelEnergy n q k) ≤
      (1152 / 7 : Real) * (q : Real) ^ 4 /
          (((2 ^ n : Nat) : Real) ^ 6) *
        (1 / 8 : Real) ^ (r - 4) := by
  let C : Real :=
    144 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (∑ k ∈ Finset.Icc r (min q (4 * n + 1)),
        injectionLevelEnergy n q k) ≤
      ∑ k ∈ Finset.Icc r (min q (4 * n + 1)),
        C * (1 / 8 : Real) ^ (k - 4) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkmem := Finset.mem_Icc.mp hk
      exact injectionLevelEnergy_le_medium_geometric hn h2q
        (hr4.trans hkmem.1)
        (hkmem.2.trans (min_le_left _ _))
        (hkmem.2.trans (min_le_right _ _))
    _ = C * (∑ k ∈ Finset.Icc r (min q (4 * n + 1)),
        (1 / 8 : Real) ^ (k - 4)) := by
      rw [Finset.mul_sum]
    _ ≤ C * ((8 / 7 : Real) * (1 / 8 : Real) ^ (r - 4)) :=
      mul_le_mul_of_nonneg_left (sum_icc_pow_sub_four_from_le hr4) hC
    _ = (1152 / 7 : Real) * (q : Real) ^ 4 /
          (((2 ^ n : Nat) : Real) ^ 6) *
        (1 / 8 : Real) ^ (r - 4) := by
      dsimp [C]
      ring

/-- Closed energy envelope for a signed truncation tail. -/
def signedTailEnergyBound (n q r : Nat) : Real :=
  (1152 / 7 : Real) * (q : Real) ^ 4 /
      (((2 ^ n : Nat) : Real) ^ 6) *
      (1 / 8 : Real) ^ (r - 4) +
    8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8)

/-- The geometric signed-tail bound.  The cutoff may range through the first
high-level boundary; cutoffs beyond it can use the exact `signedTailEnergy`
statement directly. -/
theorem signed_tail_energy_le_bound {n q r : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (hr4 : 4 ≤ r) (hrTop : r ≤ 4 * n + 2) :
    signedTailEnergy n q r ≤ signedTailEnergyBound n q r := by
  rw [signed_tail_energy_eq_sum_levels,
    sum_icc_cutoff_split (fun k => injectionLevelEnergy n q k) hrTop]
  unfold signedTailEnergyBound
  exact add_le_add
    (medium_level_energy_from_le hn h2q hr4)
    (highLevelEnergy_le_eight hn h2q)

/-- Statistical-distance cost of the unretained signed levels. -/
def signedTailErrorBound (n q r : Nat) : Real :=
  (1 / 2 : Real) * Real.sqrt (signedTailEnergyBound n q r)

theorem signed_tail_advantage_le_error_bound {n q r : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (hr4 : 4 ≤ r) (hrTop : r ≤ 4 * n + 2) :
    signedTailAdvantage n q r ≤ signedTailErrorBound n q r := by
  calc
    signedTailAdvantage n q r ≤
        (1 / 2 : Real) * Real.sqrt (signedTailEnergy n q r) :=
      signed_tail_advantage_le_half_sqrt_energy n q r
    _ ≤ (1 / 2 : Real) * Real.sqrt (signedTailEnergyBound n q r) :=
      mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (signed_tail_energy_le_bound hn h2q hr4 hrTop))
        (by norm_num)
    _ = signedTailErrorBound n q r := rfl

/-- Fully closed two-sided certificate for every admissible signed cutoff. -/
theorem abs_advantage_sub_signed_truncation_advantage_le_error_bound
    {n q r : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (hr4 : 4 ≤ r) (hrTop : r ≤ 4 * n + 2) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        signedTruncationAdvantage n q r| ≤
      signedTailErrorBound n q r := by
  have hq : q ≤ 2 ^ n := by omega
  have hr2 : 2 ≤ r := by omega
  exact (abs_advantage_sub_signed_truncation_advantage_le_tail hr2 hq).trans
    (signed_tail_advantage_le_error_bound hn h2q hr4 hrTop)

/-- One signed cutoff gives a direct operational advantage bound. -/
theorem adaptive_transcript_advantage_le_signed_truncation_add_error_bound
    {n q r : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (hr4 : 4 ≤ r) (hrTop : r ≤ 4 * n + 2) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
      signedTruncationAdvantage n q r + signedTailErrorBound n q r := by
  have h := (abs_le.mp
    (abs_advantage_sub_signed_truncation_advantage_le_error_bound
      hn h2q hr4 hrTop)).2
  linarith

end RandomSystems.SoP.XORSignedTruncation
