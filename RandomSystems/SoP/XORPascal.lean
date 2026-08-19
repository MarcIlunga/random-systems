/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORTail

/-!
# Positive Pascal recurrence for full-support injection energy

This is Dinur's normalized Pascal calculation in forward-difference form.
Writing the alternating sum as a forward difference makes the recurrence a
short discrete product rule and retains the exact rational coefficients.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORPascal

open RandomSystems.SoP.XORTail

/-- Sampling energy after `a` ambient cards have already been exposed. -/
def shiftedSamplingEnergy (N a i : Nat) : Real :=
  (N : Real) ^ i / (((N - a).descFactorial i : Nat) : Real)

/-- Dinur's auxiliary normalized Pascal weight. -/
def pascalWeight (N k a : Nat) : Real :=
  (fwdDiff (1 : Nat))^[k] (shiftedSamplingEnergy N a) 0

@[simp]
theorem shiftedSamplingEnergy_zero_shift (N i : Nat) :
    shiftedSamplingEnergy N 0 i = samplingEnergy N i := by
  simp [shiftedSamplingEnergy, samplingEnergy]

/-- The intrinsic Fourier weight is the zero-shift Pascal weight. -/
theorem fullSecondEnergy_eq_pascalWeight {n k : Nat} (hk : k ≤ 2 ^ n) :
    fullSecondEnergy n k = pascalWeight (2 ^ n) k 0 := by
  rw [fullSecondEnergy_eq_samplingEnergy_fwdDiff hk]
  unfold pascalWeight
  congr 1

/-- One forward difference exposes either a previously exposed card or the
coordinate index. -/
theorem fwdDiff_shiftedSamplingEnergy {N a i : Nat}
    (hai : a + i < N) :
    fwdDiff (1 : Nat) (shiftedSamplingEnergy N a) i =
      (1 / ((N - a : Nat) : Real)) *
        (((a : Real) + (i : Real)) * shiftedSamplingEnergy N (a + 1) i) := by
  have haN : a < N := by omega
  have hiaN : i < N - a := by omega
  have hD : (((N - a).descFactorial i : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hiaN.le).ne'
  have hD' : (((N - (a + 1)).descFactorial i : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : i ≤ N - (a + 1))).ne'
  have hNa : ((N - a : Nat) : Real) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt haN
  have hNai : ((N - a - i : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : N - a - i ≠ 0)
  unfold fwdDiff shiftedSamplingEnergy
  rw [Nat.descFactorial_succ, pow_succ]
  have htail : N - (a + 1) = N - a - 1 := by omega
  have hshift :
      (N - a - i) * (N - a).descFactorial i =
        (N - a) * (N - (a + 1)).descFactorial i := by
    calc
      (N - a - i) * (N - a).descFactorial i =
          (N - a).descFactorial (i + 1) := by
        rw [Nat.descFactorial_succ]
      _ = (N - a) * (N - a - 1).descFactorial i := by
        have hs := Nat.succ_descFactorial_succ (N - a - 1) i
        simpa [show N - a - 1 + 1 = N - a by omega] using hs
      _ = (N - a) * (N - (a + 1)).descFactorial i := by rw [htail]
  have hshiftR :
      ((N - a - i : Nat) : Real) *
          (((N - a).descFactorial i : Nat) : Real) =
        ((N - a : Nat) : Real) *
          (((N - (a + 1)).descFactorial i : Nat) : Real) := by
    exact_mod_cast hshift
  rw [show ((((N - a - i) * (N - a).descFactorial i : Nat) : Real)) =
      ((N - a : Nat) : Real) *
        (((N - (a + 1)).descFactorial i : Nat) : Real) by
    exact_mod_cast hshift]
  field_simp [hD, hD', hNa]
  have hcastNai : ((N - a - i : Nat) : Real) =
      (N : Real) - (a : Real) - (i : Real) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  have hcastNa : ((N - a : Nat) : Real) =
      (N : Real) - (a : Real) := by rw [Nat.cast_sub haN.le]
  rw [hcastNai, hcastNa] at hshiftR
  have hcore :
      (N : Real) * (((N - a).descFactorial i : Nat) : Real) -
          ((N - a : Nat) : Real) *
            (((N - (a + 1)).descFactorial i : Nat) : Real) =
        ((a : Real) + (i : Real)) *
          (((N - a).descFactorial i : Nat) : Real) := by
    rw [hcastNa]
    nlinarith [hshiftR]
  rw [show
      (N : Real) * (((N - a).descFactorial i : Nat) : Real) -
          ((N - a : Nat) : Real) *
            (((N - (a + 1)).descFactorial i : Nat) : Real) =
        ((a : Real) + (i : Real)) *
          (((N - a).descFactorial i : Nat) : Real) from hcore]
  ring

/-- Shifting the coordinate consumes the next exposed ambient card. -/
theorem shiftedSamplingEnergy_succ {N a i : Nat}
    (hai : a + i + 1 < N) :
    shiftedSamplingEnergy N (a + 1) (i + 1) =
      (N : Real) / ((N - a - 1 : Nat) : Real) *
        shiftedSamplingEnergy N (a + 2) i := by
  have ha1N : a + 1 < N := by omega
  have hD : (((N - (a + 2)).descFactorial i : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : i ≤ N - (a + 2))).ne'
  have hNa1 : ((N - a - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast (by omega : N - a - 1 ≠ 0)
  have htail : N - (a + 2) + 1 = N - (a + 1) := by omega
  have hdf :
      (N - (a + 1)).descFactorial (i + 1) =
        (N - a - 1) * (N - (a + 2)).descFactorial i := by
    have hs := Nat.succ_descFactorial_succ (N - (a + 2)) i
    rw [htail] at hs
    simpa [show N - a - 1 = N - (a + 1) by omega] using hs
  unfold shiftedSamplingEnergy
  rw [hdf, Nat.cast_mul, pow_succ]
  field_simp [hD, hNa1]

/-- Iterated discrete product rule for an affine coordinate multiplier. -/
theorem fwdDiff_iter_succ_affine_mul (g : Nat → Real) (c : Real)
    (m : Nat) :
    (fwdDiff (1 : Nat))^[m + 1]
        (fun i => (c + (i : Real)) * g i) 0 =
      c * (fwdDiff (1 : Nat))^[m + 1] g 0 +
        ((m + 1 : Nat) : Real) *
          (fwdDiff (1 : Nat))^[m] g 1 := by
  rw [show (fun i : Nat => (c + (i : Real)) * g i) =
      (fun i : Nat => c * g i) + (fun i : Nat => (i : Real) * g i) by
    funext i
    simp only [Pi.add_apply]
    ring]
  rw [fwdDiff_iter_add]
  change
    (fwdDiff (1 : Nat))^[m + 1] (c • g) 0 +
        (fwdDiff (1 : Nat))^[m + 1]
          (fun i => (i : Real) * g i) 0 = _
  rw [fwdDiff_iter_const_smul]
  change c * (fwdDiff (1 : Nat))^[m + 1] g 0 + _ = _
  rw [fwdDiff_iter_succ_coordinate_mul]
  norm_num

/-- Iterated form of `shiftedSamplingEnergy_succ`. -/
theorem fwdDiff_iter_shiftedSamplingEnergy_one {N a m : Nat}
    (ham : a + m + 1 < N) :
    (fwdDiff (1 : Nat))^[m] (shiftedSamplingEnergy N (a + 1)) 1 =
      (N : Real) / ((N - a - 1 : Nat) : Real) *
        pascalWeight N m (a + 2) := by
  rw [← fwdDiff_iter_shift_one
    (shiftedSamplingEnergy N (a + 1)) m 0]
  unfold pascalWeight
  have hcongr :
      (fwdDiff (1 : Nat))^[m]
          (fun i => shiftedSamplingEnergy N (a + 1) (i + 1)) 0 =
        (fwdDiff (1 : Nat))^[m]
          (fun i =>
            (N : Real) / ((N - a - 1 : Nat) : Real) *
              shiftedSamplingEnergy N (a + 2) i) 0 := by
    apply fwdDiff_iter_apply_zero_congr
    intro i hi
    rw [shiftedSamplingEnergy_succ]
    omega
  rw [hcongr]
  change
    (fwdDiff (1 : Nat))^[m]
        (((N : Real) / ((N - a - 1 : Nat) : Real)) •
          shiftedSamplingEnergy N (a + 2)) 0 = _
  rw [fwdDiff_iter_const_smul]
  rfl

@[simp]
theorem pascalWeight_zero (N a : Nat) : pascalWeight N 0 a = 1 := by
  simp [pascalWeight, shiftedSamplingEnergy]

theorem pascalWeight_one {N a : Nat} (haN : a < N) :
    pascalWeight N 1 a = (a : Real) / ((N - a : Nat) : Real) := by
  unfold pascalWeight
  rw [show (fwdDiff (1 : Nat))^[1] = fwdDiff (1 : Nat) by rfl]
  rw [fwdDiff_shiftedSamplingEnergy (N := N) (a := a) (i := 0) (by omega)]
  simp [shiftedSamplingEnergy]
  ring

/-- Dinur Proposition 21, with every rational coefficient retained. -/
theorem pascalWeight_recurrence {N k a : Nat}
    (hk : 2 ≤ k) (hak : a + k ≤ N) :
    pascalWeight N k a =
      (a : Real) / ((N - a : Nat) : Real) *
          pascalWeight N (k - 1) (a + 1) +
        (((k - 1 : Nat) : Real) * (N : Real)) /
            (((N - a : Nat) : Real) * ((N - a - 1 : Nat) : Real)) *
          pascalWeight N (k - 2) (a + 2) := by
  let f : Nat → Real := shiftedSamplingEnergy N a
  let g : Nat → Real := shiftedSamplingEnergy N (a + 1)
  have hk1 : k - 1 + 1 = k := by omega
  have hk2 : k - 2 + 1 = k - 1 := by omega
  have hlocal (i : Nat) (hi : i ≤ k - 1) :
      fwdDiff (1 : Nat) f i =
        (1 / ((N - a : Nat) : Real)) *
          (((a : Real) + (i : Real)) * g i) := by
    dsimp [f, g]
    exact fwdDiff_shiftedSamplingEnergy (by omega)
  have hcongr :
      (fwdDiff (1 : Nat))^[k - 1] (fwdDiff (1 : Nat) f) 0 =
        (fwdDiff (1 : Nat))^[k - 1]
          (fun i =>
            (1 / ((N - a : Nat) : Real)) *
              (((a : Real) + (i : Real)) * g i)) 0 := by
    exact fwdDiff_iter_apply_zero_congr hlocal
  unfold pascalWeight
  change (fwdDiff (1 : Nat))^[k] f 0 = _
  rw [← hk1, Function.iterate_succ_apply]
  rw [hcongr]
  change
    (fwdDiff (1 : Nat))^[k - 1]
        ((1 / ((N - a : Nat) : Real)) •
          (fun i : Nat => ((a : Real) + (i : Real)) * g i)) 0 = _
  rw [fwdDiff_iter_const_smul]
  change
    (1 / ((N - a : Nat) : Real)) *
      (fwdDiff (1 : Nat))^[k - 1]
        (fun i : Nat => ((a : Real) + (i : Real)) * g i) 0 = _
  rw [← hk2, fwdDiff_iter_succ_affine_mul]
  rw [fwdDiff_iter_shiftedSamplingEnergy_one (N := N) (a := a)
    (m := k - 2) (by omega)]
  dsimp [g]
  rw [show k - 2 + 1 + 1 - 2 = k - 2 by omega]
  simp only [pascalWeight]
  ring

/-- The even half of Dinur's exact parity-sensitive majorant. -/
def evenPascalBound (N m a : Nat) : Real :=
  ((N : Real) * ((a + 2 * m - 1 : Nat) : Real)) ^ m /
    (((N - a).descFactorial (2 * m) : Nat) : Real)

/-- The odd half of Dinur's exact parity-sensitive majorant. -/
def oddPascalBound (N m a : Nat) : Real :=
  (((N : Real) * ((a + 2 * m : Nat) : Real)) ^ m *
      ((a + 2 * m : Nat) : Real)) /
    (((N - a).descFactorial (2 * m + 1) : Nat) : Real)

/-- Peel the first card from a descending factorial, with shifts expressed in
the form used by the Pascal recurrence. -/
theorem cast_descFactorial_shift_one {N a k : Nat} (haN : a < N) :
    ((((N - a).descFactorial (k + 1) : Nat) : Real)) =
      ((N - a : Nat) : Real) *
        ((((N - (a + 1)).descFactorial k : Nat) : Real)) := by
  have hstep := Nat.succ_descFactorial_succ (N - a - 1) k
  have htop : N - a - 1 + 1 = N - a := by omega
  have htail : N - a - 1 = N - (a + 1) := by omega
  rw [htop, htail] at hstep
  exact_mod_cast hstep

/-- Two-card form of `cast_descFactorial_shift_one`. -/
theorem cast_descFactorial_shift_two {N a k : Nat} (haN : a + 1 < N) :
    ((((N - a).descFactorial (k + 2) : Nat) : Real)) =
      ((N - a : Nat) : Real) * ((N - a - 1 : Nat) : Real) *
        ((((N - (a + 2)).descFactorial k : Nat) : Real)) := by
  rw [show k + 2 = (k + 1) + 1 by omega,
    cast_descFactorial_shift_one (a := a) (k := k + 1) (by omega),
    cast_descFactorial_shift_one (a := a + 1) (k := k) (by omega)]
  rw [show N - (a + 1) = N - a - 1 by omega]
  ring

/-- The two parity bounds are proved simultaneously because the Pascal
recurrence switches parity in its first branch.  No paper constant is rounded. -/
theorem pascalWeight_even_odd_bounds (N m : Nat) :
    (∀ a, a + 2 * m ≤ N →
      pascalWeight N (2 * m) a ≤ evenPascalBound N m a) ∧
    (∀ a, a + (2 * m + 1) ≤ N →
      pascalWeight N (2 * m + 1) a ≤ oddPascalBound N m a) := by
  induction m with
  | zero =>
      constructor
      · intro a ha
        simp [evenPascalBound]
      · intro a ha
        rw [pascalWeight_one (by omega)]
        simp [oddPascalBound]
  | succ m ih =>
      have hevenNext : ∀ a, a + 2 * (m + 1) ≤ N →
          pascalWeight N (2 * (m + 1)) a ≤
            evenPascalBound N (m + 1) a := by
        intro a ha
        have hk : 2 ≤ 2 * (m + 1) := by omega
        rw [pascalWeight_recurrence hk (by omega)]
        have hodd := ih.2 (a + 1) (by omega)
        have heven := ih.1 (a + 2) (by omega)
        calc
          _ ≤ (a : Real) / ((N - a : Nat) : Real) *
                oddPascalBound N m (a + 1) +
              ((((2 * (m + 1) - 1 : Nat) : Real) * (N : Real)) /
                  (((N - a : Nat) : Real) *
                    ((N - a - 1 : Nat) : Real))) *
                evenPascalBound N m (a + 2) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hodd (by positivity))
                (mul_le_mul_of_nonneg_left heven (by positivity))
          _ ≤ evenPascalBound N (m + 1) a := by
              have htop : 2 * (m + 1) = 2 * m + 2 := by omega
              have hcoef : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
              have hsOdd : a + 1 + 2 * m = a + 2 * m + 1 := by omega
              have hsEven : a + 2 + 2 * m - 1 = a + 2 * m + 1 := by
                omega
              have hsTop : a + 2 * (m + 1) - 1 = a + 2 * m + 1 := by
                omega
              unfold oddPascalBound evenPascalBound
              rw [hcoef, hsOdd, hsEven, hsTop, htop]
              rw [cast_descFactorial_shift_one (N := N) (a := a + 1)
                (k := 2 * m) (by omega)]
              rw [cast_descFactorial_shift_two (N := N) (a := a)
                (k := 2 * m) (by omega)]
              rw [show N - (a + 1) = N - a - 1 by omega,
                show N - (a + 1 + 1) = N - (a + 2) by omega]
              have htailNat : 0 < (N - (a + 2)).descFactorial (2 * m) :=
                Nat.descFactorial_pos.mpr (by omega)
              have hNa : 0 < ((N - a : Nat) : Real) := by
                exact_mod_cast (by omega : 0 < N - a)
              have hNa1 : 0 < ((N - a - 1 : Nat) : Real) := by
                exact_mod_cast (by omega : 0 < N - a - 1)
              have htail : 0 <
                  (((N - (a + 2)).descFactorial (2 * m) : Nat) : Real) := by
                exact_mod_cast htailNat
              have hden : 0 <
                  ((N - a : Nat) : Real) * ((N - a - 1 : Nat) : Real) *
                    (((N - (a + 2)).descFactorial (2 * m) : Nat) : Real) := by
                exact mul_pos (mul_pos hNa hNa1) htail
              rw [show
                  (a : Real) / ((N - a : Nat) : Real) *
                        (((N : Real) * ((a + 2 * m + 1 : Nat) : Real)) ^ m *
                            ((a + 2 * m + 1 : Nat) : Real) /
                          (((N - a - 1 : Nat) : Real) *
                            (((N - (a + 2)).descFactorial (2 * m) : Nat) : Real))) +
                      (((2 * m + 1 : Nat) : Real) * (N : Real)) /
                          (((N - a : Nat) : Real) *
                            ((N - a - 1 : Nat) : Real)) *
                        (((N : Real) * ((a + 2 * m + 1 : Nat) : Real)) ^ m /
                          (((N - (a + 2)).descFactorial (2 * m) : Nat) : Real)) =
                    (((N : Real) * ((a + 2 * m + 1 : Nat) : Real)) ^ m *
                        ((a : Real) * ((a + 2 * m + 1 : Nat) : Real) +
                          ((2 * m + 1 : Nat) : Real) * (N : Real))) /
                      (((N - a : Nat) : Real) *
                        ((N - a - 1 : Nat) : Real) *
                        (((N - (a + 2)).descFactorial (2 * m) : Nat) : Real)) by
                    ring]
              rw [pow_succ]
              apply (div_le_div_iff_of_pos_right hden).2
              apply mul_le_mul_of_nonneg_left _
                (pow_nonneg (mul_nonneg (by positivity) (by positivity)) _)
              have hsle : ((a + 2 * m + 1 : Nat) : Real) ≤ (N : Real) := by
                exact_mod_cast (by omega : a + 2 * m + 1 ≤ N)
              have hsplit : ((a + 2 * m + 1 : Nat) : Real) =
                  (a : Real) + ((2 * m + 1 : Nat) : Real) := by
                norm_num
                ring
              have hgap : 0 ≤ (a : Real) *
                  ((N : Real) - ((a + 2 * m + 1 : Nat) : Real)) :=
                mul_nonneg (by positivity) (sub_nonneg.mpr hsle)
              nlinarith
      have hoddNext : ∀ a, a + (2 * (m + 1) + 1) ≤ N →
          pascalWeight N (2 * (m + 1) + 1) a ≤
            oddPascalBound N (m + 1) a := by
        intro a ha
        have hk : 2 ≤ 2 * (m + 1) + 1 := by omega
        rw [pascalWeight_recurrence hk (by omega)]
        have heven := hevenNext (a + 1) (by omega)
        have hodd := ih.2 (a + 2) (by omega)
        calc
          _ ≤ (a : Real) / ((N - a : Nat) : Real) *
                evenPascalBound N (m + 1) (a + 1) +
              ((((2 * (m + 1) + 1 - 1 : Nat) : Real) * (N : Real)) /
                  (((N - a : Nat) : Real) *
                    ((N - a - 1 : Nat) : Real))) *
                oddPascalBound N m (a + 2) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left heven (by positivity))
                (mul_le_mul_of_nonneg_left hodd (by positivity))
          _ ≤ oddPascalBound N (m + 1) a := by
              have htwo : 2 * (m + 1) = 2 * m + 2 := by omega
              have hcoef : 2 * (m + 1) + 1 - 1 = 2 * m + 2 := by omega
              have hsEven : a + 1 + 2 * (m + 1) - 1 =
                  a + 2 * m + 2 := by omega
              have hsOdd : a + 2 + 2 * m = a + 2 * m + 2 := by omega
              have hsTop : a + 2 * (m + 1) = a + 2 * m + 2 := by omega
              have hlen : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
              unfold evenPascalBound oddPascalBound
              rw [hcoef, hsEven, hsOdd, hsTop, hlen, htwo]
              rw [cast_descFactorial_shift_one (N := N) (a := a + 1)
                (k := 2 * m + 1) (by omega)]
              rw [show 2 * m + 3 = (2 * m + 1) + 2 by omega,
                cast_descFactorial_shift_two (N := N) (a := a)
                  (k := 2 * m + 1) (by omega)]
              rw [show N - (a + 1) = N - a - 1 by omega,
                show N - (a + 1 + 1) = N - (a + 2) by omega]
              rw [pow_succ]
              have hsplit : ((a + 2 * m + 2 : Nat) : Real) =
                  (a : Real) + ((2 * m + 2 : Nat) : Real) := by
                norm_num
                ring
              rw [hsplit]
              ring_nf
              exact le_rfl
      exact ⟨hevenNext, hoddNext⟩

/-- Exact unrounded even branch of Dinur Proposition 22. -/
theorem pascalWeight_even_le {N m a : Nat} (h : a + 2 * m ≤ N) :
    pascalWeight N (2 * m) a ≤ evenPascalBound N m a :=
  (pascalWeight_even_odd_bounds N m).1 a h

/-- Exact unrounded odd branch of Dinur Proposition 22. -/
theorem pascalWeight_odd_le {N m a : Nat} (h : a + (2 * m + 1) ≤ N) :
    pascalWeight N (2 * m + 1) a ≤ oddPascalBound N m a :=
  (pascalWeight_even_odd_bounds N m).2 a h

/-- Intrinsic full-support energy, exact even-parity majorant. -/
theorem fullSecondEnergy_even_le {n m : Nat} (hm : 2 * m ≤ 2 ^ n) :
    fullSecondEnergy n (2 * m) ≤
      (((2 ^ n : Nat) : Real) * ((2 * m - 1 : Nat) : Real)) ^ m /
        ((((2 ^ n : Nat).descFactorial (2 * m) : Nat) : Real)) := by
  rw [fullSecondEnergy_eq_pascalWeight hm]
  simpa [evenPascalBound] using
    (pascalWeight_even_le (N := 2 ^ n) (m := m) (a := 0)
      (by simpa using hm))

/-- Intrinsic full-support energy, exact odd-parity majorant. -/
theorem fullSecondEnergy_odd_le {n m : Nat} (hm : 2 * m + 1 ≤ 2 ^ n) :
    fullSecondEnergy n (2 * m + 1) ≤
      ((((2 ^ n : Nat) : Real) * ((2 * m : Nat) : Real)) ^ m *
          ((2 * m : Nat) : Real)) /
        ((((2 ^ n : Nat).descFactorial (2 * m + 1) : Nat) : Real)) := by
  rw [fullSecondEnergy_eq_pascalWeight hm]
  simpa [oddPascalBound] using
    (pascalWeight_odd_le (N := 2 ^ n) (m := m) (a := 0)
      (by simpa using hm))

end RandomSystems.SoP.XORPascal
