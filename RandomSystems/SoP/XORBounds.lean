/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORCore
import RandomSystems.SoP.XORCoefficient
import RandomSystems.SoP.XORPascal

/-!
# Finite broken-cycle tail bounds

This file turns the exact level-three calculation, the maximal-coefficient
estimate, and the unrounded Pascal bounds into a finite estimate for the
level-four-and-higher Fourier tail.  The intermediate geometric envelope is
kept explicit; the published decimal-looking constants are only corollaries.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORBounds

open RandomSystems.CR18
open RandomSystems.Applications.XoP.ANOVA
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.XORTail
open RandomSystems.SoP.XORCoefficient
open RandomSystems.SoP.XORPascal
open RandomSystems.SoP.CollisionProxy

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The squared `L2` mass of all broken-cycle modes, starting at row level
three. -/
def fourierTailEnergy (n q : Nat) : Real :=
  ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
      (fun a => 3 ≤ level a),
    (XORFourier.fourier (injectionDensity n q) a) ^ 4

/-- Partition the broken-cycle energy by its exact number of used rows. -/
theorem fourierTailEnergy_eq_sum_levels (n q : Nat) :
    fourierTailEnergy n q =
      ∑ k ∈ Finset.Icc 3 q, injectionLevelEnergy n q k := by
  calc
    fourierTailEnergy n q =
        ∑ a : BitMatrix q n,
          if 3 ≤ level a then
            (XORFourier.fourier (injectionDensity n q) a) ^ 4 else 0 := by
      unfold fourierTailEnergy
      rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range (q + 1),
          ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
              (fun a => level a = k),
            if 3 ≤ level a then
              (XORFourier.fourier (injectionDensity n q) a) ^ 4 else 0 :=
      sum_eq_sum_levels _
    _ = ∑ k ∈ Finset.range (q + 1),
          if 3 ≤ k then injectionLevelEnergy n q k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h3 : 3 ≤ k
      · rw [if_pos h3]
        unfold injectionLevelEnergy
        apply Finset.sum_congr rfl
        intro a ha
        have hlevel : level a = k := by simpa using ha
        rw [hlevel, if_pos h3]
      · rw [if_neg h3]
        apply Finset.sum_eq_zero
        intro a ha
        have hlevel : level a = k := by simpa using ha
        rw [hlevel, if_neg h3]
    _ = ∑ k ∈ Finset.Icc 3 q, injectionLevelEnergy n q k := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext k
        simp [Finset.mem_Icc, and_comm]
      · intro k hk
        rfl

/-- The elementary growth fact needed to keep the recurrence contraction
uniform through level `4*n`. -/
theorem hundred_mul_le_two_pow {n : Nat} (hn : 10 ≤ n) :
    100 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hp : 100 ≤ 2 ^ n := by
        calc
          100 ≤ 2 ^ 10 := by norm_num
          _ ≤ 2 ^ n := pow_le_pow_right' (by omega) hn
      rw [pow_succ]
      omega

/-- Four descending factors are at least four copies of `N/2`. -/
theorem half_pow_four_le_descFactorial_four {N : Nat} (hN : 8 ≤ N) :
    ((N : Real) / 2) ^ 4 ≤ ((N.descFactorial 4 : Nat) : Real) := by
  have hNR : (8 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have h0 : (N : Real) / 2 ≤ (N : Real) := by linarith
  have h1 : (N : Real) / 2 ≤ ((N - 1 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  have h2 : (N : Real) / 2 ≤ ((N - 2 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  have h3 : (N : Real) / 2 ≤ ((N - 3 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  norm_num [Nat.descFactorial_succ]
  calc
    ((N : Real) / 2) ^ 4 =
        ((N : Real) / 2) * ((N : Real) / 2) *
          ((N : Real) / 2) * ((N : Real) / 2) := by ring
    _ ≤ ((N - 3 : Nat) : Real) * ((N - 2 : Nat) : Real) *
          ((N - 1 : Nat) : Real) * (N : Real) := by
      gcongr
    _ = ((N - 3 : Nat) : Real) *
          (((N - 2 : Nat) : Real) *
            (((N - 1 : Nat) : Real) * (N : Real))) := by ring

/-- Five descending factors are at least five copies of `N/2`. -/
theorem half_pow_five_le_descFactorial_five {N : Nat} (hN : 10 ≤ N) :
    ((N : Real) / 2) ^ 5 ≤ ((N.descFactorial 5 : Nat) : Real) := by
  have hNR : (10 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have h0 : (N : Real) / 2 ≤ (N : Real) := by linarith
  have h1 : (N : Real) / 2 ≤ ((N - 1 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  have h2 : (N : Real) / 2 ≤ ((N - 2 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  have h3 : (N : Real) / 2 ≤ ((N - 3 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  have h4 : (N : Real) / 2 ≤ ((N - 4 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega)]
    norm_num
    linarith
  norm_num [Nat.descFactorial_succ]
  calc
    ((N : Real) / 2) ^ 5 =
        ((N : Real) / 2) * ((N : Real) / 2) *
          ((N : Real) / 2) * ((N : Real) / 2) *
            ((N : Real) / 2) := by ring
    _ ≤ ((N - 4 : Nat) : Real) * ((N - 3 : Nat) : Real) *
          ((N - 2 : Nat) : Real) * ((N - 1 : Nat) : Real) *
            (N : Real) := by
      gcongr
    _ = ((N - 4 : Nat) : Real) *
          (((N - 3 : Nat) : Real) *
            (((N - 2 : Nat) : Real) *
              (((N - 1 : Nat) : Real) * (N : Real)))) := by ring

/-- The first base of the recurrence envelope. -/
theorem fullSecondEnergy_four_le {n : Nat} (hn : 10 ≤ n) :
    fullSecondEnergy n 4 ≤ 144 / (((2 ^ n : Nat) : Real) ^ 2) := by
  let N : Nat := 2 ^ n
  have hNlarge : 1000 ≤ N := by
    dsimp [N]
    exact (by omega : 1000 ≤ 100 * n).trans (hundred_mul_le_two_pow hn)
  have hpas := fullSecondEnergy_even_le (n := n) (m := 2)
    (by dsimp [N] at hNlarge ⊢; omega)
  norm_num at hpas
  have hhalf := half_pow_four_le_descFactorial_four (N := N) (by omega)
  have hNpos : 0 < (N : Real) := by exact_mod_cast (by omega : 0 < N)
  have hhalfPos : 0 < ((N : Real) / 2) ^ 4 := by positivity
  calc
    fullSecondEnergy n 4 ≤
        ((N : Real) * 3) ^ 2 / ((N.descFactorial 4 : Nat) : Real) := by
      simpa [N] using hpas
    _ ≤ ((N : Real) * 3) ^ 2 / (((N : Real) / 2) ^ 4) :=
      div_le_div_of_nonneg_left (by positivity) hhalfPos hhalf
    _ = 144 / ((N : Real) ^ 2) := by
      field_simp [hNpos.ne']
      ring
    _ = 144 / (((2 ^ n : Nat) : Real) ^ 2) := by rfl

/-- The second base of the recurrence envelope. -/
theorem fullSecondEnergy_five_le {n : Nat} (hn : 10 ≤ n) :
    fullSecondEnergy n 5 ≤ 36 / (((2 ^ n : Nat) : Real) ^ 2) := by
  let N : Nat := 2 ^ n
  have hNlarge : 1000 ≤ N := by
    dsimp [N]
    exact (by omega : 1000 ≤ 100 * n).trans (hundred_mul_le_two_pow hn)
  have hpas := fullSecondEnergy_odd_le (n := n) (m := 2)
    (by dsimp [N] at hNlarge ⊢; omega)
  norm_num at hpas
  have hhalf := half_pow_five_le_descFactorial_five (N := N) (by omega)
  have hNpos : 0 < (N : Real) := by exact_mod_cast (by omega : 0 < N)
  have hhalfPos : 0 < ((N : Real) / 2) ^ 5 := by positivity
  calc
    fullSecondEnergy n 5 ≤
        ((N : Real) * 4) ^ 2 * 4 /
          ((N.descFactorial 5 : Nat) : Real) := by
      simpa [N] using hpas
    _ ≤ ((N : Real) * 4) ^ 2 * 4 / (((N : Real) / 2) ^ 5) :=
      div_le_div_of_nonneg_left (by positivity) hhalfPos hhalf
    _ = 2048 / ((N : Real) ^ 3) := by
      field_simp [hNpos.ne']
      ring
    _ ≤ 36 / ((N : Real) ^ 2) := by
      apply (div_le_div_iff₀ (pow_pos hNpos 3) (pow_pos hNpos 2)).2
      have hNR : (1000 : Real) ≤ (N : Real) := by exact_mod_cast hNlarge
      nlinarith [sq_nonneg ((N : Real) - 1000)]
    _ = 36 / (((2 ^ n : Nat) : Real) ^ 2) := by rfl

/-- A recurrence envelope stronger than the paper's pointwise simplification.
It starts with the exact parity bounds and contracts by `1/4` at every level
through `4*n+1`. -/
theorem fullSecondEnergy_le_geometric {n k : Nat}
    (hn : 10 ≤ n) (hk4 : 4 ≤ k) (hkTop : k ≤ 4 * n + 1) :
    fullSecondEnergy n k ≤
      144 / (((2 ^ n : Nat) : Real) ^ 2) *
        (1 / 4 : Real) ^ (k - 4) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hkEq4 : k = 4
      · subst k
        simpa using fullSecondEnergy_four_le hn
      by_cases hkEq5 : k = 5
      · subst k
        calc
          fullSecondEnergy n 5 ≤ 36 / (((2 ^ n : Nat) : Real) ^ 2) :=
            fullSecondEnergy_five_le hn
          _ = 144 / (((2 ^ n : Nat) : Real) ^ 2) *
                (1 / 4 : Real) ^ (5 - 4) := by
            norm_num
            ring
      have hk6 : 6 ≤ k := by omega
      let N : Nat := 2 ^ n
      let j : Nat := k - 1
      let A : Real :=
        144 / ((N : Real) ^ 2) * (1 / 4 : Real) ^ (k - 6)
      have hNlarge : 100 * n ≤ N := by
        simpa [N] using hundred_mul_le_two_pow hn
      have hj5 : 5 ≤ j := by omega
      have hjTop : j ≤ 4 * n := by omega
      have hjN : j < N := by
        have : 4 * n < N := by omega
        omega
      have hcur := ih j (by omega) (by omega : 4 ≤ j) (by omega)
      have hprev := ih (j - 1) (by omega) (by omega : 4 ≤ j - 1) (by omega)
      have hrec := fullSecondEnergy_succ_eq (n := n) (k := j)
        (by omega) (by simpa [N] using hjN)
      have h25 : 25 * j ≤ N := by omega
      have hdenPos : 0 < (N : Real) - (j : Real) := by
        have hjNR : (j : Real) < (N : Real) := by exact_mod_cast hjN
        linarith
      have hratio : (j : Real) / ((N : Real) - (j : Real)) ≤ 1 / 24 := by
        apply (div_le_iff₀ hdenPos).2
        have h25R : (25 : Real) * (j : Real) ≤ (N : Real) := by
          exact_mod_cast h25
        nlinarith
      have hA : 0 ≤ A := by
        dsimp [A]
        positivity
      have hcurEnvelope :
          144 / ((N : Real) ^ 2) * (1 / 4 : Real) ^ (j - 4) = A / 4 := by
        have hexp : j - 4 = (k - 6) + 1 := by omega
        rw [hexp, pow_succ]
        dsimp [A]
        ring
      have hprevEnvelope :
          144 / ((N : Real) ^ 2) * (1 / 4 : Real) ^ (j - 1 - 4) = A := by
        have hexp : j - 1 - 4 = k - 6 := by omega
        rw [hexp]
      have htargetEnvelope :
          144 / ((N : Real) ^ 2) * (1 / 4 : Real) ^ (k - 4) = A / 16 := by
        have hexp : k - 4 = (k - 6) + 2 := by omega
        rw [hexp, pow_succ, pow_succ]
        dsimp [A]
        ring
      rw [hcurEnvelope] at hcur
      rw [hprevEnvelope] at hprev
      have hkj : j + 1 = k := by dsimp [j]; omega
      rw [hkj] at hrec
      calc
        fullSecondEnergy n k =
            (j : Real) / ((N : Real) - (j : Real)) *
              (2 * fullSecondEnergy n j + fullSecondEnergy n (j - 1)) := by
          simpa [N] using hrec
        _ ≤ (j : Real) / ((N : Real) - (j : Real)) *
              (2 * (A / 4) + A) := by
          apply mul_le_mul_of_nonneg_left _
            (div_nonneg (by positivity) hdenPos.le)
          linarith
        _ = (j : Real) / ((N : Real) - (j : Real)) * (3 * A / 2) := by
          ring
        _ ≤ (1 / 24 : Real) * (3 * A / 2) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
        _ = A / 16 := by ring
        _ = 144 / (((2 ^ n : Nat) : Real) ^ 2) *
              (1 / 4 : Real) ^ (k - 4) := by
          simpa [N] using htargetEnvelope.symm

/-- Sampling `k` points without replacement contracts at least as fast under
the smaller population.  This is the exact falling-factorial ratio used in
Dinur's summation, proved without replacing `N-i` by a worst-case factor. -/
theorem descFactorial_ratio_le_pow {q N k : Nat}
    (hqN : q ≤ N) (hkq : k ≤ q) (hN : 0 < N) :
    ((q.descFactorial k : Nat) : Real) /
        ((N.descFactorial k : Nat) : Real) ≤
      ((q : Real) / (N : Real)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkq' : k ≤ q := by omega
      have hkN : k < N := lt_of_lt_of_le (by omega : k < q) hqN
      have hqpos : 0 < q := by omega
      have hNkNat : 0 < N - k := Nat.sub_pos_of_lt hkN
      have hNreal : 0 < (N : Real) := by exact_mod_cast hN
      have hNk : 0 < ((N - k : Nat) : Real) := by exact_mod_cast hNkNat
      have hDNat : 0 < N.descFactorial k :=
        Nat.descFactorial_pos.mpr (by omega)
      have hD : ((N.descFactorial k : Nat) : Real) ≠ 0 := by
        exact_mod_cast hDNat.ne'
      have hfactor :
          ((q - k : Nat) : Real) / ((N - k : Nat) : Real) ≤
            (q : Real) / (N : Real) := by
        apply (div_le_div_iff₀ hNk hNreal).2
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have hqNR : (q : Real) ≤ (N : Real) := by exact_mod_cast hqN
        nlinarith
      have ih' := ih hkq'
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.cast_mul, Nat.cast_mul]
      calc
        ((q - k : Nat) : Real) * ((q.descFactorial k : Nat) : Real) /
              (((N - k : Nat) : Real) *
                ((N.descFactorial k : Nat) : Real)) =
            (((q - k : Nat) : Real) / ((N - k : Nat) : Real)) *
              (((q.descFactorial k : Nat) : Real) /
                ((N.descFactorial k : Nat) : Real)) := by
          field_simp [hNk.ne', hD]
        _ ≤ ((q : Real) / (N : Real)) *
              ((q : Real) / (N : Real)) ^ k := by
          exact mul_le_mul hfactor ih' (by positivity) (by positivity)
        _ = ((q : Real) / (N : Real)) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- Binomial support multiplicity is bounded by the corresponding independent
sampling ratio, with no `N-k` denominator loss. -/
theorem choose_ratio_le_pow {q N k : Nat}
    (hqN : q ≤ N) (hkq : k ≤ q) (hN : 0 < N) :
    (q.choose k : Real) * (1 / (N.choose k : Real)) ≤
      ((q : Real) / (N : Real)) ^ k := by
  have hdesc := descFactorial_ratio_le_pow hqN hkq hN
  have hkN : k ≤ N := hkq.trans hqN
  have hkFact : (k.factorial : Real) ≠ 0 := by positivity
  have hchooseN : (N.choose k : Real) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hkN).ne'
  have hqIdentity := Nat.descFactorial_eq_factorial_mul_choose q k
  have hNIdentity := Nat.descFactorial_eq_factorial_mul_choose N k
  have hratio :
      (q.choose k : Real) * (1 / (N.choose k : Real)) =
        ((q.descFactorial k : Nat) : Real) /
          ((N.descFactorial k : Nat) : Real) := by
    rw [hqIdentity, hNIdentity, Nat.cast_mul, Nat.cast_mul]
    field_simp [hkFact, hchooseN]
  rwa [hratio]

/-- Full-support energy is a nonnegative sub-sum of total Fourier energy. -/
theorem fullSecondEnergy_le_totalSecondEnergy {n k : Nat}
    (hk : k ≤ 2 ^ n) :
    fullSecondEnergy n k ≤ totalSecondEnergy n k := by
  have hlevel := levelSecondEnergy_eq_choose_mul_fullSecondEnergy
    (n := n) (q := k) (k := k) hk
  rw [Nat.choose_self, Nat.cast_one, one_mul] at hlevel
  rw [← hlevel]
  unfold totalSecondEnergy
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (fun _a _ha _hnot => sq_nonneg _)

/-- The support ratio times the total sampling energy has one exact factor per
exposed card.  Under `2*q ≤ N`, every such factor is at most `q/N`. -/
theorem descFactorial_combined_ratio_le_pow {q N k : Nat}
    (h2q : 2 * q ≤ N) (hkq : k ≤ q) (hN : 0 < N) :
    ((q.descFactorial k : Nat) : Real) * (N : Real) ^ k /
        (((N.descFactorial k : Nat) : Real) ^ 2) ≤
      ((q : Real) / (N : Real)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkq' : k ≤ q := by omega
      have hkN : k < N := lt_of_lt_of_le (by omega : k < q) (by omega)
      have hNkNat : 0 < N - k := Nat.sub_pos_of_lt hkN
      have hNreal : 0 < (N : Real) := by exact_mod_cast hN
      have hNk : 0 < ((N - k : Nat) : Real) := by exact_mod_cast hNkNat
      have hDNat : 0 < N.descFactorial k :=
        Nat.descFactorial_pos.mpr (by omega)
      have hD : ((N.descFactorial k : Nat) : Real) ≠ 0 := by
        exact_mod_cast hDNat.ne'
      have hfactor :
          (N : Real) * ((q - k : Nat) : Real) /
              (((N - k : Nat) : Real) ^ 2) ≤
            (q : Real) / (N : Real) := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hNk) hNreal).2
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
        have h2qR : 2 * (q : Real) ≤ (N : Real) := by exact_mod_cast h2q
        have hbase : 0 ≤
            (N : Real) * ((N : Real) - 2 * (q : Real)) +
              (q : Real) * (k : Real) := by
          exact add_nonneg
            (mul_nonneg (by positivity) (sub_nonneg.mpr h2qR))
            (mul_nonneg (by positivity) (by positivity))
        have hgap : 0 ≤ (k : Real) *
            ((N : Real) * ((N : Real) - 2 * (q : Real)) +
              (q : Real) * (k : Real)) :=
          mul_nonneg (by positivity) hbase
        nlinarith
      have ih' := ih hkq'
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.cast_mul, Nat.cast_mul, pow_succ]
      calc
        ((q - k : Nat) : Real) * ((q.descFactorial k : Nat) : Real) *
                ((N : Real) ^ k * (N : Real)) /
              ((((N - k : Nat) : Real) *
                  ((N.descFactorial k : Nat) : Real)) ^ 2) =
            ((N : Real) * ((q - k : Nat) : Real) /
                (((N - k : Nat) : Real) ^ 2)) *
              (((q.descFactorial k : Nat) : Real) * (N : Real) ^ k /
                  (((N.descFactorial k : Nat) : Real) ^ 2)) := by
          field_simp [hNk.ne', hD]
        _ ≤ ((q : Real) / (N : Real)) *
              ((q : Real) / (N : Real)) ^ k := by
          exact mul_le_mul hfactor ih' (by positivity) (by positivity)
        _ = ((q : Real) / (N : Real)) ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- High-level pointwise energy bound.  It combines multiplicity and sampling
before estimating, so no separate `W_k ≤ 1` lemma is needed. -/
theorem injectionLevelEnergy_le_ratio_pow {n q k : Nat}
    (h2q : 2 * q ≤ 2 ^ n) (hkq : k ≤ q) :
    injectionLevelEnergy n q k ≤
      ((q : Real) / ((2 ^ n : Nat) : Real)) ^ k := by
  let N : Nat := 2 ^ n
  have hN : 0 < N := by dsimp [N]; positivity
  have hqN : q ≤ N := by omega
  have hkN : k ≤ N := hkq.trans hqN
  have hV := injectionLevelEnergy_le_choose_ratio_mul_fullSecondEnergy
    (n := n) (q := q) (k := k) hqN (by omega)
  have hW := fullSecondEnergy_le_totalSecondEnergy (n := n) hkN
  rw [totalSecondEnergy_eq hkN] at hW
  have hchooseNonneg : 0 ≤
      (q.choose k : Real) * (1 / (N.choose k : Real)) := by positivity
  calc
    injectionLevelEnergy n q k ≤
        (q.choose k : Real) * (1 / (N.choose k : Real)) *
          fullSecondEnergy n k := by simpa [N] using hV
    _ ≤ (q.choose k : Real) * (1 / (N.choose k : Real)) *
          ((N : Real) ^ k / ((N.descFactorial k : Nat) : Real)) :=
      mul_le_mul_of_nonneg_left hW hchooseNonneg
    _ = ((q.descFactorial k : Nat) : Real) * (N : Real) ^ k /
          (((N.descFactorial k : Nat) : Real) ^ 2) := by
      have hkFact : (k.factorial : Real) ≠ 0 := by positivity
      have hchooseN : (N.choose k : Real) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hkN).ne'
      rw [Nat.descFactorial_eq_factorial_mul_choose q k,
        Nat.descFactorial_eq_factorial_mul_choose N k,
        Nat.cast_mul, Nat.cast_mul]
      field_simp [hkFact, hchooseN]
    _ ≤ ((q : Real) / (N : Real)) ^ k :=
      descFactorial_combined_ratio_le_pow h2q hkq hN
    _ = ((q : Real) / ((2 ^ n : Nat) : Real)) ^ k := by rfl

/-- Medium-level energy inherits an explicit `1/8` contraction.  The leading
constant `144` is retained; summing it gives `1152/7`, strictly below `200`. -/
theorem injectionLevelEnergy_le_medium_geometric {n q k : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (hk4 : 4 ≤ k) (hkq : k ≤ q) (hkTop : k ≤ 4 * n + 1) :
    injectionLevelEnergy n q k ≤
      144 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6) *
        (1 / 8 : Real) ^ (k - 4) := by
  let N : Nat := 2 ^ n
  let rho : Real := (q : Real) / (N : Real)
  have hN : 0 < N := by dsimp [N]; positivity
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hqN : q ≤ N := by omega
  have hratio := choose_ratio_le_pow hqN hkq hN
  have hW := fullSecondEnergy_le_geometric hn hk4 hkTop
  have hV := injectionLevelEnergy_le_choose_ratio_mul_fullSecondEnergy
    (n := n) (q := q) (k := k) hqN (by omega)
  have hrhoNonneg : 0 ≤ rho := by dsimp [rho]; positivity
  have hrhoHalf : rho ≤ 1 / 2 := by
    dsimp [rho]
    apply (div_le_iff₀ hNreal).2
    have h2qR : 2 * (q : Real) ≤ (N : Real) := by exact_mod_cast h2q
    linarith
  have hbase : rho * (1 / 4 : Real) ≤ 1 / 8 := by
    nlinarith
  have hbaseNonneg : 0 ≤ rho * (1 / 4 : Real) := by positivity
  have hpow :
      (rho * (1 / 4 : Real)) ^ (k - 4) ≤
        (1 / 8 : Real) ^ (k - 4) :=
    pow_le_pow_left₀ hbaseNonneg hbase _
  calc
    injectionLevelEnergy n q k ≤
        (q.choose k : Real) * (1 / (N.choose k : Real)) *
          fullSecondEnergy n k := by simpa [N] using hV
    _ ≤ rho ^ k * fullSecondEnergy n k :=
      mul_le_mul_of_nonneg_right hratio (fullSecondEnergy_nonneg n k)
    _ ≤ rho ^ k *
          (144 / ((N : Real) ^ 2) * (1 / 4 : Real) ^ (k - 4)) := by
      exact mul_le_mul_of_nonneg_left (by simpa [N] using hW)
        (pow_nonneg hrhoNonneg _)
    _ = rho ^ 4 * (144 / ((N : Real) ^ 2)) *
          (rho * (1 / 4 : Real)) ^ (k - 4) := by
      rw [show k = 4 + (k - 4) by omega,
        show 4 + (k - 4) - 4 = k - 4 by omega, pow_add, mul_pow]
      ring
    _ ≤ rho ^ 4 * (144 / ((N : Real) ^ 2)) *
          (1 / 8 : Real) ^ (k - 4) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 144 * (q : Real) ^ 4 / ((N : Real) ^ 6) *
          (1 / 8 : Real) ^ (k - 4) := by
      dsimp [rho]
      field_simp [hNreal.ne']
    _ = 144 * (q : Real) ^ 4 /
          (((2 ^ n : Nat) : Real) ^ 6) *
            (1 / 8 : Real) ^ (k - 4) := by rfl

/-- Any finite initial segment of the shifted `1/8` series is at most `8/7`. -/
theorem sum_Icc_pow_sub_four_le (b : Nat) :
    (∑ k ∈ Finset.Icc 4 b, (1 / 8 : Real) ^ (k - 4)) ≤ 8 / 7 := by
  calc
    (∑ k ∈ Finset.Icc 4 b, (1 / 8 : Real) ^ (k - 4)) =
        ∑ i ∈ Finset.range (b + 1 - 4), (1 / 8 : Real) ^ i := by
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega
    _ = (((1 / 8 : Real) ^ (b + 1 - 4)) - 1) /
          ((1 / 8 : Real) - 1) := geom_sum_eq (by norm_num) _
    _ ≤ 8 / 7 := by
      have hp : 0 ≤ (1 / 8 : Real) ^ (b + 1 - 4) := by positivity
      rw [show
        (((1 / 8 : Real) ^ (b + 1 - 4)) - 1) /
            ((1 / 8 : Real) - 1) =
          (8 / 7 : Real) *
            (1 - (1 / 8 : Real) ^ (b + 1 - 4)) by ring]
      linarith

/-- Summed medium tail with the stronger constant `1152/7`. -/
theorem mediumLevelEnergy_le {n q : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    (∑ k ∈ Finset.Icc 4 (min q (4 * n + 1)),
        injectionLevelEnergy n q k) ≤
      (1152 / 7 : Real) * (q : Real) ^ 4 /
        (((2 ^ n : Nat) : Real) ^ 6) := by
  let C : Real :=
    144 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (∑ k ∈ Finset.Icc 4 (min q (4 * n + 1)),
        injectionLevelEnergy n q k) ≤
        ∑ k ∈ Finset.Icc 4 (min q (4 * n + 1)),
          C * (1 / 8 : Real) ^ (k - 4) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkmem := Finset.mem_Icc.mp hk
      exact injectionLevelEnergy_le_medium_geometric hn h2q
        hkmem.1 (hkmem.2.trans (min_le_left _ _))
        (hkmem.2.trans (min_le_right _ _))
    _ = C * (∑ k ∈ Finset.Icc 4 (min q (4 * n + 1)),
          (1 / 8 : Real) ^ (k - 4)) := by
      rw [Finset.mul_sum]
    _ ≤ C * (8 / 7 : Real) :=
      mul_le_mul_of_nonneg_left (sum_Icc_pow_sub_four_le _) hC
    _ = (1152 / 7 : Real) * (q : Real) ^ 4 /
          (((2 ^ n : Nat) : Real) ^ 6) := by
      dsimp [C]
      ring

/-- Rounded terminal form requested by the collision-proxy theorem. -/
theorem mediumLevelEnergy_le_two_hundred {n q : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    (∑ k ∈ Finset.Icc 4 (min q (4 * n + 1)),
        injectionLevelEnergy n q k) ≤
      200 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6) := by
  refine (mediumLevelEnergy_le hn h2q).trans ?_
  have hq4 : 0 ≤ (q : Real) ^ 4 := by positivity
  have hN6 : 0 ≤ (((2 ^ n : Nat) : Real) ^ 6) := by positivity
  apply div_le_div_of_nonneg_right _ hN6
  nlinarith

/-- A finite tail of a nonnegative geometric series with ratio at most one
half is bounded by twice its first term. -/
theorem sum_Icc_pow_le_two_mul_pow {rho : Real} {a b : Nat}
    (hrho0 : 0 ≤ rho) (hrhoHalf : rho ≤ 1 / 2) :
    (∑ k ∈ Finset.Icc a b, rho ^ k) ≤ 2 * rho ^ a := by
  have hrhoOne : rho ≠ 1 := by linarith
  have hsum :
      (∑ i ∈ Finset.range (b + 1 - a), rho ^ i) ≤ 2 := by
    rw [geom_sum_eq hrhoOne]
    rw [show (rho ^ (b + 1 - a) - 1) / (rho - 1) =
        (1 - rho ^ (b + 1 - a)) / (1 - rho) by
          have hr1 : rho - 1 ≠ 0 := sub_ne_zero.mpr hrhoOne
          have h1r : 1 - rho ≠ 0 := sub_ne_zero.mpr hrhoOne.symm
          field_simp [hr1, h1r]
          ring]
    have hden : 0 < 1 - rho := by linarith
    apply (div_le_iff₀ hden).2
    have hp : 0 ≤ rho ^ (b + 1 - a) := pow_nonneg hrho0 _
    linarith
  calc
    (∑ k ∈ Finset.Icc a b, rho ^ k) =
        rho ^ a * ∑ i ∈ Finset.range (b + 1 - a), rho ^ i := by
      rw [← Finset.Ico_add_one_right_eq_Icc,
        Finset.sum_Ico_eq_sum_range]
      simp_rw [pow_add]
      rw [Finset.mul_sum]
    _ ≤ rho ^ a * 2 :=
      mul_le_mul_of_nonneg_left hsum (pow_nonneg hrho0 _)
    _ = 2 * rho ^ a := by ring

/-- The levels beyond `4*n+1` already contribute at most the stronger
constant `8`; the terminal theorem may safely round this to `16`. -/
theorem highLevelEnergy_le_eight {n q : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    (∑ k ∈ Finset.Icc (4 * n + 2) q,
        injectionLevelEnergy n q k) ≤
      8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8) := by
  let N : Nat := 2 ^ n
  let rho : Real := (q : Real) / (N : Real)
  have hN : 0 < N := by dsimp [N]; positivity
  have hNreal : 0 < (N : Real) := by exact_mod_cast hN
  have hrho0 : 0 ≤ rho := by dsimp [rho]; positivity
  have hrhoHalf : rho ≤ 1 / 2 := by
    dsimp [rho]
    apply (div_le_iff₀ hNreal).2
    have h2qR : 2 * (q : Real) ≤ (N : Real) := by exact_mod_cast h2q
    linarith
  calc
    (∑ k ∈ Finset.Icc (4 * n + 2) q,
        injectionLevelEnergy n q k) ≤
        ∑ k ∈ Finset.Icc (4 * n + 2) q, rho ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkq := (Finset.mem_Icc.mp hk).2
      simpa [rho, N] using
        (injectionLevelEnergy_le_ratio_pow (n := n) h2q hkq)
    _ ≤ 2 * rho ^ (4 * n + 2) :=
      sum_Icc_pow_le_two_mul_pow hrho0 hrhoHalf
    _ = 2 * rho ^ 4 * rho ^ (4 * n - 2) := by
      rw [show 4 * n + 2 = 4 + (4 * n - 2) by omega, pow_add]
      ring
    _ ≤ 2 * rho ^ 4 * (1 / 2 : Real) ^ (4 * n - 2) := by
      have hp := pow_le_pow_left₀ hrho0 hrhoHalf (4 * n - 2)
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 8 * (q : Real) ^ 4 / ((N : Real) ^ 8) := by
      have htwo :
          (1 / 2 : Real) ^ (4 * n - 2) = 4 / ((N : Real) ^ 4) := by
        have hdecomp : 4 * n = (4 * n - 2) + 2 := by omega
        dsimp [N]
        norm_num [Nat.cast_pow]
        rw [← pow_mul, show n * 4 = 4 * n by omega, hdecomp, pow_add]
        rw [show 4 * n - 2 + 2 - 2 = 4 * n - 2 by omega]
        rw [one_div, inv_pow]
        have hp : (2 : Real) ^ (4 * n - 2) ≠ 0 := by positivity
        norm_num
        field_simp [hp]
      rw [htwo]
      dsimp [rho]
      field_simp [hNreal.ne']
      ring
    _ = 8 * (q : Real) ^ 4 /
          (((2 ^ n : Nat) : Real) ^ 8) := by rfl

theorem highLevelEnergy_le_sixteen {n q : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    (∑ k ∈ Finset.Icc (4 * n + 2) q,
        injectionLevelEnergy n q k) ≤
      16 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8) := by
  refine (highLevelEnergy_le_eight hn h2q).trans ?_
  have hq4 : 0 ≤ (q : Real) ^ 4 := by positivity
  have hN8 : 0 ≤ (((2 ^ n : Nat) : Real) ^ 8) := by positivity
  apply div_le_div_of_nonneg_right _ hN8
  nlinarith

/-- Exact interval partition used by the terminal tail estimate. -/
theorem sum_Icc_three_split (f : Nat → Real) {q L : Nat}
    (hq3 : 3 ≤ q) (hL3 : 3 ≤ L) :
    (∑ k ∈ Finset.Icc 3 q, f k) =
      f 3 + (∑ k ∈ Finset.Icc 4 (min q L), f k) +
        ∑ k ∈ Finset.Icc (L + 1) q, f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.Ico_add_one_right_eq_Icc,
    ← Finset.Ico_add_one_right_eq_Icc]
  have hfirst := Finset.sum_Ico_consecutive f
    (show 3 ≤ 4 by omega) (show 4 ≤ q + 1 by omega)
  calc
    (∑ k ∈ Finset.Ico 3 (q + 1), f k) =
        (∑ k ∈ Finset.Ico 3 4, f k) +
          ∑ k ∈ Finset.Ico 4 (q + 1), f k := hfirst.symm
    _ = f 3 + ∑ k ∈ Finset.Ico 4 (q + 1), f k := by simp
    _ = f 3 + (∑ k ∈ Finset.Ico 4 (min q L + 1), f k) +
          ∑ k ∈ Finset.Ico (L + 1) (q + 1), f k := by
      by_cases hqL : q ≤ L
      · rw [min_eq_left hqL]
        have hempty : Finset.Ico (L + 1) (q + 1) = ∅ :=
          Finset.Ico_eq_empty (by omega)
        rw [hempty]
        simp
      · have hLq : L < q := by omega
        rw [min_eq_right hLq.le]
        have hsplit := Finset.sum_Ico_consecutive f
          (show 4 ≤ L + 1 by omega) (show L + 1 ≤ q + 1 by omega)
        rw [← hsplit]
        ring

/-- Complete squared-`L2` bound with the strongest constants proved by the
geometric recurrence argument. -/
theorem fourierTailEnergy_le_tight {n q : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    fourierTailEnergy n q ≤
      16 * (q.choose 3 : Real) /
          ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
            (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
        (1152 / 7 : Real) * (q : Real) ^ 4 /
          (((2 ^ n : Nat) : Real) ^ 6) +
        8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8) := by
  have hN3 : 3 ≤ 2 ^ n := by
    have hNlarge := hundred_mul_le_two_pow hn
    omega
  have hqN : q ≤ 2 ^ n := by omega
  by_cases hq3 : 3 ≤ q
  · rw [fourierTailEnergy_eq_sum_levels,
      sum_Icc_three_split (fun k => injectionLevelEnergy n q k)
        (L := 4 * n + 1) hq3 (by omega)]
    rw [injectionLevelEnergy_three_eq hN3 hqN]
    exact add_le_add
      (add_le_add le_rfl (mediumLevelEnergy_le hn h2q))
      (by simpa [Nat.add_assoc] using highLevelEnergy_le_eight hn h2q)
  · have hq : q < 3 := by omega
    rw [fourierTailEnergy_eq_sum_levels]
    have hempty : Finset.Icc 3 q = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty]
    positivity

/-- Rounded terminal form matching the convenient `200` and `16` constants. -/
theorem fourierTailEnergy_le {n q : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    fourierTailEnergy n q ≤
      16 * (q.choose 3 : Real) /
          ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
            (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
        200 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6) +
        16 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8) := by
  have hN3 : 3 ≤ 2 ^ n := by
    have hNlarge := hundred_mul_le_two_pow hn
    omega
  have hqN : q ≤ 2 ^ n := by omega
  by_cases hq3 : 3 ≤ q
  · rw [fourierTailEnergy_eq_sum_levels,
      sum_Icc_three_split (fun k => injectionLevelEnergy n q k)
        (L := 4 * n + 1) hq3 (by omega)]
    rw [injectionLevelEnergy_three_eq hN3 hqN]
    exact add_le_add
      (add_le_add le_rfl (mediumLevelEnergy_le_two_hundred hn h2q))
      (by simpa [Nat.add_assoc] using highLevelEnergy_le_sixteen hn h2q)
  · have hq : q < 3 := by omega
    rw [fourierTailEnergy_eq_sum_levels]
    have hempty : Finset.Icc 3 q = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty]
    positivity

/-- Tight terminal squared-energy envelope. -/
def remainderEnergyBound (n q : Nat) : Real :=
  16 * (q.choose 3 : Real) /
      ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
        (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
    (1152 / 7 : Real) * (q : Real) ^ 4 /
      (((2 ^ n : Nat) : Real) ^ 6) +
    8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8)

/-- Rounded squared-energy envelope. -/
def remainderEnergyBoundRounded (n q : Nat) : Real :=
  16 * (q.choose 3 : Real) /
      ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
        (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
    200 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6) +
    16 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8)

/-- Statistical-distance cost assigned to the higher broken-cycle modes. -/
def remainderErrorBound (n q : Nat) : Real :=
  (1 / 2 : Real) * Real.sqrt (remainderEnergyBound n q)

def remainderErrorBoundRounded (n q : Nat) : Real :=
  (1 / 2 : Real) * Real.sqrt (remainderEnergyBoundRounded n q)

theorem remainderEnergyBound_le_rounded (n q : Nat) :
    remainderEnergyBound n q ≤ remainderEnergyBoundRounded n q := by
  let A : Real := (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 6)
  let B : Real := (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  unfold remainderEnergyBound remainderEnergyBoundRounded
  dsimp [A, B] at hA hB ⊢
  ring_nf at hA hB ⊢
  nlinarith

theorem remainderErrorBound_le_rounded (n q : Nat) :
    remainderErrorBound n q ≤ remainderErrorBoundRounded n q := by
  unfold remainderErrorBound remainderErrorBoundRounded
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (remainderEnergyBound_le_rounded n q)) (by norm_num)

/-- Cauchy--Schwarz converts the exact broken-cycle `L2` identity into its
statistical-distance cost. -/
theorem remainderAdvantage_le_half_sqrt_tail {n q : Nat}
    (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n) :
    remainderAdvantage (G := XorSpace n) q ≤
      (1 / 2 : Real) * Real.sqrt (fourierTailEnergy n q) := by
  have hcauchy := uniformAverage_abs_le_sqrt_uniformAverage_sq
    (fun y : BitMatrix q n => remainderDensity (G := XorSpace n) q y)
  have hL2 := average_remainderDensity_sq_eq_fourierTail
    (n := n) (q := q) hN hq
  unfold remainderAdvantage
  calc
    (1 / 2 : Real) *
        uniformAverage (BitMatrix q n)
          (fun y => |remainderDensity (G := XorSpace n) q y|) ≤
      (1 / 2 : Real) *
        Real.sqrt
          (uniformAverage (BitMatrix q n)
            (fun y => (remainderDensity (G := XorSpace n) q y) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcauchy (by norm_num)
    _ = (1 / 2 : Real) * Real.sqrt (fourierTailEnergy n q) := by
      rw [show
        uniformAverage (BitMatrix q n)
            (fun y => (remainderDensity (G := XorSpace n) q y) ^ 2) =
          average (BitMatrix q n)
            (fun y => (remainderDensity (G := XorSpace n) q y) ^ 2) by rfl,
        hL2]
      rfl

/-- Fully closed remainder theorem. -/
theorem remainderAdvantage_le {n q : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    remainderAdvantage (G := XorSpace n) q ≤ remainderErrorBound n q := by
  have hN : 2 ≤ 2 ^ n := by
    have hNlarge := hundred_mul_le_two_pow hn
    omega
  have hq : q ≤ 2 ^ n := by omega
  calc
    remainderAdvantage (G := XorSpace n) q ≤
        (1 / 2 : Real) * Real.sqrt (fourierTailEnergy n q) :=
      remainderAdvantage_le_half_sqrt_tail hN hq
    _ ≤ (1 / 2 : Real) * Real.sqrt (remainderEnergyBound n q) := by
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by
          simpa [remainderEnergyBound] using fourierTailEnergy_le_tight hn h2q))
        (by norm_num)
    _ = remainderErrorBound n q := by rfl

/-- Exact two-sided collision-proxy approximation to the adaptive advantage. -/
theorem abs_advantage_sub_collisionAdvantage_le {n q : Nat}
    (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionAdvantage (XorSpace n) q| ≤ remainderErrorBound n q := by
  have hq : q ≤ Fintype.card (XorSpace n) := by
    rw [card_xorSpace]
    omega
  exact (abs_advantage_sub_collisionAdvantage_le_remainder
    (G := XorSpace n) q hq).trans (remainderAdvantage_le hn h2q)

/-- Final two-regime upper bound, stated through the planted-collision
representative so both sparse and dense constants remain readable. -/
theorem adaptiveTranscriptAdvantage_le_min_add_remainder {n q : Nat}
    (hn : 10 ≤ n) (hq2 : 2 ≤ q) (h2q : 2 * q ≤ 2 ^ n) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
      min (sparseBound (XorSpace n) q) (denseBound (XorSpace n) q) +
        remainderErrorBound n q := by
  let adv : Real := PFunPDS.Prob.adaptiveTranscriptAdvantage
    (q := q) (RandomSystems.SoP.xop (XorSpace n))
      (RandomSystems.SoP.urf (XorSpace n))
  let col : Real := collisionAdvantage (XorSpace n) q
  have hN : 2 ≤ Fintype.card (XorSpace n) := by
    rw [card_xorSpace]
    have hNlarge := hundred_mul_le_two_pow hn
    omega
  have hcol : col ≤
      min (sparseBound (XorSpace n) q) (denseBound (XorSpace n) q) :=
    collisionAdvantage_le_min (G := XorSpace n) q hq2 hN
  have hproxy : |adv - col| ≤ remainderErrorBound n q := by
    simpa [adv, col] using
      abs_advantage_sub_collisionAdvantage_le hn h2q
  have hadv : adv ≤ col + remainderErrorBound n q := by
    have := (abs_le.mp hproxy).2
    linarith
  exact hadv.trans (add_le_add hcol le_rfl)

/-- Expanded tight formula.  Here `N = 2^n`; no published tail constant has
been rounded upward. -/
theorem adaptiveTranscriptAdvantage_le_explicit {n q : Nat}
    (hn : 10 ≤ n) (hq2 : 2 ≤ q) (h2q : 2 * q ≤ 2 ^ n) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
      min
          ((q.choose 2 : Real) /
            (((2 ^ n - 1 : Nat) : Real) ^ 2))
          (Real.sqrt (q.choose 2 : Real) /
            (2 * ((2 ^ n - 1 : Nat) : Real) *
              Real.sqrt ((2 ^ n - 1 : Nat) : Real))) +
        (1 / 2 : Real) * Real.sqrt
          (16 * (q.choose 3 : Real) /
              ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
                (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
            (1152 / 7 : Real) * (q : Real) ^ 4 /
              (((2 ^ n : Nat) : Real) ^ 6) +
            8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8)) := by
  simpa [sparseBound, denseBound, remainderErrorBound,
    remainderEnergyBound, pairCount_eq, card_xorSpace] using
      (adaptiveTranscriptAdvantage_le_min_add_remainder hn hq2 h2q)

/-- The same theorem with the simpler rounded remainder constants. -/
theorem adaptiveTranscriptAdvantage_le_explicit_rounded {n q : Nat}
    (hn : 10 ≤ n) (hq2 : 2 ≤ q) (h2q : 2 * q ≤ 2 ^ n) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
      min (sparseBound (XorSpace n) q) (denseBound (XorSpace n) q) +
        remainderErrorBoundRounded n q := by
  exact (adaptiveTranscriptAdvantage_le_min_add_remainder hn hq2 h2q).trans
    (add_le_add le_rfl (remainderErrorBound_le_rounded n q))

end RandomSystems.SoP.XORBounds
