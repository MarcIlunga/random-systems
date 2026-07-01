/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist
import RandomSystems.StatDist
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# CR18 Statistical Distance

This module formalizes CR18 Definition 2.8: the statistical distance of two
random variables over a finite set is one half of the sum of the absolute
pointwise differences of their probability laws.

The existing `RandomSystems.Dist A` carrier is reused for the laws. Since
`Dist` takes values in `NNReal`, the pointwise subtraction in the CR18 formula is
performed after coercing both masses to `Real`.

CR18 Lemma 2.1 states that this distance is exactly the advantage of the best
distinguisher. This file records the definition and its relationship to the
existing truncated-subtraction distance used elsewhere in the development.
-/

open scoped BigOperators NNReal

noncomputable section

namespace RandomSystems.CR18

/-- CR18 Definition 2.8: statistical distance as a half-sum of absolute
differences. -/
def statDist {A : Type*} [Fintype A] (X Y : RandomSystems.Dist A) : Real :=
  (1 / 2 : Real) * ∑ a : A, |(X a : Real) - (Y a : Real)|

/-- The CR18 half-absolute-value statistical distance is nonnegative. -/
theorem statDist_nonneg {A : Type*} [Fintype A] (X Y : RandomSystems.Dist A) :
    0 ≤ statDist X Y := by
  unfold statDist
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun a _ => abs_nonneg ((X a : Real) - (Y a : Real)))

/-- Statistical distance from a law to itself is zero. -/
theorem statDist_self {A : Type*} [Fintype A] (X : RandomSystems.Dist A) :
    statDist X X = 0 := by
  simp [statDist]

/-- The CR18 half-absolute-value statistical distance is symmetric. -/
theorem statDist_comm {A : Type*} [Fintype A] (X Y : RandomSystems.Dist A) :
    statDist X Y = statDist Y X := by
  unfold statDist
  simp [abs_sub_comm]

/-- Alias for the symmetry of CR18 statistical distance. -/
theorem statDist_symm {A : Type*} [Fintype A] (X Y : RandomSystems.Dist A) :
    statDist X Y = statDist Y X := by
  exact statDist_comm X Y

private lemma abs_sub_eq_coe_tsub_add_coe_tsub (x y : NNReal) :
    |(x : Real) - (y : Real)| =
      ((x - y : NNReal) : Real) + ((y - x : NNReal) : Real) := by
  rcases le_total x y with hxy | hyx
  · have hxyR : (x : Real) ≤ (y : Real) := by exact_mod_cast hxy
    have hsub1 : x - y = 0 := tsub_eq_zero_of_le hxy
    have hsub2 : ((y - x : NNReal) : Real) = (y : Real) - (x : Real) :=
      NNReal.coe_sub hxy
    rw [hsub1, NNReal.coe_zero, zero_add, hsub2]
    rw [abs_of_nonpos (by linarith)]
    ring
  · have hyxR : (y : Real) ≤ (x : Real) := by exact_mod_cast hyx
    have hsub1 : ((x - y : NNReal) : Real) = (x : Real) - (y : Real) :=
      NNReal.coe_sub hyx
    have hsub2 : y - x = 0 := tsub_eq_zero_of_le hyx
    rw [hsub2, NNReal.coe_zero, add_zero, hsub1]
    rw [abs_of_nonneg (by linarith)]

/-- For equal-weight distributions, CR18 Definition 2.8 coincides with the
existing truncated-subtraction statistical distance. -/
theorem statDist_eq_of_eq_weight {A : Type*} [Fintype A]
    (X Y : RandomSystems.Dist A) (h : X.weight = Y.weight) :
    statDist X Y = (RandomSystems.statDist X Y : Real) := by
  unfold statDist
  have h_abs_sum :
      (∑ a : A, |(X a : Real) - (Y a : Real)|) =
        (RandomSystems.statDist X Y : Real) + (RandomSystems.statDist Y X : Real) := by
    simp only [RandomSystems.statDist]
    rw [NNReal.coe_sum, NNReal.coe_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    exact abs_sub_eq_coe_tsub_add_coe_tsub (X a) (Y a)
  rw [h_abs_sum]
  have hsym : (RandomSystems.statDist Y X : Real) =
      (RandomSystems.statDist X Y : Real) := by
    exact congrArg (fun z : NNReal => (z : Real))
      (RandomSystems.statDist_symm_of_eq_weight X Y h).symm
  rw [hsym]
  ring

/-- CR18 Definition 2.5: the winning probability of a winner `W` for a game
`G`, written `Gamma^W(G) = Pr_{WG}(A = 1)` in equation (2.1).

This abstract definition follows the Real-valued style of `advantageD`: the
interaction experiment and binary winning output are represented by the
operand `probA1`, the probability that the output `A` equals `1`. -/
def winProb (probA1 : Real) : Real :=
  probA1

/-- The abstract winning probability is nonnegative when `Pr(A = 1)` is
nonnegative. -/
theorem winProb_nonneg (probA1 : Real) (hprob : 0 ≤ probA1) :
    0 ≤ winProb probA1 := by
  simpa [winProb] using hprob

/-- The abstract winning probability is at most one when `Pr(A = 1)` is at
most one. -/
theorem winProb_le_one (probA1 : Real) (hprob : probA1 ≤ 1) :
    winProb probA1 ≤ 1 := by
  simpa [winProb] using hprob

/-- The winning probability is exactly the probability that the binary winning
output `A` equals `1`. -/
theorem winProb_eq (probA1 : Real) : winProb probA1 = probA1 := by
  simp [winProb]

/-- CR18 Definition 2.6: advantage of `D` in distinguishing `S` and `T`,
`Delta_D(S,T) = Pr^{DT}[Z=1] - Pr^{DS}[Z=1]`. Operands are the
probabilities that `D` outputs `1` connected to `S` (`probOut1S`) and to `T`
(`probOut1T`).

This is the per-distinguisher signed building block. The existing
`RandomSystems.advantage` is an optimal advantage: a supremum over inputs of
statistical distance, valued in `NNReal`, corresponding to CR18 Definition 2.7.
Taking a supremum of the absolute value of this signed quantity yields the
optimal distinguishing advantage; that supremum is intentionally out of scope
for CR18 Definition 2.6. -/
def advantageD (probOut1S probOut1T : Real) : Real :=
  probOut1T - probOut1S

/-- A distinguisher has zero signed advantage between equal output
probabilities. -/
theorem advantageD_self (p : Real) : advantageD p p = 0 := by
  simp [advantageD]

/-- Swapping the two systems negates the signed distinguishing advantage. -/
theorem advantageD_neg (a b : Real) : advantageD a b = - advantageD b a := by
  unfold advantageD
  ring

/-- If both output probabilities lie in `[0, 1]`, the absolute signed
advantage is at most one. -/
theorem advantageD_abs_le_one (a b : Real) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : |advantageD a b| ≤ 1 := by
  unfold advantageD
  have h_lower : -1 ≤ b - a := by
    linarith
  have h_upper : b - a ≤ 1 := by
    linarith
  exact abs_le.mpr ⟨h_lower, h_upper⟩

/-- CR18 Definition 2.7: the maximal advantage of a distinguisher class,
`Delta_D(S,T) := sup_{D in D} Delta_D(S,T)`.

The distinguisher class is represented by the index type `D`, and `adv d` is
the signed per-distinguisher advantage of `d`, matching `advantageD`. The
variant for the class of all distinguishers,
`Delta(S,T) := sup_D Delta_D(S,T)`, is the special case where `D` ranges over
the universal/full distinguisher class. -/
def maxAdvantage {D : Type*} (adv : D -> Real) : Real :=
  ⨆ d, adv d

/-- CR18 Definition 2.9: the advantage of a distinguisher `D` in guessing
the bit `B`, `Lambda_D(S, B) := 2 * (Pr_{D(S,B)}(Z = B) - 1/2)`.

The operand `probCorrect` represents `Pr_{D(S,B)}(Z = B)`. The normalization
calibrates random guessing (`probCorrect = 1/2`) to advantage `0`, an always
correct distinguisher (`probCorrect = 1`) to advantage `1`, and a never correct
distinguisher (`probCorrect = 0`) to advantage `-1`. -/
def bitGuessAdvantage (probCorrect : Real) : Real :=
  2 * (probCorrect - (1 / 2 : Real))

/-- The abstract bit-guessing advantage is the normalized probability of
guessing the bit correctly. -/
theorem bitGuessAdvantage_eq (probCorrect : Real) :
    bitGuessAdvantage probCorrect = 2 * (probCorrect - (1 / 2 : Real)) := by
  simp [bitGuessAdvantage]

/-- A random bit guess has zero bit-guessing advantage. -/
theorem bitGuessAdvantage_half : bitGuessAdvantage (1 / 2 : Real) = 0 := by
  norm_num [bitGuessAdvantage]

/-- An always-correct bit guesser has bit-guessing advantage one. -/
theorem bitGuessAdvantage_one : bitGuessAdvantage 1 = 1 := by
  norm_num [bitGuessAdvantage]

/-- A never-correct bit guesser has bit-guessing advantage negative one. -/
theorem bitGuessAdvantage_zero : bitGuessAdvantage 0 = -1 := by
  norm_num [bitGuessAdvantage]

/-- If the correctness probability lies in `[0, 1]`, the bit-guessing
advantage lies in `[-1, 1]`. -/
theorem bitGuessAdvantage_abs_le_one (probCorrect : Real)
    (hprob0 : 0 ≤ probCorrect) (hprob1 : probCorrect ≤ 1) :
    |bitGuessAdvantage probCorrect| ≤ 1 := by
  unfold bitGuessAdvantage
  have h_lower : -1 ≤ 2 * (probCorrect - (1 / 2 : Real)) := by
    linarith
  have h_upper : 2 * (probCorrect - (1 / 2 : Real)) ≤ 1 := by
    linarith
  exact abs_le.mpr ⟨h_lower, h_upper⟩

/-- A correctness probability at least random guessing gives nonnegative
bit-guessing advantage. -/
theorem bitGuessAdvantage_nonneg (probCorrect : Real)
    (hprob : (1 / 2 : Real) ≤ probCorrect) :
    0 ≤ bitGuessAdvantage probCorrect := by
  unfold bitGuessAdvantage
  linarith

/-- If every distinguisher in the class has advantage at most `b`, then the
maximal advantage is at most `b`. -/
lemma maxAdvantage_le {D : Type*} [Nonempty D] (adv : D -> Real) (b : Real)
    (hb : ∀ d, adv d ≤ b) : maxAdvantage adv ≤ b := by
  exact ciSup_le hb

/-- Each distinguisher's advantage is bounded above by the class maximal
advantage whenever the class advantages are bounded above. -/
lemma le_maxAdvantage {D : Type*} (adv : D -> Real) (d : D)
    (h_bdd : BddAbove (Set.range adv)) : adv d ≤ maxAdvantage adv := by
  exact le_ciSup h_bdd d

end RandomSystems.CR18
