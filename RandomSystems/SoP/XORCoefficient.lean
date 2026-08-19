/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORTail

/-!
# Maximal full-support checkerboard coefficients

This file proves the second ingredient in the XOR collision-proxy tail bound.
Exposing the first card of an ordered injection and summing its balanced Walsh
sign over the unused cards gives an exact merge recurrence.  Taking absolute
values only after that cancellation yields the sharp even/odd survivor
envelope and, in particular, Dinur's maximal-coefficient estimate.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORCoefficient

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.XORTail

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Product of the one-row Walsh signs carried by a mask. -/
def checkerProduct {n k : Nat} (a : BitMatrix k n)
    (e : Fin k ↪ XorSpace n) : Real :=
  ∏ i : Fin k, vectorWalsh (a i) (e i)

/-- The matrix Walsh sign is the product of its row signs. -/
theorem walsh_eq_checkerProduct {n k : Nat} (a : BitMatrix k n)
    (x : BitMatrix k n) :
    walsh a x = ∏ i : Fin k, vectorWalsh (a i) (x i) := by
  unfold walsh dot vectorWalsh vectorDot
  rw [show
      bitSign (∑ i : Fin k, ∑ j : Fin n, a i j * x i j) =
        ∏ i : Fin k, bitSign (∑ j : Fin n, a i j * x i j) by
    induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi, bitSign_add, ih]]

/-- Fourier coefficients of the injection density are ordered-injection
checkerboard correlations. -/
theorem fourier_injectionDensity_eq_average_checkerProduct
    {n k : Nat} (hk : k ≤ 2 ^ n) (a : BitMatrix k n) :
    fourier (injectionDensity n k) a =
      average (Fin k ↪ XorSpace n) (checkerProduct a) := by
  rw [fourier_injectionDensity_eq_average_embedding hk]
  congr 1
  funext e
  exact walsh_eq_checkerProduct a e

/-- Sum over the cards omitted by an injection. -/
theorem sum_not_range_embedding {G : Type*} [Fintype G] [DecidableEq G]
    {k : Nat} (e : Fin k ↪ G) (F : G → Real) :
    (∑ x : {x : G // x ∉ Set.range e}, F x.1) =
      (∑ x : G, F x) - ∑ i : Fin k, F (e i) := by
  let R : Finset G := Finset.univ.image e
  have hR : ∀ x : G, x ∈ R ↔ x ∈ Set.range e := by
    intro x
    simp [R]
  have hcompl :
      (∑ x : {x : G // x ∉ Set.range e}, F x.1) =
        ∑ x ∈ Finset.univ \ R, F x := by
    rw [← sum_filter_eq_sum_subtype]
    apply Finset.sum_congr
    · ext x
      simp [hR x]
    · intro x _hx
      rfl
  have hsplit :
      (∑ x ∈ R, F x) + (∑ x ∈ Finset.univ \ R, F x) =
        ∑ x : G, F x := by
    rw [← Finset.sum_union]
    · rw [Finset.union_sdiff_of_subset (by simp [R])]
    · exact Finset.disjoint_sdiff
  have hrange : (∑ x ∈ R, F x) = ∑ i : Fin k, F (e i) := by
    rw [show R = Finset.univ.image e by rfl]
    rw [Finset.sum_image]
    intro i _hi j _hj hij
    exact e.injective hij
  rw [hcompl, ← hrange]
  linarith

/-- Reindex an embedding by its tail and its unused head card. -/
theorem sum_embedding_succ {G : Type*} [Fintype G] [DecidableEq G]
    (k : Nat) (F : (Fin (k + 1) ↪ G) → Real) :
    (∑ e : Fin (k + 1) ↪ G, F e) =
      ∑ t : Fin k ↪ G,
        ∑ x : {x : G // x ∉ Set.range t},
          F ((Equiv.embeddingFinSucc k G).symm ⟨t, x⟩) := by
  calc
    (∑ e : Fin (k + 1) ↪ G, F e) =
        ∑ z : Σ t : Fin k ↪ G, {x : G // x ∉ Set.range t},
          F ((Equiv.embeddingFinSucc k G).symm z) := by
      exact Fintype.sum_equiv (Equiv.embeddingFinSucc k G)
        F (fun z => F ((Equiv.embeddingFinSucc k G).symm z))
        (fun e => by simp)
    _ = _ := by rw [Fintype.sum_sigma]

/-- Delete the head row of a mask. -/
def tailMask {n k : Nat} (a : BitMatrix (k + 1) n) : BitMatrix k n :=
  fun i => a i.succ

/-- Merge the exposed head character into tail row `j`. -/
def mergeHead {n k : Nat} (a : BitMatrix (k + 1) n) (j : Fin k) :
    BitMatrix k n :=
  Function.update (tailMask a) j (a 0 + a j.succ)

theorem checkerProduct_cons {n k : Nat} (a : BitMatrix (k + 1) n)
    (t : Fin k ↪ XorSpace n) (x : {x : XorSpace n // x ∉ Set.range t}) :
    checkerProduct a ((Equiv.embeddingFinSucc k (XorSpace n)).symm ⟨t, x⟩) =
      vectorWalsh (a 0) x.1 * checkerProduct (tailMask a) t := by
  unfold checkerProduct tailMask
  rw [Fin.prod_univ_succ]
  simp

/-- A merged checkerboard is the tail checkerboard with one additional head
sign attached at row `j`. -/
theorem checkerProduct_mergeHead {n k : Nat} (a : BitMatrix (k + 1) n)
    (j : Fin k) (t : Fin k ↪ XorSpace n) :
    checkerProduct (mergeHead a j) t =
      vectorWalsh (a 0) (t j) * checkerProduct (tailMask a) t := by
  unfold checkerProduct
  rw [Fintype.prod_eq_mul_prod_compl j]
  rw [Fintype.prod_eq_mul_prod_compl j]
  unfold mergeHead
  rw [Function.update_self, vectorWalsh_add_left]
  rw [mul_assoc]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i ≠ j := by simpa using hi
  simp [hij]

/-- The unused-card sum of a nontrivial Walsh sign is the negative of its
sum over the cards already used by the tail injection. -/
theorem sum_unused_vectorWalsh {n k : Nat} (head : XorSpace n)
    (hhead : head ≠ 0) (t : Fin k ↪ XorSpace n) :
    (∑ x : {x : XorSpace n // x ∉ Set.range t}, vectorWalsh head x.1) =
      -∑ j : Fin k, vectorWalsh head (t j) := by
  rw [sum_not_range_embedding]
  rw [sum_vectorWalsh, if_neg hhead]
  ring

/-- Ordered-injection checkerboard correlation. -/
def checkerCorrelation {n k : Nat} (a : BitMatrix k n) : Real :=
  average (Fin k ↪ XorSpace n) (checkerProduct a)

/-- Numerator form of the exposed-card merge recurrence. -/
theorem sum_checkerProduct_succ {n k : Nat} (a : BitMatrix (k + 1) n)
    (hhead : a 0 ≠ 0) :
    (∑ e : Fin (k + 1) ↪ XorSpace n, checkerProduct a e) =
      -∑ j : Fin k,
        ∑ t : Fin k ↪ XorSpace n, checkerProduct (mergeHead a j) t := by
  rw [sum_embedding_succ]
  calc
    (∑ t : Fin k ↪ XorSpace n,
        ∑ x : {x : XorSpace n // x ∉ Set.range t},
          checkerProduct a
            ((Equiv.embeddingFinSucc k (XorSpace n)).symm ⟨t, x⟩)) =
      ∑ t : Fin k ↪ XorSpace n,
        checkerProduct (tailMask a) t *
          (∑ x : {x : XorSpace n // x ∉ Set.range t},
            vectorWalsh (a 0) x.1) := by
      apply Finset.sum_congr rfl
      intro t _ht
      simp_rw [checkerProduct_cons]
      rw [← Finset.sum_mul]
      ring
    _ = ∑ t : Fin k ↪ XorSpace n,
        checkerProduct (tailMask a) t *
          (-∑ j : Fin k, vectorWalsh (a 0) (t j)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [sum_unused_vectorWalsh (a 0) hhead t]
    _ = -∑ j : Fin k,
        ∑ t : Fin k ↪ XorSpace n,
          vectorWalsh (a 0) (t j) * checkerProduct (tailMask a) t := by
      rw [show (fun t : Fin k ↪ XorSpace n =>
          checkerProduct (tailMask a) t *
            (-∑ j : Fin k, vectorWalsh (a 0) (t j))) =
          (fun t => -∑ j : Fin k,
            vectorWalsh (a 0) (t j) * checkerProduct (tailMask a) t) by
        funext t
        rw [show (∑ j : Fin k,
            vectorWalsh (a 0) (t j) * checkerProduct (tailMask a) t) =
          checkerProduct (tailMask a) t *
            ∑ j : Fin k, vectorWalsh (a 0) (t j) by
          rw [← Finset.sum_mul]
          ring]
        ring]
      rw [Finset.sum_neg_distrib, Finset.sum_comm]
    _ = -∑ j : Fin k,
        ∑ t : Fin k ↪ XorSpace n, checkerProduct (mergeHead a j) t := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro t _ht
      rw [checkerProduct_mergeHead]

/-- Exact exposed-card recurrence after probability normalization. -/
theorem checkerCorrelation_succ_eq {n k : Nat}
    (hk : k + 1 ≤ 2 ^ n) (a : BitMatrix (k + 1) n)
    (hhead : a 0 ≠ 0) :
    checkerCorrelation a =
      -(1 / (((2 ^ n - k : Nat) : Real))) *
        ∑ j : Fin k, checkerCorrelation (mergeHead a j) := by
  let N : Nat := 2 ^ n
  let D : Nat := N.descFactorial k
  have hkN : k < N := by simpa [N] using hk
  have hD : (D : Real) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (Nat.le_of_lt hkN)).ne'
  have hNk : ((N - k : Nat) : Real) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hkN
  unfold checkerCorrelation average
  rw [sum_checkerProduct_succ a hhead]
  rw [Fintype.card_embedding_eq, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_fin]
  rw [Nat.descFactorial_succ]
  simp only [card_xorSpace]
  change
    (-∑ j : Fin k,
        ∑ t : Fin k ↪ XorSpace n, checkerProduct (mergeHead a j) t) /
          (((N - k) * D : Nat) : Real) =
      -(1 / ((N - k : Nat) : Real)) *
        ∑ j : Fin k,
          (∑ t : Fin k ↪ XorSpace n,
            checkerProduct (mergeHead a j) t) / (D : Real)
  rw [Nat.cast_mul]
  rw [← Finset.sum_div]
  field_simp [hD, hNk]

/-- Merging the head changes the full tail level only when the merged row
cancels to zero. -/
theorem level_mergeHead {n k : Nat} (a : BitMatrix (k + 1) n)
    (hfull : ∀ i, a i ≠ 0) (j : Fin k) :
    level (mergeHead a j) =
      if a 0 + a j.succ = 0 then k - 1 else k := by
  by_cases hz : a 0 + a j.succ = 0
  · rw [if_pos hz]
    have hsupp : rowSupport (mergeHead a j) = Finset.univ.erase j := by
      ext i
      rw [mem_rowSupport]
      by_cases hij : i = j
      · subst i
        simp [mergeHead, hz]
      · simp [mergeHead, tailMask, hij, hfull i.succ]
    unfold level
    rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp
  · rw [if_neg hz]
    have hsupp : rowSupport (mergeHead a j) = Finset.univ := by
      ext i
      rw [mem_rowSupport]
      by_cases hij : i = j
      · subst i
        simp [mergeHead, hz]
      · simp [mergeHead, tailMask, hij, hfull i.succ]
    unfold level
    rw [hsupp]
    simp

/-- Positive survivor envelope generated by the exposed-card recurrence. -/
def coefficientEnvelope (N : Nat) : Nat → Real
  | 0 => 1
  | 1 => 0
  | k + 2 =>
      ((k + 1 : Nat) : Real) / (((N - (k + 1) : Nat) : Real)) *
        max (coefficientEnvelope N (k + 1)) (coefficientEnvelope N k)

theorem coefficientEnvelope_nonneg (N k : Nat) :
    0 ≤ coefficientEnvelope N k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | _ | k
      · simp [coefficientEnvelope]
      · simp [coefficientEnvelope]
      · simp only [coefficientEnvelope]
        exact mul_nonneg (by positivity)
          ((ih k (by omega)).trans (le_max_right _ _))

/-- Every injection coefficient is controlled by the survivor envelope at
its exact row level. -/
theorem abs_fourier_injectionDensity_le_coefficientEnvelope
    {n q : Nat} (hq : q ≤ 2 ^ n) (a : BitMatrix q n) :
    |fourier (injectionDensity n q) a| ≤
      coefficientEnvelope (2 ^ n) (level a) := by
  let N : Nat := 2 ^ n
  have main : ∀ r : Nat, ∀ (q : Nat), q ≤ N → ∀ a : BitMatrix q n,
      level a = r →
        |fourier (injectionDensity n q) a| ≤ coefficientEnvelope N r := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
        intro q hq a ha
        rcases r with _ | _ | k
        · have ha0 : a = 0 := (level_eq_zero_iff a).mp ha
          subst a
          rw [fourier_injectionDensity_zero (by simpa [N] using hq)]
          simp [coefficientEnvelope]
        · rw [fourier_injectionDensity_of_level_eq_one
              (by simpa [N] using hq) a ha]
          simp [coefficientEnvelope]
        · have hrq : k + 2 ≤ q := by
            rw [← ha]
            exact level_le_rows a
          have hrN : k + 2 ≤ N := hrq.trans hq
          let A : LevelMask n q (k + 2) := ⟨a, ha⟩
          let S : KSupport q (k + 2) := levelSupportOf A
          let z : {a : LevelMask n q (k + 2) // levelSupportOf a = S} :=
            ⟨A, rfl⟩
          let b : FullMask n (k + 2) := levelMaskFiberEquiv S z
          have hfour :
              fourier (injectionDensity n q) a =
                fourier (injectionDensity n (k + 2)) b.1 := by
            simpa [A, S, z, b] using
              (fourier_levelMask_eq_fiber
                (n := n) (q := q) (k := k + 2)
                (by simpa [N] using hq) S z)
          rw [hfour]
          rw [fourier_injectionDensity_eq_average_checkerProduct
            (by simpa [N] using hrN)]
          change |checkerCorrelation b.1| ≤ coefficientEnvelope N (k + 2)
          have hrec := checkerCorrelation_succ_eq
            (n := n) (k := k + 1) (by simpa [N] using hrN)
              b.1 (b.2 0)
          have hrec' : checkerCorrelation b.1 =
              -(1 / ((N - (k + 1) : Nat) : Real)) *
                ∑ j : Fin (k + 1), checkerCorrelation (mergeHead b.1 j) := by
            simpa [N] using hrec
          have hdenpos : (0 : Real) < ((N - (k + 1) : Nat) : Real) := by
            exact_mod_cast Nat.sub_pos_of_lt (by omega : k + 1 < N)
          have hterm (j : Fin (k + 1)) :
              |checkerCorrelation (mergeHead b.1 j)| ≤
                max (coefficientEnvelope N (k + 1))
                  (coefficientEnvelope N k) := by
            let m : BitMatrix (k + 1) n := mergeHead b.1 j
            have hmlevel := level_mergeHead b.1 b.2 j
            have hm_lt : level m < k + 2 := by
              exact (level_le_rows m).trans_lt (by omega)
            have hm := ih (level m) hm_lt (k + 1) (by omega) m rfl
            rw [fourier_injectionDensity_eq_average_checkerProduct
              (by simpa [N] using (show k + 1 ≤ N by omega))] at hm
            change |checkerCorrelation m| ≤ _ at hm
            by_cases hz : b.1 0 + b.1 j.succ = 0
            · rw [hmlevel, if_pos hz] at hm
              have hlevel : k + 1 - 1 = k := by omega
              rw [hlevel] at hm
              exact hm.trans (le_max_right _ _)
            · rw [hmlevel, if_neg hz] at hm
              exact hm.trans (le_max_left _ _)
          calc
            |checkerCorrelation b.1| =
                (1 / ((N - (k + 1) : Nat) : Real)) *
                  |∑ j : Fin (k + 1), checkerCorrelation (mergeHead b.1 j)| := by
              rw [hrec', abs_mul, abs_neg, abs_div, abs_one,
                abs_of_pos hdenpos]
            _ ≤ (1 / ((N - (k + 1) : Nat) : Real)) *
                  ∑ j : Fin (k + 1),
                    |checkerCorrelation (mergeHead b.1 j)| := by
              exact mul_le_mul_of_nonneg_left
                (Finset.abs_sum_le_sum_abs _ _) (by positivity)
            _ ≤ (1 / ((N - (k + 1) : Nat) : Real)) *
                  ∑ _j : Fin (k + 1),
                    max (coefficientEnvelope N (k + 1))
                      (coefficientEnvelope N k) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact Finset.sum_le_sum fun j _hj => hterm j
            _ = coefficientEnvelope N (k + 2) := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
                Fintype.card_fin]
              simp only [coefficientEnvelope]
              field_simp [hdenpos.ne']
  simpa [N] using main (level a) q (by simpa [N] using hq) a rfl

/-- The two-step rational contraction behind the binomial envelope. -/
theorem coefficient_ratio_sq_mul_choose_inv_le {N k : Nat}
    (hk : 2 * (k + 2) ≤ N) :
    (((k + 1 : Nat) : Real) / (((N - (k + 1) : Nat) : Real))) ^ 2 *
        (1 / (N.choose k : Real)) ≤
      1 / (N.choose (k + 2) : Real) := by
  let j : Nat := k + 1
  let d : Nat := N - j
  let A : Nat := N.choose k
  let B : Nat := N.choose j
  let C : Nat := N.choose (k + 2)
  have hkN : k ≤ N := by omega
  have hjN : j ≤ N := by omega
  have hj1N : k + 2 ≤ N := by omega
  have hdpos : 0 < d := by omega
  have hApos : 0 < A := by
    exact Nat.choose_pos hkN
  have hCpos : 0 < C := by
    exact Nat.choose_pos hj1N
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hdpos
  have hAR : (0 : Real) < (A : Real) := by exact_mod_cast hApos
  have hCR : (0 : Real) < (C : Real) := by exact_mod_cast hCpos
  have hrel1 : B * j = A * (N - k) := by
    simpa [A, B, j] using Nat.choose_succ_right_eq N k
  have hrel2 : C * (k + 2) = B * d := by
    simpa [B, C, d, j, Nat.add_assoc] using
      Nat.choose_succ_right_eq N (k + 1)
  have hcoef : (j : Real) * ((N - k : Nat) : Real) ≤
      (d : Real) * ((k + 2 : Nat) : Real) := by
    have hkR : ((2 * (k + 2) : Nat) : Real) ≤ (N : Real) := by
      exact_mod_cast hk
    dsimp [j, d]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num [Nat.cast_mul, Nat.cast_add] at hkR ⊢
    nlinarith
  have hrel1R : (B : Real) * (j : Real) =
      (A : Real) * ((N - k : Nat) : Real) := by
    exact_mod_cast hrel1
  have hrel2R : (C : Real) * ((k + 2 : Nat) : Real) =
      (B : Real) * (d : Real) := by
    exact_mod_cast hrel2
  have hpoly : (j : Real) ^ 2 * (C : Real) ≤
      (d : Real) ^ 2 * (A : Real) := by
    norm_num [Nat.cast_add] at hrel2R hcoef
    have hk2R : (0 : Real) < (k : Real) + 2 := by positivity
    apply le_of_mul_le_mul_right ?_ hk2R
    calc
      (j : Real) ^ 2 * (C : Real) * ((k : Real) + 2) =
          (j : Real) ^ 2 * ((C : Real) * ((k : Real) + 2)) := by ring
      _ = (j : Real) ^ 2 * ((B : Real) * (d : Real)) := by rw [hrel2R]
      _ = ((B : Real) * (j : Real)) *
          ((j : Real) * (d : Real)) := by ring
      _ = ((A : Real) * ((N - k : Nat) : Real)) *
          ((j : Real) * (d : Real)) := by rw [hrel1R]
      _ = (A : Real) * (d : Real) *
          ((j : Real) * ((N - k : Nat) : Real)) := by
        ring
      _ ≤ (A : Real) * (d : Real) *
          ((d : Real) * ((k : Real) + 2)) := by
        exact mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = (d : Real) ^ 2 * (A : Real) * ((k : Real) + 2) := by
        ring
  change ((j : Real) / (d : Real)) ^ 2 * (1 / (A : Real)) ≤
    1 / (C : Real)
  rw [show ((j : Real) / (d : Real)) ^ 2 * (1 / (A : Real)) =
      (j : Real) ^ 2 / ((d : Real) ^ 2 * (A : Real)) by
    field_simp [hdR.ne', hAR.ne']]
  rw [div_le_div_iff₀ (mul_pos (sq_pos_of_pos hdR) hAR) hCR]
  simpa using hpoly

/-- Dinur's maximal-coefficient estimate, obtained here from the sharper
one-step survivor recurrence. -/
theorem coefficientEnvelope_sq_le_choose_inv {N k : Nat}
    (hk : 2 * k ≤ N) :
    (coefficientEnvelope N k) ^ 2 ≤ 1 / (N.choose k : Real) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      rcases k with _ | _ | k
      · norm_num [coefficientEnvelope]
      · simp [coefficientEnvelope]
      · have hk0 : 2 * k ≤ N := by omega
        have hk1 : 2 * (k + 1) ≤ N := by omega
        have hprev := ih k (by omega) hk0
        have hcur := ih (k + 1) (by omega) hk1
        have hchoose : N.choose k ≤ N.choose (k + 1) := by
          apply Nat.choose_le_succ_of_lt_half_left
          omega
        have hchoosePos : (0 : Real) < (N.choose k : Real) := by
          exact_mod_cast Nat.choose_pos (by omega : k ≤ N)
        have hrecip : 1 / (N.choose (k + 1) : Real) ≤
            1 / (N.choose k : Real) := by
          apply one_div_le_one_div_of_le hchoosePos
          exact_mod_cast hchoose
        have hmax :
            (max (coefficientEnvelope N (k + 1))
              (coefficientEnvelope N k)) ^ 2 ≤
                1 / (N.choose k : Real) := by
          rcases le_total (coefficientEnvelope N (k + 1))
              (coefficientEnvelope N k) with hle | hge
          · rw [max_eq_right hle]
            exact hprev
          · rw [max_eq_left hge]
            exact hcur.trans hrecip
        rw [coefficientEnvelope]
        calc
          ((((k + 1 : Nat) : Real) / (((N - (k + 1) : Nat) : Real))) *
              max (coefficientEnvelope N (k + 1))
                (coefficientEnvelope N k)) ^ 2 =
            (((k + 1 : Nat) : Real) / (((N - (k + 1) : Nat) : Real))) ^ 2 *
              (max (coefficientEnvelope N (k + 1))
                (coefficientEnvelope N k)) ^ 2 := by ring
          _ ≤ (((k + 1 : Nat) : Real) /
                (((N - (k + 1) : Nat) : Real))) ^ 2 *
              (1 / (N.choose k : Real)) := by
            exact mul_le_mul_of_nonneg_left hmax (sq_nonneg _)
          _ ≤ 1 / (N.choose (k + 2) : Real) :=
            coefficient_ratio_sq_mul_choose_inv_le hk

/-- Pointwise maximal-coefficient bound in the form consumed by the fourth
energy estimate. -/
theorem fourier_injectionDensity_sq_le_choose_inv
    {n q : Nat} (hq : q ≤ 2 ^ n) (hhalf : 2 * q ≤ 2 ^ n)
    (a : BitMatrix q n) :
    (fourier (injectionDensity n q) a) ^ 2 ≤
      1 / ((2 ^ n).choose (level a) : Real) := by
  have habs := abs_fourier_injectionDensity_le_coefficientEnvelope hq a
  have henv := coefficientEnvelope_sq_le_choose_inv
    (N := 2 ^ n) (k := level a) (by
      exact (Nat.mul_le_mul_left 2 (level_le_rows a)).trans hhalf)
  calc
    (fourier (injectionDensity n q) a) ^ 2 =
        |fourier (injectionDensity n q) a| ^ 2 := by rw [sq_abs]
    _ ≤ (coefficientEnvelope (2 ^ n) (level a)) ^ 2 := by
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ _ := henv

theorem level_fullMask {n k : Nat} (a : FullMask n k) :
    level a.1 = k := by
  have hsupp : rowSupport a.1 = Finset.univ := by
    ext i
    rw [mem_rowSupport]
    simp [a.2 i]
  unfold level
  rw [hsupp]
  simp

/-- Fourth energy is the second energy times the sharp maximal squared
coefficient. -/
theorem fullFourthEnergy_le_choose_inv_mul_fullSecondEnergy
    {n k : Nat} (hhalf : 2 * k ≤ 2 ^ n) :
    fullFourthEnergy n k ≤
      (1 / ((2 ^ n).choose k : Real)) * fullSecondEnergy n k := by
  unfold fullFourthEnergy fullSecondEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _ha
  let c : Real := fourier (injectionDensity n k) a.1
  have hc := fourier_injectionDensity_sq_le_choose_inv
    (n := n) (q := k) (by omega) hhalf a.1
  rw [level_fullMask a] at hc
  change c ^ 2 ≤ 1 / ((2 ^ n).choose k : Real) at hc
  change c ^ 4 ≤ (1 / ((2 ^ n).choose k : Real)) * c ^ 2
  calc
    c ^ 4 = c ^ 2 * c ^ 2 := by ring
    _ ≤ (1 / ((2 ^ n).choose k : Real)) * c ^ 2 := by
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg c)
  rfl

/-- Level-`k` fourth energy with query-support multiplicity exposed. -/
theorem injectionLevelEnergy_le_choose_ratio_mul_fullSecondEnergy
    {n q k : Nat} (hq : q ≤ 2 ^ n) (hhalf : 2 * k ≤ 2 ^ n) :
    injectionLevelEnergy n q k ≤
      (q.choose k : Real) *
        (1 / ((2 ^ n).choose k : Real)) * fullSecondEnergy n k := by
  rw [injectionLevelEnergy_eq_choose_mul_fullFourthEnergy hq]
  have h := mul_le_mul_of_nonneg_left
    (fullFourthEnergy_le_choose_inv_mul_fullSecondEnergy hhalf)
    (show (0 : Real) ≤ (q.choose k : Real) by positivity)
  simpa [mul_assoc] using h

end RandomSystems.SoP.XORCoefficient
