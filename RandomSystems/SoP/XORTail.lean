/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Group.ForwardDiff
import RandomSystems.SoP.XORCore

/-!
# Full-support Fourier energies for XOR SoP

This file separates query-support multiplicity from the intrinsic
`k`-coordinate checkerboard calculation.  It is the support-reindexing layer
used by the higher-order broken-cycle tail bound.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.SoP.XORTail

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Masks using every one of their `k` rows. -/
abbrev FullMask (n k : Nat) :=
  {a : BitMatrix k n // ∀ i, a i ≠ 0}

/-- Intrinsic second Fourier energy on `k` used rows. -/
def fullSecondEnergy (n k : Nat) : Real :=
  ∑ a : FullMask n k,
    (fourier (injectionDensity n k) a.1) ^ 2

/-- Intrinsic fourth Fourier energy on `k` used rows. -/
def fullFourthEnergy (n k : Nat) : Real :=
  ∑ a : FullMask n k,
    (fourier (injectionDensity n k) a.1) ^ 4

/-- Query supports of cardinality `k`. -/
abbrev KSupport (q k : Nat) :=
  {S : Finset (Fin q) // S.card = k}

/-- Masks on `q` rows whose exact row support has cardinality `k`. -/
abbrev LevelMask (n q k : Nat) :=
  {a : BitMatrix q n // level a = k}

/-- The exact support carried by a level-`k` mask. -/
def levelSupportOf {n q k : Nat} (a : LevelMask n q k) : KSupport q k :=
  ⟨rowSupport a.1, by simpa [level] using a.2⟩

/-- Canonical enumeration of a support of cardinality `k`. -/
def supportEquivFin {q k : Nat} (S : KSupport q k) : Fin k ≃ S.1 :=
  (finCongr (by simpa using S.2)).symm.trans (Fintype.equivFin S.1).symm

/-- A fiber of the exact-support map is a full mask on `k` coordinates. -/
def levelMaskFiberEquiv {n q k : Nat} (S : KSupport q k) :
    {a : LevelMask n q k // levelSupportOf a = S} ≃ FullMask n k where
  toFun a := ⟨fun i => a.1.1 ((supportEquivFin S i).1), by
    intro i
    have hsupp : rowSupport a.1.1 = S.1 := congrArg Subtype.val a.2
    apply (mem_rowSupport a.1.1 ((supportEquivFin S i).1)).mp
    rw [hsupp]
    exact (supportEquivFin S i).2⟩
  invFun b :=
    let f : S.1 → XorSpace n := fun i => b.1 ((supportEquivFin S).symm i)
    ⟨⟨supportExtension S.1 f, by
        unfold level
        rw [rowSupport_supportExtension S.1 f]
        · exact S.2
        · intro i
          exact b.2 ((supportEquivFin S).symm i)⟩, by
      apply Subtype.ext
      change rowSupport (supportExtension S.1 f) = S.1
      apply rowSupport_supportExtension
      intro i
      exact b.2 ((supportEquivFin S).symm i)⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    have hsupp : rowSupport a.1.1 = S.1 := congrArg Subtype.val a.2
    funext i j
    by_cases hi : i ∈ S.1
    · let is : S.1 := ⟨i, hi⟩
      have hie : (supportEquivFin S ((supportEquivFin S).symm is)).1 = i := by
        simp [is]
      simp [supportExtension, hi, hie, is]
    · have hz : a.1.1 i = 0 := by
        rw [← hsupp] at hi
        simpa using hi
      simp [supportExtension, hi, hz]
  right_inv b := by
    apply Subtype.ext
    funext i j
    simp [supportExtension]

/-- The fiber equivalence is exactly restriction along the canonical support
embedding. -/
theorem levelMaskFiberEquiv_apply {n q k : Nat} (S : KSupport q k)
    (a : {a : LevelMask n q k // levelSupportOf a = S}) :
    (levelMaskFiberEquiv S a).1 =
      restrictMask
        ((supportEquivFin S).toEmbedding.trans
          (Function.Embedding.subtype (fun i => i ∈ S.1))) a.1.1 := by
  rfl

/-- Restricting to an exact support preserves the injection Fourier
coefficient. -/
theorem fourier_levelMask_eq_fiber {n q k : Nat} (hq : q ≤ 2 ^ n)
    (S : KSupport q k)
    (a : {a : LevelMask n q k // levelSupportOf a = S}) :
    fourier (injectionDensity n q) a.1.1 =
      fourier (injectionDensity n k) (levelMaskFiberEquiv S a).1 := by
  let r : Fin k ↪ Fin q :=
    (supportEquivFin S).toEmbedding.trans
      (Function.Embedding.subtype (fun i => i ∈ S.1))
  have hsupp : rowSupport a.1.1 = S.1 := congrArg Subtype.val a.2
  have hout : ∀ i, i ∉ Set.range r -> a.1.1 i = 0 := by
    intro i hi
    by_contra hne
    have hiS : i ∈ S.1 := by
      rw [← hsupp]
      exact (mem_rowSupport a.1.1 i).mpr hne
    apply hi
    let is : S.1 := ⟨i, hiS⟩
    refine ⟨(supportEquivFin S).symm is, ?_⟩
    change ((supportEquivFin S) ((supportEquivFin S).symm is)).1 = i
    simp [is]
  rw [fourier_injectionDensity_eq_restrictMask hq r a.1.1 hout]
  rfl

/-- Number of `k`-element query supports. -/
theorem card_kSupport (q k : Nat) :
    Fintype.card (KSupport q k) = q.choose k := by
  let e : KSupport q k ≃
      {S : Finset (Fin q) //
        S ∈ (Finset.univ : Finset (Fin q)).powersetCard k} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun S => by simp)
  rw [Fintype.card_congr e, Fintype.card_coe]
  simp [Finset.card_powersetCard]

/-- Reindex a filtered finite sum as a sum over the corresponding subtype. -/
theorem sum_filter_eq_sum_subtype {A : Type*} [Fintype A] [DecidableEq A]
    (p : A → Prop) [DecidablePred p] (F : A → Real) :
    (∑ a ∈ (Finset.univ : Finset A).filter p, F a) =
      ∑ a : {a : A // p a}, F a.1 := by
  rw [Finset.sum_subtype]
  intro a
  simp

/-- Exact support-multiplicity factorization of the fourth energy. -/
theorem injectionLevelEnergy_eq_choose_mul_fullFourthEnergy
    {n q k : Nat} (hq : q ≤ 2 ^ n) :
    injectionLevelEnergy n q k =
      (q.choose k : Real) * fullFourthEnergy n k := by
  unfold injectionLevelEnergy
  rw [sum_filter_eq_sum_subtype]
  let E := Equiv.sigmaFiberEquiv (levelSupportOf (n := n) (q := q) (k := k))
  calc
    (∑ a : LevelMask n q k,
        (fourier (injectionDensity n q) a.1) ^ 4) =
      ∑ z : Σ S : KSupport q k,
          {a : LevelMask n q k // levelSupportOf a = S},
        (fourier (injectionDensity n q) (E z).1) ^ 4 := by
      exact (Fintype.sum_equiv E
        (fun z => (fourier (injectionDensity n q) (E z).1) ^ 4)
        (fun a : LevelMask n q k =>
          (fourier (injectionDensity n q) a.1) ^ 4)
        (fun _z => rfl)).symm
    _ = ∑ S : KSupport q k,
        ∑ a : {a : LevelMask n q k // levelSupportOf a = S},
          (fourier (injectionDensity n q) a.1.1) ^ 4 := by
      rw [Fintype.sum_sigma]
      simp [E]
    _ = ∑ _S : KSupport q k, fullFourthEnergy n k := by
      apply Finset.sum_congr rfl
      intro S _hS
      unfold fullFourthEnergy
      exact Fintype.sum_equiv (levelMaskFiberEquiv S)
        (fun a : {a : LevelMask n q k // levelSupportOf a = S} =>
          (fourier (injectionDensity n q) a.1.1) ^ 4)
        (fun b : FullMask n k =>
          (fourier (injectionDensity n k) b.1) ^ 4)
        (fun a => by
          dsimp
          rw [fourier_levelMask_eq_fiber hq S a])
    _ = (q.choose k : Real) * fullFourthEnergy n k := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul, Finset.card_univ, card_kSupport]

/-- The same exact support factorization for second energy. -/
theorem levelSecondEnergy_eq_choose_mul_fullSecondEnergy
    {n q k : Nat} (hq : q ≤ 2 ^ n) :
    (∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
        (fun a => level a = k),
      (fourier (injectionDensity n q) a) ^ 2) =
      (q.choose k : Real) * fullSecondEnergy n k := by
  rw [sum_filter_eq_sum_subtype]
  let E := Equiv.sigmaFiberEquiv (levelSupportOf (n := n) (q := q) (k := k))
  calc
    (∑ a : LevelMask n q k,
        (fourier (injectionDensity n q) a.1) ^ 2) =
      ∑ z : Σ S : KSupport q k,
          {a : LevelMask n q k // levelSupportOf a = S},
        (fourier (injectionDensity n q) (E z).1) ^ 2 := by
      exact (Fintype.sum_equiv E
        (fun z => (fourier (injectionDensity n q) (E z).1) ^ 2)
        (fun a : LevelMask n q k =>
          (fourier (injectionDensity n q) a.1) ^ 2)
        (fun _z => rfl)).symm
    _ = ∑ S : KSupport q k,
        ∑ a : {a : LevelMask n q k // levelSupportOf a = S},
          (fourier (injectionDensity n q) a.1.1) ^ 2 := by
      rw [Fintype.sum_sigma]
      simp [E]
    _ = ∑ _S : KSupport q k, fullSecondEnergy n k := by
      apply Finset.sum_congr rfl
      intro S _hS
      unfold fullSecondEnergy
      exact Fintype.sum_equiv (levelMaskFiberEquiv S)
        (fun a : {a : LevelMask n q k // levelSupportOf a = S} =>
          (fourier (injectionDensity n q) a.1.1) ^ 2)
        (fun b : FullMask n k =>
          (fourier (injectionDensity n k) b.1) ^ 2)
        (fun a => by
          dsimp
          rw [fourier_levelMask_eq_fiber hq S a])
    _ = (q.choose k : Real) * fullSecondEnergy n k := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul, Finset.card_univ, card_kSupport]

/-! ## Total second energy and the binomial support transform -/

/-- Total squared Fourier mass of the injection density. -/
def totalSecondEnergy (n k : Nat) : Real :=
  ∑ a : BitMatrix k n, (fourier (injectionDensity n k) a) ^ 2

/-- The squared `L2` norm of the injection density is its constant nonzero
density value, namely `N^k/(N)_k`. -/
theorem average_injectionDensity_sq_eq {n k : Nat} (hk : k ≤ 2 ^ n) :
    average (BitMatrix k n) (fun x => (injectionDensity n k x) ^ 2) =
      (((2 ^ n : Nat) : Real) ^ k) /
        (((2 ^ n).descFactorial k : Nat) : Real) := by
  let N : Nat := 2 ^ n
  let D : Nat := N.descFactorial k
  have hD : D ≠ 0 :=
    (Nat.descFactorial_pos.mpr (by simpa [N] using hk)).ne'
  have hDR : (D : Real) ≠ 0 := by exact_mod_cast hD
  have hNR : (N : Real) ≠ 0 := by dsimp [N]; positivity
  have hcardInjective :
      ((Finset.univ : Finset (BitMatrix k n)).filter
        (fun x => Function.Injective x)).card = D := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr
      (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (XorSpace n))]
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    simp [D, N, card_xorSpace]
  unfold average injectionDensity
  rw [show
      (∑ x : BitMatrix k n,
        (if Function.Injective x then (N : Real) ^ k / (D : Real) else 0) ^ 2) =
      (((Finset.univ : Finset (BitMatrix k n)).filter
        (fun x => Function.Injective x)).card : Real) *
          (((N : Real) ^ k / (D : Real)) ^ 2) by
      rw [show
          (fun x : BitMatrix k n =>
            (if Function.Injective x then
              (N : Real) ^ k / (D : Real) else 0) ^ 2) =
          (fun x => if Function.Injective x then
            (((N : Real) ^ k / (D : Real)) ^ 2) else 0) by
        funext x
        by_cases hx : Function.Injective x <;> simp [hx]]
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]]
  rw [hcardInjective]
  have hcard : Fintype.card (BitMatrix k n) = N ^ k := by
    simp [BitMatrix, N]
  rw [hcard]
  change (D : Real) * (((N : Real) ^ k / (D : Real)) ^ 2) /
      (((N ^ k : Nat) : Real)) = (N : Real) ^ k / (D : Real)
  norm_num [Nat.cast_pow]
  field_simp [hDR, hNR]

theorem totalSecondEnergy_eq {n k : Nat} (hk : k ≤ 2 ^ n) :
    totalSecondEnergy n k =
      (((2 ^ n : Nat) : Real) ^ k) /
        (((2 ^ n).descFactorial k : Nat) : Real) := by
  unfold totalSecondEnergy
  rw [← parseval_sq]
  exact average_injectionDensity_sq_eq hk

/-- Any finite mask has at most all `q` query rows in its support. -/
theorem level_le_rows {n q : Nat} (a : BitMatrix q n) : level a ≤ q := by
  unfold level
  calc
    (rowSupport a).card ≤ (Finset.univ : Finset (Fin q)).card :=
      Finset.card_le_card (by simp)
    _ = q := by simp

/-- Partition a finite sum by the exact row level. -/
theorem sum_eq_sum_levels {n q : Nat} (F : BitMatrix q n → Real) :
    (∑ a : BitMatrix q n, F a) =
      ∑ k ∈ Finset.range (q + 1),
        ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
          (fun a => level a = k), F a := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  have hmem : level a ∈ Finset.range (q + 1) := by
    simp
    exact level_le_rows a
  simpa [eq_comm, hmem] using
    (Finset.sum_ite_eq' (Finset.range (q + 1)) (level a) (fun _k => F a))

/-- Total Fourier mass is the binomial transform of the intrinsic full-support
weights. -/
theorem totalSecondEnergy_eq_sum_choose_fullSecondEnergy
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    totalSecondEnergy n q =
      ∑ k ∈ Finset.range (q + 1),
        (q.choose k : Real) * fullSecondEnergy n k := by
  unfold totalSecondEnergy
  rw [sum_eq_sum_levels]
  apply Finset.sum_congr rfl
  intro k _hk
  exact levelSecondEnergy_eq_choose_mul_fullSecondEnergy hq

/-! ## Dinur's normalized Pascal weight as a forward difference -/

/-- The intrinsic full-support weight is the corresponding forward difference
of the total collision energy.  This is binomial inversion supplied by the
Gregory--Newton formula, with no separately postulated mirror recurrence. -/
theorem fullSecondEnergy_eq_forwardDiff {n k : Nat} (hk : k ≤ 2 ^ n) :
    fullSecondEnergy n k =
      (fwdDiff (1 : Nat))^[k] (totalSecondEnergy n) 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      have htransform :=
        totalSecondEnergy_eq_sum_choose_fullSecondEnergy (n := n) (q := k) hk
      have hnewton :=
        shift_eq_sum_fwdDiff_iter (M := Nat) (G := Real) (1 : Nat)
          (totalSecondEnergy n) k 0
      have hnewton' :
          totalSecondEnergy n k =
            ∑ r ∈ Finset.range (k + 1),
              (k.choose r : Real) *
                (fwdDiff (1 : Nat))^[r] (totalSecondEnergy n) 0 := by
        simpa [nsmul_eq_mul] using hnewton
      have heq :
          (∑ r ∈ Finset.range (k + 1),
              (k.choose r : Real) * fullSecondEnergy n r) =
            ∑ r ∈ Finset.range (k + 1),
              (k.choose r : Real) *
                (fwdDiff (1 : Nat))^[r] (totalSecondEnergy n) 0 :=
        htransform.symm.trans hnewton'
      have hlower :
          (∑ r ∈ Finset.range k,
              (k.choose r : Real) * fullSecondEnergy n r) =
            ∑ r ∈ Finset.range k,
              (k.choose r : Real) *
                (fwdDiff (1 : Nat))^[r] (totalSecondEnergy n) 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [ih r (by simpa using hr) ((Finset.mem_range.mp hr).le.trans hk)]
      rw [Finset.sum_range_succ, Finset.sum_range_succ] at heq
      rw [hlower] at heq
      simpa using heq

/-- Explicit alternating form of the same exact weight (Dinur Proposition
20). -/
theorem fullSecondEnergy_eq_alternating_sum {n k : Nat} (hk : k ≤ 2 ^ n) :
    fullSecondEnergy n k =
      ∑ i ∈ Finset.range (k + 1),
        ((-1 : Real) ^ (k - i) * (k.choose i : Real)) *
          ((((2 ^ n : Nat) : Real) ^ i) /
            (((2 ^ n).descFactorial i : Nat) : Real)) := by
  rw [fullSecondEnergy_eq_forwardDiff hk]
  rw [fwdDiff_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i ≤ k := by simpa using hi
  simp only [zero_add, nsmul_one, Nat.cast_id]
  have htotal := totalSecondEnergy_eq (n := n) (k := i) (hik.trans hk)
  simp only [zsmul_eq_mul]
  rw [htotal]
  norm_num

/-! ## Exact positive recurrence for the intrinsic weight -/

/-- The total energy formula, with the ambient cardinality exposed as a
parameter. -/
def samplingEnergy (N k : Nat) : Real :=
  (N : Real) ^ k / (N.descFactorial k : Real)

/-- The elementary one-step equation for sampling without replacement. -/
theorem samplingEnergy_step {N k : Nat} (hk : k < N) :
    (N : Real) *
        (samplingEnergy N (k + 1) - samplingEnergy N k) =
      (k : Real) * samplingEnergy N (k + 1) := by
  have hD : (N.descFactorial k : Real) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hk.le).ne'
  have hNk : ((N - k : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt hk)
  have hcast : ((N - k : Nat) : Real) = (N : Real) - (k : Real) := by
    rw [Nat.cast_sub hk.le]
  have hdiff : (N : Real) - (k : Real) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hk.ne')
  unfold samplingEnergy
  rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
  rw [hcast]
  field_simp [hD, hNk, hdiff]
  ring

/-- Discrete Leibniz rule specialized to the coordinate function.  This is
the cancellation which turns the alternating formula into a positive
three-term recurrence. -/
theorem fwdDiff_iter_succ_coordinate_mul (g : Nat → Real) (m x : Nat) :
    (fwdDiff (1 : Nat))^[m + 1] (fun r => (r : Real) * g r) x =
      (x : Real) * (fwdDiff (1 : Nat))^[m + 1] g x +
        (m + 1 : Nat) * (fwdDiff (1 : Nat))^[m] g (x + 1) := by
  induction m generalizing x with
  | zero =>
      simp [fwdDiff]
      ring
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      change
        (fwdDiff (1 : Nat))^[m + 1] (fun r => (r : Real) * g r) (x + 1) -
            (fwdDiff (1 : Nat))^[m + 1] (fun r => (r : Real) * g r) x = _
      rw [ih (x + 1), ih x]
      simp only [Nat.cast_add, Nat.cast_one]
      have hhigh :
          (fwdDiff (1 : Nat))^[m + 1] g (x + 1) -
              (fwdDiff (1 : Nat))^[m + 1] g x =
            (fwdDiff (1 : Nat))^[m + 2] g x := by
        simp [Function.iterate_succ_apply', fwdDiff, Nat.add_assoc]
      have hlow :
          (fwdDiff (1 : Nat))^[m] g (x + 1 + 1) -
              (fwdDiff (1 : Nat))^[m] g (x + 1) =
            (fwdDiff (1 : Nat))^[m + 1] g (x + 1) := by
        simp [Function.iterate_succ_apply', fwdDiff, Nat.add_assoc]
      rw [← hhigh, ← hlow]
      ring

/-- An iterated difference at zero only reads the first `m+1` values. -/
theorem fwdDiff_iter_apply_zero_congr {f g : Nat → Real} {m : Nat}
    (h : ∀ i, i ≤ m → f i = g i) :
    (fwdDiff (1 : Nat))^[m] f 0 =
      (fwdDiff (1 : Nat))^[m] g 0 := by
  rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := by simpa using hi
  simp only [zero_add, nsmul_one, Nat.cast_id]
  rw [h i him]

/-- Moving an iterated difference two places is the second Newton step. -/
theorem fwdDiff_iter_apply_two (f : Nat → Real) (m : Nat) :
    (fwdDiff (1 : Nat))^[m] f 2 =
      (fwdDiff (1 : Nat))^[m] f 0 +
        2 * (fwdDiff (1 : Nat))^[m + 1] f 0 +
        (fwdDiff (1 : Nat))^[m + 2] f 0 := by
  let g : Nat → Real := (fwdDiff (1 : Nat))^[m] f
  have h := shift_eq_sum_fwdDiff_iter (M := Nat) (G := Real)
    (1 : Nat) g 2 0
  have h' : g 2 = g 0 + 2 * fwdDiff (1 : Nat) g 0 +
      (fwdDiff (1 : Nat))^[2] g 0 := by
    norm_num [Finset.sum_range_succ, nsmul_eq_mul] at h ⊢
    simpa [add_assoc, add_comm, add_left_comm] using h
  dsimp [g] at h'
  simpa [Function.iterate_succ_apply', Nat.add_assoc] using h'

/-- Forward differences commute with a one-step shift. -/
theorem fwdDiff_iter_shift_one (f : Nat → Real) (m x : Nat) :
    (fwdDiff (1 : Nat))^[m] (fun r => f (r + 1)) x =
      (fwdDiff (1 : Nat))^[m] f (x + 1) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change
        (fwdDiff (1 : Nat))^[m] (fun r => f (r + 1)) (x + 1) -
            (fwdDiff (1 : Nat))^[m] (fun r => f (r + 1)) x =
          (fwdDiff (1 : Nat))^[m] f (x + 1 + 1) -
            (fwdDiff (1 : Nat))^[m] f (x + 1)
      rw [ih (x + 1), ih x]

/-- Forward-difference form of the intrinsic weight with the closed total
energy formula substituted on its whole dependency range. -/
theorem fullSecondEnergy_eq_samplingEnergy_fwdDiff {n k : Nat}
    (hk : k ≤ 2 ^ n) :
    fullSecondEnergy n k =
      (fwdDiff (1 : Nat))^[k] (samplingEnergy (2 ^ n)) 0 := by
  rw [fullSecondEnergy_eq_forwardDiff hk]
  apply fwdDiff_iter_apply_zero_congr
  intro i hi
  rw [totalSecondEnergy_eq (hi.trans hk)]
  rfl

/-- Exact normalized Pascal recurrence.  This is slightly sharper and
one-dimensional compared with the auxiliary two-parameter recurrence used in
the paper. -/
theorem fullSecondEnergy_recurrence {n k : Nat}
    (hkpos : 1 ≤ k) (hkN : k < 2 ^ n) :
    (((2 ^ n : Nat) : Real) - (k : Real)) *
        fullSecondEnergy n (k + 1) =
      (k : Real) *
        (2 * fullSecondEnergy n k + fullSecondEnergy n (k - 1)) := by
  let N : Nat := 2 ^ n
  let f : Nat → Real := samplingEnergy N
  have hpoint (i : Nat) (hi : i ≤ k) :
      (N : Real) * fwdDiff (1 : Nat) f i =
        (i : Real) * f (i + 1) := by
    have hiN : i < N := hi.trans_lt (by simpa [N] using hkN)
    simpa [fwdDiff, f, Nat.add_comm] using
      (samplingEnergy_step (N := N) (k := i) hiN)
  have hdiff :
      (fwdDiff (1 : Nat))^[k]
          (fun i => (N : Real) * fwdDiff (1 : Nat) f i) 0 =
        (fwdDiff (1 : Nat))^[k]
          (fun i => (i : Real) * f (i + 1)) 0 := by
    apply fwdDiff_iter_apply_zero_congr
    intro i hi
    exact hpoint i hi
  have hleft :
      (fwdDiff (1 : Nat))^[k]
          (fun i => (N : Real) * fwdDiff (1 : Nat) f i) 0 =
        (N : Real) * (fwdDiff (1 : Nat))^[k + 1] f 0 := by
    change
      (fwdDiff (1 : Nat))^[k]
          ((N : Real) • fwdDiff (1 : Nat) f) 0 = _
    rw [fwdDiff_iter_const_smul]
    change (N : Real) *
      ((fwdDiff (1 : Nat))^[k] (fwdDiff (1 : Nat) f)) 0 = _
    rw [← Function.iterate_succ_apply]
  have hkdecomp : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
  have hright :
      (fwdDiff (1 : Nat))^[k]
          (fun i => (i : Real) * f (i + 1)) 0 =
        (k : Real) * (fwdDiff (1 : Nat))^[k - 1] f 2 := by
    have hcoord :=
      fwdDiff_iter_succ_coordinate_mul (fun r => f (r + 1)) (k - 1) 0
    rw [hkdecomp] at hcoord
    simp only [Nat.cast_zero, zero_mul, zero_add] at hcoord
    rw [hcoord, fwdDiff_iter_shift_one]
  have htwo := fwdDiff_iter_apply_two f (k - 1)
  rw [hkdecomp, show k - 1 + 2 = k + 1 by omega] at htwo
  have hraw :
      (N : Real) * (fwdDiff (1 : Nat))^[k + 1] f 0 =
        (k : Real) *
          ((fwdDiff (1 : Nat))^[k - 1] f 0 +
            2 * (fwdDiff (1 : Nat))^[k] f 0 +
            (fwdDiff (1 : Nat))^[k + 1] f 0) := by
    rw [← hleft, hdiff, hright, htwo]
  have hprev : k - 1 ≤ N := by omega
  have hcur : k ≤ N := by omega
  have hnext : k + 1 ≤ N := by omega
  have hWprev := fullSecondEnergy_eq_samplingEnergy_fwdDiff
    (n := n) (k := k - 1) (by simpa [N] using hprev)
  have hWcur := fullSecondEnergy_eq_samplingEnergy_fwdDiff
    (n := n) (k := k) (by simpa [N] using hcur)
  have hWnext := fullSecondEnergy_eq_samplingEnergy_fwdDiff
    (n := n) (k := k + 1) (by simpa [N] using hnext)
  rw [Function.iterate_succ_apply] at hWnext
  dsimp [f] at hraw
  dsimp [N] at hraw
  rw [← hWprev, ← hWcur, ← hWnext] at hraw
  linarith

/-- Division form of the same exact recurrence. -/
theorem fullSecondEnergy_succ_eq {n k : Nat}
    (hkpos : 1 ≤ k) (hkN : k < 2 ^ n) :
    fullSecondEnergy n (k + 1) =
      (k : Real) /
          (((2 ^ n : Nat) : Real) - (k : Real)) *
        (2 * fullSecondEnergy n k + fullSecondEnergy n (k - 1)) := by
  have hden : (((2 ^ n : Nat) : Real) - (k : Real)) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hkN.ne')
  calc
    fullSecondEnergy n (k + 1) =
        ((k : Real) *
          (2 * fullSecondEnergy n k + fullSecondEnergy n (k - 1))) /
            (((2 ^ n : Nat) : Real) - (k : Real)) := by
      apply (eq_div_iff hden).mpr
      rw [mul_comm]
      exact fullSecondEnergy_recurrence (n := n) hkpos hkN
    _ = (k : Real) /
          (((2 ^ n : Nat) : Real) - (k : Real)) *
        (2 * fullSecondEnergy n k + fullSecondEnergy n (k - 1)) := by
      ring

theorem fullSecondEnergy_nonneg (n k : Nat) :
    0 ≤ fullSecondEnergy n k := by
  unfold fullSecondEnergy
  positivity

@[simp]
theorem fullSecondEnergy_zero (n : Nat) :
    fullSecondEnergy n 0 = 1 := by
  rw [fullSecondEnergy_eq_alternating_sum (n := n) (k := 0) (Nat.zero_le _)]
  norm_num [Finset.sum_range_succ, Nat.descFactorial_zero]

@[simp]
theorem fullSecondEnergy_one (n : Nat) :
    fullSecondEnergy n 1 = 0 := by
  have hN : 1 ≤ 2 ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
  rw [fullSecondEnergy_eq_alternating_sum (n := n) (k := 1) hN]
  norm_num [Finset.sum_range_succ, Nat.descFactorial_succ,
    Nat.descFactorial_zero]

/-- Exact level-two intrinsic energy. -/
theorem fullSecondEnergy_two {n : Nat} (hN : 2 ≤ 2 ^ n) :
    fullSecondEnergy n 2 =
      1 / (((2 ^ n - 1 : Nat) : Real)) := by
  have hrec := fullSecondEnergy_succ_eq (n := n) (k := 1)
    (by omega) (by omega)
  norm_num at hrec
  simpa [one_div] using hrec

end RandomSystems.SoP.XORTail
