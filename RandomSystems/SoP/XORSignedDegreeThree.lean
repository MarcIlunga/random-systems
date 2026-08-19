/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORSignedTruncation

/-!
# Exact signed degree-three truncation for XOR SoP

The degree-two collision proxy loses cancellation when its absolute value is
taken before the next Fourier layer is added.  This module retains levels two
and three together.  A closed three-row checkerboard has only three visible
values:

```text
all distinct:       2
exactly one repeat: -(N-2)
all equal:          (N-1)(N-2).
```

In the sparse sign range, the combined level-two-plus-three density is
negative exactly on collision-free tapes and nonnegative everywhere else.
Its half-L1 norm is therefore elementary: collision-free probability times
the magnitude of its collision-free value.  The resulting main term is

```text
(N)_q / N^q *
  (choose(q,2)/(N-1)^2
    - 8*choose(q,3)/((N-1)^2*(N-2)^2)).
```

The operational theorem adds only the already-formalized signed tail from
row level four onward.  No mirror theory or conditioning argument is used.
-/

noncomputable section
open scoped BigOperators

namespace RandomSystems.SoP.XORSignedDegreeThree

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.XORTail
open RandomSystems.SoP.XORBounds
open RandomSystems.SoP.XORSignedTruncation
open RandomSystems.SoP.CollisionProxy
open RandomSystems.Applications.SoP

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def nonzeroWords (n : Nat) : Finset (XorSpace n) :=
  (Finset.univ : Finset (XorSpace n)).erase 0

def closedThreeMaskSum {n : Nat} (u v w : XorSpace n) : Real :=
  ∑ a ∈ nonzeroWords n, ∑ b ∈ (nonzeroWords n).erase a,
    vectorWalsh a u * vectorWalsh b v * vectorWalsh (a + b) w

theorem sum_nonzero_words_vector_walsh {n : Nat} (x : XorSpace n) :
    (∑ a ∈ nonzeroWords n, vectorWalsh a x) =
      if x = 0 then ((2 ^ n - 1 : Nat) : Real) else -1 := by
  have hset : nonzeroWords n =
      (Finset.univ : Finset (XorSpace n)).filter (fun a => a ≠ 0) := by
    ext a
    simp [nonzeroWords]
  rw [hset]
  exact sum_nonzero_vectorWalsh x

theorem closed_three_mask_sum_rewrite {n : Nat} (u v w : XorSpace n) :
    closedThreeMaskSum u v w =
      (∑ a ∈ nonzeroWords n, vectorWalsh a (u + w)) *
          (∑ b ∈ nonzeroWords n, vectorWalsh b (v + w)) -
        ∑ a ∈ nonzeroWords n, vectorWalsh a (u + v) := by
  unfold closedThreeMaskSum
  rw [Finset.sum_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hinner :
      (∑ b ∈ (nonzeroWords n).erase a,
          vectorWalsh a u * vectorWalsh b v * vectorWalsh (a + b) w) =
        vectorWalsh a (u + w) *
          ((∑ b ∈ nonzeroWords n, vectorWalsh b (v + w)) -
            vectorWalsh a (v + w)) := by
    have ha' : a ∈ nonzeroWords n := ha
    have herase := Finset.sum_erase_add
      (s := nonzeroWords n) (f := fun b => vectorWalsh b (v + w)) ha'
    calc
      (∑ b ∈ (nonzeroWords n).erase a,
          vectorWalsh a u * vectorWalsh b v * vectorWalsh (a + b) w) =
        ∑ b ∈ (nonzeroWords n).erase a,
          vectorWalsh a (u + w) * vectorWalsh b (v + w) := by
            apply Finset.sum_congr rfl
            intro b _hb
            rw [vectorWalsh_add_left, vectorWalsh_add_right,
              vectorWalsh_add_right]
            ring
      _ = vectorWalsh a (u + w) *
          ∑ b ∈ (nonzeroWords n).erase a, vectorWalsh b (v + w) := by
            rw [Finset.mul_sum]
      _ = vectorWalsh a (u + w) *
          ((∑ b ∈ nonzeroWords n, vectorWalsh b (v + w)) -
            vectorWalsh a (v + w)) := by
            congr 1
            linarith
  rw [hinner]
  rw [mul_sub]
  congr 1
  rw [← vectorWalsh_add_right]
  have hxor : (u + w) + (v + w) = u + v := by
    calc
      (u + w) + (v + w) = (u + v) + (w + w) := by abel
      _ = u + v := by rw [xorSpace_add_self_eq_zero]; simp
  rw [hxor]

theorem closed_three_mask_sum_eq_pattern {n : Nat} (hN : 2 ≤ 2 ^ n)
    (u v w : XorSpace n) :
    closedThreeMaskSum u v w =
      if u = v ∧ u = w then
        ((2 ^ n - 1 : Nat) : Real) * ((2 ^ n - 2 : Nat) : Real)
      else if u = v ∨ u = w ∨ v = w then
        -((2 ^ n - 2 : Nat) : Real)
      else 2 := by
  rw [closed_three_mask_sum_rewrite,
    sum_nonzero_words_vector_walsh, sum_nonzero_words_vector_walsh,
    sum_nonzero_words_vector_walsh]
  rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ n), Nat.cast_sub hN]
  norm_num
  simp only [xorSpace_add_eq_zero_iff_eq]
  by_cases huv : u = v <;> by_cases huw : u = w <;>
    by_cases hvw : v = w <;> simp_all <;> ring

def levelThreeDensity (n q : Nat) : BitMatrix q n → Real :=
  spectralPart (fun a : BitMatrix q n => level a = 3)
    (convolution (injectionDensity n q) (injectionDensity n q))

theorem level_three_density_eq_closed_mask_sum
    {n q : Nat} (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    levelThreeDensity n q y =
      (2 / (((2 ^ n - 1 : Nat) : Real) *
        ((2 ^ n - 2 : Nat) : Real))) ^ 2 *
        ∑ a : LevelThreeZeroMask n q, walsh a.1 y := by
  let c : Real :=
    2 / (((2 ^ n - 1 : Nat) : Real) *
      ((2 ^ n - 2 : Nat) : Real))
  change spectralPart (fun a : BitMatrix q n => level a = 3)
      (convolution (injectionDensity n q) (injectionDensity n q)) y =
    c ^ 2 * ∑ a : LevelThreeZeroMask n q, walsh a.1 y
  rw [spectralPart_apply]
  calc
    _ =
      ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
        (fun a => level a = 3),
        if maskRowSum a = 0 then c ^ 2 * walsh a y else 0 := by
          apply Finset.sum_congr (by ext a; simp)
          intro a ha
          have haLevel : level a = 3 := by simpa using ha
          rw [fourier_convolution,
            fourier_injectionDensity_of_level_eq_three hq a haLevel]
          by_cases hsum : maskRowSum a = 0 <;> simp [hsum, c, pow_two]
    _ = ∑ a ∈ (Finset.univ : Finset (BitMatrix q n)).filter
          (fun a => level a = 3 ∧ maskRowSum a = 0),
        c ^ 2 * walsh a y := by
          rw [show
            (Finset.univ : Finset (BitMatrix q n)).filter
                (fun a => level a = 3 ∧ maskRowSum a = 0) =
              ((Finset.univ : Finset (BitMatrix q n)).filter
                (fun a => level a = 3)).filter (fun a => maskRowSum a = 0) by
            ext a
            simp]
          exact (Finset.sum_filter (fun a : BitMatrix q n => maskRowSum a = 0)
            (fun a => c ^ 2 * walsh a y)).symm
    _ = ∑ a : LevelThreeZeroMask n q, c ^ 2 * walsh a.1 y := by
          rw [sum_filter_eq_sum_subtype]
    _ = c ^ 2 * ∑ a : LevelThreeZeroMask n q, walsh a.1 y := by
          rw [Finset.mul_sum]
    _ = _ := by rfl

theorem walsh_eq_walsh_restrict_mask_fun {n q k : Nat}
    (r : Fin k ↪ Fin q) (a : BitMatrix q n)
    (hout : ∀ i, i ∉ Set.range r -> a i = 0)
    (x : BitMatrix q n) :
    walsh a x = walsh (restrictMask r a) (fun i => x (r i)) := by
  unfold walsh dot restrictMask
  congr 1
  symm
  apply Fintype.sum_of_injective r r.injective
    (fun i : Fin k => ∑ j : Fin n, a (r i) j * x (r i) j)
    (fun i : Fin q => ∑ j : Fin n, a i j * x i j)
  · intro i hi
    rw [hout i hi]
    simp
  · intro i
    rfl

def levelThreeFiberPairEquiv {n q : Nat} (S : ThreeSupport q) :
    {a : LevelThreeZeroMask n q // levelThreeSupportOf a = S} ≃
      DistinctNonzeroPair n :=
  (levelThreeZeroFiberEquiv S).trans
    ((fullZeroSumAssignmentCongr (supportEquivFin S).symm).trans
      (fullZeroSumThreeEquivPair n))

def supportTapeThree {n q : Nat} (S : ThreeSupport q)
    (y : BitMatrix q n) : BitMatrix 3 n :=
  fun i => y ((supportEquivFin S i).1)

theorem walsh_level_three_fiber_pair_equiv {n q : Nat}
    (S : ThreeSupport q)
    (a : {a : LevelThreeZeroMask n q // levelThreeSupportOf a = S})
    (y : BitMatrix q n) :
    walsh a.1.1 y =
      vectorWalsh (levelThreeFiberPairEquiv S a).1.1 (supportTapeThree S y 0) *
        vectorWalsh (levelThreeFiberPairEquiv S a).1.2 (supportTapeThree S y 1) *
        vectorWalsh ((levelThreeFiberPairEquiv S a).1.1 +
          (levelThreeFiberPairEquiv S a).1.2) (supportTapeThree S y 2) := by
  let r : Fin 3 ↪ Fin q :=
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
  rw [walsh_eq_walsh_restrict_mask_fun r a.1.1 hout y]
  have hmask : restrictMask r a.1.1 =
      threeMask ((levelThreeFiberPairEquiv S a).1.1)
        ((levelThreeFiberPairEquiv S a).1.2)
        ((levelThreeFiberPairEquiv S a).1.1 +
          (levelThreeFiberPairEquiv S a).1.2) := by
    have hsum : a.1.1 (r 0) + a.1.1 (r 1) + a.1.1 (r 2) = 0 := by
      have h := a.1.2.2
      rw [maskRowSum_eq_sum_restrictMask r a.1.1 hout] at h
      rw [Fin.sum_univ_three] at h
      exact h
    have hthird : a.1.1 (r 2) = a.1.1 (r 0) + a.1.1 (r 1) := by
      have h := congrArg (fun z => z + a.1.1 (r 2)) hsum
      symm
      simpa [add_assoc] using h
    funext i j
    fin_cases i
    · rfl
    · rfl
    · exact congrFun hthird j
  rw [hmask, walsh_threeMask]
  rfl

theorem sum_distinct_nonzero_pair_eq_closed_three_mask_sum {n : Nat}
    (u v w : XorSpace n) :
    (∑ p : DistinctNonzeroPair n,
      vectorWalsh p.1.1 u * vectorWalsh p.1.2 v *
        vectorWalsh (p.1.1 + p.1.2) w) =
      closedThreeMaskSum u v w := by
  unfold closedThreeMaskSum
  calc
    (∑ p : DistinctNonzeroPair n,
      vectorWalsh p.1.1 u * vectorWalsh p.1.2 v *
        vectorWalsh (p.1.1 + p.1.2) w) =
      ∑ z : Σ a : {a : XorSpace n // a ≠ 0},
          {b : XorSpace n // b ≠ 0 ∧ b ≠ a.1},
        vectorWalsh z.1.1 u * vectorWalsh z.2.1 v *
          vectorWalsh (z.1.1 + z.2.1) w := by
            exact Fintype.sum_equiv (distinctNonzeroPairSigmaEquiv n)
              _ _ (fun _ => rfl)
    _ = ∑ a : {a : XorSpace n // a ≠ 0},
        ∑ b : {b : XorSpace n // b ≠ 0 ∧ b ≠ a.1},
          vectorWalsh a.1 u * vectorWalsh b.1 v *
            vectorWalsh (a.1 + b.1) w := by
              rw [Fintype.sum_sigma]
    _ = ∑ a ∈ nonzeroWords n,
        ∑ b ∈ (nonzeroWords n).erase a,
          vectorWalsh a u * vectorWalsh b v * vectorWalsh (a + b) w := by
      have hnonzero : nonzeroWords n =
          (Finset.univ : Finset (XorSpace n)).filter (fun a => a ≠ 0) := by
        ext a
        simp [nonzeroWords]
      rw [hnonzero, sum_filter_eq_sum_subtype]
      apply Finset.sum_congr rfl
      intro a _ha
      have herase :
          ((Finset.univ : Finset (XorSpace n)).filter
            (fun b => b ≠ 0)).erase a.1 =
          (Finset.univ : Finset (XorSpace n)).filter
            (fun b => b ≠ 0 ∧ b ≠ a.1) := by
        ext b
        simp [and_comm]
      rw [herase, sum_filter_eq_sum_subtype]

theorem sum_level_three_fiber_eq_closed_three_mask_sum {n q : Nat}
    (S : ThreeSupport q) (y : BitMatrix q n) :
    (∑ a : {a : LevelThreeZeroMask n q // levelThreeSupportOf a = S},
      walsh a.1.1 y) =
      closedThreeMaskSum (supportTapeThree S y 0)
        (supportTapeThree S y 1) (supportTapeThree S y 2) := by
  calc
    (∑ a : {a : LevelThreeZeroMask n q // levelThreeSupportOf a = S},
      walsh a.1.1 y) =
      ∑ p : DistinctNonzeroPair n,
        vectorWalsh p.1.1 (supportTapeThree S y 0) *
          vectorWalsh p.1.2 (supportTapeThree S y 1) *
          vectorWalsh (p.1.1 + p.1.2) (supportTapeThree S y 2) := by
            exact Fintype.sum_equiv (levelThreeFiberPairEquiv S)
              _ _ (fun a => walsh_level_three_fiber_pair_equiv S a y)
    _ = _ := sum_distinct_nonzero_pair_eq_closed_three_mask_sum _ _ _

theorem sum_level_three_zero_mask_eq_sum_support {n q : Nat}
    (y : BitMatrix q n) :
    (∑ a : LevelThreeZeroMask n q, walsh a.1 y) =
      ∑ S : ThreeSupport q,
        closedThreeMaskSum (supportTapeThree S y 0)
          (supportTapeThree S y 1) (supportTapeThree S y 2) := by
  let E := Equiv.sigmaFiberEquiv
    (levelThreeSupportOf (n := n) (q := q))
  calc
    (∑ a : LevelThreeZeroMask n q, walsh a.1 y) =
      ∑ z : Σ S : ThreeSupport q,
          {a : LevelThreeZeroMask n q // levelThreeSupportOf a = S},
        walsh z.2.1.1 y := by
          symm
          exact Fintype.sum_equiv E _ _ (fun _z => rfl)
    _ = ∑ S : ThreeSupport q,
        ∑ a : {a : LevelThreeZeroMask n q // levelThreeSupportOf a = S},
          walsh a.1.1 y := by
            rw [Fintype.sum_sigma]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _hS
      exact sum_level_three_fiber_eq_closed_three_mask_sum S y

theorem level_three_density_eq_sum_support
    {n q : Nat} (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    levelThreeDensity n q y =
      (2 / (((2 ^ n - 1 : Nat) : Real) *
        ((2 ^ n - 2 : Nat) : Real))) ^ 2 *
      ∑ S : ThreeSupport q,
        closedThreeMaskSum (supportTapeThree S y 0)
          (supportTapeThree S y 1) (supportTapeThree S y 2) := by
  rw [level_three_density_eq_closed_mask_sum hq,
    sum_level_three_zero_mask_eq_sum_support]

theorem closed_three_mask_sum_lower_bound {n : Nat} (hN : 2 ≤ 2 ^ n)
    (u v w : XorSpace n) :
    -((2 ^ n - 2 : Nat) : Real) ≤ closedThreeMaskSum u v w := by
  rw [closed_three_mask_sum_eq_pattern hN]
  by_cases hall : u = v ∧ u = w
  · rw [if_pos hall]
    have hcast : 0 ≤ ((2 ^ n - 2 : Nat) : Real) := by positivity
    have hprod : 0 ≤
        ((2 ^ n - 1 : Nat) : Real) * ((2 ^ n - 2 : Nat) : Real) := by
      positivity
    linarith
  · rw [if_neg hall]
    by_cases hpair : u = v ∨ u = w ∨ v = w
    · rw [if_pos hpair]
    · rw [if_neg hpair]
      have hcast : 0 ≤ ((2 ^ n - 2 : Nat) : Real) := by positivity
      linarith

theorem closed_three_mask_sum_eq_two_of_injective {n q : Nat}
    (hN : 2 ≤ 2 ^ n) (S : ThreeSupport q) (y : BitMatrix q n)
    (hy : Function.Injective y) :
    closedThreeMaskSum (supportTapeThree S y 0)
      (supportTapeThree S y 1) (supportTapeThree S y 2) = 2 := by
  have hidx (i j : Fin 3) (hij : i ≠ j) :
      (supportEquivFin S i).1 ≠ (supportEquivFin S j).1 := by
    intro h
    apply hij
    apply (supportEquivFin S).injective
    exact Subtype.ext h
  have h01 : supportTapeThree S y 0 ≠ supportTapeThree S y 1 := by
    intro h
    exact hidx 0 1 (by decide) (hy h)
  have h02 : supportTapeThree S y 0 ≠ supportTapeThree S y 2 := by
    intro h
    exact hidx 0 2 (by decide) (hy h)
  have h12 : supportTapeThree S y 1 ≠ supportTapeThree S y 2 := by
    intro h
    exact hidx 1 2 (by decide) (hy h)
  rw [closed_three_mask_sum_eq_pattern hN]
  simp [h01, h02, h12]

theorem level_three_density_eq_of_injective
    {n q : Nat} (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (y : BitMatrix q n) (hy : Function.Injective y) :
    levelThreeDensity n q y =
      8 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
          (((2 ^ n - 2 : Nat) : Real) ^ 2)) := by
  rw [level_three_density_eq_sum_support hq]
  simp_rw [closed_three_mask_sum_eq_two_of_injective hN _ y hy]
  rw [Finset.sum_const, Finset.card_univ, card_threeSupport]
  ring

theorem level_three_density_lower_bound
    {n q : Nat} (hN : 3 ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (y : BitMatrix q n) :
    -(4 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
          ((2 ^ n - 2 : Nat) : Real))) ≤
      levelThreeDensity n q y := by
  rw [level_three_density_eq_sum_support hq]
  let c : Real :=
    2 / (((2 ^ n - 1 : Nat) : Real) *
      ((2 ^ n - 2 : Nat) : Real))
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  have hsum :
      -((q.choose 3 : Real) * ((2 ^ n - 2 : Nat) : Real)) ≤
        ∑ S : ThreeSupport q,
          closedThreeMaskSum (supportTapeThree S y 0)
            (supportTapeThree S y 1) (supportTapeThree S y 2) := by
    calc
      -((q.choose 3 : Real) * ((2 ^ n - 2 : Nat) : Real)) =
          ∑ _S : ThreeSupport q,
            -((2 ^ n - 2 : Nat) : Real) := by
              rw [Finset.sum_const, Finset.card_univ, card_threeSupport]
              simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro S _hS
        exact closed_three_mask_sum_lower_bound (by omega) _ _ _
  change -(4 * (q.choose 3 : Real) /
      ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
        ((2 ^ n - 2 : Nat) : Real))) ≤ c ^ 2 * _
  calc
    -(4 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
          ((2 ^ n - 2 : Nat) : Real))) =
        c ^ 2 *
          -((q.choose 3 : Real) * ((2 ^ n - 2 : Nat) : Real)) := by
            dsimp [c]
            have hN2 : ((2 ^ n - 2 : Nat) : Real) ≠ 0 := by
              exact_mod_cast (by omega : 2 ^ n - 2 ≠ 0)
            field_simp [hN2]
            ring
    _ ≤ c ^ 2 * _ := mul_le_mul_of_nonneg_left hsum hc

theorem signed_truncation_density_four_eq_collision_add_three
    {n q : Nat} (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (y : BitMatrix q n) :
    signedTruncationDensity n q 4 y =
      collisionKernel (XorSpace n) q y + levelThreeDensity n q y := by
  have hsplit : signedTruncationDensity n q 4 y =
      spectralPart (fun a : BitMatrix q n => level a = 2)
          (convolution (injectionDensity n q) (injectionDensity n q)) y +
        spectralPart (fun a : BitMatrix q n => level a = 3)
          (convolution (injectionDensity n q) (injectionDensity n q)) y := by
    unfold signedTruncationDensity spectralPart
    simp_rw [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases h2 : level a = 2
    · simp [h2]
    · by_cases h3 : level a = 3
      · simp [h3]
      · have hrange : ¬(2 ≤ level a ∧ level a < 4) := by omega
        simp [h2, h3, hrange]
  rw [hsplit, levelTwoSpectrum_eq_collisionKernel hN hq]
  rfl

theorem one_le_pair_collision_count_nat_of_not_injective
    {G : Type*} [DecidableEq G] {q : Nat} (y : Fin q → G)
    (hy : ¬Function.Injective y) :
    1 ≤ pairCollisionCountNat G q y := by
  obtain ⟨i, j, hijValue, hij⟩ := Function.not_injective_iff.mp hy
  unfold pairCollisionCountNat
  rcases lt_or_gt_of_ne hij with hijOrder | hjiOrder
  · let p : PairIndex q := ⟨(i, j), hijOrder⟩
    have hterm :
        (if y p.1.2 = y p.1.1 then 1 else 0 : Nat) = 1 := by
      simp [p, hijValue.symm]
    have hle := Finset.single_le_sum
      (s := (Finset.univ : Finset (PairIndex q)))
      (f := fun p : PairIndex q =>
        (if y p.1.2 = y p.1.1 then 1 else 0 : Nat))
      (fun _p _hp => Nat.zero_le _) (Finset.mem_univ p)
    simpa [hterm] using hle
  · let p : PairIndex q := ⟨(j, i), hjiOrder⟩
    have hterm :
        (if y p.1.2 = y p.1.1 then 1 else 0 : Nat) = 1 := by
      simp [p, hijValue]
    have hle := Finset.single_le_sum
      (s := (Finset.univ : Finset (PairIndex q)))
      (f := fun p : PairIndex q =>
        (if y p.1.2 = y p.1.1 then 1 else 0 : Nat))
      (fun _p _hp => Nat.zero_le _) (Finset.mem_univ p)
    simpa [hterm] using hle

theorem collision_kernel_eq_nat_numerator
    {n q : Nat} (y : BitMatrix q n) :
    collisionKernel (XorSpace n) q y =
      (((2 ^ n : Nat) : Real) *
          (pairCollisionCountNat (XorSpace n) q y : Real) -
        (q.choose 2 : Real)) /
        (((2 ^ n - 1 : Nat) : Real) ^ 2) := by
  unfold collisionKernel centeredCollisionCount collisionMean collisionCount
  rw [pairCollisionCountReal_eq_pairCollisionCountNat, pairCount_eq]
  simp only [card_xorSpace]
  have hNR : ((2 ^ n : Nat) : Real) ≠ 0 := by positivity
  field_simp [hNR]

theorem collision_kernel_lower_bound_of_not_injective
    {n q : Nat} (y : BitMatrix q n)
    (hy : ¬Function.Injective y) :
    (((2 ^ n : Nat) : Real) - (q.choose 2 : Real)) /
        (((2 ^ n - 1 : Nat) : Real) ^ 2) ≤
      collisionKernel (XorSpace n) q y := by
  rw [collision_kernel_eq_nat_numerator y]
  have hK := one_le_pair_collision_count_nat_of_not_injective y hy
  have hKreal : (1 : Real) ≤
      (pairCollisionCountNat (XorSpace n) q y : Real) := by
    exact_mod_cast hK
  have hden : 0 ≤ ((2 ^ n - 1 : Nat) : Real) ^ 2 := sq_nonneg _
  apply div_le_div_of_nonneg_right _ hden
  have hNreal : (0 : Real) ≤ ((2 ^ n : Nat) : Real) := by positivity
  nlinarith

theorem pair_collision_count_nat_eq_zero_of_injective
    {G : Type*} [DecidableEq G] {q : Nat} (y : Fin q → G)
    (hy : Function.Injective y) :
    pairCollisionCountNat G q y = 0 := by
  unfold pairCollisionCountNat
  apply Finset.sum_eq_zero
  intro p _hp
  have hne : y p.1.2 ≠ y p.1.1 := by
    intro h
    exact (ne_of_gt p.2) (hy h)
  simp [hne]

theorem signed_truncation_density_four_eq_of_injective
    {n q : Nat} (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (y : BitMatrix q n) (hy : Function.Injective y) :
    signedTruncationDensity n q 4 y =
      -(q.choose 2 : Real) /
          (((2 ^ n - 1 : Nat) : Real) ^ 2) +
        8 * (q.choose 3 : Real) /
          ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
            (((2 ^ n - 2 : Nat) : Real) ^ 2)) := by
  rw [signed_truncation_density_four_eq_collision_add_three hN hq,
    collision_kernel_eq_nat_numerator y,
    pair_collision_count_nat_eq_zero_of_injective y hy,
    level_three_density_eq_of_injective hN hq y hy]
  ring

theorem signed_truncation_density_four_nonpos_of_injective
    {n q : Nat} (hN : 3 ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hneg : 8 * (q.choose 3 : Real) ≤
      (q.choose 2 : Real) * ((2 ^ n - 2 : Nat) : Real) ^ 2)
    (y : BitMatrix q n) (hy : Function.Injective y) :
    signedTruncationDensity n q 4 y ≤ 0 := by
  rw [signed_truncation_density_four_eq_of_injective (by omega) hq y hy]
  have hN1pos : 0 < ((2 ^ n - 1 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < 2 ^ n - 1)
  have hN2pos : 0 < ((2 ^ n - 2 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < 2 ^ n - 2)
  have hD1 : 0 < ((2 ^ n - 1 : Nat) : Real) ^ 2 := by
    positivity
  have hD2 : 0 < ((2 ^ n - 2 : Nat) : Real) ^ 2 := by
    positivity
  have hrearrange :
      -(q.choose 2 : Real) /
          (((2 ^ n - 1 : Nat) : Real) ^ 2) +
        8 * (q.choose 3 : Real) /
          ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
            (((2 ^ n - 2 : Nat) : Real) ^ 2)) =
      (8 * (q.choose 3 : Real) -
          (q.choose 2 : Real) * ((2 ^ n - 2 : Nat) : Real) ^ 2) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
          (((2 ^ n - 2 : Nat) : Real) ^ 2)) := by
    field_simp [hN1pos.ne', hN2pos.ne']; ring
  rw [hrearrange]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hneg)
    (mul_nonneg hD1.le hD2.le)

theorem signed_truncation_density_four_nonneg_of_not_injective
    {n q : Nat} (hN : 3 ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpos : 4 * (q.choose 3 : Real) ≤
      (((2 ^ n : Nat) : Real) - (q.choose 2 : Real)) *
        ((2 ^ n - 2 : Nat) : Real))
    (y : BitMatrix q n) (hy : ¬Function.Injective y) :
    0 ≤ signedTruncationDensity n q 4 y := by
  rw [signed_truncation_density_four_eq_collision_add_three (by omega) hq]
  have hcollision := collision_kernel_lower_bound_of_not_injective
    y hy
  have hthree := level_three_density_lower_bound hN hq y
  have hN1pos : 0 < ((2 ^ n - 1 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < 2 ^ n - 1)
  have hD1 : 0 < ((2 ^ n - 1 : Nat) : Real) ^ 2 := by positivity
  have hD2 : 0 < ((2 ^ n - 2 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < 2 ^ n - 2)
  have hbase : 0 ≤
      (((2 ^ n : Nat) : Real) - (q.choose 2 : Real)) /
          (((2 ^ n - 1 : Nat) : Real) ^ 2) -
        4 * (q.choose 3 : Real) /
          ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
            ((2 ^ n - 2 : Nat) : Real)) := by
    have hrearrange :
        (((2 ^ n : Nat) : Real) - (q.choose 2 : Real)) /
            (((2 ^ n - 1 : Nat) : Real) ^ 2) -
          4 * (q.choose 3 : Real) /
            ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
              ((2 ^ n - 2 : Nat) : Real)) =
        ((((2 ^ n : Nat) : Real) - (q.choose 2 : Real)) *
            ((2 ^ n - 2 : Nat) : Real) -
          4 * (q.choose 3 : Real)) /
          ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
            ((2 ^ n - 2 : Nat) : Real)) := by
      field_simp [hN1pos.ne', hD2.ne']
    rw [hrearrange]
    exact div_nonneg (sub_nonneg.mpr hpos) (mul_nonneg hD1.le hD2.le)
  linarith

theorem average_signed_truncation_density_eq_zero
    (n q r : Nat) :
    average (BitMatrix q n) (signedTruncationDensity n q r) = 0 := by
  unfold signedTruncationDensity spectralPart
  rw [average_finset_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have haRange : 2 ≤ level a ∧ level a < r := by simpa using ha
  have haNe : a ≠ 0 := by
    intro haz
    subst a
    simp at haRange
  rw [average_const_mul, average_walsh]
  simp [haNe]

theorem half_average_abs_eq_neg_average_on
    {A : Type*} [Fintype A] [Nonempty A]
    (p : A → Prop) [DecidablePred p] (f : A → Real)
    (hmean : average A f = 0)
    (hnonpos : ∀ x, p x → f x ≤ 0)
    (hnonneg : ∀ x, ¬p x → 0 ≤ f x) :
    (1 / 2 : Real) * average A (fun x => |f x|) =
      -average A (fun x => if p x then f x else 0) := by
  have hpoint : (fun x : A => |f x|) =
      (fun x => f x - 2 * (if p x then f x else 0)) := by
    funext x
    by_cases hx : p x
    · rw [if_pos hx, abs_of_nonpos (hnonpos x hx)]
      ring
    · rw [if_neg hx, abs_of_nonneg (hnonneg x hx)]
      ring
  rw [hpoint]
  have havgSub (g h : A → Real) :
      average A (fun x => g x - h x) = average A g - average A h := by
    unfold average
    rw [Finset.sum_sub_distrib, sub_div]
  rw [havgSub, average_const_mul, hmean]
  ring

theorem average_if_injective_const (n q : Nat) (c : Real) :
    average (BitMatrix q n)
        (fun y => if Function.Injective y then c else 0) =
      ((((2 ^ n).descFactorial q : Nat) : Real) /
          (((2 ^ n : Nat) : Real) ^ q)) * c := by
  let N : Nat := 2 ^ n
  have hcardInjective :
      ((Finset.univ : Finset (BitMatrix q n)).filter
        (fun y => Function.Injective y)).card = N.descFactorial q := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr
      (Equiv.subtypeInjectiveEquivEmbedding (Fin q) (XorSpace n))]
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    simp [N]
  have hcardTape : Fintype.card (BitMatrix q n) = N ^ q := by
    simp [BitMatrix, N]
  unfold average
  rw [show
      (∑ y : BitMatrix q n, if Function.Injective y then c else 0) =
        (((Finset.univ : Finset (BitMatrix q n)).filter
          (fun y => Function.Injective y)).card : Real) * c by
      rw [← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]]
  rw [hcardInjective, hcardTape]
  dsimp [N]
  norm_num [Nat.cast_pow]
  ring

/-- Closed signed degree-three main term: the collision-free probability
times the degree-two charge after the exact triangle correction. -/
def signedDegreeThreeMain (n q : Nat) : Real :=
  ((((2 ^ n).descFactorial q : Nat) : Real) /
      (((2 ^ n : Nat) : Real) ^ q)) *
    ((q.choose 2 : Real) /
        (((2 ^ n - 1 : Nat) : Real) ^ 2) -
      8 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
          (((2 ^ n - 2 : Nat) : Real) ^ 2)))

/-- Closed level-four-and-higher error paired with
`signedDegreeThreeMain`. -/
def signedDegreeThreeError (n q : Nat) : Real :=
  (1 / 2 : Real) * Real.sqrt
    ((1152 / 7 : Real) * (q : Real) ^ 4 /
        (((2 ^ n : Nat) : Real) ^ 6) +
      8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8))

@[simp]
theorem signed_tail_error_bound_four_eq_signed_degree_three_error (n q : Nat) :
    signedTailErrorBound n q 4 = signedDegreeThreeError n q := by
  unfold signedTailErrorBound signedTailEnergyBound signedDegreeThreeError
  norm_num

/-- Removing the entire level-three energy makes the new closed tail no
larger than the collision-proxy remainder. -/
theorem signed_degree_three_error_le_remainder_error_bound (n q : Nat) :
    signedDegreeThreeError n q ≤ remainderErrorBound n q := by
  unfold signedDegreeThreeError remainderErrorBound remainderEnergyBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.sqrt_le_sqrt
  have hthree : 0 ≤
      16 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
          (((2 ^ n - 2 : Nat) : Real) ^ 3)) := by positivity
  linarith

/-- Once triples exist, deleting the level-three energy makes the new tail
strictly smaller. -/
theorem signed_degree_three_error_lt_remainder_error_bound
    {n q : Nat} (hN : 3 ≤ 2 ^ n) (hq : 3 ≤ q) :
    signedDegreeThreeError n q < remainderErrorBound n q := by
  unfold signedDegreeThreeError remainderErrorBound remainderEnergyBound
  apply mul_lt_mul_of_pos_left _ (by norm_num)
  apply Real.sqrt_lt_sqrt (by positivity)
  have hC : 0 < (q.choose 3 : Real) := by
    exact_mod_cast Nat.choose_pos hq
  have hN1 : 0 < ((2 ^ n - 1 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < 2 ^ n - 1)
  have hN2 : 0 < ((2 ^ n - 2 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < 2 ^ n - 2)
  have hthree : 0 <
      16 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
          (((2 ^ n - 2 : Nat) : Real) ^ 3)) := by positivity
  linarith

/-- A finite product of losses is at most the reciprocal of one plus their
sum.  Unlike an exponential estimate, this rational form is convenient for
the exact sparse/dense comparison below. -/
theorem prod_one_sub_le_one_div_one_add_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → Real)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    ∏ i ∈ s, (1 - f i) ≤ 1 / (1 + ∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hfa0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
      have hfa1 : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
      have hs0 : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have hih := ih
        (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      calc
        (1 - f a) * ∏ i ∈ s, (1 - f i) ≤
            (1 - f a) * (1 / (1 + ∑ i ∈ s, f i)) :=
          mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hfa1)
        _ ≤ 1 / (1 + (f a + ∑ i ∈ s, f i)) := by
          have hd1 : 0 < 1 + ∑ i ∈ s, f i := by linarith
          have hd2 : 0 < 1 + (f a + ∑ i ∈ s, f i) := by linarith
          rw [show (1 - f a) * (1 / (1 + ∑ i ∈ s, f i)) =
              (1 - f a) / (1 + ∑ i ∈ s, f i) by ring]
          apply (div_le_div_iff₀ hd1 hd2).2
          nlinarith [sq_nonneg (f a), mul_nonneg hfa0 hs0]

/-- Rational upper bound on the exact no-collision probability. -/
theorem desc_factorial_ratio_le_card_div_card_add_choose
    {N q : Nat} (hN : 0 < N) (hqN : q ≤ N) :
    ((N.descFactorial q : Nat) : Real) / (N : Real) ^ q ≤
      (N : Real) / ((N : Real) + (q.choose 2 : Real)) := by
  have hNr : (0 : Real) < N := by exact_mod_cast hN
  have hdesc : (((N.descFactorial q : Nat) : Real)) =
      ∏ k ∈ Finset.range q, ((N : Real) - (k : Real)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro k hk
    rw [Nat.cast_sub]
    exact (Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) hqN).le
  have hprod :
      (∏ k ∈ Finset.range q, (1 - (k : Real) / (N : Real))) =
        ((N.descFactorial q : Nat) : Real) / (N : Real) ^ q := by
    conv_lhs =>
      arg 2
      ext k
      rw [show 1 - (k : Real) / (N : Real) =
          ((N : Real) - (k : Real)) / (N : Real) by field_simp]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
      ← hdesc]
  have hsumNat : ∑ k ∈ Finset.range q, k = q.choose 2 := by
    rw [Finset.sum_range_id, Nat.choose_two_right]
  have hsum : ∑ k ∈ Finset.range q, (k : Real) / (N : Real) =
      (q.choose 2 : Real) / (N : Real) := by
    rw [← Finset.sum_div]
    congr 1
    simpa only [Nat.cast_sum] using
      congrArg (fun x : Nat => (x : Real)) hsumNat
  rw [← hprod]
  calc
    ∏ k ∈ Finset.range q, (1 - (k : Real) / (N : Real)) ≤
        1 / (1 + ∑ k ∈ Finset.range q, (k : Real) / (N : Real)) := by
      apply prod_one_sub_le_one_div_one_add_sum
      · intro k hk
        positivity
      · intro k hk
        rw [div_le_one hNr]
        exact_mod_cast
          (Nat.lt_of_lt_of_le (Finset.mem_range.mp hk) hqN).le
    _ = (N : Real) / ((N : Real) + (q.choose 2 : Real)) := by
      rw [hsum]
      field_simp

/-- At or below half a collision in expectation, the rationally damped
sparse term is no larger than the old square-root dense term. -/
theorem card_ratio_mul_sparse_le_dense
    {N M : Nat} (hN : 9 ≤ N) (h2M : 2 * M ≤ N) :
    ((N : Real) / ((N : Real) + (M : Real))) *
        ((M : Real) / ((N - 1 : Nat) : Real) ^ 2) ≤
      Real.sqrt (M : Real) /
        (2 * ((N - 1 : Nat) : Real) *
          Real.sqrt ((N - 1 : Nat) : Real)) := by
  let NR : Real := N
  let MR : Real := M
  let A : Real := (N - 1 : Nat)
  have hNR9 : 9 ≤ NR := by dsimp [NR]; exact_mod_cast hN
  have h2MR : 2 * MR ≤ NR := by dsimp [MR, NR]; exact_mod_cast h2M
  have hMR0 : 0 ≤ MR := by dsimp [MR]; positivity
  have hNR0 : 0 ≤ NR := by linarith
  have hAeq : A = NR - 1 := by
    dsimp [A, NR]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  have hApos : 0 < A := by rw [hAeq]; linarith
  have hhalf : NR / 2 ≤ NR - MR := by linarith
  have hhalf0 : 0 ≤ NR / 2 := by positivity
  have hdiff0 : 0 ≤ NR - MR := by linarith
  have hsqDiff : (NR / 2) ^ 2 ≤ (NR - MR) ^ 2 :=
    (sq_le_sq₀ hhalf0 hdiff0).2 hhalf
  have h4NM : 4 * NR * MR ≤ 2 * NR ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left h2MR
      (show 0 ≤ 2 * NR by positivity)
    nlinarith
  have hN9term : 0 ≤ (NR - 9) * NR ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg NR)
  have hlargeDiff : 2 * NR ^ 2 ≤ (NR - 1) * (NR - MR) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsqDiff
      (show 0 ≤ NR - 1 by linarith)
    nlinarith
  have hpoly : 4 * NR ^ 2 * MR ≤ (NR + MR) ^ 2 * A := by
    rw [hAeq]
    nlinarith [hlargeDiff, h4NM]
  have hsqrtM : Real.sqrt MR ^ 2 = MR := Real.sq_sqrt hMR0
  have hsqrtA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hApos.le
  have hcoreSq : (2 * NR * Real.sqrt MR) ^ 2 ≤
      ((NR + MR) * Real.sqrt A) ^ 2 := by
    calc
      (2 * NR * Real.sqrt MR) ^ 2 = 4 * NR ^ 2 * MR := by
        rw [mul_pow, mul_pow, hsqrtM]
        ring
      _ ≤ (NR + MR) ^ 2 * A := hpoly
      _ = ((NR + MR) * Real.sqrt A) ^ 2 := by
        rw [mul_pow, hsqrtA]
  have hcore : 2 * NR * Real.sqrt MR ≤
      (NR + MR) * Real.sqrt A :=
    (sq_le_sq₀ (by positivity) (by positivity)).1 hcoreSq
  have hdenL : 0 < (NR + MR) * A ^ 2 := by positivity
  have hdenR : 0 < 2 * A * Real.sqrt A := by positivity
  dsimp [NR, MR, A] at hcore hdenL hdenR ⊢
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ hdenL hdenR).2
  have hfactor : 0 ≤
      Real.sqrt (M : Real) * ((N - 1 : Nat) : Real) *
        Real.sqrt ((N - 1 : Nat) : Real) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcore hfactor
  have hsm : Real.sqrt (M : Real) ^ 2 = (M : Real) :=
    Real.sq_sqrt (by positivity)
  have hsa : Real.sqrt ((N - 1 : Nat) : Real) ^ 2 =
      ((N - 1 : Nat) : Real) := Real.sq_sqrt (by positivity)
  calc
    (N : Real) * (M : Real) *
          (2 * ((N - 1 : Nat) : Real) *
            Real.sqrt ((N - 1 : Nat) : Real)) =
        2 * (N : Real) * (M : Real) * ((N - 1 : Nat) : Real) *
          Real.sqrt ((N - 1 : Nat) : Real) := by ring
    _ = 2 * (N : Real) * (Real.sqrt (M : Real) ^ 2) *
          ((N - 1 : Nat) : Real) *
          Real.sqrt ((N - 1 : Nat) : Real) := by rw [hsm]
    _ = 2 * (N : Real) * Real.sqrt (M : Real) *
          (Real.sqrt (M : Real) * ((N - 1 : Nat) : Real) *
            Real.sqrt ((N - 1 : Nat) : Real)) := by ring
    _ ≤ ((N : Real) + (M : Real)) *
          Real.sqrt ((N - 1 : Nat) : Real) *
          (Real.sqrt (M : Real) * ((N - 1 : Nat) : Real) *
            Real.sqrt ((N - 1 : Nat) : Real)) := hmul
    _ = ((N : Real) + (M : Real)) * Real.sqrt (M : Real) *
          ((N - 1 : Nat) : Real) *
          (Real.sqrt ((N - 1 : Nat) : Real) ^ 2) := by ring
    _ = Real.sqrt (M : Real) *
          (((N : Real) + (M : Real)) *
            ((N - 1 : Nat) : Real) ^ 2) := by
      rw [hsa]
      ring

theorem signed_truncation_advantage_four_eq_signed_degree_three_main
    {n q : Nat} (hN : 3 ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hneg : 8 * (q.choose 3 : Real) ≤
      (q.choose 2 : Real) * ((2 ^ n - 2 : Nat) : Real) ^ 2)
    (hpos : 4 * (q.choose 3 : Real) ≤
      (((2 ^ n : Nat) : Real) - (q.choose 2 : Real)) *
        ((2 ^ n - 2 : Nat) : Real)) :
    signedTruncationAdvantage n q 4 = signedDegreeThreeMain n q := by
  unfold signedTruncationAdvantage
  rw [half_average_abs_eq_neg_average_on
    (fun y : BitMatrix q n => Function.Injective y)
    (signedTruncationDensity n q 4)
    (average_signed_truncation_density_eq_zero n q 4)
    (signed_truncation_density_four_nonpos_of_injective hN hq hneg)
    (signed_truncation_density_four_nonneg_of_not_injective hN hq hpos)]
  have hpoint :
      (fun y : BitMatrix q n =>
        if Function.Injective y then signedTruncationDensity n q 4 y else 0) =
      (fun y => if Function.Injective y then
        (-(q.choose 2 : Real) /
            (((2 ^ n - 1 : Nat) : Real) ^ 2) +
          8 * (q.choose 3 : Real) /
            ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
              (((2 ^ n - 2 : Nat) : Real) ^ 2))) else 0) := by
    funext y
    by_cases hy : Function.Injective y
    · rw [if_pos hy, if_pos hy,
        signed_truncation_density_four_eq_of_injective (by omega) hq y hy]
    · rw [if_neg hy, if_neg hy]
  rw [hpoint, average_if_injective_const]
  unfold signedDegreeThreeMain
  ring

/-- The corrected signed main term never exceeds the elementary sparse
collision charge.  This records one formal sense in which the new certificate
is sharper before comparing dense branches. -/
theorem signed_degree_three_main_le_sparse_bound
    {n q : Nat} (hN : 3 ≤ 2 ^ n)
    (hneg : 8 * (q.choose 3 : Real) ≤
      (q.choose 2 : Real) * ((2 ^ n - 2 : Nat) : Real) ^ 2) :
    signedDegreeThreeMain n q ≤ sparseBound (XorSpace n) q := by
  let P : Real := ((((2 ^ n).descFactorial q : Nat) : Real) /
    (((2 ^ n : Nat) : Real) ^ q))
  let S : Real := (q.choose 2 : Real) /
    (((2 ^ n - 1 : Nat) : Real) ^ 2)
  let T : Real := 8 * (q.choose 3 : Real) /
    ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
      (((2 ^ n - 2 : Nat) : Real) ^ 2))
  have hN1pos : 0 < ((2 ^ n - 1 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < 2 ^ n - 1)
  have hN2pos : 0 < ((2 ^ n - 2 : Nat) : Real) := by
    exact_mod_cast (by omega : 0 < 2 ^ n - 2)
  have hpowPos : 0 < (((2 ^ n : Nat) : Real) ^ q) := by positivity
  have hdesc :
      ((((2 ^ n).descFactorial q : Nat) : Real)) ≤
        (((2 ^ n : Nat) : Real) ^ q) := by
    exact_mod_cast Nat.descFactorial_le_pow (2 ^ n) q
  have hPle : P ≤ 1 := by
    dsimp [P]
    exact (div_le_one hpowPos).2 hdesc
  have hPnonneg : 0 ≤ P := by dsimp [P]; positivity
  have hSnonneg : 0 ≤ S := by dsimp [S]; positivity
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hBnonneg : 0 ≤ S - T := by
    have hrearrange : S - T =
        ((q.choose 2 : Real) * ((2 ^ n - 2 : Nat) : Real) ^ 2 -
          8 * (q.choose 3 : Real)) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
          (((2 ^ n - 2 : Nat) : Real) ^ 2)) := by
      dsimp [S, T]
      field_simp [hN1pos.ne', hN2pos.ne']
    rw [hrearrange]
    exact div_nonneg (sub_nonneg.mpr hneg) (by positivity)
  have hBle : S - T ≤ S := by linarith
  unfold signedDegreeThreeMain sparseBound
  rw [pairCount_eq]
  simp only [card_xorSpace]
  change P * (S - T) ≤ S
  calc
    P * (S - T) ≤ 1 * (S - T) :=
      mul_le_mul_of_nonneg_right hPle hBnonneg
    _ ≤ S := by simpa using hBle

/-- The exact no-collision factor also places the corrected main term below
the old dense square-root branch throughout the sparse sign range. -/
theorem signed_degree_three_main_le_dense_bound_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    signedDegreeThreeMain n q ≤ denseBound (XorSpace n) q := by
  have hNpos : 0 < 2 ^ n := by positivity
  have hqN : q ≤ 2 ^ n := by omega
  have hN9 : 9 ≤ 2 ^ n := by
    have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have hPnonneg : 0 ≤
      (((2 ^ n).descFactorial q : Nat) : Real) /
        (((2 ^ n : Nat) : Real) ^ q) := by positivity
  have hTnonneg : 0 ≤
      8 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
          (((2 ^ n - 2 : Nat) : Real) ^ 2)) := by positivity
  have hSnonneg : 0 ≤
      (q.choose 2 : Real) /
        (((2 ^ n - 1 : Nat) : Real) ^ 2) := by positivity
  have hPbound :=
    desc_factorial_ratio_le_card_div_card_add_choose hNpos hqN
  calc
    signedDegreeThreeMain n q ≤
        ((((2 ^ n).descFactorial q : Nat) : Real) /
            (((2 ^ n : Nat) : Real) ^ q)) *
          ((q.choose 2 : Real) /
            (((2 ^ n - 1 : Nat) : Real) ^ 2)) := by
      unfold signedDegreeThreeMain
      apply mul_le_mul_of_nonneg_left _ hPnonneg
      linarith
    _ ≤ (((2 ^ n : Nat) : Real) /
            (((2 ^ n : Nat) : Real) + (q.choose 2 : Real))) *
          ((q.choose 2 : Real) /
            (((2 ^ n - 1 : Nat) : Real) ^ 2)) :=
      mul_le_mul_of_nonneg_right hPbound hSnonneg
    _ ≤ denseBound (XorSpace n) q := by
      simpa [denseBound, pairCount_eq, card_xorSpace] using
        (card_ratio_mul_sparse_le_dense hN9 h2pairs)

/-- Both pieces of the signed degree-three certificate improve the sparse
collision-proxy certificate. -/
theorem signed_degree_three_bound_le_sparse_add_remainder
    {n q : Nat} (hN : 3 ≤ 2 ^ n)
    (hneg : 8 * (q.choose 3 : Real) ≤
      (q.choose 2 : Real) * ((2 ^ n - 2 : Nat) : Real) ^ 2) :
    signedDegreeThreeMain n q + signedDegreeThreeError n q ≤
      sparseBound (XorSpace n) q + remainderErrorBound n q :=
  add_le_add (signed_degree_three_main_le_sparse_bound hN hneg)
    (signed_degree_three_error_le_remainder_error_bound n q)

theorem adaptive_transcript_advantage_le_signed_degree_three_main_add_error
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (hneg : 8 * (q.choose 3 : Real) ≤
      (q.choose 2 : Real) * ((2 ^ n - 2 : Nat) : Real) ^ 2)
    (hpos : 4 * (q.choose 3 : Real) ≤
      (((2 ^ n : Nat) : Real) - (q.choose 2 : Real)) *
        ((2 ^ n - 2 : Nat) : Real)) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
      signedDegreeThreeMain n q + signedDegreeThreeError n q := by
  have hq : q ≤ 2 ^ n := by omega
  have hN : 3 ≤ 2 ^ n := by
    have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  rw [← signed_tail_error_bound_four_eq_signed_degree_three_error,
    ← signed_truncation_advantage_four_eq_signed_degree_three_main
    hN hq hneg hpos]
  exact adaptive_transcript_advantage_le_signed_truncation_add_error_bound
    (r := 4) hn h2q (by omega) (by omega)

/-- Two transparent sparse-range checks imply both pointwise sign
inequalities.  The first is the ordinary half-population query condition;
the second says the expected pair count is at most one half. -/
theorem signed_degree_three_sign_conditions_of_sparse
    {n q : Nat} (hN : 6 ≤ 2 ^ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    8 * (q.choose 3 : Real) ≤
        (q.choose 2 : Real) * ((2 ^ n - 2 : Nat) : Real) ^ 2 ∧
      4 * (q.choose 3 : Real) ≤
        (((2 ^ n : Nat) : Real) - (q.choose 2 : Real)) *
          ((2 ^ n - 2 : Nat) : Real) := by
  let N : Real := ((2 ^ n : Nat) : Real)
  let M : Real := (q.choose 2 : Real)
  let C : Real := (q.choose 3 : Real)
  let Q : Real := (q : Real)
  let X : Real := ((q - 2 : Nat) : Real)
  have hN6 : (6 : Real) ≤ N := by
    dsimp [N]
    exact_mod_cast hN
  have h2qR : 2 * Q ≤ N := by
    dsimp [Q, N]
    exact_mod_cast h2q
  have h2MR : 2 * M ≤ N := by
    dsimp [M, N]
    exact_mod_cast h2pairs
  have hXQ : X ≤ Q := by
    dsimp [X, Q]
    exact_mod_cast Nat.sub_le q 2
  have h2X : 2 * X ≤ N := by linarith
  have hrelNat := Nat.choose_succ_right_eq q 2
  have hrel : 3 * C = M * X := by
    dsimp [C, M, X]
    norm_num at hrelNat
    have hrelReal : (q.choose 3 : Real) * 3 =
        (q.choose 2 : Real) * (q - 2 : Nat) := by
      exact_mod_cast hrelNat
    linarith
  have hN2cast : ((2 ^ n - 2 : Nat) : Real) = N - 2 := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : 2 ≤ 2 ^ n)]
    norm_num
  have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hXnonneg : 0 ≤ X := by dsimp [X]; positivity
  have hNnonneg : 0 ≤ N := by linarith
  constructor
  · have hquad : 4 * N ≤ 3 * (N - 2) ^ 2 := by
      nlinarith [sq_nonneg (N - 6)]
    have h8X : 8 * X ≤ 3 * (N - 2) ^ 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left h8X hMnonneg
    rw [hN2cast]
    nlinarith
  · have hprod := mul_le_mul h2MR h2X
        (mul_nonneg (by norm_num) hXnonneg) hNnonneg
    have h12C : 12 * C ≤ N ^ 2 := by
      nlinarith
    have hNtimes : 2 * N ^ 2 ≤ 3 * N * (N - 2) := by
      nlinarith [mul_nonneg hNnonneg (sub_nonneg.mpr hN6)]
    have h8C : 8 * C ≤ N * (N - 2) := by nlinarith
    have hgap : N ≤ 2 * (N - M) := by linarith
    have hN2nonneg : 0 ≤ N - 2 := by linarith
    have hgapMul := mul_le_mul_of_nonneg_right hgap hN2nonneg
    rw [hN2cast]
    nlinarith

/-- In the whole transparent sparse range, the new closed certificate is no
larger than the previous two-regime collision-proxy certificate.  This is a
finite theorem about the displayed formulas, not a numerical experiment. -/
theorem signed_degree_three_bound_le_min_sparse_dense_add_remainder_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    signedDegreeThreeMain n q + signedDegreeThreeError n q ≤
      min (sparseBound (XorSpace n) q) (denseBound (XorSpace n) q) +
        remainderErrorBound n q := by
  have hN6 : 6 ≤ 2 ^ n := by
    have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  obtain ⟨hneg, _⟩ :=
    signed_degree_three_sign_conditions_of_sparse hN6 h2q h2pairs
  apply add_le_add
  · exact le_min
      (signed_degree_three_main_le_sparse_bound (by omega) hneg)
      (signed_degree_three_main_le_dense_bound_sparse hn h2q h2pairs)
  · exact signed_degree_three_error_le_remainder_error_bound n q

/-- For three or more queries, the improvement over the previous closed
two-regime certificate is strict. -/
theorem signed_degree_three_bound_lt_min_sparse_dense_add_remainder_sparse
    {n q : Nat} (hn : 10 ≤ n) (hq3 : 3 ≤ q)
    (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    signedDegreeThreeMain n q + signedDegreeThreeError n q <
      min (sparseBound (XorSpace n) q) (denseBound (XorSpace n) q) +
        remainderErrorBound n q := by
  have hN6 : 6 ≤ 2 ^ n := by
    have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  obtain ⟨hneg, _⟩ :=
    signed_degree_three_sign_conditions_of_sparse hN6 h2q h2pairs
  apply add_lt_add_of_le_of_lt
  · exact le_min
      (signed_degree_three_main_le_sparse_bound (by omega) hneg)
      (signed_degree_three_main_le_dense_bound_sparse hn h2q h2pairs)
  · exact signed_degree_three_error_lt_remainder_error_bound (by omega) hq3

theorem adaptive_transcript_advantage_le_signed_degree_three_main_add_error_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
      signedDegreeThreeMain n q + signedDegreeThreeError n q := by
  have hN : 6 ≤ 2 ^ n := by
    have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  obtain ⟨hneg, hpos⟩ :=
    signed_degree_three_sign_conditions_of_sparse hN h2q h2pairs
  exact adaptive_transcript_advantage_le_signed_degree_three_main_add_error
    hn h2q hneg hpos

/-- The same sparse hypotheses give a two-sided approximation, not only an
upper bound: the true adaptive advantage lies within the level-four tail of
the exact signed degree-three main term. -/
theorem abs_advantage_sub_signed_degree_three_main_le_error_sparse
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    |RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        signedDegreeThreeMain n q| ≤
      signedDegreeThreeError n q := by
  have hN6 : 6 ≤ 2 ^ n := by
    have : 2 ^ 10 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  have hN3 : 3 ≤ 2 ^ n := by omega
  have hq : q ≤ 2 ^ n := by omega
  obtain ⟨hneg, hpos⟩ :=
    signed_degree_three_sign_conditions_of_sparse hN6 h2q h2pairs
  rw [← signed_tail_error_bound_four_eq_signed_degree_three_error,
    ← signed_truncation_advantage_four_eq_signed_degree_three_main
    hN3 hq hneg hpos]
  exact abs_advantage_sub_signed_truncation_advantage_le_error_bound
    (r := 4) hn h2q (by omega) (by omega)

end RandomSystems.SoP.XORSignedDegreeThree
