/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORInjection
import RandomSystems.SoP.XORCollisionProxy

/-!
# Full-deck checksum and quotient symmetries for XOR SoP

This file records the exact algebraic part of the representative used to
study the XOR of two permutations when more than half of the domain is
queried.  At the full domain, the visible density is the XOR convolution of
two uniform-injection densities.  Its Walsh coefficients are constant on the
orbits obtained by adding one character to every row.

The zero-checksum slice is the orbit of the constant Walsh mode.  Its density
is normalized and its exact distance from uniform is `1 - 1 / 2^n`.  These
facts explain the last-query jump without imposing a low-query hypothesis.

The analytic estimate on the remaining quotient orbits is deliberately not
claimed here.  That estimate is the open high-query tail obligation described
in `sketches/sop-complement-regime.md`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.SoP.XORComplement

open RandomSystems.Applications.SoP
open RandomSystems.SoP.CollisionProxy
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-! ## The checksum slice -/

/-- XOR checksum of a visible tape. -/
def tapeXor {n q : Nat} (y : BitMatrix q n) : XorSpace n :=
  ∑ i : Fin q, y i

/-- The Walsh mask which repeats one character on every row. -/
def constantMask {n q : Nat} (alpha : XorSpace n) : BitMatrix q n :=
  fun _i => alpha

/-- Tape checksum is additive. -/
theorem tape_xor_add {n q : Nat} (x y : BitMatrix q n) :
    tapeXor (x + y) = tapeXor x + tapeXor y := by
  unfold tapeXor
  simp_rw [Pi.add_apply]
  rw [Finset.sum_add_distrib]

/-- A constant Walsh mask reads exactly the XOR checksum of the tape. -/
theorem vector_walsh_tape_xor {n q : Nat}
    (alpha : XorSpace n) (y : BitMatrix q n) :
    vectorWalsh alpha (tapeXor y) = walsh (constantMask alpha) y := by
  unfold vectorWalsh vectorDot tapeXor walsh dot constantMask
  congr 1
  simp_rw [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Density, relative to uniform, of the zero-checksum slice. -/
def checksumDensity (n q : Nat) (y : BitMatrix q n) : Real :=
  if tapeXor y = 0 then ((2 ^ n : Nat) : Real) else 0

/-- Fourier expansion of the zero-checksum density. -/
theorem checksum_density_eq_sum_walsh {n q : Nat} (y : BitMatrix q n) :
    checksumDensity n q y =
      ∑ alpha : XorSpace n, walsh (constantMask alpha) y := by
  calc
    checksumDensity n q y =
        ∑ alpha : XorSpace n, vectorWalsh alpha (tapeXor y) := by
      unfold checksumDensity
      rw [sum_vectorWalsh_dual]
      by_cases hy : tapeXor y = 0
      · norm_num [hy]
      · norm_num [hy]
    _ = ∑ alpha : XorSpace n, walsh (constantMask alpha) y := by
      apply Finset.sum_congr rfl
      intro alpha _halpha
      exact vector_walsh_tape_xor alpha y

/-- With at least one row, the constant-mask embedding has trivial kernel. -/
theorem constant_mask_eq_zero_iff {n q : Nat} (hq : 0 < q)
    (alpha : XorSpace n) :
    constantMask (q := q) alpha = 0 ↔ alpha = 0 := by
  constructor
  · intro h
    have hi : Fin q := ⟨0, hq⟩
    exact congrFun h hi
  · intro h
    subst alpha
    rfl

/-- The zero-checksum density has total mass one. -/
theorem average_checksum_density_eq_one {n q : Nat} (hq : 0 < q) :
    average (BitMatrix q n) (checksumDensity n q) = 1 := by
  calc
    average (BitMatrix q n) (checksumDensity n q) =
        average (BitMatrix q n)
          (fun y => ∑ alpha : XorSpace n,
            walsh (constantMask alpha) y) := by
      apply congrArg (average (BitMatrix q n))
      funext y
      exact checksum_density_eq_sum_walsh y
    _ = ∑ alpha : XorSpace n,
        average (BitMatrix q n) (walsh (constantMask alpha)) :=
      average_fintype_sum _
    _ = ∑ alpha : XorSpace n,
        if constantMask (q := q) alpha = 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro alpha _halpha
      exact average_walsh _
    _ = 1 := by
      simp [constant_mask_eq_zero_iff hq]

/-- The finite set of tapes satisfying the XOR checksum. -/
def checksumSlice (n q : Nat) : Finset (BitMatrix q n) :=
  Finset.univ.filter (fun y => tapeXor y = 0)

/-- A uniformly random nonempty tape has zero checksum with probability
exactly `1 / 2^n`. -/
theorem checksum_slice_card_div_card {n q : Nat} (hq : 0 < q) :
    (checksumSlice n q).card /
        (Fintype.card (BitMatrix q n) : Real) =
      1 / ((2 ^ n : Nat) : Real) := by
  have havg := average_checksum_density_eq_one (n := n) hq
  have hN : (((2 ^ n : Nat) : Real)) ≠ 0 := by positivity
  have hcard : (Fintype.card (BitMatrix q n) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (BitMatrix q n) ≠ 0)
  unfold average at havg
  rw [show (∑ y : BitMatrix q n, checksumDensity n q y) =
      ((checksumSlice n q).card : Real) * ((2 ^ n : Nat) : Real) by
    unfold checksumDensity checksumSlice
    rw [← Finset.sum_filter]
    simp [Finset.sum_const, nsmul_eq_mul]] at havg
  field_simp [hN, hcard] at havg ⊢
  nlinarith

/-- Cauchy--Schwarz restricted to the checksum slice.  Compared with an
unrestricted bound, the squared energy gains the support probability
`1 / 2^n`. -/
theorem average_abs_le_sqrt_checksum_average_sq {n q : Nat} (hq : 0 < q)
    (f : BitMatrix q n → Real)
    (hsupport : ∀ y, tapeXor y ≠ 0 → f y = 0) :
    average (BitMatrix q n) (fun y => |f y|) ≤
      Real.sqrt
        ((1 / ((2 ^ n : Nat) : Real)) *
          average (BitMatrix q n) (fun y => (f y) ^ 2)) := by
  let A := BitMatrix q n
  let s := checksumSlice n q
  have hsum_abs :
      (∑ y : A, |f y|) = ∑ y ∈ s, |f y| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro y _hyuniv hynot
    have hne : tapeXor y ≠ 0 := by
      intro hzero
      apply hynot
      simp [s, checksumSlice, hzero]
    simp [hsupport y hne]
  have hsum_sq :
      (∑ y : A, (f y) ^ 2) = ∑ y ∈ s, (f y) ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ s)
    intro y _hyuniv hynot
    have hne : tapeXor y ≠ 0 := by
      intro hzero
      apply hynot
      simp [s, checksumSlice, hzero]
    simp [hsupport y hne]
  have hs := sq_sum_le_card_mul_sum_sq
    (s := s) (f := fun y : A => |f y|)
  have hsquare :
      (average A (fun y => |f y|)) ^ 2 ≤
        ((s.card : Real) / (Fintype.card A : Real)) *
          average A (fun y => (f y) ^ 2) := by
    unfold average
    rw [hsum_abs, hsum_sq]
    have hcard : (Fintype.card A : Real) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
    by_cases hs0 : s.card = 0
    · have hempty : s = ∅ := Finset.card_eq_zero.mp hs0
      simp [hempty]
    · have hsR : (s.card : Real) ≠ 0 := by exact_mod_cast hs0
      field_simp [hcard, hsR]
      simpa [sq_abs] using hs
  apply Real.le_sqrt_of_sq_le
  rw [← checksum_slice_card_div_card (n := n) hq]
  exact hsquare

/-- Half of the uniform `L1` distance of the checksum density from one. -/
def checksumAdvantage (n q : Nat) : Real :=
  (1 / 2 : Real) *
    average (BitMatrix q n) (fun y => |checksumDensity n q y - 1|)

/-- Exact distinguishing gap of the zero-checksum test. -/
theorem checksum_advantage_eq {n q : Nat} (hn : 1 ≤ n) (hq : 0 < q) :
    checksumAdvantage n q = 1 - 1 / ((2 ^ n : Nat) : Real) := by
  let N : Nat := 2 ^ n
  have hn0 : n ≠ 0 := by omega
  have hN : 2 ≤ N := by
    change 2 ≤ 2 ^ n
    exact Nat.one_lt_two_pow hn0
  have hNR : (N : Real) ≠ 0 := by positivity
  have hNone : (1 : Real) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hNm1 : 0 ≤ (N : Real) - 1 := by linarith
  have hpoint (y : BitMatrix q n) :
      |checksumDensity n q y - 1| =
        checksumDensity n q y * (1 - 2 / (N : Real)) + 1 := by
    by_cases hy : tapeXor y = 0
    · rw [show checksumDensity n q y = (N : Real) by
        simp [checksumDensity, hy, N]]
      rw [abs_of_nonneg hNm1]
      field_simp [hNR]
      ring
    · rw [show checksumDensity n q y = 0 by
        simp [checksumDensity, hy]]
      norm_num
  unfold checksumAdvantage
  simp_rw [hpoint]
  rw [average_add, average_const, average_mul_const,
    average_checksum_density_eq_one hq]
  dsimp [N] at hNR ⊢
  field_simp [hNR]
  ring

/-! ## The full collision proxy is pointwise honest -/

/-- The checksum-conditioned collision proxy on a full tape.  Its two
factors expose the global checksum orbit and the translated pair orbit. -/
def fullProxyDensity (n : Nat) (y : BitMatrix (2 ^ n) n) : Real :=
  checksumDensity n (2 ^ n) y *
    proxyDensity (XorSpace n) (2 ^ n) y

/-- At the full domain the ordinary planted-collision density remains
nonnegative.  This is one ingredient of the checksum-conditioned full proxy. -/
theorem proxy_density_full_nonneg {n : Nat} (hn : 1 ≤ n)
    (y : BitMatrix (2 ^ n) n) :
    0 ≤ proxyDensity (XorSpace n) (2 ^ n) y := by
  let N : Nat := 2 ^ n
  have hn0 : n ≠ 0 := by omega
  have hN : 2 ≤ N := by
    dsimp [N]
    exact Nat.one_lt_two_pow hn0
  have hNreal : (2 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have hNm1 : 0 < (N : Real) - 1 := by linarith
  have hK : 0 ≤ collisionCount (G := XorSpace n) N y := by
    change 0 ≤ pairCollisionCountReal (XorSpace n) N y
    rw [pairCollisionCountReal_eq_pairCollisionCountNat]
    positivity
  have hcoef :
      0 ≤ (N : Real) / ((N - 1 : Nat) : Real) ^ 2 := by
    positivity
  have hbase :
      0 ≤ 1 + (N : Real) / ((N - 1 : Nat) : Real) ^ 2 *
        (0 - (pairCount N : Real) / (N : Real)) := by
    rw [pairCount_eq, Nat.cast_choose_two]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num only [Nat.cast_one]
    have hN0 : (N : Real) ≠ 0 := by positivity
    have hNm10 : (N : Real) - 1 ≠ 0 := ne_of_gt hNm1
    have hprod :
        0 ≤ ((N : Real) - 1) * ((N : Real) - 2) :=
      mul_nonneg (by linarith) (by linarith)
    field_simp [hN0, hNm10]
    nlinarith
  unfold proxyDensity collisionKernel centeredCollisionCount collisionMean
  simp only [card_xorSpace]
  change 0 ≤ 1 + (N : Real) / ((N - 1 : Nat) : Real) ^ 2 *
    (collisionCount (G := XorSpace n) N y -
      (pairCount N : Real) / (N : Real))
  calc
    0 ≤ 1 + (N : Real) / ((N - 1 : Nat) : Real) ^ 2 *
        (0 - (pairCount N : Real) / (N : Real)) := hbase
    _ ≤ 1 + (N : Real) / ((N - 1 : Nat) : Real) ^ 2 *
        (collisionCount (G := XorSpace n) N y -
          (pairCount N : Real) / (N : Real)) := by
      gcongr

/-- Exact transcript-independent floor of the full collision proxy. -/
theorem proxy_density_full_lower_bound {n : Nat} (hn : 1 ≤ n)
    (y : BitMatrix (2 ^ n) n) :
    (((2 ^ n : Nat) : Real) - 2) /
        (2 * (((2 ^ n : Nat) : Real) - 1)) ≤
      proxyDensity (XorSpace n) (2 ^ n) y := by
  let N : Nat := 2 ^ n
  have hn0 : n ≠ 0 := by omega
  have hN : 2 ≤ N := by
    dsimp [N]
    exact Nat.one_lt_two_pow hn0
  have hNreal : (2 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have hNm1 : 0 < (N : Real) - 1 := by linarith
  have hK : 0 ≤ collisionCount (G := XorSpace n) N y := by
    change 0 ≤ pairCollisionCountReal (XorSpace n) N y
    rw [pairCollisionCountReal_eq_pairCollisionCountNat]
    positivity
  have hcoef :
      0 ≤ (N : Real) / ((N - 1 : Nat) : Real) ^ 2 := by
    positivity
  have hbase :
      1 + (N : Real) / ((N - 1 : Nat) : Real) ^ 2 *
          (0 - (pairCount N : Real) / (N : Real)) =
        ((N : Real) - 2) / (2 * ((N : Real) - 1)) := by
    rw [pairCount_eq, Nat.cast_choose_two]
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num only [Nat.cast_one]
    have hN0 : (N : Real) ≠ 0 := by positivity
    have hNm10 : (N : Real) - 1 ≠ 0 := ne_of_gt hNm1
    field_simp [hN0, hNm10]
    ring
  unfold proxyDensity collisionKernel centeredCollisionCount collisionMean
  simp only [card_xorSpace]
  change ((N : Real) - 2) / (2 * ((N : Real) - 1)) ≤
    1 + (N : Real) / ((N - 1 : Nat) : Real) ^ 2 *
      (collisionCount (G := XorSpace n) N y -
        (pairCount N : Real) / (N : Real))
  rw [← hbase]
  gcongr

/-- The full checksum-conditioned collision proxy has no negative mass. -/
theorem full_proxy_density_nonneg {n : Nat} (hn : 1 ≤ n)
    (y : BitMatrix (2 ^ n) n) :
    0 ≤ fullProxyDensity n y := by
  apply mul_nonneg
  · unfold checksumDensity
    split
    · positivity
    · positivity
  · exact proxy_density_full_nonneg hn y

/-- A nonzero character repeated on every row uses every row. -/
theorem level_constant_mask {n q : Nat} (alpha : XorSpace n)
    (halpha : alpha ≠ 0) :
    level (constantMask (q := q) alpha) = q := by
  simp [level, rowSupport, constantMask, halpha]

/-- With at least three rows, a constant mask cannot be a nontrivial pair
mask. -/
theorem constant_mask_ne_pair_mask {n q : Nat} (hq : 3 ≤ q)
    (p : PairIndex q) (alpha beta : XorSpace n) (halpha : alpha ≠ 0) :
    constantMask (q := q) beta ≠ pairMask p alpha := by
  intro h
  have hlevel := congrArg level h
  rw [level_pairMask p alpha halpha] at hlevel
  by_cases hbeta : beta = 0
  · subst beta
    simp [constantMask, level, rowSupport] at hlevel
  · rw [level_constant_mask beta hbeta] at hlevel
    omega

/-- Full-domain collision kernel as the sum of its nontrivial pair masks. -/
theorem collision_kernel_eq_pair_mask_sum_full {n : Nat} (hn : 1 ≤ n)
    (y : BitMatrix (2 ^ n) n) :
    collisionKernel (XorSpace n) (2 ^ n) y =
      ∑ p : PairIndex (2 ^ n),
        ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
            (fun alpha => alpha ≠ 0),
          (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
            walsh (pairMask p alpha) y := by
  have hn0 : n ≠ 0 := by omega
  have hN : 2 ≤ 2 ^ n := Nat.one_lt_two_pow hn0
  rw [← levelTwoSpectrum_eq_collisionKernel hN (le_refl (2 ^ n))]
  exact levelTwoSpectrum_eq_pairMaskSum (le_refl (2 ^ n)) y

/-- Constant checksum modes are orthogonal to every nontrivial pair mode
once the tape has at least three rows. -/
theorem average_constant_mask_mul_pair_mask_eq_zero {n q : Nat}
    (hq : 3 ≤ q) (p : PairIndex q) (alpha beta : XorSpace n)
    (halpha : alpha ≠ 0) :
    average (BitMatrix q n)
        (fun y => walsh (constantMask beta) y * walsh (pairMask p alpha) y) =
      0 := by
  rw [average_walsh_mul_walsh]
  simp [constant_mask_ne_pair_mask hq p alpha beta halpha]

/-- Conditioning on the full checksum does not change the mean of the
centered pair-collision kernel. -/
theorem average_checksum_density_mul_collision_kernel_eq_zero {n : Nat}
    (hn : 2 ≤ n) :
    average (BitMatrix (2 ^ n) n)
        (fun y => checksumDensity n (2 ^ n) y *
          collisionKernel (XorSpace n) (2 ^ n) y) = 0 := by
  have hn1 : 1 ≤ n := by omega
  have hq : 3 ≤ 2 ^ n := by
    have : 4 ≤ 2 ^ n := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  let c : Real := 1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)
  rw [show (fun y : BitMatrix (2 ^ n) n =>
      checksumDensity n (2 ^ n) y *
        collisionKernel (XorSpace n) (2 ^ n) y) =
      (fun y =>
        (∑ beta : XorSpace n, walsh (constantMask beta) y) *
          (∑ p : PairIndex (2 ^ n),
            ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
                (fun alpha => alpha ≠ 0),
              c * walsh (pairMask p alpha) y)) by
    funext y
    rw [← checksum_density_eq_sum_walsh,
      ← collision_kernel_eq_pair_mask_sum_full hn1]]
  rw [show (fun y : BitMatrix (2 ^ n) n =>
      (∑ beta : XorSpace n, walsh (constantMask beta) y) *
        (∑ p : PairIndex (2 ^ n),
          ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
              (fun alpha => alpha ≠ 0),
            c * walsh (pairMask p alpha) y)) =
      (fun y =>
        ∑ p : PairIndex (2 ^ n),
          ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
              (fun alpha => alpha ≠ 0),
            ∑ beta : XorSpace n,
              c * (walsh (constantMask beta) y *
                walsh (pairMask p alpha) y)) by
    funext y
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    apply Finset.sum_congr rfl
    intro alpha _halpha
    apply Finset.sum_congr rfl
    intro beta _hbeta
    ring]
  rw [average_fintype_sum]
  apply Finset.sum_eq_zero
  intro p _hp
  rw [average_finset_sum]
  apply Finset.sum_eq_zero
  intro alpha halpha
  rw [average_fintype_sum]
  apply Finset.sum_eq_zero
  intro beta _hbeta
  rw [average_const_mul]
  rw [average_constant_mask_mul_pair_mask_eq_zero hq p alpha beta]
  · ring
  · simpa using (Finset.mem_filter.mp halpha).2

/-- The checksum-conditioned full collision proxy has total mass one. -/
theorem average_full_proxy_density_eq_one {n : Nat} (hn : 2 ≤ n) :
    average (BitMatrix (2 ^ n) n) (fullProxyDensity n) = 1 := by
  have hq : 0 < 2 ^ n := pow_pos (by omega) n
  rw [show fullProxyDensity n =
      (fun y => checksumDensity n (2 ^ n) y +
        checksumDensity n (2 ^ n) y *
          collisionKernel (XorSpace n) (2 ^ n) y) by
    funext y
    unfold fullProxyDensity proxyDensity
    ring]
  rw [average_add, average_checksum_density_eq_one hq,
    average_checksum_density_mul_collision_kernel_eq_zero hn]
  ring

/-- On the checksum slice, the full proxy density is at least one. -/
theorem one_le_full_proxy_density_of_tape_xor_eq_zero {n : Nat}
    (hn : 2 ≤ n) (y : BitMatrix (2 ^ n) n) (hy : tapeXor y = 0) :
    1 ≤ fullProxyDensity n y := by
  let N : Nat := 2 ^ n
  have hN : 4 ≤ N := by
    dsimp [N]
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hNreal : (4 : Real) ≤ (N : Real) := by exact_mod_cast hN
  have hNm1 : 0 < (N : Real) - 1 := by linarith
  have hden : 0 < 2 * ((N : Real) - 1) := mul_pos (by norm_num) hNm1
  have hfirst :
      1 ≤ (N : Real) *
        (((N : Real) - 2) / (2 * ((N : Real) - 1))) := by
    rw [show (N : Real) *
        (((N : Real) - 2) / (2 * ((N : Real) - 1))) =
      ((N : Real) * ((N : Real) - 2)) /
        (2 * ((N : Real) - 1)) by ring]
    rw [le_div_iff₀ hden]
    have hprod : 0 ≤ (N : Real) * ((N : Real) - 4) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith
  have hlower := proxy_density_full_lower_bound (n := n) (by omega) y
  rw [show fullProxyDensity n y =
      (N : Real) * proxyDensity (XorSpace n) N y by
    unfold fullProxyDensity checksumDensity
    simp [hy, N]]
  exact hfirst.trans (mul_le_mul_of_nonneg_left hlower (by positivity))

/-- Half of the uniform `L1` distance of the full proxy from uniform. -/
def fullProxyAdvantage (n : Nat) : Real :=
  (1 / 2 : Real) *
    average (BitMatrix (2 ^ n) n) (fun y => |fullProxyDensity n y - 1|)

/-- The full proxy has the exact checksum-saturation distance `1 - 1/N`. -/
theorem full_proxy_advantage_eq {n : Nat} (hn : 2 ≤ n) :
    fullProxyAdvantage n = 1 - 1 / ((2 ^ n : Nat) : Real) := by
  let N : Nat := 2 ^ n
  have hN0 : (N : Real) ≠ 0 := by positivity
  have hq : 0 < 2 ^ n := pow_pos (by omega) n
  have hpoint (y : BitMatrix (2 ^ n) n) :
      |fullProxyDensity n y - 1| =
        fullProxyDensity n y + 1 +
          (-2 / (N : Real)) * checksumDensity n (2 ^ n) y := by
    by_cases hy : tapeXor y = 0
    · rw [abs_of_nonneg
          (sub_nonneg.mpr
            (one_le_full_proxy_density_of_tape_xor_eq_zero hn y hy))]
      rw [show checksumDensity n (2 ^ n) y = (N : Real) by
        simp [checksumDensity, hy, N]]
      field_simp [hN0]
      ring
    · rw [show fullProxyDensity n y = 0 by
        unfold fullProxyDensity checksumDensity
        simp [hy]]
      rw [show checksumDensity n (2 ^ n) y = 0 by
        simp [checksumDensity, hy]]
      norm_num
  unfold fullProxyAdvantage
  simp_rw [hpoint]
  rw [average_add, average_add, average_full_proxy_density_eq_one hn,
    average_const, average_const_mul,
    average_checksum_density_eq_one hq]
  dsimp [N] at hN0 ⊢
  field_simp [hN0]
  ring

/-! ## Quotienting full Walsh masks by global character shifts -/

/-- A full injection contains every XOR word exactly once. -/
theorem tape_xor_full_embedding {n : Nat}
    (e : Fin (2 ^ n) ↪ XorSpace n) :
    tapeXor e = ∑ x : XorSpace n, x := by
  have hb : Function.Bijective e :=
    (Fintype.bijective_iff_injective_and_card e).2
      ⟨e.injective, by simp⟩
  let ee : Fin (2 ^ n) ≃ XorSpace n := Equiv.ofBijective e hb
  exact Fintype.sum_equiv ee (fun i : Fin (2 ^ n) => e i)
    (fun x : XorSpace n => x) (fun _i => rfl)

/-- The exact full convolution has no mass away from the zero-checksum
slice. -/
theorem full_convolution_eq_zero_of_tape_xor_ne_zero {n : Nat}
    (y : BitMatrix (2 ^ n) n) (hy : tapeXor y ≠ 0) :
    convolution (injectionDensity n (2 ^ n))
        (injectionDensity n (2 ^ n)) y = 0 := by
  unfold convolution average
  have hsum :
      (∑ x : BitMatrix (2 ^ n) n,
        injectionDensity n (2 ^ n) x *
          injectionDensity n (2 ^ n) (y + x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _hxmem
    by_cases hx : Function.Injective x
    · by_cases hyx : Function.Injective (y + x)
      · have hxsum : tapeXor x = ∑ z : XorSpace n, z :=
          tape_xor_full_embedding ⟨x, hx⟩
        have hyxsum : tapeXor (y + x) = ∑ z : XorSpace n, z :=
          tape_xor_full_embedding ⟨y + x, hyx⟩
        rw [tape_xor_add, hxsum] at hyxsum
        have hyzero : tapeXor y = 0 := by
          apply add_right_cancel (b := ∑ z : XorSpace n, z)
          simpa using hyxsum
        exact (hy hyzero).elim
      · simp [injectionDensity, hyx]
    · simp [injectionDensity, hx]
  rw [hsum]
  simp

/-- Signed error left after removing the checksum-conditioned collision
proxy from the exact full convolution. -/
def fullResidualDensity (n : Nat) (y : BitMatrix (2 ^ n) n) : Real :=
  convolution (injectionDensity n (2 ^ n))
      (injectionDensity n (2 ^ n)) y - fullProxyDensity n y

/-- Half of the uniform `L1` norm of the signed full residual. -/
def fullResidualAdvantage (n : Nat) : Real :=
  (1 / 2 : Real) *
    average (BitMatrix (2 ^ n) n) (fun y => |fullResidualDensity n y|)

/-- Uniform squared energy of the signed full residual. -/
def fullResidualEnergy (n : Nat) : Real :=
  average (BitMatrix (2 ^ n) n)
    (fun y => (fullResidualDensity n y) ^ 2)

/-- The signed full residual inherits the exact checksum support. -/
theorem full_residual_density_eq_zero_of_tape_xor_ne_zero {n : Nat}
    (y : BitMatrix (2 ^ n) n) (hy : tapeXor y ≠ 0) :
    fullResidualDensity n y = 0 := by
  unfold fullResidualDensity fullProxyDensity checksumDensity
  rw [full_convolution_eq_zero_of_tape_xor_ne_zero y hy]
  simp [hy]

/-- Support-aware conversion of a full residual energy estimate to `L1`.
This is the extra `1 / sqrt(N)` supplied by the signed full-deck
representative. -/
theorem average_abs_full_residual_density_le_sqrt_energy {n : Nat} :
    average (BitMatrix (2 ^ n) n) (fun y => |fullResidualDensity n y|) ≤
      Real.sqrt
        ((1 / ((2 ^ n : Nat) : Real)) *
          average (BitMatrix (2 ^ n) n)
            (fun y => (fullResidualDensity n y) ^ 2)) := by
  apply average_abs_le_sqrt_checksum_average_sq
  · positivity
  · intro y hy
    exact full_residual_density_eq_zero_of_tape_xor_ne_zero y hy

/-- Half-`L1` form of the support-aware energy conversion. -/
theorem full_residual_advantage_le_sqrt_energy {n : Nat} :
    fullResidualAdvantage n ≤
      (1 / 2 : Real) *
        Real.sqrt
          ((1 / ((2 ^ n : Nat) : Real)) * fullResidualEnergy n) := by
  unfold fullResidualAdvantage fullResidualEnergy
  gcongr
  exact average_abs_full_residual_density_le_sqrt_energy

/-- Adding one character to every full mask row changes an injection
coefficient only by a sign independent of the sampled injection. -/
theorem fourier_injection_density_add_constant_mask_full {n : Nat}
    (a : BitMatrix (2 ^ n) n) (alpha : XorSpace n) :
    fourier (injectionDensity n (2 ^ n)) (a + constantMask alpha) =
      vectorWalsh alpha (∑ x : XorSpace n, x) *
        fourier (injectionDensity n (2 ^ n)) a := by
  rw [fourier_injectionDensity_eq_average_embedding (le_refl (2 ^ n))]
  rw [fourier_injectionDensity_eq_average_embedding (le_refl (2 ^ n))]
  calc
    average (Fin (2 ^ n) ↪ XorSpace n)
        (fun e => walsh (a + constantMask alpha) e) =
      average (Fin (2 ^ n) ↪ XorSpace n)
        (fun e => walsh a e *
          vectorWalsh alpha (∑ x : XorSpace n, x)) := by
        apply congrArg (average (Fin (2 ^ n) ↪ XorSpace n))
        funext e
        rw [walsh_add_left, ← vector_walsh_tape_xor,
          tape_xor_full_embedding]
    _ = average (Fin (2 ^ n) ↪ XorSpace n)
          (fun e => walsh a e) *
        vectorWalsh alpha (∑ x : XorSpace n, x) := by
      rw [average_mul_const]
    _ = vectorWalsh alpha (∑ x : XorSpace n, x) *
        average (Fin (2 ^ n) ↪ XorSpace n)
          (fun e => walsh a e) := by ring

/-- The squared injection coefficient is exactly invariant under a global
character shift. -/
theorem fourier_injection_density_sq_add_constant_mask_full {n : Nat}
    (a : BitMatrix (2 ^ n) n) (alpha : XorSpace n) :
    fourier (injectionDensity n (2 ^ n))
        (a + constantMask alpha) ^ 2 =
      fourier (injectionDensity n (2 ^ n)) a ^ 2 := by
  rw [fourier_injection_density_add_constant_mask_full]
  have hc :
      vectorWalsh alpha (∑ x : XorSpace n, x) ^ 2 = 1 := by
    unfold vectorWalsh
    rw [pow_two, bitSign_mul_self]
  rw [mul_pow, hc]
  ring

/-- The full visible convolution coefficient is constant on every global
character-shift orbit.  This is the exact quotient identity needed before
estimating the high-query signed tail. -/
theorem fourier_full_convolution_add_constant_mask {n : Nat}
    (a : BitMatrix (2 ^ n) n) (alpha : XorSpace n) :
    fourier
        (convolution (injectionDensity n (2 ^ n))
          (injectionDensity n (2 ^ n)))
        (a + constantMask alpha) =
      fourier
        (convolution (injectionDensity n (2 ^ n))
          (injectionDensity n (2 ^ n))) a := by
  simp only [fourier_convolution]
  simpa [pow_two] using
    fourier_injection_density_sq_add_constant_mask_full a alpha

/-! ## A concrete cross-section of the global-shift quotient -/

/-- A distinguished row of a full Walsh mask.  The full domain is nonempty
for every bit width, including `n = 0`. -/
def fullAnchor (n : Nat) : Fin (2 ^ n) :=
  ⟨0, pow_pos (by omega) n⟩

/-- Full Walsh masks whose distinguished row is zero.  Every global-character
orbit has exactly one such representative. -/
def AnchoredMask (n : Nat) :=
  {a : BitMatrix (2 ^ n) n // a (fullAnchor n) = 0}

noncomputable instance anchoredMaskFintype (n : Nat) :
    Fintype (AnchoredMask n) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Subtract (equivalently, in characteristic two, add) the anchor row from
every row of a full mask. -/
def normalizeFullMask {n : Nat} (a : BitMatrix (2 ^ n) n) :
    BitMatrix (2 ^ n) n :=
  a + constantMask (a (fullAnchor n))

@[simp]
theorem normalizeFullMask_anchor {n : Nat} (a : BitMatrix (2 ^ n) n) :
    normalizeFullMask a (fullAnchor n) = 0 := by
  funext j
  change a (fullAnchor n) j + a (fullAnchor n) j = 0
  exact CharTwo.add_self_eq_zero _

/-- A full mask is uniquely its anchored representative plus one global
character.  This is the finite quotient construction used by the dense
residual estimate; no abstract quotient type is needed. -/
def globalShiftOrbitEquiv (n : Nat) :
    (XorSpace n × AnchoredMask n) ≃ BitMatrix (2 ^ n) n where
  toFun z := z.2.1 + constantMask z.1
  invFun a :=
    ⟨a (fullAnchor n), ⟨normalizeFullMask a, normalizeFullMask_anchor a⟩⟩
  left_inv z := by
    rcases z with ⟨alpha, b⟩
    dsimp
    apply Prod.ext
    · change b.1 (fullAnchor n) + alpha = alpha
      rw [b.2, zero_add]
    · apply Subtype.ext
      funext i
      change b.1 i + alpha + (b.1 (fullAnchor n) + alpha) = b.1 i
      rw [b.2, zero_add, add_assoc]
      have hself : alpha + alpha = 0 := by
        funext j
        exact CharTwo.add_self_eq_zero (alpha j)
      rw [hself, add_zero]
  right_inv a := by
    dsimp
    funext i
    change a i + a (fullAnchor n) + a (fullAnchor n) = a i
    rw [add_assoc]
    have hself : a (fullAnchor n) + a (fullAnchor n) = 0 := by
      funext j
      exact CharTwo.add_self_eq_zero _
    rw [hself, add_zero]

/-- An orbit-invariant sum over all full masks is `2^n` times its sum over
the anchored cross-section. -/
theorem sum_global_shift_invariant_eq_card_mul_sum_anchored
    {n : Nat} (F : BitMatrix (2 ^ n) n → Real)
    (hinv : ∀ a alpha, F (a + constantMask alpha) = F a) :
    (∑ a : BitMatrix (2 ^ n) n, F a) =
      ((2 ^ n : Nat) : Real) * ∑ b : AnchoredMask n, F b.1 := by
  calc
    (∑ a : BitMatrix (2 ^ n) n, F a) =
        ∑ z : XorSpace n × AnchoredMask n,
          F (globalShiftOrbitEquiv n z) := by
      exact Fintype.sum_equiv (globalShiftOrbitEquiv n).symm
        F (fun z => F (globalShiftOrbitEquiv n z))
        (fun a => by simp)
    _ = ∑ alpha : XorSpace n, ∑ b : AnchoredMask n, F b.1 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro alpha _halpha
      apply Finset.sum_congr rfl
      intro b _hb
      exact hinv b.1 alpha
    _ = ((2 ^ n : Nat) : Real) * ∑ b : AnchoredMask n, F b.1 := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- Any function supported on the zero-checksum slice has Fourier
coefficients constant on global-character orbits. -/
theorem fourier_add_constant_mask_of_checksum_support
    {n q : Nat} (f : BitMatrix q n → Real)
    (hsupport : ∀ y, tapeXor y ≠ 0 → f y = 0)
    (a : BitMatrix q n) (alpha : XorSpace n) :
    fourier f (a + constantMask alpha) = fourier f a := by
  unfold XORFourier.fourier
  apply congrArg (average (BitMatrix q n))
  funext y
  by_cases hy : tapeXor y = 0
  · rw [walsh_add_left, ← vector_walsh_tape_xor, hy]
    simp
  · rw [hsupport y hy]
    ring

theorem fourier_full_residual_add_constant_mask {n : Nat}
    (a : BitMatrix (2 ^ n) n) (alpha : XorSpace n) :
    fourier (fullResidualDensity n) (a + constantMask alpha) =
      fourier (fullResidualDensity n) a := by
  apply fourier_add_constant_mask_of_checksum_support
  intro y hy
  exact full_residual_density_eq_zero_of_tape_xor_ne_zero y hy

/-- The residual Fourier energy after choosing the unique representative in
each global-shift orbit whose anchor row is zero. -/
def anchoredResidualEnergy (n : Nat) : Real :=
  ∑ b : AnchoredMask n, (fourier (fullResidualDensity n) b.1) ^ 2

/-- Full Parseval counts exactly `2^n` copies of every quotient mode. -/
theorem full_residual_energy_eq_card_mul_anchored {n : Nat} :
    fullResidualEnergy n =
      ((2 ^ n : Nat) : Real) * anchoredResidualEnergy n := by
  unfold fullResidualEnergy anchoredResidualEnergy
  rw [parseval_sq]
  apply sum_global_shift_invariant_eq_card_mul_sum_anchored
  intro a alpha
  rw [fourier_full_residual_add_constant_mask]

/-- After quotienting global shifts, the checksum support gain and the orbit
multiplicity cancel exactly.  This is the normalized dense-regime endpoint:
only `anchoredResidualEnergy` remains to be estimated. -/
theorem full_residual_advantage_le_sqrt_anchored {n : Nat} :
    fullResidualAdvantage n ≤
      (1 / 2 : Real) * Real.sqrt (anchoredResidualEnergy n) := by
  calc
    fullResidualAdvantage n ≤
        (1 / 2 : Real) *
          Real.sqrt
            ((1 / ((2 ^ n : Nat) : Real)) * fullResidualEnergy n) :=
      full_residual_advantage_le_sqrt_energy
    _ = (1 / 2 : Real) * Real.sqrt (anchoredResidualEnergy n) := by
      rw [full_residual_energy_eq_card_mul_anchored]
      congr 2
      have hN : ((2 ^ n : Nat) : Real) ≠ 0 := by positivity
      field_simp

/-- Direct consumer for the one remaining aggregate fourth-moment estimate. -/
theorem full_residual_advantage_le_of_anchored_energy
    {n : Nat} {B : Real} (henergy : anchoredResidualEnergy n ≤ B) :
    fullResidualAdvantage n ≤ (1 / 2 : Real) * Real.sqrt B := by
  calc
    fullResidualAdvantage n ≤
        (1 / 2 : Real) * Real.sqrt (anchoredResidualEnergy n) :=
      full_residual_advantage_le_sqrt_anchored
    _ ≤ (1 / 2 : Real) * Real.sqrt B := by
      gcongr

end RandomSystems.SoP.XORComplement
