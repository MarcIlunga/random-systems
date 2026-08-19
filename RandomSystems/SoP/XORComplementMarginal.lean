/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORComplementEntropy
import RandomSystems.VirtualPDS

/-!
# Marginal contraction for the XOR complement residual

The full-deck complement argument produces a signed residual on `N = 2^n`
answer coordinates.  This file packages it as a virtual finite law and proves
that signed marginalization cannot increase its norm.  Zero-extension of
Walsh masks then identifies the marginal exactly: whenever at least three
rows remain hidden, the full checksum-conditioned proxy becomes the ordinary
collision proxy and the full residual becomes the visible remainder.

Consequently the exact adaptive XOR-SoP advantage differs from the collision
proxy advantage by at most `7/N` for every `q ≤ N - 3` and `n ≥ 63`.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORComplement

open RandomSystems
open RandomSystems.CR18
open RandomSystems.Applications.SoP
open RandomSystems.SoP.CollisionProxy
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Restrict a full answer tape to its first `q` coordinates. -/
def fullTapePrefix {n q : Nat} (hq : q ≤ 2 ^ n) :
    BitMatrix (2 ^ n) n → BitMatrix q n :=
  fun y i => y (Fin.castLE hq i)

/-- The signed full-deck residual as an actual element of the repository's
linear distribution carrier. -/
def fullResidualSignedLaw (n : Nat) : Dist (BitMatrix (2 ^ n) n) :=
  Dist.ofUniformDensity (BitMatrix (2 ^ n) n) (fullResidualDensity n)

/-- The residual visible on the first `q` coordinates.  Fiber masses are
combined before absolute values are taken. -/
def prefixResidualSignedLaw {n q : Nat} (hq : q ≤ 2 ^ n) :
    Dist (BitMatrix q n) :=
  Dist.fTransform (fullTapePrefix hq) (fullResidualSignedLaw n)

theorem virtualDistance_fullResidualSignedLaw_zero (n : Nat) :
    Dist.virtualDistance (fullResidualSignedLaw n) 0 =
      fullResidualAdvantage n := by
  rw [fullResidualSignedLaw, Dist.virtualDistance_ofUniformDensity_zero]
  rfl

/-- Signed data processing is exactly the desired full-to-prefix residual
contraction. -/
theorem virtualDistance_prefixResidualSignedLaw_le_full
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    Dist.virtualDistance (prefixResidualSignedLaw hq) 0 ≤
      fullResidualAdvantage n := by
  calc
    Dist.virtualDistance (prefixResidualSignedLaw hq) 0 =
        Dist.virtualDistance
          (Dist.fTransform (fullTapePrefix hq) (fullResidualSignedLaw n))
          (Dist.fTransform (fullTapePrefix hq) 0) := by
      rw [show Dist.fTransform (fullTapePrefix hq)
          (0 : Dist (BitMatrix (2 ^ n) n)) = 0 from
        Finsupp.mapDomain_zero]
      rfl
    _ ≤ Dist.virtualDistance (fullResidualSignedLaw n) 0 :=
      Dist.virtualDistance_fTransform_le
        (fullTapePrefix hq) (fullResidualSignedLaw n) 0
    _ = fullResidualAdvantage n :=
      virtualDistance_fullResidualSignedLaw_zero n

theorem virtualDistance_prefixResidualSignedLaw_le_seven_div
    {n q : Nat} (hn : 63 ≤ n) (hq : q ≤ 2 ^ n) :
    Dist.virtualDistance (prefixResidualSignedLaw hq) 0 ≤
      7 / (((2 ^ n : Nat) : Real)) :=
  (virtualDistance_prefixResidualSignedLaw_le_full hq).trans
    (fullResidualAdvantage_le_seven_div hn)

/-- Split the full row set into its first `q` rows and its remaining rows. -/
def rowSplitEquiv {q N : Nat} (hq : q ≤ N) :
    Fin q ⊕ Fin (N - q) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hq))

/-- Join a visible prefix and a hidden suffix into one full tape. -/
def joinTape {G : Type*} {q N : Nat} (hq : q ≤ N)
    (y : Fin q → G) (z : Fin (N - q) → G) : Fin N → G :=
  fun i => Sum.elim y z ((rowSplitEquiv hq).symm i)

@[simp]
theorem joinTape_left {G : Type*} {q N : Nat} (hq : q ≤ N)
    (y : Fin q → G) (z : Fin (N - q) → G) (i : Fin q) :
    joinTape hq y z (rowSplitEquiv hq (Sum.inl i)) = y i := by
  simp [joinTape]

@[simp]
theorem joinTape_right {G : Type*} {q N : Nat} (hq : q ≤ N)
    (y : Fin q → G) (z : Fin (N - q) → G) (i : Fin (N - q)) :
    joinTape hq y z (rowSplitEquiv hq (Sum.inr i)) = z i := by
  simp [joinTape]

/-- Splitting and joining tapes is an equivalence. -/
def joinTapeEquiv (G : Type*) {q N : Nat} (hq : q ≤ N) :
    ((Fin q → G) × (Fin (N - q) → G)) ≃ (Fin N → G) where
  toFun yz := joinTape hq yz.1 yz.2
  invFun x :=
    (λi => x (rowSplitEquiv hq (Sum.inl i)),
      λj => x (rowSplitEquiv hq (Sum.inr j)))
  left_inv yz := by
    apply Prod.ext <;> funext i <;> simp [joinTape]
  right_inv x := by
    funext i
    have he := (rowSplitEquiv hq).apply_symm_apply i
    generalize hs : (rowSplitEquiv hq).symm i = s at he ⊢
    cases s <;> simp_all [joinTape]

/-- Uniform hidden marginal of a density on full tapes. -/
def prefixMarginal {G : Type*} [Fintype G] {q N : Nat} (hq : q ≤ N)
    (f : (Fin N → G) → ℝ) (y : Fin q → G) : ℝ :=
  average (Fin (N - q) → G) (fun z => f (joinTape hq y z))

theorem average_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : A × B → ℝ) :
    average (A × B) f = average A (fun a => average B (fun b => f (a, b))) := by
  unfold average
  rw [Fintype.sum_prod_type]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [Fintype.card_prod, Nat.cast_mul]
  field_simp

theorem average_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) :
    average A (fun a => f (e a)) = average B f := by
  unfold average
  rw [Equiv.sum_comp e]
  congr 1
  exact_mod_cast Fintype.card_congr e

/-- Finite Jensen/triangle inequality for a uniform average. -/
theorem abs_average_le_average_abs {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    |average A f| ≤ average A (fun a => |f a|) := by
  unfold average
  have hc : 0 ≤ (Fintype.card A : ℝ) := by positivity
  rw [abs_div, abs_of_nonneg hc]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hc

/-- Marginalization cannot increase the uniform `L1` norm. -/
theorem average_abs_prefixMarginal_le {G : Type*} [Fintype G] [Nonempty G]
    {q N : Nat} (hq : q ≤ N) (f : (Fin N → G) → ℝ) :
    average (Fin q → G) (fun y => |prefixMarginal hq f y|) ≤
      average (Fin N → G) (fun x => |f x|) := by
  calc
    average (Fin q → G) (fun y => |prefixMarginal hq f y|) ≤
        average (Fin q → G)
          (fun y => average (Fin (N - q) → G)
            (fun z => |f (joinTape hq y z)|)) := by
      apply CollisionProxy.uniformAverage_mono
      intro y
      exact abs_average_le_average_abs _
    _ = average (((Fin q → G) × (Fin (N - q) → G)))
          (fun yz => |f (joinTape hq yz.1 yz.2)|) := by
      rw [average_prod]
    _ = average (Fin N → G) (fun x => |f x|) := by
      exact average_equiv (joinTapeEquiv G hq) (fun x => |f x|)

/-- Include the visible row set into the full row set. -/
def prefixEmbedding {q N : Nat} (hq : q ≤ N) : Fin q ↪ Fin N where
  toFun i := rowSplitEquiv hq (Sum.inl i)
  inj' := fun _ _ h => Sum.inl.inj ((rowSplitEquiv hq).injective h)

/-- Extend a visible Walsh mask by zero on every hidden row. -/
def padMask {n q N : Nat} (hq : q ≤ N) (a : BitMatrix q n) :
    BitMatrix N n :=
  joinTape hq a 0

@[simp]
theorem restrictMask_padMask {n q N : Nat} (hq : q ≤ N)
    (a : BitMatrix q n) :
    restrictMask (prefixEmbedding hq) (padMask hq a) = a := by
  funext i
  simp [restrictMask, prefixEmbedding, padMask]

theorem padMask_eq_zero_off_prefix {n q N : Nat} (hq : q ≤ N)
    (a : BitMatrix q n) (i : Fin N)
    (hi : i ∉ Set.range (prefixEmbedding hq)) :
    padMask hq a i = 0 := by
  have hs : ∃ j : Fin (N - q), rowSplitEquiv hq (Sum.inr j) = i := by
    let s := (rowSplitEquiv hq).symm i
    have he : rowSplitEquiv hq s = i := (rowSplitEquiv hq).apply_symm_apply i
    rcases hs' : s with k | j
    · exfalso
      apply hi
      refine ⟨k, ?_⟩
      simpa [prefixEmbedding, hs'] using he
    · refine ⟨j, ?_⟩
      simpa [hs'] using he
  obtain ⟨j, rfl⟩ := hs
  simp [padMask]

/-- A zero-padded mask ignores the hidden suffix. -/
theorem walsh_padMask_joinTape {n q N : Nat} (hq : q ≤ N)
    (a : BitMatrix q n) (y : BitMatrix q n)
    (z : BitMatrix (N - q) n) :
    walsh (padMask hq a) (joinTape hq y z) = walsh a y := by
  unfold walsh dot padMask
  congr 1
  rw [show
      (∑ i : Fin N,
        ∑ j : Fin n, joinTape hq a 0 i j * joinTape hq y z i j) =
      ∑ s : Fin q ⊕ Fin (N - q),
        ∑ j : Fin n,
          joinTape hq a 0 (rowSplitEquiv hq s) j *
            joinTape hq y z (rowSplitEquiv hq s) j by
    exact (Equiv.sum_comp (rowSplitEquiv hq)
      (fun i : Fin N =>
        ∑ j : Fin n, joinTape hq a 0 i j * joinTape hq y z i j)).symm]
  rw [Fintype.sum_sum_type]
  simp [joinTape]

/-- Fourier transform commutes exactly with the prefix marginal: it simply
deletes every full mask having a nonzero hidden row. -/
theorem fourier_prefixMarginal {n q N : Nat} (hq : q ≤ N)
    (f : BitMatrix N n → ℝ) (a : BitMatrix q n) :
    XORFourier.fourier (prefixMarginal hq f) a =
      XORFourier.fourier f (padMask hq a) := by
  unfold XORFourier.fourier prefixMarginal
  rw [show
      (fun y : BitMatrix q n =>
        average (BitMatrix (N - q) n) (fun z => f (joinTape hq y z)) *
          walsh a y) =
      (fun y => average (BitMatrix (N - q) n)
        (fun z => f (joinTape hq y z) * walsh a y)) by
    funext y
    rw [average_mul_const]]
  rw [← average_prod
    (fun yz : BitMatrix q n × BitMatrix (N - q) n =>
      f (joinTape hq yz.1 yz.2) * walsh a yz.1)]
  rw [show
      (fun yz : BitMatrix q n × BitMatrix (N - q) n =>
        f (joinTape hq yz.1 yz.2) * walsh a yz.1) =
      (fun yz => f (joinTape hq yz.1 yz.2) *
        walsh (padMask hq a) (joinTape hq yz.1 yz.2)) by
    funext yz
    rw [walsh_padMask_joinTape]]
  exact average_equiv (joinTapeEquiv (XorSpace n) hq)
    (fun x => f x * walsh (padMask hq a) x)

/-- The full uniform-injection density marginalizes to the corresponding
visible uniform-injection density.  In Fourier language this is just the fact
that a zero-padded checkerboard only uses visible rows. -/
theorem fourier_prefixMarginal_full_injection {n q : Nat}
    (hq : q ≤ 2 ^ n) (a : BitMatrix q n) :
    XORFourier.fourier
        (prefixMarginal hq (injectionDensity n (2 ^ n))) a =
      XORFourier.fourier (injectionDensity n q) a := by
  rw [fourier_prefixMarginal]
  rw [fourier_injectionDensity_eq_restrictMask
    (le_refl (2 ^ n)) (prefixEmbedding hq) (padMask hq a)
    (padMask_eq_zero_off_prefix hq a)]
  rw [restrictMask_padMask]

/-- Marginalization of the exact full two-permutation likelihood is exactly
the visible two-permutation likelihood. -/
theorem fourier_prefixMarginal_full_convolution {n q : Nat}
    (hq : q ≤ 2 ^ n) (a : BitMatrix q n) :
    XORFourier.fourier
        (prefixMarginal hq
          (convolution (injectionDensity n (2 ^ n))
            (injectionDensity n (2 ^ n)))) a =
      XORFourier.fourier
        (convolution (injectionDensity n q) (injectionDensity n q)) a := by
  rw [fourier_prefixMarginal]
  rw [fourier_convolution, fourier_convolution]
  rw [fourier_injectionDensity_eq_restrictMask
    (le_refl (2 ^ n)) (prefixEmbedding hq) (padMask hq a)
    (padMask_eq_zero_off_prefix hq a)]
  rw [restrictMask_padMask]

theorem prefixMarginal_full_convolution_eq {n q : Nat}
    (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    prefixMarginal hq
        (convolution (injectionDensity n (2 ^ n))
          (injectionDensity n (2 ^ n))) y =
      convolution (injectionDensity n q) (injectionDensity n q) y := by
  rw [← fourier_inversion
    (prefixMarginal hq
      (convolution (injectionDensity n (2 ^ n))
        (injectionDensity n (2 ^ n)))) y]
  rw [← fourier_inversion
    (convolution (injectionDensity n q) (injectionDensity n q)) y]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fourier_prefixMarginal_full_convolution hq a]

theorem proxy_density_eq_level_zero_add_two {n q : Nat}
    (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    proxyDensity (XorSpace n) q y =
      spectralPart (fun a : BitMatrix q n => level a = 0)
          (convolution (injectionDensity n q) (injectionDensity n q)) y +
        spectralPart (fun a : BitMatrix q n => level a = 2)
          (convolution (injectionDensity n q) (injectionDensity n q)) y := by
  unfold proxyDensity
  rw [levelZeroSpectrum_eq_one hq]
  rw [levelTwoSpectrum_eq_collisionKernel hN hq]

theorem fourier_add_density {n q : Nat} (f g : BitMatrix q n → ℝ)
    (a : BitMatrix q n) :
    XORFourier.fourier (fun y => f y + g y) a =
      XORFourier.fourier f a + XORFourier.fourier g a := by
  unfold XORFourier.fourier
  rw [show
      (fun x : BitMatrix q n => (f x + g x) * walsh a x) =
        (fun x => f x * walsh a x + g x * walsh a x) by
    funext x
    ring]
  exact average_add _ _

/-- Exact visible spectrum of the collision proxy: retain precisely levels
zero and two of the exact two-injection convolution. -/
theorem fourier_proxyDensity {n q : Nat}
    (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n) (a : BitMatrix q n) :
    XORFourier.fourier (proxyDensity (XorSpace n) q) a =
      (if level a = 0 then
          XORFourier.fourier
            (convolution (injectionDensity n q) (injectionDensity n q)) a
        else 0) +
      (if level a = 2 then
          XORFourier.fourier
            (convolution (injectionDensity n q) (injectionDensity n q)) a
        else 0) := by
  rw [show proxyDensity (XorSpace n) q =
      (fun y =>
        spectralPart (fun a : BitMatrix q n => level a = 0)
            (convolution (injectionDensity n q) (injectionDensity n q)) y +
          spectralPart (fun a : BitMatrix q n => level a = 2)
            (convolution (injectionDensity n q) (injectionDensity n q)) y) by
    funext y
    exact proxy_density_eq_level_zero_add_two hN hq y]
  rw [fourier_add_density, fourier_spectralPart, fourier_spectralPart]
  split_ifs <;> rfl

/-- Include the hidden row set into the full row set. -/
def hiddenEmbedding {q N : Nat} (hq : q ≤ N) : Fin (N - q) ↪ Fin N where
  toFun i := rowSplitEquiv hq (Sum.inr i)
  inj' := fun _ _ h => Sum.inr.inj ((rowSplitEquiv hq).injective h)

theorem hiddenEmbedding_not_prefix_range {q N : Nat} (hq : q ≤ N)
    (j : Fin (N - q)) :
    hiddenEmbedding hq j ∉ Set.range (prefixEmbedding hq) := by
  rintro ⟨i, h⟩
  have := (rowSplitEquiv hq).injective h
  cases this

@[simp]
theorem padMask_hidden {n q N : Nat} (hq : q ≤ N)
    (a : BitMatrix q n) (j : Fin (N - q)) :
    padMask hq a (hiddenEmbedding hq j) = 0 := by
  simp [padMask, hiddenEmbedding]

/-- Three hidden rows guarantee that one hidden row lies outside any chosen
pair of full coordinates. -/
theorem exists_hiddenEmbedding_outside_pair {q N : Nat} (hq : q ≤ N)
    (hhidden : 3 ≤ N - q) (p : PairIndex N) :
    ∃ j : Fin (N - q),
      hiddenEmbedding hq j ≠ p.1.1 ∧ hiddenEmbedding hq j ≠ p.1.2 := by
  let S : Finset (Fin N) :=
    (Finset.univ : Finset (Fin (N - q))).image (hiddenEmbedding hq)
  by_contra h
  have hsub : S ⊆ {p.1.1, p.1.2} := by
    intro i hi
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hi
    have hjnot : ¬ (hiddenEmbedding hq j ≠ p.1.1 ∧
        hiddenEmbedding hq j ≠ p.1.2) := by
      intro hj
      exact h ⟨j, hj⟩
    have hj : hiddenEmbedding hq j = p.1.1 ∨
        hiddenEmbedding hq j = p.1.2 := by tauto
    rcases hj with hj | hj <;> simp [hj]
  have hcardS : S.card = N - q := by
    simp [S, Finset.card_image_of_injective, (hiddenEmbedding hq).injective]
  have hcardPair : ({p.1.1, p.1.2} : Finset (Fin N)).card ≤ 2 := by
    calc
      ({p.1.1, p.1.2} : Finset (Fin N)).card ≤
          ({p.1.2} : Finset (Fin N)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 := by simp
  have := Finset.card_le_card hsub
  rw [hcardS] at this
  omega

theorem padMask_eq_constantMask_iff {n q N : Nat} (hq : q ≤ N)
    (hhidden : 0 < N - q) (a : BitMatrix q n) (beta : XorSpace n) :
    padMask hq a = constantMask beta ↔ a = 0 ∧ beta = 0 := by
  constructor
  · intro h
    let j : Fin (N - q) := ⟨0, hhidden⟩
    have hb := congrFun h (hiddenEmbedding hq j)
    have hb0 : beta = 0 := by
      simpa [constantMask] using hb.symm
    subst beta
    constructor
    · rw [← restrictMask_padMask hq a]
      funext i
      simp [restrictMask, constantMask, h, prefixEmbedding]
    · rfl
  · rintro ⟨rfl, rfl⟩
    funext i j
    simp [padMask, constantMask, joinTape]

@[simp]
theorem constantMask_zero' {n q : Nat} :
    constantMask (q := q) (0 : XorSpace n) = 0 := by
  rfl

theorem padMask_isConstantMode_iff {n q N : Nat} (hq : q ≤ N)
    (hhidden : 0 < N - q) (a : BitMatrix q n) :
    IsConstantMode (padMask hq a) ↔ a = 0 := by
  constructor
  · rintro ⟨beta, h⟩
    exact (padMask_eq_constantMask_iff hq hhidden a beta).mp h |>.1
  · rintro rfl
    refine ⟨0, ?_⟩
    exact (padMask_eq_constantMask_iff hq hhidden 0 0).mpr ⟨rfl, rfl⟩

theorem pairMask_apply_eq_if_mem {n q : Nat} (p : PairIndex q)
    (alpha : XorSpace n) (i : Fin q) :
    pairMask p alpha i =
      if i ∈ ({p.1.1, p.1.2} : Finset (Fin q)) then alpha else 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  unfold pairMask
  by_cases hil : i = p.1.1 <;> by_cases hir : i = p.1.2 <;>
    simp [hil, hir]

/-- Send a visible unordered pair to the corresponding pair of full rows. -/
def liftPairIndex {q N : Nat} (hq : q ≤ N) (p : PairIndex q) : PairIndex N :=
  pairIndexOfNe (prefixEmbedding hq p.1.1) (prefixEmbedding hq p.1.2)
    (fun h => (ne_of_lt p.2) ((prefixEmbedding hq).injective h))

theorem liftPairIndex_endpointSet {q N : Nat} (hq : q ≤ N)
    (p : PairIndex q) :
    ({(liftPairIndex hq p).1.1, (liftPairIndex hq p).1.2} : Finset (Fin N)) =
      {prefixEmbedding hq p.1.1, prefixEmbedding hq p.1.2} := by
  unfold liftPairIndex
  exact pairIndexOfNe_endpointSet _

/-- Padding commutes with the pair-mask construction. -/
theorem padMask_pairMask {n q N : Nat} (hq : q ≤ N)
    (p : PairIndex q) (alpha : XorSpace n) :
    padMask hq (pairMask p alpha) = pairMask (liftPairIndex hq p) alpha := by
  funext i
  have he := (rowSplitEquiv hq).apply_symm_apply i
  generalize hs : (rowSplitEquiv hq).symm i = s at he
  cases s with
  | inl k =>
    rw [← he]
    rw [show padMask hq (pairMask p alpha)
        (rowSplitEquiv hq (Sum.inl k)) = pairMask p alpha k by
      simp [padMask]]
    change pairMask p alpha k =
      pairMask (liftPairIndex hq p) alpha (prefixEmbedding hq k)
    rw [pairMask_apply_eq_if_mem, pairMask_apply_eq_if_mem]
    rw [liftPairIndex_endpointSet]
    simp [(prefixEmbedding hq).injective.eq_iff]
  | inr j =>
    rw [← he]
    rw [show padMask hq (pairMask p alpha)
        (rowSplitEquiv hq (Sum.inr j)) = 0 by
      simp [padMask]]
    change 0 = pairMask (liftPairIndex hq p) alpha (hiddenEmbedding hq j)
    rw [pairMask_apply_eq_if_mem]
    rw [liftPairIndex_endpointSet]
    have hj1 : hiddenEmbedding hq j ≠ prefixEmbedding hq p.1.1 := by
      intro h
      exact hiddenEmbedding_not_prefix_range hq j ⟨p.1.1, h.symm⟩
    have hj2 : hiddenEmbedding hq j ≠ prefixEmbedding hq p.1.2 := by
      intro h
      exact hiddenEmbedding_not_prefix_range hq j ⟨p.1.2, h.symm⟩
    simp [hj1, hj2]

/-- Equal-row level-two masks are exactly the nontrivial pair masks. -/
theorem exists_pairMask_iff_level_two_supportRowsEqual {n q : Nat}
    (a : BitMatrix q n) :
    (∃ p : PairIndex q, ∃ alpha : XorSpace n,
        alpha ≠ 0 ∧ a = pairMask p alpha) ↔
      level a = 2 ∧ supportRowsEqual a := by
  constructor
  · rintro ⟨p, alpha, halpha, rfl⟩
    exact ⟨level_pairMask p alpha halpha,
      supportRowsEqual_pairMask p alpha⟩
  · intro ha
    let aa : EqualLevelTwoMask n q := ⟨a, ha⟩
    obtain ⟨z, hz⟩ := pairMaskParameterToMask_surjective aa
    refine ⟨z.1, z.2.1, z.2.2, ?_⟩
    exact congrArg Subtype.val hz |>.symm

theorem exists_prefixEmbedding_or_hiddenEmbedding {q N : Nat}
    (hq : q ≤ N) (i : Fin N) :
    (∃ k : Fin q, prefixEmbedding hq k = i) ∨
      ∃ j : Fin (N - q), hiddenEmbedding hq j = i := by
  have he := (rowSplitEquiv hq).apply_symm_apply i
  generalize hs : (rowSplitEquiv hq).symm i = s at he
  cases s with
  | inl k =>
      left
      exact ⟨k, by simpa [prefixEmbedding] using he⟩
  | inr j =>
      right
      exact ⟨j, by simpa [hiddenEmbedding] using he⟩

/-- With three unobserved rows, a zero-padded mask lies in a translated-pair
orbit exactly when its visible part is a genuine equal-row pair mask. -/
theorem padMask_isTranslatedPairMode_iff {n q N : Nat} (hq : q ≤ N)
    (hhidden : 3 ≤ N - q) (a : BitMatrix q n) :
    IsTranslatedPairMode (padMask hq a) ↔
      level a = 2 ∧ supportRowsEqual a := by
  constructor
  · rintro ⟨⟨beta, ⟨p, ⟨alpha, halpha⟩⟩⟩, hmode⟩
    obtain ⟨j, hjl, hjr⟩ :=
      exists_hiddenEmbedding_outside_pair hq hhidden p
    have hbeta_eval := congrFun hmode (hiddenEmbedding hq j)
    have hbeta : beta = 0 := by
      simpa [translatedPairParameterToMask, constantMask, pairMask,
        hjl, hjr] using hbeta_eval.symm
    subst beta
    have hpair : padMask hq a = pairMask p alpha := by
      simpa [translatedPairParameterToMask, constantMask] using hmode
    have hpLeft : ∃ i : Fin q, prefixEmbedding hq i = p.1.1 := by
      rcases exists_prefixEmbedding_or_hiddenEmbedding hq p.1.1 with hi | hi
      · exact hi
      · obtain ⟨j, hj⟩ := hi
        have hv := congrFun hpair (hiddenEmbedding hq j)
        rw [padMask_hidden, hj, pairMask_left] at hv
        exact (halpha hv.symm).elim
    have hpRight : ∃ i : Fin q, prefixEmbedding hq i = p.1.2 := by
      rcases exists_prefixEmbedding_or_hiddenEmbedding hq p.1.2 with hi | hi
      · exact hi
      · obtain ⟨j, hj⟩ := hi
        have hv := congrFun hpair (hiddenEmbedding hq j)
        rw [padMask_hidden, hj, pairMask_right] at hv
        exact (halpha hv.symm).elim
    obtain ⟨il, hil⟩ := hpLeft
    obtain ⟨ir, hir⟩ := hpRight
    have hilr : il ≠ ir := by
      intro h
      apply ne_of_lt p.2
      rw [← hil, ← hir, h]
    let pv : PairIndex q := pairIndexOfNe il ir hilr
    have hpvSet :
        ({(liftPairIndex hq pv).1.1, (liftPairIndex hq pv).1.2} :
            Finset (Fin N)) = {p.1.1, p.1.2} := by
      rw [liftPairIndex_endpointSet]
      have hset := congrArg (Finset.image (prefixEmbedding hq))
        (pairIndexOfNe_endpointSet hilr)
      simpa [pv, Finset.image_insert, Finset.image_singleton, hil, hir] using hset
    have hpv : liftPairIndex hq pv = p :=
      pairIndex_eq_of_endpointSet_eq _ _ hpvSet
    have hpadded : padMask hq a = padMask hq (pairMask pv alpha) := by
      calc
        padMask hq a = pairMask p alpha := hpair
        _ = pairMask (liftPairIndex hq pv) alpha := by rw [hpv]
        _ = padMask hq (pairMask pv alpha) :=
          (padMask_pairMask hq pv alpha).symm
    have hvis : a = pairMask pv alpha := by
      have hr := congrArg (restrictMask (prefixEmbedding hq)) hpadded
      simpa using hr
    exact exists_pairMask_iff_level_two_supportRowsEqual a |>.mp
      ⟨pv, alpha, halpha, hvis⟩
  · intro ha
    obtain ⟨p, alpha, halpha, haeq⟩ :=
      exists_pairMask_iff_level_two_supportRowsEqual a |>.mpr ha
    refine ⟨⟨0, ⟨liftPairIndex hq p, ⟨alpha, halpha⟩⟩⟩, ?_⟩
    rw [haeq, padMask_pairMask]
    simp [translatedPairParameterToMask]

/-- On every zero-padded mask with at least three hidden rows, the full
checksum-conditioned proxy has exactly the visible collision-proxy Fourier
coefficient. -/
theorem two_le_exponent_of_three_hidden {n q : Nat}
    (hhidden : 3 ≤ 2 ^ n - q) : 2 ≤ n := by
  have hpow : 3 ≤ 2 ^ n := hhidden.trans (Nat.sub_le _ _)
  by_contra hn
  have hnle : n ≤ 1 := by omega
  have hp : 2 ^ n ≤ 2 ^ 1 :=
    Nat.pow_le_pow_right (by omega) hnle
  norm_num at hp
  omega

theorem three_le_exponent_of_level_two_and_three_hidden {n q : Nat}
    (hq : q ≤ 2 ^ n) (hhidden : 3 ≤ 2 ^ n - q)
    (a : BitMatrix q n) (htwo : level a = 2) : 3 ≤ n := by
  have hlevel : level a ≤ q := by
    unfold level
    simpa using Finset.card_le_card (Finset.subset_univ (rowSupport a))
  have hq2 : 2 ≤ q := by omega
  have hpow5 : 5 ≤ 2 ^ n := by omega
  by_contra hn
  have hnle : n ≤ 2 := by omega
  have hp : 2 ^ n ≤ 2 ^ 2 :=
    Nat.pow_le_pow_right (by omega) hnle
  norm_num at hp
  omega

theorem fullProxySpectrum_padMask_eq_fourier_proxyDensity {n q : Nat}
    (hq : q ≤ 2 ^ n) (hhidden : 3 ≤ 2 ^ n - q)
    (a : BitMatrix q n) :
    fullProxySpectrum n (padMask hq a) =
      XORFourier.fourier (proxyDensity (XorSpace n) q) a := by
  have hn2 : 2 ≤ n := two_le_exponent_of_three_hidden hhidden
  have hN : 2 ≤ 2 ^ n := by omega
  rw [fourier_proxyDensity hN hq]
  by_cases hzero : level a = 0
  · have ha0 : a = 0 := (level_eq_zero_iff a).mp hzero
    subst a
    have hpad : padMask hq (0 : BitMatrix q n) = constantMask 0 :=
      (padMask_eq_constantMask_iff hq (by omega) 0 0).mpr ⟨rfl, rfl⟩
    rw [hpad, fullProxySpectrum_constantMask hn2]
    simp only [if_pos hzero]
    have hnot2 : level (0 : BitMatrix q n) ≠ 2 := by simp [level]
    rw [if_neg hnot2, add_zero, fourier_convolution,
      fourier_injectionDensity_zero hq]
    norm_num
  · rw [if_neg hzero]
    by_cases htwo : level a = 2
    · rw [if_pos htwo, zero_add]
      by_cases heq : supportRowsEqual a
      · obtain ⟨p, alpha, halpha, ha⟩ :=
          exists_pairMask_iff_level_two_supportRowsEqual a |>.mpr ⟨htwo, heq⟩
        have hfull :
            fullProxySpectrum n (padMask hq a) =
              1 / (((2 ^ n - 1 : Nat) : ℝ) ^ 2) := by
          rw [ha, padMask_pairMask]
          have hn3 : 3 ≤ n :=
            three_le_exponent_of_level_two_and_three_hidden hq hhidden a htwo
          simpa using
            (fullProxySpectrum_translatedPairMask hn3 0
              (liftPairIndex hq p) alpha halpha)
        rw [hfull, fourier_convolution]
        rw [fourier_injectionDensity_of_level_eq_two hq a htwo]
        rw [if_pos heq]
        ring
      · have hconst : ¬ IsConstantMode (padMask hq a) := by
          rw [padMask_isConstantMode_iff hq (by omega)]
          intro ha0
          subst a
          simp [level] at htwo
        have hpair : ¬ IsTranslatedPairMode (padMask hq a) := by
          rw [padMask_isTranslatedPairMode_iff hq hhidden]
          exact fun h => heq h.2
        rw [fullProxySpectrum_eq_zero_of_not_low_mode _ hconst hpair]
        rw [fourier_convolution]
        rw [fourier_injectionDensity_of_level_eq_two hq a htwo]
        rw [if_neg heq]
        norm_num
    · rw [if_neg htwo, add_zero]
      have hconst : ¬ IsConstantMode (padMask hq a) := by
        rw [padMask_isConstantMode_iff hq (by omega)]
        intro ha0
        subst a
        exact hzero (by simp [level])
      have hpair : ¬ IsTranslatedPairMode (padMask hq a) := by
        rw [padMask_isTranslatedPairMode_iff hq hhidden]
        exact fun h => htwo h.1
      exact fullProxySpectrum_eq_zero_of_not_low_mode _ hconst hpair

/-- Exact coefficientwise proxy marginal. -/
theorem fourier_prefixMarginal_fullProxyDensity {n q : Nat}
    (hq : q ≤ 2 ^ n) (hhidden : 3 ≤ 2 ^ n - q)
    (a : BitMatrix q n) :
    XORFourier.fourier (prefixMarginal hq (fullProxyDensity n)) a =
      XORFourier.fourier (proxyDensity (XorSpace n) q) a := by
  rw [fourier_prefixMarginal]
  rw [fourier_full_proxy_density_eq_spectrum
    (by have := two_le_exponent_of_three_hidden hhidden; omega)]
  exact fullProxySpectrum_padMask_eq_fourier_proxyDensity hq hhidden a

/-- Exact pointwise marginal identity for the checksum-conditioned full
proxy.  This is the missing `N-q ≥ 3` bridge. -/
theorem prefixMarginal_fullProxyDensity_eq {n q : Nat}
    (hq : q ≤ 2 ^ n) (hhidden : 3 ≤ 2 ^ n - q)
    (y : BitMatrix q n) :
    prefixMarginal hq (fullProxyDensity n) y =
      proxyDensity (XorSpace n) q y := by
  rw [← fourier_inversion (prefixMarginal hq (fullProxyDensity n)) y]
  rw [← fourier_inversion (proxyDensity (XorSpace n) q) y]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fourier_prefixMarginal_fullProxyDensity hq hhidden a]

theorem average_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    average A (fun x => f x - g x) = average A f - average A g := by
  unfold average
  rw [Finset.sum_sub_distrib, sub_div]

theorem prefixMarginal_sub {G : Type*} [Fintype G] {q N : Nat}
    (hq : q ≤ N) (f g : (Fin N → G) → ℝ) (y : Fin q → G) :
    prefixMarginal hq (fun x => f x - g x) y =
      prefixMarginal hq f y - prefixMarginal hq g y := by
  unfold prefixMarginal
  exact average_sub _ _

/-- The full signed residual marginalizes exactly to the visible signed
remainder. -/
theorem prefixMarginal_fullResidualDensity_eq_remainderDensity {n q : Nat}
    (hq : q ≤ 2 ^ n) (hhidden : 3 ≤ 2 ^ n - q)
    (y : BitMatrix q n) :
    prefixMarginal hq (fullResidualDensity n) y =
      remainderDensity (G := XorSpace n) q y := by
  unfold fullResidualDensity remainderDensity
  rw [prefixMarginal_sub]
  rw [prefixMarginal_full_convolution_eq hq]
  rw [prefixMarginal_fullProxyDensity_eq hq hhidden]
  rw [visibleDensityRatioReal_eq_convolution_injectionDensity hq]

/-- Data processing transports the full-deck residual certificate to every
prefix leaving at least three hidden rows. -/
theorem remainderAdvantage_le_fullResidualAdvantage {n q : Nat}
    (hq : q ≤ 2 ^ n) (hhidden : 3 ≤ 2 ^ n - q) :
    remainderAdvantage (G := XorSpace n) q ≤ fullResidualAdvantage n := by
  unfold remainderAdvantage fullResidualAdvantage
  have hfun :
      (fun y : BitMatrix q n =>
        |remainderDensity (G := XorSpace n) q y|) =
      (fun y => |prefixMarginal hq (fullResidualDensity n) y|) := by
    funext y
    rw [prefixMarginal_fullResidualDensity_eq_remainderDensity hq hhidden]
  rw [hfun]
  gcongr
  exact average_abs_prefixMarginal_le hq (fullResidualDensity n)

/-- Closed inherited dense residual bound for every prefix with three hidden
rows. -/
theorem remainderAdvantage_le_seven_div_of_three_hidden {n q : Nat}
    (hn : 63 ≤ n) (hq : q ≤ 2 ^ n) (hhidden : 3 ≤ 2 ^ n - q) :
    remainderAdvantage (G := XorSpace n) q ≤
      7 / (((2 ^ n : Nat) : ℝ)) := by
  exact (remainderAdvantage_le_fullResidualAdvantage hq hhidden).trans
    (fullResidualAdvantage_le_seven_div hn)

/-- Operational form of the complement-regime result: whenever at least
three full-deck rows remain hidden, the exact adaptive advantage differs from
the collision proxy by at most `7 / 2^n`. -/
theorem abs_adaptiveAdvantage_sub_collisionAdvantage_le_seven_div_of_three_hidden
    {n q : Nat} (hn : 63 ≤ n) (hq : q ≤ 2 ^ n)
    (hhidden : 3 ≤ 2 ^ n - q) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionAdvantage (XorSpace n) q| ≤
      7 / (((2 ^ n : Nat) : Real)) := by
  exact
    (abs_advantage_sub_collisionAdvantage_le_remainder
      (G := XorSpace n) q (by simpa using hq)).trans
      (remainderAdvantage_le_seven_div_of_three_hidden hn hq hhidden)

end RandomSystems.SoP.XORComplement
