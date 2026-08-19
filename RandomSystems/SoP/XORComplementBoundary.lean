/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORComplementMarginal
import RandomSystems.SoP.XORCollisionThreshold

/-!
# Exact complement-regime boundary marginals for XOR SoP

This module closes both boundaries omitted by the three-hidden-row marginal
theorem.

* With two hidden rows, their pair can absorb a global Walsh character.  The
  extra centered-checksum density has exact half-`L1` cost
  `1 / (N * (N - 1))`.
* With one hidden row, the extra modes are constant masks with one visible row
  deleted.  Orthogonality bounds their half-`L1` cost by `1 / (2 * (N - 1))`.

Together with the full residual theorem, this proves for every `q < N` that
the exact adaptive XOR-SoP advantage is within

```text
7/N + 1/(2*(N-1)) <= 8/N
```

of the collision proxy.  The module also combines this complement bound with
the sharper sparse Fourier remainder below half the deck and proves that the
explicit collision-threshold test matches the optimal adaptive advantage up
to twice that best certified residual.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORComplement

open RandomSystems
open RandomSystems.CR18
open RandomSystems.Applications.SoP
open RandomSystems.SoP.CollisionProxy
open RandomSystems.SoP.CollisionThreshold
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORBounds

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The first of exactly two hidden rows. -/
def hiddenZero {q N : Nat} (_hq : q ≤ N) (htwo : N - q = 2) : Fin (N - q) :=
  (finCongr htwo).symm 0

/-- The second of exactly two hidden rows. -/
def hiddenOne {q N : Nat} (_hq : q ≤ N) (htwo : N - q = 2) : Fin (N - q) :=
  (finCongr htwo).symm 1

theorem hiddenZero_ne_hiddenOne {q N : Nat} (hq : q ≤ N)
    (htwo : N - q = 2) : hiddenZero hq htwo ≠ hiddenOne hq htwo := by
  intro h
  have := congrArg (finCongr htwo) h
  simp [hiddenZero, hiddenOne] at this

theorem hidden_eq_zero_or_one {q N : Nat} (hq : q ≤ N)
    (htwo : N - q = 2) (j : Fin (N - q)) :
    j = hiddenZero hq htwo ∨ j = hiddenOne hq htwo := by
  let k : Fin 2 := finCongr htwo j
  have hk : k = 0 ∨ k = 1 := by
    have hkval : k.val ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hkval with h | h
    · left
      apply Fin.ext
      simpa using h
    · right
      apply Fin.ext
      simpa using h
  rcases hk with hk | hk
  · left
    apply (finCongr htwo).injective
    simpa [hiddenZero, k] using hk
  · right
    apply (finCongr htwo).injective
    simpa [hiddenOne, k] using hk

/-- The unordered pair consisting of the two hidden full rows. -/
def hiddenPairIndex {q N : Nat} (hq : q ≤ N) (htwo : N - q = 2) :
    PairIndex N :=
  pairIndexOfNe
    (hiddenEmbedding hq (hiddenZero hq htwo))
    (hiddenEmbedding hq (hiddenOne hq htwo))
    (fun h => hiddenZero_ne_hiddenOne hq htwo
      ((hiddenEmbedding hq).injective h))

theorem hiddenPairIndex_endpointSet {q N : Nat} (hq : q ≤ N)
    (htwo : N - q = 2) :
    ({(hiddenPairIndex hq htwo).1.1, (hiddenPairIndex hq htwo).1.2} :
        Finset (Fin N)) =
      {hiddenEmbedding hq (hiddenZero hq htwo),
        hiddenEmbedding hq (hiddenOne hq htwo)} := by
  unfold hiddenPairIndex
  exact pairIndexOfNe_endpointSet _

theorem hiddenEmbedding_mem_hiddenPair {q N : Nat} (hq : q ≤ N)
    (htwo : N - q = 2) (j : Fin (N - q)) :
    hiddenEmbedding hq j ∈
      ({(hiddenPairIndex hq htwo).1.1,
        (hiddenPairIndex hq htwo).1.2} : Finset (Fin N)) := by
  rw [hiddenPairIndex_endpointSet]
  rcases hidden_eq_zero_or_one hq htwo j with rfl | rfl <;> simp

theorem pairMask_hiddenPair_prefix {n q N : Nat} (hq : q ≤ N)
    (htwo : N - q = 2) (alpha : XorSpace n) (i : Fin q) :
    pairMask (hiddenPairIndex hq htwo) alpha (prefixEmbedding hq i) = 0 := by
  rw [pairMask_apply_eq_if_mem, hiddenPairIndex_endpointSet]
  have hne0 : prefixEmbedding hq i ≠
      hiddenEmbedding hq (hiddenZero hq htwo) := by
    intro h
    exact hiddenEmbedding_not_prefix_range hq (hiddenZero hq htwo) ⟨i, h⟩
  have hne1 : prefixEmbedding hq i ≠
      hiddenEmbedding hq (hiddenOne hq htwo) := by
    intro h
    exact hiddenEmbedding_not_prefix_range hq (hiddenOne hq htwo) ⟨i, h⟩
  simp [hne0, hne1]

theorem pairMask_hiddenPair_hidden {n q N : Nat} (hq : q ≤ N)
    (htwo : N - q = 2) (alpha : XorSpace n) (j : Fin (N - q)) :
    pairMask (hiddenPairIndex hq htwo) alpha (hiddenEmbedding hq j) = alpha := by
  rw [pairMask_apply_eq_if_mem]
  rw [if_pos (hiddenEmbedding_mem_hiddenPair hq htwo j)]

/-- A visible constant mode zero-pads to the translated pair whose pair is
exactly the two hidden rows. -/
theorem padMask_constantMask_eq_hidden_translatedPair {n q N : Nat}
    (hq : q ≤ N) (htwo : N - q = 2) (alpha : XorSpace n) :
    padMask hq (constantMask alpha) =
      constantMask alpha + pairMask (hiddenPairIndex hq htwo) alpha := by
  funext i
  have he := (rowSplitEquiv hq).apply_symm_apply i
  generalize hs : (rowSplitEquiv hq).symm i = s at he
  cases s with
  | inl k =>
      rw [← he]
      rw [show padMask hq (constantMask alpha)
          (rowSplitEquiv hq (Sum.inl k)) = alpha by
        simp [padMask, constantMask]]
      rw [Pi.add_apply]
      rw [show constantMask alpha (rowSplitEquiv hq (Sum.inl k)) = alpha by
        rfl]
      change alpha = alpha +
        pairMask (hiddenPairIndex hq htwo) alpha (prefixEmbedding hq k)
      rw [pairMask_hiddenPair_prefix]
      simp
  | inr j =>
      rw [← he]
      rw [show padMask hq (constantMask alpha)
          (rowSplitEquiv hq (Sum.inr j)) = 0 by
        simp [padMask]]
      rw [Pi.add_apply]
      rw [show constantMask alpha (rowSplitEquiv hq (Sum.inr j)) = alpha by
        rfl]
      change 0 = alpha +
        pairMask (hiddenPairIndex hq htwo) alpha (hiddenEmbedding hq j)
      rw [pairMask_hiddenPair_hidden]
      exact (RandomSystems.SoP.XORCore.xorSpace_add_self_eq_zero alpha).symm

/-- A visible Walsh mask is a nontrivial checksum character. -/
def IsNonzeroConstantMode {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∃ alpha : XorSpace n, alpha ≠ 0 ∧ a = constantMask alpha

theorem pair_eq_hiddenPair_of_all_hidden_mem {q N : Nat} (hq : q ≤ N)
    (htwo : N - q = 2) (p : PairIndex N)
    (hall : ∀ j : Fin (N - q),
      hiddenEmbedding hq j ∈ ({p.1.1, p.1.2} : Finset (Fin N))) :
    p = hiddenPairIndex hq htwo := by
  let H : Finset (Fin N) :=
    {hiddenEmbedding hq (hiddenZero hq htwo),
      hiddenEmbedding hq (hiddenOne hq htwo)}
  let P : Finset (Fin N) := {p.1.1, p.1.2}
  have hsub : H ⊆ P := by
    intro i hi
    simp only [H, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hall (hiddenZero hq htwo)
    · exact hall (hiddenOne hq htwo)
  have hcardH : H.card = 2 := by
    have hne : hiddenEmbedding hq (hiddenZero hq htwo) ≠
        hiddenEmbedding hq (hiddenOne hq htwo) := by
      exact fun h => hiddenZero_ne_hiddenOne hq htwo
        ((hiddenEmbedding hq).injective h)
    simp [H, hne]
  have hcardP : P.card = 2 := by
    simp [P, ne_of_lt p.2]
  have hHP : H = P :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardP, hcardH])
  apply pairIndex_eq_of_endpointSet_eq
  rw [hiddenPairIndex_endpointSet]
  exact hHP.symm

/-- At the two-hidden boundary there is exactly one additional translated
pair family: the hidden pair turns into a nonzero visible checksum mode. -/
theorem padMask_isTranslatedPairMode_iff_two_hidden {n q N : Nat}
    (hq : q ≤ N) (htwo : N - q = 2) (a : BitMatrix q n) :
    IsTranslatedPairMode (padMask hq a) ↔
      (level a = 2 ∧ supportRowsEqual a) ∨ IsNonzeroConstantMode a := by
  constructor
  · rintro ⟨⟨beta, ⟨p, ⟨alpha, halpha⟩⟩⟩, hmode⟩
    by_cases hout : ∃ j : Fin (N - q),
        hiddenEmbedding hq j ≠ p.1.1 ∧ hiddenEmbedding hq j ≠ p.1.2
    · obtain ⟨j, hjl, hjr⟩ := hout
      have hbeta_eval := congrFun hmode (hiddenEmbedding hq j)
      have hbeta : beta = 0 := by
        simpa [translatedPairParameterToMask, constantMask, pairMask,
          hjl, hjr] using hbeta_eval.symm
      subst beta
      have hpair : padMask hq a = pairMask p alpha := by
        simpa [translatedPairParameterToMask] using hmode
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
      left
      exact exists_pairMask_iff_level_two_supportRowsEqual a |>.mp
        ⟨pv, alpha, halpha, hvis⟩
    · have hall : ∀ j : Fin (N - q),
          hiddenEmbedding hq j ∈ ({p.1.1, p.1.2} : Finset (Fin N)) := by
        intro j
        have hj : ¬ (hiddenEmbedding hq j ≠ p.1.1 ∧
            hiddenEmbedding hq j ≠ p.1.2) := by
          intro h
          exact hout ⟨j, h⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hp : p = hiddenPairIndex hq htwo :=
        pair_eq_hiddenPair_of_all_hidden_mem hq htwo p hall
      subst p
      have hsum := congrFun hmode
        (hiddenEmbedding hq (hiddenZero hq htwo))
      have hba : beta = alpha := by
        have hzero : padMask hq a
            (hiddenEmbedding hq (hiddenZero hq htwo)) = 0 :=
          padMask_hidden hq a _
        rw [hzero] at hsum
        simp only [translatedPairParameterToMask, Pi.add_apply,
          constantMask, pairMask_hiddenPair_hidden] at hsum
        exact RandomSystems.SoP.XORCore.xorSpace_add_eq_zero_iff_eq beta alpha |>.mp
          hsum.symm
      subst beta
      right
      refine ⟨alpha, halpha, ?_⟩
      funext i
      have hv := congrFun hmode (prefixEmbedding hq i)
      have hleft : padMask hq a (prefixEmbedding hq i) = a i := by
        simp [padMask, prefixEmbedding]
      rw [hleft] at hv
      simpa [translatedPairParameterToMask, constantMask,
        pairMask_hiddenPair_prefix] using hv
  · rintro (hpair | hconst)
    · obtain ⟨p, alpha, halpha, ha⟩ :=
        exists_pairMask_iff_level_two_supportRowsEqual a |>.mpr hpair
      refine ⟨⟨0, ⟨liftPairIndex hq p, ⟨alpha, halpha⟩⟩⟩, ?_⟩
      rw [ha, padMask_pairMask]
      simp [translatedPairParameterToMask]
    · obtain ⟨alpha, halpha, ha⟩ := hconst
      refine ⟨⟨alpha, ⟨hiddenPairIndex hq htwo,
        ⟨alpha, halpha⟩⟩⟩, ?_⟩
      rw [ha, padMask_constantMask_eq_hidden_translatedPair]
      rfl

/-- The exact extra density contributed by the hidden-pair orbit. -/
def twoHiddenProxyCorrection (n q : Nat) (y : BitMatrix q n) : ℝ :=
  (1 / (((2 ^ n - 1 : Nat) : ℝ) ^ 2)) *
    (checksumDensity n q y - 1)

theorem sum_nonzero_constant_walsh_eq_checksum_sub_one {n q : Nat}
    (y : BitMatrix q n) :
    (∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
        (fun alpha => alpha ≠ 0), walsh (constantMask alpha) y) =
      checksumDensity n q y - 1 := by
  have hpartition := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (XorSpace n)))
    (p := fun alpha : XorSpace n => alpha ≠ 0)
    (f := fun alpha => walsh (constantMask alpha) y)
  have hzero :
      (∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
        (fun alpha => ¬ alpha ≠ 0), walsh (constantMask alpha) y) = 1 := by
    have hfilter : (Finset.univ : Finset (XorSpace n)).filter
        (fun alpha => ¬ alpha ≠ 0) = {0} := by
      ext alpha
      simp
    rw [hfilter]
    simp
  rw [hzero] at hpartition
  rw [checksum_density_eq_sum_walsh]
  linarith

theorem twoHiddenProxyCorrection_eq_walsh_sum {n q : Nat}
    (y : BitMatrix q n) :
    twoHiddenProxyCorrection n q y =
      ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
          (fun alpha => alpha ≠ 0),
        (1 / (((2 ^ n - 1 : Nat) : ℝ) ^ 2)) *
          walsh (constantMask alpha) y := by
  unfold twoHiddenProxyCorrection
  rw [← sum_nonzero_constant_walsh_eq_checksum_sub_one]
  rw [Finset.mul_sum]

/-- The correction has one coefficient on every nonzero checksum mode and
zero elsewhere. -/
theorem fourier_twoHiddenProxyCorrection {n q : Nat} (hq : 0 < q)
    (a : BitMatrix q n) :
    XORFourier.fourier (twoHiddenProxyCorrection n q) a =
      if IsNonzeroConstantMode a then
        1 / (((2 ^ n - 1 : Nat) : ℝ) ^ 2)
      else 0 := by
  unfold XORFourier.fourier
  rw [show (fun y : BitMatrix q n =>
      twoHiddenProxyCorrection n q y * walsh a y) =
      (fun y =>
        ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
            (fun alpha => alpha ≠ 0),
          (1 / (((2 ^ n - 1 : Nat) : ℝ) ^ 2)) *
            (walsh (constantMask alpha) y * walsh a y)) by
    funext y
    rw [twoHiddenProxyCorrection_eq_walsh_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro alpha _halpha
    ring]
  rw [average_finset_sum]
  simp_rw [average_const_mul, average_walsh_mul_walsh]
  by_cases ha : IsNonzeroConstantMode a
  · obtain ⟨alpha, halpha, haeq⟩ := ha
    rw [if_pos ⟨alpha, halpha, haeq⟩]
    have hinj := constantMask_injective (n := n) hq
    simp_rw [show ∀ beta : XorSpace n,
        constantMask beta = a ↔ beta = alpha by
      intro beta
      rw [haeq]
      exact hinj.eq_iff]
    simp [halpha]
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro alpha halphaMem
    have halpha : alpha ≠ 0 := (Finset.mem_filter.mp halphaMem).2
    rw [if_neg]
    · ring
    · intro heq
      exact ha ⟨alpha, halpha, heq.symm⟩

theorem not_nonzeroConstantMode_zero {n q : Nat} (hq : 0 < q) :
    ¬ IsNonzeroConstantMode (0 : BitMatrix q n) := by
  rintro ⟨alpha, halpha, ha⟩
  have hz : constantMask (q := q) alpha = 0 := ha.symm
  exact halpha ((constant_mask_eq_zero_iff hq alpha).mp hz)

theorem not_nonzeroConstantMode_of_level_two {n q : Nat} (hq : 3 ≤ q)
    (a : BitMatrix q n) (htwo : level a = 2) :
    ¬ IsNonzeroConstantMode a := by
  rintro ⟨alpha, halpha, ha⟩
  rw [ha, level_constant_mask alpha halpha] at htwo
  omega

/-- Coefficientwise form of the exact two-hidden-row marginal. -/
theorem fullProxySpectrum_padMask_eq_proxy_add_twoHiddenCorrection
    {n q : Nat} (hn : 3 ≤ n) (hq : q ≤ 2 ^ n)
    (htail : 2 ^ n - q = 2) (a : BitMatrix q n) :
    fullProxySpectrum n (padMask hq a) =
      XORFourier.fourier (proxyDensity (XorSpace n) q) a +
        XORFourier.fourier (twoHiddenProxyCorrection n q) a := by
  have hN : 2 ≤ 2 ^ n := by
    calc
      2 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hN8 : 8 ≤ 2 ^ n := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hq3 : 3 ≤ q := by omega
  have hq0 : 0 < q := by omega
  rw [fourier_proxyDensity hN hq, fourier_twoHiddenProxyCorrection hq0]
  by_cases hzero : level a = 0
  · have ha0 : a = 0 := (level_eq_zero_iff a).mp hzero
    subst a
    have hpad : padMask hq (0 : BitMatrix q n) = constantMask 0 :=
      (padMask_eq_constantMask_iff hq (by omega) 0 0).mpr ⟨rfl, rfl⟩
    rw [hpad, fullProxySpectrum_constantMask (by omega)]
    simp only [if_pos hzero]
    have hnot2 : level (0 : BitMatrix q n) ≠ 2 := by simp [level]
    rw [if_neg hnot2, if_neg (not_nonzeroConstantMode_zero hq0),
      add_zero, add_zero, fourier_convolution,
      fourier_injectionDensity_zero hq]
    norm_num
  · rw [if_neg hzero]
    by_cases htwo : level a = 2
    · rw [if_pos htwo, zero_add]
      have hnconst : ¬ IsNonzeroConstantMode a :=
        not_nonzeroConstantMode_of_level_two hq3 a htwo
      rw [if_neg hnconst, add_zero]
      by_cases heq : supportRowsEqual a
      · obtain ⟨p, alpha, halpha, ha⟩ :=
          exists_pairMask_iff_level_two_supportRowsEqual a |>.mpr ⟨htwo, heq⟩
        have hfull :
            fullProxySpectrum n (padMask hq a) =
              1 / (((2 ^ n - 1 : Nat) : ℝ) ^ 2) := by
          rw [ha, padMask_pairMask]
          simpa using
            (fullProxySpectrum_translatedPairMask hn 0
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
          rw [padMask_isTranslatedPairMode_iff_two_hidden hq htail]
          push Not
          exact ⟨fun _hlevel => heq, hnconst⟩
        rw [fullProxySpectrum_eq_zero_of_not_low_mode _ hconst hpair]
        rw [fourier_convolution]
        rw [fourier_injectionDensity_of_level_eq_two hq a htwo]
        rw [if_neg heq]
        norm_num
    · rw [if_neg htwo, add_zero]
      by_cases hnconst : IsNonzeroConstantMode a
      · rw [if_pos hnconst, zero_add]
        obtain ⟨alpha, halpha, ha⟩ := hnconst
        have hfull :
            fullProxySpectrum n (padMask hq a) =
              1 / (((2 ^ n - 1 : Nat) : ℝ) ^ 2) := by
          rw [ha, padMask_constantMask_eq_hidden_translatedPair hq htail]
          simpa using
            (fullProxySpectrum_translatedPairMask hn alpha
              (hiddenPairIndex hq htail) alpha halpha)
        exact hfull
      · rw [if_neg hnconst, add_zero]
        have hconst : ¬ IsConstantMode (padMask hq a) := by
          rw [padMask_isConstantMode_iff hq (by omega)]
          intro ha0
          subst a
          exact hzero (by simp [level])
        have hpair : ¬ IsTranslatedPairMode (padMask hq a) := by
          rw [padMask_isTranslatedPairMode_iff_two_hidden hq htail]
          push Not
          exact ⟨fun hlevel => (htwo hlevel).elim, hnconst⟩
        exact fullProxySpectrum_eq_zero_of_not_low_mode _ hconst hpair

/-- Exact coefficientwise two-hidden-row marginal. -/
theorem fourier_prefixMarginal_fullProxyDensity_two_hidden {n q : Nat}
    (hn : 3 ≤ n) (hq : q ≤ 2 ^ n) (htail : 2 ^ n - q = 2)
    (a : BitMatrix q n) :
    XORFourier.fourier (prefixMarginal hq (fullProxyDensity n)) a =
      XORFourier.fourier
        (fun y => proxyDensity (XorSpace n) q y +
          twoHiddenProxyCorrection n q y) a := by
  rw [fourier_prefixMarginal]
  rw [fourier_full_proxy_density_eq_spectrum (by omega)]
  rw [fourier_add_density]
  exact fullProxySpectrum_padMask_eq_proxy_add_twoHiddenCorrection
    hn hq htail a

/-- Pointwise boundary formula.  Relative to the ordinary collision proxy,
the only correction is the centered visible checksum density. -/
theorem prefixMarginal_fullProxyDensity_eq_proxy_add_twoHiddenCorrection
    {n q : Nat} (hn : 3 ≤ n) (hq : q ≤ 2 ^ n)
    (htail : 2 ^ n - q = 2) (y : BitMatrix q n) :
    prefixMarginal hq (fullProxyDensity n) y =
      proxyDensity (XorSpace n) q y + twoHiddenProxyCorrection n q y := by
  rw [← fourier_inversion (prefixMarginal hq (fullProxyDensity n)) y]
  rw [← fourier_inversion
    (fun y => proxyDensity (XorSpace n) q y +
      twoHiddenProxyCorrection n q y) y]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fourier_prefixMarginal_fullProxyDensity_two_hidden hn hq htail a]

/-- Half of the uniform `L1` norm of the two-hidden checksum correction. -/
def twoHiddenProxyCorrectionAdvantage (n q : Nat) : ℝ :=
  (1 / 2 : ℝ) *
    average (BitMatrix q n) (fun y => |twoHiddenProxyCorrection n q y|)

/-- The checksum correction costs exactly `1 / (N(N-1))` in half-`L1`. -/
theorem twoHiddenProxyCorrectionAdvantage_eq {n q : Nat}
    (hn : 1 ≤ n) (hq : 0 < q) :
    twoHiddenProxyCorrectionAdvantage n q =
      1 / (((2 ^ n : Nat) : ℝ) * ((2 ^ n - 1 : Nat) : ℝ)) := by
  let N : Nat := 2 ^ n
  let d : ℝ := 1 / (((N - 1 : Nat) : ℝ) ^ 2)
  have hn0 : n ≠ 0 := by omega
  have hN : 2 ≤ N := by
    dsimp [N]
    exact Nat.one_lt_two_pow hn0
  have hNR : (N : ℝ) ≠ 0 := by positivity
  have hNm1Nat : N - 1 ≠ 0 := by omega
  have hNm1 : (((N - 1 : Nat) : ℝ)) ≠ 0 := by exact_mod_cast hNm1Nat
  have hd : 0 ≤ d := by dsimp [d]; positivity
  unfold twoHiddenProxyCorrectionAdvantage twoHiddenProxyCorrection
  change (1 / 2 : ℝ) *
      average (BitMatrix q n)
        (fun y => |d * (checksumDensity n q y - 1)|) =
    1 / ((N : ℝ) * ((N - 1 : Nat) : ℝ))
  simp_rw [abs_mul, abs_of_nonneg hd]
  rw [average_const_mul]
  rw [show average (BitMatrix q n)
      (fun y => |checksumDensity n q y - 1|) =
      2 * checksumAdvantage n q by
    unfold checksumAdvantage
    ring]
  rw [checksum_advantage_eq hn hq]
  dsimp [d]
  change (1 / 2 : ℝ) *
      (1 / (((N - 1 : Nat) : ℝ) ^ 2) *
        (2 * (1 - 1 / (N : ℝ)))) =
    1 / ((N : ℝ) * ((N - 1 : Nat) : ℝ))
  rw [Nat.cast_sub (by omega : 1 ≤ N)] at hNm1 ⊢
  norm_num only [Nat.cast_one]
  field_simp [hNR, hNm1]

/-- The full residual marginal is the ordinary visible remainder minus the
explicit checksum correction. -/
theorem prefixMarginal_fullResidualDensity_eq_remainder_sub_twoHiddenCorrection
    {n q : Nat} (hn : 3 ≤ n) (hq : q ≤ 2 ^ n)
    (htail : 2 ^ n - q = 2) (y : BitMatrix q n) :
    prefixMarginal hq (fullResidualDensity n) y =
      remainderDensity (G := XorSpace n) q y -
        twoHiddenProxyCorrection n q y := by
  unfold fullResidualDensity remainderDensity
  rw [prefixMarginal_sub]
  rw [prefixMarginal_full_convolution_eq hq]
  rw [prefixMarginal_fullProxyDensity_eq_proxy_add_twoHiddenCorrection
    hn hq htail]
  rw [visibleDensityRatioReal_eq_convolution_injectionDensity hq]
  ring

theorem average_abs_add_le {A : Type*} [Fintype A] [Nonempty A]
    (f g : A → ℝ) :
    average A (fun x => |f x + g x|) ≤
      average A (fun x => |f x|) + average A (fun x => |g x|) := by
  calc
    average A (fun x => |f x + g x|) ≤
        average A (fun x => |f x| + |g x|) := by
      exact CollisionProxy.uniformAverage_mono fun x => abs_add_le (f x) (g x)
    _ = average A (fun x => |f x|) + average A (fun x => |g x|) :=
      average_add _ _

/-- The visible remainder is bounded by the full residual plus the exact
two-hidden checksum correction. -/
theorem remainderAdvantage_le_fullResidual_add_twoHiddenCorrection
    {n q : Nat} (hn : 3 ≤ n) (hq : q ≤ 2 ^ n)
    (htail : 2 ^ n - q = 2) :
    remainderAdvantage (G := XorSpace n) q ≤
      fullResidualAdvantage n + twoHiddenProxyCorrectionAdvantage n q := by
  unfold remainderAdvantage fullResidualAdvantage
  have hfun :
      (fun y : BitMatrix q n => remainderDensity (G := XorSpace n) q y) =
      (fun y => prefixMarginal hq (fullResidualDensity n) y +
        twoHiddenProxyCorrection n q y) := by
    funext y
    have h := prefixMarginal_fullResidualDensity_eq_remainder_sub_twoHiddenCorrection
      hn hq htail y
    linarith
  simp_rw [show ∀ y : BitMatrix q n,
      remainderDensity (G := XorSpace n) q y =
        prefixMarginal hq (fullResidualDensity n) y +
          twoHiddenProxyCorrection n q y by
    intro y
    exact congrFun hfun y]
  calc
    (1 / 2 : ℝ) * average (BitMatrix q n)
        (fun y => |prefixMarginal hq (fullResidualDensity n) y +
          twoHiddenProxyCorrection n q y|) ≤
      (1 / 2 : ℝ) *
        (average (BitMatrix q n)
            (fun y => |prefixMarginal hq (fullResidualDensity n) y|) +
          average (BitMatrix q n)
            (fun y => |twoHiddenProxyCorrection n q y|)) := by
        gcongr
        exact average_abs_add_le _ _
    _ = (1 / 2 : ℝ) * average (BitMatrix q n)
          (fun y => |prefixMarginal hq (fullResidualDensity n) y|) +
        twoHiddenProxyCorrectionAdvantage n q := by
      unfold twoHiddenProxyCorrectionAdvantage
      ring
    _ ≤ (1 / 2 : ℝ) * average (BitMatrix (2 ^ n) n)
          (fun y => |fullResidualDensity n y|) +
        twoHiddenProxyCorrectionAdvantage n q := by
      gcongr
      exact average_abs_prefixMarginal_le hq (fullResidualDensity n)

/-- Closed two-hidden boundary inherited from the full residual estimate. -/
theorem remainderAdvantage_le_seven_div_add_twoHidden_exact {n q : Nat}
    (hn : 63 ≤ n) (hq : q ≤ 2 ^ n) (htail : 2 ^ n - q = 2) :
    remainderAdvantage (G := XorSpace n) q ≤
      7 / (((2 ^ n : Nat) : ℝ)) +
        1 / (((2 ^ n : Nat) : ℝ) * ((2 ^ n - 1 : Nat) : ℝ)) := by
  have hq0 : 0 < q := by
    have hN8 : 8 ≤ 2 ^ n := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  calc
    remainderAdvantage (G := XorSpace n) q ≤
        fullResidualAdvantage n + twoHiddenProxyCorrectionAdvantage n q :=
      remainderAdvantage_le_fullResidual_add_twoHiddenCorrection
        (by omega) hq htail
    _ ≤ 7 / (((2 ^ n : Nat) : ℝ)) +
        twoHiddenProxyCorrectionAdvantage n q := by
      gcongr
      exact fullResidualAdvantage_le_seven_div hn
    _ = 7 / (((2 ^ n : Nat) : ℝ)) +
        1 / (((2 ^ n : Nat) : ℝ) * ((2 ^ n - 1 : Nat) : ℝ)) := by
      rw [twoHiddenProxyCorrectionAdvantage_eq (by omega) hq0]

/-- Operational two-hidden-row comparison between the exact adaptive XOR-SoP
advantage and the collision proxy. -/
theorem abs_adaptiveAdvantage_sub_collisionAdvantage_le_seven_div_add_twoHidden_exact
    {n q : Nat} (hn : 63 ≤ n) (hq : q ≤ 2 ^ n)
    (htail : 2 ^ n - q = 2) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionAdvantage (XorSpace n) q| ≤
      7 / (((2 ^ n : Nat) : Real)) +
        1 / (((2 ^ n : Nat) : Real) * ((2 ^ n - 1 : Nat) : Real)) := by
  exact
    (abs_advantage_sub_collisionAdvantage_le_remainder
      (G := XorSpace n) q (by simpa using hq)).trans
      (remainderAdvantage_le_seven_div_add_twoHidden_exact hn hq htail)

/-- A constant mask with one visible row deleted. -/
def coSingletonMask {n q : Nat} (i : Fin q) (alpha : XorSpace n) :
    BitMatrix q n :=
  fun j => if j = i then 0 else alpha

@[simp]
theorem coSingletonMask_self {n q : Nat} (i : Fin q)
    (alpha : XorSpace n) :
    coSingletonMask i alpha i = 0 := by
  simp [coSingletonMask]

theorem coSingletonMask_ne {n q : Nat} (i j : Fin q)
    (alpha : XorSpace n) (hji : j ≠ i) :
    coSingletonMask i alpha j = alpha := by
  simp [coSingletonMask, hji]

def IsCoSingletonMode {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∃ i : Fin q, ∃ alpha : XorSpace n,
    alpha ≠ 0 ∧ a = coSingletonMask i alpha

/-- The unique hidden row when exactly one row is omitted. -/
def uniqueHiddenFin {q N : Nat} (hone : N - q = 1) : Fin (N - q) :=
  ⟨0, by omega⟩

def uniqueHiddenRow {q N : Nat} (hq : q ≤ N) (hone : N - q = 1) :
    Fin N :=
  hiddenEmbedding hq (uniqueHiddenFin hone)

theorem hiddenEmbedding_eq_uniqueHiddenRow {q N : Nat} (hq : q ≤ N)
    (hone : N - q = 1) (j : Fin (N - q)) :
    hiddenEmbedding hq j = uniqueHiddenRow hq hone := by
  congr 1
  apply Fin.ext
  omega

theorem uniqueHiddenRow_not_prefix_range {q N : Nat} (hq : q ≤ N)
    (hone : N - q = 1) :
    uniqueHiddenRow hq hone ∉ Set.range (prefixEmbedding hq) := by
  exact hiddenEmbedding_not_prefix_range hq (uniqueHiddenFin hone)

/-- Pair the unique hidden row with one visible row. -/
def hiddenVisiblePair {q N : Nat} (hq : q ≤ N) (hone : N - q = 1)
    (i : Fin q) : PairIndex N :=
  pairIndexOfNe (uniqueHiddenRow hq hone) (prefixEmbedding hq i)
    (fun h => uniqueHiddenRow_not_prefix_range hq hone ⟨i, h.symm⟩)

theorem hiddenVisiblePair_endpointSet {q N : Nat} (hq : q ≤ N)
    (hone : N - q = 1) (i : Fin q) :
    ({(hiddenVisiblePair hq hone i).1.1,
        (hiddenVisiblePair hq hone i).1.2} : Finset (Fin N)) =
      {uniqueHiddenRow hq hone, prefixEmbedding hq i} := by
  unfold hiddenVisiblePair
  exact pairIndexOfNe_endpointSet _

/-- Padding a co-singleton mode produces precisely the translated pair which
joins its deleted visible row to the unique hidden row. -/
theorem padMask_coSingletonMask {n q N : Nat} (hq : q ≤ N)
    (hone : N - q = 1) (i : Fin q) (alpha : XorSpace n) :
    padMask hq (coSingletonMask i alpha) =
      constantMask alpha + pairMask (hiddenVisiblePair hq hone i) alpha := by
  funext r
  rcases exists_prefixEmbedding_or_hiddenEmbedding hq r with hr | hr
  · obtain ⟨k, rfl⟩ := hr
    rw [show padMask hq (coSingletonMask i alpha) (prefixEmbedding hq k) =
        coSingletonMask i alpha k by
      change joinTape hq (coSingletonMask i alpha) 0
        (rowSplitEquiv hq (Sum.inl k)) = _
      simp]
    change coSingletonMask i alpha k =
      alpha + pairMask (hiddenVisiblePair hq hone i) alpha
        (prefixEmbedding hq k)
    rw [pairMask_apply_eq_if_mem, hiddenVisiblePair_endpointSet]
    have hnotHidden : prefixEmbedding hq k ≠ uniqueHiddenRow hq hone := by
      intro h
      exact uniqueHiddenRow_not_prefix_range hq hone ⟨k, h⟩
    by_cases hki : k = i
    · subst k
      simp [coSingletonMask, hnotHidden]
    · have hprefix : prefixEmbedding hq k ≠ prefixEmbedding hq i :=
        fun h => hki ((prefixEmbedding hq).injective h)
      simp [coSingletonMask, hki, hnotHidden, hprefix]
  · obtain ⟨j, rfl⟩ := hr
    rw [padMask_hidden]
    change 0 = alpha +
      pairMask (hiddenVisiblePair hq hone i) alpha (hiddenEmbedding hq j)
    rw [hiddenEmbedding_eq_uniqueHiddenRow hq hone j]
    rw [pairMask_apply_eq_if_mem, hiddenVisiblePair_endpointSet]
    simp

theorem translatedPair_of_coSingleton {n q N : Nat} (hq : q ≤ N)
    (hone : N - q = 1) (i : Fin q) (alpha : XorSpace n)
    (halpha : alpha ≠ 0) :
    IsTranslatedPairMode (padMask hq (coSingletonMask i alpha)) := by
  refine ⟨⟨alpha, ⟨hiddenVisiblePair hq hone i,
    ⟨alpha, halpha⟩⟩⟩, ?_⟩
  exact padMask_coSingletonMask hq hone i alpha

/-- If the unique hidden row is not an endpoint, both pair endpoints are
visible. -/
theorem pair_endpoints_visible_of_uniqueHidden_outside {q N : Nat}
    (hq : q ≤ N) (hone : N - q = 1) (p : PairIndex N)
    (hl : uniqueHiddenRow hq hone ≠ p.1.1)
    (hr : uniqueHiddenRow hq hone ≠ p.1.2) :
    (∃ il : Fin q, prefixEmbedding hq il = p.1.1) ∧
      ∃ ir : Fin q, prefixEmbedding hq ir = p.1.2 := by
  constructor
  · rcases exists_prefixEmbedding_or_hiddenEmbedding hq p.1.1 with hv | hh
    · exact hv
    · obtain ⟨j, hj⟩ := hh
      exfalso
      apply hl
      rw [← hj]
      exact (hiddenEmbedding_eq_uniqueHiddenRow hq hone j).symm
  · rcases exists_prefixEmbedding_or_hiddenEmbedding hq p.1.2 with hv | hh
    · exact hv
    · obtain ⟨j, hj⟩ := hh
      exfalso
      apply hr
      rw [← hj]
      exact (hiddenEmbedding_eq_uniqueHiddenRow hq hone j).symm

/-- A nonzero full pair mask which is zero-padded must come from a visible
pair. -/
theorem visible_pair_of_padMask_eq_pairMask {n q N : Nat} (hq : q ≤ N)
    (a : BitMatrix q n) (p : PairIndex N) (alpha : XorSpace n)
    (halpha : alpha ≠ 0) (hpair : padMask hq a = pairMask p alpha) :
    ∃ pv : PairIndex q, a = pairMask pv alpha := by
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
  refine ⟨pv, ?_⟩
  have hr := congrArg (restrictMask (prefixEmbedding hq)) hpadded
  simpa using hr

theorem coSingleton_of_hidden_left {n q N : Nat} (hq : q ≤ N)
    (hone : N - q = 1) (a : BitMatrix q n) (beta alpha : XorSpace n)
    (p : PairIndex N) (halpha : alpha ≠ 0)
    (hleft : uniqueHiddenRow hq hone = p.1.1)
    (hmode : padMask hq a = constantMask beta + pairMask p alpha) :
    IsCoSingletonMode a := by
  have heval := congrFun hmode (uniqueHiddenRow hq hone)
  have hbeta : beta = alpha := by
    change padMask hq a (uniqueHiddenRow hq hone) =
      beta + pairMask p alpha (uniqueHiddenRow hq hone) at heval
    have hpad : padMask hq a (uniqueHiddenRow hq hone) = 0 := by
      unfold uniqueHiddenRow
      simp
    rw [hpad, hleft, pairMask_left] at heval
    exact (xorSpace_add_eq_zero_iff_eq beta alpha).mp heval.symm
  obtain ⟨i, hi⟩ : ∃ i : Fin q, prefixEmbedding hq i = p.1.2 := by
    rcases exists_prefixEmbedding_or_hiddenEmbedding hq p.1.2 with hv | hh
    · exact hv
    · obtain ⟨j, hj⟩ := hh
      exfalso
      apply ne_of_lt p.2
      exact hleft.symm.trans
        ((hiddenEmbedding_eq_uniqueHiddenRow hq hone j).symm.trans hj)
  refine ⟨i, alpha, halpha, ?_⟩
  funext k
  have hv := congrFun hmode (prefixEmbedding hq k)
  rw [show padMask hq a (prefixEmbedding hq k) = a k by
    change joinTape hq a 0 (rowSplitEquiv hq (Sum.inl k)) = _
    simp] at hv
  change a k = beta + pairMask p alpha (prefixEmbedding hq k) at hv
  rw [hbeta] at hv
  rw [pairMask_apply_eq_if_mem] at hv
  have hend : ({p.1.1, p.1.2} : Finset (Fin N)) =
      {uniqueHiddenRow hq hone, prefixEmbedding hq i} := by
    rw [hleft, hi]
  rw [hend] at hv
  have hnotHidden : prefixEmbedding hq k ≠ uniqueHiddenRow hq hone := by
    intro h
    exact uniqueHiddenRow_not_prefix_range hq hone ⟨k, h⟩
  by_cases hki : k = i
  · subst k
    simpa [coSingletonMask, hnotHidden] using hv
  · have hprefix : prefixEmbedding hq k ≠ prefixEmbedding hq i :=
      fun h => hki ((prefixEmbedding hq).injective h)
    simpa [coSingletonMask, hki, hnotHidden, hprefix] using hv

theorem coSingleton_of_hidden_right {n q N : Nat} (hq : q ≤ N)
    (hone : N - q = 1) (a : BitMatrix q n) (beta alpha : XorSpace n)
    (p : PairIndex N) (halpha : alpha ≠ 0)
    (hright : uniqueHiddenRow hq hone = p.1.2)
    (hmode : padMask hq a = constantMask beta + pairMask p alpha) :
    IsCoSingletonMode a := by
  have heval := congrFun hmode (uniqueHiddenRow hq hone)
  have hbeta : beta = alpha := by
    change padMask hq a (uniqueHiddenRow hq hone) =
      beta + pairMask p alpha (uniqueHiddenRow hq hone) at heval
    have hpad : padMask hq a (uniqueHiddenRow hq hone) = 0 := by
      unfold uniqueHiddenRow
      simp
    rw [hpad, hright, pairMask_right] at heval
    exact (xorSpace_add_eq_zero_iff_eq beta alpha).mp heval.symm
  obtain ⟨i, hi⟩ : ∃ i : Fin q, prefixEmbedding hq i = p.1.1 := by
    rcases exists_prefixEmbedding_or_hiddenEmbedding hq p.1.1 with hv | hh
    · exact hv
    · obtain ⟨j, hj⟩ := hh
      exfalso
      apply ne_of_lt p.2
      exact (hj.symm.trans
        (hiddenEmbedding_eq_uniqueHiddenRow hq hone j)).trans hright
  refine ⟨i, alpha, halpha, ?_⟩
  funext k
  have hv := congrFun hmode (prefixEmbedding hq k)
  rw [show padMask hq a (prefixEmbedding hq k) = a k by
    change joinTape hq a 0 (rowSplitEquiv hq (Sum.inl k)) = _
    simp] at hv
  change a k = beta + pairMask p alpha (prefixEmbedding hq k) at hv
  rw [hbeta] at hv
  rw [pairMask_apply_eq_if_mem] at hv
  have hend : ({p.1.1, p.1.2} : Finset (Fin N)) =
      {uniqueHiddenRow hq hone, prefixEmbedding hq i} := by
    rw [hright, hi]
    simp [Finset.pair_comm]
  rw [hend] at hv
  have hnotHidden : prefixEmbedding hq k ≠ uniqueHiddenRow hq hone := by
    intro h
    exact uniqueHiddenRow_not_prefix_range hq hone ⟨k, h⟩
  by_cases hki : k = i
  · subst k
    simpa [coSingletonMask, hnotHidden] using hv
  · have hprefix : prefixEmbedding hq k ≠ prefixEmbedding hq i :=
      fun h => hki ((prefixEmbedding hq).injective h)
    simpa [coSingletonMask, hki, hnotHidden, hprefix] using hv

/-- Exact one-hidden translated-pair classification. -/
theorem padMask_isTranslatedPairMode_iff_one_hidden {n q N : Nat}
    (hq : q ≤ N) (hone : N - q = 1) (a : BitMatrix q n) :
    IsTranslatedPairMode (padMask hq a) ↔
      (level a = 2 ∧ supportRowsEqual a) ∨ IsCoSingletonMode a := by
  constructor
  · rintro ⟨⟨beta, ⟨p, ⟨alpha, halpha⟩⟩⟩, hmode⟩
    by_cases hl : uniqueHiddenRow hq hone = p.1.1
    · exact Or.inr
        (coSingleton_of_hidden_left hq hone a beta alpha p halpha hl hmode)
    · by_cases hr : uniqueHiddenRow hq hone = p.1.2
      · exact Or.inr
          (coSingleton_of_hidden_right hq hone a beta alpha p halpha hr hmode)
      · have heval := congrFun hmode (uniqueHiddenRow hq hone)
        have hbeta : beta = 0 := by
          change padMask hq a (uniqueHiddenRow hq hone) =
            beta + pairMask p alpha (uniqueHiddenRow hq hone) at heval
          have hpad : padMask hq a (uniqueHiddenRow hq hone) = 0 := by
            unfold uniqueHiddenRow
            simp
          have hpairzero :
              pairMask p alpha (uniqueHiddenRow hq hone) = 0 := by
            simp [pairMask, hl, hr]
          rw [hpad, hpairzero, add_zero] at heval
          exact heval.symm
        subst beta
        have hpair : padMask hq a = pairMask p alpha := by
          simpa [translatedPairParameterToMask, constantMask] using hmode
        obtain ⟨pv, hpv⟩ :=
          visible_pair_of_padMask_eq_pairMask hq a p alpha halpha hpair
        exact Or.inl
          (exists_pairMask_iff_level_two_supportRowsEqual a |>.mp
            ⟨pv, alpha, halpha, hpv⟩)
  · rintro (hpair | hco)
    · obtain ⟨p, alpha, halpha, ha⟩ :=
        exists_pairMask_iff_level_two_supportRowsEqual a |>.mpr hpair
      refine ⟨⟨0, ⟨liftPairIndex hq p, ⟨alpha, halpha⟩⟩⟩, ?_⟩
      rw [ha, padMask_pairMask]
      simp [translatedPairParameterToMask]
    · obtain ⟨i, alpha, halpha, ha⟩ := hco
      subst a
      exact translatedPair_of_coSingleton hq hone i alpha halpha

abbrev CoSingletonParameter (n q : Nat) :=
  Fin q × {alpha : XorSpace n // alpha ≠ 0}

abbrev CoSingletonModeMask (n q : Nat) :=
  {a : BitMatrix q n // IsCoSingletonMode a}

def coSingletonParameterToMask {n q : Nat}
    (z : CoSingletonParameter n q) : CoSingletonModeMask n q :=
  ⟨coSingletonMask z.1 z.2.1, ⟨z.1, z.2.1, z.2.2, rfl⟩⟩

theorem coSingletonParameterToMask_injective {n q : Nat} (hq2 : 2 ≤ q) :
    Function.Injective
      (coSingletonParameterToMask :
        CoSingletonParameter n q → CoSingletonModeMask n q) := by
  rintro ⟨i, ⟨alpha, halpha⟩⟩ ⟨j, ⟨beta, hbeta⟩⟩ h
  have hfun : coSingletonMask i alpha = coSingletonMask j beta :=
    congrArg Subtype.val h
  have hij : i = j := by
    by_contra hij
    have hv := congrFun hfun i
    rw [coSingletonMask_self, coSingletonMask_ne j i beta hij] at hv
    exact hbeta hv.symm
  subst j
  have hcard : 1 < (Finset.univ : Finset (Fin q)).card := by
    simp
    omega
  obtain ⟨k, _hk, hki⟩ := Finset.exists_mem_ne hcard i
  have hv := congrFun hfun k
  rw [coSingletonMask_ne i k alpha hki,
    coSingletonMask_ne i k beta hki] at hv
  subst beta
  rfl

theorem coSingletonParameterToMask_surjective {n q : Nat} :
    Function.Surjective
      (coSingletonParameterToMask :
        CoSingletonParameter n q → CoSingletonModeMask n q) := by
  rintro ⟨a, i, alpha, halpha, rfl⟩
  exact ⟨⟨i, ⟨alpha, halpha⟩⟩, rfl⟩

noncomputable def coSingletonParameterEquiv (n q : Nat) (hq2 : 2 ≤ q) :
    CoSingletonParameter n q ≃ CoSingletonModeMask n q :=
  Equiv.ofBijective coSingletonParameterToMask
    ⟨coSingletonParameterToMask_injective hq2,
      coSingletonParameterToMask_surjective⟩

theorem card_coSingletonModeMask {n q : Nat} (hq2 : 2 ≤ q) :
    Fintype.card (CoSingletonModeMask n q) = q * (2 ^ n - 1) := by
  rw [← Fintype.card_congr (coSingletonParameterEquiv n q hq2)]
  simp [CoSingletonParameter]

/-- Extra density left by marginalizing the full proxy with exactly one
hidden row. -/
def oneHiddenCorrectionDensity (n q : Nat) (y : BitMatrix q n) : Real :=
  ∑ a : CoSingletonModeMask n q,
    (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) * walsh a.1 y

theorem fourier_oneHiddenCorrectionDensity {n q : Nat}
    (a : BitMatrix q n) :
    fourier (oneHiddenCorrectionDensity n q) a =
      if IsCoSingletonMode a then
        1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)
      else 0 := by
  unfold oneHiddenCorrectionDensity XORFourier.fourier
  rw [show (fun x : BitMatrix q n =>
      (∑ b : CoSingletonModeMask n q,
          (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) * walsh b.1 x) *
        walsh a x) =
      (fun x => ∑ b : CoSingletonModeMask n q,
        (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
          (walsh b.1 x * walsh a x)) by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _hb
    ring]
  rw [average_fintype_sum]
  simp_rw [average_const_mul, average_walsh_mul_walsh]
  by_cases ha : IsCoSingletonMode a
  · rw [if_pos ha]
    let aa : CoSingletonModeMask n q := ⟨a, ha⟩
    rw [Finset.sum_eq_single aa]
    · simp only [aa, if_true, mul_one]
    · intro b _hb hba
      have hne : b.1 ≠ a := by
        intro hval
        apply hba
        exact Subtype.ext hval
      simp [hne]
    · simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b _hb
    have hne : b.1 ≠ a := by
      intro h
      apply ha
      rw [← h]
      exact b.2
    simp [hne]

theorem rowSupport_coSingletonMask {n q : Nat} (i : Fin q)
    (alpha : XorSpace n) (halpha : alpha ≠ 0) :
    rowSupport (coSingletonMask i alpha) =
      (Finset.univ : Finset (Fin q)).erase i := by
  ext j
  rw [mem_rowSupport]
  simp [coSingletonMask, halpha]

theorem level_coSingletonMask {n q : Nat} (i : Fin q)
    (alpha : XorSpace n) (halpha : alpha ≠ 0) :
    level (coSingletonMask i alpha) = q - 1 := by
  unfold level
  rw [rowSupport_coSingletonMask i alpha halpha]
  simp

theorem level_eq_sub_one_of_isCoSingletonMode {n q : Nat}
    (a : BitMatrix q n) (ha : IsCoSingletonMode a) :
    level a = q - 1 := by
  obtain ⟨i, alpha, halpha, rfl⟩ := ha
  exact level_coSingletonMask i alpha halpha

/-- Exact coefficientwise full-proxy marginal with one hidden row. -/
theorem fourier_prefixMarginal_fullProxyDensity_one_hidden {n q : Nat}
    (hn : 3 ≤ n) (hq : q ≤ 2 ^ n) (hone : 2 ^ n - q = 1)
    (a : BitMatrix q n) :
    fourier (prefixMarginal hq (fullProxyDensity n)) a =
      fourier (fun y => proxyDensity (XorSpace n) q y +
        oneHiddenCorrectionDensity n q y) a := by
  have hN : 2 ≤ 2 ^ n := by
    calc
      2 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hq7 : 7 ≤ q := by
    have h8 : 8 ≤ 2 ^ n := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  rw [fourier_prefixMarginal,
    fourier_full_proxy_density_eq_spectrum (by omega),
    fourier_add_density,
    fourier_proxyDensity hN hq,
    fourier_oneHiddenCorrectionDensity]
  by_cases hzero : level a = 0
  · have ha0 : a = 0 := (level_eq_zero_iff a).mp hzero
    subst a
    have hpad : padMask hq (0 : BitMatrix q n) = constantMask 0 :=
      (padMask_eq_constantMask_iff hq (by omega) 0 0).mpr ⟨rfl, rfl⟩
    rw [hpad, fullProxySpectrum_constantMask (by omega)]
    have hnot2 : level (0 : BitMatrix q n) ≠ 2 := by simp [level]
    have hnotCo : ¬ IsCoSingletonMode (0 : BitMatrix q n) := by
      intro hco
      have hl := level_eq_sub_one_of_isCoSingletonMode 0 hco
      simp [level] at hl
      omega
    rw [if_pos hzero, if_neg hnot2, if_neg hnotCo]
    rw [fourier_convolution, fourier_injectionDensity_zero hq]
    norm_num
  · rw [if_neg hzero]
    by_cases htwo : level a = 2
    · rw [if_pos htwo]
      have hnotCo : ¬ IsCoSingletonMode a := by
        intro hco
        have hl := level_eq_sub_one_of_isCoSingletonMode a hco
        omega
      rw [if_neg hnotCo, add_zero]
      by_cases heq : supportRowsEqual a
      · obtain ⟨p, alpha, halpha, ha⟩ :=
          exists_pairMask_iff_level_two_supportRowsEqual a |>.mpr ⟨htwo, heq⟩
        have hfull :
            fullProxySpectrum n (padMask hq a) =
              1 / (((2 ^ n - 1 : Nat) : Real) ^ 2) := by
          rw [ha, padMask_pairMask]
          simpa using
            (fullProxySpectrum_translatedPairMask hn 0
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
          rw [padMask_isTranslatedPairMode_iff_one_hidden hq hone]
          exact not_or_intro (fun h => heq h.2) hnotCo
        rw [fullProxySpectrum_eq_zero_of_not_low_mode _ hconst hpair]
        rw [fourier_convolution]
        rw [fourier_injectionDensity_of_level_eq_two hq a htwo]
        rw [if_neg heq]
        norm_num
    · rw [if_neg htwo, add_zero]
      by_cases hco : IsCoSingletonMode a
      · rw [if_pos hco]
        obtain ⟨i, alpha, halpha, ha⟩ := hco
        rw [ha, padMask_coSingletonMask]
        simpa using (fullProxySpectrum_translatedPairMask hn alpha
          (hiddenVisiblePair hq hone i) alpha halpha)
      · rw [if_neg hco]
        have hconst : ¬ IsConstantMode (padMask hq a) := by
          rw [padMask_isConstantMode_iff hq (by omega)]
          intro ha0
          subst a
          exact hzero (by simp [level])
        have hpair : ¬ IsTranslatedPairMode (padMask hq a) := by
          rw [padMask_isTranslatedPairMode_iff_one_hidden hq hone]
          exact not_or_intro (fun h => htwo h.1) hco
        simpa using fullProxySpectrum_eq_zero_of_not_low_mode _ hconst hpair

theorem prefixMarginal_fullProxyDensity_eq_one_hidden {n q : Nat}
    (hn : 3 ≤ n) (hq : q ≤ 2 ^ n) (hone : 2 ^ n - q = 1)
    (y : BitMatrix q n) :
    prefixMarginal hq (fullProxyDensity n) y =
      proxyDensity (XorSpace n) q y + oneHiddenCorrectionDensity n q y := by
  rw [← fourier_inversion (prefixMarginal hq (fullProxyDensity n)) y]
  rw [← fourier_inversion
    (fun y => proxyDensity (XorSpace n) q y +
      oneHiddenCorrectionDensity n q y) y]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [fourier_prefixMarginal_fullProxyDensity_one_hidden hn hq hone a]

def oneHiddenCorrectionAdvantage (n q : Nat) : Real :=
  (1 / 2 : Real) *
    average (BitMatrix q n) (fun y => |oneHiddenCorrectionDensity n q y|)

theorem average_oneHiddenCorrectionDensity_sq {n q : Nat} (hq2 : 2 ≤ q) :
    average (BitMatrix q n)
        (fun y => (oneHiddenCorrectionDensity n q y) ^ 2) =
      ((q : Real) * ((2 ^ n - 1 : Nat) : Real)) *
        (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) ^ 2 := by
  rw [parseval_sq]
  simp_rw [fourier_oneHiddenCorrectionDensity]
  let c : Real := 1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)
  calc
    (∑ a : BitMatrix q n,
        (if IsCoSingletonMode a then c else 0) ^ 2) =
        ∑ a : BitMatrix q n,
          if IsCoSingletonMode a then c ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases h : IsCoSingletonMode a <;> simp [h]
    _ = ∑ a : CoSingletonModeMask n q, c ^ 2 := by
      rw [← RandomSystems.SoP.XORTail.sum_filter_eq_sum_subtype
        IsCoSingletonMode (fun _ : BitMatrix q n => c ^ 2)]
      rw [Finset.sum_filter]
    _ = (Fintype.card (CoSingletonModeMask n q) : Real) * c ^ 2 := by
      simp
    _ = ((q : Real) * ((2 ^ n - 1 : Nat) : Real)) * c ^ 2 := by
      rw [card_coSingletonModeMask hq2]
      norm_num
    _ = _ := rfl

theorem average_oneHiddenCorrectionDensity_sq_of_one_hidden {n q : Nat}
    (hn : 3 ≤ n) (hone : 2 ^ n - q = 1) :
    average (BitMatrix q n)
        (fun y => (oneHiddenCorrectionDensity n q y) ^ 2) =
      1 / (((2 ^ n - 1 : Nat) : Real) ^ 2) := by
  have h8 : 8 ≤ 2 ^ n := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hq2 : 2 ≤ q := by omega
  rw [average_oneHiddenCorrectionDensity_sq hq2]
  have hqeq : q = 2 ^ n - 1 := by omega
  rw [hqeq]
  have hDnat : 0 < 2 ^ n - 1 := by omega
  have hD : (((2 ^ n - 1 : Nat) : Real)) ≠ 0 := by
    exact_mod_cast hDnat.ne'
  field_simp [hD]

theorem oneHiddenCorrectionAdvantage_le {n q : Nat}
    (hn : 3 ≤ n) (hone : 2 ^ n - q = 1) :
    oneHiddenCorrectionAdvantage n q ≤
      1 / (2 * ((2 ^ n - 1 : Nat) : Real)) := by
  have hDpos : 0 < (((2 ^ n - 1 : Nat) : Real)) := by
    have h8 : 8 ≤ 2 ^ n := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    exact_mod_cast (show 0 < 2 ^ n - 1 by omega)
  have hcauchy := uniformAverage_abs_le_sqrt_uniformAverage_sq
    (oneHiddenCorrectionDensity n q)
  unfold oneHiddenCorrectionAdvantage
  calc
    (1 / 2 : Real) *
        average (BitMatrix q n)
          (fun y => |oneHiddenCorrectionDensity n q y|) ≤
      (1 / 2 : Real) * Real.sqrt
        (average (BitMatrix q n)
          (fun y => (oneHiddenCorrectionDensity n q y) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcauchy (by norm_num)
    _ = (1 / 2 : Real) *
        Real.sqrt (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) := by
      rw [average_oneHiddenCorrectionDensity_sq_of_one_hidden hn hone]
    _ = 1 / (2 * ((2 ^ n - 1 : Nat) : Real)) := by
      rw [show 1 / (((2 ^ n - 1 : Nat) : Real) ^ 2) =
          (1 / (((2 ^ n - 1 : Nat) : Real))) ^ 2 by ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hDpos)]
      ring

theorem prefixMarginal_fullResidualDensity_eq_one_hidden {n q : Nat}
    (hn : 3 ≤ n) (hq : q ≤ 2 ^ n) (hone : 2 ^ n - q = 1)
    (y : BitMatrix q n) :
    prefixMarginal hq (fullResidualDensity n) y =
      remainderDensity (G := XorSpace n) q y -
        oneHiddenCorrectionDensity n q y := by
  unfold fullResidualDensity remainderDensity
  rw [prefixMarginal_sub]
  rw [prefixMarginal_full_convolution_eq hq]
  rw [prefixMarginal_fullProxyDensity_eq_one_hidden hn hq hone]
  rw [visibleDensityRatioReal_eq_convolution_injectionDensity hq]
  ring

theorem remainderDensity_eq_prefixMarginal_add_oneHiddenCorrection
    {n q : Nat} (hn : 3 ≤ n) (hq : q ≤ 2 ^ n)
    (hone : 2 ^ n - q = 1) (y : BitMatrix q n) :
    remainderDensity (G := XorSpace n) q y =
      prefixMarginal hq (fullResidualDensity n) y +
        oneHiddenCorrectionDensity n q y := by
  rw [prefixMarginal_fullResidualDensity_eq_one_hidden hn hq hone]
  ring

theorem remainderAdvantage_le_fullResidual_add_oneHiddenCorrection
    {n q : Nat} (hn : 3 ≤ n) (hq : q ≤ 2 ^ n)
    (hone : 2 ^ n - q = 1) :
    remainderAdvantage (G := XorSpace n) q ≤
      fullResidualAdvantage n + oneHiddenCorrectionAdvantage n q := by
  have hfun :
      (fun y : BitMatrix q n =>
        |remainderDensity (G := XorSpace n) q y|) =
      (fun y => |prefixMarginal hq (fullResidualDensity n) y +
        oneHiddenCorrectionDensity n q y|) := by
    funext y
    rw [remainderDensity_eq_prefixMarginal_add_oneHiddenCorrection
      hn hq hone]
  have htri := average_abs_add_le
    (fun y : BitMatrix q n => prefixMarginal hq (fullResidualDensity n) y)
    (oneHiddenCorrectionDensity n q)
  have hprefix := average_abs_prefixMarginal_le hq (fullResidualDensity n)
  unfold remainderAdvantage fullResidualAdvantage oneHiddenCorrectionAdvantage
  rw [hfun]
  calc
    (1 / 2 : Real) *
        average (BitMatrix q n)
          (fun y => |prefixMarginal hq (fullResidualDensity n) y +
            oneHiddenCorrectionDensity n q y|) ≤
      (1 / 2 : Real) *
        (average (BitMatrix q n)
            (fun y => |prefixMarginal hq (fullResidualDensity n) y|) +
          average (BitMatrix q n)
            (fun y => |oneHiddenCorrectionDensity n q y|)) :=
      mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ (1 / 2 : Real) *
        (average (BitMatrix (2 ^ n) n)
            (fun y => |fullResidualDensity n y|) +
          average (BitMatrix q n)
            (fun y => |oneHiddenCorrectionDensity n q y|)) := by
      gcongr
    _ = (1 / 2 : Real) *
          average (BitMatrix (2 ^ n) n)
            (fun y => |fullResidualDensity n y|) +
        (1 / 2 : Real) *
          average (BitMatrix q n)
            (fun y => |oneHiddenCorrectionDensity n q y|) := by ring

theorem remainderAdvantage_le_one_hidden_closed {n q : Nat}
    (hn : 63 ≤ n) (hq : q ≤ 2 ^ n) (hone : 2 ^ n - q = 1) :
    remainderAdvantage (G := XorSpace n) q ≤
      7 / (((2 ^ n : Nat) : Real)) +
        1 / (2 * ((2 ^ n - 1 : Nat) : Real)) := by
  exact (remainderAdvantage_le_fullResidual_add_oneHiddenCorrection
      (by omega) hq hone).trans
    (add_le_add (fullResidualAdvantage_le_seven_div hn)
      (oneHiddenCorrectionAdvantage_le (by omega) hone))

theorem abs_adaptiveAdvantage_sub_collisionAdvantage_le_one_hidden
    {n q : Nat} (hn : 63 ≤ n) (hq : q ≤ 2 ^ n)
    (hone : 2 ^ n - q = 1) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionAdvantage (XorSpace n) q| ≤
      7 / (((2 ^ n : Nat) : Real)) +
        1 / (2 * ((2 ^ n - 1 : Nat) : Real)) := by
  exact (abs_advantage_sub_collisionAdvantage_le_remainder
      (G := XorSpace n) q (by simpa using hq)).trans
    (remainderAdvantage_le_one_hidden_closed hn hq hone)

/-! ## Unified pre-saturation endpoint -/

theorem two_hidden_correction_le_one_hidden_correction {n : Nat}
    (hn : 1 ≤ n) :
    1 / (((2 ^ n : Nat) : Real) * ((2 ^ n - 1 : Nat) : Real)) ≤
      1 / (2 * ((2 ^ n - 1 : Nat) : Real)) := by
  let N : Nat := 2 ^ n
  have hn0 : n ≠ 0 := by omega
  have hN : 2 ≤ N := by
    dsimp [N]
    exact Nat.one_lt_two_pow hn0
  have hpredNat : 0 < N - 1 := by omega
  have hpred : (0 : Real) < ((N - 1 : Nat) : Real) := by
    exact_mod_cast hpredNat
  apply one_div_le_one_div_of_le (mul_pos (by norm_num) hpred)
  have hNR : (2 : Real) ≤ (N : Real) := by exact_mod_cast hN
  nlinarith

theorem one_hidden_correction_le_inv_card {n : Nat} (hn : 1 ≤ n) :
    1 / (2 * ((2 ^ n - 1 : Nat) : Real)) ≤
      1 / (((2 ^ n : Nat) : Real)) := by
  let N : Nat := 2 ^ n
  have hn0 : n ≠ 0 := by omega
  have hN : 2 ≤ N := by
    dsimp [N]
    exact Nat.one_lt_two_pow hn0
  have hNR : (0 : Real) < (N : Real) := by positivity
  apply one_div_le_one_div_of_le hNR
  rw [Nat.cast_sub (by omega : 1 ≤ N)]
  norm_num only [Nat.cast_one]
  have hNreal : (2 : Real) ≤ (N : Real) := by exact_mod_cast hN
  linarith

/-- Every strict prefix of the full deck has remainder at most the worst of
the three exact marginal cases. -/
theorem remainderAdvantage_le_pre_saturation {n q : Nat}
    (hn : 63 ≤ n) (hq : q < 2 ^ n) :
    remainderAdvantage (G := XorSpace n) q ≤
      7 / (((2 ^ n : Nat) : Real)) +
        1 / (2 * ((2 ^ n - 1 : Nat) : Real)) := by
  have hqle : q ≤ 2 ^ n := Nat.le_of_lt hq
  have htailPos : 0 < 2 ^ n - q := Nat.sub_pos_of_lt hq
  by_cases hthree : 3 ≤ 2 ^ n - q
  · exact (remainderAdvantage_le_seven_div_of_three_hidden
      hn hqle hthree).trans (le_add_of_nonneg_right (by positivity))
  · have hboundary : 2 ^ n - q = 1 ∨ 2 ^ n - q = 2 := by omega
    rcases hboundary with hone | htwo
    · exact remainderAdvantage_le_one_hidden_closed hn hqle hone
    · calc
        remainderAdvantage (G := XorSpace n) q ≤
            7 / (((2 ^ n : Nat) : Real)) +
              1 / (((2 ^ n : Nat) : Real) *
                ((2 ^ n - 1 : Nat) : Real)) :=
          remainderAdvantage_le_seven_div_add_twoHidden_exact hn hqle htwo
        _ ≤ 7 / (((2 ^ n : Nat) : Real)) +
              1 / (2 * ((2 ^ n - 1 : Nat) : Real)) := by
          exact add_le_add_right
            (two_hidden_correction_le_one_hidden_correction
              (n := n) (by omega)) _

/-- Unified exact comparison for every query depth strictly before the
full-deck checksum-saturation point. -/
theorem abs_adaptiveAdvantage_sub_collisionAdvantage_le_pre_saturation
    {n q : Nat} (hn : 63 ≤ n) (hq : q < 2 ^ n) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionAdvantage (XorSpace n) q| ≤
      7 / (((2 ^ n : Nat) : Real)) +
        1 / (2 * ((2 ^ n - 1 : Nat) : Real)) := by
  exact
    (abs_advantage_sub_collisionAdvantage_le_remainder
      (G := XorSpace n) q (by simpa using Nat.le_of_lt hq)).trans
      (remainderAdvantage_le_pre_saturation hn hq)

/-- Terminal-readable rounded form of the pre-saturation error. -/
theorem abs_adaptiveAdvantage_sub_collisionAdvantage_le_eight_div_pre_saturation
    {n q : Nat} (hn : 63 ≤ n) (hq : q < 2 ^ n) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionAdvantage (XorSpace n) q| ≤
      8 / (((2 ^ n : Nat) : Real)) := by
  calc
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionAdvantage (XorSpace n) q| ≤
        7 / (((2 ^ n : Nat) : Real)) +
          1 / (2 * ((2 ^ n - 1 : Nat) : Real)) :=
      abs_adaptiveAdvantage_sub_collisionAdvantage_le_pre_saturation hn hq
    _ ≤ 7 / (((2 ^ n : Nat) : Real)) +
          1 / (((2 ^ n : Nat) : Real)) := by
      exact add_le_add_right
        (one_hidden_correction_le_inv_card (n := n) (by omega)) _
    _ = 8 / (((2 ^ n : Nat) : Real)) := by ring

/-! ## Best compiled residual in both query regimes -/

/-- Use the sharper sparse Fourier remainder below half the deck and the
signed complement remainder above it.  In the overlap we retain the smaller
of the two certified quantities. -/
def preSaturationRemainderBound (n q : Nat) : Real :=
  let complement :=
    7 / (((2 ^ n : Nat) : Real)) +
      1 / (2 * ((2 ^ n - 1 : Nat) : Real))
  if 2 * q ≤ 2 ^ n then
    min (remainderErrorBound n q) complement
  else complement

theorem remainderAdvantage_le_preSaturationRemainderBound {n q : Nat}
    (hn : 63 ≤ n) (hq : q < 2 ^ n) :
    remainderAdvantage (G := XorSpace n) q ≤
      preSaturationRemainderBound n q := by
  unfold preSaturationRemainderBound
  dsimp only
  split_ifs with hhalf
  · apply le_min
    · exact remainderAdvantage_le (by omega) hhalf
    · exact remainderAdvantage_le_pre_saturation hn hq
  · exact remainderAdvantage_le_pre_saturation hn hq

/-- Tightest currently compiled two-sided collision approximation: the
existing sparse residual is used through half the deck and the signed
full-deck residual thereafter. -/
theorem abs_adaptiveAdvantage_sub_collisionAdvantage_le_best_pre_saturation
    {n q : Nat} (hn : 63 ≤ n) (hq : q < 2 ^ n) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionAdvantage (XorSpace n) q| ≤
      preSaturationRemainderBound n q := by
  exact (abs_advantage_sub_collisionAdvantage_le_remainder
      (G := XorSpace n) q (by simpa using Nat.le_of_lt hq)).trans
    (remainderAdvantage_le_preSaturationRemainderBound hn hq)

/-- The explicit collision-threshold distinguisher has the same main term and
the same all-regime signed residual error. -/
theorem abs_collisionThresholdTestGap_sub_collisionAdvantage_le_best_pre_saturation
    {n q : Nat} (hn : 63 ≤ n) (hq0 : 0 < q) (hq : q < 2 ^ n) :
    |collisionThresholdTestGap n q - collisionAdvantage (XorSpace n) q| ≤
      preSaturationRemainderBound n q := by
  have hN : 2 ≤ 2 ^ n := by
    have hn0 : n ≠ 0 := by omega
    exact Nat.one_lt_two_pow hn0
  exact (abs_collision_threshold_gap_sub_proxy_le_remainder
      hN hq0 (Nat.le_of_lt hq)).trans
    (remainderAdvantage_le_preSaturationRemainderBound hn hq)

/-- Matching-attack certificate: before checksum saturation, the concrete
collision-threshold test is within twice the certified residual of the exact
optimal adaptive advantage. -/
theorem abs_adaptiveAdvantage_sub_collisionThresholdTestGap_le_best_pre_saturation
    {n q : Nat} (hn : 63 ≤ n) (hq0 : 0 < q) (hq : q < 2 ^ n) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        collisionThresholdTestGap n q| ≤
      2 * preSaturationRemainderBound n q := by
  let adv := PFunPDS.Prob.adaptiveTranscriptAdvantage
    (q := q) (RandomSystems.SoP.xop (XorSpace n))
      (RandomSystems.SoP.urf (XorSpace n))
  let col := collisionAdvantage (XorSpace n) q
  let gap := collisionThresholdTestGap n q
  have hadv : |adv - col| ≤ preSaturationRemainderBound n q := by
    simpa [adv, col] using
      abs_adaptiveAdvantage_sub_collisionAdvantage_le_best_pre_saturation hn hq
  have hgap : |gap - col| ≤ preSaturationRemainderBound n q := by
    simpa [gap, col] using
      abs_collisionThresholdTestGap_sub_collisionAdvantage_le_best_pre_saturation
        hn hq0 hq
  calc
    |adv - gap| = |(adv - col) + (col - gap)| := by ring_nf
    _ ≤ |adv - col| + |col - gap| := abs_add_le _ _
    _ = |adv - col| + |gap - col| := by rw [abs_sub_comm col gap]
    _ ≤ preSaturationRemainderBound n q +
        preSaturationRemainderBound n q := add_le_add hadv hgap
    _ = 2 * preSaturationRemainderBound n q := by ring

end RandomSystems.SoP.XORComplement
