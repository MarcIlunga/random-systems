/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORComplement

/-!
# Exact quotient spectrum for the full-domain XOR SoP residual

This file identifies, without an estimate, every Walsh mode removed by the
checksum-conditioned collision proxy.  Global-character modes and translated
two-row modes are disjoint and uniquely parametrized once `n >= 3`.  The
signed residual energy is consequently exactly the anchored fourth moment of
the injection coefficients after those modes have been deleted.

The remaining dense-regime obligation is now the single positive inequality
`anchoredInjectionFourthTail n <= C / (2^n)^2`.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORComplement

open RandomSystems.Applications.SoP
open RandomSystems.SoP.CollisionProxy
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

def fullProxySpectrum (n : Nat) (a : BitMatrix (2 ^ n) n) : Real :=
  (∑ beta : XorSpace n,
      if constantMask beta = a then 1 else 0) +
    ∑ p : PairIndex (2 ^ n),
      ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
          (fun alpha => alpha ≠ 0),
        ∑ beta : XorSpace n,
          (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
            (if constantMask beta + pairMask p alpha = a then 1 else 0)

theorem full_proxy_density_eq_walsh_orbit_sum {n : Nat} (hn : 1 ≤ n)
    (y : BitMatrix (2 ^ n) n) :
    fullProxyDensity n y =
      (∑ beta : XorSpace n, walsh (constantMask beta) y) +
        ∑ p : PairIndex (2 ^ n),
          ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
              (fun alpha => alpha ≠ 0),
            ∑ beta : XorSpace n,
              (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
                walsh (constantMask beta + pairMask p alpha) y := by
  let c : Real := 1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)
  rw [show fullProxyDensity n y =
      checksumDensity n (2 ^ n) y +
        checksumDensity n (2 ^ n) y *
          collisionKernel (XorSpace n) (2 ^ n) y by
    unfold fullProxyDensity proxyDensity
    ring_nf]
  rw [checksum_density_eq_sum_walsh,
    collision_kernel_eq_pair_mask_sum_full hn]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply congrArg ((∑ beta : XorSpace n, walsh (constantMask beta) y) + ·)
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro alpha _halpha
  rw [show
      ∑ beta : XorSpace n,
          walsh (constantMask beta) y *
            (c * walsh (pairMask p alpha) y) =
        ∑ beta : XorSpace n,
          c * walsh (constantMask beta + pairMask p alpha) y by
    apply Finset.sum_congr rfl
    intro beta _hbeta
    rw [walsh_add_left]
    ring]

theorem fourier_walsh_eq_indicator {n q : Nat}
    (b a : BitMatrix q n) :
    fourier (walsh b) a = if b = a then 1 else 0 := by
  unfold XORFourier.fourier
  rw [average_walsh_mul_walsh]

theorem fourier_full_proxy_density_eq_spectrum {n : Nat} (hn : 1 ≤ n)
    (a : BitMatrix (2 ^ n) n) :
    fourier (fullProxyDensity n) a = fullProxySpectrum n a := by
  unfold XORFourier.fourier fullProxySpectrum
  rw [show (fun x : BitMatrix (2 ^ n) n => fullProxyDensity n x * walsh a x) =
      (fun x =>
        ((∑ beta : XorSpace n, walsh (constantMask beta) x) +
          ∑ p : PairIndex (2 ^ n),
            ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
                (fun alpha => alpha ≠ 0),
              ∑ beta : XorSpace n,
                (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
                  walsh (constantMask beta + pairMask p alpha) x) *
          walsh a x) by
    funext x
    rw [full_proxy_density_eq_walsh_orbit_sum hn]]
  rw [show (fun x : BitMatrix (2 ^ n) n =>
      ((∑ beta : XorSpace n, walsh (constantMask beta) x) +
        ∑ p : PairIndex (2 ^ n),
          ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
              (fun alpha => alpha ≠ 0),
            ∑ beta : XorSpace n,
              (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
                walsh (constantMask beta + pairMask p alpha) x) *
        walsh a x) =
      (fun x =>
        (∑ beta : XorSpace n,
          walsh (constantMask beta) x * walsh a x) +
        ∑ p : PairIndex (2 ^ n),
          ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
              (fun alpha => alpha ≠ 0),
            ∑ beta : XorSpace n,
              (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
                (walsh (constantMask beta + pairMask p alpha) x *
                  walsh a x)) by
    funext x
    simp only [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro p _hp
    apply Finset.sum_congr rfl
    intro alpha _halpha
    apply Finset.sum_congr rfl
    intro beta _hbeta
    ring]
  rw [average_add, average_fintype_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro beta _hbeta
    rw [average_walsh_mul_walsh]
  · rw [average_fintype_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [average_finset_sum]
    apply Finset.sum_congr rfl
    intro alpha _halpha
    rw [average_fintype_sum]
    apply Finset.sum_congr rfl
    intro beta _hbeta
    rw [average_const_mul, average_walsh_mul_walsh]

abbrev TranslatedPairParameter (n q : Nat) :=
  XorSpace n × PairMaskParameter n q

def translatedPairParameterToMask {n q : Nat}
    (z : TranslatedPairParameter n q) : BitMatrix q n :=
  constantMask z.1 + pairMask z.2.1 z.2.2.1

theorem constantMask_injective {n q : Nat} (hq : 0 < q) :
    Function.Injective (constantMask : XorSpace n → BitMatrix q n) := by
  intro alpha beta h
  have hi := congrFun h ⟨0, hq⟩
  simpa [constantMask] using hi

theorem exists_row_outside_two_pairs {q : Nat} (hq : 5 ≤ q)
    (p r : PairIndex q) :
    ∃ i : Fin q,
      i ≠ p.1.1 ∧ i ≠ p.1.2 ∧ i ≠ r.1.1 ∧ i ≠ r.1.2 := by
  let s : Finset (Fin q) := {p.1.1, p.1.2, r.1.1, r.1.2}
  have hsCard : s.card ≤ 4 := by
    dsimp [s]
    calc
      ({p.1.1, p.1.2, r.1.1, r.1.2} : Finset (Fin q)).card ≤
          ({p.1.2, r.1.1, r.1.2} : Finset (Fin q)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (({r.1.1, r.1.2} : Finset (Fin q)).card + 1) + 1 := by
        exact Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ ≤ ((({r.1.2} : Finset (Fin q)).card + 1) + 1) + 1 := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) 1
      _ ≤ 4 := by simp
  have hnot : s ≠ Finset.univ := by
    intro hsuniv
    have hcard : q ≤ 4 := by
      have := congrArg Finset.card hsuniv
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    omega
  have hnforall : ¬ ∀ i : Fin q, i ∈ s := by
    simpa [Finset.eq_univ_iff_forall] using hnot
  push Not at hnforall
  obtain ⟨i, hi⟩ := hnforall
  refine ⟨i, ?_⟩
  simpa [s] using hi

theorem translatedPairParameterToMask_injective {n q : Nat} (hq : 5 ≤ q) :
    Function.Injective
      (translatedPairParameterToMask :
        TranslatedPairParameter n q → BitMatrix q n) := by
  rintro ⟨beta, ⟨p, ⟨alpha, halpha⟩⟩⟩
    ⟨gamma, ⟨r, ⟨delta, hdelta⟩⟩⟩ h
  obtain ⟨i, hip, hip', hir, hir'⟩ := exists_row_outside_two_pairs hq p r
  have hbg : beta = gamma := by
    have hi := congrFun h i
    simpa [translatedPairParameterToMask, constantMask, pairMask,
      hip, hip', hir, hir'] using hi
  subst gamma
  have hpair : pairMask p alpha = pairMask r delta := by
    exact add_left_cancel h
  let z : PairMaskParameter n q := ⟨p, ⟨alpha, halpha⟩⟩
  let w : PairMaskParameter n q := ⟨r, ⟨delta, hdelta⟩⟩
  have hzw : z = w := by
    apply pairMaskParameterToMask_injective
    apply Subtype.ext
    exact hpair
  exact Prod.ext rfl hzw

theorem constantMask_ne_translatedPairMask {n q : Nat} (hq : 3 ≤ q)
    (gamma beta : XorSpace n) (p : PairIndex q) (alpha : XorSpace n)
    (halpha : alpha ≠ 0) :
    constantMask gamma ≠ constantMask beta + pairMask p alpha := by
  intro h
  let s : Finset (Fin q) := {p.1.1, p.1.2}
  have hsCard : s.card ≤ 2 := by
    dsimp [s]
    calc
      ({p.1.1, p.1.2} : Finset (Fin q)).card ≤
          ({p.1.2} : Finset (Fin q)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 := by simp
  have hnot : s ≠ Finset.univ := by
    intro hsuniv
    have hcard : q ≤ 2 := by
      have := congrArg Finset.card hsuniv
      simp only [Finset.card_univ, Fintype.card_fin] at this
      omega
    omega
  have hnforall : ¬ ∀ i : Fin q, i ∈ s := by
    simpa [Finset.eq_univ_iff_forall] using hnot
  push Not at hnforall
  obtain ⟨i, hi⟩ := hnforall
  have hi' : i ≠ p.1.1 ∧ i ≠ p.1.2 := by simpa [s] using hi
  have hgb : gamma = beta := by
    have hv := congrFun h i
    simpa [constantMask, pairMask, hi'.1, hi'.2] using hv
  have hp := congrFun h p.1.1
  rw [hgb] at hp
  have hz : beta + alpha = beta := by
    simpa [constantMask, pairMask] using hp.symm
  have : alpha = 0 := add_left_cancel (show beta + alpha = beta + 0 by simpa using hz)
  exact halpha this

def IsConstantMode {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∃ beta : XorSpace n, a = constantMask beta

def IsTranslatedPairMode {n q : Nat} (a : BitMatrix q n) : Prop :=
  ∃ z : TranslatedPairParameter n q, a = translatedPairParameterToMask z

theorem fullProxySpectrum_eq_zero_of_not_low_mode {n : Nat} (a : BitMatrix (2 ^ n) n)
    (hconst : ¬ IsConstantMode a) (hpair : ¬ IsTranslatedPairMode a) :
    fullProxySpectrum n a = 0 := by
  unfold fullProxySpectrum
  have hc (beta : XorSpace n) : constantMask beta ≠ a := by
    intro h
    apply hconst
    exact ⟨beta, h.symm⟩
  have hp (p : PairIndex (2 ^ n)) (alpha : XorSpace n)
      (halpha : alpha ≠ 0) (beta : XorSpace n) :
      constantMask beta + pairMask p alpha ≠ a := by
    intro h
    apply hpair
    exact ⟨⟨beta, ⟨p, ⟨alpha, halpha⟩⟩⟩, h.symm⟩
  simp only [if_neg (hc _), Finset.sum_const_zero, zero_add]
  apply Finset.sum_eq_zero
  intro p _hp
  apply Finset.sum_eq_zero
  intro alpha halphaMem
  have halpha : alpha ≠ 0 := (Finset.mem_filter.mp halphaMem).2
  apply Finset.sum_eq_zero
  intro beta _hbeta
  rw [if_neg (hp p alpha halpha beta)]
  ring

theorem fullProxySpectrum_constantMask {n : Nat} (hn : 2 ≤ n)
    (gamma : XorSpace n) :
    fullProxySpectrum n (constantMask gamma) = 1 := by
  have hq0 : 0 < 2 ^ n := by positivity
  have hq3 : 3 ≤ 2 ^ n := by
    calc
      3 ≤ 4 := by omega
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  unfold fullProxySpectrum
  have hc (beta : XorSpace n) :
      constantMask beta = constantMask gamma ↔ beta = gamma :=
    (constantMask_injective hq0).eq_iff
  simp_rw [hc]
  rw [Finset.sum_ite_eq' (s := Finset.univ) (a := gamma)]
  simp only [Finset.mem_univ, if_true]
  have hsum :
      (∑ p : PairIndex (2 ^ n),
        ∑ alpha ∈ (Finset.univ : Finset (XorSpace n)).filter
            (fun alpha => alpha ≠ 0),
          ∑ beta : XorSpace n,
            (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
              (if constantMask beta + pairMask p alpha = constantMask gamma
                then 1 else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro p _hp
    apply Finset.sum_eq_zero
    intro alpha halphaMem
    have halpha : alpha ≠ 0 := (Finset.mem_filter.mp halphaMem).2
    apply Finset.sum_eq_zero
    intro beta _hbeta
    rw [if_neg]
    · ring
    · exact (constantMask_ne_translatedPairMask hq3 gamma beta p alpha halpha).symm
  rw [hsum]
  ring

theorem translatedPairMask_eq_iff {n q : Nat} (hq : 5 ≤ q)
    (beta gamma : XorSpace n) (p r : PairIndex q)
    (alpha delta : XorSpace n) (halpha : alpha ≠ 0) (hdelta : delta ≠ 0) :
    constantMask gamma + pairMask r delta =
        constantMask beta + pairMask p alpha ↔
      r = p ∧ delta = alpha ∧ gamma = beta := by
  constructor
  · intro h
    let z : TranslatedPairParameter n q :=
      ⟨gamma, ⟨r, ⟨delta, hdelta⟩⟩⟩
    let w : TranslatedPairParameter n q :=
      ⟨beta, ⟨p, ⟨alpha, halpha⟩⟩⟩
    have hzw : z = w := translatedPairParameterToMask_injective hq h
    have hgamma : gamma = beta := congrArg (fun x => x.1) hzw
    have hrest := congrArg (fun x => x.2) hzw
    have hr : r = p := congrArg (fun x => x.1) hrest
    have hdsub : (⟨delta, hdelta⟩ : {x : XorSpace n // x ≠ 0}) =
        ⟨alpha, halpha⟩ := congrArg (fun x => x.2) hrest
    exact ⟨hr, congrArg Subtype.val hdsub, hgamma⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem fullProxySpectrum_translatedPairMask {n : Nat} (hn : 3 ≤ n)
    (beta : XorSpace n) (p : PairIndex (2 ^ n))
    (alpha : XorSpace n) (halpha : alpha ≠ 0) :
    fullProxySpectrum n (constantMask beta + pairMask p alpha) =
      1 / (((2 ^ n - 1 : Nat) : Real) ^ 2) := by
  have hq3 : 3 ≤ 2 ^ n := by
    calc
      3 ≤ 8 := by omega
      _ = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hq5 : 5 ≤ 2 ^ n := by
    calc
      5 ≤ 8 := by omega
      _ = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  unfold fullProxySpectrum
  have hc (gamma : XorSpace n) :
      constantMask gamma ≠ constantMask beta + pairMask p alpha :=
    constantMask_ne_translatedPairMask hq3 gamma beta p alpha halpha
  simp only [if_neg (hc _), Finset.sum_const_zero, zero_add]
  have heq (r : PairIndex (2 ^ n)) (delta : XorSpace n)
      (hdelta : delta ≠ 0) (gamma : XorSpace n) :
      constantMask gamma + pairMask r delta =
          constantMask beta + pairMask p alpha ↔
        r = p ∧ delta = alpha ∧ gamma = beta :=
    translatedPairMask_eq_iff hq5 beta gamma p r alpha delta halpha hdelta
  calc
    (∑ r : PairIndex (2 ^ n),
      ∑ delta ∈ (Finset.univ : Finset (XorSpace n)).filter
          (fun delta => delta ≠ 0),
        ∑ gamma : XorSpace n,
          (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
            (if constantMask gamma + pairMask r delta =
                constantMask beta + pairMask p alpha then 1 else 0)) =
      ∑ r : PairIndex (2 ^ n),
        ∑ delta ∈ (Finset.univ : Finset (XorSpace n)).filter
            (fun delta => delta ≠ 0),
          ∑ gamma : XorSpace n,
            (1 / (((2 ^ n - 1 : Nat) : Real) ^ 2)) *
              (if r = p ∧ delta = alpha ∧ gamma = beta then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r _hr
        apply Finset.sum_congr rfl
        intro delta hdeltaMem
        have hdelta : delta ≠ 0 := (Finset.mem_filter.mp hdeltaMem).2
        apply Finset.sum_congr rfl
        intro gamma _hgamma
        simp only [heq r delta hdelta gamma]
    _ = 1 / (((2 ^ n - 1 : Nat) : Real) ^ 2) := by
      simp_rw [ite_and]
      simp [Finset.sum_ite_irrel, halpha]

theorem fourier_sub_density {n q : Nat} (f g : BitMatrix q n → Real)
    (a : BitMatrix q n) :
    fourier (fun y => f y - g y) a = fourier f a - fourier g a := by
  unfold XORFourier.fourier average
  rw [show
      (∑ x : BitMatrix q n, (f x - g x) * walsh a x) =
        (∑ x : BitMatrix q n, f x * walsh a x) -
          ∑ x : BitMatrix q n, g x * walsh a x by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring]
  rw [sub_div]

theorem fourier_full_residual_density_eq {n : Nat} (hn : 1 ≤ n)
    (a : BitMatrix (2 ^ n) n) :
    fourier (fullResidualDensity n) a =
      fourier
          (convolution (injectionDensity n (2 ^ n))
            (injectionDensity n (2 ^ n))) a -
        fullProxySpectrum n a := by
  unfold fullResidualDensity
  rw [fourier_sub_density, fourier_full_proxy_density_eq_spectrum hn]

theorem fourier_full_convolution_constantMask {n : Nat}
    (beta : XorSpace n) :
    fourier
        (convolution (injectionDensity n (2 ^ n))
          (injectionDensity n (2 ^ n)))
        (constantMask beta) = 1 := by
  have hshift := fourier_full_convolution_add_constant_mask
    (n := n) (0 : BitMatrix (2 ^ n) n) beta
  simp only [zero_add] at hshift
  rw [hshift, fourier_convolution,
    fourier_injectionDensity_zero (le_refl (2 ^ n))]
  ring

theorem fourier_full_convolution_translatedPairMask {n : Nat}
    (beta : XorSpace n) (p : PairIndex (2 ^ n))
    (alpha : XorSpace n) (halpha : alpha ≠ 0) :
    fourier
        (convolution (injectionDensity n (2 ^ n))
          (injectionDensity n (2 ^ n)))
        (constantMask beta + pairMask p alpha) =
      1 / (((2 ^ n - 1 : Nat) : Real) ^ 2) := by
  have hshift := fourier_full_convolution_add_constant_mask
    (n := n) (pairMask p alpha) beta
  have heq : pairMask p alpha + constantMask beta =
      constantMask beta + pairMask p alpha := by
    rw [add_comm]
  rw [heq] at hshift
  rw [hshift, fourier_convolution]
  have hcoef := fourier_injectionDensity_of_level_eq_two
    (n := n) (q := 2 ^ n) (le_refl (2 ^ n))
    (pairMask p alpha) (level_pairMask p alpha halpha)
  rw [if_pos (supportRowsEqual_pairMask p alpha)] at hcoef
  rw [hcoef]
  ring

theorem fourier_full_residual_constantMode_eq_zero {n : Nat} (hn : 2 ≤ n)
    (beta : XorSpace n) :
    fourier (fullResidualDensity n) (constantMask beta) = 0 := by
  rw [fourier_full_residual_density_eq (by omega),
    fourier_full_convolution_constantMask,
    fullProxySpectrum_constantMask hn]
  ring

theorem fourier_full_residual_translatedPairMode_eq_zero {n : Nat}
    (hn : 3 ≤ n) (beta : XorSpace n) (p : PairIndex (2 ^ n))
    (alpha : XorSpace n) (halpha : alpha ≠ 0) :
    fourier (fullResidualDensity n)
        (constantMask beta + pairMask p alpha) = 0 := by
  rw [fourier_full_residual_density_eq (by omega),
    fourier_full_convolution_translatedPairMask beta p alpha halpha,
    fullProxySpectrum_translatedPairMask hn beta p alpha halpha]
  ring

theorem fourier_full_residual_eq_injection_sq_of_not_low_mode {n : Nat}
    (hn : 1 ≤ n) (a : BitMatrix (2 ^ n) n)
    (hconst : ¬ IsConstantMode a) (hpair : ¬ IsTranslatedPairMode a) :
    fourier (fullResidualDensity n) a =
      fourier (injectionDensity n (2 ^ n)) a ^ 2 := by
  rw [fourier_full_residual_density_eq hn,
    fullProxySpectrum_eq_zero_of_not_low_mode a hconst hpair,
    fourier_convolution]
  ring

def IsFullProxyMode {n : Nat} (a : BitMatrix (2 ^ n) n) : Prop :=
  IsConstantMode a ∨ IsTranslatedPairMode a

/-- The quotient fourth moment with the constant and translated pair modes
deleted before taking a norm. -/
def anchoredInjectionFourthTail (n : Nat) : Real :=
  ∑ b : AnchoredMask n,
    if IsFullProxyMode b.1 then 0
    else fourier (injectionDensity n (2 ^ n)) b.1 ^ 4

theorem anchoredResidualEnergy_eq_injectionFourthTail {n : Nat}
    (hn : 3 ≤ n) :
    anchoredResidualEnergy n = anchoredInjectionFourthTail n := by
  unfold anchoredResidualEnergy anchoredInjectionFourthTail
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hc : IsConstantMode b.1
  · rw [if_pos (show IsFullProxyMode b.1 from Or.inl hc)]
    obtain ⟨beta, hbeta⟩ := hc
    rw [hbeta, fourier_full_residual_constantMode_eq_zero (by omega)]
    ring
  · by_cases hp : IsTranslatedPairMode b.1
    · rw [if_pos (show IsFullProxyMode b.1 from Or.inr hp)]
      obtain ⟨⟨beta, ⟨p, ⟨alpha, halpha⟩⟩⟩, hmode⟩ := hp
      rw [hmode]
      change
        fourier (fullResidualDensity n)
            (constantMask beta + pairMask p alpha) ^ 2 = 0
      rw [fourier_full_residual_translatedPairMode_eq_zero
        hn beta p alpha halpha]
      ring
    · rw [if_neg (show ¬ IsFullProxyMode b.1 from not_or_intro hc hp),
        fourier_full_residual_eq_injection_sq_of_not_low_mode
          (by omega) b.1 hc hp]
      ring

/-! ## Removing the checksum coordinate

An anchored full mask has a zero distinguished row.  Deleting that row turns
it into an ordinary `(2^n - 1)`-row mask, and the full-permutation Fourier
coefficient is exactly the coefficient of the corresponding uniform
injection.  This identifies the remaining quotient tail with the concrete
dense Fourier tail used in Eberhard's formulation.
-/

def fullTailCardEq (n : Nat) : (2 ^ n - 1) + 1 = 2 ^ n :=
  Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero n (by norm_num)))

def fullTailEmbedding (n : Nat) : Fin (2 ^ n - 1) ↪ Fin (2 ^ n) :=
  (Fin.succEmb (2 ^ n - 1)).trans (finCongr (fullTailCardEq n)).toEmbedding

@[simp]
theorem fullTailEmbedding_apply (n : Nat) (i : Fin (2 ^ n - 1)) :
    fullTailEmbedding n i = Fin.cast (fullTailCardEq n) i.succ := rfl

theorem fullTailEmbedding_ne_anchor (n : Nat) (i : Fin (2 ^ n - 1)) :
    fullTailEmbedding n i ≠ fullAnchor n := by
  intro h
  have hv := congrArg Fin.val h
  simp [fullTailEmbedding, fullAnchor] at hv

theorem exists_fullTailEmbedding_eq {n : Nat} (i : Fin (2 ^ n))
    (hi : i ≠ fullAnchor n) :
    ∃ j : Fin (2 ^ n - 1), fullTailEmbedding n j = i := by
  have hi0 : i.val ≠ 0 := by
    intro hzero
    apply hi
    apply Fin.ext
    simpa [fullAnchor] using hzero
  let j : Fin (2 ^ n - 1) := ⟨i.val - 1, by omega⟩
  refine ⟨j, ?_⟩
  apply Fin.ext
  simp [fullTailEmbedding, j]
  omega

def anchoredMaskToTail {n : Nat} (b : AnchoredMask n) :
    BitMatrix (2 ^ n - 1) n :=
  restrictMask (fullTailEmbedding n) b.1

def tailMaskToAnchored {n : Nat} (a : BitMatrix (2 ^ n - 1) n) :
    AnchoredMask n :=
  ⟨Function.extend (fullTailEmbedding n) a 0, by
    apply Function.extend_apply'
    rintro ⟨i, h⟩
    exact fullTailEmbedding_ne_anchor n i h⟩

/-- Deleting the distinguished zero row is an equivalence from quotient masks
to ordinary masks on `2^n - 1` rows. -/
def anchoredMaskEquivTail (n : Nat) :
    AnchoredMask n ≃ BitMatrix (2 ^ n - 1) n where
  toFun := anchoredMaskToTail
  invFun := tailMaskToAnchored
  left_inv b := by
    apply Subtype.ext
    funext i
    by_cases hi : i = fullAnchor n
    · subst i
      rw [b.2]
      unfold tailMaskToAnchored
      change Function.extend (fullTailEmbedding n)
          (anchoredMaskToTail b) 0 (fullAnchor n) = 0
      rw [Function.extend_apply' _ _ _ (by
        rintro ⟨j, hj⟩
        exact fullTailEmbedding_ne_anchor n j hj)]
      rfl
    · obtain ⟨j, rfl⟩ := exists_fullTailEmbedding_eq i hi
      unfold tailMaskToAnchored
      change Function.extend (fullTailEmbedding n)
          (anchoredMaskToTail b) 0 (fullTailEmbedding n j) =
        b.1 (fullTailEmbedding n j)
      rw [(fullTailEmbedding n).injective.extend_apply]
      rfl
  right_inv a := by
    funext i
    change Function.extend (fullTailEmbedding n) a 0
        (fullTailEmbedding n i) = a i
    rw [(fullTailEmbedding n).injective.extend_apply]

/-- The anchored full-deck coefficient is precisely its `N-1`-query
injection coefficient. -/
theorem fourier_anchored_full_eq_tail {n : Nat} (b : AnchoredMask n) :
    fourier (injectionDensity n (2 ^ n)) b.1 =
      fourier (injectionDensity n (2 ^ n - 1))
        (anchoredMaskEquivTail n b) := by
  apply fourier_injectionDensity_eq_restrictMask (le_refl (2 ^ n))
  intro i hi
  by_contra hne
  have hia : i ≠ fullAnchor n := by
    intro h
    subst i
    exact hne b.2
  obtain ⟨j, hj⟩ := exists_fullTailEmbedding_eq i hia
  exact hi ⟨j, hj⟩

/-- The proxy modes transported to the ordinary `N-1`-row mask space. -/
def IsTailProxyMode {n : Nat} (a : BitMatrix (2 ^ n - 1) n) : Prop :=
  IsFullProxyMode ((anchoredMaskEquivTail n).symm a).1

/-- Exact final reduction: the open quotient energy is an ordinary
`N-1`-query injection fourth moment with the transported constant and pair
modes deleted. -/
theorem anchoredInjectionFourthTail_eq_tail (n : Nat) :
    anchoredInjectionFourthTail n =
      ∑ a : BitMatrix (2 ^ n - 1) n,
        if IsTailProxyMode a then 0
        else fourier (injectionDensity n (2 ^ n - 1)) a ^ 4 := by
  unfold anchoredInjectionFourthTail
  apply Fintype.sum_equiv (anchoredMaskEquivTail n)
  intro b
  simp only [IsTailProxyMode, Equiv.symm_apply_apply]
  rw [fourier_anchored_full_eq_tail]

end RandomSystems.SoP.XORComplement
