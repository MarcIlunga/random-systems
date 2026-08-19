/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.CollisionStein
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The absolute-value Stein certificate

This file constructs, rather than postulates, the analytic certificate used by
the finite local-dependence theorem in `CollisionStein`.  Its target is the
standard Gaussian mean absolute deviation `sqrt (2 / pi)`.

The construction uses the elementary half-line kernels

```text
R(x) = integral exp(-x*u-u^2/2) du
J(x) = integral u*exp(-x*u-u^2/2) du
```

for nonnegative `x`.  Integration by parts gives `J(x)+x*R(x)=1`.
The Stein solution is the odd extension of `sqrt(2/pi)*R(x)-1`; its derivative
is the even function `-sqrt(2/pi)*J(|x|)`.  All bounds are proved directly.
-/

noncomputable section

open Set
open MeasureTheory

namespace RandomSystems.SoP.CollisionStein

def steinKernel (x u : ℝ) : ℝ :=
  Real.exp (-x * u - (1 / 2 : ℝ) * u ^ 2)

def steinR (x : ℝ) : ℝ :=
  ∫ u : ℝ in Set.Ioi 0, steinKernel x u

def steinJ (x : ℝ) : ℝ :=
  ∫ u : ℝ in Set.Ioi 0, u * steinKernel x u

def steinL (x : ℝ) : ℝ :=
  ∫ u : ℝ in Set.Ioi 0, u ^ 2 * steinKernel x u

lemma steinKernel_zero (u : ℝ) :
    steinKernel 0 u = Real.exp (-(1 / 2 : ℝ) * u ^ 2) := by
  simp [steinKernel]

lemma integrableOn_steinKernel_zero :
    IntegrableOn (steinKernel 0) (Set.Ioi 0) := by
  refine (integrable_exp_neg_mul_sq
    (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn.congr_fun ?_ measurableSet_Ioi
  intro u _hu
  simp [steinKernel]

lemma integrableOn_mul_steinKernel_zero :
    IntegrableOn (fun u : ℝ => u * steinKernel 0 u) (Set.Ioi 0) := by
  simpa [steinKernel] using
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn

lemma integrableOn_sq_mul_steinKernel_zero :
    IntegrableOn (fun u : ℝ => u ^ 2 * steinKernel 0 u) (Set.Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (s := (2 : ℝ)) (by norm_num) (by norm_num)
  rw [show (fun u : ℝ => u ^ 2 * steinKernel 0 u) =
      (fun u => u ^ (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * u ^ 2)) by
    funext u
    rw [Real.rpow_two]
    simp [steinKernel]]
  exact h

lemma steinKernel_nonneg (x u : ℝ) : 0 ≤ steinKernel x u := by
  exact (Real.exp_pos _).le

lemma steinKernel_le_zero {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    steinKernel x u ≤ steinKernel 0 u := by
  apply Real.exp_le_exp.mpr
  dsimp [steinKernel]
  nlinarith

lemma integrableOn_steinKernel {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (steinKernel x) (Set.Ioi 0) := by
  apply integrableOn_steinKernel_zero.mono'
  · exact (show Continuous (steinKernel x) by
      unfold steinKernel
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (steinKernel_nonneg x u)]
    exact steinKernel_le_zero hx hu.le

lemma integrableOn_mul_steinKernel {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun u : ℝ => u * steinKernel x u) (Set.Ioi 0) := by
  apply integrableOn_mul_steinKernel_zero.mono'
  · exact (show Continuous (fun u : ℝ => u * steinKernel x u) by
      unfold steinKernel
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu.le,
      abs_of_nonneg (steinKernel_nonneg x u)]
    exact mul_le_mul_of_nonneg_left (steinKernel_le_zero hx hu.le) hu.le

lemma integrableOn_sq_mul_steinKernel {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun u : ℝ => u ^ 2 * steinKernel x u) (Set.Ioi 0) := by
  apply integrableOn_sq_mul_steinKernel_zero.mono'
  · exact (show Continuous (fun u : ℝ => u ^ 2 * steinKernel x u) by
      unfold steinKernel
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg u),
      abs_of_nonneg (steinKernel_nonneg x u)]
    exact mul_le_mul_of_nonneg_left (steinKernel_le_zero hx hu.le) (sq_nonneg u)

lemma steinR_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ steinR x := by
  unfold steinR
  exact integral_nonneg_of_ae <| by
    filter_upwards with u
    exact steinKernel_nonneg x u

lemma steinJ_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ steinJ x := by
  unfold steinJ
  exact integral_nonneg_of_ae <| by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg hu.le (steinKernel_nonneg x u)

lemma steinL_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ steinL x := by
  unfold steinL
  exact integral_nonneg_of_ae <| by
    filter_upwards with u
    exact mul_nonneg (sq_nonneg u) (steinKernel_nonneg x u)

lemma steinR_le_zero {x : ℝ} (hx : 0 ≤ x) : steinR x ≤ steinR 0 := by
  unfold steinR
  exact setIntegral_mono_on (integrableOn_steinKernel hx)
    integrableOn_steinKernel_zero measurableSet_Ioi fun u hu =>
      steinKernel_le_zero hx hu.le

lemma steinJ_le_zero {x : ℝ} (hx : 0 ≤ x) : steinJ x ≤ steinJ 0 := by
  unfold steinJ
  exact setIntegral_mono_on (integrableOn_mul_steinKernel hx)
    integrableOn_mul_steinKernel_zero measurableSet_Ioi fun u hu =>
      mul_le_mul_of_nonneg_left (steinKernel_le_zero hx hu.le) hu.le

lemma steinL_le_zero {x : ℝ} (hx : 0 ≤ x) : steinL x ≤ steinL 0 := by
  unfold steinL
  exact setIntegral_mono_on (integrableOn_sq_mul_steinKernel hx)
    integrableOn_sq_mul_steinKernel_zero measurableSet_Ioi fun u hu =>
      mul_le_mul_of_nonneg_left (steinKernel_le_zero hx hu.le) (sq_nonneg u)

lemma steinR_zero : steinR 0 = Real.sqrt (2 * Real.pi) / 2 := by
  unfold steinR
  rw [show (fun u : ℝ => steinKernel 0 u) =
      (fun u => Real.exp (-(1 / 2 : ℝ) * u ^ 2)) by
    funext u
    simp [steinKernel]]
  rw [integral_gaussian_Ioi (1 / 2 : ℝ)]
  congr 1
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring]

lemma steinJ_zero : steinJ 0 = 1 := by
  unfold steinJ
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (1 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simp [steinKernel, Real.rpow_one]
  · norm_num [Real.Gamma_one]

lemma steinL_zero : steinL 0 = Real.sqrt (2 * Real.pi) / 2 := by
  unfold steinL
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  rw [show (fun u : ℝ => u ^ 2 * steinKernel 0 u) =
      (fun u => u ^ (2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * u ^ (2 : ℝ))) by
    funext u
    rw [Real.rpow_two]
    simp [steinKernel]]
  rw [h]
  rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by ring,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  have hrpow : (1 / 2 : ℝ) ^ (-(3 : ℝ) / 2) = 2 * Real.sqrt 2 := by
    rw [show -(3 : ℝ) / 2 = -(3 / 2 : ℝ) by ring]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2), Real.rpow_one]
    rw [← Real.sqrt_eq_rpow]
    have hs : Real.sqrt (1 / 2 : ℝ) = Real.sqrt 2 / 2 := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num
      have hs2 : Real.sqrt 2 ≠ 0 := by positivity
      field_simp [hs2]
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hs]
    have hs2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp [hs2]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show -(2 + 1 : ℝ) / 2 = -(3 : ℝ) / 2 by norm_num, hrpow]
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  rw [show Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]]
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp [hs2]

lemma real_exp_lipschitz_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have hderiv : ∀ z ∈ Set.Iic (0 : ℝ),
      HasDerivWithinAt Real.exp (Real.exp z) (Set.Iic 0) z := by
    intro z _hz
    exact Real.hasDerivAt_exp z |>.hasDerivWithinAt
  have hbound : ∀ z ∈ Set.Iic (0 : ℝ), ‖Real.exp z‖ ≤ (1 : ℝ) := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
    exact Real.exp_le_one_iff.mpr hz
  have h := (convex_Iic (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hx hy
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

lemma real_exp_taylor_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y - Real.exp y * (x - y)| ≤ (x - y) ^ 2 := by
  let r : ℝ → ℝ := fun z => Real.exp z - Real.exp y - Real.exp y * (z - y)
  let s : Set ℝ := Set.uIcc x y
  have hderiv : ∀ z ∈ s,
      HasDerivWithinAt r (Real.exp z - Real.exp y) s z := by
    intro z _hz
    dsimp [r]
    convert ((Real.hasDerivAt_exp z).sub_const (Real.exp y)).sub
      ((hasDerivAt_id z).sub_const y |>.const_mul (Real.exp y)) |>.hasDerivWithinAt using 1 <;>
      ring
  have hbound : ∀ z ∈ s, ‖Real.exp z - Real.exp y‖ ≤ |x - y| := by
    intro z hz
    rw [Real.norm_eq_abs]
    have hz0 : z ≤ 0 := by
      exact hz.2.trans (max_le hx hy)
    refine (real_exp_lipschitz_nonpos hz0 hy).trans ?_
    dsimp [s] at hz
    rcases le_total x y with hxy | hyx
    · rw [uIcc_of_le hxy] at hz
      rcases hz with ⟨hz1, hz2⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hz2),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith
    · rw [uIcc_of_ge hyx] at hz
      rcases hz with ⟨hz1, hz2⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hz1),
        abs_of_nonneg (sub_nonneg.mpr hyx)]
      linarith
  have hxy : x ∈ s := left_mem_uIcc
  have hyx : y ∈ s := right_mem_uIcc
  have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound hxy hyx
  have hrx : r x = Real.exp x - Real.exp y - Real.exp y * (x - y) := rfl
  have hry : r y = 0 := by simp [r]
  rw [hrx, hry, zero_sub, norm_neg] at h
  simpa [Real.norm_eq_abs, abs_sub_comm, pow_two] using h

lemma steinKernel_eq_zero_mul_exp (x u : ℝ) :
    steinKernel x u = steinKernel 0 u * Real.exp (-x * u) := by
  simp only [steinKernel, zero_mul, neg_zero, zero_sub]
  rw [← Real.exp_add]
  congr 1
  ring

lemma tendsto_steinKernel_atTop_zero {x : ℝ} (hx : 0 ≤ x) :
    Filter.Tendsto (steinKernel x) Filter.atTop (nhds 0) := by
  have hzero : Filter.Tendsto (steinKernel 0) Filter.atTop (nhds 0) := by
    unfold steinKernel
    have h := Real.tendsto_exp_atBot.comp
        ((Filter.tendsto_pow_atTop (by norm_num : (2 : Nat) ≠ 0)).const_mul_atTop_of_neg
          (by norm_num : -(1 / 2 : ℝ) < 0))
    convert h using 1
    funext u
    congr 1
    ring
  exact squeeze_zero' (Filter.Eventually.of_forall fun u => steinKernel_nonneg x u)
    (Filter.eventually_atTop.2 ⟨0, fun u hu => steinKernel_le_zero hx hu⟩) hzero

lemma hasDerivAt_steinKernel_right (x u : ℝ) :
    HasDerivAt (steinKernel x) (-(x + u) * steinKernel x u) u := by
  have hexponent : HasDerivAt
      (fun z : ℝ => -x * z - (1 / 2 : ℝ) * z ^ 2) (-x - u) u := by
    convert ((hasDerivAt_id u).const_mul (-x)).sub
      ((hasDerivAt_pow 2 u).const_mul (1 / 2)) using 1 <;> ring
  convert hexponent.exp using 1 <;> simp only [steinKernel] <;> ring

lemma steinJ_add_mul_steinR {x : ℝ} (hx : 0 ≤ x) :
    steinJ x + x * steinR x = 1 := by
  let d : ℝ → ℝ := fun u => -(x + u) * steinKernel x u
  have hd : ∀ u ∈ Set.Ici (0 : ℝ), HasDerivAt (steinKernel x) (d u) u := by
    intro u _hu
    exact hasDerivAt_steinKernel_right x u
  have hdint : IntegrableOn d (Set.Ioi 0) := by
    have hsum : IntegrableOn
        (fun u : ℝ => x * steinKernel x u + u * steinKernel x u)
        (Set.Ioi 0) :=
      (integrableOn_steinKernel hx).const_mul x |>.add
        (integrableOn_mul_steinKernel hx)
    apply hsum.neg.congr_fun
    · intro u _hu
      dsimp [d]
      ring
    · exact measurableSet_Ioi
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hd hdint
    (tendsto_steinKernel_atTop_zero hx)
  have hzero : steinKernel x 0 = 1 := by simp [steinKernel]
  have hintegral :
      (∫ u : ℝ in Set.Ioi 0, d u) = -(x * steinR x + steinJ x) := by
    unfold steinR steinJ
    dsimp [d]
    rw [show (fun u : ℝ => -(x + u) * steinKernel x u) =
        (fun u => -(x * steinKernel x u + u * steinKernel x u)) by
      funext u
      ring]
    rw [MeasureTheory.integral_neg,
      MeasureTheory.integral_add ((integrableOn_steinKernel hx).const_mul x)
        (integrableOn_mul_steinKernel hx),
      MeasureTheory.integral_const_mul]
  rw [hintegral, hzero] at hftc
  linarith

lemma steinJ_lipschitz_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |steinJ x - steinJ y| ≤ steinL 0 * |x - y| := by
  have hpoint : ∀ u ∈ Set.Ioi (0 : ℝ),
      |u * steinKernel x u - u * steinKernel y u| ≤
        |x - y| * (u ^ 2 * steinKernel 0 u) := by
    intro u hu
    have hxu : -x * u ≤ 0 := by nlinarith [mul_nonneg hx hu.le]
    have hyu : -y * u ≤ 0 := by nlinarith [mul_nonneg hy hu.le]
    have hexp := real_exp_lipschitz_nonpos hxu hyu
    have hscale : |-x * u - (-y * u)| = u * |x - y| := by
      have huabs : |u| = u := abs_of_pos hu
      rw [show -x * u - -y * u = -(x - y) * u by ring, abs_mul,
        abs_neg, huabs]
      ring
    rw [hscale] at hexp
    have hdiff :
        u * steinKernel x u - u * steinKernel y u =
          u * steinKernel 0 u *
            (Real.exp (-x * u) - Real.exp (-y * u)) := by
      rw [steinKernel_eq_zero_mul_exp x u, steinKernel_eq_zero_mul_exp y u]
      ring
    rw [hdiff, abs_mul, abs_mul, abs_of_pos hu,
      abs_of_nonneg (steinKernel_nonneg 0 u)]
    calc
      u * steinKernel 0 u *
          |Real.exp (-x * u) - Real.exp (-y * u)| ≤
          u * steinKernel 0 u * (u * |x - y|) :=
        mul_le_mul_of_nonneg_left hexp
          (mul_nonneg hu.le (steinKernel_nonneg 0 u))
      _ = |x - y| * (u ^ 2 * steinKernel 0 u) := by ring
  unfold steinJ
  rw [← MeasureTheory.integral_sub (integrableOn_mul_steinKernel hx)
    (integrableOn_mul_steinKernel hy)]
  rw [← Real.norm_eq_abs]
  have hboundInt : IntegrableOn
      (fun u : ℝ => |x - y| * (u ^ 2 * steinKernel 0 u)) (Set.Ioi 0) :=
    integrableOn_sq_mul_steinKernel_zero.const_mul |x - y|
  calc
    ‖∫ u : ℝ in Set.Ioi 0,
        (u * steinKernel x u - u * steinKernel y u)‖ ≤
        ∫ u : ℝ in Set.Ioi 0,
          |x - y| * (u ^ 2 * steinKernel 0 u) := by
      apply norm_integral_le_of_norm_le hboundInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa [Real.norm_eq_abs] using hpoint u hu
    _ = steinL 0 * |x - y| := by
      unfold steinL
      rw [MeasureTheory.integral_const_mul]
      ring

lemma steinR_taylor_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |steinR x - steinR y + steinJ y * (x - y)| ≤
      steinL 0 * (x - y) ^ 2 := by
  let H : ℝ → ℝ := fun u =>
    steinKernel x u - steinKernel y u +
      (u * steinKernel y u) * (x - y)
  have hpoint : ∀ u ∈ Set.Ioi (0 : ℝ),
      |H u| ≤ (x - y) ^ 2 * (u ^ 2 * steinKernel 0 u) := by
    intro u hu
    have hxu : -x * u ≤ 0 := by nlinarith [mul_nonneg hx hu.le]
    have hyu : -y * u ≤ 0 := by nlinarith [mul_nonneg hy hu.le]
    have he := real_exp_taylor_nonpos hxu hyu
    have hscale : (-x * u - (-y * u)) ^ 2 = (x - y) ^ 2 * u ^ 2 := by ring
    rw [hscale] at he
    have hrewrite : H u = steinKernel 0 u *
        (Real.exp (-x * u) - Real.exp (-y * u) -
          Real.exp (-y * u) * (-x * u - (-y * u))) := by
      dsimp [H]
      rw [steinKernel_eq_zero_mul_exp x u, steinKernel_eq_zero_mul_exp y u]
      ring
    rw [hrewrite, abs_mul, abs_of_nonneg (steinKernel_nonneg 0 u)]
    calc
      steinKernel 0 u *
          |Real.exp (-x * u) - Real.exp (-y * u) -
            Real.exp (-y * u) * (-x * u - -y * u)| ≤
          steinKernel 0 u * ((x - y) ^ 2 * u ^ 2) :=
        mul_le_mul_of_nonneg_left he (steinKernel_nonneg 0 u)
      _ = (x - y) ^ 2 * (u ^ 2 * steinKernel 0 u) := by ring
  have hboundInt : IntegrableOn
      (fun u : ℝ => (x - y) ^ 2 * (u ^ 2 * steinKernel 0 u))
      (Set.Ioi 0) := integrableOn_sq_mul_steinKernel_zero.const_mul _
  have hIntegral :
      (∫ u : ℝ in Set.Ioi 0, H u) =
        steinR x - steinR y + steinJ y * (x - y) := by
    calc
      (∫ u : ℝ in Set.Ioi 0, H u) =
          ∫ u : ℝ in Set.Ioi 0,
            (steinKernel x u - steinKernel y u) +
              (u * steinKernel y u) * (x - y) := by rfl
      _ = (∫ u : ℝ in Set.Ioi 0,
              (steinKernel x u - steinKernel y u)) +
            ∫ u : ℝ in Set.Ioi 0,
              (u * steinKernel y u) * (x - y) := by
        simpa only [Pi.sub_apply] using
          MeasureTheory.integral_add
            ((integrableOn_steinKernel hx).sub (integrableOn_steinKernel hy))
            ((integrableOn_mul_steinKernel hy).mul_const (x - y))
      _ = (∫ u : ℝ in Set.Ioi 0, steinKernel x u) -
            (∫ u : ℝ in Set.Ioi 0, steinKernel y u) +
            (∫ u : ℝ in Set.Ioi 0, u * steinKernel y u) * (x - y) := by
        rw [MeasureTheory.integral_sub (integrableOn_steinKernel hx)
          (integrableOn_steinKernel hy), MeasureTheory.integral_mul_const]
      _ = _ := rfl
  rw [← hIntegral, ← Real.norm_eq_abs]
  calc
    ‖∫ u : ℝ in Set.Ioi 0, H u‖ ≤
        ∫ u : ℝ in Set.Ioi 0,
          (x - y) ^ 2 * (u ^ 2 * steinKernel 0 u) := by
      apply norm_integral_le_of_norm_le hboundInt
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa [Real.norm_eq_abs] using hpoint u hu
    _ = steinL 0 * (x - y) ^ 2 := by
      unfold steinL
      rw [MeasureTheory.integral_const_mul]
      ring

def normalAbsConstant : ℝ := Real.sqrt (2 / Real.pi)

lemma normalAbsConstant_pos : 0 < normalAbsConstant := by
  unfold normalAbsConstant
  positivity

lemma normalAbsConstant_mul_steinR_zero :
    normalAbsConstant * steinR 0 = 1 := by
  rw [steinR_zero]
  unfold normalAbsConstant
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hspi : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hs2, hspi]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma normalAbsConstant_mul_steinL_zero :
    normalAbsConstant * steinL 0 = 1 := by
  rw [steinL_zero, ← steinR_zero]
  exact normalAbsConstant_mul_steinR_zero

def absSteinF (x : ℝ) : ℝ :=
  if 0 ≤ x then normalAbsConstant * steinR x - 1
  else 1 - normalAbsConstant * steinR (-x)

def absSteinG (x : ℝ) : ℝ :=
  -normalAbsConstant * steinJ |x|

@[simp]
lemma absSteinF_zero : absSteinF 0 = 0 := by
  rw [absSteinF, if_pos le_rfl]
  linarith [normalAbsConstant_mul_steinR_zero]

lemma absSteinF_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    absSteinF x = normalAbsConstant * steinR x - 1 := by
  rw [absSteinF, if_pos hx]

lemma absSteinF_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    absSteinF x = 1 - normalAbsConstant * steinR (-x) := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [absSteinF_zero]
    simp only [neg_zero]
    linarith [normalAbsConstant_mul_steinR_zero]
  · rw [absSteinF, if_neg (not_le.mpr hx)]

lemma absSteinF_neg (x : ℝ) : absSteinF (-x) = -absSteinF x := by
  rcases le_total 0 x with hx | hx
  · rw [absSteinF_of_nonpos (neg_nonpos.mpr hx), absSteinF_of_nonneg hx]
    ring_nf
  · rw [absSteinF_of_nonneg (neg_nonneg.mpr hx), absSteinF_of_nonpos hx]
    ring_nf

lemma absSteinG_neg (x : ℝ) : absSteinG (-x) = absSteinG x := by
  simp [absSteinG]

lemma absStein_equation (x : ℝ) :
    absSteinG x - x * absSteinF x = |x| - normalAbsConstant := by
  rcases le_total 0 x with hx | hx
  · rw [absSteinF_of_nonneg hx]
    unfold absSteinG
    rw [abs_of_nonneg hx]
    have hRJ := steinJ_add_mul_steinR hx
    have hscaled := congrArg (fun z : ℝ => normalAbsConstant * z) hRJ
    ring_nf at hscaled ⊢
    linarith
  · rw [absSteinF_of_nonpos hx]
    unfold absSteinG
    rw [abs_of_nonpos hx]
    have hnx : 0 ≤ -x := neg_nonneg.mpr hx
    have hRJ := steinJ_add_mul_steinR hnx
    have hscaled := congrArg (fun z : ℝ => normalAbsConstant * z) hRJ
    ring_nf at hscaled ⊢
    linarith

lemma abs_absSteinG_le (x : ℝ) :
    |absSteinG x| ≤ normalAbsConstant := by
  have hr : 0 ≤ |x| := abs_nonneg x
  have hJ0 := steinJ_le_zero hr
  have hJ := steinJ_nonneg hr
  have ha := normalAbsConstant_pos.le
  rw [steinJ_zero] at hJ0
  unfold absSteinG
  rw [abs_mul, abs_neg, abs_of_nonneg ha, abs_of_nonneg hJ]
  exact mul_le_of_le_one_right ha hJ0

lemma absSteinG_lipschitz (x y : ℝ) :
    |absSteinG x - absSteinG y| ≤ |x - y| := by
  have hx : 0 ≤ |x| := abs_nonneg x
  have hy : 0 ≤ |y| := abs_nonneg y
  have hJ := steinJ_lipschitz_nonneg hx hy
  have habs : abs (abs x - abs y) ≤ abs (x - y) :=
    abs_abs_sub_abs_le_abs_sub x y
  have ha : 0 ≤ normalAbsConstant := normalAbsConstant_pos.le
  unfold absSteinG
  rw [show -normalAbsConstant * steinJ |x| -
      -normalAbsConstant * steinJ |y| =
      -normalAbsConstant * (steinJ |x| - steinJ |y|) by ring,
    abs_mul, abs_neg, abs_of_nonneg ha]
  calc
    normalAbsConstant * abs (steinJ (abs x) - steinJ (abs y)) ≤
        normalAbsConstant * (steinL 0 * abs (abs x - abs y)) :=
      mul_le_mul_of_nonneg_left hJ ha
    _ ≤ normalAbsConstant * (steinL 0 * |x - y|) := by
      gcongr
      exact steinL_nonneg le_rfl
    _ = |x - y| := by
      rw [← mul_assoc, normalAbsConstant_mul_steinL_zero, one_mul]

lemma absSteinF_taylor_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |absSteinF x - absSteinF y - absSteinG y * (x - y)| ≤
      (x - y) ^ 2 := by
  have hR := steinR_taylor_nonneg hx hy
  have ha : 0 ≤ normalAbsConstant := normalAbsConstant_pos.le
  rw [absSteinF_of_nonneg hx, absSteinF_of_nonneg hy]
  unfold absSteinG
  rw [abs_of_nonneg hy]
  rw [show normalAbsConstant * steinR x - 1 -
      (normalAbsConstant * steinR y - 1) -
        (-normalAbsConstant * steinJ y) * (x - y) =
      normalAbsConstant *
        (steinR x - steinR y + steinJ y * (x - y)) by ring,
    abs_mul, abs_of_nonneg ha]
  calc
    normalAbsConstant *
        |steinR x - steinR y + steinJ y * (x - y)| ≤
        normalAbsConstant * (steinL 0 * (x - y) ^ 2) :=
      mul_le_mul_of_nonneg_left hR ha
    _ = (x - y) ^ 2 := by
      rw [← mul_assoc, normalAbsConstant_mul_steinL_zero, one_mul]

lemma absSteinF_taylor_cross {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 0) :
    |absSteinF x - absSteinF y - absSteinG y * (x - y)| ≤
      (x - y) ^ 2 := by
  let s : ℝ := -y
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hA := absSteinF_taylor_nonneg hx (show 0 ≤ (0 : ℝ) by norm_num)
  have hB := absSteinF_taylor_nonneg (show 0 ≤ (0 : ℝ) by norm_num) hs
  have hC := absSteinG_lipschitz 0 s
  have hFy : absSteinF y = -absSteinF s := by
    have h := absSteinF_neg s
    simpa [s] using h
  have hGy : absSteinG y = absSteinG s := by
    have h := absSteinG_neg s
    simpa [s] using h
  have hFs0 : absSteinF 0 = 0 := absSteinF_zero
  have hGs0 : |absSteinG 0 - absSteinG s| ≤ s := by
    simpa [abs_of_nonneg hs] using hC
  let A : ℝ := absSteinF x - absSteinF 0 - absSteinG 0 * (x - 0)
  let B : ℝ := absSteinF 0 - absSteinF s - absSteinG s * (0 - s)
  let C : ℝ := (absSteinG 0 - absSteinG s) * x
  have hdecomp :
      absSteinF x - absSteinF y - absSteinG y * (x - y) = A - B + C := by
    dsimp [A, B, C]
    rw [hFy, hGy, hFs0]
    dsimp [s]
    ring
  rw [hdecomp]
  calc
    |A - B + C| ≤ |A| + |B| + |C| := by
      calc
        |A - B + C| ≤ |A - B| + |C| := abs_add_le _ _
        _ ≤ (|A| + |B|) + |C| := by
          gcongr
          exact abs_sub A B
        _ = |A| + |B| + |C| := by ring
    _ ≤ x ^ 2 + s ^ 2 + s * x := by
      gcongr
      · simpa [A] using hA
      · simpa [B] using hB
      · dsimp [C]
        rw [abs_mul, abs_of_nonneg hx]
        exact mul_le_mul_of_nonneg_right hGs0 hx
    _ ≤ (x - y) ^ 2 := by
      dsimp [s]
      nlinarith [mul_nonneg hx hs]

lemma absSteinF_taylor (x y : ℝ) :
    |absSteinF x - absSteinF y - absSteinG y * (x - y)| ≤
      (x - y) ^ 2 := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · exact absSteinF_taylor_nonneg hx hy
    · exact absSteinF_taylor_cross hx (le_of_not_ge hy)
  · have hx' : x ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have h := absSteinF_taylor_cross
        (x := -x) (y := -y) (neg_nonneg.mpr hx') (neg_nonpos.mpr hy)
      have hFx : absSteinF (-x) = -absSteinF x := absSteinF_neg x
      have hFy : absSteinF (-y) = -absSteinF y := absSteinF_neg y
      have hGy : absSteinG (-y) = absSteinG y := absSteinG_neg y
      rw [hFx, hFy, hGy] at h
      have hins :
          -absSteinF x - -absSteinF y -
              absSteinG y * (-x - -y) =
            -(absSteinF x - absSteinF y - absSteinG y * (x - y)) := by
        ring
      have hrs : (-x - -y) ^ 2 = (x - y) ^ 2 := by ring
      rw [hins, abs_neg, hrs] at h
      exact h

    · have hy' : y ≤ 0 := le_of_not_ge hy
      have h := absSteinF_taylor_nonneg
        (x := -x) (y := -y) (neg_nonneg.mpr hx') (neg_nonneg.mpr hy')
      have hFx : absSteinF (-x) = -absSteinF x := absSteinF_neg x
      have hFy : absSteinF (-y) = -absSteinF y := absSteinF_neg y
      have hGy : absSteinG (-y) = absSteinG y := absSteinG_neg y
      rw [hFx, hFy, hGy] at h
      have hins :
          -absSteinF x - -absSteinF y -
              absSteinG y * (-x - -y) =
            -(absSteinF x - absSteinF y - absSteinG y * (x - y)) := by
        ring
      have hrs : (-x - -y) ^ 2 = (x - y) ^ 2 := by ring
      rw [hins, abs_neg, hrs] at h
      exact h

/-- A fully proved certificate for the standard Gaussian absolute-value
Stein equation.  The Taylor constant `1` is deliberately elementary; the
sharper `1/2` is unnecessary for convergence. -/
def normalAbsSteinCertificate : AbsSteinCertificate where
  f := absSteinF
  g := absSteinG
  target := normalAbsConstant
  gBound := normalAbsConstant
  lipBound := 1
  remainderBound := 1
  equation := absStein_equation
  g_abs_le := abs_absSteinG_le
  g_sub_le := by
    intro x y
    simpa using absSteinG_lipschitz x y
  taylor_le := by
    intro x y
    simpa using absSteinF_taylor x y
  gBound_nonneg := normalAbsConstant_pos.le
  lipBound_nonneg := by norm_num
  remainderBound_nonneg := by norm_num

@[simp]
theorem normalAbsSteinCertificate_target :
    normalAbsSteinCertificate.target = Real.sqrt (2 / Real.pi) := rfl

end RandomSystems.SoP.CollisionStein
