/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORFourier
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# A finite Stein bound for the collision-count mean absolute deviation

The SoP advantage only needs `E |W|`, not convergence against every test
function.  This file therefore develops the smallest useful normal
approximation theorem: a local-dependence Stein inequality for the single
test `h(x) = |x|`.

The theorem `uniformAverage_abs_sub_target_le_of_local_stein` is completely
finite.  It separates the analytic normal certificate from three elementary
quantities of the collision family:

* fluctuation of the sum of squared normalized edge variables;
* the squared-variable/local-neighborhood term;
* the Taylor remainder term.

This is the exact point at which the complete-graph coloring calculation is
plugged in below.  Keeping the interface explicit also prevents the
four-cycle omission that can occur in a generic dependency-graph variance
argument: no covariance is declared zero unless the corresponding finite
average is proved zero.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.CollisionStein

open RandomSystems.SoP.XORFourier

/-- Local spelling of uniform expectation, kept independent of the legacy
ANOVA development. -/
def uniformAverage (A : Type*) [Fintype A] (f : A → ℝ) : ℝ :=
  average A f

theorem uniformAverage_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformAverage A (fun a ↦ f a + g a) =
      uniformAverage A f + uniformAverage A g :=
  by simpa [uniformAverage] using average_add f g

theorem uniformAverage_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    uniformAverage A (fun a ↦ f a - g a) =
      uniformAverage A f - uniformAverage A g := by
  unfold uniformAverage average
  rw [Finset.sum_sub_distrib, sub_div]

theorem uniformAverage_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    uniformAverage A (fun _ ↦ c) = c :=
  by simpa [uniformAverage] using average_const c

theorem uniformAverage_const_mul {A : Type*} [Fintype A]
    (c : ℝ) (f : A → ℝ) :
    uniformAverage A (fun a ↦ c * f a) = c * uniformAverage A f :=
  by simpa [uniformAverage] using average_const_mul c f

theorem uniformAverage_finset_sum {A I : Type*} [Fintype A] [Fintype I]
    (f : I → A → ℝ) :
    uniformAverage A (fun a ↦ ∑ i, f i a) =
      ∑ i, uniformAverage A (f i) :=
  by simpa [uniformAverage] using average_fintype_sum f

theorem uniformAverage_mono {A : Type*} [Fintype A] [Nonempty A]
    {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    uniformAverage A f ≤ uniformAverage A g := by
  unfold uniformAverage average
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun a _ ↦ h a) (by positivity)

/-- The analytic data needed from the normal Stein equation for the single
test `x ↦ |x|`.  `f` is the Stein solution and `g` its derivative. -/
structure AbsSteinCertificate where
  f : ℝ → ℝ
  g : ℝ → ℝ
  target : ℝ
  gBound : ℝ
  lipBound : ℝ
  remainderBound : ℝ
  equation : ∀ x, g x - x * f x = |x| - target
  g_abs_le : ∀ x, |g x| ≤ gBound
  g_sub_le : ∀ x y, |g x - g y| ≤ lipBound * |x - y|
  taylor_le : ∀ x y,
    |f x - f y - g y * (x - y)| ≤ remainderBound * (x - y) ^ 2
  gBound_nonneg : 0 ≤ gBound
  lipBound_nonneg : 0 ≤ lipBound
  remainderBound_nonneg : 0 ≤ remainderBound

theorem abs_uniformAverage_le_uniformAverage_abs
    {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    |uniformAverage A f| ≤ uniformAverage A (fun a ↦ |f a|) := by
  unfold uniformAverage average
  have hcard : 0 ≤ (Fintype.card A : ℝ) := by positivity
  rw [abs_div, abs_of_nonneg hcard]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcard

theorem uniformAverage_neg {A : Type*} [Fintype A] (f : A → ℝ) :
    uniformAverage A (fun a ↦ -f a) = -uniformAverage A f := by
  unfold uniformAverage average
  rw [Finset.sum_neg_distrib, neg_div]

theorem uniformAverage_mul_const {A : Type*} [Fintype A]
    (f : A → ℝ) (c : ℝ) :
    uniformAverage A (fun a ↦ f a * c) = uniformAverage A f * c := by
  unfold uniformAverage average
  rw [← Finset.sum_mul, div_mul_eq_mul_div]

theorem uniformAverage_congr
    {A : Type*} [Fintype A] {f g : A → ℝ} (h : ∀ a, f a = g a) :
    uniformAverage A f = uniformAverage A g := by
  unfold uniformAverage average
  congr 1
  exact Finset.sum_congr rfl fun a _ ↦ h a

/-- Finite local-dependence Stein bound for `E|W|`.

`W0 i` is the part of `W` outside the neighborhood of coordinate `i`, and
`Y i = W - W0 i` is the local sum.  The two cancellation hypotheses are the
only probabilistic input: the centered variable cancels against functions of
the outside, and its cross-neighborhood linear term cancels there as well. -/
theorem uniformAverage_abs_sub_target_le_of_local_stein
    {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    (cert : AbsSteinCertificate)
    (X : I → A → ℝ) (W : A → ℝ)
    (W0 Y : I → A → ℝ)
    (hW : ∀ a, W a = ∑ i, X i a)
    (hsplit : ∀ i a, W a = W0 i a + Y i a)
    (hcenter : ∀ i,
      uniformAverage A (fun a ↦ X i a * cert.f (W0 i a)) = 0)
    (hcross : ∀ i,
      uniformAverage A (fun a ↦
        X i a * (Y i a - X i a) * cert.g (W0 i a)) = 0) :
    |uniformAverage A (fun a ↦ |W a|) - cert.target| ≤
      cert.gBound *
          uniformAverage A (fun a ↦ |1 - ∑ i, (X i a) ^ 2|) +
        cert.lipBound *
          uniformAverage A (fun a ↦
            ∑ i, (X i a) ^ 2 * |Y i a|) +
        cert.remainderBound *
          uniformAverage A (fun a ↦
            ∑ i, |X i a| * (Y i a) ^ 2) := by
  let R : I → A → ℝ := fun i a ↦
    cert.f (W a) - cert.f (W0 i a) -
      cert.g (W0 i a) * (W a - W0 i a)
  have hR : ∀ i a,
      |R i a| ≤ cert.remainderBound * (Y i a) ^ 2 := by
    intro i a
    dsimp [R]
    have hdiff : W a - W0 i a = Y i a := by
      linarith [hsplit i a]
    simpa [hdiff] using cert.taylor_le (W a) (W0 i a)
  have hWf :
      uniformAverage A (fun a ↦ W a * cert.f (W a)) =
        ∑ i, uniformAverage A (fun a ↦ X i a * cert.f (W a)) := by
    calc
      uniformAverage A (fun a ↦ W a * cert.f (W a)) =
          uniformAverage A (fun a ↦
            ∑ i, X i a * cert.f (W a)) := by
        apply uniformAverage_congr
        intro a
        rw [hW a, Finset.sum_mul]
      _ = _ := uniformAverage_finset_sum _
  have hcentered (i : I) :
      uniformAverage A (fun a ↦ X i a * cert.f (W a)) =
        uniformAverage A (fun a ↦
          X i a * (cert.f (W a) - cert.f (W0 i a))) := by
    calc
      uniformAverage A (fun a ↦ X i a * cert.f (W a)) =
          uniformAverage A (fun a ↦ X i a * cert.f (W a)) - 0 := by ring
      _ = uniformAverage A (fun a ↦ X i a * cert.f (W a)) -
          uniformAverage A (fun a ↦ X i a * cert.f (W0 i a)) := by
        rw [hcenter i]
      _ = uniformAverage A (fun a ↦
          X i a * cert.f (W a) - X i a * cert.f (W0 i a)) := by
        rw [uniformAverage_sub]
      _ = _ := by
        apply uniformAverage_congr
        intro a
        ring
  have hlinearized (i : I) :
      uniformAverage A (fun a ↦
          X i a * (cert.f (W a) - cert.f (W0 i a))) =
        uniformAverage A (fun a ↦
          X i a * (cert.g (W0 i a) * Y i a + R i a)) := by
    apply uniformAverage_congr
    intro a
    have hdiff : W a - W0 i a = Y i a := by
      linarith [hsplit i a]
    dsimp [R]
    rw [hdiff]
    ring
  have hlocal (i : I) :
      uniformAverage A (fun a ↦
          X i a * cert.g (W0 i a) * Y i a) =
        uniformAverage A (fun a ↦
          (X i a) ^ 2 * cert.g (W0 i a)) := by
    calc
      uniformAverage A (fun a ↦
          X i a * cert.g (W0 i a) * Y i a) =
          uniformAverage A (fun a ↦
            (X i a) ^ 2 * cert.g (W0 i a) +
              X i a * (Y i a - X i a) * cert.g (W0 i a)) := by
        apply uniformAverage_congr
        intro a
        ring
      _ = uniformAverage A (fun a ↦
            (X i a) ^ 2 * cert.g (W0 i a)) +
          uniformAverage A (fun a ↦
            X i a * (Y i a - X i a) * cert.g (W0 i a)) :=
        uniformAverage_add _ _
      _ = _ := by rw [hcross i, add_zero]
  have hcoordinate (i : I) :
      uniformAverage A (fun a ↦ X i a * cert.f (W a)) =
        uniformAverage A (fun a ↦
          (X i a) ^ 2 * cert.g (W0 i a) + X i a * R i a) := by
    rw [hcentered i, hlinearized i]
    calc
      uniformAverage A (fun a ↦
          X i a * (cert.g (W0 i a) * Y i a + R i a)) =
          uniformAverage A (fun a ↦
            X i a * cert.g (W0 i a) * Y i a + X i a * R i a) := by
        apply uniformAverage_congr
        intro a
        ring
      _ = uniformAverage A (fun a ↦
            X i a * cert.g (W0 i a) * Y i a) +
          uniformAverage A (fun a ↦ X i a * R i a) :=
        uniformAverage_add _ _
      _ = uniformAverage A (fun a ↦
            (X i a) ^ 2 * cert.g (W0 i a)) +
          uniformAverage A (fun a ↦ X i a * R i a) := by
        rw [hlocal i]
      _ = _ := (uniformAverage_add _ _).symm
  have hsum :
      ∑ i, uniformAverage A (fun a ↦ X i a * cert.f (W a)) =
        uniformAverage A (fun a ↦
          ∑ i, ((X i a) ^ 2 * cert.g (W0 i a) + X i a * R i a)) := by
    rw [uniformAverage_finset_sum]
    exact Finset.sum_congr rfl fun i _hi ↦ hcoordinate i
  have hstein :
      uniformAverage A (fun a ↦ |W a|) - cert.target =
        uniformAverage A (fun a ↦
          (1 - ∑ i, (X i a) ^ 2) * cert.g (W a)) +
        uniformAverage A (fun a ↦
          ∑ i, (X i a) ^ 2 *
            (cert.g (W a) - cert.g (W0 i a))) -
        uniformAverage A (fun a ↦
          ∑ i, X i a * R i a) := by
    calc
      uniformAverage A (fun a ↦ |W a|) - cert.target =
          uniformAverage A (fun a ↦ |W a| - cert.target) := by
        rw [uniformAverage_sub, uniformAverage_const]
      _ = uniformAverage A (fun a ↦
          cert.g (W a) - W a * cert.f (W a)) := by
        apply uniformAverage_congr
        intro a
        exact (cert.equation (W a)).symm
      _ = uniformAverage A (fun a ↦ cert.g (W a)) -
          ∑ i, uniformAverage A (fun a ↦ X i a * cert.f (W a)) := by
        rw [uniformAverage_sub, hWf]
      _ = uniformAverage A (fun a ↦ cert.g (W a)) -
          uniformAverage A (fun a ↦
            ∑ i, ((X i a) ^ 2 * cert.g (W0 i a) + X i a * R i a)) := by
        rw [hsum]
      _ = uniformAverage A (fun a ↦
          cert.g (W a) -
            ∑ i, ((X i a) ^ 2 * cert.g (W0 i a) + X i a * R i a)) := by
        rw [uniformAverage_sub]
      _ = uniformAverage A (fun a ↦
          (1 - ∑ i, (X i a) ^ 2) * cert.g (W a) +
            (∑ i, (X i a) ^ 2 *
              (cert.g (W a) - cert.g (W0 i a))) -
            ∑ i, X i a * R i a) := by
        apply uniformAverage_congr
        intro a
        rw [Finset.sum_add_distrib]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        ring
      _ = _ := by
        rw [uniformAverage_sub, uniformAverage_add]
  rw [hstein]
  have htriangle (x y z : ℝ) :
      |x + y - z| ≤ |x| + |y| + |z| := by
    calc
      |x + y - z| = |(x + y) + (-z)| := by ring
      _ ≤ |x + y| + |-z| := abs_add_le _ _
      _ ≤ (|x| + |y|) + |z| := by
        rw [abs_neg]
        gcongr
        exact abs_add_le _ _
      _ = |x| + |y| + |z| := by ring
  calc
    |uniformAverage A (fun a ↦
          (1 - ∑ i, (X i a) ^ 2) * cert.g (W a)) +
        uniformAverage A (fun a ↦
          ∑ i, (X i a) ^ 2 * (cert.g (W a) - cert.g (W0 i a))) -
        uniformAverage A (fun a ↦ ∑ i, X i a * R i a)| ≤
      |uniformAverage A (fun a ↦
          (1 - ∑ i, (X i a) ^ 2) * cert.g (W a))| +
        |uniformAverage A (fun a ↦
          ∑ i, (X i a) ^ 2 * (cert.g (W a) - cert.g (W0 i a)))| +
        |uniformAverage A (fun a ↦ ∑ i, X i a * R i a)| := by
      exact htriangle _ _ _
    _ ≤ cert.gBound *
          uniformAverage A (fun a ↦ |1 - ∑ i, (X i a) ^ 2|) +
        cert.lipBound *
          uniformAverage A (fun a ↦ ∑ i, (X i a) ^ 2 * |Y i a|) +
        cert.remainderBound *
          uniformAverage A (fun a ↦ ∑ i, |X i a| * (Y i a) ^ 2) := by
      gcongr
      · refine (abs_uniformAverage_le_uniformAverage_abs _).trans ?_
        calc
          uniformAverage A (fun a ↦
              |(1 - ∑ i, (X i a) ^ 2) * cert.g (W a)|) ≤
              uniformAverage A (fun a ↦
                cert.gBound * |1 - ∑ i, (X i a) ^ 2|) := by
            apply uniformAverage_mono
            intro a
            rw [abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (cert.g_abs_le _) (abs_nonneg _)
          _ = _ := by rw [uniformAverage_const_mul]
      · refine (abs_uniformAverage_le_uniformAverage_abs _).trans ?_
        calc
          uniformAverage A (fun a ↦
              |∑ i, (X i a) ^ 2 *
                (cert.g (W a) - cert.g (W0 i a))|) ≤
              uniformAverage A (fun a ↦
                cert.lipBound * ∑ i, (X i a) ^ 2 * |Y i a|) := by
            apply uniformAverage_mono
            intro a
            calc
              |∑ i, (X i a) ^ 2 *
                    (cert.g (W a) - cert.g (W0 i a))| ≤
                  ∑ i, |(X i a) ^ 2 *
                    (cert.g (W a) - cert.g (W0 i a))| :=
                Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i, cert.lipBound * ((X i a) ^ 2 * |Y i a|) := by
                apply Finset.sum_le_sum
                intro i _
                rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
                have hg := cert.g_sub_le (W a) (W0 i a)
                have hy : |W a - W0 i a| = |Y i a| := by
                  rw [show W a - W0 i a = Y i a by linarith [hsplit i a]]
                rw [hy] at hg
                nlinarith [sq_nonneg (X i a)]
              _ = cert.lipBound * ∑ i, (X i a) ^ 2 * |Y i a| := by
                rw [Finset.mul_sum]
          _ = _ := by rw [uniformAverage_const_mul]
      · refine (abs_uniformAverage_le_uniformAverage_abs _).trans ?_
        calc
          uniformAverage A (fun a ↦ |∑ i, X i a * R i a|) ≤
              uniformAverage A (fun a ↦
                cert.remainderBound *
                  ∑ i, |X i a| * (Y i a) ^ 2) := by
            apply uniformAverage_mono
            intro a
            calc
              |∑ i, X i a * R i a| ≤
                  ∑ i, |X i a * R i a| :=
                Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i, cert.remainderBound *
                    (|X i a| * (Y i a) ^ 2) := by
                apply Finset.sum_le_sum
                intro i _
                rw [abs_mul]
                have := hR i a
                nlinarith [abs_nonneg (X i a)]
              _ = cert.remainderBound *
                  ∑ i, |X i a| * (Y i a) ^ 2 := by
                rw [Finset.mul_sum]
          _ = _ := by rw [uniformAverage_const_mul]

end RandomSystems.SoP.CollisionStein
