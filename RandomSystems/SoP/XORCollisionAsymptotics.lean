/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORCollisionThreshold
import RandomSystems.SoP.CollisionCountPoissonFixed
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Poisson and normal targets for the XOR SoP collision statistic

This module formalizes the exact analytic targets on both sides of the
birthday transition.

For a Poisson variable of rate `lambda`, its mean absolute deviation is proved
from the PMF recurrence and a finite telescoping sum:

```text
E|X-lambda| = 2*lambda*Pr[X=floor(lambda)].
```

For a standard Gaussian, the corresponding integral is evaluated exactly as

```text
E|Z| = sqrt(2/pi).
```

The collision-proxy advantage is then factored into its dense Cauchy--Schwarz
scale and the standardized collision MAD.  This gives an exact finite error
term measuring the remaining normal approximation, and combines it with the
already-formalized Fourier remainder for the true adaptive SoP advantage.

The independent finite developments in `CollisionCountPoisson.lean` and
`CollisionCountPoissonFixed.lean` now supply both missing approximation inputs
without postulates.  An elementary
birthday-product argument proves the Poisson MAD limit at every limiting rate
strictly below one (including the central `q ~ sqrt N` rate `1/2`).  A planted-
edge size-bias recurrence extends this to every fixed finite rate, including
integer boundary rates.  A direct local-dependence Stein argument gives an
explicit finite normal-MAD error and the dense normal limit.  The terminal
theorem below transports that finite Stein error to the true adaptive SoP
advantage, adding only the already formalized Fourier remainder.
-/
noncomputable section
open scoped BigOperators NNReal
open Filter

namespace RandomSystems.SoP.CollisionAsymptotics

open ProbabilityTheory
open RandomSystems.SoP.CollisionProxy
open RandomSystems.SoP.XORBounds
open RandomSystems.Applications.XoP.ANOVA
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORCore
open RandomSystems.SoP.CollisionCountPoissonFixed
open RandomSystems.SoP.CollisionThreshold

theorem poisson_pmf_succ_recurrence (r : NNReal) (k : Nat) :
    ((k + 1 : Nat) : Real) * poissonPMFReal r (k + 1) =
      (r : Real) * poissonPMFReal r k := by
  unfold poissonPMFReal
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  have hk : (k : Real) + 1 ≠ 0 := by positivity
  field_simp [hk]

theorem poisson_mean_hasSum (r : NNReal) :
    HasSum (fun k : Nat => (k : Real) * poissonPMFReal r k) (r : Real) := by
  apply (hasSum_nat_add_iff' 1).mp
  have hs : HasSum (fun k => (r : Real) * poissonPMFReal r k)
      ((r : Real) - ∑ i ∈ Finset.range 1,
        (i : Real) * poissonPMFReal r i) := by
    simpa using (poissonPMFRealSum r).mul_left (r : Real)
  refine HasSum.congr_fun hs ?_
  intro k
  simpa only [Nat.cast_add, Nat.cast_one] using
    poisson_pmf_succ_recurrence r k

theorem poisson_centered_hasSum_zero (r : NNReal) :
    HasSum (fun k : Nat => ((k : Real) - (r : Real)) * poissonPMFReal r k) 0 := by
  have h := (poisson_mean_hasSum r).sub
    ((poissonPMFRealSum r).mul_left (r : Real))
  simpa [sub_mul] using h

theorem poisson_lower_deficiency_sum (r : NNReal) (m : Nat) :
    (∑ k ∈ Finset.range (m + 1),
      ((r : Real) - (k : Real)) * poissonPMFReal r k) =
      (r : Real) * poissonPMFReal r m := by
  calc
    (∑ k ∈ Finset.range (m + 1),
        ((r : Real) - (k : Real)) * poissonPMFReal r k) =
      (r : Real) *
          (∑ k ∈ Finset.range (m + 1), poissonPMFReal r k) -
        ∑ k ∈ Finset.range (m + 1),
          (k : Real) * poissonPMFReal r k := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (r : Real) *
          ((∑ k ∈ Finset.range m, poissonPMFReal r k) +
            poissonPMFReal r m) -
        ((∑ k ∈ Finset.range m,
            ((k + 1 : Nat) : Real) * poissonPMFReal r (k + 1)) + 0) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      norm_num
    _ = (r : Real) *
          ((∑ k ∈ Finset.range m, poissonPMFReal r k) +
            poissonPMFReal r m) -
        ∑ k ∈ Finset.range m,
          (r : Real) * poissonPMFReal r k := by
      simp only [add_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro k _hk
      exact poisson_pmf_succ_recurrence r k
    _ = (r : Real) * poissonPMFReal r m := by
      rw [← Finset.mul_sum]
      ring

theorem tsum_abs_eq_neg_two_mul_lower_sum
    (z : Nat → Real) (m : Nat) (hz : HasSum z 0)
    (hlower : ∀ k ∈ Finset.range (m + 1), z k ≤ 0)
    (hupper : ∀ k : Nat, 0 ≤ z (k + (m + 1))) :
    ∑' k : Nat, |z k| =
      -2 * ∑ k ∈ Finset.range (m + 1), z k := by
  have hsum := hz.summable.sum_add_tsum_nat_add (m + 1)
  have habsSum := hz.summable.abs.sum_add_tsum_nat_add (m + 1)
  have hlowerAbs :
      (∑ k ∈ Finset.range (m + 1), |z k|) =
        -(∑ k ∈ Finset.range (m + 1), z k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact abs_of_nonpos (hlower k hk)
  have hupperAbs :
      (∑' k : Nat, |z (k + (m + 1))|) =
        ∑' k : Nat, z (k + (m + 1)) := by
    congr 1
    funext k
    exact abs_of_nonneg (hupper k)
  rw [hz.tsum_eq] at hsum
  rw [hlowerAbs, hupperAbs] at habsSum
  linarith

/-- Mean absolute deviation of a Poisson law, written directly as its real
probability series. -/
def poissonMAD (r : NNReal) : Real :=
  ∑' k : Nat, |(k : Real) - (r : Real)| * poissonPMFReal r k

theorem poisson_mad_eq_two_mul_rate_mul_floor_pmf (r : NNReal) :
    poissonMAD r =
      2 * (r : Real) * poissonPMFReal r ⌊(r : Real)⌋₊ := by
  let m : Nat := ⌊(r : Real)⌋₊
  let z : Nat → Real := fun k =>
    ((k : Real) - (r : Real)) * poissonPMFReal r k
  have hz : HasSum z 0 := poisson_centered_hasSum_zero r
  have hlower : ∀ k ∈ Finset.range (m + 1), z k ≤ 0 := by
    intro k hk
    have hkNat : k ≤ m := by simpa using hk
    have hm : (m : Real) ≤ (r : Real) := by
      dsimp [m]
      exact Nat.floor_le (show 0 ≤ (r : Real) by positivity)
    have hkReal : (k : Real) ≤ (r : Real) := by
      exact (Nat.cast_le.mpr hkNat).trans hm
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hkReal)
      poissonPMFReal_nonneg
  have hupper : ∀ k : Nat, 0 ≤ z (k + (m + 1)) := by
    intro k
    have hm : (r : Real) < (m : Real) + 1 := by
      dsimp [m]
      exact Nat.lt_floor_add_one (r : Real)
    have hindex : (r : Real) ≤ (k + (m + 1) : Nat) := by
      have hmk : (m : Real) + 1 ≤ (k + (m + 1) : Nat) := by
        norm_num [Nat.cast_add]
      exact hm.le.trans hmk
    exact mul_nonneg (sub_nonneg.mpr hindex) poissonPMFReal_nonneg
  have habs := tsum_abs_eq_neg_two_mul_lower_sum z m hz hlower hupper
  have hpoint :
      (fun k : Nat => |z k|) =
        (fun k : Nat => |(k : Real) - (r : Real)| * poissonPMFReal r k) := by
    funext k
    dsimp [z]
    rw [abs_mul, abs_of_nonneg poissonPMFReal_nonneg]
  have hlowerSum :
      (∑ k ∈ Finset.range (m + 1), z k) =
        -((r : Real) * poissonPMFReal r m) := by
    rw [show (∑ k ∈ Finset.range (m + 1), z k) =
        -(∑ k ∈ Finset.range (m + 1),
          ((r : Real) - (k : Real)) * poissonPMFReal r k) by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _hk
      dsimp [z]
      ring]
    rw [poisson_lower_deficiency_sum]
  unfold poissonMAD
  rw [← hpoint, habs, hlowerSum]
  dsimp [m]
  ring

/-- The finite planted-edge development and the infinite-series definition
have exactly the same fixed-rate Poisson target. -/
theorem fixedPoissonMAD_eq_poissonMAD (r : NNReal) :
    fixedPoissonMAD r = poissonMAD r := by
  rw [poisson_mad_eq_two_mul_rate_mul_floor_pmf]
  rfl

/-- Birthday-transition Poisson parameter `M/N`. -/
def poissonCollisionRate (N q : Nat) : NNReal :=
  (pairCount q : NNReal) / (N : NNReal)

/-- Collision-proxy target obtained by replacing the exact collision count by
a Poisson variable of the same mean. -/
def poissonCollisionTarget (N q : Nat) : Real :=
  (N : Real) / (2 * ((N - 1 : Nat) : Real) ^ 2) *
    poissonMAD (poissonCollisionRate N q)

theorem poisson_collision_target_eq_floor_pmf
    {N q : Nat} (hN : 0 < N) :
    poissonCollisionTarget N q =
      (pairCount q : Real) / (((N - 1 : Nat) : Real) ^ 2) *
        poissonPMFReal (poissonCollisionRate N q)
          ⌊((poissonCollisionRate N q : NNReal) : Real)⌋₊ := by
  unfold poissonCollisionTarget
  rw [poisson_mad_eq_two_mul_rate_mul_floor_pmf]
  unfold poissonCollisionRate
  simp only [NNReal.coe_div, NNReal.coe_natCast]
  have hNR : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hNR]

/-- Mean absolute value of a standard real Gaussian. -/
def standardNormalMAD : Real :=
  ∫ x : Real, |x| * gaussianPDFReal 0 1 x

theorem integral_Ioi_mul_exp_neg_half_sq :
    (∫ x : Real in Set.Ioi 0, x * Real.exp (-(1 / 2 : Real) * x ^ 2)) = 1 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : Real)) (q := (1 : Real)) (b := (1 / 2 : Real))
    (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [Real.rpow_one]
  · norm_num [Real.Gamma_one]

theorem standard_normal_mad_eq_sqrt_two_div_pi :
    standardNormalMAD = Real.sqrt (2 / Real.pi) := by
  have heven (x : Real) :
      gaussianPDFReal 0 1 |x| = gaussianPDFReal 0 1 x := by
    simp [gaussianPDFReal, sq_abs]
  have hpoint :
      (fun x : Real => |x| * gaussianPDFReal 0 1 x) =
        (fun x => (fun t : Real => t * gaussianPDFReal 0 1 t) |x|) := by
    funext x
    change |x| * gaussianPDFReal 0 1 x =
      |x| * gaussianPDFReal 0 1 |x|
    exact congrArg (fun t => |x| * t) (heven x).symm
  unfold standardNormalMAD
  rw [hpoint, integral_comp_abs
    (f := fun t : Real => t * gaussianPDFReal 0 1 t)]
  have hI :
      (∫ x : Real in Set.Ioi 0, x * gaussianPDFReal 0 1 x) =
        (Real.sqrt (2 * Real.pi))⁻¹ := by
    unfold gaussianPDFReal
    norm_num
    rw [show (fun x : Real =>
        x * (((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
          Real.exp (-(x ^ 2) / 2))) =
        (fun x => ((Real.sqrt Real.pi)⁻¹ * (Real.sqrt 2)⁻¹) *
          (x * Real.exp (-(1 / 2 : Real) * x ^ 2))) by
      funext x
      have hexp : -(x ^ 2) / 2 = -(1 / 2 : Real) * x ^ 2 := by ring
      rw [hexp]
      ring]
    rw [MeasureTheory.integral_const_mul, integral_Ioi_mul_exp_neg_half_sq]
    ring
  rw [hI]
  have hsqrt2 : Real.sqrt (2 : Real) ≠ 0 := by positivity
  have hsqrtPi : Real.sqrt Real.pi ≠ 0 := by positivity
  rw [Real.sqrt_div (by norm_num : (0 : Real) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
  have hsquare : Real.sqrt (2 : Real) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  field_simp [hsqrt2, hsqrtPi]
  nlinarith

/-- Mean absolute deviation of the collision count after exact variance
normalization. -/
def standardizedCollisionMAD
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) : Real :=
  uniformAverage (Fin q → G)
      (fun y => |centeredCollisionCount G q y|) /
    Real.sqrt
      ((pairCount q : Real) * ((Fintype.card G - 1 : Nat) : Real) /
        (Fintype.card G : Real) ^ 2)

theorem collision_advantage_eq_dense_mul_standardized_mad
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    collisionAdvantage G q =
      denseBound G q * standardizedCollisionMAD G q := by
  let V : Real :=
    (pairCount q : Real) * ((Fintype.card G - 1 : Nat) : Real) /
      (Fintype.card G : Real) ^ 2
  have hM : 0 < (pairCount q : Real) := by
    rw [pairCount_eq]
    exact_mod_cast Nat.choose_pos hq2
  have hNm1 : 0 < ((Fintype.card G - 1 : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt hN
  have hcard : 0 < (Fintype.card G : Real) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hV : 0 < V := by
    dsimp [V]
    positivity
  have hsqrtV : Real.sqrt V ≠ 0 := Real.sqrt_ne_zero'.mpr hV
  rw [collisionAdvantage_eq (G := G) q hN,
    ← denseBound_raw_eq (G := G) q hN]
  unfold standardizedCollisionMAD
  change
    (Fintype.card G : Real) /
          (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) *
        uniformAverage (Fin q → G)
          (fun y => |centeredCollisionCount G q y|) =
      ((Fintype.card G : Real) /
          (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) *
        Real.sqrt V) *
      (uniformAverage (Fin q → G)
          (fun y => |centeredCollisionCount G q y|) / Real.sqrt V)
  field_simp [hsqrtV]

/-- The collision proxy with its standardized collision count replaced by a
standard Gaussian. -/
def normalCollisionTarget
    (G : Type*) [Fintype G] (q : Nat) : Real :=
  denseBound G q * standardNormalMAD

theorem normal_collision_target_eq_closed
    (G : Type*) [Fintype G] (q : Nat) :
    normalCollisionTarget G q =
      denseBound G q * Real.sqrt (2 / Real.pi) := by
  rw [normalCollisionTarget, standard_normal_mad_eq_sqrt_two_div_pi]

theorem normal_collision_target_xor_eq_expanded (n q : Nat) :
    normalCollisionTarget (XorSpace n) q =
      Real.sqrt (q.choose 2 : Real) * Real.sqrt (2 / Real.pi) /
        (2 * ((2 ^ n - 1 : Nat) : Real) *
          Real.sqrt ((2 ^ n - 1 : Nat) : Real)) := by
  rw [normal_collision_target_eq_closed]
  unfold denseBound
  simp only [pairCount_eq, card_xorSpace]
  ring

/-- Exact residual left by the normal approximation at the one-dimensional
collision statistic. -/
def collisionNormalMADError
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) : Real :=
  |standardizedCollisionMAD G q - standardNormalMAD|

private theorem finiteNormal_collisionCount_eq
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    RandomSystems.SoP.CollisionCountNormal.collisionCount G q y =
      CollisionProxy.collisionCount (G := G) q y := by
  unfold RandomSystems.SoP.CollisionCountNormal.collisionCount
    RandomSystems.SoP.CollisionCountNormal.edgeIndicator
    CollisionProxy.collisionCount
  rw [RandomSystems.Applications.SoP.pairCollisionCountReal_eq_pairCollisionCountNat]
  unfold RandomSystems.Applications.SoP.pairCollisionCountNat
  push_cast
  rfl

private theorem finiteNormal_centeredCollisionCount_eq
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount G q y =
      CollisionProxy.centeredCollisionCount G q y := by
  unfold RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount
    CollisionProxy.centeredCollisionCount
  rw [finiteNormal_collisionCount_eq]
  rfl

/-- The lightweight collision-count average is the same finite average used
by the SoP proxy, before standardization. -/
theorem finiteNormal_collisionMAD_eq
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) :
    RandomSystems.SoP.CollisionStein.uniformAverage (Fin q → G)
        (fun y =>
          |RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount
            G q y|) =
      RandomSystems.Applications.XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y => |CollisionProxy.centeredCollisionCount G q y|) := by
  rw [show (fun y : Fin q → G =>
      |RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount G q y|) =
      (fun y => |CollisionProxy.centeredCollisionCount G q y|) by
        funext y
        rw [finiteNormal_centeredCollisionCount_eq]]
  unfold RandomSystems.SoP.CollisionStein.uniformAverage
    RandomSystems.SoP.XORFourier.average
    RandomSystems.Applications.XoP.ANOVA.uniformAverage
  rfl

theorem finiteNormal_centeredCollisionCount_comp_equiv
    {G H : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (q : Nat) (y : Fin q → G) :
    RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount H q
        (fun i => e (y i)) =
      RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount G q y := by
  unfold RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount
    RandomSystems.SoP.CollisionCountNormal.collisionCount
    RandomSystems.SoP.CollisionCountNormal.collisionMean
    RandomSystems.SoP.CollisionCountNormal.edgeIndicator
  rw [Fintype.card_congr e]
  apply congrArg (fun z : Real => z -
    (RandomSystems.SoP.CollisionCountNormal.edgeCount q : Real) /
      (Fintype.card H : Real))
  apply Finset.sum_congr rfl
  intro a _ha
  simp

/-- The collision-count MAD depends only on the carrier cardinality. -/
theorem finiteNormal_collisionMAD_equiv
    {G H : Type*} [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H]
    (e : G ≃ H) (q : Nat) :
    RandomSystems.SoP.CollisionStein.uniformAverage (Fin q → G)
        (fun y =>
          |RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount
            G q y|) =
      RandomSystems.SoP.CollisionStein.uniformAverage (Fin q → H)
        (fun y =>
          |RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount
            H q y|) := by
  let E : (Fin q → G) ≃ (Fin q → H) :=
    Equiv.arrowCongr (Equiv.refl (Fin q)) e
  unfold RandomSystems.SoP.CollisionStein.uniformAverage
    RandomSystems.SoP.XORFourier.average
  have hsum :
      (∑ y : Fin q → G,
          |RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount
            G q y|) =
        ∑ z : Fin q → H,
          |RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount
            H q z| := by
    rw [← Equiv.sum_comp E]
    apply Finset.sum_congr rfl
    intro y _hy
    rw [show E y = fun i => e (y i) by rfl,
      finiteNormal_centeredCollisionCount_comp_equiv e q y]
  rw [hsum, Fintype.card_congr E]

/-- The finite collision proxy depends only on the alphabet size, so the
standalone `Fin N` development is exactly the proxy for every finite carrier. -/
theorem collisionAdvantage_eq_finiteCollisionProxyAdvantage
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hN : 2 ≤ Fintype.card G) :
    collisionAdvantage G q =
      RandomSystems.SoP.CollisionCountPoisson.finiteCollisionProxyAdvantage
        (Fintype.card G) q := by
  rw [CollisionProxy.collisionAdvantage_eq q hN]
  unfold RandomSystems.SoP.CollisionCountPoisson.finiteCollisionProxyAdvantage
    RandomSystems.SoP.CollisionCountPoisson.finiteCollisionMAD
  rw [← finiteNormal_collisionMAD_eq]
  rw [finiteNormal_collisionMAD_equiv (Fintype.equivFin G) q]

/-- The standalone finite collision proxy is definitionally the same
one-dimensional representative used by the SoP adaptive endpoint. -/
theorem collisionAdvantage_fin_eq_finiteCollisionProxyAdvantage
    {N q : Nat} (hN : 2 ≤ N) :
    collisionAdvantage (Fin N) q =
      RandomSystems.SoP.CollisionCountPoisson.finiteCollisionProxyAdvantage
        N q := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  simpa using collisionAdvantage_eq_finiteCollisionProxyAdvantage
    (Fin N) q (by simpa using hN)

private def cardRemainderEnergyBound (N q : Nat) : Real :=
  16 * (q.choose 3 : Real) /
      ((((N - 1 : Nat) : Real) ^ 3) *
        (((N - 2 : Nat) : Real) ^ 3)) +
    (1152 / 7 : Real) * (q : Real) ^ 4 / ((N : Real) ^ 6) +
    8 * (q : Real) ^ 4 / ((N : Real) ^ 8)

private def cardRemainderErrorBound (N q : Nat) : Real :=
  (1 / 2 : Real) * Real.sqrt (cardRemainderEnergyBound N q)

private theorem cardRemainderEnergyBound_nonneg (N q : Nat) :
    0 ≤ cardRemainderEnergyBound N q := by
  unfold cardRemainderEnergyBound
  positivity

/-- The higher broken-cycle remainder is lower order at every fixed birthday
rate.  In fact, the conclusion only needs `q/N → 0`. -/
private theorem tendsto_card_mul_cardRemainderErrorBound_zero
    (N q : Nat → Nat)
    (hN : Tendsto N atTop atTop)
    (hsmall : Tendsto (fun t => (q t : Real) / (N t : Real))
      atTop (nhds 0)) :
    Tendsto (fun t => (N t : Real) *
        cardRemainderErrorBound (N t) (q t))
      atTop (nhds 0) := by
  have hNreal : Tendsto (fun t => (N t : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hinv : Tendsto (fun t => (1 : Real) / (N t : Real))
      atTop (nhds 0) := by
    simpa [one_div] using tendsto_inv_atTop_zero.comp hNreal
  have hNfour : ∀ᶠ t in atTop, 4 ≤ N t :=
    hN (eventually_ge_atTop 4)
  have hratio (c : Nat) : Tendsto
      (fun t => (N t : Real) / ((N t - c : Nat) : Real))
      atTop (nhds 1) := by
    have hsub : Tendsto (fun t => N t - c) atTop atTop :=
      (tendsto_sub_atTop_nat c).comp hN
    have hsubReal : Tendsto (fun t => ((N t - c : Nat) : Real))
        atTop atTop := tendsto_natCast_atTop_atTop.comp hsub
    have hinvSub : Tendsto
        (fun t => (1 : Real) / ((N t - c : Nat) : Real))
        atTop (nhds 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero.comp hsubReal
    have hc : Tendsto (fun _t : Nat => (c : Real))
        atTop (nhds (c : Real)) := tendsto_const_nhds
    have hadd := (tendsto_const_nhds :
      Tendsto (fun _t : Nat => (1 : Real)) atTop (nhds 1)).add
        (hc.mul hinvSub)
    have hadd' : Tendsto
        (fun t => (1 : Real) + (c : Real) /
          ((N t - c : Nat) : Real)) atTop (nhds 1) := by
      simpa [div_eq_mul_inv] using hadd
    apply hadd'.congr'
    have hNc : ∀ᶠ t in atTop, c + 1 ≤ N t :=
      hN (eventually_ge_atTop (c + 1))
    filter_upwards [hNc] with t ht
    rw [Nat.cast_sub (by omega : c ≤ N t)]
    have hden : (N t : Real) - (c : Real) ≠ 0 := by
      have hcast : ((c + 1 : Nat) : Real) ≤ (N t : Real) := by
        exact_mod_cast ht
      push_cast at hcast
      linarith
    field_simp [hden]
    ring
  have hterm1 : Tendsto (fun t =>
      16 * ((q t : Real) / (N t : Real)) ^ 3 *
        (1 / (N t : Real)) *
        ((N t : Real) / ((N t - 1 : Nat) : Real)) ^ 3 *
        ((N t : Real) / ((N t - 2 : Nat) : Real)) ^ 3)
      atTop (nhds 0) := by
    have h16 : Tendsto (fun _t : Nat => (16 : Real)) atTop (nhds 16) :=
      tendsto_const_nhds
    simpa using ((((h16.mul (hsmall.pow 3)).mul hinv).mul
      ((hratio 1).pow 3)).mul ((hratio 2).pow 3))
  have hterm2 : Tendsto (fun t =>
      (1152 / 7 : Real) * ((q t : Real) / (N t : Real)) ^ 4)
      atTop (nhds 0) := by
    have hc : Tendsto (fun _t : Nat => (1152 / 7 : Real))
        atTop (nhds (1152 / 7 : Real)) := tendsto_const_nhds
    simpa using hc.mul (hsmall.pow 4)
  have hterm3 : Tendsto (fun t =>
      8 * ((q t : Real) / (N t : Real)) ^ 4 *
        (1 / (N t : Real)) ^ 2)
      atTop (nhds 0) := by
    have h8 : Tendsto (fun _t : Nat => (8 : Real)) atTop (nhds 8) :=
      tendsto_const_nhds
    simpa using (h8.mul (hsmall.pow 4)).mul (hinv.pow 2)
  have henvelope := (hterm1.add hterm2).add hterm3
  have hscaledEnergy : Tendsto
      (fun t => (N t : Real) ^ 2 *
        cardRemainderEnergyBound (N t) (q t))
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun t =>
        mul_nonneg (sq_nonneg _)
          (cardRemainderEnergyBound_nonneg (N t) (q t)))
    · filter_upwards [hNfour] with t hNt
      have hNpos : (0 : Real) < (N t : Real) := by positivity
      have hN1pos : (0 : Real) < ((N t - 1 : Nat) : Real) := by
        exact_mod_cast (by omega : 0 < N t - 1)
      have hN2pos : (0 : Real) < ((N t - 2 : Nat) : Real) := by
        exact_mod_cast (by omega : 0 < N t - 2)
      have hchoose : (q t).choose 3 ≤ (q t) ^ 3 := Nat.choose_le_pow _ _
      calc
        (N t : Real) ^ 2 * cardRemainderEnergyBound (N t) (q t) ≤
            (N t : Real) ^ 2 *
              (16 * ((q t : Real) ^ 3) /
                  (((N t - 1 : Nat) : Real) ^ 3 *
                    ((N t - 2 : Nat) : Real) ^ 3) +
                (1152 / 7 : Real) * (q t : Real) ^ 4 /
                  (N t : Real) ^ 6 +
                8 * (q t : Real) ^ 4 / (N t : Real) ^ 8) := by
          unfold cardRemainderEnergyBound
          gcongr
          exact_mod_cast hchoose
        _ = 16 * ((q t : Real) / (N t : Real)) ^ 3 *
              (1 / (N t : Real)) *
              ((N t : Real) / ((N t - 1 : Nat) : Real)) ^ 3 *
              ((N t : Real) / ((N t - 2 : Nat) : Real)) ^ 3 +
            (1152 / 7 : Real) *
              ((q t : Real) / (N t : Real)) ^ 4 +
            8 * ((q t : Real) / (N t : Real)) ^ 4 *
              (1 / (N t : Real)) ^ 2 := by
          field_simp [hNpos.ne', hN1pos.ne', hN2pos.ne']
    · simpa using henvelope
  have hsqrt : Tendsto (fun t =>
      Real.sqrt ((N t : Real) ^ 2 *
        cardRemainderEnergyBound (N t) (q t)))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hscaledEnergy
  have hhalf : Tendsto (fun _t : Nat => (1 / 2 : Real))
      atTop (nhds (1 / 2 : Real)) := tendsto_const_nhds
  have hfinal := hhalf.mul hsqrt
  have hfinal' : Tendsto (fun t =>
      (1 / 2 : Real) * Real.sqrt ((N t : Real) ^ 2 *
        cardRemainderEnergyBound (N t) (q t)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hfinal
  apply hfinal'.congr'
  filter_upwards with t
  unfold cardRemainderErrorBound
  rw [Real.sqrt_mul (sq_nonneg (N t : Real)),
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity : (0 : Real) ≤ N t)]
  ring

theorem tendsto_card_mul_remainderErrorBound_zero
    (n q : Nat → Nat)
    (hN : Tendsto (fun t => 2 ^ n t) atTop atTop)
    (hsmall : Tendsto
      (fun t => (q t : Real) / ((2 ^ n t : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto (fun t => ((2 ^ n t : Nat) : Real) *
        remainderErrorBound (n t) (q t)) atTop (nhds 0) := by
  simpa [cardRemainderErrorBound, cardRemainderEnergyBound,
    remainderErrorBound, remainderEnergyBound] using
      tendsto_card_mul_cardRemainderErrorBound_zero
        (fun t => 2 ^ n t) q hN hsmall

/-- Exact finite birthday target for the collision proxy. -/
def birthdayCollisionTarget (N q : Nat) : Real :=
  (pairCount q : Real) / ((N - 1 : Nat) : Real) ^ 2 *
    RandomSystems.SoP.CollisionCountPoisson.birthdayProduct N q

/-- Below collision rate one, the SoP collision proxy is exactly its birthday
target.  This is the finite bridge from the elementary zero-collision argument
to the proxy used by the adaptive SoP proof. -/
theorem collision_advantage_eq_birthday_collision_target
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hN : 2 ≤ Fintype.card G)
    (hrate : RandomSystems.SoP.CollisionCountPoisson.birthdayRate
      (Fintype.card G) q ≤ 1) :
    collisionAdvantage G q =
      birthdayCollisionTarget (Fintype.card G) q := by
  have hmean :
      RandomSystems.SoP.CollisionCountNormal.collisionMean G q ≤ 1 := by
    simpa [RandomSystems.SoP.CollisionCountNormal.collisionMean,
      RandomSystems.SoP.CollisionCountPoisson.birthdayRate,
      RandomSystems.SoP.CollisionCountNormal.edgeCount_eq_choose,
      pairCount_eq] using hrate
  rw [CollisionProxy.collisionAdvantage_eq q hN]
  rw [← finiteNormal_collisionMAD_eq]
  rw [RandomSystems.SoP.CollisionCountPoisson.collisionMAD_eq_two_mul_mean_mul_collisionFree
    G hmean]
  rw [RandomSystems.SoP.CollisionCountPoisson.collisionFreeProbability_eq_birthdayProduct]
  unfold birthdayCollisionTarget
    RandomSystems.SoP.CollisionCountNormal.collisionMean
  rw [RandomSystems.SoP.CollisionCountNormal.edgeCount_eq_choose,
    ← pairCount_eq]
  have hcard : (Fintype.card G : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  field_simp [hcard]

/-- The lightweight finite-Stein normalization is exactly the collision MAD
normalization used by the SoP proxy layer. -/
theorem finiteNormal_standardizedCollisionMAD_eq
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) :
    RandomSystems.SoP.CollisionStein.uniformAverage (Fin q → G)
        (fun y =>
          |RandomSystems.SoP.CollisionCountNormal.standardizedCollisionCount
            G q y|) =
      standardizedCollisionMAD G q := by
  unfold RandomSystems.SoP.CollisionCountNormal.standardizedCollisionCount
    standardizedCollisionMAD
  rw [show (fun y : Fin q → G =>
      |RandomSystems.SoP.CollisionCountNormal.centeredCollisionCount G q y /
        RandomSystems.SoP.CollisionCountNormal.collisionSigma G q|) =
      (fun y => |CollisionProxy.centeredCollisionCount G q y| /
        Real.sqrt
          ((pairCount q : ℝ) * ((Fintype.card G - 1 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2)) by
        funext y
        rw [abs_div, finiteNormal_centeredCollisionCount_eq]
        unfold RandomSystems.SoP.CollisionCountNormal.collisionSigma
          RandomSystems.SoP.CollisionCountNormal.collisionVariance
        rw [abs_of_nonneg (Real.sqrt_nonneg _)]
        rfl]
  rw [show (fun y : Fin q → G =>
      |CollisionProxy.centeredCollisionCount G q y| /
        Real.sqrt
          ((pairCount q : ℝ) * ((Fintype.card G - 1 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2)) =
      (fun y => (1 / Real.sqrt
          ((pairCount q : ℝ) * ((Fintype.card G - 1 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2)) *
        |CollisionProxy.centeredCollisionCount G q y|) by
      funext y
      ring]
  rw [RandomSystems.SoP.CollisionStein.uniformAverage_const_mul]
  unfold RandomSystems.SoP.CollisionStein.uniformAverage
    RandomSystems.SoP.XORFourier.average
    RandomSystems.Applications.XoP.ANOVA.uniformAverage
  ring

/-- The formerly abstract normal-MAD residual now has a compiled explicit
finite upper bound. -/
theorem collisionNormalMADError_le_finiteNormalErrorBound
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hq : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    collisionNormalMADError G q ≤
      RandomSystems.SoP.CollisionCountNormal.collisionNormalErrorBound G q := by
  unfold collisionNormalMADError
  rw [← finiteNormal_standardizedCollisionMAD_eq]
  rw [standard_normal_mad_eq_sqrt_two_div_pi]
  exact
    RandomSystems.SoP.CollisionCountNormal.standardizedCollisionMAD_sub_normal_le_errorBound
      G hq hN

theorem abs_collision_advantage_sub_normal_target
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hN : 2 ≤ Fintype.card G) :
    |collisionAdvantage G q - normalCollisionTarget G q| =
      denseBound G q * collisionNormalMADError G q := by
  rw [collision_advantage_eq_dense_mul_standardized_mad G q hq2 hN]
  unfold normalCollisionTarget collisionNormalMADError
  rw [← mul_sub, abs_mul]
  have hdense : 0 ≤ denseBound G q := by
    unfold denseBound
    positivity
  rw [abs_of_nonneg hdense]

/-- Finite normal-target certificate.  The only term not already bounded in
the SoP development is the explicit one-dimensional MAD approximation error. -/
theorem abs_advantage_sub_normal_collision_target_le
    {n q : Nat} (hn : 10 ≤ n) (hq2 : 2 ≤ q)
    (h2q : 2 * q ≤ 2 ^ n) :
    |RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        normalCollisionTarget (XorSpace n) q| ≤
      remainderErrorBound n q +
        denseBound (XorSpace n) q *
          collisionNormalMADError (XorSpace n) q := by
  let adv : Real :=
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
      (q := q) (RandomSystems.SoP.xop (XorSpace n))
        (RandomSystems.SoP.urf (XorSpace n))
  let col : Real := collisionAdvantage (XorSpace n) q
  let target : Real := normalCollisionTarget (XorSpace n) q
  calc
    |adv - target| = |(adv - col) + (col - target)| := by ring_nf
    _ ≤ |adv - col| + |col - target| := abs_add_le _ _
    _ ≤ remainderErrorBound n q + |col - target| := by
      gcongr
      simpa [adv, col] using abs_advantage_sub_collisionAdvantage_le hn h2q
    _ = remainderErrorBound n q +
        denseBound (XorSpace n) q *
          collisionNormalMADError (XorSpace n) q := by
      rw [abs_collision_advantage_sub_normal_target
        (XorSpace n) q hq2 (by
          simp only [card_xorSpace]
          have h := hundred_mul_le_two_pow hn
          omega)]

/-- Closed finite normal-target theorem: the collision-MAD placeholder in the
previous transfer theorem is discharged by the explicit local Stein bound. -/
theorem abs_advantage_sub_normal_collision_target_le_finiteStein
    {n q : Nat} (hn : 10 ≤ n) (hq2 : 2 ≤ q)
    (h2q : 2 * q ≤ 2 ^ n) :
    |RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        normalCollisionTarget (XorSpace n) q| ≤
      remainderErrorBound n q +
        denseBound (XorSpace n) q *
          RandomSystems.SoP.CollisionCountNormal.collisionNormalErrorBound
            (XorSpace n) q := by
  have hcard : 2 ≤ Fintype.card (XorSpace n) := by
    simp only [card_xorSpace]
    have h := hundred_mul_le_two_pow hn
    omega
  have herr := collisionNormalMADError_le_finiteNormalErrorBound
    (XorSpace n) hq2 hcard
  have hdense : 0 ≤ denseBound (XorSpace n) q := by
    unfold denseBound
    positivity
  exact (abs_advantage_sub_normal_collision_target_le hn hq2 h2q).trans
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left herr hdense))

/-- Closed finite birthday-target theorem for the true adaptive XOR SoP
advantage.  At every rate at most one, the only remaining error is the already
formalized higher-order SoP remainder. -/
theorem abs_advantage_sub_birthday_collision_target_le
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (hrate : RandomSystems.SoP.CollisionCountPoisson.birthdayRate
      (2 ^ n) q ≤ 1) :
    |RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) -
        birthdayCollisionTarget (2 ^ n) q| ≤
      remainderErrorBound n q := by
  have hcard : 2 ≤ Fintype.card (XorSpace n) := by
    simp only [card_xorSpace]
    have h := hundred_mul_le_two_pow hn
    omega
  have hrate' :
      RandomSystems.SoP.CollisionCountPoisson.birthdayRate
        (Fintype.card (XorSpace n)) q ≤ 1 := by
    simpa [card_xorSpace] using hrate
  have hbase := abs_advantage_sub_collisionAdvantage_le hn h2q
  rw [collision_advantage_eq_birthday_collision_target
    (XorSpace n) q hcard hrate'] at hbase
  simpa [card_xorSpace] using hbase

private theorem tendsto_of_abs_sub_le_tendsto_zero
    {f g e : Nat → Real} {a : Real}
    (hg : Tendsto g atTop (nhds a))
    (he : Tendsto e atTop (nhds 0))
    (hfg : ∀ᶠ t in atTop, |f t - g t| ≤ e t) :
    Tendsto f atTop (nhds a) := by
  have habs : Tendsto (fun t => |f t - g t|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun t => abs_nonneg _)
    · exact hfg
    · exact he
  have hdiff : Tendsto (fun t => f t - g t) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using habs
  have hsum := hdiff.add hg
  convert hsum using 1
  · funext t
    ring
  · ring

/-- Full sharp fixed-rate Poisson interpolation for the true adaptive XOR
sum-of-two-permutations advantage. -/
theorem tendsto_card_mul_adaptiveTranscriptAdvantage_fixedPoisson
    (n q : Nat → Nat) (r : NNReal)
    (hN : Tendsto (fun t => 2 ^ n t) atTop atTop)
    (hn : ∀ᶠ t in atTop, 10 ≤ n t)
    (h2q : ∀ᶠ t in atTop, 2 * q t ≤ 2 ^ n t)
    (hrate : Tendsto (fun t =>
      RandomSystems.SoP.CollisionCountPoisson.birthdayRate
        (2 ^ n t) (q t)) atTop (nhds (r : Real)))
    (hsmall : Tendsto
      (fun t => (q t : Real) / ((2 ^ n t : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto (fun t => ((2 ^ n t : Nat) : Real) *
        RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q t) (RandomSystems.SoP.xop (XorSpace (n t)))
            (RandomSystems.SoP.urf (XorSpace (n t))))
      atTop (nhds (fixedPoissonAdvantageConstant r)) := by
  have hproxy :=
    tendsto_card_mul_finiteCollisionProxyAdvantage_fixedPoisson
      (fun t => 2 ^ n t) q r hN h2q hrate hsmall
  have hrem := tendsto_card_mul_remainderErrorBound_zero n q hN hsmall
  apply tendsto_of_abs_sub_le_tendsto_zero hproxy hrem
  filter_upwards [hn, h2q] with t hnt h2qt
  let N : Nat := 2 ^ n t
  let adv : Real :=
    RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
      (q := q t) (RandomSystems.SoP.xop (XorSpace (n t)))
        (RandomSystems.SoP.urf (XorSpace (n t)))
  let proxy : Real :=
    RandomSystems.SoP.CollisionCountPoisson.finiteCollisionProxyAdvantage
      N (q t)
  have hcard : 2 ≤ Fintype.card (XorSpace (n t)) := by
    simp only [card_xorSpace]
    have hlarge := hundred_mul_le_two_pow hnt
    omega
  have heq : collisionAdvantage (XorSpace (n t)) (q t) = proxy := by
    dsimp [proxy, N]
    simpa [card_xorSpace] using
      collisionAdvantage_eq_finiteCollisionProxyAdvantage
        (XorSpace (n t)) (q t) hcard
  have hbase := abs_advantage_sub_collisionAdvantage_le hnt h2qt
  change |(N : Real) * adv - (N : Real) * proxy| ≤
    (N : Real) * remainderErrorBound (n t) (q t)
  calc
    |(N : Real) * adv - (N : Real) * proxy| =
        (N : Real) * |adv - collisionAdvantage (XorSpace (n t)) (q t)| := by
      rw [heq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity :
        (0 : Real) ≤ N)]
    _ ≤ (N : Real) * remainderErrorBound (n t) (q t) := by
      exact mul_le_mul_of_nonneg_left (by simpa [adv] using hbase) (by positivity)

/-- The concrete centered-collision threshold test attains the same sharp
fixed-rate constant, so the preceding asymptotic is a matching attack rather
than only an upper bound. -/
theorem tendsto_card_mul_collisionThresholdTestGap_fixedPoisson
    (n q : Nat → Nat) (r : NNReal)
    (hN : Tendsto (fun t => 2 ^ n t) atTop atTop)
    (hn : ∀ᶠ t in atTop, 10 ≤ n t)
    (hq0 : ∀ᶠ t in atTop, 0 < q t)
    (h2q : ∀ᶠ t in atTop, 2 * q t ≤ 2 ^ n t)
    (hrate : Tendsto (fun t =>
      RandomSystems.SoP.CollisionCountPoisson.birthdayRate
        (2 ^ n t) (q t)) atTop (nhds (r : Real)))
    (hsmall : Tendsto
      (fun t => (q t : Real) / ((2 ^ n t : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto (fun t => ((2 ^ n t : Nat) : Real) *
        collisionThresholdTestGap (n t) (q t))
      atTop (nhds (fixedPoissonAdvantageConstant r)) := by
  have hproxy :=
    tendsto_card_mul_finiteCollisionProxyAdvantage_fixedPoisson
      (fun t => 2 ^ n t) q r hN h2q hrate hsmall
  have hrem := tendsto_card_mul_remainderErrorBound_zero n q hN hsmall
  apply tendsto_of_abs_sub_le_tendsto_zero hproxy hrem
  filter_upwards [hn, hq0, h2q] with t hnt hq0t h2qt
  let N : Nat := 2 ^ n t
  let proxy : Real :=
    RandomSystems.SoP.CollisionCountPoisson.finiteCollisionProxyAdvantage
      N (q t)
  have hcard : 2 ≤ Fintype.card (XorSpace (n t)) := by
    simp only [card_xorSpace]
    have hlarge := hundred_mul_le_two_pow hnt
    omega
  have heq : collisionAdvantage (XorSpace (n t)) (q t) = proxy := by
    dsimp [proxy, N]
    simpa [card_xorSpace] using
      collisionAdvantage_eq_finiteCollisionProxyAdvantage
        (XorSpace (n t)) (q t) hcard
  have hbase := abs_collision_threshold_gap_sub_proxy_le_error
    hnt hq0t h2qt
  change |(N : Real) * collisionThresholdTestGap (n t) (q t) -
      (N : Real) * proxy| ≤
    (N : Real) * remainderErrorBound (n t) (q t)
  calc
    |(N : Real) * collisionThresholdTestGap (n t) (q t) -
        (N : Real) * proxy| =
      (N : Real) *
        |collisionThresholdTestGap (n t) (q t) -
          collisionAdvantage (XorSpace (n t)) (q t)| := by
      rw [heq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity :
        (0 : Real) ≤ N)]
    _ ≤ (N : Real) * remainderErrorBound (n t) (q t) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)

/-- At every positive fixed Poisson rate, the explicit collision-threshold
test is asymptotically optimal: its signed gap divided by the maximum adaptive
advantage tends to one.  This is the literal matching-attack form of the two
preceding scaled limits. -/
theorem tendsto_collisionThresholdTestGap_div_adaptiveAdvantage_fixedPoisson
    (n q : Nat → Nat) (r : NNReal) (hr : 0 < r)
    (hN : Tendsto (fun t => 2 ^ n t) atTop atTop)
    (hn : ∀ᶠ t in atTop, 10 ≤ n t)
    (hq0 : ∀ᶠ t in atTop, 0 < q t)
    (h2q : ∀ᶠ t in atTop, 2 * q t ≤ 2 ^ n t)
    (hrate : Tendsto (fun t =>
      RandomSystems.SoP.CollisionCountPoisson.birthdayRate
        (2 ^ n t) (q t)) atTop (nhds (r : Real)))
    (hsmall : Tendsto
      (fun t => (q t : Real) / ((2 ^ n t : Nat) : Real))
      atTop (nhds 0)) :
    Tendsto (fun t =>
        collisionThresholdTestGap (n t) (q t) /
          RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
            (q := q t) (RandomSystems.SoP.xop (XorSpace (n t)))
              (RandomSystems.SoP.urf (XorSpace (n t))))
      atTop (nhds 1) := by
  have hadv := tendsto_card_mul_adaptiveTranscriptAdvantage_fixedPoisson
    n q r hN hn h2q hrate hsmall
  have hattack := tendsto_card_mul_collisionThresholdTestGap_fixedPoisson
    n q r hN hn hq0 h2q hrate hsmall
  have hcpos : 0 < fixedPoissonAdvantageConstant r := by
    unfold fixedPoissonAdvantageConstant
    exact mul_pos (by exact_mod_cast hr) (poissonPMFReal_pos hr)
  have hratio := hattack.div hadv hcpos.ne'
  rw [div_self hcpos.ne'] at hratio
  have hscaled : Tendsto (fun t =>
      (((2 ^ n t : Nat) : Real) * collisionThresholdTestGap (n t) (q t)) /
        (((2 ^ n t : Nat) : Real) *
          RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
            (q := q t) (RandomSystems.SoP.xop (XorSpace (n t)))
              (RandomSystems.SoP.urf (XorSpace (n t)))))
      atTop (nhds 1) := hratio
  apply hscaled.congr'
  exact Eventually.of_forall (fun t => by
    have hpow : (((2 ^ n t : Nat) : Real)) ≠ 0 := by positivity
    field_simp)

end RandomSystems.SoP.CollisionAsymptotics
