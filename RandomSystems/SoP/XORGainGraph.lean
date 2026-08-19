/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.GainGraphCancellation
import RandomSystems.SoP.XORBounds

/-!
# Gain-graph presentation of the sharp XOR SoP bound

This file joins two previously separate proof lanes:

* `GainGraphCancellation` gives the exact signed expansion of the compatible
  hidden-state count and removes every chosen balanced broken circuit by a
  sign-reversing involution;
* `XORBounds` controls the centered level-three-and-higher remainder with the
  tight finite checkerboard/orthogonality estimate.

The bridge is pointwise.  The broken-circuit sum is proved to be the actual SoP
likelihood ratio, not merely a heuristic graph model.  Subtracting the constant
and pair-collision proxy therefore gives exactly the already-certified
remainder.  The final theorem retains the strongest constants in the XOR lane.

The quantitative tail proof still uses the finite Walsh/checkerboard basis for
the final orthogonal core-pair count.  The representative and the exact
cancellation layer are gain-graph based; no claim of a spectral-free tail proof
is made here.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORGainGraph

open RandomSystems.CR18
open RandomSystems.Applications.SoP
open RandomSystems.Applications.XoP.ANOVA
open RandomSystems.SoP.GainGraphCancellation
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.CollisionProxy
open RandomSystems.SoP.XORBounds

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The exact compatible count after balanced broken circuits have been
cancelled. -/
def brokenCircuitCompatibleCountInt (n q : Nat) (y : BitMatrix q n) : Int :=
  ∑ A ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
      ¬ ContainsBrokenCircuit (balancedCycleCertificates y) A,
    gainGraphTermInt y A

theorem brokenCircuitCompatibleCountInt_eq_compatibleCountNat
    (n q : Nat) (y : BitMatrix q n) :
    brokenCircuitCompatibleCountInt n q y =
      (CompatibleCount.compatibleCountNat y : Int) := by
  exact (compatibleCountNat_eq_brokenCircuitGainGraph y).symm

/-- Normalized real likelihood obtained directly from the restricted
gain-graph sum. -/
def brokenCircuitDensity (n q : Nat) (y : BitMatrix q n) : Real :=
  (brokenCircuitCompatibleCountInt n q y : Real) *
      ((2 ^ n : Nat) : Real) ^ q /
    ((((2 ^ n).descFactorial q : Nat) : Real) ^ 2)

theorem brokenCircuitDensity_eq_compatibleDensity
    (n q : Nat) (y : BitMatrix q n) :
    brokenCircuitDensity n q y = compatibleDensity n q y := by
  have hcount := brokenCircuitCompatibleCountInt_eq_compatibleCountNat n q y
  have hcountReal :
      (brokenCircuitCompatibleCountInt n q y : Real) =
        (CompatibleCount.compatibleCountNat y : Real) := by
    exact_mod_cast hcount
  simp only [brokenCircuitDensity, compatibleDensity]
  rw [hcountReal]

/-- Pointwise exactness: the broken-circuit gain graph is the real SoP
likelihood ratio. -/
theorem brokenCircuitDensity_eq_visibleDensityRatioReal
    {n q : Nat} (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    brokenCircuitDensity n q y =
      visibleDensityRatioReal (G := XorSpace n) (q := q) y := by
  rw [brokenCircuitDensity_eq_compatibleDensity]
  exact compatibleDensity_eq_visibleDensityRatioReal hq y

/-- What remains in the gain-graph density after removing the constant and the
single planted-collision contribution. -/
def brokenCircuitResidual (n q : Nat) (y : BitMatrix q n) : Real :=
  brokenCircuitDensity n q y - proxyDensity (XorSpace n) q y

theorem brokenCircuitResidual_eq_remainderDensity
    {n q : Nat} (hq : q ≤ 2 ^ n) (y : BitMatrix q n) :
    brokenCircuitResidual n q y =
      remainderDensity (G := XorSpace n) q y := by
  unfold brokenCircuitResidual remainderDensity
  rw [brokenCircuitDensity_eq_visibleDensityRatioReal hq]

/-- Exact squared-energy identity for the uncancelled gain-graph residual.
The right-hand side is where the finite checkerboard basis performs the final
orthogonal core-pair count. -/
theorem average_brokenCircuitResidual_sq_eq_fourierTail
    {n q : Nat} (hN : 2 ≤ 2 ^ n) (hq : q ≤ 2 ^ n) :
    average (BitMatrix q n) (fun y => (brokenCircuitResidual n q y) ^ 2) =
      fourierTailEnergy n q := by
  rw [show
      (fun y : BitMatrix q n => (brokenCircuitResidual n q y) ^ 2) =
        (fun y => (remainderDensity (G := XorSpace n) q y) ^ 2) by
      funext y
      rw [brokenCircuitResidual_eq_remainderDensity hq y]]
  exact average_remainderDensity_sq_eq_fourierTail hN hq

/-- The strongest finite energy bound, now stated directly for the
broken-circuit residual. -/
theorem average_brokenCircuitResidual_sq_le
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    average (BitMatrix q n) (fun y => (brokenCircuitResidual n q y) ^ 2) ≤
      remainderEnergyBound n q := by
  have hN : 2 ≤ 2 ^ n := by
    have hlarge := hundred_mul_le_two_pow hn
    omega
  have hq : q ≤ 2 ^ n := by omega
  rw [average_brokenCircuitResidual_sq_eq_fourierTail hN hq]
  simpa [remainderEnergyBound] using fourierTailEnergy_le_tight hn h2q

/-- Half the uniform `L1` mass of the surviving gain-graph correction. -/
def brokenCircuitResidualAdvantage (n q : Nat) : Real :=
  (1 / 2 : Real) *
    average (BitMatrix q n) (fun y => |brokenCircuitResidual n q y|)

theorem brokenCircuitResidualAdvantage_eq_remainderAdvantage
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    brokenCircuitResidualAdvantage n q =
      remainderAdvantage (G := XorSpace n) q := by
  unfold brokenCircuitResidualAdvantage remainderAdvantage
  apply congrArg ((1 / 2 : Real) * ·)
  apply congrArg (average (BitMatrix q n))
  funext y
  rw [brokenCircuitResidual_eq_remainderDensity hq y]

theorem brokenCircuitResidualAdvantage_le
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n) :
    brokenCircuitResidualAdvantage n q ≤ remainderErrorBound n q := by
  have hq : q ≤ 2 ^ n := by omega
  rw [brokenCircuitResidualAdvantage_eq_remainderAdvantage hq]
  exact remainderAdvantage_le hn h2q

/-- Final sharp two-regime theorem routed through the exact broken-circuit
gain-graph density.  No tail constant is rounded upward. -/
theorem adaptiveTranscriptAdvantage_le_explicit_gainGraph
    {n q : Nat} (hn : 10 ≤ n) (hq2 : 2 ≤ q) (h2q : 2 * q ≤ 2 ^ n) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
      min
          ((q.choose 2 : Real) /
            (((2 ^ n - 1 : Nat) : Real) ^ 2))
          (Real.sqrt (q.choose 2 : Real) /
            (2 * ((2 ^ n - 1 : Nat) : Real) *
              Real.sqrt ((2 ^ n - 1 : Nat) : Real))) +
        (1 / 2 : Real) * Real.sqrt
          (16 * (q.choose 3 : Real) /
              ((((2 ^ n - 1 : Nat) : Real) ^ 3) *
                (((2 ^ n - 2 : Nat) : Real) ^ 3)) +
            (1152 / 7 : Real) * (q : Real) ^ 4 /
              (((2 ^ n : Nat) : Real) ^ 6) +
            8 * (q : Real) ^ 4 / (((2 ^ n : Nat) : Real) ^ 8)) := by
  exact adaptiveTranscriptAdvantage_le_explicit hn hq2 h2q

end RandomSystems.SoP.XORGainGraph
