/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.VirtualPDS
import RandomSystems.SoP.XORSignedDegreeThree

/-!
# The XOR signed truncation as a virtual visible representative

This module connects the concrete Fourier certificate to the general signed
`Dist` layer.  It deliberately works at one fixed visible `q`-query tape: the
objects below are virtual transcript laws, not yet full PDS representatives
valid simultaneously for every environment.

The exact real-minus-ideal visible law splits into the retained signed
truncation and its tail.  Each density is divided by the number of tapes, so
the already-proved half-uniform-`L1` quantities are definitionally the general
`Dist.virtualDistance` costs.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.XORVirtualRepresentative

open RandomSystems
open RandomSystems.CR18
open RandomSystems.Applications.XoP.ANOVA
open RandomSystems.SoP.CollisionProxy
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORSignedTruncation
open RandomSystems.SoP.XORSignedDegreeThree

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The exact visible SoP-minus-URF error as a signed finite law. -/
def exactVisibleError (n q : Nat) : Dist (BitMatrix q n) :=
  Dist.ofUniformDensity (BitMatrix q n)
    (visibleDensityErrorReal (G := XorSpace n) (q := q))

/-- The retained low-level Fourier error as a signed finite law. -/
def truncationError (n q r : Nat) : Dist (BitMatrix q n) :=
  Dist.ofUniformDensity (BitMatrix q n)
    (signedTruncationDensity n q r)

/-- The unretained Fourier tail as a signed finite law. -/
def tailError (n q r : Nat) : Dist (BitMatrix q n) :=
  Dist.ofUniformDensity (BitMatrix q n) (signedTailDensity n q r)

/-- The ideal visible law. -/
def idealVisible (n q : Nat) : Dist (BitMatrix q n) :=
  Dist.uniform (BitMatrix q n)

/-- The exact visible law, written as the ideal law plus its signed error. -/
def exactVisible (n q : Nat) : Dist (BitMatrix q n) :=
  idealVisible n q + exactVisibleError n q

/-- The virtual low-level representative obtained by adding only the retained
signed modes to the ideal law. -/
def truncationVisible (n q r : Nat) : Dist (BitMatrix q n) :=
  idealVisible n q + truncationError n q r

/-- Exact decomposition in the signed finite-law space. -/
theorem exact_visible_error_eq_truncation_add_tail
    {n q r : Nat} (hr : 2 ≤ r) (hq : q ≤ 2 ^ n) :
    exactVisibleError n q = truncationError n q r + tailError n q r := by
  rw [exactVisibleError, truncationError, tailError,
    ← Dist.ofUniformDensity_add]
  congr 1
  funext y
  exact visible_density_error_real_eq_signed_truncation_add_tail hr hq y

/-- The general virtual norm recovers the existing truncation quantity
exactly. -/
theorem virtualDistance_truncation_error_zero
    (n q r : Nat) :
    Dist.virtualDistance (truncationError n q r) 0 =
      signedTruncationAdvantage n q r := by
  rw [truncationError, Dist.virtualDistance_ofUniformDensity_zero]
  rfl

/-- The same identification for the unretained tail. -/
theorem virtualDistance_tail_error_zero
    (n q r : Nat) :
    Dist.virtualDistance (tailError n q r) 0 =
      signedTailAdvantage n q r := by
  rw [tailError, Dist.virtualDistance_ofUniformDensity_zero]
  rfl

/-- Every retained nonconstant Fourier level is centered, hence the virtual
truncation has total signed mass zero. -/
theorem truncation_error_weight_eq_zero (n q r : Nat) :
    (truncationError n q r).weight = 0 := by
  rw [truncationError, Dist.weight_ofUniformDensity]
  simpa [average] using
    (average_signed_truncation_density_eq_zero n q r)

/-- The virtual visible representative is normalized in total mass, although
it need not be pointwise non-negative. -/
theorem truncation_visible_weight_eq_one (n q r : Nat) :
    (truncationVisible n q r).weight = 1 := by
  rw [truncationVisible, Dist.weight_add, truncation_error_weight_eq_zero,
    idealVisible, Dist.weight_uniform, add_zero]

/-- Translating both laws by the ideal law does not change the truncation
cost. -/
theorem virtualDistance_truncation_visible_ideal
    (n q r : Nat) :
    Dist.virtualDistance (truncationVisible n q r) (idealVisible n q) =
      signedTruncationAdvantage n q r := by
  rw [truncationVisible, Dist.virtualDistance]
  have hsub : idealVisible n q + truncationError n q r - idealVisible n q =
      truncationError n q r := by abel
  rw [hsub]
  simpa [Dist.virtualDistance] using
    (virtualDistance_truncation_error_zero n q r)

/-- The exact visible virtual distance is the ordinary adaptive advantage. -/
theorem virtualDistance_exact_error_zero_eq_advantage
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    Dist.virtualDistance (exactVisibleError n q) 0 =
      PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (RandomSystems.SoP.xop (XorSpace n))
          (RandomSystems.SoP.urf (XorSpace n)) := by
  rw [exactVisibleError, Dist.virtualDistance_ofUniformDensity_zero]
  symm
  simpa [average, uniformAverage] using
    (advantage_eq_half_uniformL1 (G := XorSpace n) q (by
      simpa [card_xorSpace] using hq))

/-- Shifted form of the exact visible-distance identity. -/
theorem virtualDistance_exact_visible_ideal_eq_advantage
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    Dist.virtualDistance (exactVisible n q) (idealVisible n q) =
      PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (RandomSystems.SoP.xop (XorSpace n))
          (RandomSystems.SoP.urf (XorSpace n)) := by
  rw [exactVisible, Dist.virtualDistance]
  have hsub : idealVisible n q + exactVisibleError n q - idealVisible n q =
      exactVisibleError n q := by abel
  rw [hsub]
  simpa [Dist.virtualDistance] using
    (virtualDistance_exact_error_zero_eq_advantage hq)

/-- The former reverse-triangle certificate is exactly the statement that the
distance of the retained virtual representative approximates the exact
visible distance, with the virtual tail norm as the only loss. -/
theorem abs_exact_virtualDistance_sub_truncation_virtualDistance_le_tail
    {n q r : Nat} (hr : 2 ≤ r) (hq : q ≤ 2 ^ n) :
    |Dist.virtualDistance (exactVisible n q) (idealVisible n q) -
        Dist.virtualDistance (truncationVisible n q r) (idealVisible n q)| ≤
      Dist.virtualDistance (tailError n q r) 0 := by
  rw [virtualDistance_exact_visible_ideal_eq_advantage hq,
    virtualDistance_truncation_visible_ideal,
    virtualDistance_tail_error_zero]
  exact abs_advantage_sub_signed_truncation_advantage_le_tail hr hq

end RandomSystems.SoP.XORVirtualRepresentative
