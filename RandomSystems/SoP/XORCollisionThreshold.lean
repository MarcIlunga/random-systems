/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORCollisionAttack
import RandomSystems.SoP.XORBounds

/-!
# Collision-count threshold attack for XOR SoP

The sparse collision test asks only whether any visible collision occurred.
Across the birthday transition the correct observable test is instead the
positive centered-collision event

```text
M < N*K,
```

where `K` is the visible number of equal output pairs and
`M = choose(q,2)`.  This integer predicate is exactly `K > M/N`, so it is
the positive set of the planted-collision proxy likelihood.

This module proves that the concrete fixed-query threshold distinguisher is
within the same higher-order remainder as the proxy itself.  Consequently the
finite collision-proxy analysis is two-sided throughout its full proved range,
not only in the sparse range where the event reduces approximately to
`K > 0`.
-/

noncomputable section
open scoped BigOperators

namespace RandomSystems.SoP.CollisionThreshold

open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORBounds
open RandomSystems.SoP.CollisionProxy
open RandomSystems.SoP.XORSignedDegreeThree
open RandomSystems.Applications.SoP
open RandomSystems.Applications.XoP.ANOVA

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Exact integer form of the positive centered-collision event.  It avoids
division: `K > M/N` is represented as `M < N*K`. -/
def collisionThresholdEvent
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : Prop :=
  pairCount q < Fintype.card G * pairCollisionCountNat G q y

def collisionThresholdDecision
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : Bool :=
  decide (collisionThresholdEvent G q y)

@[simp]
theorem collision_threshold_decision_eq_true_iff
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    collisionThresholdDecision G q y = true ↔
      collisionThresholdEvent G q y := by
  simp [collisionThresholdDecision]

theorem collision_threshold_event_iff_centered_pos
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (y : Fin q → G) :
    collisionThresholdEvent G q y ↔
      0 < centeredCollisionCount G q y := by
  have hN : (0 : Real) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  unfold collisionThresholdEvent centeredCollisionCount collisionMean
  change pairCount q < Fintype.card G * pairCollisionCountNat G q y ↔
    0 < pairCollisionCountReal G q y -
      (pairCount q : Real) / (Fintype.card G : Real)
  rw [pairCollisionCountReal_eq_pairCollisionCountNat, sub_pos]
  rw [div_lt_iff₀ hN]
  constructor
  · intro h
    have h' : pairCount q <
        pairCollisionCountNat G q y * Fintype.card G := by
      simpa [Nat.mul_comm] using h
    exact_mod_cast h'
  · intro h
    have h' : pairCount q <
        pairCollisionCountNat G q y * Fintype.card G := by
      exact_mod_cast h
    simpa [Nat.mul_comm] using h'

theorem collision_threshold_event_iff_kernel_pos
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hN : 2 ≤ Fintype.card G) (y : Fin q → G) :
    collisionThresholdEvent G q y ↔ 0 < collisionKernel G q y := by
  rw [collision_threshold_event_iff_centered_pos]
  have hcoef : 0 < (Fintype.card G : Real) /
      ((Fintype.card G - 1 : Nat) : Real) ^ 2 := by
    have hNm1 : 0 < ((Fintype.card G - 1 : Nat) : Real) := by
      exact_mod_cast Nat.sub_pos_of_lt hN
    positivity
  unfold collisionKernel
  constructor
  · exact mul_pos hcoef
  · intro h
    nlinarith

/-- Signed real-minus-ideal acceptance gap of the collision-count threshold
test on the visible fresh-query tape. -/
def collisionThresholdTestGap (n q : Nat) : Real :=
  average (BitMatrix q n) (fun y =>
    if collisionThresholdEvent (XorSpace n) q y then
      visibleDensityErrorReal (G := XorSpace n) (q := q) y
    else 0)

theorem average_collision_kernel_on_threshold_eq_advantage
    {n q : Nat} (hN : 2 ≤ 2 ^ n) (hq0 : 0 < q) :
    average (BitMatrix q n) (fun y =>
      if collisionThresholdEvent (XorSpace n) q y then
        collisionKernel (XorSpace n) q y
      else 0) = collisionAdvantage (XorSpace n) q := by
  have hpoint :
      (fun y : BitMatrix q n =>
        if collisionThresholdEvent (XorSpace n) q y then
          collisionKernel (XorSpace n) q y
        else 0) =
      (fun y => max (collisionKernel (XorSpace n) q y) 0) := by
    funext y
    rw [collision_threshold_event_iff_kernel_pos
      (XorSpace n) q (by simpa [card_xorSpace] using hN) y]
    by_cases hpos : 0 < collisionKernel (XorSpace n) q y
    · rw [if_pos hpos, max_eq_left hpos.le]
    · rw [if_neg hpos, max_eq_right (le_of_not_gt hpos)]
  rw [hpoint]
  change uniformAverage (BitMatrix q n)
      (fun y => max (collisionKernel (XorSpace n) q y) 0) =
    collisionAdvantage (XorSpace n) q
  rw [uniformAverage_max_zero_eq_half_l1]
  · rfl
  · exact uniformAverage_collisionKernel (G := XorSpace n) q hq0

theorem collision_threshold_gap_eq_proxy_add_remainder_event
    {n q : Nat} (hN : 2 ≤ 2 ^ n) (hq0 : 0 < q) :
    collisionThresholdTestGap n q =
      collisionAdvantage (XorSpace n) q +
        average (BitMatrix q n) (fun y =>
          if collisionThresholdEvent (XorSpace n) q y then
            remainderDensity (G := XorSpace n) q y
          else 0) := by
  unfold collisionThresholdTestGap
  have hpoint :
      (fun y : BitMatrix q n =>
        if collisionThresholdEvent (XorSpace n) q y then
          visibleDensityErrorReal (G := XorSpace n) (q := q) y
        else 0) =
      (fun y =>
        (if collisionThresholdEvent (XorSpace n) q y then
          collisionKernel (XorSpace n) q y else 0) +
        (if collisionThresholdEvent (XorSpace n) q y then
          remainderDensity (G := XorSpace n) q y else 0)) := by
    funext y
    by_cases hy : collisionThresholdEvent (XorSpace n) q y
    · simp only [hy, ↓reduceIte]
      unfold remainderDensity visibleDensityErrorReal proxyDensity
      ring
    · simp [hy]
  rw [hpoint, average_add,
    average_collision_kernel_on_threshold_eq_advantage hN hq0]

theorem abs_collision_threshold_gap_sub_proxy_le_remainder
    {n q : Nat} (hN : 2 ≤ 2 ^ n) (hq0 : 0 < q)
    (hq : q ≤ 2 ^ n) :
    |collisionThresholdTestGap n q -
        collisionAdvantage (XorSpace n) q| ≤
      remainderAdvantage (G := XorSpace n) q := by
  rw [collision_threshold_gap_eq_proxy_add_remainder_event hN hq0]
  ring_nf
  exact abs_average_indicator_le_half_average_abs_of_average_eq_zero
    (fun y : BitMatrix q n =>
      collisionThresholdEvent (XorSpace n) q y)
    (remainderDensity (G := XorSpace n) q)
    (uniformAverage_remainderDensity (G := XorSpace n) q hq0 (by
      simpa [card_xorSpace] using hq))

theorem collision_threshold_test_gap_eq_visible_mass_gap
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    collisionThresholdTestGap n q =
      (realVisibleDist (G := XorSpace n) (q := q)).mass
          (collisionThresholdEvent (XorSpace n) q) -
        (idealVisibleDist (G := XorSpace n) (q := q)).mass
          (collisionThresholdEvent (XorSpace n) q) := by
  unfold collisionThresholdTestGap average
  rw [Dist.mass_eq_sum, Dist.mass_eq_sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  rw [show
      (∑ y : BitMatrix q n,
          if collisionThresholdEvent (XorSpace n) q y then
            visibleDensityErrorReal (G := XorSpace n) (q := q) y
          else 0) /
          (Fintype.card (BitMatrix q n) : Real) =
        ∑ y : BitMatrix q n,
          (if collisionThresholdEvent (XorSpace n) q y then
            visibleDensityErrorReal (G := XorSpace n) (q := q) y
          else 0) /
            (Fintype.card (BitMatrix q n) : Real) by
      rw [Finset.sum_div]]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hevent : collisionThresholdEvent (XorSpace n) q y
  · simp only [hevent, ↓reduceIte]
    exact (visible_mass_sub_eq_density_error_div_card hq y).symm
  · simp [hevent]

theorem collision_threshold_test_gap_le_adaptive_advantage
    {n q : Nat} (hq : q ≤ 2 ^ n) :
    collisionThresholdTestGap n q ≤
      RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (RandomSystems.SoP.xop (XorSpace n))
          (RandomSystems.SoP.urf (XorSpace n)) := by
  rw [collision_threshold_test_gap_eq_visible_mass_gap hq,
    RandomSystems.SoP.adv_prf_eq_visible_stat_dist_of_le_card]
  · exact RandomSystems.mass_sub_mass_le_statDist
      (realVisibleDist (G := XorSpace n) (q := q))
      (idealVisibleDist (G := XorSpace n) (q := q))
      (collisionThresholdEvent (XorSpace n) q)
  · simpa [card_xorSpace] using hq

theorem abs_collision_threshold_gap_sub_proxy_le_error
    {n q : Nat} (hn : 10 ≤ n) (hq0 : 0 < q)
    (h2q : 2 * q ≤ 2 ^ n) :
    |collisionThresholdTestGap n q -
        collisionAdvantage (XorSpace n) q| ≤
      remainderErrorBound n q := by
  exact (abs_collision_threshold_gap_sub_proxy_le_remainder
    (by have h := hundred_mul_le_two_pow hn; omega) hq0 (by omega)).trans
      (remainderAdvantage_le hn h2q)

theorem collision_advantage_sub_error_le_threshold_test_gap
    {n q : Nat} (hn : 10 ≤ n) (hq0 : 0 < q)
    (h2q : 2 * q ≤ 2 ^ n) :
    collisionAdvantage (XorSpace n) q - remainderErrorBound n q ≤
      collisionThresholdTestGap n q := by
  have h := (abs_le.mp
    (abs_collision_threshold_gap_sub_proxy_le_error hn hq0 h2q)).1
  linarith

theorem collision_advantage_sub_error_le_adaptive_advantage
    {n q : Nat} (hn : 10 ≤ n) (hq0 : 0 < q)
    (h2q : 2 * q ≤ 2 ^ n) :
    collisionAdvantage (XorSpace n) q - remainderErrorBound n q ≤
      RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (RandomSystems.SoP.xop (XorSpace n))
          (RandomSystems.SoP.urf (XorSpace n)) := by
  exact (collision_advantage_sub_error_le_threshold_test_gap
    hn hq0 h2q).trans
      (collision_threshold_test_gap_le_adaptive_advantage (by omega))

end RandomSystems.SoP.CollisionThreshold

