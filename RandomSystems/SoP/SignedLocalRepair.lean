/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.XORCollisionAttack

/-!
# Signed local-repair representative for XOR SoP

Uniformly averaging away one visible coordinate is the operation of
recoloring that coordinate while retaining all others.  Its difference from
the original function is therefore a signed local repair.  The first theorem
below records the fundamental cancellation: every such repair has mean zero.

For XOR SoP, retaining the pair and triple repair cores gives the density
`1 + signedTruncationDensity n q 4`.  In the sparse sign range this is not only
a virtual density: it is nonnegative and normalized, hence an honest proxy.
Its exact distance from the uniform density is `signedDegreeThreeMain`; the
ordinary collision test matches that main term up to the certified
level-four-and-higher tail.
-/

noncomputable section

open scoped BigOperators

namespace RandomSystems.SoP.SignedLocalRepair

open RandomSystems.Applications.XoP.ANOVA
open RandomSystems.Applications.SoP
open RandomSystems.SoP.XORFourier
open RandomSystems.SoP.XORInjection
open RandomSystems.SoP.XORSignedTruncation
open RandomSystems.SoP.XORSignedDegreeThree

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- The coordinates retained when coordinate `i` is locally repaired. -/
def keepExcept {q : Nat} (i : Fin q) : Finset (Fin q) :=
  (Finset.univ : Finset (Fin q)).erase i

/-- Average away one coordinate while retaining every other coordinate. -/
def recolorAverage {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (i : Fin q) (f : (Fin q → G) → Real) : (Fin q → G) → Real :=
  project (keepExcept i) f

/-- The signed difference between a tape and a uniformly recolored tape. -/
def repairDifference {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (i : Fin q) (f : (Fin q → G) → Real) : (Fin q → G) → Real :=
  fun y => f y - recolorAverage i f y

/-- A local repair only moves mass: its signed total is zero. -/
theorem uniform_average_repair_difference_eq_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (i : Fin q) (f : (Fin q → G) → Real) :
    uniformAverage (Fin q → G) (repairDifference i f) = 0 := by
  unfold repairDifference recolorAverage
  rw [uniformAverage_sub, uniformAverage_project]
  ring

/-- Honest density suggested by retaining the pair and triple repair cores. -/
def threeCoreProxyDensity (n q : Nat) : BitMatrix q n → Real :=
  fun y => 1 + signedTruncationDensity n q 4 y

/-- Statistical distance from the uniformly flat density. -/
def threeCoreProxyAdvantage (n q : Nat) : Real :=
  (1 / 2 : Real) * average (BitMatrix q n) (fun y =>
    |threeCoreProxyDensity n q y - 1|)

/-- The three-core proxy has total mass one. -/
theorem average_three_core_proxy_density_eq_one (n q : Nat) :
    average (BitMatrix q n) (threeCoreProxyDensity n q) = 1 := by
  unfold threeCoreProxyDensity
  rw [average_add, average_const,
    average_signed_truncation_density_eq_zero]
  ring

/-- In the sparse sign range, the signed repair proxy is an honest
nonnegative density. -/
theorem three_core_proxy_density_nonneg_sparse
    {n q : Nat} (hN : 6 ≤ 2 ^ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n)
    (y : BitMatrix q n) :
    0 ≤ threeCoreProxyDensity n q y := by
  have hq : q ≤ 2 ^ n := by omega
  obtain ⟨_hneg, hpos⟩ :=
    signed_degree_three_sign_conditions_of_sparse hN h2q h2pairs
  by_cases hy : Function.Injective y
  · rw [threeCoreProxyDensity,
      signed_truncation_density_four_eq_of_injective (by omega) hq y hy]
    have hMleN : q.choose 2 ≤ 2 ^ n := by omega
    have hNleSq : 2 ^ n ≤ (2 ^ n - 1) ^ 2 := by
      have hsub : 2 ^ n - 1 + 1 = 2 ^ n := by omega
      nlinarith [Nat.zero_le (2 ^ n - 1)]
    have hMleSq : q.choose 2 ≤ (2 ^ n - 1) ^ 2 :=
      hMleN.trans hNleSq
    have hmain : (q.choose 2 : Real) /
          (((2 ^ n - 1 : Nat) : Real) ^ 2) ≤ 1 := by
      have hM' : (q.choose 2 : Real) ≤
          ((2 ^ n - 1 : Nat) : Real) ^ 2 := by
        exact_mod_cast hMleSq
      have hden : 0 < (((2 ^ n - 1 : Nat) : Real) ^ 2) := by
        have : 0 < 2 ^ n - 1 := by omega
        positivity
      exact (div_le_one hden).2 hM'
    have hcorr : 0 ≤ 8 * (q.choose 3 : Real) /
        ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
          (((2 ^ n - 2 : Nat) : Real) ^ 2)) := by positivity
    have hbase : 0 ≤ 1 - (q.choose 2 : Real) /
        (((2 ^ n - 1 : Nat) : Real) ^ 2) := sub_nonneg.mpr hmain
    calc
      0 ≤ (1 - (q.choose 2 : Real) /
          (((2 ^ n - 1 : Nat) : Real) ^ 2)) +
          8 * (q.choose 3 : Real) /
            ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
              (((2 ^ n - 2 : Nat) : Real) ^ 2)) := add_nonneg hbase hcorr
      _ = 1 + (-(q.choose 2 : Real) /
          (((2 ^ n - 1 : Nat) : Real) ^ 2) +
          8 * (q.choose 3 : Real) /
            ((((2 ^ n - 1 : Nat) : Real) ^ 2) *
              (((2 ^ n - 2 : Nat) : Real) ^ 2))) := by ring
  · unfold threeCoreProxyDensity
    have := signed_truncation_density_four_nonneg_of_not_injective
      (by omega : 3 ≤ 2 ^ n) hq hpos y hy
    linarith

/-- The exact distance of the honest local-repair proxy from uniform. -/
theorem three_core_proxy_advantage_eq_signed_degree_three_main
    {n q : Nat} (hN : 6 ≤ 2 ^ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    threeCoreProxyAdvantage n q = signedDegreeThreeMain n q := by
  have hq : q ≤ 2 ^ n := by omega
  obtain ⟨hneg, hpos⟩ :=
    signed_degree_three_sign_conditions_of_sparse hN h2q h2pairs
  have hpoint : (fun y : BitMatrix q n =>
      |threeCoreProxyDensity n q y - 1|) =
      (fun y => |signedTruncationDensity n q 4 y|) := by
    funext y
    unfold threeCoreProxyDensity
    congr 1
    ring
  unfold threeCoreProxyAdvantage
  rw [hpoint]
  change signedTruncationAdvantage n q 4 = signedDegreeThreeMain n q
  exact signed_truncation_advantage_four_eq_signed_degree_three_main
    (by omega) hq hneg hpos

/-- The local-repair endpoint is strictly smaller than the former closed
collision-proxy endpoint as soon as triples exist. -/
theorem signed_local_repair_bound_lt_previous
    {n q : Nat} (hn : 10 ≤ n) (hq3 : 3 ≤ q)
    (h2q : 2 * q ≤ 2 ^ n) (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    signedDegreeThreeMain n q + signedDegreeThreeError n q <
      min (RandomSystems.SoP.CollisionProxy.sparseBound (XorSpace n) q)
          (RandomSystems.SoP.CollisionProxy.denseBound (XorSpace n) q) +
        RandomSystems.SoP.XORBounds.remainderErrorBound n q := by
  exact signed_degree_three_bound_lt_min_sparse_dense_add_remainder_sparse
    hn hq3 h2q h2pairs

/-- The local-repair proxy is matched by the collision test up to the same
level-four tail that controls the true system. -/
theorem signed_local_repair_two_sided
    {n q : Nat} (hn : 10 ≤ n) (h2q : 2 * q ≤ 2 ^ n)
    (h2pairs : 2 * q.choose 2 ≤ 2 ^ n) :
    signedDegreeThreeMain n q - signedDegreeThreeError n q ≤
        visibleCollisionTestGap n q ∧
      visibleCollisionTestGap n q ≤
        RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ∧
      RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop (XorSpace n))
            (RandomSystems.SoP.urf (XorSpace n)) ≤
        signedDegreeThreeMain n q + signedDegreeThreeError n q := by
  refine ⟨signed_degree_three_main_sub_error_le_collision_test_gap_sparse
      hn h2q h2pairs, ?_,
    adaptive_transcript_advantage_le_signed_degree_three_main_add_error_sparse
      hn h2q h2pairs⟩
  exact visible_collision_test_gap_le_adaptive_advantage (by omega)

end RandomSystems.SoP.SignedLocalRepair
