/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Applications.SoP.TV
import RandomSystems.Applications.XoPAnalytic
import RandomSystems.Applications.XoPANOVA

/-!
# SoP Small-Query Exact Values

This file reuses the existing XoP visible positive-error calculations for
`q = 0, 1, 2`, after identifying the SoP visible statistical distance with the
same count-normalized positive-error expression.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace SoP

variable {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]

/-- The SoP visible `statDist` is the existing XoP pure visible positive-error
expression. -/
theorem visibleStatDist_eq_pureVisiblePositiveError (q : Nat)
    (hq : q ≤ Fintype.card G) :
    visibleStatDist (G := G) (q := q) =
      XoP.Analytic.pureVisiblePositiveError (G := G) q := by
  rw [visibleStatDist_eq_sum]
  simp [XoP.Analytic.pureVisiblePositiveError,
    realVisibleMass_eq_densityRatio_mul_ideal (G := G) (q := q) hq,
    visibleDensityRatio, expectationNormalizer_value, idealVisibleMass]

/-- With no queries, the exact visible advantage is zero. -/
theorem visibleStatDist_zero :
    visibleStatDist (G := G) (q := 0) = 0 := by
  rw [visibleStatDist_eq_pureVisiblePositiveError (G := G) (q := 0) (Nat.zero_le _)]
  exact XoP.Analytic.pureVisiblePositiveError_zero (G := G)

/-- With one query, the exact visible advantage is zero. -/
theorem visibleStatDist_one :
    visibleStatDist (G := G) (q := 1) = 0 := by
  have hq : 1 ≤ Fintype.card G := Fintype.card_pos
  rw [visibleStatDist_eq_pureVisiblePositiveError (G := G) (q := 1) hq]
  exact XoP.Analytic.pureVisiblePositiveError_one (G := G)

/-- Exact two-query visible advantage. -/
theorem visibleStatDist_two (hG : 2 ≤ Fintype.card G) :
    visibleStatDist (G := G) (q := 2) =
      1 / ((Fintype.card G : NNReal) * ((Fintype.card G - 1 : Nat) : NNReal)) := by
  rw [visibleStatDist_eq_pureVisiblePositiveError (G := G) (q := 2) hG]
  exact XoP.Analytic.pureVisiblePositiveError_two (G := G) hG

/-! ## Concrete finite-bound target pieces -/

/-- The spatial-reconstruction leading bound
\[
  B_q(N)=|\mathrm{PairIndex}(q)|\,(N)_q/(N^q(N-1)^2).
\]

This is the bound used as the low-rank/spatial part of the LM20-orbit proof
target. -/
def spatialReconstructionBound (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  (((Fintype.card (PairIndex q)) * (Fintype.card G).descFactorial q : Nat) : NNReal) /
    (((Fintype.card G ^ q) * (Fintype.card G - 1) ^ 2 : Nat) : NNReal)

/-- Current explicit finite tail error coming from the formal rank-tail
cardinality estimate:
\[
  E_{\mathrm{tail}}(q,N)
  =
  \bigl(2^{q(q-1)}-(1+3|\mathrm{PairIndex}(q)|)\bigr)N^{2q-2}/((N)_q)^2.
\]

This term is intentionally crude: it is the triangle-inequality rank-tail
bound, not the desired cancellation-aware final estimate. -/
def rankTailErrorBound (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  (((2 ^ (q * (q - 1)) - (1 + 3 * Fintype.card (PairIndex q))) *
      (Fintype.card G) ^ (2 * q - 2) : Nat) : NNReal) /
    ((((Fintype.card G).descFactorial q *
      (Fintype.card G).descFactorial q : Nat) : NNReal))

/-- Closed pointwise fallback for the genuinely high-rank gain-graph tail
after ranks zero, one, and two have been separated:
\[
  E_{\ge 3}(q,N)=2^{q(q-1)}N^{2q-3}/((N)_q)^2.
\]

This keeps only the one-power improvement from `rank >= 3`; it deliberately
does not yet use cancellation or consistency probabilities. -/
def rankTailBeyondTwoErrorBound (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  (((2 ^ (q * (q - 1))) * (Fintype.card G) ^ (2 * q - 3) : Nat) : NNReal) /
    ((((Fintype.card G).descFactorial q *
      (Fintype.card G).descFactorial q : Nat) : NNReal))

/-- Closed pointwise fallback for the rank-four-and-higher gain-graph tail after
the signed rank-three layer has been separated:
\[
  E_{\ge 4}(q,N)=2^{q(q-1)}N^{2q-4}/((N)_q)^2.
\]

This is still a crude powerset-cardinality bound, but its field-size scale is
the target fourth-order scale once the signed rank-three residual is controlled. -/
def rankTailBeyondThreeErrorBound (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  (((2 ^ (q * (q - 1))) * (Fintype.card G) ^ (2 * q - 4) : Nat) : NNReal) /
    ((((Fintype.card G).descFactorial q *
      (Fintype.card G).descFactorial q : Nat) : NNReal))

/-- Exact number of collision-event subfamilies whose support graph has graphic
rank two.  This is a finite combinatorial quantity depending only on `q`. -/
def rankTwoSubfamilyCount (q : Nat) : Nat :=
  ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
    (fun T => collisionSubfamilyGraphicRank (q := q) T = 2)).card

/-- Closed pointwise fallback for the rank-two layer, using the exact number of
rank-two collision-event subfamilies:
\[
  E_2(q,N)=\#\{T:\operatorname{rank}(T)=2\}N^{2q-2}/((N)_q)^2.
\]
-/
def rankTwoLayerErrorBound (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  (((rankTwoSubfamilyCount q) * (Fintype.card G) ^ (2 * q - 2) : Nat) : NNReal) /
    ((((Fintype.card G).descFactorial q *
      (Fintype.card G).descFactorial q : Nat) : NNReal))

/-- Real-valued low-rank density ratio obtained by replacing the compatible
hidden-state count by the rank-zero plus rank-one approximation
`compatibleCountLowRankInt`.  This is signed because the approximation itself
is an integer-valued inclusion-exclusion truncation. -/
def compatibleCountLowRankDensityReal (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  ((compatibleCountLowRankInt (G := G) (q := q) y : ℤ) : ℝ) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Positive-error contribution of the low-rank density approximation under
the ideal visible law.  This is the exact theorem-shaped object that should be
bounded by `spatialReconstructionBound G q`. -/
def compatibleCountLowRankPositiveErrorReal
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max (compatibleCountLowRankDensityReal G q y - 1) 0)

/-- Real-valued true compatible-count density positive error.  This is the
`ℝ` analogue of the repository's `NNReal` visible positive-error expression. -/
def compatibleCountTruePositiveErrorReal
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max (XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y - 1) 0)

/-- Scaling a positive part by a positive reciprocal. -/
theorem max_mul_inv_sub_inv_eq_max_sub_div (d c : ℝ) (hc : 0 < c) :
    max (d * (1 / c) - 1 / c) 0 = max (d - 1) 0 / c := by
  have hrewrite : d * (1 / c) - 1 / c = (d - 1) / c := by
    field_simp [ne_of_gt hc]
  rw [hrewrite]
  by_cases h : 0 ≤ d - 1
  · rw [max_eq_left h]
    rw [max_eq_left]
    exact div_nonneg h (le_of_lt hc)
  · have hle : d - 1 ≤ 0 := le_of_not_ge h
    rw [max_eq_right hle]
    rw [max_eq_right]
    · simp
    · exact div_nonpos_of_nonpos_of_nonneg hle (le_of_lt hc)

/-- The visible statistical distance, cast to `ℝ`, is the true density positive
error under the ideal visible law. -/
theorem visibleStatDist_toReal_eq_compatibleCountTruePositiveErrorReal
    (q : Nat) (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) =
      compatibleCountTruePositiveErrorReal G q := by
  rw [visibleStatDist_eq_pureVisiblePositiveError (G := G) q hq]
  unfold XoP.Analytic.pureVisiblePositiveError compatibleCountTruePositiveErrorReal
    XoP.ANOVA.uniformAverage XoP.ANOVA.visibleDensityRatioReal
  simp only [NNReal.coe_sum, NNReal.coe_sub_def, NNReal.coe_mul, NNReal.coe_div,
    RandomSystems.Dist.uniform_apply]
  let c : ℝ := Fintype.card (Fin q → G)
  let D : (Fin q → G) → ℝ := fun x =>
    ↑(XoP.Combinatorics.compatibleCountNNReal x) /
      (↑↑((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q) /
        ↑↑(Fintype.card G ^ q))
  have hc : 0 < c := by
    dsimp [c]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Fin q → G))
  change (∑ x, max (D x * (1 / c) - 1 / c) 0) =
    (∑ x, max (D x - 1) 0) / c
  calc
    (∑ x, max (D x * (1 / c) - 1 / c) 0) =
        ∑ x, max (D x - 1) 0 / c := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact max_mul_inv_sub_inv_eq_max_sub_div (D x) c hc
    _ = (∑ x, max (D x - 1) 0) / c := by
          simp [div_eq_mul_inv, Finset.sum_mul]

/-- Pointwise positive-part comparison used by the low-rank/tail bridge. -/
theorem max_sub_one_le_max_sub_one_add_abs_sub (a b : ℝ) :
    max (a - 1) 0 ≤ max (b - 1) 0 + |a - b| := by
  apply max_le
  · calc
      a - 1 = (b - 1) + (a - b) := by ring
      _ ≤ max (b - 1) 0 + |a - b| :=
        add_le_add (le_max_left _ _) (le_abs_self _)
  · exact add_nonneg (le_max_right _ _) (abs_nonneg _)

/-- Positive part of a sum is bounded by the sum of positive parts. -/
theorem max_add_zero_le_max_zero_add_max_zero (a b : ℝ) :
    max (a + b) 0 ≤ max a 0 + max b 0 := by
  apply max_le
  · exact add_le_add (le_max_left _ _) (le_max_left _ _)
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

/-- Comparing the true density to the low-rank density reduces positive error
to the low-rank positive error plus the uniform average of the density
difference. -/
theorem compatibleCountTruePositiveErrorReal_le_lowRank_add_average_abs_diff
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) :
    compatibleCountTruePositiveErrorReal G q ≤
      compatibleCountLowRankPositiveErrorReal G q +
        XoP.ANOVA.uniformAverage (Fin q → G)
          (fun y => |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
            compatibleCountLowRankDensityReal G q y|) := by
  unfold compatibleCountTruePositiveErrorReal compatibleCountLowRankPositiveErrorReal
    XoP.ANOVA.uniformAverage
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro y _hy
  exact max_sub_one_le_max_sub_one_add_abs_sub
    (XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y)
    (compatibleCountLowRankDensityReal G q y)

/-- Named low-rank obligation for the finite-bound endpoint. -/
def CompatibleCountLowRankPositiveErrorBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Prop :=
  compatibleCountLowRankPositiveErrorReal G q ≤
    (spatialReconstructionBound G q : ℝ)

/-- Number of visible coordinate-pair collisions in a transcript. -/
def pairCollisionCountNat (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) : Nat :=
  ∑ p : PairIndex q, (if y p.1.2 = y p.1.1 then 1 else 0 : Nat)

/-- Number of visible coordinate-pair collisions in a transcript, as a real
quantity. -/
def pairCollisionCountReal (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) : ℝ :=
  ((∑ p : PairIndex q,
    (if y p.1.2 = y p.1.1 then 1 else 0 : Nat)) : ℝ)

/-- Integer form of the visible pair-collision count. -/
def pairCollisionCountInt (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) : ℤ :=
  ((∑ p : PairIndex q,
    (if y p.1.2 = y p.1.1 then 1 else 0 : Nat)) : ℤ)

/-- Query pairs whose visible transcript values collide. -/
noncomputable def pairCollisionSet (G : Type*) [DecidableEq G] {q : Nat}
    (y : Fin q → G) : Finset (PairIndex q) := by
  classical
  exact (Finset.univ : Finset (PairIndex q)).filter (fun p => y p.1.2 = y p.1.1)

/-- The visible pair-collision count is the cardinality of the collision
pair set. -/
theorem pairCollisionSet_card
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    (pairCollisionSet G y).card = pairCollisionCountNat G q y := by
  classical
  unfold pairCollisionSet pairCollisionCountNat
  rw [Finset.card_filter]

/-- The natural-valued collision count is bounded by the number of coordinate
pairs. -/
theorem pairCollisionCountNat_le_pairIndex_card
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    pairCollisionCountNat G q y ≤ Fintype.card (PairIndex q) := by
  unfold pairCollisionCountNat
  calc
    (∑ p : PairIndex q, (if y p.1.2 = y p.1.1 then 1 else 0 : Nat)) ≤
        ∑ _p : PairIndex q, (1 : Nat) := by
          apply Finset.sum_le_sum
          intro p _hp
          by_cases h : y p.1.2 = y p.1.1 <;> simp [h]
    _ = Fintype.card (PairIndex q) := by simp

/-- The integer collision count is the cast of the natural-valued count. -/
theorem pairCollisionCountInt_eq_pairCollisionCountNat
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    pairCollisionCountInt G q y = (pairCollisionCountNat G q y : ℤ) := by
  unfold pairCollisionCountInt pairCollisionCountNat
  exact_mod_cast rfl

/-- The real collision count is the cast of the natural-valued count. -/
theorem pairCollisionCountReal_eq_pairCollisionCountNat
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    pairCollisionCountReal G q y = (pairCollisionCountNat G q y : ℝ) := by
  unfold pairCollisionCountReal pairCollisionCountNat
  exact_mod_cast rfl

/-- Cardinality of one visible pair-collision-count fiber. -/
def pairCollisionCountFiberCard (G : Type*) [Fintype G] [DecidableEq G]
    (q k : Nat) : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter
    (fun y => pairCollisionCountNat G q y = k)).card

/-- Cardinality of the visible transcript fiber where every query pair in `S`
is a visible collision.  This is the two-pair occupancy object needed for the
second factorial moment of the visible pair-collision count. -/
def pairPairCollisionFiberCard (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (S : Finset (PairIndex q)) : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter
    (fun y => S ⊆ pairCollisionSet G y)).card

/-- Uniform averages of functions of the visible pair-collision count can be
collapsed to a finite one-dimensional sum over collision-count fibers. -/
theorem uniformAverage_of_pairCollisionCountNat
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (F : Nat → ℝ) :
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y => F (pairCollisionCountNat G q y)) =
      (∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
        (pairCollisionCountFiberCard G q k : ℝ) * F k) /
        (Fintype.card (Fin q → G) : ℝ) := by
  unfold XoP.ANOVA.uniformAverage
  have hmap : ∀ y ∈ (Finset.univ : Finset (Fin q → G)),
      pairCollisionCountNat G q y ∈
        Finset.range (Fintype.card (PairIndex q) + 1) := by
    intro y _hy
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le
      (pairCollisionCountNat_le_pairIndex_card (G := G) (q := q) y)
  have hfiber :
      (∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
        ∑ y ∈ (Finset.univ : Finset (Fin q → G)).filter
          (fun y => pairCollisionCountNat G q y = k),
          F (pairCollisionCountNat G q y)) =
        ∑ y : Fin q → G, F (pairCollisionCountNat G q y) := by
    simpa using Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin q → G)))
      (t := Finset.range (Fintype.card (PairIndex q) + 1))
      (g := pairCollisionCountNat G q) hmap
      (fun y : Fin q → G => F (pairCollisionCountNat G q y))
  rw [← hfiber]
  apply congrArg (fun s : ℝ => s / (Fintype.card (Fin q → G) : ℝ))
  apply Finset.sum_congr rfl
  intro k _hk
  calc
    (∑ y ∈ (Finset.univ : Finset (Fin q → G)).filter
      (fun y => pairCollisionCountNat G q y = k),
      F (pairCollisionCountNat G q y)) =
        ∑ _y ∈ (Finset.univ : Finset (Fin q → G)).filter
          (fun y => pairCollisionCountNat G q y = k), F k := by
          apply Finset.sum_congr rfl
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rw [hy]
    _ = (((Finset.univ : Finset (Fin q → G)).filter
          (fun y => pairCollisionCountNat G q y = k)).card : ℝ) * F k := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (pairCollisionCountFiberCard G q k : ℝ) * F k := by
          rfl

/-- Second factorial moment of the visible pair-collision count, before
evaluating the individual two-pair fibers.

This is the exact occupancy bridge:
\[
  \sum_y \binom{K(y)}2 =
  \sum_{\{p,r\}\subseteq \mathrm{PairIndex}(q)}
    \#\{y : p,r \subseteq \mathrm{Coll}(y)\}.
\]

The proof reuses the existing `powersetCard` bookkeeping for
`pairCollisionSet`; the remaining mathematical task is to evaluate the
two-pair fiber cardinality uniformly as `|G|^(q-2)`. -/
theorem sum_pairCollisionCountNat_choose_two_eq_pairPairCollisionFiberCard
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    (∑ y : Fin q → G, (pairCollisionCountNat G q y).choose 2) =
      ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
        pairPairCollisionFiberCard G S := by
  classical
  calc
    (∑ y : Fin q → G, (pairCollisionCountNat G q y).choose 2) =
        ∑ y : Fin q → G, (pairCollisionSet G y).card.choose 2 := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [pairCollisionSet_card (G := G) (q := q) y]
    _ = ∑ y : Fin q → G, ((pairCollisionSet G y).powersetCard 2).card := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [Finset.card_powersetCard]
    _ = ∑ y : Fin q → G,
          (((Finset.univ : Finset (PairIndex q)).powersetCard 2).filter
            (fun S => S ⊆ pairCollisionSet G y)).card := by
          apply Finset.sum_congr rfl
          intro y _hy
          congr 1
          ext S
          simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
            true_and]
          constructor <;> intro h
          · exact ⟨h.2, h.1⟩
          · exact ⟨h.2, h.1⟩
    _ = ∑ y : Fin q → G,
          ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
            (if S ⊆ pairCollisionSet G y then 1 else 0 : Nat) := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
          ∑ y : Fin q → G,
            (if S ⊆ pairCollisionSet G y then 1 else 0 : Nat) := by
          exact Finset.sum_comm
    _ = ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
          pairPairCollisionFiberCard G S := by
          apply Finset.sum_congr rfl
          intro S _hS
          unfold pairPairCollisionFiberCard
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Real uniform-average form of
`sum_pairCollisionCountNat_choose_two_eq_pairPairCollisionFiberCard`. -/
theorem uniformAverage_pairCollisionCountNat_choose_two_eq_pairPairCollisionFiberCard
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y => ((pairCollisionCountNat G q y).choose 2 : ℝ)) =
      (∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
        (pairPairCollisionFiberCard G S : ℝ)) /
        (Fintype.card (Fin q → G) : ℝ) := by
  unfold XoP.ANOVA.uniformAverage
  have hsumNat :=
    sum_pairCollisionCountNat_choose_two_eq_pairPairCollisionFiberCard
      (G := G) (q := q)
  have hsumReal :
      (∑ y : Fin q → G, ((pairCollisionCountNat G q y).choose 2 : ℝ)) =
        (∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
          (pairPairCollisionFiberCard G S : ℝ)) := by
    exact_mod_cast hsumNat
  rw [hsumReal]

/-- Uniformity obligation for two visible pair-collision fibers.  This is the
local combinatorial statement needed to close the second factorial moment of
the visible pair-collision count. -/
def PairPairCollisionFiberUniform
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Prop :=
  ∀ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
    pairPairCollisionFiberCard G S = Fintype.card G ^ (q - 2)

/-- If every two-pair visible-collision fiber has size `|G|^(q-2)`, then the
second factorial moment of the visible pair-collision count is
`choose(#PairIndex, 2) / |G|^2`. -/
theorem uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q)
    (hfiber : PairPairCollisionFiberUniform G q) :
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y => ((pairCollisionCountNat G q y).choose 2 : ℝ)) =
      ((Fintype.card (PairIndex q)).choose 2 : ℝ) /
        (Fintype.card G : ℝ) ^ 2 := by
  rw [uniformAverage_pairCollisionCountNat_choose_two_eq_pairPairCollisionFiberCard
    (G := G) (q := q)]
  have hsum :
      (∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
        (pairPairCollisionFiberCard G S : ℝ)) =
        (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) *
          (Fintype.card G : ℝ) ^ (q - 2) := by
    calc
      (∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
        (pairPairCollisionFiberCard G S : ℝ)) =
          ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
            ((Fintype.card G ^ (q - 2) : Nat) : ℝ) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [hfiber S hS]
      _ = (((Finset.univ : Finset (PairIndex q)).powersetCard 2).card : ℝ) *
            ((Fintype.card G ^ (q - 2) : Nat) : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ = (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) *
            (Fintype.card G : ℝ) ^ (q - 2) := by
            rw [Finset.card_powersetCard]
            simp only [Finset.card_univ, Nat.cast_pow]
  rw [hsum]
  have hcardFun : Fintype.card (Fin q → G) = Fintype.card G ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hcardFun]
  have hN_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hN_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hpow : q - 2 + 2 = q := Nat.sub_add_cancel hq2
  have hpowR :
      (Fintype.card G : ℝ) ^ q =
        (Fintype.card G : ℝ) ^ (q - 2) * (Fintype.card G : ℝ) ^ 2 := by
    rw [← pow_add, hpow]
  simp only [Nat.cast_pow]
  rw [hpowR]
  field_simp [hN_ne]

/-- The rank-one coefficient is the visible collision count minus twice the
number of query pairs. -/
theorem pairCoefficient_sum_eq_pairCollisionCountInt_sub_two_pairIndex
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    (∑ p : PairIndex q, (-2 + (if y p.1.2 = y p.1.1 then 1 else 0) : ℤ)) =
      pairCollisionCountInt G q y - 2 * (Fintype.card (PairIndex q) : ℤ) := by
  unfold pairCollisionCountInt
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_const]
  ring

/-! ### Rank-two support bookkeeping -/

/-- The query-pair support of a collision-event subfamily, forgetting whether
each selected event is hidden or shifted. -/
def collisionSubfamilyPairSupport (q : Nat)
    (T : Finset (CollisionEvent q)) : Finset (PairIndex q) :=
  T.image (fun e => e.1)

/-- Membership in the pair support is membership of some hidden/shifted event
over that query pair. -/
theorem mem_collisionSubfamilyPairSupport_iff
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q} :
    p ∈ collisionSubfamilyPairSupport q T ↔
      ∃ k : CollisionKind, (p, k) ∈ T := by
  unfold collisionSubfamilyPairSupport
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨e, heT, heq⟩
    subst p
    exact ⟨e.2, heT⟩
  · intro hp
    rcases hp with ⟨k, hkT⟩
    exact Finset.mem_image.mpr ⟨(p, k), hkT, rfl⟩

/-- The fiber of a collision-event subfamily over one query pair. -/
def collisionSubfamilyPairFiber
    {q : Nat} (T : Finset (CollisionEvent q)) (p : PairIndex q) :
    Finset (CollisionEvent q) :=
  T ∩ collisionPairEvents (q := q) p

/-- Pair-fiber membership is just membership in `T` with the underlying query
pair fixed. -/
theorem mem_collisionSubfamilyPairFiber_iff
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    {e : CollisionEvent q} :
    e ∈ collisionSubfamilyPairFiber (q := q) T p ↔ e ∈ T ∧ e.1 = p := by
  constructor
  · intro he
    simp only [collisionSubfamilyPairFiber, Finset.mem_inter] at he
    exact ⟨he.1, collisionEvent_pairIndex_eq_of_mem_collisionPairEvents
      (q := q) he.2⟩
  · rintro ⟨heT, hep⟩
    rcases e with ⟨p', k⟩
    simp only at hep
    subst p'
    cases k <;> simp [collisionSubfamilyPairFiber, collisionPairEvents, heT]

/-- A pair-local fiber is nonempty exactly when its query pair lies in the pair
support. -/
theorem collisionSubfamilyPairFiber_nonempty_iff
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q} :
    (collisionSubfamilyPairFiber (q := q) T p).Nonempty ↔
      p ∈ collisionSubfamilyPairSupport q T := by
  constructor
  · rintro ⟨e, he⟩
    rw [mem_collisionSubfamilyPairSupport_iff]
    have hef := (mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
      (p := p) (e := e)).mp he
    rcases e with ⟨p', k⟩
    simp only at hef
    exact ⟨k, by simpa [hef.2] using hef.1⟩
  · intro hp
    rcases (mem_collisionSubfamilyPairSupport_iff (T := T) (p := p)).mp hp with
      ⟨k, hk⟩
    exact ⟨(p, k), (mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
      (p := p) (e := (p, k))).mpr ⟨hk, rfl⟩⟩

/-- A collision subfamily is the disjoint union of its nonempty pair-local
fibers over its pair support. -/
theorem collisionSubfamily_eq_biUnion_pairSupport_fibers
    {q : Nat} (T : Finset (CollisionEvent q)) :
    (collisionSubfamilyPairSupport q T).biUnion
      (fun p => collisionSubfamilyPairFiber (q := q) T p) = T := by
  ext e
  constructor
  · intro he
    simp only [Finset.mem_biUnion] at he
    rcases he with ⟨p, _hp, hef⟩
    exact ((mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
      (p := p) (e := e)).mp hef).1
  · intro heT
    simp only [Finset.mem_biUnion]
    refine ⟨e.1, ?_, ?_⟩
    · exact (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr
        ⟨e.2, heT⟩
    · exact (mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
        (p := e.1) (e := e)).mpr ⟨heT, rfl⟩

/-- Pair-local fibers over distinct query pairs are disjoint. -/
theorem collisionSubfamilyPairFiber_pairwiseDisjoint
    {q : Nat} (T : Finset (CollisionEvent q)) :
    (↑(collisionSubfamilyPairSupport q T) : Set (PairIndex q)).PairwiseDisjoint
      (fun p => collisionSubfamilyPairFiber (q := q) T p) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro p _hp p' _hp' hnonempty
  rcases hnonempty with ⟨e, he⟩
  have hp := ((mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
    (p := p) (e := e)).mp (Finset.mem_inter.mp he).1).2
  have hp' := ((mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
    (p := p') (e := e)).mp (Finset.mem_inter.mp he).2).2
  exact hp.symm.trans hp'

/-- The cardinalities of pair-local fibers sum to the cardinality of the
original collision-event subfamily. -/
theorem sum_pairFiber_card_eq_card
    {q : Nat} (T : Finset (CollisionEvent q)) :
    (∑ p ∈ collisionSubfamilyPairSupport q T,
      (collisionSubfamilyPairFiber (q := q) T p).card) = T.card := by
  have hcard := Finset.card_biUnion
    (s := collisionSubfamilyPairSupport q T)
    (t := fun p => collisionSubfamilyPairFiber (q := q) T p)
    (collisionSubfamilyPairFiber_pairwiseDisjoint (q := q) T)
  rw [collisionSubfamily_eq_biUnion_pairSupport_fibers (q := q) T] at hcard
  simpa using hcard.symm

/-- A pair-local fiber is contained in the two-event family over that pair. -/
theorem collisionSubfamilyPairFiber_subset_pairEvents
    {q : Nat} (T : Finset (CollisionEvent q)) (p : PairIndex q) :
    collisionSubfamilyPairFiber (q := q) T p ⊆ collisionPairEvents (q := q) p := by
  intro e he
  exact (Finset.mem_inter.mp he).2

/-- Pair-local fibers have cardinality at most two. -/
theorem collisionSubfamilyPairFiber_card_le_two
    {q : Nat} (T : Finset (CollisionEvent q)) (p : PairIndex q) :
    (collisionSubfamilyPairFiber (q := q) T p).card ≤ 2 := by
  calc
    (collisionSubfamilyPairFiber (q := q) T p).card ≤
        (collisionPairEvents (q := q) p).card :=
      Finset.card_le_card (collisionSubfamilyPairFiber_subset_pairEvents (q := q) T p)
    _ = 2 := by
      simp [collisionPairEvents, collisionKind_hidden_ne_shifted]

/-- Every pair-local fiber indexed by the pair support is nonempty. -/
theorem collisionSubfamilyPairFiber_card_pos_of_mem_support
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    (hp : p ∈ collisionSubfamilyPairSupport q T) :
    0 < (collisionSubfamilyPairFiber (q := q) T p).card := by
  exact Finset.card_pos.mpr
    ((collisionSubfamilyPairFiber_nonempty_iff (q := q) (T := T) (p := p)).mpr hp)

/-- Every touched pair-local fiber is either a singleton event or the full
hidden/shifted pair. -/
theorem collisionSubfamilyPairFiber_card_eq_one_or_two_of_mem_support
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    (hp : p ∈ collisionSubfamilyPairSupport q T) :
    (collisionSubfamilyPairFiber (q := q) T p).card = 1 ∨
      (collisionSubfamilyPairFiber (q := q) T p).card = 2 := by
  have hpos := collisionSubfamilyPairFiber_card_pos_of_mem_support
    (q := q) (T := T) (p := p) hp
  have hle := collisionSubfamilyPairFiber_card_le_two (q := q) T p
  omega

/-- A two-element pair-local fiber is the full hidden/shifted pair-local event
family. -/
theorem collisionSubfamilyPairFiber_eq_pairEvents_of_card_eq_two
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    (hcard : (collisionSubfamilyPairFiber (q := q) T p).card = 2) :
    collisionSubfamilyPairFiber (q := q) T p = collisionPairEvents (q := q) p := by
  apply Finset.eq_of_subset_of_card_le
  · exact collisionSubfamilyPairFiber_subset_pairEvents (q := q) T p
  · rw [hcard]
    simp [collisionPairEvents, collisionKind_hidden_ne_shifted]

/-- A one-element pair-local fiber is a singleton event over the indexed query
pair. -/
theorem exists_collisionSubfamilyPairFiber_eq_singleton_of_card_eq_one
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    (hcard : (collisionSubfamilyPairFiber (q := q) T p).card = 1) :
    ∃ k : CollisionKind,
      collisionSubfamilyPairFiber (q := q) T p = {(p, k)} := by
  rcases Finset.card_eq_one.mp hcard with ⟨e, heq⟩
  have he_mem : e ∈ collisionSubfamilyPairFiber (q := q) T p := by
    rw [heq]
    simp
  have hep := ((mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
    (p := p) (e := e)).mp he_mem).2
  rcases e with ⟨p', k⟩
  simp only at hep
  exact ⟨k, by simpa [hep] using heq⟩

/-- If a collision subfamily touches exactly two query pairs, then its
cardinality is at least two. -/
theorem collisionSubfamily_card_two_le_of_pairSupport_card_eq_two
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hsupport : (collisionSubfamilyPairSupport q T).card = 2) :
    2 ≤ T.card := by
  have hsum := sum_pairFiber_card_eq_card (q := q) T
  calc
    2 = (collisionSubfamilyPairSupport q T).card := hsupport.symm
    _ = ∑ _p ∈ collisionSubfamilyPairSupport q T, 1 := by
      simp
    _ ≤ ∑ p ∈ collisionSubfamilyPairSupport q T,
        (collisionSubfamilyPairFiber (q := q) T p).card := by
          exact Finset.sum_le_sum (fun _p hp =>
            collisionSubfamilyPairFiber_card_pos_of_mem_support (q := q) (T := T) hp)
    _ = T.card := hsum

/-- If a collision subfamily touches exactly two query pairs, then its
cardinality is at most four. -/
theorem collisionSubfamily_card_le_four_of_pairSupport_card_eq_two
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hsupport : (collisionSubfamilyPairSupport q T).card = 2) :
    T.card ≤ 4 := by
  rw [← sum_pairFiber_card_eq_card (q := q) T]
  calc
    (∑ p ∈ collisionSubfamilyPairSupport q T,
      (collisionSubfamilyPairFiber (q := q) T p).card) ≤
        ∑ _p ∈ collisionSubfamilyPairSupport q T, 2 := by
          exact Finset.sum_le_sum (fun p _hp =>
            collisionSubfamilyPairFiber_card_le_two (q := q) T p)
    _ = 2 * (collisionSubfamilyPairSupport q T).card := by
          simp [mul_comm]
    _ = 4 := by omega

/-- Support-size-two subfamilies have only the three event-cardinality cases
that arise from two nonempty pair-local fibers of size at most two. -/
theorem collisionSubfamily_card_eq_two_or_three_or_four_of_pairSupport_card_eq_two
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hsupport : (collisionSubfamilyPairSupport q T).card = 2) :
    T.card = 2 ∨ T.card = 3 ∨ T.card = 4 := by
  have hle := collisionSubfamily_card_le_four_of_pairSupport_card_eq_two
    (q := q) (T := T) hsupport
  have hge := collisionSubfamily_card_two_le_of_pairSupport_card_eq_two
    (q := q) (T := T) hsupport
  omega

/-- Every touched query pair has connected endpoints in the support graph of
the collision-event subfamily. -/
theorem collisionSubfamilyPairSupport_connected
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    (hp : p ∈ collisionSubfamilyPairSupport q T) :
    collisionSubfamilyConnected (q := q) T p.1.1 p.1.2 := by
  rcases (mem_collisionSubfamilyPairSupport_iff (T := T) (p := p)).mp hp with
    ⟨k, hkT⟩
  exact Relation.ReflTransGen.single ⟨(p, k), hkT, Or.inl ⟨rfl, rfl⟩⟩

/-- Pair-support endpoints lie in the same connected component of the
collision-event support graph. -/
theorem collisionSubfamilyPairSupport_component_eq
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    (hp : p ∈ collisionSubfamilyPairSupport q T) :
    (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) p.1.1 :
      collisionSubfamilyComponent (q := q) T) =
    Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) p.1.2 := by
  apply Quotient.sound
  exact collisionSubfamilyPairSupport_connected (q := q) (T := T) (p := p) hp

/-- Vertices belonging to a fixed connected component of a collision-event
support graph. -/
def collisionSubfamilyComponentVertexSet
    {q : Nat} (T : Finset (CollisionEvent q))
    (c : collisionSubfamilyComponent (q := q) T) : Finset (Fin q) :=
  (Finset.univ : Finset (Fin q)).filter
    (fun i => (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
      collisionSubfamilyComponent (q := q) T) = c)

/-- Every support component contains at least one query coordinate. -/
theorem collisionSubfamilyComponentVertexSet_nonempty
    {q : Nat} (T : Finset (CollisionEvent q))
    (c : collisionSubfamilyComponent (q := q) T) :
    (collisionSubfamilyComponentVertexSet (q := q) T c).Nonempty := by
  induction c using Quotient.inductionOn with
  | h i =>
      exact ⟨i, by simp [collisionSubfamilyComponentVertexSet]⟩

/-- Component vertex sets are pairwise disjoint. -/
theorem collisionSubfamilyComponentVertexSet_pairwiseDisjoint
    {q : Nat} (T : Finset (CollisionEvent q)) :
    (↑(Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)) :
      Set (collisionSubfamilyComponent (q := q) T)).PairwiseDisjoint
      (fun c => collisionSubfamilyComponentVertexSet (q := q) T c) := by
  rw [Finset.pairwiseDisjoint_iff]
  intro c _hc d _hd hnonempty
  rcases hnonempty with ⟨i, hi⟩
  simp only [Finset.mem_inter, collisionSubfamilyComponentVertexSet, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi
  exact hi.1.symm.trans hi.2

/-- Component vertex sets cover all query coordinates. -/
theorem collisionSubfamilyComponentVertexSet_biUnion_eq_univ
    {q : Nat} (T : Finset (CollisionEvent q)) :
    (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
      (fun c => collisionSubfamilyComponentVertexSet (q := q) T c) =
    (Finset.univ : Finset (Fin q)) := by
  ext i
  constructor
  · intro _hi
    simp
  · intro _hi
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨(Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
      collisionSubfamilyComponent (q := q) T), ?_⟩
    simp [collisionSubfamilyComponentVertexSet]

/-- The component vertex-set cardinalities sum to the number of query
coordinates. -/
theorem sum_componentVertexSet_card_eq_query
    {q : Nat} (T : Finset (CollisionEvent q)) :
    (∑ c : collisionSubfamilyComponent (q := q) T,
      (collisionSubfamilyComponentVertexSet (q := q) T c).card) = q := by
  have hcard := Finset.card_biUnion
    (s := (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)))
    (t := fun c => collisionSubfamilyComponentVertexSet (q := q) T c)
    (collisionSubfamilyComponentVertexSet_pairwiseDisjoint (q := q) T)
  rw [collisionSubfamilyComponentVertexSet_biUnion_eq_univ (q := q) T] at hcard
  simpa [Fintype.card_fin] using hcard.symm

/-- The sum of component excesses `|C|-1` is the graphic rank. -/
theorem sum_componentVertexSet_card_sub_one_eq_graphicRank
    {q : Nat} (T : Finset (CollisionEvent q)) :
    (∑ c : collisionSubfamilyComponent (q := q) T,
      ((collisionSubfamilyComponentVertexSet (q := q) T c).card - 1)) =
    collisionSubfamilyGraphicRank (q := q) T := by
  have hdist := Finset.sum_tsub_distrib
    (s := (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)))
    (f := fun c => (collisionSubfamilyComponentVertexSet (q := q) T c).card)
    (g := fun _c => 1)
    (by
      intro c _hc
      exact Nat.succ_le_iff.mpr
        (Finset.card_pos.mpr
          (collisionSubfamilyComponentVertexSet_nonempty (q := q) T c)))
  rw [hdist, sum_componentVertexSet_card_eq_query (q := q) T]
  simp [collisionSubfamilyGraphicRank, collisionSubfamilyComponentCount]

/-- Query pairs whose endpoints both lie in a fixed set of query coordinates. -/
def queryPairSet {q : Nat} (S : Finset (Fin q)) : Finset (PairIndex q) :=
  (Finset.univ : Finset (PairIndex q)).filter
    (fun p => p.1.1 ∈ S ∧ p.1.2 ∈ S)

/-- If every touched query pair is internal to `S`, then every support-graph
adjacency step ends in `S`. -/
theorem collisionSubfamilyAdjacent_mem_of_pairSupport_subset_queryPairSet
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (Fin q)}
    (hsupport : collisionSubfamilyPairSupport q T ⊆ queryPairSet S)
    {i j : Fin q}
    (hadj : collisionSubfamilyAdjacent (q := q) T i j) :
    j ∈ S := by
  rcases hadj with ⟨e, heT, hends | hends⟩
  · have hp : e.1 ∈ collisionSubfamilyPairSupport q T :=
      (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr ⟨e.2, heT⟩
    have hpS : e.1 ∈ queryPairSet S := hsupport hp
    simp only [queryPairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hpS
    simpa [collisionEventRight, hends.2.symm] using hpS.2
  · have hp : e.1 ∈ collisionSubfamilyPairSupport q T :=
      (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr ⟨e.2, heT⟩
    have hpS : e.1 ∈ queryPairSet S := hsupport hp
    simp only [queryPairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hpS
    simpa [collisionEventLeft, hends.1.symm] using hpS.1

/-- If every touched query pair is internal to `S`, then support-graph
connectivity starting in `S` also ends in `S`. -/
theorem collisionSubfamilyConnected_mem_of_pairSupport_subset_queryPairSet
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (Fin q)}
    (hsupport : collisionSubfamilyPairSupport q T ⊆ queryPairSet S)
    {i j : Fin q}
    (hconn : collisionSubfamilyConnected (q := q) T i j)
    (hi : i ∈ S) :
    j ∈ S := by
  induction hconn with
  | refl => exact hi
  | tail _hprev hadj ih =>
      exact collisionSubfamilyAdjacent_mem_of_pairSupport_subset_queryPairSet
        (q := q) (T := T) (S := S) hsupport hadj

/-- If every touched query pair is internal to `S`, then a vertex outside `S`
is isolated in the support graph. -/
theorem collisionSubfamilyConnected_eq_of_not_mem_of_pairSupport_subset_queryPairSet
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (Fin q)}
    (hsupport : collisionSubfamilyPairSupport q T ⊆ queryPairSet S)
    {i j : Fin q}
    (hi : i ∉ S)
    (hconn : collisionSubfamilyConnected (q := q) T i j) :
    j = i := by
  induction hconn with
  | refl => rfl
  | tail _hprev hadj ih =>
      rename_i b c
      rw [ih] at hadj
      have hi_mem : i ∈ S :=
        collisionSubfamilyAdjacent_mem_of_pairSupport_subset_queryPairSet
          (q := q) (T := T) (S := S) hsupport
          ((collisionSubfamilyAdjacent_symm (q := q) T) hadj)
      exact False.elim (hi hi_mem)

/-- A support component containing one vertex of `S` is wholly contained in
`S`, provided all touched query pairs are internal to `S`. -/
theorem collisionSubfamilyComponentVertexSet_subset_of_mem_of_pairSupport_subset_queryPairSet
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (Fin q)}
    (hsupport : collisionSubfamilyPairSupport q T ⊆ queryPairSet S)
    {c : collisionSubfamilyComponent (q := q) T} {i : Fin q}
    (hic : (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
      collisionSubfamilyComponent (q := q) T) = c)
    (hi : i ∈ S) :
    collisionSubfamilyComponentVertexSet (q := q) T c ⊆ S := by
  intro j hj
  simp only [collisionSubfamilyComponentVertexSet, Finset.mem_filter,
    Finset.mem_univ, true_and] at hj
  have hquot :
      (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
        collisionSubfamilyComponent (q := q) T) =
      Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) j := by
    exact hic.trans hj.symm
  have hconn : collisionSubfamilyConnected (q := q) T i j := by
    simpa [collisionSubfamilyConnectedSetoid] using Quotient.exact hquot
  exact collisionSubfamilyConnected_mem_of_pairSupport_subset_queryPairSet
    (q := q) (T := T) (S := S) hsupport hconn hi

/-- A component represented by a vertex outside `S` is the singleton containing
that vertex, provided all touched query pairs are internal to `S`. -/
theorem collisionSubfamilyComponentVertexSet_eq_singleton_of_not_mem_of_pairSupport_subset_queryPairSet
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (Fin q)}
    (hsupport : collisionSubfamilyPairSupport q T ⊆ queryPairSet S)
    {c : collisionSubfamilyComponent (q := q) T} {i : Fin q}
    (hic : (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
      collisionSubfamilyComponent (q := q) T) = c)
    (hi : i ∉ S) :
    collisionSubfamilyComponentVertexSet (q := q) T c = {i} := by
  ext j
  constructor
  · intro hj
    simp only [collisionSubfamilyComponentVertexSet, Finset.mem_filter,
      Finset.mem_univ, true_and] at hj
    have hquot :
        (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
          collisionSubfamilyComponent (q := q) T) =
        Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) j := by
      exact hic.trans hj.symm
    have hconn : collisionSubfamilyConnected (q := q) T i j := by
      simpa [collisionSubfamilyConnectedSetoid] using Quotient.exact hquot
    have hji : j = i :=
      collisionSubfamilyConnected_eq_of_not_mem_of_pairSupport_subset_queryPairSet
        (q := q) (T := T) (S := S) hsupport hi hconn
    simp [hji]
  · intro hj
    simp only [Finset.mem_singleton] at hj
    subst j
    simp [collisionSubfamilyComponentVertexSet, hic]

/-- The `PairIndex` determined by two distinct query coordinates, oriented in
increasing order. -/
def pairIndexOfNe {q : Nat} (i j : Fin q) (hij : i ≠ j) : PairIndex q :=
  if hlt : i < j then
    ⟨(i, j), hlt⟩
  else
    ⟨(j, i), lt_of_le_of_ne (le_of_not_gt hlt) hij.symm⟩

/-- The left endpoint of `pairIndexOfNe i j` is one of `i,j`. -/
theorem pairIndexOfNe_left_mem_pair
    {q : Nat} {i j : Fin q} (hij : i ≠ j) :
    (pairIndexOfNe i j hij).1.1 ∈ ({i, j} : Finset (Fin q)) := by
  unfold pairIndexOfNe
  by_cases hlt : i < j <;> simp [hlt]

/-- The right endpoint of `pairIndexOfNe i j` is one of `i,j`. -/
theorem pairIndexOfNe_right_mem_pair
    {q : Nat} {i j : Fin q} (hij : i ≠ j) :
    (pairIndexOfNe i j hij).1.2 ∈ ({i, j} : Finset (Fin q)) := by
  unfold pairIndexOfNe
  by_cases hlt : i < j <;> simp [hlt]

/-- The canonical pair index for two vertices in `S` is internal to `S`. -/
theorem pairIndexOfNe_mem_queryPairSet
    {q : Nat} {S : Finset (Fin q)} {i j : Fin q}
    (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    pairIndexOfNe i j hij ∈ queryPairSet S := by
  unfold queryPairSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold pairIndexOfNe
  by_cases hlt : i < j
  · simp [hlt, hi, hj]
  · simp [hlt, hi, hj]

/-- Under exact internal pair support on `S`, any two vertices of `S` are
connected in the support graph. -/
theorem collisionSubfamilyConnected_of_mem_of_mem_of_pairSupport_eq_queryPairSet
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (Fin q)}
    (hsupport : collisionSubfamilyPairSupport q T = queryPairSet S)
    {i j : Fin q} (hi : i ∈ S) (hj : j ∈ S) :
    collisionSubfamilyConnected (q := q) T i j := by
  by_cases hij : i = j
  · subst j
    exact collisionSubfamilyConnected_refl (q := q) T i
  · let p : PairIndex q := pairIndexOfNe i j hij
    have hp : p ∈ collisionSubfamilyPairSupport q T := by
      rw [hsupport]
      exact pairIndexOfNe_mem_queryPairSet hij hi hj
    have hconn := collisionSubfamilyPairSupport_connected (q := q) (T := T) (p := p) hp
    unfold p pairIndexOfNe at hconn
    by_cases hlt : i < j
    · simpa [hlt] using hconn
    · have hconn' := (collisionSubfamilyConnected_symm (q := q) T) hconn
      simpa [hlt] using hconn'

/-- Under exact internal pair support on `S`, the component containing one
vertex of `S` has vertex set exactly `S`. -/
theorem collisionSubfamilyComponentVertexSet_eq_of_mem_of_pairSupport_eq_queryPairSet
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (Fin q)}
    (hsupport : collisionSubfamilyPairSupport q T = queryPairSet S)
    {c : collisionSubfamilyComponent (q := q) T} {i : Fin q}
    (hic : (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
      collisionSubfamilyComponent (q := q) T) = c)
    (hi : i ∈ S) :
    collisionSubfamilyComponentVertexSet (q := q) T c = S := by
  ext j
  constructor
  · intro hj
    exact collisionSubfamilyComponentVertexSet_subset_of_mem_of_pairSupport_subset_queryPairSet
      (q := q) (T := T) (S := S) (by rw [hsupport]) hic hi hj
  · intro hj
    simp only [collisionSubfamilyComponentVertexSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hconn : collisionSubfamilyConnected (q := q) T i j :=
      collisionSubfamilyConnected_of_mem_of_mem_of_pairSupport_eq_queryPairSet
        (q := q) (T := T) (S := S) hsupport hi hj
    exact (Quotient.sound (by
      simpa [collisionSubfamilyConnectedSetoid] using hconn)).symm.trans hic

/-- `pairIndexOfNe` has exactly the two endpoints it was built from. -/
theorem pairIndexOfNe_endpointSet
    {q : Nat} {i j : Fin q} (hij : i ≠ j) :
    ({(pairIndexOfNe i j hij).1.1, (pairIndexOfNe i j hij).1.2} :
        Finset (Fin q)) = {i, j} := by
  unfold pairIndexOfNe
  by_cases hlt : i < j
  · simp [hlt]
  · simpa [hlt] using (Finset.pair_comm j i)

/-- If the canonical pair for `i,j` is internal to `S`, then `i` lies in `S`. -/
theorem pairIndexOfNe_leftOriginal_mem_of_mem_queryPairSet
    {q : Nat} {S : Finset (Fin q)} {i j : Fin q} (hij : i ≠ j)
    (hp : pairIndexOfNe i j hij ∈ queryPairSet S) :
    i ∈ S := by
  have hends :
      (pairIndexOfNe i j hij).1.1 ∈ S ∧
        (pairIndexOfNe i j hij).1.2 ∈ S := by
    simpa [queryPairSet] using hp
  have hi_end :
      i ∈ ({(pairIndexOfNe i j hij).1.1, (pairIndexOfNe i j hij).1.2} :
          Finset (Fin q)) := by
    rw [pairIndexOfNe_endpointSet hij]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi_end
  rcases hi_end with hi_left | hi_right
  · rw [hi_left]
    exact hends.1
  · rw [hi_right]
    exact hends.2

/-- If the canonical pair for `i,j` is internal to `S`, then `j` lies in `S`. -/
theorem pairIndexOfNe_rightOriginal_mem_of_mem_queryPairSet
    {q : Nat} {S : Finset (Fin q)} {i j : Fin q} (hij : i ≠ j)
    (hp : pairIndexOfNe i j hij ∈ queryPairSet S) :
    j ∈ S := by
  have hends :
      (pairIndexOfNe i j hij).1.1 ∈ S ∧
        (pairIndexOfNe i j hij).1.2 ∈ S := by
    simpa [queryPairSet] using hp
  have hj_end :
      j ∈ ({(pairIndexOfNe i j hij).1.1, (pairIndexOfNe i j hij).1.2} :
          Finset (Fin q)) := by
    rw [pairIndexOfNe_endpointSet hij]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj_end
  rcases hj_end with hj_left | hj_right
  · rw [hj_left]
    exact hends.1
  · rw [hj_right]
    exact hends.2

/-- Two canonical query pairs are distinct whenever their endpoint sets are
distinct. -/
theorem pairIndexOfNe_ne_of_endpointSet_ne
    {q : Nat} {i j k l : Fin q} (hij : i ≠ j) (hkl : k ≠ l)
    (hset : ({i, j} : Finset (Fin q)) ≠ {k, l}) :
    pairIndexOfNe i j hij ≠ pairIndexOfNe k l hkl := by
  intro h
  apply hset
  rw [← pairIndexOfNe_endpointSet hij, ← pairIndexOfNe_endpointSet hkl, h]

/-- Query pairs internal to a vertex set inject into the two-element subsets of
that vertex set. -/
theorem queryPairSet_card_le_choose
    {q : Nat} (S : Finset (Fin q)) :
    (queryPairSet S).card ≤ S.card.choose 2 := by
  calc
    (queryPairSet S).card ≤ (S.powersetCard 2).card := by
        refine Finset.card_le_card_of_injOn
          (fun p : PairIndex q => ({p.1.1, p.1.2} : Finset (Fin q))) ?_ ?_
        · intro p hp
          simp only [Finset.mem_coe] at hp ⊢
          simp only [Finset.mem_powersetCard]
          simp only [queryPairSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨hleft, hright⟩
          constructor
          · intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hleft
            · exact hright
          · simp [ne_of_lt p.2]
        · intro p _hp r _hr hset
          have hp_left_mem : p.1.1 ∈ ({r.1.1, r.1.2} : Finset (Fin q)) := by
            change p.1.1 ∈ (fun p : PairIndex q =>
              ({p.1.1, p.1.2} : Finset (Fin q))) r
            rw [← hset]
            simp
          have hp_right_mem : p.1.2 ∈ ({r.1.1, r.1.2} : Finset (Fin q)) := by
            change p.1.2 ∈ (fun p : PairIndex q =>
              ({p.1.1, p.1.2} : Finset (Fin q))) r
            rw [← hset]
            simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hp_left_mem hp_right_mem
          rcases hp_left_mem with hll | hlr
          · rcases hp_right_mem with hrl | hrr
            · exfalso
              have hbad : p.1.1 = p.1.2 := hll.trans hrl.symm
              exact (ne_of_lt p.2) hbad
            · apply Subtype.ext
              exact Prod.ext hll hrr
          · rcases hp_right_mem with hrl | hrr
            · exfalso
              have hbad : r.1.2 < r.1.1 := by
                calc
                  r.1.2 = p.1.1 := hlr.symm
                  _ < p.1.2 := p.2
                  _ = r.1.1 := hrl
              exact (not_lt_of_ge (le_of_lt r.2)) hbad
            · exfalso
              have hbad : p.1.1 = p.1.2 := hlr.trans hrr.symm
              exact (ne_of_lt p.2) hbad
    _ = S.card.choose 2 := by
      rw [Finset.card_powersetCard]

/-- A three-vertex query set has exactly the three internal query pairs. -/
theorem queryPairSet_card_eq_three_of_card_eq_three
    {q : Nat} {S : Finset (Fin q)} (hS : S.card = 3) :
    (queryPairSet S).card = 3 := by
  rcases Finset.card_eq_three.mp hS with ⟨i, j, k, hij, hik, hjk, hS_eq⟩
  let pij : PairIndex q := pairIndexOfNe i j hij
  let pik : PairIndex q := pairIndexOfNe i k hik
  let pjk : PairIndex q := pairIndexOfNe j k hjk
  have hi : i ∈ S := by rw [hS_eq]; simp
  have hj : j ∈ S := by rw [hS_eq]; simp
  have hk : k ∈ S := by rw [hS_eq]; simp
  have hpij : pij ∈ queryPairSet S := pairIndexOfNe_mem_queryPairSet hij hi hj
  have hpik : pik ∈ queryPairSet S := pairIndexOfNe_mem_queryPairSet hik hi hk
  have hpjk : pjk ∈ queryPairSet S := pairIndexOfNe_mem_queryPairSet hjk hj hk
  have hset_ij_ik : ({i, j} : Finset (Fin q)) ≠ {i, k} := by
    intro hset
    have hj_mem : j ∈ ({i, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : j ∈ ({i, j} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj_mem
    rcases hj_mem with hji | hjk_eq
    · exact hij hji.symm
    · exact hjk hjk_eq
  have hset_ij_jk : ({i, j} : Finset (Fin q)) ≠ {j, k} := by
    intro hset
    have hi_mem : i ∈ ({j, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : i ∈ ({i, j} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem
    rcases hi_mem with hij_eq | hik_eq
    · exact hij hij_eq
    · exact hik hik_eq
  have hset_ik_jk : ({i, k} : Finset (Fin q)) ≠ {j, k} := by
    intro hset
    have hi_mem : i ∈ ({j, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : i ∈ ({i, k} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem
    rcases hi_mem with hij_eq | hik_eq
    · exact hij hij_eq
    · exact hik hik_eq
  have hpij_ne_pik : pij ≠ pik := by
    exact pairIndexOfNe_ne_of_endpointSet_ne hij hik hset_ij_ik
  have hpij_ne_pjk : pij ≠ pjk := by
    exact pairIndexOfNe_ne_of_endpointSet_ne hij hjk hset_ij_jk
  have hpik_ne_pjk : pik ≠ pjk := by
    exact pairIndexOfNe_ne_of_endpointSet_ne hik hjk hset_ik_jk
  have htriple_subset :
      ({pij, pik, pjk} : Finset (PairIndex q)) ⊆ queryPairSet S := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact hpij
    · exact hpik
    · exact hpjk
  have htriple_card : ({pij, pik, pjk} : Finset (PairIndex q)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨pij, pik, pjk, hpij_ne_pik, hpij_ne_pjk, hpik_ne_pjk, rfl⟩
  have hle_lower : 3 ≤ (queryPairSet S).card := by
    calc
      3 = ({pij, pik, pjk} : Finset (PairIndex q)).card := htriple_card.symm
      _ ≤ (queryPairSet S).card := Finset.card_le_card htriple_subset
  have hle_upper : (queryPairSet S).card ≤ 3 := by
    have hchoose := queryPairSet_card_le_choose (q := q) S
    rw [hS] at hchoose
    norm_num at hchoose
    exact hchoose
  exact Nat.le_antisymm hle_upper hle_lower

/-- For an ordered visible triangle, `queryPairSet` is exactly the three
canonical internal query pairs.  This packages the finite-set bookkeeping used
by the local triangle coefficient calculation. -/
theorem queryPairSet_orderedTriple
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k) :
    queryPairSet ({i, j, k} : Finset (Fin q)) =
      ({pairIndexOfNe i j (ne_of_lt hij),
        pairIndexOfNe j k (ne_of_lt hjk),
        pairIndexOfNe i k (ne_of_lt (hij.trans hjk))} : Finset (PairIndex q)) := by
  have hik : i < k := hij.trans hjk
  let RHS : Finset (PairIndex q) :=
    {pairIndexOfNe i j (ne_of_lt hij),
      pairIndexOfNe j k (ne_of_lt hjk),
      pairIndexOfNe i k (ne_of_lt hik)}
  have hsub : RHS ⊆ queryPairSet ({i, j, k} : Finset (Fin q)) := by
    intro p hp
    simp only [RHS, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact pairIndexOfNe_mem_queryPairSet (ne_of_lt hij) (by simp) (by simp)
    · exact pairIndexOfNe_mem_queryPairSet (ne_of_lt hjk) (by simp) (by simp)
    · exact pairIndexOfNe_mem_queryPairSet (ne_of_lt hik) (by simp) (by simp)
  have htriple : ({i, j, k} : Finset (Fin q)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨i, j, k, ne_of_lt hij, ne_of_lt hik, ne_of_lt hjk, rfl⟩
  have hcardL : (queryPairSet ({i, j, k} : Finset (Fin q))).card = 3 :=
    queryPairSet_card_eq_three_of_card_eq_three htriple
  have hset_ij_jk : ({i, j} : Finset (Fin q)) ≠ {j, k} := by
    intro hset
    have hi_mem : i ∈ ({j, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : i ∈ ({i, j} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem
    rcases hi_mem with hij_eq | hik_eq
    · exact (ne_of_lt hij) hij_eq
    · exact (ne_of_lt hik) hik_eq
  have hset_ij_ik : ({i, j} : Finset (Fin q)) ≠ {i, k} := by
    intro hset
    have hj_mem : j ∈ ({i, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : j ∈ ({i, j} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj_mem
    rcases hj_mem with hji | hjk_eq
    · exact (ne_of_lt hij) hji.symm
    · exact (ne_of_lt hjk) hjk_eq
  have hset_jk_ik : ({j, k} : Finset (Fin q)) ≠ {i, k} := by
    intro hset
    have hj_mem : j ∈ ({i, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : j ∈ ({j, k} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj_mem
    rcases hj_mem with hji | hjk_eq
    · exact (ne_of_lt hij) hji.symm
    · exact (ne_of_lt hjk) hjk_eq
  have hpij_ne_pjk :
      pairIndexOfNe i j (ne_of_lt hij) ≠ pairIndexOfNe j k (ne_of_lt hjk) :=
    pairIndexOfNe_ne_of_endpointSet_ne (ne_of_lt hij) (ne_of_lt hjk) hset_ij_jk
  have hpij_ne_pik :
      pairIndexOfNe i j (ne_of_lt hij) ≠ pairIndexOfNe i k (ne_of_lt hik) :=
    pairIndexOfNe_ne_of_endpointSet_ne (ne_of_lt hij) (ne_of_lt hik) hset_ij_ik
  have hpjk_ne_pik :
      pairIndexOfNe j k (ne_of_lt hjk) ≠ pairIndexOfNe i k (ne_of_lt hik) :=
    pairIndexOfNe_ne_of_endpointSet_ne (ne_of_lt hjk) (ne_of_lt hik) hset_jk_ik
  have hcardR : RHS.card = 3 := by
    rw [Finset.card_eq_three]
    exact
      ⟨pairIndexOfNe i j (ne_of_lt hij), pairIndexOfNe j k (ne_of_lt hjk),
        pairIndexOfNe i k (ne_of_lt hik), hpij_ne_pjk, hpij_ne_pik,
        hpjk_ne_pik, rfl⟩
  have heq : RHS = queryPairSet ({i, j, k} : Finset (Fin q)) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcardL, hcardR])
  simpa [RHS, hik] using heq.symm

/-- Any three-coordinate set can be written as an ordered triple.  This wraps
Mathlib's `Finset.orderEmbOfFin` API so the local triangle coefficient lemmas
can work with ordered coordinates without redoing sorting arguments. -/
theorem exists_orderedTriple_eq_of_card_eq_three
    {q : Nat} {V : Finset (Fin q)} (hV : V.card = 3) :
    ∃ i j k : Fin q, i < j ∧ j < k ∧ V = {i, j, k} := by
  let e := V.orderEmbOfFin hV
  refine ⟨e ⟨0, by norm_num⟩, e ⟨1, by norm_num⟩, e ⟨2, by norm_num⟩, ?_, ?_, ?_⟩
  · exact e.strictMono (by decide)
  · exact e.strictMono (by decide)
  · have himage := Finset.image_orderEmbOfFin_univ (s := V) hV
    rw [← himage]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · intro hx
      rcases hx with ⟨a, rfl⟩
      fin_cases a <;> simp [e]
    · intro hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨⟨0, by norm_num⟩, by simp [e]⟩
      · exact ⟨⟨1, by norm_num⟩, by simp [e]⟩
      · exact ⟨⟨2, by norm_num⟩, by simp [e]⟩

/-- The three canonical query pairs of an ordered triangle are pairwise
distinct. -/
theorem pairIndexOfNe_orderedTriple_pairwise_ne
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k) :
    pairIndexOfNe i j (ne_of_lt hij) ≠ pairIndexOfNe j k (ne_of_lt hjk) ∧
    pairIndexOfNe i j (ne_of_lt hij) ≠ pairIndexOfNe i k (ne_of_lt (hij.trans hjk)) ∧
    pairIndexOfNe j k (ne_of_lt hjk) ≠
      pairIndexOfNe i k (ne_of_lt (hij.trans hjk)) := by
  have hik : i < k := hij.trans hjk
  have hset_ij_jk : ({i, j} : Finset (Fin q)) ≠ {j, k} := by
    intro hset
    have hi_mem : i ∈ ({j, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : i ∈ ({i, j} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi_mem
    rcases hi_mem with hij_eq | hik_eq
    · exact (ne_of_lt hij) hij_eq
    · exact (ne_of_lt hik) hik_eq
  have hset_ij_ik : ({i, j} : Finset (Fin q)) ≠ {i, k} := by
    intro hset
    have hj_mem : j ∈ ({i, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : j ∈ ({i, j} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj_mem
    rcases hj_mem with hji | hjk_eq
    · exact (ne_of_lt hij) hji.symm
    · exact (ne_of_lt hjk) hjk_eq
  have hset_jk_ik : ({j, k} : Finset (Fin q)) ≠ {i, k} := by
    intro hset
    have hj_mem : j ∈ ({i, k} : Finset (Fin q)) := by
      simpa [hset] using (by simp : j ∈ ({j, k} : Finset (Fin q)))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj_mem
    rcases hj_mem with hji | hjk_eq
    · exact (ne_of_lt hij) hji.symm
    · exact (ne_of_lt hjk) hjk_eq
  exact
    ⟨pairIndexOfNe_ne_of_endpointSet_ne (ne_of_lt hij) (ne_of_lt hjk) hset_ij_jk,
      pairIndexOfNe_ne_of_endpointSet_ne (ne_of_lt hij) (ne_of_lt hik) hset_ij_ik,
      pairIndexOfNe_ne_of_endpointSet_ne (ne_of_lt hjk) (ne_of_lt hik) hset_jk_ik⟩

/-- On three-coordinate vertex sets, the internal query-pair set determines the
vertex set. -/
theorem queryPairSet_injective_on_card_three
    {q : Nat} {V W : Finset (Fin q)}
    (hV : V.card = 3) (hW : W.card = 3)
    (hquery : queryPairSet V = queryPairSet W) :
    V = W := by
  have hsubset : V ⊆ W := by
    rcases Finset.card_eq_three.mp hV with ⟨i, j, k, hij, hik, hjk, hV_eq⟩
    intro x hx
    have hiW : i ∈ W := by
      have hpV : pairIndexOfNe i j hij ∈ queryPairSet V :=
        pairIndexOfNe_mem_queryPairSet hij (by rw [hV_eq]; simp) (by rw [hV_eq]; simp)
      have hpW : pairIndexOfNe i j hij ∈ queryPairSet W := by
        simpa [hquery] using hpV
      exact pairIndexOfNe_leftOriginal_mem_of_mem_queryPairSet hij hpW
    have hjW : j ∈ W := by
      have hpV : pairIndexOfNe i j hij ∈ queryPairSet V :=
        pairIndexOfNe_mem_queryPairSet hij (by rw [hV_eq]; simp) (by rw [hV_eq]; simp)
      have hpW : pairIndexOfNe i j hij ∈ queryPairSet W := by
        simpa [hquery] using hpV
      exact pairIndexOfNe_rightOriginal_mem_of_mem_queryPairSet hij hpW
    have hkW : k ∈ W := by
      have hpV : pairIndexOfNe i k hik ∈ queryPairSet V :=
        pairIndexOfNe_mem_queryPairSet hik (by rw [hV_eq]; simp) (by rw [hV_eq]; simp)
      have hpW : pairIndexOfNe i k hik ∈ queryPairSet W := by
        simpa [hquery] using hpV
      exact pairIndexOfNe_rightOriginal_mem_of_mem_queryPairSet hik hpW
    rw [hV_eq] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hiW
    · exact hjW
    · exact hkW
  exact Finset.eq_of_subset_of_card_le hsubset (by rw [hV, hW])

/-- Query pairs whose endpoints both lie in a fixed connected component of a
collision-event support graph. -/
def collisionSubfamilyComponentPairSet
    {q : Nat} (T : Finset (CollisionEvent q))
    (c : collisionSubfamilyComponent (q := q) T) : Finset (PairIndex q) :=
  queryPairSet (collisionSubfamilyComponentVertexSet (q := q) T c)

/-- A component with at most one vertex contains no query pair internally. -/
theorem collisionSubfamilyComponentPairSet_eq_empty_of_vertexSet_card_le_one
    {q : Nat} {T : Finset (CollisionEvent q)}
    {c : collisionSubfamilyComponent (q := q) T}
    (hcard : (collisionSubfamilyComponentVertexSet (q := q) T c).card ≤ 1) :
    collisionSubfamilyComponentPairSet (q := q) T c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  simp only [collisionSubfamilyComponentPairSet, queryPairSet, Finset.mem_filter, Finset.mem_univ,
    true_and] at hp
  have heq := (Finset.card_le_one_iff.mp hcard) hp.1 hp.2
  exact (ne_of_lt p.2) heq

/-- The pair support is contained in the union of component-internal query
pairs. -/
theorem collisionSubfamilyPairSupport_subset_biUnion_componentPairSet
    {q : Nat} (T : Finset (CollisionEvent q)) :
    collisionSubfamilyPairSupport q T ⊆
      (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
        (fun c => collisionSubfamilyComponentPairSet (q := q) T c) := by
  intro p hp
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  refine ⟨(Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) p.1.1 :
    collisionSubfamilyComponent (q := q) T), ?_⟩
  have hcomp := collisionSubfamilyPairSupport_component_eq (q := q) (T := T) (p := p) hp
  simp [collisionSubfamilyComponentPairSet, queryPairSet,
    collisionSubfamilyComponentVertexSet, hcomp.symm]

/-- The component-internal query pairs are bounded by the number of unordered
two-subsets of the component vertex set. -/
theorem collisionSubfamilyComponentPairSet_card_le_choose
    {q : Nat} (T : Finset (CollisionEvent q))
    (c : collisionSubfamilyComponent (q := q) T) :
    (collisionSubfamilyComponentPairSet (q := q) T c).card ≤
      (collisionSubfamilyComponentVertexSet (q := q) T c).card.choose 2 := by
  exact queryPairSet_card_le_choose (collisionSubfamilyComponentVertexSet (q := q) T c)

/-- A subfamily is contained in the union of pair-local event sets indexed by
its pair support. -/
theorem collisionSubfamily_subset_biUnion_pairSupport
    {q : Nat} (T : Finset (CollisionEvent q)) :
    T ⊆ (collisionSubfamilyPairSupport q T).biUnion
      (fun p => collisionPairEvents (q := q) p) := by
  intro e heT
  simp only [Finset.mem_biUnion]
  refine ⟨e.1, ?_, ?_⟩
  · exact (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr
      ⟨e.2, heT⟩
  · rcases e with ⟨p, k⟩
    cases k <;> simp [collisionPairEvents]

/-- Exact pair-support can be recognized by nonempty fibers over the claimed
support and absence of events over every other query pair. -/
theorem collisionSubfamilyPairSupport_eq_iff
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (PairIndex q)} :
    collisionSubfamilyPairSupport q T = S ↔
      (∀ p ∈ S, (collisionSubfamilyPairFiber (q := q) T p).Nonempty) ∧
        T ⊆ S.biUnion (fun p => collisionPairEvents (q := q) p) := by
  constructor
  · intro hsupport
    constructor
    · intro p hp
      exact (collisionSubfamilyPairFiber_nonempty_iff (q := q) (T := T) (p := p)).mpr
        (by simpa [hsupport] using hp)
    · intro e heT
      have hp : e.1 ∈ S := by
        rw [← hsupport]
        exact (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr
          ⟨e.2, heT⟩
      simp only [Finset.mem_biUnion]
      refine ⟨e.1, hp, ?_⟩
      rcases e with ⟨p, k⟩
      cases k <;> simp [collisionPairEvents]
  · rintro ⟨hnonempty, hsubset⟩
    ext p
    constructor
    · intro hp
      rcases (mem_collisionSubfamilyPairSupport_iff (T := T) (p := p)).mp hp with
        ⟨k, hkT⟩
      have hkS := hsubset hkT
      simp only [Finset.mem_biUnion] at hkS
      rcases hkS with ⟨p', hp'S, hkp'⟩
      have hp_eq : p = p' :=
        collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hkp'
      simpa [hp_eq] using hp'S
    · intro hp
      rcases hnonempty p hp with ⟨e, he⟩
      have hef := (mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
        (p := p) (e := e)).mp he
      rcases e with ⟨p', k⟩
      simp only at hef
      have hkT : (p, k) ∈ T := by
        simpa [hef.2] using hef.1
      exact (mem_collisionSubfamilyPairSupport_iff (T := T) (p := p)).mpr
        ⟨k, hkT⟩

/-- Fibers outside the pair support are empty. -/
theorem collisionSubfamilyPairFiber_eq_empty_of_not_mem_support
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    (hp : p ∉ collisionSubfamilyPairSupport q T) :
    collisionSubfamilyPairFiber (q := q) T p = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  intro hnonempty
  exact hp ((collisionSubfamilyPairFiber_nonempty_iff (q := q) (T := T) (p := p)).mp
    hnonempty)

/-- Exact-support families have empty fibers outside the claimed support. -/
theorem collisionSubfamilyPairFiber_eq_empty_of_not_mem_of_pairSupport_eq
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (PairIndex q)}
    (hsupport : collisionSubfamilyPairSupport q T = S)
    {p : PairIndex q} (hp : p ∉ S) :
    collisionSubfamilyPairFiber (q := q) T p = ∅ := by
  apply collisionSubfamilyPairFiber_eq_empty_of_not_mem_support
  simpa [hsupport] using hp

/-- Any nonempty pair-local event choice is either a singleton or the full
hidden/shifted pair.  This is the version for arbitrary local choices, not just
the fibers of an existing global subfamily. -/
theorem pairLocalChoice_card_eq_one_or_two_of_nonempty_subset_pairEvents
    {q : Nat} {p : PairIndex q} {U : Finset (CollisionEvent q)}
    (hsub : U ⊆ collisionPairEvents (q := q) p) (hne : U.Nonempty) :
    U.card = 1 ∨ U.card = 2 := by
  have hpos : 0 < U.card := Finset.card_pos.mpr hne
  have hle : U.card ≤ 2 := by
    calc
      U.card ≤ (collisionPairEvents (q := q) p).card := Finset.card_le_card hsub
      _ = 2 := by simp [collisionPairEvents, collisionKind_hidden_ne_shifted]
  omega

/-- A two-element pair-local event choice is the full hidden/shifted pair-local
event set. -/
theorem pairLocalChoice_eq_pairEvents_of_card_eq_two
    {q : Nat} {p : PairIndex q} {U : Finset (CollisionEvent q)}
    (hsub : U ⊆ collisionPairEvents (q := q) p) (hcard : U.card = 2) :
    U = collisionPairEvents (q := q) p := by
  apply Finset.eq_of_subset_of_card_le
  · exact hsub
  · rw [hcard]
    simp [collisionPairEvents, collisionKind_hidden_ne_shifted]

/-- A one-element pair-local event choice is a singleton event over the indexed
query pair. -/
theorem exists_pairLocalChoice_eq_singleton_of_card_eq_one
    {q : Nat} {p : PairIndex q} {U : Finset (CollisionEvent q)}
    (hsub : U ⊆ collisionPairEvents (q := q) p) (hcard : U.card = 1) :
    ∃ k : CollisionKind, U = {(p, k)} := by
  rcases Finset.card_eq_one.mp hcard with ⟨e, heq⟩
  have he_mem : e ∈ U := by
    rw [heq]
    simp
  have hep := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub he_mem)
  rcases e with ⟨p', k⟩
  simp only at hep
  exact ⟨k, by simpa [hep] using heq⟩

/-- A choice function appearing in the pair-local `Finset.pi` product expansion
selects a subfamily of the corresponding pair-local event set. -/
theorem pairChoice_mem_pi_subset_pairEvents
    {q : Nat} {S : Finset (PairIndex q)}
    {F : (p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)}
    (hF : F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (p : S) :
    F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
  have hp := Finset.mem_pi.mp hF p.1 p.2
  simp only [Finset.mem_filter, Finset.mem_powerset] at hp
  exact hp.1

/-- A choice function appearing in the pair-local `Finset.pi` product expansion
selects a nonempty local event subfamily over every touched query pair. -/
theorem pairChoice_mem_pi_nonempty
    {q : Nat} {S : Finset (PairIndex q)}
    {F : (p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)}
    (hF : F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (p : S) :
    (F p.1 p.2).Nonempty := by
  have hp := Finset.mem_pi.mp hF p.1 p.2
  simp only [Finset.mem_filter, Finset.mem_powerset] at hp
  exact hp.2

/-- Each pair-local choice in a `Finset.pi` product summand is either a singleton
or the full hidden/shifted pair. -/
theorem pairChoice_mem_pi_card_eq_one_or_two
    {q : Nat} {S : Finset (PairIndex q)}
    {F : (p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)}
    (hF : F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (p : S) :
    (F p.1 p.2).card = 1 ∨ (F p.1 p.2).card = 2 := by
  exact pairLocalChoice_card_eq_one_or_two_of_nonempty_subset_pairEvents
    (pairChoice_mem_pi_subset_pairEvents hF p) (pairChoice_mem_pi_nonempty hF p)

/-- A two-event local choice in a `Finset.pi` product summand is the full
hidden/shifted pair-local event set. -/
theorem pairChoice_mem_pi_eq_pairEvents_of_card_eq_two
    {q : Nat} {S : Finset (PairIndex q)}
    {F : (p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)}
    (hF : F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    {p : S} (hcard : (F p.1 p.2).card = 2) :
    F p.1 p.2 = collisionPairEvents (q := q) p.1 := by
  exact pairLocalChoice_eq_pairEvents_of_card_eq_two
    (pairChoice_mem_pi_subset_pairEvents hF p) hcard

/-- A one-event local choice in a `Finset.pi` product summand is a singleton
collision event over the indexed query pair. -/
theorem exists_pairChoice_mem_pi_eq_singleton_of_card_eq_one
    {q : Nat} {S : Finset (PairIndex q)}
    {F : (p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)}
    (hF : F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    {p : S} (hcard : (F p.1 p.2).card = 1) :
    ∃ k : CollisionKind, F p.1 p.2 = {(p.1, k)} := by
  exact exists_pairLocalChoice_eq_singleton_of_card_eq_one
    (pairChoice_mem_pi_subset_pairEvents hF p) hcard

/-- Reassemble a collision-event subfamily from one chosen pair-local subfamily
over each query pair in a support set. -/
def collisionSubfamilyPairChoiceUnion
    {q : Nat} {S : Finset (PairIndex q)}
    (F : ∀ _p : S, Finset (CollisionEvent q)) : Finset (CollisionEvent q) :=
  S.attach.biUnion F

/-- If every local choice over `p ∈ S` is nonempty and contained in the pair-local
event set for `p`, then the reassembled subfamily has pair support exactly `S`.
This is the forward half of the support-size-two product bijection. -/
theorem collisionSubfamilyPairSupport_pairChoiceUnion_eq
    {q : Nat} {S : Finset (PairIndex q)}
    (F : ∀ _p : S, Finset (CollisionEvent q))
    (hsub : ∀ p : S, F p ⊆ collisionPairEvents (q := q) p.1)
    (hne : ∀ p : S, (F p).Nonempty) :
    collisionSubfamilyPairSupport q (collisionSubfamilyPairChoiceUnion F) = S := by
  ext p
  constructor
  · intro hp
    rcases (mem_collisionSubfamilyPairSupport_iff
      (T := collisionSubfamilyPairChoiceUnion F) (p := p)).mp hp with ⟨k, hk⟩
    unfold collisionSubfamilyPairChoiceUnion at hk
    simp only [Finset.mem_biUnion, Finset.mem_attach] at hk
    rcases hk with ⟨pS, _h, hkF⟩
    have hmem := hsub pS hkF
    have hp_eq := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hmem
    change (p, k).1 ∈ S
    rw [hp_eq]
    exact pS.2
  · intro hp
    let pS : S := ⟨p, hp⟩
    rcases hne pS with ⟨e, heF⟩
    have hmem := hsub pS heF
    have hep := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hmem
    rcases e with ⟨p', k⟩
    simp only at hep
    subst p'
    exact (mem_collisionSubfamilyPairSupport_iff
      (T := collisionSubfamilyPairChoiceUnion F) (p := p)).mpr ⟨k, by
        unfold collisionSubfamilyPairChoiceUnion
        exact Finset.mem_biUnion.mpr ⟨pS, by simp, heF⟩⟩

/-- Reassembling the actual nonempty pair fibers over an exact support recovers
the original collision-event subfamily.  This is the inverse half of the
support-size-two product bijection. -/
theorem collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
    {q : Nat} {T : Finset (CollisionEvent q)} {S : Finset (PairIndex q)}
    (hsupport : collisionSubfamilyPairSupport q T = S) :
    collisionSubfamilyPairChoiceUnion
      (S := S) (fun p : S => collisionSubfamilyPairFiber (q := q) T p.1) = T := by
  subst S
  unfold collisionSubfamilyPairChoiceUnion
  ext e
  constructor
  · intro he
    simp only [Finset.mem_biUnion, Finset.mem_attach] at he ⊢
    rcases he with ⟨p, _hp, hef⟩
    exact ((mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
      (p := p.1) (e := e)).mp hef).1
  · intro he
    simp only [Finset.mem_biUnion, Finset.mem_attach] at he ⊢
    refine ⟨⟨e.1, ?_⟩, trivial, ?_⟩
    · exact (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr
        ⟨e.2, he⟩
    · exact (mem_collisionSubfamilyPairFiber_iff (q := q) (T := T)
        (p := e.1) (e := e)).mpr ⟨he, rfl⟩

/-- The pair-local fiber of a reassembled choice union is the chosen local
subfamily.  This is the fiber-level inverse used to turn exact-support
subfamilies into independent pair-local choices. -/
theorem collisionSubfamilyPairFiber_pairChoiceUnion_eq
    {q : Nat} {S : Finset (PairIndex q)}
    (F : ∀ _p : S, Finset (CollisionEvent q))
    (hsub : ∀ p : S, F p ⊆ collisionPairEvents (q := q) p.1)
    (p : S) :
    collisionSubfamilyPairFiber (q := q) (collisionSubfamilyPairChoiceUnion F) p.1 = F p := by
  ext e
  constructor
  · intro he
    have he' := (mem_collisionSubfamilyPairFiber_iff (q := q)
      (T := collisionSubfamilyPairChoiceUnion F) (p := p.1) (e := e)).mp he
    unfold collisionSubfamilyPairChoiceUnion at he'
    simp only [Finset.mem_biUnion, Finset.mem_attach] at he'
    rcases he'.1 with ⟨r, _hr, heF⟩
    have her := hsub r heF
    have her_pair := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) her
    have hrp : r = p := by
      apply Subtype.ext
      exact her_pair.symm.trans he'.2
    simpa [hrp] using heF
  · intro heF
    exact (mem_collisionSubfamilyPairFiber_iff (q := q)
      (T := collisionSubfamilyPairChoiceUnion F) (p := p.1) (e := e)).mpr ⟨by
        unfold collisionSubfamilyPairChoiceUnion
        exact Finset.mem_biUnion.mpr ⟨p, by simp, heF⟩, by
        exact collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub p heF)
      ⟩

/-- The cardinality of a reassembled pair-choice union is the sum of the
cardinalities of its pair-local choices.  Pair-local choices over distinct
query pairs are disjoint because membership in `collisionPairEvents p` fixes the
underlying query pair. -/
theorem collisionSubfamilyPairChoiceUnion_card_eq_sum
    {q : Nat} {S : Finset (PairIndex q)}
    (F : ∀ _p : S, Finset (CollisionEvent q))
    (hsub : ∀ p : S, F p ⊆ collisionPairEvents (q := q) p.1) :
    (collisionSubfamilyPairChoiceUnion F).card = ∑ p : S, (F p).card := by
  unfold collisionSubfamilyPairChoiceUnion
  have hpd : (↑S.attach : Set S).PairwiseDisjoint F := by
    rw [Finset.pairwiseDisjoint_iff]
    intro p _hp r _hr hnonempty
    rcases hnonempty with ⟨e, he⟩
    have hep : e ∈ F p := (Finset.mem_inter.mp he).1
    have her : e ∈ F r := (Finset.mem_inter.mp he).2
    have hpairp := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub p hep)
    have hpairr := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub r her)
    apply Subtype.ext
    exact hpairp.symm.trans hpairr
  have hcard := Finset.card_biUnion
    (s := S.attach) (t := F) hpd
  simpa using hcard

/-- The alternating sign of a reassembled pair-choice union factors into the
product of the alternating signs of the pair-local choices.  This isolates the
pure cardinality/sign part of the support-cardinality-two product expansion;
the remaining labelled fact is cycle-consistency factorization. -/
theorem collisionSubfamilyPairChoiceUnion_neg_one_pow_card_eq_prod
    {q : Nat} {S : Finset (PairIndex q)}
    (F : ∀ _p : S, Finset (CollisionEvent q))
    (hsub : ∀ p : S, F p ⊆ collisionPairEvents (q := q) p.1) :
    (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion F).card =
      ∏ p : S, (-1 : ℤ) ^ (F p).card := by
  rw [collisionSubfamilyPairChoiceUnion_card_eq_sum F hsub]
  exact (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset S)
    (fun p => (F p).card) (-1 : ℤ)).symm

/-- If cycle-consistency also factors over a reassembled pair-choice union, then
the full signed summand factors into the product of pair-local signed summands.
This theorem makes the remaining support-cardinality-two obligation precise:
after the cardinality/sign theorem above, only cycle-consistency factorization
has to be proved. -/
theorem collisionSubfamilyPairChoiceUnion_signedTerm_eq_prod_of_cycleConsistent_iff
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S : Finset (PairIndex q)}
    (y : Fin q → G)
    (F : ∀ _p : S, Finset (CollisionEvent q))
    (hsub : ∀ p : S, F p ⊆ collisionPairEvents (q := q) p.1)
    (hcycle : collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion F) ↔
      ∀ p : S, collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p)) :
    (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion F) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion F).card
    else
      0) =
      ∏ p : S,
        (if collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p) then
          (-1 : ℤ) ^ (F p).card
        else
          0) := by
  by_cases hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion F)
  · have hlocal : ∀ p : S, collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (F p) :=
      hcycle.mp hglobal
    simpa [hglobal, hlocal,
      collisionSubfamilyPairChoiceUnion_card_eq_sum F hsub]
      using (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset S)
        (fun p => (F p).card) (-1 : ℤ)).symm
  · have hnotlocal : ¬ ∀ p : S, collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (F p) := by
      intro hlocal
      exact hglobal (hcycle.mpr hlocal)
    rcases not_forall.mp hnotlocal with ⟨p, hp⟩
    simp [hglobal]
    exact ((Finset.prod_eq_zero_iff (s := (Finset.univ : Finset S))
      (f := fun p : S =>
        (if collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p) then
          (-1 : ℤ) ^ (F p).card
        else
          0))).mpr ⟨p, by simp [hp]⟩).symm

/-- Labelled steps are monotone under enlarging the collision-event subfamily. -/
theorem collisionSubfamilyStepLabel_mono
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S T : Finset (CollisionEvent q)} {y : Fin q → G}
    (hST : S ⊆ T) {i j : Fin q} {label : G}
    (hstep : collisionSubfamilyStepLabel (G := G) (q := q) y S i j label) :
    collisionSubfamilyStepLabel (G := G) (q := q) y T i j label := by
  rcases hstep with ⟨e, heS, hends⟩
  exact ⟨e, hST heS, hends⟩

/-- Labelled reachability is monotone under enlarging the collision-event
subfamily. -/
theorem collisionSubfamilyLabelReach_mono
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S T : Finset (CollisionEvent q)} {y : Fin q → G}
    (hST : S ⊆ T) {i j : Fin q} {label : G}
    (hreach : collisionSubfamilyLabelReach (G := G) (q := q) y S i j label) :
    collisionSubfamilyLabelReach (G := G) (q := q) y T i j label := by
  induction hreach with
  | refl => exact collisionSubfamilyLabelReach.refl (y := y) (T := T) _
  | tail _hprev hstep ih =>
      exact collisionSubfamilyLabelReach.tail ih
        (collisionSubfamilyStepLabel_mono (G := G) (q := q) hST hstep)

/-- Cycle consistency is downward closed under taking a collision-event
subfamily. -/
theorem collisionSubfamilyCycleConsistent_mono
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S T : Finset (CollisionEvent q)} {y : Fin q → G}
    (hST : S ⊆ T)
    (hT : collisionSubfamilyCycleConsistent (G := G) (q := q) y T) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y S := by
  intro i label hreach
  exact hT i label (collisionSubfamilyLabelReach_mono (G := G) (q := q) hST hreach)

/-- If a reassembled pair-choice union is cycle-consistent, then every local
pair choice is cycle-consistent.  This proves the easy direction of the
support-size-two labelled factorization; the hard direction is constructing
global consistency from the two local predicates. -/
theorem collisionSubfamilyPairChoiceUnion_local_cycleConsistent_of_global
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S : Finset (PairIndex q)} {y : Fin q → G}
    (F : ∀ _p : S, Finset (CollisionEvent q)) (p : S)
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion F)) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p) := by
  apply collisionSubfamilyCycleConsistent_mono (G := G) (q := q) ?_ hglobal
  intro e he
  unfold collisionSubfamilyPairChoiceUnion
  exact Finset.mem_biUnion.mpr ⟨p, by simp, he⟩

/-- A cycle-consistent pair-local choice has one visible label value: all
chosen hidden/shifted events over the same query pair have equal labels. -/
theorem pairLocalChoice_labels_eq_of_cycleConsistent
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {p : PairIndex q} {U : Finset (CollisionEvent q)}
    {y : Fin q → G}
    (hsub : U ⊆ collisionPairEvents (q := q) p)
    (hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y U)
    {e e' : CollisionEvent q} (he : e ∈ U) (he' : e' ∈ U) :
    collisionEventLabel y e = collisionEventLabel y e' := by
  have htwo : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      ({e, e'} : Finset (CollisionEvent q)) := by
    apply collisionSubfamilyCycleConsistent_mono (G := G) (q := q) ?_ hcyc
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact he
    · exact he'
  have hep : e.1 = p :=
    collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub he)
  have hep' : e'.1 = p :=
    collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub he')
  have hl : collisionEventLeft e' = collisionEventLeft e := by
    rcases e with ⟨pe, ke⟩
    rcases e' with ⟨pe', ke'⟩
    simp only at hep hep'
    subst pe
    subst pe'
    rfl
  have hr : collisionEventRight e' = collisionEventRight e := by
    rcases e with ⟨pe, ke⟩
    rcases e' with ⟨pe', ke'⟩
    simp only at hep hep'
    subst pe
    subst pe'
    rfl
  exact (collisionSubfamilyCycleConsistent_pair_sameEndpoints_iff_label_eq
    (G := G) (q := q) y hl hr).mp htwo

/-- If two collision events touch different query pairs, then the endpoint pair
of the second event is not connected inside the singleton support graph of the
first. -/
theorem collisionEvent_endpoints_not_connected_singleton_of_pairIndex_ne
    {q : Nat} {e₁ e₂ : CollisionEvent q} (hne : e₁.1 ≠ e₂.1) :
    ¬ collisionSubfamilyConnected (q := q) ({e₁} : Finset (CollisionEvent q))
        (collisionEventRight e₂) (collisionEventLeft e₂) := by
  intro hconn
  have hconn' : collisionSubfamilyConnected (q := q) ({e₁} : Finset (CollisionEvent q))
      (collisionEventLeft e₂) (collisionEventRight e₂) :=
    collisionSubfamilyConnected_symm (q := q) ({e₁} : Finset (CollisionEvent q)) hconn
  have hrep :=
    (collisionSubfamilySingletonConnected_iff_rep_eq (q := q) e₁).mp hconn'
  have hends := collisionEvent_endpoints_eq_of_singletonRep_eq (q := q) e₁ e₂ hrep
  have hp := collisionEvent_pairIndex_eq_of_endpoints_eq (q := q) hends.1 hends.2
  exact hne hp.symm

/-- Two singleton constraints over distinct query pairs are always semantically
consistent.  Starting from a solution of the first equation, shift the whole
connected component containing the left endpoint of the second equation. -/
theorem collisionSubfamilyConsistent_two_singletons_of_pairIndex_ne
    {G : Type*} [AddCommGroup G]
    {q : Nat} (y : Fin q → G) {e₁ e₂ : CollisionEvent q}
    (hne : e₁.1 ≠ e₂.1) :
    collisionSubfamilyConsistent (G := G) (q := q) y
      ({e₁, e₂} : Finset (CollisionEvent q)) := by
  classical
  rcases collisionSubfamilyConsistent_singleton (G := G) (q := q) y e₁ with ⟨a, ha⟩
  let l₂ := collisionEventLeft e₂
  let r₂ := collisionEventRight e₂
  let delta : G := collisionEventLabel y e₂ - (a l₂ - a r₂)
  let z : Fin q → G := fun i =>
    if collisionSubfamilyConnected (q := q) ({e₁} : Finset (CollisionEvent q)) i l₂ then
      delta
    else
      0
  have hz : collisionSubfamilyComponentConstant (q := q)
      ({e₁} : Finset (CollisionEvent q)) z := by
    intro i j hij
    dsimp [z]
    by_cases hi : collisionSubfamilyConnected (q := q)
        ({e₁} : Finset (CollisionEvent q)) i l₂
    · have hj : collisionSubfamilyConnected (q := q)
          ({e₁} : Finset (CollisionEvent q)) j l₂ := by
        exact Relation.ReflTransGen.trans
          (collisionSubfamilyConnected_symm (q := q)
            ({e₁} : Finset (CollisionEvent q)) hij) hi
      simp [hi, hj]
    · have hj : ¬ collisionSubfamilyConnected (q := q)
          ({e₁} : Finset (CollisionEvent q)) j l₂ := by
        intro hj
        exact hi (Relation.ReflTransGen.trans hij hj)
      simp [hi, hj]
  have hbase' : ∀ e ∈ ({e₁} : Finset (CollisionEvent q)),
      collisionEventEquation (G := G) (q := q) y e (fun i => a i + z i) :=
    collisionSubfamilyEquations_add_componentConstant (G := G) (q := q)
      (y := y) (T := ({e₁} : Finset (CollisionEvent q))) (base := a) (z := z) ha hz
  refine ⟨fun i => a i + z i, ?_⟩
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with heq | heq
  · subst e
    exact hbase' e₁ (by simp)
  · subst e
    have hlconn : collisionSubfamilyConnected (q := q)
        ({e₁} : Finset (CollisionEvent q)) l₂ l₂ :=
      collisionSubfamilyConnected_refl (q := q) ({e₁} : Finset (CollisionEvent q)) l₂
    have hrnot : ¬ collisionSubfamilyConnected (q := q)
        ({e₁} : Finset (CollisionEvent q)) r₂ l₂ :=
      collisionEvent_endpoints_not_connected_singleton_of_pairIndex_ne
        (q := q) (e₁ := e₁) (e₂ := e₂) hne
    unfold collisionEventEquation
    dsimp [l₂, r₂, z, delta] at *
    rw [if_pos hlconn, if_neg hrnot]
    abel

/-- For a two-query-pair support, cycle-consistency of a reassembled pair-choice
union is exactly componentwise cycle-consistency of its two pair-local choices.
This is the labelled half of the support-cardinality-two product expansion. -/
theorem collisionSubfamilyPairChoiceUnion_cycleConsistent_iff_of_card_eq_two
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S : Finset (PairIndex q)} {y : Fin q → G}
    (F : ∀ _p : S, Finset (CollisionEvent q))
    (hsub : ∀ p : S, F p ⊆ collisionPairEvents (q := q) p.1)
    (hne : ∀ p : S, (F p).Nonempty)
    (hS : S.card = 2) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion F) ↔
    ∀ p : S, collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p) := by
  constructor
  · intro hglobal p
    exact collisionSubfamilyPairChoiceUnion_local_cycleConsistent_of_global
      (G := G) (q := q) (F := F) (p := p) hglobal
  · intro hlocal
    classical
    rcases Finset.card_eq_two.mp hS with ⟨p₀, p₁, hp_ne, hS_eq⟩
    let p₀S : S := ⟨p₀, by simp [hS_eq]⟩
    let p₁S : S := ⟨p₁, by simp [hS_eq]⟩
    rcases hne p₀S with ⟨e₀, he₀⟩
    rcases hne p₁S with ⟨e₁, he₁⟩
    have he₀pair : e₀.1 = p₀ :=
      collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub p₀S he₀)
    have he₁pair : e₁.1 = p₁ :=
      collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub p₁S he₁)
    have he_ne : e₀.1 ≠ e₁.1 := by
      intro h
      exact hp_ne (he₀pair.symm.trans (h.trans he₁pair))
    rcases collisionSubfamilyConsistent_two_singletons_of_pairIndex_ne
        (G := G) (q := q) y (e₁ := e₀) (e₂ := e₁) he_ne with ⟨a, ha⟩
    refine (collisionSubfamilyConsistent_iff_cycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion F)).mp ?_
    refine ⟨a, ?_⟩
    intro e he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach] at he
    rcases he with ⟨pS, _hpS, hepS⟩
    have hp_cases : pS.1 = p₀ ∨ pS.1 = p₁ := by
      have hp_mem : pS.1 ∈ ({p₀, p₁} : Finset (PairIndex q)) := by
        simpa [hS_eq] using pS.2
      simpa using hp_mem
    rcases hp_cases with hp | hp
    · have hpS_eq : pS = p₀S := Subtype.ext hp
      subst pS
      have hlabel : collisionEventLabel y e = collisionEventLabel y e₀ :=
        pairLocalChoice_labels_eq_of_cycleConsistent (G := G) (q := q)
          (p := p₀) (U := F p₀S) (y := y) (hsub p₀S) (hlocal p₀S) hepS he₀
      have he_pair : e.1 = p₀ :=
        collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub p₀S hepS)
      have hl : collisionEventLeft e = collisionEventLeft e₀ := by
        rcases e with ⟨pe, ke⟩
        rcases e₀ with ⟨pe₀, ke₀⟩
        simp only at he_pair he₀pair
        subst pe
        subst pe₀
        rfl
      have hr : collisionEventRight e = collisionEventRight e₀ := by
        rcases e with ⟨pe, ke⟩
        rcases e₀ with ⟨pe₀, ke₀⟩
        simp only at he_pair he₀pair
        subst pe
        subst pe₀
        rfl
      have hbase := ha e₀ (by simp)
      unfold collisionEventEquation at hbase ⊢
      simpa [hl, hr, hlabel] using hbase
    · have hpS_eq : pS = p₁S := Subtype.ext hp
      subst pS
      have hlabel : collisionEventLabel y e = collisionEventLabel y e₁ :=
        pairLocalChoice_labels_eq_of_cycleConsistent (G := G) (q := q)
          (p := p₁) (U := F p₁S) (y := y) (hsub p₁S) (hlocal p₁S) hepS he₁
      have he_pair : e.1 = p₁ :=
        collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub p₁S hepS)
      have hl : collisionEventLeft e = collisionEventLeft e₁ := by
        rcases e with ⟨pe, ke⟩
        rcases e₁ with ⟨pe₁, ke₁⟩
        simp only at he_pair he₁pair
        subst pe
        subst pe₁
        rfl
      have hr : collisionEventRight e = collisionEventRight e₁ := by
        rcases e with ⟨pe, ke⟩
        rcases e₁ with ⟨pe₁, ke₁⟩
        simp only at he_pair he₁pair
        subst pe
        subst pe₁
        rfl
      have hbase := ha e₁ (by simp)
      unfold collisionEventEquation at hbase ⊢
      simpa [hl, hr, hlabel] using hbase

/-- On a two-query-pair support, the signed summand of a reassembled
pair-choice union factors into the product of the two local signed summands. -/
theorem collisionSubfamilyPairChoiceUnion_signedTerm_eq_prod_of_card_eq_two
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S : Finset (PairIndex q)} {y : Fin q → G}
    (F : ∀ _p : S, Finset (CollisionEvent q))
    (hsub : ∀ p : S, F p ⊆ collisionPairEvents (q := q) p.1)
    (hne : ∀ p : S, (F p).Nonempty)
    (hS : S.card = 2) :
    (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion F) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion F).card
    else
      0) =
      ∏ p : S,
        (if collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p) then
          (-1 : ℤ) ^ (F p).card
        else
          0) := by
  apply collisionSubfamilyPairChoiceUnion_signedTerm_eq_prod_of_cycleConsistent_iff
  · exact hsub
  · exact collisionSubfamilyPairChoiceUnion_cycleConsistent_iff_of_card_eq_two
      (G := G) (q := q) (y := y) F hsub hne hS

/-- Cycle consistency factorizes over an exact query-pair support when every
pair-local choice is globally consistent exactly when all of its local fibers
are consistent. -/
def PairSupportCycleConsistentFactors
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) (S : Finset (PairIndex q)) : Prop :=
  ∀ F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)),
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)) ↔
    ∀ p : S, collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p.1 p.2)

/-- Support adjacency depends only on query-pair support, not on the
hidden/shifted event kind selected over each query pair. -/
theorem collisionSubfamilyAdjacent_iff_of_pairSupport_eq
    {q : Nat} {S T : Finset (CollisionEvent q)}
    (hsupport : collisionSubfamilyPairSupport q S = collisionSubfamilyPairSupport q T)
    {i j : Fin q} :
    collisionSubfamilyAdjacent (q := q) S i j ↔
      collisionSubfamilyAdjacent (q := q) T i j := by
  constructor
  · rintro ⟨e, heS, hends⟩
    have hpT : e.1 ∈ collisionSubfamilyPairSupport q T := by
      rw [← hsupport]
      exact (mem_collisionSubfamilyPairSupport_iff (T := S) (p := e.1)).mpr
        ⟨e.2, heS⟩
    rcases (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mp hpT with
      ⟨k, hkT⟩
    refine ⟨(e.1, k), hkT, ?_⟩
    rcases e with ⟨p, k'⟩
    simpa [collisionEventLeft, collisionEventRight] using hends
  · rintro ⟨e, heT, hends⟩
    have hpS : e.1 ∈ collisionSubfamilyPairSupport q S := by
      rw [hsupport]
      exact (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr
        ⟨e.2, heT⟩
    rcases (mem_collisionSubfamilyPairSupport_iff (T := S) (p := e.1)).mp hpS with
      ⟨k, hkS⟩
    refine ⟨(e.1, k), hkS, ?_⟩
    rcases e with ⟨p, k'⟩
    simpa [collisionEventLeft, collisionEventRight] using hends

/-- Support connectivity depends only on query-pair support, not on the
hidden/shifted event kind selected over each query pair. -/
theorem collisionSubfamilyConnected_iff_of_pairSupport_eq
    {q : Nat} {S T : Finset (CollisionEvent q)}
    (hsupport : collisionSubfamilyPairSupport q S = collisionSubfamilyPairSupport q T)
    {i j : Fin q} :
    collisionSubfamilyConnected (q := q) S i j ↔
      collisionSubfamilyConnected (q := q) T i j := by
  constructor
  · intro hij
    induction hij with
    | refl => exact Relation.ReflTransGen.refl
    | tail _hprev hadj ih =>
        exact Relation.ReflTransGen.tail ih
          ((collisionSubfamilyAdjacent_iff_of_pairSupport_eq
            (q := q) hsupport).mp hadj)
  · intro hij
    induction hij with
    | refl => exact Relation.ReflTransGen.refl
    | tail _hprev hadj ih =>
        exact Relation.ReflTransGen.tail ih
          ((collisionSubfamilyAdjacent_iff_of_pairSupport_eq
            (q := q) hsupport).mpr hadj)

/-- Equal query-pair support gives equivalent support-graph component quotients. -/
def collisionSubfamilyComponentEquivOfPairSupportEq
    {q : Nat} {S T : Finset (CollisionEvent q)}
    (hsupport : collisionSubfamilyPairSupport q S = collisionSubfamilyPairSupport q T) :
    collisionSubfamilyComponent (q := q) S ≃
      collisionSubfamilyComponent (q := q) T where
  toFun c :=
    Quotient.liftOn c
      (fun i => (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i :
        collisionSubfamilyComponent (q := q) T))
      (by
        intro i j hij
        apply Quotient.sound
        exact (collisionSubfamilyConnected_iff_of_pairSupport_eq (q := q) hsupport).mp
          (by simpa [collisionSubfamilyConnectedSetoid] using hij))
  invFun c :=
    Quotient.liftOn c
      (fun i => (Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) S) i :
        collisionSubfamilyComponent (q := q) S))
      (by
        intro i j hij
        apply Quotient.sound
        exact (collisionSubfamilyConnected_iff_of_pairSupport_eq (q := q) hsupport).mpr
          (by simpa [collisionSubfamilyConnectedSetoid] using hij))
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h i => rfl
  right_inv c := by
    induction c using Quotient.inductionOn with
    | h i => rfl

/-- Component count depends only on query-pair support. -/
theorem collisionSubfamilyComponentCount_eq_of_pairSupport_eq
    {q : Nat} {S T : Finset (CollisionEvent q)}
    (hsupport : collisionSubfamilyPairSupport q S = collisionSubfamilyPairSupport q T) :
    collisionSubfamilyComponentCount (q := q) S =
      collisionSubfamilyComponentCount (q := q) T := by
  unfold collisionSubfamilyComponentCount
  exact Fintype.card_congr
    (collisionSubfamilyComponentEquivOfPairSupportEq (q := q) hsupport)

/-- Graphic rank depends only on query-pair support. -/
theorem collisionSubfamilyGraphicRank_eq_of_pairSupport_eq
    {q : Nat} {S T : Finset (CollisionEvent q)}
    (hsupport : collisionSubfamilyPairSupport q S = collisionSubfamilyPairSupport q T) :
    collisionSubfamilyGraphicRank (q := q) S =
      collisionSubfamilyGraphicRank (q := q) T := by
  unfold collisionSubfamilyGraphicRank
  rw [collisionSubfamilyComponentCount_eq_of_pairSupport_eq (q := q) hsupport]

/-- Canonical hidden-event representative of a query-pair support set.  It has
one hidden collision event over each touched query pair. -/
def collisionPairSupportHiddenRepresentative
    {q : Nat} (S : Finset (PairIndex q)) : Finset (CollisionEvent q) :=
  S.image (fun p => (p, CollisionKind.hidden))

/-- Graphic rank of an exact query-pair support, computed on the canonical
hidden-event representative. -/
def pairSupportGraphicRank (q : Nat) (S : Finset (PairIndex q)) : Nat :=
  collisionSubfamilyGraphicRank (q := q)
    (collisionPairSupportHiddenRepresentative (q := q) S)

/-- The canonical hidden-event representative has exactly the claimed query-pair
support. -/
theorem collisionSubfamilyPairSupport_hiddenRepresentative
    {q : Nat} (S : Finset (PairIndex q)) :
    collisionSubfamilyPairSupport q
        (collisionPairSupportHiddenRepresentative (q := q) S) = S := by
  ext p
  constructor
  · intro hp
    rcases (mem_collisionSubfamilyPairSupport_iff
      (T := collisionPairSupportHiddenRepresentative (q := q) S) (p := p)).mp hp with
      ⟨k, hk⟩
    simp only [collisionPairSupportHiddenRepresentative, Finset.mem_image] at hk
    rcases hk with ⟨p', hp'S, hp'⟩
    have hp_eq : p' = p := (Prod.ext_iff.mp hp').1
    simpa [hp_eq] using hp'S
  · intro hp
    exact (mem_collisionSubfamilyPairSupport_iff
      (T := collisionPairSupportHiddenRepresentative (q := q) S) (p := p)).mpr
      ⟨CollisionKind.hidden, by
        simp [collisionPairSupportHiddenRepresentative, hp]⟩

/-- The graphic rank of a subfamily is the graphic rank of its exact query-pair
support. -/
theorem collisionSubfamilyGraphicRank_eq_pairSupportGraphicRank
    {q : Nat} (T : Finset (CollisionEvent q)) :
    collisionSubfamilyGraphicRank (q := q) T =
      pairSupportGraphicRank q (collisionSubfamilyPairSupport q T) := by
  unfold pairSupportGraphicRank
  rw [collisionSubfamilyGraphicRank_eq_of_pairSupport_eq
    (q := q)
    (S := T)
    (T := collisionPairSupportHiddenRepresentative
      (q := q) (collisionSubfamilyPairSupport q T))]
  exact (collisionSubfamilyPairSupport_hiddenRepresentative
    (q := q) (collisionSubfamilyPairSupport q T)).symm

/-- The canonical hidden-event representative has one event per query-pair
support element. -/
theorem collisionPairSupportHiddenRepresentative_card
    {q : Nat} (S : Finset (PairIndex q)) :
    (collisionPairSupportHiddenRepresentative (q := q) S).card = S.card := by
  unfold collisionPairSupportHiddenRepresentative
  rw [Finset.card_image_iff]
  intro p hp r hr hpr
  exact Prod.ext_iff.mp hpr |>.1

/-- Visible collision constraints on a pair set are the same as component
constancy for the canonical hidden-event representative of that pair support. -/
theorem pairCollisionSet_subset_iff_componentConstant_hiddenRepresentative
    (G : Type*) [DecidableEq G] {q : Nat} (S : Finset (PairIndex q))
    (y : Fin q → G) :
    S ⊆ pairCollisionSet G y ↔
      collisionSubfamilyComponentConstant (q := q)
        (collisionPairSupportHiddenRepresentative (q := q) S) y := by
  constructor
  · intro hS i j hconn
    induction hconn with
    | refl => rfl
    | tail _hprev hstep ih =>
        exact ih.trans (by
          rcases hstep with ⟨e, heT, hends | hends⟩
          · rcases hends with ⟨hl, hr⟩
            rcases Finset.mem_image.mp heT with ⟨p, hpS, hpe⟩
            have hpColl : p ∈ pairCollisionSet G y := hS hpS
            unfold pairCollisionSet at hpColl
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpColl
            subst e
            rw [← hl, ← hr]
            simpa [collisionEventLeft, collisionEventRight] using hpColl.symm
          · rcases hends with ⟨hl, hr⟩
            rcases Finset.mem_image.mp heT with ⟨p, hpS, hpe⟩
            have hpColl : p ∈ pairCollisionSet G y := hS hpS
            unfold pairCollisionSet at hpColl
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpColl
            subst e
            rw [← hr, ← hl]
            simpa [collisionEventLeft, collisionEventRight] using hpColl)
  · intro hconst p hpS
    unfold pairCollisionSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have heT : (p, CollisionKind.hidden) ∈
        collisionPairSupportHiddenRepresentative (q := q) S := by
      simp [collisionPairSupportHiddenRepresentative, hpS]
    have hconn := collisionSubfamilyEvent_connected (q := q) (T :=
      collisionPairSupportHiddenRepresentative (q := q) S) heT
    have heq := hconst hconn
    simpa [collisionEventLeft, collisionEventRight] using heq.symm

/-- The visible two-pair collision fiber is the component-constant fiber for
the canonical hidden representative of that pair support. -/
theorem pairPairCollisionFiberCard_eq_componentConstant_card
    (G : Type*) [Fintype G] [DecidableEq G] {q : Nat}
    (S : Finset (PairIndex q)) :
    pairPairCollisionFiberCard G S =
      Fintype.card { y : Fin q → G //
        collisionSubfamilyComponentConstant (q := q)
          (collisionPairSupportHiddenRepresentative (q := q) S) y } := by
  classical
  unfold pairPairCollisionFiberCard
  rw [Fintype.card_subtype]
  congr 1
  ext y
  simpa using pairCollisionSet_subset_iff_componentConstant_hiddenRepresentative
    (G := G) (q := q) S y

/-- Canonical-representative form of the rank-versus-support-cardinality
inequality.  Since graphic rank only depends on query-pair support, this is the
only graph inequality that remains after removing hidden/shifted multiplicity. -/
def HiddenRepresentativeGraphicRankLeCard (q : Nat) : Prop :=
  ∀ S : Finset (PairIndex q),
    collisionSubfamilyGraphicRank (q := q)
        (collisionPairSupportHiddenRepresentative (q := q) S) ≤ S.card

/-- The specialized canonical graph endpoint actually needed for rank-two
automaticity: a canonical hidden representative with two support edges has
graphic rank at most two. -/
def HiddenRepresentativeGraphicRankLeTwoOnCardTwo (q : Nat) : Prop :=
  ∀ S : Finset (PairIndex q),
    S.card = 2 →
      collisionSubfamilyGraphicRank (q := q)
          (collisionPairSupportHiddenRepresentative (q := q) S) ≤ 2

/-- The general canonical edge-count bound implies the exact two-edge canonical
bound used by rank-two automaticity. -/
theorem HiddenRepresentativeGraphicRankLeTwoOnCardTwo.of_le_card
    {q : Nat} (hhidden : HiddenRepresentativeGraphicRankLeCard q) :
    HiddenRepresentativeGraphicRankLeTwoOnCardTwo q := by
  intro S hS
  rw [← hS]
  exact hhidden S

/-- Nonempty collision-event subfamilies have nonempty pair support. -/
theorem collisionSubfamilyPairSupport_nonempty_of_nonempty
    {q : Nat} {T : Finset (CollisionEvent q)} (hT : T.Nonempty) :
    (collisionSubfamilyPairSupport q T).Nonempty := by
  rcases hT with ⟨e, heT⟩
  exact ⟨e.1, (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr
    ⟨e.2, heT⟩⟩

/-- A graphic-rank-one subfamily has exactly one query pair in its pair
support.  This is the support-level analogue of the existing rank-one
classifier. -/
theorem collisionSubfamilyPairSupport_card_eq_one_of_graphicRank_eq_one
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 1) :
    (collisionSubfamilyPairSupport q T).card = 1 := by
  rcases (collisionSubfamilyGraphicRank_eq_one_iff_nonempty_subset_collisionPairEvents
    (q := q) T).mp hrank with ⟨hne, p, hsub⟩
  have hsupport : collisionSubfamilyPairSupport q T = {p} := by
    ext p'
    constructor
    · intro hp'
      rcases (mem_collisionSubfamilyPairSupport_iff (T := T) (p := p')).mp hp' with
        ⟨k, hkT⟩
      have hkp := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents
        (q := q) (hsub hkT)
      simpa [hkp]
    · intro hp'
      simp only [Finset.mem_singleton] at hp'
      subst p'
      rcases hne with ⟨e, heT⟩
      have hep := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents
        (q := q) (hsub heT)
      have heq : (p, e.2) = e := by
        rcases e with ⟨p0, k⟩
        simp only at hep
        subst p
        rfl
      exact (mem_collisionSubfamilyPairSupport_iff (T := T) (p := p)).mpr
        ⟨e.2, by simpa [heq] using heT⟩
  rw [hsupport]
  simp

/-- If the pair support is a singleton, the whole collision-event subfamily is
contained in that pair-local event set. -/
theorem collisionSubfamily_subset_collisionPairEvents_of_pairSupport_eq_singleton
    {q : Nat} {T : Finset (CollisionEvent q)} {p : PairIndex q}
    (hsupport : collisionSubfamilyPairSupport q T = {p}) :
    T ⊆ collisionPairEvents (q := q) p := by
  intro e heT
  have hp : e.1 ∈ collisionSubfamilyPairSupport q T :=
    (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr ⟨e.2, heT⟩
  rw [hsupport] at hp
  simp only [Finset.mem_singleton] at hp
  rcases e with ⟨p0, k⟩
  simp only at hp
  subst p0
  cases k <;> simp [collisionPairEvents]

/-- Graphic-rank-two subfamilies must touch at least two query pairs.  This is
the lower-bound half of the rank-two support classification. -/
theorem collisionSubfamilyPairSupport_two_le_of_graphicRank_eq_two
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 2) :
    2 ≤ (collisionSubfamilyPairSupport q T).card := by
  by_contra hlt
  have hcard_le_one : (collisionSubfamilyPairSupport q T).card ≤ 1 := by omega
  have hne : T.Nonempty := by
    by_contra hempty
    have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    subst T
    simp [collisionSubfamilyGraphicRank_empty] at hrank
  have hsupport_ne := collisionSubfamilyPairSupport_nonempty_of_nonempty (q := q) hne
  have hsupport_card_pos : 0 < (collisionSubfamilyPairSupport q T).card :=
    Finset.card_pos.mpr hsupport_ne
  have hsupport_card_one : (collisionSubfamilyPairSupport q T).card = 1 := by omega
  rcases Finset.card_eq_one.mp hsupport_card_one with ⟨p, hsupport⟩
  have hsubset :
      T ⊆ collisionPairEvents (q := q) p :=
    collisionSubfamily_subset_collisionPairEvents_of_pairSupport_eq_singleton
      (q := q) (T := T) hsupport
  have hrank_one :
      collisionSubfamilyGraphicRank (q := q) T = 1 :=
    collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_collisionPairEvents
      (q := q) p hne hsubset
  omega

/-- The set of query coordinates touched by two collision events. -/
def collisionEventPairEndpointSet
    {q : Nat} (e₁ e₂ : CollisionEvent q) : Finset (Fin q) :=
  {collisionEventLeft e₁, collisionEventRight e₁,
    collisionEventLeft e₂, collisionEventRight e₂}

/-- A two-event deletion set of size at most two that hits every selected
event.  If the two events have the same right endpoint, we delete that common
right endpoint and the second left endpoint; otherwise we delete the two right
endpoints. -/
def collisionEventPairDeletionSet
    {q : Nat} (e₁ e₂ : CollisionEvent q) : Finset (Fin q) :=
  if collisionEventRight e₂ = collisionEventRight e₁ then
    {collisionEventRight e₁, collisionEventLeft e₂}
  else
    {collisionEventRight e₁, collisionEventRight e₂}

/-- The explicit two-event deletion set has size at most two. -/
theorem collisionEventPairDeletionSet_card_le_two
    {q : Nat} (e₁ e₂ : CollisionEvent q) :
    (collisionEventPairDeletionSet e₁ e₂).card ≤ 2 := by
  unfold collisionEventPairDeletionSet
  by_cases hright : collisionEventRight e₂ = collisionEventRight e₁
  · rw [if_pos hright]
    by_cases h :
        collisionEventRight e₁ = collisionEventLeft e₂
    · simp [h]
    · simp [h]
  · rw [if_neg hright]
    by_cases h :
        collisionEventRight e₁ = collisionEventRight e₂
    · simp [h]
    · simp [h]

/-- The first selected event is hit by the two-event deletion set. -/
theorem collisionEventPairDeletionSet_right_one_mem
    {q : Nat} (e₁ e₂ : CollisionEvent q) :
    collisionEventRight e₁ ∈ collisionEventPairDeletionSet e₁ e₂ := by
  unfold collisionEventPairDeletionSet
  by_cases h : collisionEventRight e₂ = collisionEventRight e₁
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    simp

/-- The second selected event is hit by the two-event deletion set. -/
theorem collisionEventPairDeletionSet_endpoint_two_mem
    {q : Nat} (e₁ e₂ : CollisionEvent q) :
    collisionEventLeft e₂ ∈ collisionEventPairDeletionSet e₁ e₂ ∨
      collisionEventRight e₂ ∈ collisionEventPairDeletionSet e₁ e₂ := by
  unfold collisionEventPairDeletionSet
  by_cases h : collisionEventRight e₂ = collisionEventRight e₁
  · rw [if_pos h]
    left
    simp
  · rw [if_neg h]
    right
    simp

/-- Any edge-adjacency in a two-event support graph starts at one of the four
event endpoints. -/
theorem collisionSubfamilyAdjacent_pair_left_mem_endpointSet
    {q : Nat} {e₁ e₂ : CollisionEvent q} {i j : Fin q}
    (hadj : collisionSubfamilyAdjacent (q := q)
      ({e₁, e₂} : Finset (CollisionEvent q)) i j) :
    i ∈ collisionEventPairEndpointSet e₁ e₂ := by
  rcases hadj with ⟨e, he, hends | hends⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> rcases hends with ⟨rfl, rfl⟩ <;>
      simp [collisionEventPairEndpointSet]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> rcases hends with ⟨rfl, rfl⟩ <;>
      simp [collisionEventPairEndpointSet]

/-- A coordinate outside the four endpoints of a two-event support graph is an
isolated connected component. -/
theorem collisionSubfamilyConnected_pair_eq_of_left_not_mem_endpointSet
    {q : Nat} {e₁ e₂ : CollisionEvent q} {i j : Fin q}
    (hi : i ∉ collisionEventPairEndpointSet e₁ e₂)
    (hconn : collisionSubfamilyConnected (q := q)
      ({e₁, e₂} : Finset (CollisionEvent q)) i j) :
    i = j := by
  induction hconn with
  | refl => rfl
  | tail _hprev hadj ih =>
      subst ih
      exact False.elim
        (hi (collisionSubfamilyAdjacent_pair_left_mem_endpointSet
          (q := q) (e₁ := e₁) (e₂ := e₂) hadj))

/-- No two-event adjacency can have both endpoints outside the explicit
two-event deletion set.  This is the local vertex-cover fact used to turn the
two-event support graph into a component-count lower bound. -/
theorem collisionSubfamilyAdjacent_pair_not_both_not_mem_deletionSet
    {q : Nat} {e₁ e₂ : CollisionEvent q} {i j : Fin q}
    (hadj : collisionSubfamilyAdjacent (q := q)
      ({e₁, e₂} : Finset (CollisionEvent q)) i j)
    (hi : i ∉ collisionEventPairDeletionSet e₁ e₂)
    (hj : j ∉ collisionEventPairDeletionSet e₁ e₂) : False := by
  rcases hadj with ⟨e, he, hends | hends⟩
  · have he_cases : e = e₁ ∨ e = e₂ := by simpa using he
    rcases he_cases with heq | heq
    · rw [heq] at hends
      rcases hends with ⟨rfl, rfl⟩
      exact hj (collisionEventPairDeletionSet_right_one_mem e₁ e₂)
    · rw [heq] at hends
      rcases hends with ⟨rfl, rfl⟩
      rcases collisionEventPairDeletionSet_endpoint_two_mem e₁ e₂ with hleft | hright
      · exact hi hleft
      · exact hj hright
  · have he_cases : e = e₁ ∨ e = e₂ := by simpa using he
    rcases he_cases with heq | heq
    · rw [heq] at hends
      rcases hends with ⟨rfl, rfl⟩
      exact hi (collisionEventPairDeletionSet_right_one_mem e₁ e₂)
    · rw [heq] at hends
      rcases hends with ⟨rfl, rfl⟩
      rcases collisionEventPairDeletionSet_endpoint_two_mem e₁ e₂ with hleft | hright
      · exact hj hleft
      · exact hi hright

/-- Folded component representative for a two-event support graph.  First fold
the singleton graph `{e₁}`, then fold the singleton component containing the
right endpoint of `e₂` into the singleton component containing the left endpoint
of `e₂`. -/
def collisionSubfamilyPairComponentRep
    {q : Nat} (e₁ e₂ : CollisionEvent q) (i : Fin q) :
    {j : Fin q // j ≠ collisionEventRight e₁} :=
  let r := collisionSubfamilySingletonComponentRep (q := q) e₁ i
  if r = collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventRight e₂) then
    collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventLeft e₂)
  else
    r

/-- Folding the second event preserves equality of singleton representatives. -/
theorem collisionSubfamilyPairComponentRep_eq_of_singleton_rep_eq
    {q : Nat} (e₁ e₂ : CollisionEvent q) {i j : Fin q}
    (h : collisionSubfamilySingletonComponentRep (q := q) e₁ i =
      collisionSubfamilySingletonComponentRep (q := q) e₁ j) :
    collisionSubfamilyPairComponentRep e₁ e₂ i =
      collisionSubfamilyPairComponentRep e₁ e₂ j := by
  unfold collisionSubfamilyPairComponentRep
  rw [h]

/-- The folded two-event representative is constant across each adjacency in
the two-event support graph. -/
theorem collisionSubfamilyPairComponentRep_eq_of_adjacent
    {q : Nat} {e₁ e₂ : CollisionEvent q} {i j : Fin q}
    (hadj : collisionSubfamilyAdjacent (q := q)
      ({e₁, e₂} : Finset (CollisionEvent q)) i j) :
    collisionSubfamilyPairComponentRep e₁ e₂ i =
      collisionSubfamilyPairComponentRep e₁ e₂ j := by
  rcases hadj with ⟨e, he, hends | hends⟩
  · have he_cases : e = e₁ ∨ e = e₂ := by simpa using he
    rcases he_cases with heq | heq
    · rw [heq] at hends
      rcases hends with ⟨rfl, rfl⟩
      apply collisionSubfamilyPairComponentRep_eq_of_singleton_rep_eq
      exact collisionSubfamilySingletonConnected_rep_eq (q := q) e₁
        (Relation.ReflTransGen.single
          (r := collisionSubfamilyAdjacent (q := q) ({e₁} : Finset (CollisionEvent q)))
          ⟨e₁, by simp, Or.inl ⟨rfl, rfl⟩⟩)
    · rw [heq] at hends
      rcases hends with ⟨rfl, rfl⟩
      unfold collisionSubfamilyPairComponentRep
      by_cases h : collisionSubfamilySingletonComponentRep (q := q) e₁
          (collisionEventLeft e₂) =
        collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventRight e₂)
      · simp [h]
      · simp [h]
  · have he_cases : e = e₁ ∨ e = e₂ := by simpa using he
    rcases he_cases with heq | heq
    · rw [heq] at hends
      rcases hends with ⟨rfl, rfl⟩
      symm
      apply collisionSubfamilyPairComponentRep_eq_of_singleton_rep_eq
      exact collisionSubfamilySingletonConnected_rep_eq (q := q) e₁
        (Relation.ReflTransGen.single
          (r := collisionSubfamilyAdjacent (q := q) ({e₁} : Finset (CollisionEvent q)))
          ⟨e₁, by simp, Or.inl ⟨rfl, rfl⟩⟩)
    · rw [heq] at hends
      rcases hends with ⟨rfl, rfl⟩
      symm
      unfold collisionSubfamilyPairComponentRep
      by_cases h : collisionSubfamilySingletonComponentRep (q := q) e₁
          (collisionEventLeft e₂) =
        collisionSubfamilySingletonComponentRep (q := q) e₁ (collisionEventRight e₂)
      · simp [h]
      · simp [h]

/-- The folded two-event representative is constant on connected components of
the two-event support graph. -/
theorem collisionSubfamilyPairComponentRep_eq_of_connected
    {q : Nat} {e₁ e₂ : CollisionEvent q} {i j : Fin q}
    (hconn : collisionSubfamilyConnected (q := q)
      ({e₁, e₂} : Finset (CollisionEvent q)) i j) :
    collisionSubfamilyPairComponentRep e₁ e₂ i =
      collisionSubfamilyPairComponentRep e₁ e₂ j := by
  induction hconn with
  | refl => rfl
  | tail _ hadj ih =>
      exact ih.trans (collisionSubfamilyPairComponentRep_eq_of_adjacent hadj)

/-- Map two-event connected components to the image of the folded
representative. -/
noncomputable def collisionSubfamilyPairComponentToRepImage
    {q : Nat} (e₁ e₂ : CollisionEvent q) :
    collisionSubfamilyComponent (q := q) ({e₁, e₂} : Finset (CollisionEvent q)) →
      ((Finset.univ : Finset (Fin q)).image
        (collisionSubfamilyPairComponentRep e₁ e₂)) :=
  fun c => Quotient.liftOn c
    (fun i => ⟨collisionSubfamilyPairComponentRep e₁ e₂ i, by simp⟩)
    (by
      intro i j hij
      apply Subtype.ext
      exact collisionSubfamilyPairComponentRep_eq_of_connected
        (by simpa [collisionSubfamilyConnectedSetoid] using hij))

/-- Every representative value in the folded-image is attained by a two-event
support component. -/
theorem collisionSubfamilyPairComponentToRepImage_surjective
    {q : Nat} (e₁ e₂ : CollisionEvent q) :
    Function.Surjective (collisionSubfamilyPairComponentToRepImage e₁ e₂) := by
  intro r
  rcases Finset.mem_image.mp r.2 with ⟨i, _hi, hir⟩
  refine ⟨Quotient.mk (collisionSubfamilyConnectedSetoid (q := q)
    ({e₁, e₂} : Finset (CollisionEvent q))) i, ?_⟩
  apply Subtype.ext
  exact hir

/-- The folded representative image has at least `q - 2` values: starting from
the `q - 1` singleton representatives of `{e₁}`, the second fold can remove at
most one value. -/
theorem collisionSubfamilyPairComponentRep_image_card_lower
    {q : Nat} (e₁ e₂ : CollisionEvent q) :
    q - 2 ≤ ((Finset.univ : Finset (Fin q)).image
      (collisionSubfamilyPairComponentRep e₁ e₂)).card := by
  have hsub :
      ((Finset.univ : Finset {j : Fin q // j ≠ collisionEventRight e₁}).erase
        (collisionSubfamilySingletonComponentRep (q := q) e₁
          (collisionEventRight e₂))) ⊆
        (Finset.univ : Finset (Fin q)).image
          (collisionSubfamilyPairComponentRep e₁ e₂) := by
    intro r hr
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hr
    refine Finset.mem_image.mpr ⟨r.1, by simp, ?_⟩
    unfold collisionSubfamilyPairComponentRep collisionSubfamilySingletonComponentRep
    have hnot_right : ¬ r.1 = collisionEventRight e₁ := r.2
    rw [dif_neg hnot_right]
    simp only
    rw [if_neg (by
      intro h
      exact hr (by simpa [collisionSubfamilySingletonComponentRep, hnot_right] using h))]
  have hcard_le := Finset.card_le_card hsub
  have hsubtype_card :
      Fintype.card {j : Fin q // j ≠ collisionEventRight e₁} = q - 1 := by
    rw [Fintype.card_subtype_compl (p := fun i : Fin q => i = collisionEventRight e₁)]
    simp
  have hcard_erase :
      (((Finset.univ : Finset {j : Fin q // j ≠ collisionEventRight e₁}).erase
        (collisionSubfamilySingletonComponentRep (q := q) e₁
          (collisionEventRight e₂))).card) =
        q - 2 := by
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_univ, hsubtype_card]
      omega
    · simp
  omega

/-- Pure graph endpoint for the support-cardinality-two cancellation proof:
any support graph with at most two selected collision events has graphic rank at
most two. -/
def TwoEventGraphicRankLeTwo (q : Nat) : Prop :=
  ∀ e₁ e₂ : CollisionEvent q,
    collisionSubfamilyGraphicRank (q := q) ({e₁, e₂} : Finset (CollisionEvent q)) ≤ 2

/-- A two-event support graph has graphic rank at most two.  The proof maps
components onto the folded representative image; the image has at least `q - 2`
values, so the graph has at least `q - 2` components. -/
theorem twoEventGraphicRankLeTwo (q : Nat) :
    TwoEventGraphicRankLeTwo q := by
  intro e₁ e₂
  have himage_le_comp :
      ((Finset.univ : Finset (Fin q)).image
        (collisionSubfamilyPairComponentRep e₁ e₂)).card ≤
        collisionSubfamilyComponentCount (q := q)
          ({e₁, e₂} : Finset (CollisionEvent q)) := by
    have h := Fintype.card_le_of_surjective
      (collisionSubfamilyPairComponentToRepImage e₁ e₂)
      (collisionSubfamilyPairComponentToRepImage_surjective e₁ e₂)
    rw [Fintype.card_coe] at h
    simpa [collisionSubfamilyComponentCount] using h
  have himage_lower := collisionSubfamilyPairComponentRep_image_card_lower e₁ e₂
  unfold collisionSubfamilyGraphicRank
  omega

/-- A two-element query-pair support has a canonical hidden representative that
is literally a two-event support graph. -/
theorem collisionPairSupportHiddenRepresentative_eq_pair_of_card_eq_two
    {q : Nat} {S : Finset (PairIndex q)}
    (hS : S.card = 2) :
    ∃ p₀ p₁ : PairIndex q, p₀ ≠ p₁ ∧
      collisionPairSupportHiddenRepresentative (q := q) S =
        ({(p₀, CollisionKind.hidden), (p₁, CollisionKind.hidden)} :
          Finset (CollisionEvent q)) := by
  rcases Finset.card_eq_two.mp hS with ⟨p₀, p₁, hp_ne, hS_eq⟩
  refine ⟨p₀, p₁, hp_ne, ?_⟩
  unfold collisionPairSupportHiddenRepresentative
  ext e
  constructor
  · intro he
    simp only [Finset.mem_image] at he
    rcases he with ⟨p, hpS, hpe⟩
    have hp_cases : p = p₀ ∨ p = p₁ := by
      have : p ∈ ({p₀, p₁} : Finset (PairIndex q)) := by
        simpa [hS_eq] using hpS
      simpa using this
    rcases hp_cases with rfl | rfl <;> simp [hpe]
  · intro he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact Finset.mem_image.mpr ⟨p₀, by simp [hS_eq], rfl⟩
    · exact Finset.mem_image.mpr ⟨p₁, by simp [hS_eq], rfl⟩

/-- The pure two-event graph endpoint implies the specialized hidden
representative endpoint needed for support-cardinality-two cancellation. -/
theorem HiddenRepresentativeGraphicRankLeTwoOnCardTwo.of_twoEvent
    {q : Nat} (htwo : TwoEventGraphicRankLeTwo q) :
    HiddenRepresentativeGraphicRankLeTwoOnCardTwo q := by
  intro S hS
  rcases collisionPairSupportHiddenRepresentative_eq_pair_of_card_eq_two
      (q := q) (S := S) hS with ⟨p₀, p₁, _hp_ne, hrep⟩
  rw [hrep]
  exact htwo (p₀, CollisionKind.hidden) (p₁, CollisionKind.hidden)

/-- The specialized hidden-representative graph endpoint is unconditional. -/
theorem hiddenRepresentativeGraphicRankLeTwoOnCardTwo (q : Nat) :
    HiddenRepresentativeGraphicRankLeTwoOnCardTwo q :=
  HiddenRepresentativeGraphicRankLeTwoOnCardTwo.of_twoEvent
    (twoEventGraphicRankLeTwo q)

/-- Signed pair-local coefficient of one query pair in the rank-one Mayer
layer.  It is `-2` unless the visible outputs collide on that pair, in which
case the hidden+shifted two-edge subfamily is cycle-consistent and the
coefficient is `-1`. -/
def pairCollisionCoefficientInt (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) (p : PairIndex q) : ℤ :=
  -2 + (if y p.1.2 = y p.1.1 then 1 else 0)

/-- Pair-local rank-one coefficient as a function of the visible collision
set.  This isolates the transcript dependence before the global forest sum is
normalized. -/
theorem pairCollisionCoefficientInt_eq_pairCollisionSet
    (G : Type*) [DecidableEq G] {q : Nat} (y : Fin q → G) (p : PairIndex q) :
    pairCollisionCoefficientInt G q y p =
      (-2 + (if p ∈ pairCollisionSet G y then 1 else 0) : ℤ) := by
  classical
  unfold pairCollisionCoefficientInt pairCollisionSet
  by_cases h : y p.1.2 = y p.1.1 <;> simp [h]

/-- The forest part of the signed rank-two coefficient: choose two distinct
query pairs and multiply their pair-local rank-one coefficients. -/
def rankTwoForestCoefficientInt (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powerset with S.card = 2,
    ∏ p ∈ S, pairCollisionCoefficientInt G q y p

/-- Forest coefficient as a function only of the visible collision-pair set. -/
def rankTwoForestCollisionSetCoefficientInt {q : Nat}
    (C : Finset (PairIndex q)) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
    ∏ p ∈ S, (-2 + (if p ∈ C then 1 else 0) : ℤ)

/-- Power-count form of the same forest coefficient: each two-subset
contributes one factor `-1` for every visible collision pair and one factor
`-2` for every non-collision pair. -/
def rankTwoForestCollisionSetPowerCoefficientInt {q : Nat}
    (C : Finset (PairIndex q)) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
    (-1 : ℤ) ^ (S.filter fun p => p ∈ C).card *
      (-2 : ℤ) ^ (S.filter fun p => p ∉ C).card

/-- Closed collision-count form of the forest coefficient.  If `C` is the set
of visible-collision query pairs, the two-subset forest sum is obtained from
the total number of query-pair two-subsets, the all-collision two-subsets, and
the all-noncollision two-subsets. -/
def rankTwoForestCollisionCountCoefficientInt {q : Nat}
    (C : Finset (PairIndex q)) : ℤ :=
  2 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
    (((C.card.choose 2 : Nat) : ℤ)) +
    2 * (((((Finset.univ : Finset (PairIndex q)) \ C).card.choose 2 : Nat) : ℤ))

/-- A single forest summand depends only on the number of its two query pairs
that are visible collisions.  This is Mathlib's standard filter/complement
product split specialized to the two-valued pair weight. -/
theorem rankTwoForestCollisionSetSummand_eq_power
    {q : Nat} (C S : Finset (PairIndex q)) :
    (∏ p ∈ S, (-2 + (if p ∈ C then 1 else 0) : ℤ)) =
      (-1 : ℤ) ^ (S.filter fun p => p ∈ C).card *
        (-2 : ℤ) ^ (S.filter fun p => p ∉ C).card := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p ∈ C)
      (fun p => (-2 + (if p ∈ C then 1 else 0) : ℤ))]
  congr 1
  · rw [Finset.prod_eq_pow_card]
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp [hp.2]
  · rw [Finset.prod_eq_pow_card]
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp [hp.2]

/-- The collision-set forest coefficient in product form equals its power-count
normal form. -/
theorem rankTwoForestCollisionSetCoefficientInt_eq_power
    {q : Nat} (C : Finset (PairIndex q)) :
    rankTwoForestCollisionSetCoefficientInt C =
      rankTwoForestCollisionSetPowerCoefficientInt C := by
  classical
  unfold rankTwoForestCollisionSetCoefficientInt
    rankTwoForestCollisionSetPowerCoefficientInt
  apply Finset.sum_congr rfl
  intro S _hS
  exact rankTwoForestCollisionSetSummand_eq_power C S

/-- The two-subsets of the whole query-pair universe that are contained in
`C` are exactly the two-subsets of `C`. -/
theorem rankTwoForestCollisionSet_filter_subset_eq_powersetCard
    {q : Nat} (C : Finset (PairIndex q)) :
    ((Finset.univ : Finset (PairIndex q)).powersetCard 2).filter
        (fun S => S ⊆ C) =
      C.powersetCard 2 := by
  classical
  ext S
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
    true_and]
  constructor <;> intro h
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.2, h.1⟩

/-- Summing the indicator of `S ⊆ C` over all query-pair two-subsets gives
`|C| choose 2`. -/
theorem rankTwoForestCollisionSet_sum_subset_indicator
    {q : Nat} (C : Finset (PairIndex q)) :
    (∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
      (if S ⊆ C then (1 : ℤ) else 0)) =
        (C.card.choose 2 : ℤ) := by
  classical
  rw [← Finset.sum_filter]
  rw [rankTwoForestCollisionSet_filter_subset_eq_powersetCard]
  simp

/-- On a two-subset, the power-count forest summand is `2`, corrected by
whether both query pairs are visible collisions or both are visible
non-collisions. -/
theorem rankTwoForestCollisionSetPowerSummand_eq_piecewise
    {q : Nat} (C S : Finset (PairIndex q))
    (hS : S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2) :
    (-1 : ℤ) ^ (S.filter fun p => p ∈ C).card *
        (-2 : ℤ) ^ (S.filter fun p => p ∉ C).card =
      (2 - (if S ⊆ C then 1 else 0) +
        2 * (if S ⊆ (Finset.univ : Finset (PairIndex q)) \ C then 1 else 0) : ℤ) := by
  classical
  have hcard : S.card = 2 := (Finset.mem_powersetCard.mp hS).2
  by_cases hC : S ⊆ C
  · have hfilter : (S.filter fun p => p ∈ C).card = 2 := by
      rw [← hcard]
      apply congr_arg Finset.card
      exact Finset.filter_eq_self.mpr hC
    have hnot : (S.filter fun p => p ∉ C).card = 0 := by
      rw [Finset.card_eq_zero]
      exact Finset.filter_eq_empty_iff.mpr
        (fun p hpS hpC => hpC (hC hpS))
    have hDfalse : ¬ S ⊆ (Finset.univ : Finset (PairIndex q)) \ C := by
      intro hD
      have hempty : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hpS
        have hpC := hC hpS
        have hpD := hD hpS
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hpD
        exact hpD hpC
      have hzero : S.card = 0 := by simp [hempty]
      omega
    simp [hfilter, hnot, hC, hDfalse]
  · by_cases hD : S ⊆ (Finset.univ : Finset (PairIndex q)) \ C
    · have hfilter : (S.filter fun p => p ∈ C).card = 0 := by
        rw [Finset.card_eq_zero]
        exact Finset.filter_eq_empty_iff.mpr (fun p hpS hpC => by
          have hpD := hD hpS
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hpD
          exact hpD hpC)
      have hnot : (S.filter fun p => p ∉ C).card = 2 := by
        rw [← hcard]
        apply congr_arg Finset.card
        exact Finset.filter_eq_self.mpr (fun p hpS => by
          have hpD := hD hpS
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hpD
          exact hpD)
      simp [hfilter, hnot, hC, hD]
    · have hle : (S.filter fun p => p ∈ C).card ≤ 2 := by
        rw [← hcard]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      have hne2 : (S.filter fun p => p ∈ C).card ≠ 2 := by
        intro h2
        apply hC
        intro p hpS
        by_contra hpC
        have hproper : S.filter (fun p => p ∈ C) ⊂ S := by
          refine ⟨Finset.filter_subset _ _, ?_⟩
          intro hsubset
          have : p ∈ S.filter (fun p => p ∈ C) := hsubset hpS
          exact hpC (Finset.mem_filter.mp this).2
        have hlt := Finset.card_lt_card hproper
        rw [h2, hcard] at hlt
        omega
      have hne0 : (S.filter fun p => p ∈ C).card ≠ 0 := by
        intro h0
        apply hD
        intro p hpS
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        by_contra hpC
        have : p ∈ S.filter (fun p => p ∈ C) := by simp [hpS, hpC]
        have hempty : S.filter (fun p => p ∈ C) = ∅ :=
          Finset.card_eq_zero.mp h0
        rw [hempty] at this
        simp at this
      have hfilter : (S.filter fun p => p ∈ C).card = 1 := by
        omega
      have hnot : (S.filter fun p => p ∉ C).card = 1 := by
        have hsum :=
          Finset.card_filter_add_card_filter_not (s := S) (p := fun p => p ∈ C)
        rw [hfilter, hcard] at hsum
        omega
      simp [hfilter, hnot, hC, hD]

/-- The piecewise two-subset forest sum evaluates to the closed
collision-count coefficient. -/
theorem rankTwoForestCollisionSetPiecewiseSum_eq_count
    {q : Nat} (C : Finset (PairIndex q)) :
    (∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
      (2 - (if S ⊆ C then 1 else 0) +
        2 * (if S ⊆ (Finset.univ : Finset (PairIndex q)) \ C then 1 else 0) : ℤ)) =
      rankTwoForestCollisionCountCoefficientInt C := by
  classical
  unfold rankTwoForestCollisionCountCoefficientInt
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [rankTwoForestCollisionSet_sum_subset_indicator]
  rw [rankTwoForestCollisionSet_sum_subset_indicator
    ((Finset.univ : Finset (PairIndex q)) \ C)]
  simp [Finset.card_powersetCard, mul_comm]

/-- The power-count forest coefficient is the closed collision-count
coefficient. -/
theorem rankTwoForestCollisionSetPowerCoefficientInt_eq_count
    {q : Nat} (C : Finset (PairIndex q)) :
    rankTwoForestCollisionSetPowerCoefficientInt C =
      rankTwoForestCollisionCountCoefficientInt C := by
  classical
  unfold rankTwoForestCollisionSetPowerCoefficientInt
  trans ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powersetCard 2,
      (2 - (if S ⊆ C then 1 else 0) +
        2 * (if S ⊆ (Finset.univ : Finset (PairIndex q)) \ C then 1 else 0) : ℤ)
  · apply Finset.sum_congr rfl
    intro S hS
    exact rankTwoForestCollisionSetPowerSummand_eq_piecewise C S hS
  · exact rankTwoForestCollisionSetPiecewiseSum_eq_count C

/-- The collision-set forest coefficient is the closed collision-count
coefficient. -/
theorem rankTwoForestCollisionSetCoefficientInt_eq_count
    {q : Nat} (C : Finset (PairIndex q)) :
    rankTwoForestCollisionSetCoefficientInt C =
      rankTwoForestCollisionCountCoefficientInt C := by
  rw [rankTwoForestCollisionSetCoefficientInt_eq_power,
    rankTwoForestCollisionSetPowerCoefficientInt_eq_count]

/-- Closed forest coefficient for an actual transcript, written only in terms
of the visible pair-collision count. -/
theorem rankTwoForestCollisionCountCoefficientInt_pairCollisionSet_eq_pairCollisionCount
    (G : Type*) [DecidableEq G] {q : Nat} (y : Fin q → G) :
    rankTwoForestCollisionCountCoefficientInt (pairCollisionSet G y) =
      2 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
        (((pairCollisionCountNat G q y).choose 2 : Nat) : ℤ) +
        2 * (((((Fintype.card (PairIndex q) -
          pairCollisionCountNat G q y).choose 2 : Nat) : ℤ))) := by
  classical
  unfold rankTwoForestCollisionCountCoefficientInt
  have hsubset : pairCollisionSet G y ⊆ (Finset.univ : Finset (PairIndex q)) := by
    intro p _hp
    simp
  rw [Finset.card_sdiff_of_subset hsubset]
  simp [pairCollisionSet_card]

/-- The rank-two forest coefficient depends on the transcript only through
the visible collision-pair set. -/
theorem rankTwoForestCoefficientInt_eq_collisionSet
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    rankTwoForestCoefficientInt G q y =
      rankTwoForestCollisionSetCoefficientInt (pairCollisionSet G y) := by
  classical
  unfold rankTwoForestCoefficientInt rankTwoForestCollisionSetCoefficientInt
  rw [← Finset.powersetCard_eq_filter]
  apply Finset.sum_congr rfl
  intro S _hS
  apply Finset.prod_congr rfl
  intro p _hp
  exact pairCollisionCoefficientInt_eq_pairCollisionSet (G := G) (y := y) p

/-- Product-of-local-sums form of the forest part of the signed rank-two
coefficient.  This is the intermediate target for reindexing
support-cardinality-two collision-event subfamilies by their two pair-local
fibers. -/
def rankTwoForestPairFiberProductCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (PairIndex q)).powerset with S.card = 2,
    ∏ p ∈ S,
      ((collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)).sum
        (fun T =>
          if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (-1 : ℤ) ^ T.card
          else
            0)

/-- The product-of-local-sums coefficient attached to one exact query-pair
support set. -/
def rankTwoPairSupportProductCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  ∏ p ∈ S,
    ((collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)).sum
      (fun T =>
        if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
          (-1 : ℤ) ^ T.card
        else
          0)

/-- Product-side coefficient for one exact query-pair support, expanded as a
single sum over choices of one nonempty pair-local subfamily for each touched
query pair.  This is the standard finite-product expansion needed for the
support-cardinality-two bijection: the remaining work is to identify such local
choices with their disjoint union collision subfamily. -/
def rankTwoPairSupportPiProductCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  ∑ F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)),
    ∏ p : S,
      (if collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p p.2) then
        (-1 : ℤ) ^ (F p p.2).card
      else
        0)

/-- Exact-support coefficient expanded over pair-local nonempty fibers while
retaining the global cycle-consistency predicate.  This is the non-factorized
variant needed for triangle supports. -/
def rankTwoPairSupportPiUnionCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  ∑ F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)),
    if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S)
        (fun p : S => F p.1 p.2)).card
    else
      0

/-- Exact-support rank-two coefficient expanded over pair-local nonempty fibers,
retaining both the graphic-rank test and the global cycle-consistency predicate.
This is the rank-retaining variant needed before the local triangle
calculation proves rank automaticity or evaluates the rank test directly. -/
def rankTwoPairSupportPiUnionRankCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  ∑ F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)),
    let U := collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)
    if collisionSubfamilyGraphicRank (q := q) U = 2 then
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y U then
        (-1 : ℤ) ^ U.card
      else
        0
    else
      0

/-- Exact-support rank-three coefficient expanded over pair-local nonempty
fibers, retaining both the graphic-rank test and the global cycle-consistency
predicate.  This is the rank-three companion to
`rankTwoPairSupportPiUnionRankCoefficientInt`. -/
def rankThreePairSupportPiUnionRankCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  ∑ F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)),
    let U := collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)
    if collisionSubfamilyGraphicRank (q := q) U = 3 then
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y U then
        (-1 : ℤ) ^ U.card
      else
        0
    else
      0

/-- Exact-support rank-three coefficient expanded over pair-local nonempty
fibers after the support-level rank-three condition has made the per-choice
rank test automatic. -/
def rankThreePairSupportPiUnionCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  rankTwoPairSupportPiUnionCoefficientInt G q y S

/-- The exact-support product coefficient is definitionally the `Finset.pi`
expansion over pair-local nonempty fibers.  This is a product-to-sum reindexing
step; it does not use rank, labels, or any small-\(q\) enumeration. -/
theorem rankTwoPairSupportProductCoefficientInt_eq_piProduct
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) (S : Finset (PairIndex q)) :
    rankTwoPairSupportProductCoefficientInt G q y S =
      rankTwoPairSupportPiProductCoefficientInt G q y S := by
  unfold rankTwoPairSupportProductCoefficientInt
    rankTwoPairSupportPiProductCoefficientInt
  rw [Finset.prod_sum]
  rfl

/-- The exact-support product coefficient is the product of the local pair
coefficients. -/
theorem rankTwoPairSupportProductCoefficientInt_eq_prod_pairCollisionCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) (S : Finset (PairIndex q)) :
    rankTwoPairSupportProductCoefficientInt G q y S =
      ∏ p ∈ S, pairCollisionCoefficientInt G q y p := by
  unfold rankTwoPairSupportProductCoefficientInt
  apply Finset.prod_congr rfl
  intro p _hp
  exact collisionPairEvents_localPowersetAlternatingCoefficient_ite
    (G := G) (q := q) y p

/-- If cycle consistency factorizes over an exact support, then the union-form
exact-support coefficient equals the product-form exact-support coefficient. -/
theorem rankTwoPairSupportPiUnionCoefficientInt_eq_product_of_cycleConsistentFactors
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) (S : Finset (PairIndex q))
    (hfactor : PairSupportCycleConsistentFactors G y S) :
    rankTwoPairSupportPiUnionCoefficientInt G q y S =
      rankTwoPairSupportProductCoefficientInt G q y S := by
  rw [rankTwoPairSupportProductCoefficientInt_eq_piProduct]
  unfold rankTwoPairSupportPiUnionCoefficientInt rankTwoPairSupportPiProductCoefficientInt
  apply Finset.sum_congr rfl
  intro F hF
  have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
    intro p
    exact pairChoice_mem_pi_subset_pairEvents hF p
  exact collisionSubfamilyPairChoiceUnion_signedTerm_eq_prod_of_cycleConsistent_iff
    (G := G) (q := q) (y := y) (F := fun p : S => F p.1 p.2) hsub
    (hfactor F hF)

/-- The pair-fiber product form is definitionally the same forest coefficient
after evaluating each pair-local nonempty powerset sum. -/
theorem rankTwoForestPairFiberProductCoefficientInt_eq_forest
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) :
    rankTwoForestPairFiberProductCoefficientInt G q y =
      rankTwoForestCoefficientInt G q y := by
  unfold rankTwoForestPairFiberProductCoefficientInt rankTwoForestCoefficientInt
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.mem_filter] at hS
  apply Finset.prod_congr rfl
  intro p _hp
  exact collisionPairEvents_localPowersetAlternatingCoefficient_ite (G := G) (q := q) y p

/-- The global pair-fiber product coefficient is the sum of its exact-support
product coefficients over two-element query-pair supports. -/
theorem rankTwoForestPairFiberProductCoefficientInt_eq_sum_pairSupportProduct
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (y : Fin q → G) :
    rankTwoForestPairFiberProductCoefficientInt G q y =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = 2),
        rankTwoPairSupportProductCoefficientInt G q y S := by
  rfl

/-- All visible outputs indexed by `S` are equal. -/
def visibleAllEqualOn (G : Type*) [DecidableEq G] {q : Nat}
    (y : Fin q → G) (S : Finset (Fin q)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, y i = y j

/-- Visible tuples with a fixed three-coordinate equality are equivalent to
free assignments on the remaining `q - 2` coordinates.  The coordinate `i`
serves as the representative value for `j` and `k`. -/
noncomputable def orderedTripleAllEqualFiberEquiv
    {G : Type*} [DecidableEq G] {q : Nat} {i j k : Fin q}
    (hij : i ≠ j) (hik : i ≠ k) (_hjk : j ≠ k) :
    { y : Fin q → G // y i = y j ∧ y j = y k } ≃
      ({ l : Fin q // l ≠ j ∧ l ≠ k } → G) where
  toFun y := fun l => y.1 l.1
  invFun f := ⟨fun l =>
    if hlj : l = j then f ⟨i, by exact ⟨hij, hik⟩⟩
    else if hlk : l = k then f ⟨i, by exact ⟨hij, hik⟩⟩
    else f ⟨l, by exact ⟨hlj, hlk⟩⟩, by
      constructor <;> simp⟩
  left_inv y := by
    ext l
    by_cases hlj : l = j
    · subst l
      simp
      exact y.2.1
    · by_cases hlk : l = k
      · subst l
        simp
        exact y.2.1.trans y.2.2
      · simp [hlj, hlk]
  right_inv f := by
    funext l
    simp [l.2.1, l.2.2]

/-- Removing two distinct coordinates from `Fin q` leaves `q - 2` coordinates.
-/
theorem card_subtype_ne_two {q : Nat} {j k : Fin q} (hjk : j ≠ k) :
    Fintype.card { l : Fin q // l ≠ j ∧ l ≠ k } = q - 2 := by
  rw [Fintype.card_subtype]
  have hfilter : (Finset.univ.filter (fun l : Fin q => l ≠ j ∧ l ≠ k)) =
      (Finset.univ : Finset (Fin q)) \ ({j, k} : Finset (Fin q)) := by
    ext l
    simp
  rw [hfilter]
  rw [Finset.card_sdiff]
  simp [hjk]

/-- For three pairwise distinct coordinates, exactly `|G|^(q-2)` visible
tuples make the three outputs all equal. -/
theorem orderedTripleAllEqualFiber_card
    {G : Type*} [Fintype G] [DecidableEq G]
    {q : Nat} {i j k : Fin q} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ((Finset.univ : Finset (Fin q → G)).filter
      (fun y => y i = y j ∧ y j = y k)).card =
      Fintype.card G ^ (q - 2) := by
  classical
  calc
    ((Finset.univ : Finset (Fin q → G)).filter
      (fun y => y i = y j ∧ y j = y k)).card =
        Fintype.card { y : Fin q → G // y i = y j ∧ y j = y k } := by
          rw [Fintype.card_subtype]
    _ = Fintype.card ({ l : Fin q // l ≠ j ∧ l ≠ k } → G) := by
          exact Fintype.card_congr (orderedTripleAllEqualFiberEquiv
            (G := G) hij hik hjk)
    _ = Fintype.card G ^ Fintype.card { l : Fin q // l ≠ j ∧ l ≠ k } := by
          rw [Fintype.card_fun]
    _ = Fintype.card G ^ (q - 2) := by
          rw [card_subtype_ne_two hjk]

/-- For an ordered triple of coordinates, the `visibleAllEqualOn` predicate is
equivalent to the two adjacent equalities. -/
theorem visibleAllEqualOn_orderedTriple_iff
    {G : Type*} [DecidableEq G] {q : Nat} {y : Fin q → G}
    {i j k : Fin q} (hij : i < j) (hjk : j < k) :
    visibleAllEqualOn G y ({i, j, k} : Finset (Fin q)) ↔ y i = y j ∧ y j = y k := by
  constructor
  · intro h
    constructor
    · exact h i (by simp) j (by simp)
    · exact h j (by simp) k (by simp)
  · intro h a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases h with ⟨hijv, hjkv⟩
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;> grind

/-- Any fixed three-coordinate all-equal fiber has cardinality `|G|^(q - 2)`.
This is the unordered-set form of `orderedTripleAllEqualFiber_card`. -/
theorem visibleAllEqualOn_fiber_card_of_card_eq_three
    {G : Type*} [Fintype G] [DecidableEq G]
    {q : Nat} {S : Finset (Fin q)}
    [DecidablePred (fun y : Fin q → G => visibleAllEqualOn G y S)]
    (hS : S.card = 3) :
    ((Finset.univ : Finset (Fin q → G)).filter
      (fun y => visibleAllEqualOn G y S)).card =
      Fintype.card G ^ (q - 2) := by
  classical
  rcases exists_orderedTriple_eq_of_card_eq_three (q := q) (V := S) hS with
    ⟨i, j, k, hij, hjk, rfl⟩
  have hik : i < k := hij.trans hjk
  have hp : ((Finset.univ : Finset (Fin q → G)).filter
      (fun y => visibleAllEqualOn G y ({i, j, k} : Finset (Fin q)))) =
      ((Finset.univ : Finset (Fin q → G)).filter
        (fun y => y i = y j ∧ y j = y k)) := by
    ext y
    simp [visibleAllEqualOn_orderedTriple_iff (G := G) (y := y) hij hjk]
  rw [hp]
  exact orderedTripleAllEqualFiber_card (G := G)
    (hij := ne_of_lt hij) (hik := ne_of_lt hik) (hjk := ne_of_lt hjk)

/-- On an all-equal visible coordinate set, every internal hidden/shifted
collision event has zero gain label. -/
theorem collisionEventLabel_eq_zero_of_mem_queryPairSet_of_visibleAllEqualOn
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {y : Fin q → G} {V : Finset (Fin q)} {e : CollisionEvent q}
    (heV : e.1 ∈ queryPairSet V)
    (hall : visibleAllEqualOn G y V) :
    collisionEventLabel y e = 0 := by
  have hleft : collisionEventLeft e ∈ V := by
    simp only [queryPairSet, Finset.mem_filter, Finset.mem_univ, true_and] at heV
    simpa [collisionEventLeft] using heV.1
  have hright : collisionEventRight e ∈ V := by
    simp only [queryPairSet, Finset.mem_filter, Finset.mem_univ, true_and] at heV
    simpa [collisionEventRight] using heV.2
  cases e with
  | mk p k =>
      cases k
      · simp [collisionEventLabel]
      · have hy : y p.1.2 = y p.1.1 := hall p.1.2 hright p.1.1 hleft
        simp [collisionEventLabel, collisionEventLeft, collisionEventRight, hy]

/-- If every touched query pair lies in an all-equal visible coordinate set,
then every selected hidden/shifted event has label zero, so the subfamily is
cycle-consistent. -/
theorem collisionSubfamilyCycleConsistent_of_pairSupport_subset_queryPairSet_of_visibleAllEqualOn
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {y : Fin q → G} {V : Finset (Fin q)} {T : Finset (CollisionEvent q)}
    (hsupport : collisionSubfamilyPairSupport q T ⊆ queryPairSet V)
    (hall : visibleAllEqualOn G y V) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y T := by
  rw [← collisionSubfamilyConsistent_iff_cycleConsistent]
  refine ⟨fun _ => 0, ?_⟩
  intro e heT
  have hp : e.1 ∈ collisionSubfamilyPairSupport q T :=
    (mem_collisionSubfamilyPairSupport_iff (T := T) (p := e.1)).mpr ⟨e.2, heT⟩
  have hlabel :
      collisionEventLabel y e = 0 :=
    collisionEventLabel_eq_zero_of_mem_queryPairSet_of_visibleAllEqualOn
      (G := G) (q := q) (y := y) (V := V) (e := e) (hsupport hp) hall
  unfold collisionEventEquation
  simp [hlabel]

/-- The unfiltered nonempty pair-local alternating sum is `-1`: the two
singletons contribute `-1` each and the full hidden/shifted pair contributes
`+1`. -/
theorem collisionPairEvents_localNonemptyPowersetAlternatingCard
    {q : Nat} (p : PairIndex q) :
    ((collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)).sum
      (fun T => (-1 : ℤ) ^ T.card) = -1 := by
  rw [show (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty) =
      ({{(p, CollisionKind.hidden)}, {(p, CollisionKind.shifted)},
        collisionPairEvents (q := q) p} : Finset (Finset (CollisionEvent q))) by
    simpa [collisionPairEvents] using
      finset_pair_powerset_filter_nonempty
        (a := (p, CollisionKind.hidden)) (b := (p, CollisionKind.shifted)) (by simp)]
  rw [Finset.sum_insert]
  · rw [Finset.sum_insert]
    · rw [Finset.sum_singleton]
      simp [collisionPairEvents]
    · simpa using finset_singleton_ne_pair_right
        (a := (p, CollisionKind.hidden)) (b := (p, CollisionKind.shifted)) (by simp)
  · intro hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hsingle | hpair
    · have hkind : CollisionKind.hidden = CollisionKind.shifted := by
        exact congrArg Prod.snd (Finset.singleton_inj.mp hsingle)
      cases hkind
    · exact finset_singleton_ne_pair_left
        (a := (p, CollisionKind.hidden)) (b := (p, CollisionKind.shifted)) (by simp) hpair

/-- On an all-equal visible vertex set, the no-rank exact-support pair-fiber
sum factorizes into independent unfiltered pair-local alternating sums.  The
cycle-consistency predicate is automatic because all internal gains are zero. -/
theorem rankTwoPairSupportPiUnionCoefficientInt_eq_localProduct_of_visibleAllEqualOn
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) (V : Finset (Fin q))
    (hall : visibleAllEqualOn G y V) :
    rankTwoPairSupportPiUnionCoefficientInt G q y (queryPairSet V) =
      ∏ p ∈ queryPairSet V,
        (((collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)).sum
          (fun T => (-1 : ℤ) ^ T.card)) := by
  unfold rankTwoPairSupportPiUnionCoefficientInt
  rw [Finset.prod_sum]
  apply Finset.sum_congr rfl
  intro F hF
  have hFmem : F ∈ (queryPairSet V).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
    hF
  have hsub : ∀ p : (queryPairSet V), F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
    intro p
    exact pairChoice_mem_pi_subset_pairEvents hFmem p
  have hne : ∀ p : (queryPairSet V), (F p.1 p.2).Nonempty := by
    intro p
    exact pairChoice_mem_pi_nonempty hFmem p
  have hsupport : collisionSubfamilyPairSupport q
        (collisionSubfamilyPairChoiceUnion (S := queryPairSet V)
          (fun p : queryPairSet V => F p.1 p.2)) =
      queryPairSet V :=
    collisionSubfamilyPairSupport_pairChoiceUnion_eq
      (q := q) (S := queryPairSet V) (F := fun p : queryPairSet V => F p.1 p.2)
      hsub hne
  have hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := queryPairSet V)
          (fun p : queryPairSet V => F p.1 p.2)) := by
    apply collisionSubfamilyCycleConsistent_of_pairSupport_subset_queryPairSet_of_visibleAllEqualOn
      (G := G) (q := q) (y := y) (V := V)
    · intro p hp
      rw [hsupport] at hp
      exact hp
    · exact hall
  simp [hcyc, collisionSubfamilyPairChoiceUnion_card_eq_sum
    (F := fun p : queryPairSet V => F p.1 p.2) hsub]
  exact (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (queryPairSet V))
    (fun p => (F p.1 p.2).card) (-1 : ℤ)).symm

/-- The all-equal branch of the no-rank triangle calculation: once the three
visible outputs on `V` are equal, all selected internal events are
cycle-consistent and the three pair-local alternating sums multiply to `-1`. -/
theorem rankTwoPairSupportPiUnionCoefficientInt_eq_neg_one_of_visibleAllEqualOn
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {V : Finset (Fin q)}
    (hV : V.card = 3) (hall : visibleAllEqualOn G y V) :
    rankTwoPairSupportPiUnionCoefficientInt G q y (queryPairSet V) = -1 := by
  rw [rankTwoPairSupportPiUnionCoefficientInt_eq_localProduct_of_visibleAllEqualOn
    (G := G) (q := q) y V hall]
  simp_rw [collisionPairEvents_localNonemptyPowersetAlternatingCard]
  rw [Finset.prod_const]
  simp [queryPairSet_card_eq_three_of_card_eq_three hV]

/-- If a globally cycle-consistent pair-choice union uses the full
hidden/shifted local pair on one edge, then the visible outputs on that edge
must be equal. -/
theorem pairChoice_visible_eq_of_global_cycleConsistent_of_eq_pairEvents
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S : Finset (PairIndex q)} {y : Fin q → G}
    {F : ∀ _p : S, Finset (CollisionEvent q)}
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion F))
    {p : S} (hfull : F p = collisionPairEvents (q := q) p.1) :
    y p.1.1.2 = y p.1.1.1 := by
  have hlocal : collisionSubfamilyCycleConsistent (G := G) (q := q) y (F p) :=
    collisionSubfamilyPairChoiceUnion_local_cycleConsistent_of_global
      (G := G) (q := q) (F := F) (p := p) hglobal
  rw [hfull] at hlocal
  exact (collisionPairEvents_cycleConsistent_iff (G := G) (q := q) y p.1).mp hlocal

/-- On a visibly unequal edge, any globally cycle-consistent pair-choice union
must choose a singleton local event over that edge.  This is the first pruning
step for the non-all-equal triangle branch. -/
theorem exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {S : Finset (PairIndex q)} {y : Fin q → G}
    {F : (p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)}
    (hF : F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)))
    {p : S} (hneq : y p.1.1.2 ≠ y p.1.1.1) :
    ∃ k : CollisionKind, F p.1 p.2 = {(p.1, k)} := by
  rcases pairChoice_mem_pi_card_eq_one_or_two hF p with hone | htwo
  · exact exists_pairChoice_mem_pi_eq_singleton_of_card_eq_one hF hone
  · have hfull : F p.1 p.2 = collisionPairEvents (q := q) p.1 :=
      pairChoice_mem_pi_eq_pairEvents_of_card_eq_two hF htwo
    have heq : y p.1.1.2 = y p.1.1.1 :=
      pairChoice_visible_eq_of_global_cycleConsistent_of_eq_pairEvents
        (G := G) (q := q) (S := S) (y := y)
        (F := fun p : S => F p.1 p.2) hglobal hfull
    exact False.elim (hneq heq)

/-- In a cycle-consistent triangle, the direct edge label is the sum of the
two labels along the path through the middle vertex.  This is the labelled-walk
form of the triangle equation used in the remaining non-all-equal local
coefficient calculation. -/
theorem collisionSubfamilyCycleConsistent_triangle_label_eq_add
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} {y : Fin q → G} {T : Finset (CollisionEvent q)}
    {i j k : Fin q} {eij ejk eik : CollisionEvent q}
    (hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T)
    (heij : eij ∈ T) (hejk : ejk ∈ T) (heik : eik ∈ T)
    (hij_l : collisionEventLeft eij = i) (hij_r : collisionEventRight eij = j)
    (hjk_l : collisionEventLeft ejk = j) (hjk_r : collisionEventRight ejk = k)
    (hik_l : collisionEventLeft eik = i) (hik_r : collisionEventRight eik = k) :
    collisionEventLabel y eik = collisionEventLabel y eij + collisionEventLabel y ejk := by
  have hstep_ij : collisionSubfamilyStepLabel (G := G) (q := q) y T i j
      (collisionEventLabel y eij) :=
    ⟨eij, heij, Or.inl ⟨hij_l, hij_r, rfl⟩⟩
  have hstep_jk : collisionSubfamilyStepLabel (G := G) (q := q) y T j k
      (collisionEventLabel y ejk) :=
    ⟨ejk, hejk, Or.inl ⟨hjk_l, hjk_r, rfl⟩⟩
  have hstep_ik : collisionSubfamilyStepLabel (G := G) (q := q) y T i k
      (collisionEventLabel y eik) :=
    ⟨eik, heik, Or.inl ⟨hik_l, hik_r, rfl⟩⟩
  have hpath : collisionSubfamilyLabelReach (G := G) (q := q) y T i k
      (collisionEventLabel y eij + collisionEventLabel y ejk) := by
    simpa [zero_add] using
      (collisionSubfamilyLabelReach.tail
        (collisionSubfamilyLabelReach.tail
          (collisionSubfamilyLabelReach.refl (y := y) (T := T) i) hstep_ij)
        hstep_jk)
  have hdirect : collisionSubfamilyLabelReach (G := G) (q := q) y T i k
      (collisionEventLabel y eik) := by
    simpa [zero_add] using
      (collisionSubfamilyLabelReach.tail
        (collisionSubfamilyLabelReach.refl (y := y) (T := T) i) hstep_ik)
  exact collisionSubfamilyLabelReach_label_unique (G := G) (q := q) hcyc hdirect hpath

/-- For an ordered visible triangle with three unequal visible outputs, the
triangle label equation allows only the two constant singleton-kind
assignments: all hidden or all shifted. -/
theorem triangle_singletonKinds_all_hidden_or_all_shifted_of_pairwise_visible_ne
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hij_ne : y j ≠ y i) (hjk_ne : y k ≠ y j) (hik_ne : y k ≠ y i)
    {kij kjk kik : CollisionKind}
    (hlabel : collisionEventLabel y (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kik) =
        collisionEventLabel y (pairIndexOfNe i j (ne_of_lt hij), kij) +
          collisionEventLabel y (pairIndexOfNe j k (ne_of_lt hjk), kjk)) :
    (kij = CollisionKind.hidden ∧ kjk = CollisionKind.hidden ∧ kik = CollisionKind.hidden) ∨
      (kij = CollisionKind.shifted ∧ kjk = CollisionKind.shifted ∧
        kik = CollisionKind.shifted) := by
  have hik : i < k := hij.trans hjk
  have lij_h : collisionEventLabel y
      (pairIndexOfNe i j (ne_of_lt hij), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have ljk_h : collisionEventLabel y
      (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have lik_h : collisionEventLabel y
      (pairIndexOfNe i k (ne_of_lt hik), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have lij_s : collisionEventLabel y
      (pairIndexOfNe i j (ne_of_lt hij), CollisionKind.shifted) = y j - y i := by
    simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft, collisionEventRight]
  have ljk_s : collisionEventLabel y
      (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.shifted) = y k - y j := by
    simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft, collisionEventRight]
  have lik_s : collisionEventLabel y
      (pairIndexOfNe i k (ne_of_lt hik), CollisionKind.shifted) = y k - y i := by
    simp [pairIndexOfNe, hik, collisionEventLabel, collisionEventLeft, collisionEventRight]
  cases kij <;> cases kjk <;> cases kik
  · exact Or.inl ⟨rfl, rfl, rfl⟩
  · rw [lik_s, lij_h, ljk_h] at hlabel
    simp at hlabel
    exact False.elim (hik_ne (sub_eq_zero.mp hlabel))
  · rw [lik_h, lij_h, ljk_s] at hlabel
    simp at hlabel
    exact False.elim (hjk_ne (sub_eq_zero.mp hlabel.symm))
  · rw [lik_s, lij_h, ljk_s] at hlabel
    have h : y j - y i = 0 := by
      calc
        y j - y i = (y k - y i) - (y k - y j) := by abel
        _ = 0 := by rw [hlabel]; abel
    exact False.elim (hij_ne (sub_eq_zero.mp h))
  · rw [lik_h, lij_s, ljk_h] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel.symm))
  · rw [lik_s, lij_s, ljk_h] at hlabel
    have h : y k - y j = 0 := by
      calc
        y k - y j = (y k - y i) - (y j - y i) := by abel
        _ = 0 := by rw [hlabel]; abel
    exact False.elim (hjk_ne (sub_eq_zero.mp h))
  · rw [lik_h, lij_s, ljk_s] at hlabel
    have h : y k - y i = 0 := by
      calc
        y k - y i = (y j - y i) + (y k - y j) := by abel
        _ = 0 := by rw [← hlabel]
    exact False.elim (hik_ne (sub_eq_zero.mp h))
  · exact Or.inr ⟨rfl, rfl, rfl⟩

/-- The all-hidden singleton triangle is one of the two cycle-consistent
survivors in the all-distinct local rank-two triangle calculation. -/
theorem collisionSubfamilyCycleConsistent_orderedTriangle_allHidden
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
      ({(pairIndexOfNe i j (ne_of_lt hij), CollisionKind.hidden),
        (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.hidden),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), CollisionKind.hidden)} :
        Finset (CollisionEvent q)) := by
  rw [← collisionSubfamilyConsistent_iff_cycleConsistent]
  refine ⟨fun _ => 0, ?_⟩
  intro e he
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl <;>
    (unfold collisionEventEquation; simp [collisionEventLabel])

/-- The all-shifted singleton triangle is the other cycle-consistent survivor
in the all-distinct local rank-two triangle calculation. -/
theorem collisionSubfamilyCycleConsistent_orderedTriangle_allShifted
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
      ({(pairIndexOfNe i j (ne_of_lt hij), CollisionKind.shifted),
        (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.shifted),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), CollisionKind.shifted)} :
        Finset (CollisionEvent q)) := by
  rw [← collisionSubfamilyConsistent_iff_cycleConsistent]
  refine ⟨fun t => -y t, ?_⟩
  intro e he
  have hik : i < k := hij.trans hjk
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · unfold collisionEventEquation
    simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft, collisionEventRight]
    abel
  · unfold collisionEventEquation
    simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft, collisionEventRight]
    abel
  · unfold collisionEventEquation
    simp [pairIndexOfNe, hik, collisionEventLabel, collisionEventLeft, collisionEventRight]
    abel

/-- In an all-distinct ordered visible triangle, every globally
cycle-consistent pair-choice summand chooses a singleton on each of the three
internal query pairs.  This is the edge-pruning step packaged at triangle
granularity. -/
theorem orderedTriangle_pairChoice_allSingletons_of_pairwise_visible_ne
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hij_ne : y j ≠ y i) (hjk_ne : y k ≠ y j) (hik_ne : y k ≠ y i)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    ∃ kij kjk kik : CollisionKind,
      F (pairIndexOfNe i j (ne_of_lt hij)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i j (ne_of_lt hij), kij)} ∧
      F (pairIndexOfNe j k (ne_of_lt hjk)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe j k (ne_of_lt hjk), kjk)} ∧
      F (pairIndexOfNe i k (ne_of_lt (hij.trans hjk))) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kik)} := by
  let pijS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i j (ne_of_lt hij), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pjkS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe j k (ne_of_lt hjk), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pikS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), by
      rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  have hij_edge : y pijS.1.1.2 ≠ y pijS.1.1.1 := by
    simpa [pijS, pairIndexOfNe, hij] using hij_ne
  have hjk_edge : y pjkS.1.1.2 ≠ y pjkS.1.1.1 := by
    simpa [pjkS, pairIndexOfNe, hjk] using hjk_ne
  have pik_edge : y pikS.1.1.2 ≠ y pikS.1.1.1 := by
    simpa [pikS, pairIndexOfNe, hij.trans hjk] using hik_ne
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pijS) hij_edge with ⟨kij, hkij⟩
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pjkS) hjk_edge with ⟨kjk, hkjk⟩
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pikS) pik_edge with ⟨kik, hkik⟩
  refine ⟨kij, kjk, kik, ?_, ?_, ?_⟩
  · simpa [pijS] using hkij
  · simpa [pjkS] using hkjk
  · simpa [pikS] using hkik

/-- In an all-distinct ordered visible triangle, the globally cycle-consistent
summands are not just singleton on each edge: the three singleton kinds are
forced to be collectively all hidden or collectively all shifted. -/
theorem orderedTriangle_pairChoice_allHidden_or_allShifted_of_pairwise_visible_ne
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hij_ne : y j ≠ y i) (hjk_ne : y k ≠ y j) (hik_ne : y k ≠ y i)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    (F (pairIndexOfNe i j (ne_of_lt hij)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i j (ne_of_lt hij), CollisionKind.hidden)} ∧
      F (pairIndexOfNe j k (ne_of_lt hjk)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.hidden)} ∧
      F (pairIndexOfNe i k (ne_of_lt (hij.trans hjk))) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), CollisionKind.hidden)}) ∨
    (F (pairIndexOfNe i j (ne_of_lt hij)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i j (ne_of_lt hij), CollisionKind.shifted)} ∧
      F (pairIndexOfNe j k (ne_of_lt hjk)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.shifted)} ∧
      F (pairIndexOfNe i k (ne_of_lt (hij.trans hjk))) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), CollisionKind.shifted)}) := by
  let pijS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i j (ne_of_lt hij), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pjkS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe j k (ne_of_lt hjk), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pikS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), by
      rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  rcases orderedTriangle_pairChoice_allSingletons_of_pairwise_visible_ne
      (G := G) (q := q) y hij hjk hij_ne hjk_ne hik_ne hF hglobal with
    ⟨kij, kjk, kik, hkij, hkjk, hkik⟩
  have hkij' : F pijS.1 pijS.2 = {(pijS.1, kij)} := by
    simpa [pijS] using hkij
  have hkjk' : F pjkS.1 pjkS.2 = {(pjkS.1, kjk)} := by
    simpa [pjkS] using hkjk
  have hkik' : F pikS.1 pikS.2 = {(pikS.1, kik)} := by
    simpa [pikS] using hkik
  let U := collisionSubfamilyPairChoiceUnion
    (S := queryPairSet ({i, j, k} : Finset (Fin q)))
    (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2)
  have heij_mem : (pijS.1, kij) ∈ F pijS.1 pijS.2 := by
    rw [hkij']; simp
  have hejk_mem : (pjkS.1, kjk) ∈ F pjkS.1 pjkS.2 := by
    rw [hkjk']; simp
  have heik_mem : (pikS.1, kik) ∈ F pikS.1 pikS.2 := by
    rw [hkik']; simp
  have heij : (pijS.1, kij) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pijS, Finset.mem_attach _ _, heij_mem⟩
  have hejk : (pjkS.1, kjk) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pjkS, Finset.mem_attach _ _, hejk_mem⟩
  have heik : (pikS.1, kik) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pikS, Finset.mem_attach _ _, heik_mem⟩
  have hlabel : collisionEventLabel y
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kik) =
      collisionEventLabel y (pairIndexOfNe i j (ne_of_lt hij), kij) +
        collisionEventLabel y (pairIndexOfNe j k (ne_of_lt hjk), kjk) := by
    have hraw := collisionSubfamilyCycleConsistent_triangle_label_eq_add
      (G := G) (q := q) (y := y) (T := U)
      (i := i) (j := j) (k := k)
      (eij := (pijS.1, kij)) (ejk := (pjkS.1, kjk)) (eik := (pikS.1, kik))
      hglobal heij hejk heik
      (by simp [pijS, pairIndexOfNe, hij, collisionEventLeft])
      (by simp [pijS, pairIndexOfNe, hij, collisionEventRight])
      (by simp [pjkS, pairIndexOfNe, hjk, collisionEventLeft])
      (by simp [pjkS, pairIndexOfNe, hjk, collisionEventRight])
      (by simp [pikS, pairIndexOfNe, hij.trans hjk, collisionEventLeft])
      (by simp [pikS, pairIndexOfNe, hij.trans hjk, collisionEventRight])
    simpa [pijS, pjkS, pikS] using hraw
  rcases triangle_singletonKinds_all_hidden_or_all_shifted_of_pairwise_visible_ne
      (G := G) (q := q) y hij hjk hij_ne hjk_ne hik_ne hlabel with hhh | hss
  · rcases hhh with ⟨rfl, rfl, rfl⟩
    exact Or.inl ⟨hkij, hkjk, hkik⟩
  · rcases hss with ⟨rfl, rfl, rfl⟩
    exact Or.inr ⟨hkij, hkjk, hkik⟩

/-- Function-level form of the all-distinct ordered-triangle classification:
any globally cycle-consistent summand is exactly the all-hidden local-choice
function or exactly the all-shifted local-choice function on the triangle
support. -/
theorem orderedTriangle_pairChoice_eq_allHidden_or_allShifted_of_pairwise_visible_ne
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hij_ne : y j ≠ y i) (hjk_ne : y k ≠ y j) (hik_ne : y k ≠ y i)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    F = (fun p _hp => ({(p, CollisionKind.hidden)} : Finset (CollisionEvent q))) ∨
      F = (fun p _hp => ({(p, CollisionKind.shifted)} : Finset (CollisionEvent q))) := by
  rcases orderedTriangle_pairChoice_allHidden_or_allShifted_of_pairwise_visible_ne
      (G := G) (q := q) y hij hjk hij_ne hjk_ne hik_ne hF hglobal with hhid | hshift
  · left
    funext p hp
    rw [queryPairSet_orderedTriple hij hjk] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hhid with ⟨hijF, hjkF, hikF⟩
    rcases hp with rfl | rfl | rfl
    · simpa using hijF
    · simpa using hjkF
    · simpa using hikF
  · right
    funext p hp
    rw [queryPairSet_orderedTriple hij hjk] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hshift with ⟨hijF, hjkF, hikF⟩
    rcases hp with rfl | rfl | rfl
    · simpa using hijF
    · simpa using hjkF
    · simpa using hikF

/-- The constant singleton choice function on an ordered triangle is a valid
member of the pair-local product domain. -/
theorem orderedTriangle_singletonChoice_mem_pi
    {q : Nat} {i j k : Fin q} (_hij : i < j) (_hjk : j < k)
    (kind : CollisionKind) :
    (fun (p : PairIndex q) (_hp : p ∈ queryPairSet ({i, j, k} : Finset (Fin q))) =>
      ({(p, kind)} : Finset (CollisionEvent q))) ∈
      (queryPairSet ({i, j, k} : Finset (Fin q))).pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter
          (fun T => T.Nonempty)) := by
  apply Finset.mem_pi.mpr
  intro p hp
  cases kind <;> simp [collisionPairEvents]

/-- The union assembled from a constant singleton choice over an ordered
triangle is exactly the corresponding three-event triangle. -/
theorem orderedTriangle_singletonChoiceUnion_eq
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (kind : CollisionKind) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p => {(p.1, kind)}
    collisionSubfamilyPairChoiceUnion (S := S) F =
      ({(pairIndexOfNe i j (ne_of_lt hij), kind),
        (pairIndexOfNe j k (ne_of_lt hjk), kind),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
        Finset (CollisionEvent q)) := by
  intro S F
  ext e
  constructor
  · intro he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, hp⟩
    have hpS : p.1 ∈ S := p.2
    change p.1 ∈ queryPairSet ({i, j, k} : Finset (Fin q)) at hpS
    rw [queryPairSet_orderedTriple hij hjk] at hpS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpS ⊢
    simp [F] at hp
    rcases hp with rfl
    rcases hpS with hpij | hpjk | hpik
    · left
      exact Prod.ext hpij rfl
    · right
      left
      exact Prod.ext hpjk rfl
    · right
      right
      exact Prod.ext hpik rfl
  · intro he
    unfold collisionSubfamilyPairChoiceUnion
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe i j (ne_of_lt hij), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe i j (ne_of_lt hij) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · simp [F]
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe j k (ne_of_lt hjk), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe j k (ne_of_lt hjk) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · simp [F]
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe i k (ne_of_lt (hij.trans hjk)) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · simp [F]

/-- A singleton-kind ordered triangle has exactly three collision events. -/
theorem orderedTriangle_singletonEventSet_card
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (kind : CollisionKind) :
    ({(pairIndexOfNe i j (ne_of_lt hij), kind),
      (pairIndexOfNe j k (ne_of_lt hjk), kind),
      (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
      Finset (CollisionEvent q)).card = 3 := by
  rw [show ({(pairIndexOfNe i j (ne_of_lt hij), kind),
      (pairIndexOfNe j k (ne_of_lt hjk), kind),
      (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
      Finset (CollisionEvent q)) =
      (queryPairSet ({i, j, k} : Finset (Fin q))).image (fun p => (p, kind)) by
    rw [queryPairSet_orderedTriple hij hjk]
    ext e
    simp]
  rw [Finset.card_image_of_injective]
  · apply queryPairSet_card_eq_three_of_card_eq_three
    rw [Finset.card_eq_three]
    exact ⟨i, j, k, ne_of_lt hij, ne_of_lt (hij.trans hjk), ne_of_lt hjk, rfl⟩
  · intro a b h
    exact congrArg Prod.fst h

/-- Each of the two constant-kind singleton triangle choices contributes
`(-1)^3 = -1` to the local no-rank coefficient. -/
theorem orderedTriangle_singletonChoiceTerm_eq_neg_one
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (kind : CollisionKind) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p => {(p.1, kind)}
    (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) F) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S) F).card
    else
      0) = -1 := by
  cases kind
  · intro S F
    have hU := orderedTriangle_singletonChoiceUnion_eq (q := q) hij hjk CollisionKind.hidden
    change collisionSubfamilyPairChoiceUnion (S := S) F = _ at hU
    rw [hU]
    have hcyc := collisionSubfamilyCycleConsistent_orderedTriangle_allHidden
      (G := G) (q := q) y hij hjk
    have hcard := orderedTriangle_singletonEventSet_card
      (q := q) hij hjk CollisionKind.hidden
    simp [hcyc, hcard]
  · intro S F
    have hU := orderedTriangle_singletonChoiceUnion_eq (q := q) hij hjk CollisionKind.shifted
    change collisionSubfamilyPairChoiceUnion (S := S) F = _ at hU
    rw [hU]
    have hcyc := collisionSubfamilyCycleConsistent_orderedTriangle_allShifted
      (G := G) (q := q) y hij hjk
    have hcard := orderedTriangle_singletonEventSet_card
      (q := q) hij hjk CollisionKind.shifted
    simp [hcyc, hcard]

/-- The all-distinct ordered-triangle no-rank coefficient is exactly `-2`:
all non-surviving pair-local choices have zero summand, and the two survivors
are the all-hidden and all-shifted singleton triangles. -/
theorem rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_pairwise_visible_ne
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hij_ne : y j ≠ y i) (hjk_ne : y k ≠ y j) (hik_ne : y k ≠ y i) :
    rankTwoPairSupportPiUnionCoefficientInt G q y
      (queryPairSet ({i, j, k} : Finset (Fin q))) = -2 := by
  let S := queryPairSet ({i, j, k} : Finset (Fin q))
  let Fh : (p : PairIndex q) → p ∈ S → Finset (CollisionEvent q) :=
    fun p _ => {(p, CollisionKind.hidden)}
  let Fs : (p : PairIndex q) → p ∈ S → Finset (CollisionEvent q) :=
    fun p _ => {(p, CollisionKind.shifted)}
  let P := S.pi (fun p =>
    (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty))
  let term : ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)) → ℤ := fun F =>
    if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S)
        (fun p : S => F p.1 p.2)).card
    else
      0
  change ∑ F ∈ P, term F = -2
  have hFh_mem : Fh ∈ P := by
    dsimp [P, S, Fh]
    exact orderedTriangle_singletonChoice_mem_pi (q := q) hij hjk CollisionKind.hidden
  have hFs_mem : Fs ∈ P := by
    dsimp [P, S, Fs]
    exact orderedTriangle_singletonChoice_mem_pi (q := q) hij hjk CollisionKind.shifted
  have hFh_ne_Fs : Fh ≠ Fs := by
    intro h
    let pij := pairIndexOfNe i j (ne_of_lt hij)
    have hpij : pij ∈ S := by
      dsimp [S]
      rw [queryPairSet_orderedTriple hij hjk]
      simp [pij]
    have hval := congrFun (congrFun h pij) hpij
    have hkind : CollisionKind.hidden = CollisionKind.shifted :=
      congrArg Prod.snd (Finset.singleton_inj.mp hval)
    cases hkind
  have hzero : ∀ F ∈ P,
      F ∉ ({Fh, Fs} :
        Finset ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q))) →
        term F = 0 := by
    intro F hFP hnot
    dsimp [term]
    by_cases hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2))
    · exfalso
      have hclass :=
        orderedTriangle_pairChoice_eq_allHidden_or_allShifted_of_pairwise_visible_ne
          (G := G) (q := q) y hij hjk hij_ne hjk_ne hik_ne
          (by simpa [P, S] using hFP) hglobal
      rcases hclass with hhidden | hshifted
      · apply hnot
        simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        dsimp [Fh, S] at hhidden ⊢
        exact hhidden
      · apply hnot
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        dsimp [Fs, S] at hshifted ⊢
        exact hshifted
    · simp [hglobal]
  have hsum_subset := Finset.sum_subset
    (s₁ := ({Fh, Fs} :
      Finset ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q))))
    (s₂ := P) (f := term) (by
      intro F hF
      simp only [Finset.mem_insert, Finset.mem_singleton] at hF
      rcases hF with rfl | rfl
      · exact hFh_mem
      · exact hFs_mem) hzero
  rw [← hsum_subset]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    have hterm_h : term Fh = -1 := by
      dsimp [term, Fh, S]
      exact orderedTriangle_singletonChoiceTerm_eq_neg_one
        (G := G) (q := q) y hij hjk CollisionKind.hidden
    have hterm_s : term Fs = -1 := by
      dsimp [term, Fs, S]
      exact orderedTriangle_singletonChoiceTerm_eq_neg_one
        (G := G) (q := q) y hij hjk CollisionKind.shifted
    rw [hterm_h, hterm_s]
    norm_num
  · simp [hFh_ne_Fs]

/-- In a one-collision ordered triangle with `y i = y j` and `y k` distinct
from them, the triangle label equation forces the two visibly unequal
singleton edges to use the same hidden/shifted kind.  The equal edge has zero
label for either kind. -/
theorem triangle_singletonKinds_unequal_edges_eq_of_left_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hij_eq : y j = y i) (hjk_ne : y k ≠ y j)
    {kij kjk kik : CollisionKind}
    (hlabel : collisionEventLabel y (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kik) =
        collisionEventLabel y (pairIndexOfNe i j (ne_of_lt hij), kij) +
          collisionEventLabel y (pairIndexOfNe j k (ne_of_lt hjk), kjk)) :
    kjk = kik := by
  have hik : i < k := hij.trans hjk
  have lij_h : collisionEventLabel y
      (pairIndexOfNe i j (ne_of_lt hij), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have lij_s : collisionEventLabel y
      (pairIndexOfNe i j (ne_of_lt hij), CollisionKind.shifted) = 0 := by
    simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft, collisionEventRight,
      hij_eq]
  have ljk_h : collisionEventLabel y
      (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have lik_h : collisionEventLabel y
      (pairIndexOfNe i k (ne_of_lt hik), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have ljk_s : collisionEventLabel y
      (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.shifted) = y k - y j := by
    simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft, collisionEventRight]
  have lik_s : collisionEventLabel y
      (pairIndexOfNe i k (ne_of_lt hik), CollisionKind.shifted) = y k - y j := by
    simp [pairIndexOfNe, hik, collisionEventLabel, collisionEventLeft, collisionEventRight,
      hij_eq]
  cases kij <;> cases kjk <;> cases kik
  · rfl
  · rw [lik_s, lij_h, ljk_h] at hlabel
    simp at hlabel
    exact False.elim (hjk_ne (sub_eq_zero.mp hlabel))
  · rw [lik_h, lij_h, ljk_s] at hlabel
    simp at hlabel
    exact False.elim (hjk_ne (sub_eq_zero.mp hlabel.symm))
  · rfl
  · rfl
  · rw [lik_s, lij_s, ljk_h] at hlabel
    simp at hlabel
    exact False.elim (hjk_ne (sub_eq_zero.mp hlabel))
  · rw [lik_h, lij_s, ljk_s] at hlabel
    simp at hlabel
    exact False.elim (hjk_ne (sub_eq_zero.mp hlabel.symm))
  · rfl

/-- In a one-collision ordered triangle with `y j = y k` and `y i` distinct
from them, the triangle label equation forces the two visibly unequal
singleton edges to use the same hidden/shifted kind.  The equal edge has zero
label for either kind. -/
theorem triangle_singletonKinds_unequal_edges_eq_of_right_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hjk_eq : y k = y j) (hij_ne : y j ≠ y i)
    {kij kjk kik : CollisionKind}
    (hlabel : collisionEventLabel y (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kik) =
        collisionEventLabel y (pairIndexOfNe i j (ne_of_lt hij), kij) +
          collisionEventLabel y (pairIndexOfNe j k (ne_of_lt hjk), kjk)) :
    kij = kik := by
  have hik : i < k := hij.trans hjk
  have ljk_h : collisionEventLabel y
      (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have ljk_s : collisionEventLabel y
      (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.shifted) = 0 := by
    simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft, collisionEventRight,
      hjk_eq]
  have lij_h : collisionEventLabel y
      (pairIndexOfNe i j (ne_of_lt hij), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have lik_h : collisionEventLabel y
      (pairIndexOfNe i k (ne_of_lt hik), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have lij_s : collisionEventLabel y
      (pairIndexOfNe i j (ne_of_lt hij), CollisionKind.shifted) = y j - y i := by
    simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft, collisionEventRight]
  have lik_s : collisionEventLabel y
      (pairIndexOfNe i k (ne_of_lt hik), CollisionKind.shifted) = y j - y i := by
    simp [pairIndexOfNe, hik, collisionEventLabel, collisionEventLeft, collisionEventRight,
      hjk_eq]
  cases kij <;> cases kjk <;> cases kik
  · rfl
  · rw [lik_s, lij_h, ljk_h] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel))
  · rfl
  · rw [lik_s, lij_h, ljk_s] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel))
  · rw [lik_h, lij_s, ljk_h] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel.symm))
  · rfl
  · rw [lik_h, lij_s, ljk_s] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel.symm))
  · rfl

/-- In a one-collision ordered triangle with `y i = y k` and `y j` distinct
from them, the triangle label equation forces the two visibly unequal
singleton edges to use the same hidden/shifted kind.  The equal edge has zero
label for either kind. -/
theorem triangle_singletonKinds_unequal_edges_eq_of_outer_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hik_eq : y k = y i) (hij_ne : y j ≠ y i)
    {kij kjk kik : CollisionKind}
    (hlabel : collisionEventLabel y (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kik) =
        collisionEventLabel y (pairIndexOfNe i j (ne_of_lt hij), kij) +
          collisionEventLabel y (pairIndexOfNe j k (ne_of_lt hjk), kjk)) :
    kij = kjk := by
  have hik : i < k := hij.trans hjk
  have lik_h : collisionEventLabel y
      (pairIndexOfNe i k (ne_of_lt hik), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have lik_s : collisionEventLabel y
      (pairIndexOfNe i k (ne_of_lt hik), CollisionKind.shifted) = 0 := by
    simp [pairIndexOfNe, hik, collisionEventLabel, collisionEventLeft, collisionEventRight,
      hik_eq]
  have lij_h : collisionEventLabel y
      (pairIndexOfNe i j (ne_of_lt hij), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have ljk_h : collisionEventLabel y
      (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.hidden) = 0 := by
    simp [collisionEventLabel]
  have lij_s : collisionEventLabel y
      (pairIndexOfNe i j (ne_of_lt hij), CollisionKind.shifted) = y j - y i := by
    simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft, collisionEventRight]
  have ljk_s : collisionEventLabel y
      (pairIndexOfNe j k (ne_of_lt hjk), CollisionKind.shifted) = y i - y j := by
    simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft, collisionEventRight,
      hik_eq]
  cases kij <;> cases kjk <;> cases kik
  · rfl
  · rfl
  · rw [lik_h, lij_h, ljk_s] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel.symm).symm)
  · rw [lik_s, lij_h, ljk_s] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel.symm).symm)
  · rw [lik_h, lij_s, ljk_h] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel.symm))
  · rw [lik_s, lij_s, ljk_h] at hlabel
    simp at hlabel
    exact False.elim (hij_ne (sub_eq_zero.mp hlabel.symm))
  · rfl
  · rfl

/-- One-collision ordered-triangle summand classification.  If `y i = y j`
and `y k` is distinct from this value, then any globally cycle-consistent
pair-choice summand has singleton fibers of the same kind on the two visibly
unequal edges.  The visibly equal edge is intentionally left unconstrained. -/
theorem orderedTriangle_pairChoice_oneCollision_unequalSingletons_sameKind_of_left_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hij_eq : y j = y i) (hjk_ne : y k ≠ y j)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    ∃ kind : CollisionKind,
      F (pairIndexOfNe j k (ne_of_lt hjk)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe j k (ne_of_lt hjk), kind)} ∧
      F (pairIndexOfNe i k (ne_of_lt (hij.trans hjk))) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} := by
  have hik : i < k := hij.trans hjk
  have hik_ne : y k ≠ y i := by
    intro hki
    exact hjk_ne (hki.trans hij_eq.symm)
  let pijS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i j (ne_of_lt hij), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pjkS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe j k (ne_of_lt hjk), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pikS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i k (ne_of_lt hik), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  rcases pairChoice_mem_pi_nonempty hF pijS with ⟨eij, heijF⟩
  have hsub_pij := pairChoice_mem_pi_subset_pairEvents hF pijS
  have heij_pair : eij.1 = pijS.1 :=
    collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub_pij heijF)
  let kij : CollisionKind := eij.2
  have heij_eq : eij = (pijS.1, kij) := by
    cases eij with
    | mk p kind =>
        simp only at heij_pair
        subst p
        rfl
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pjkS) (by
        simpa [pjkS, pairIndexOfNe, hjk] using hjk_ne) with ⟨kjk, hkjk⟩
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pikS) (by
        simpa [pikS, pairIndexOfNe, hik] using hik_ne) with ⟨kik, hkik⟩
  let U := collisionSubfamilyPairChoiceUnion
    (S := queryPairSet ({i, j, k} : Finset (Fin q)))
    (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2)
  have heij_mem : (pijS.1, kij) ∈ F pijS.1 pijS.2 := by
    simpa [heij_eq] using heijF
  have hejk_mem : (pjkS.1, kjk) ∈ F pjkS.1 pjkS.2 := by
    rw [hkjk]
    simp
  have heik_mem : (pikS.1, kik) ∈ F pikS.1 pikS.2 := by
    rw [hkik]
    simp
  have heij : (pijS.1, kij) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pijS, Finset.mem_attach _ _, heij_mem⟩
  have hejk : (pjkS.1, kjk) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pjkS, Finset.mem_attach _ _, hejk_mem⟩
  have heik : (pikS.1, kik) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pikS, Finset.mem_attach _ _, heik_mem⟩
  have hlabel : collisionEventLabel y (pairIndexOfNe i k (ne_of_lt hik), kik) =
        collisionEventLabel y (pairIndexOfNe i j (ne_of_lt hij), kij) +
          collisionEventLabel y (pairIndexOfNe j k (ne_of_lt hjk), kjk) := by
    have hraw := collisionSubfamilyCycleConsistent_triangle_label_eq_add
      (G := G) (q := q) (y := y) (T := U)
      (i := i) (j := j) (k := k)
      (eij := (pijS.1, kij)) (ejk := (pjkS.1, kjk)) (eik := (pikS.1, kik))
      hglobal heij hejk heik
      (by simp [pijS, pairIndexOfNe, hij, collisionEventLeft])
      (by simp [pijS, pairIndexOfNe, hij, collisionEventRight])
      (by simp [pjkS, pairIndexOfNe, hjk, collisionEventLeft])
      (by simp [pjkS, pairIndexOfNe, hjk, collisionEventRight])
      (by simp [pikS, pairIndexOfNe, hik, collisionEventLeft])
      (by simp [pikS, pairIndexOfNe, hik, collisionEventRight])
    simpa [pijS, pjkS, pikS] using hraw
  have hsame : kjk = kik :=
    triangle_singletonKinds_unequal_edges_eq_of_left_visible_eq
      (G := G) (q := q) y hij hjk hij_eq hjk_ne hlabel
  refine ⟨kjk, hkjk, ?_⟩
  simpa [hsame] using hkik

/-- One-collision ordered-triangle summand classification.  If `y j = y k`
and `y i` is distinct from this value, then any globally cycle-consistent
pair-choice summand has singleton fibers of the same kind on the two visibly
unequal edges.  The visibly equal edge is intentionally left unconstrained. -/
theorem orderedTriangle_pairChoice_oneCollision_unequalSingletons_sameKind_of_right_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hjk_eq : y k = y j) (hij_ne : y j ≠ y i)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    ∃ kind : CollisionKind,
      F (pairIndexOfNe i j (ne_of_lt hij)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i j (ne_of_lt hij), kind)} ∧
      F (pairIndexOfNe i k (ne_of_lt (hij.trans hjk))) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} := by
  have hik : i < k := hij.trans hjk
  have hik_ne : y k ≠ y i := by
    intro hki
    exact hij_ne (hjk_eq.symm.trans hki)
  let pijS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i j (ne_of_lt hij), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pjkS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe j k (ne_of_lt hjk), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pikS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i k (ne_of_lt hik), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  rcases pairChoice_mem_pi_nonempty hF pjkS with ⟨ejk, hejkF⟩
  have hsub_pjk := pairChoice_mem_pi_subset_pairEvents hF pjkS
  have hejk_pair : ejk.1 = pjkS.1 :=
    collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub_pjk hejkF)
  let kjk : CollisionKind := ejk.2
  have hejk_eq : ejk = (pjkS.1, kjk) := by
    cases ejk with
    | mk p kind =>
        simp only at hejk_pair
        subst p
        rfl
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pijS) (by
        simpa [pijS, pairIndexOfNe, hij] using hij_ne) with ⟨kij, hkij⟩
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pikS) (by
        simpa [pikS, pairIndexOfNe, hik] using hik_ne) with ⟨kik, hkik⟩
  let U := collisionSubfamilyPairChoiceUnion
    (S := queryPairSet ({i, j, k} : Finset (Fin q)))
    (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2)
  have heij_mem : (pijS.1, kij) ∈ F pijS.1 pijS.2 := by
    rw [hkij]
    simp
  have hejk_mem : (pjkS.1, kjk) ∈ F pjkS.1 pjkS.2 := by
    simpa [hejk_eq] using hejkF
  have heik_mem : (pikS.1, kik) ∈ F pikS.1 pikS.2 := by
    rw [hkik]
    simp
  have heij : (pijS.1, kij) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pijS, Finset.mem_attach _ _, heij_mem⟩
  have hejk : (pjkS.1, kjk) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pjkS, Finset.mem_attach _ _, hejk_mem⟩
  have heik : (pikS.1, kik) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pikS, Finset.mem_attach _ _, heik_mem⟩
  have hlabel : collisionEventLabel y (pairIndexOfNe i k (ne_of_lt hik), kik) =
        collisionEventLabel y (pairIndexOfNe i j (ne_of_lt hij), kij) +
          collisionEventLabel y (pairIndexOfNe j k (ne_of_lt hjk), kjk) := by
    have hraw := collisionSubfamilyCycleConsistent_triangle_label_eq_add
      (G := G) (q := q) (y := y) (T := U)
      (i := i) (j := j) (k := k)
      (eij := (pijS.1, kij)) (ejk := (pjkS.1, kjk)) (eik := (pikS.1, kik))
      hglobal heij hejk heik
      (by simp [pijS, pairIndexOfNe, hij, collisionEventLeft])
      (by simp [pijS, pairIndexOfNe, hij, collisionEventRight])
      (by simp [pjkS, pairIndexOfNe, hjk, collisionEventLeft])
      (by simp [pjkS, pairIndexOfNe, hjk, collisionEventRight])
      (by simp [pikS, pairIndexOfNe, hik, collisionEventLeft])
      (by simp [pikS, pairIndexOfNe, hik, collisionEventRight])
    simpa [pijS, pjkS, pikS] using hraw
  have hsame : kij = kik :=
    triangle_singletonKinds_unequal_edges_eq_of_right_visible_eq
      (G := G) (q := q) y hij hjk hjk_eq hij_ne hlabel
  refine ⟨kij, hkij, ?_⟩
  simpa [hsame] using hkik

/-- One-collision ordered-triangle summand classification.  If `y i = y k`
and `y j` is distinct from this value, then any globally cycle-consistent
pair-choice summand has singleton fibers of the same kind on the two visibly
unequal edges.  The visibly equal edge is intentionally left unconstrained. -/
theorem orderedTriangle_pairChoice_oneCollision_unequalSingletons_sameKind_of_outer_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hik_eq : y k = y i) (hij_ne : y j ≠ y i)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    ∃ kind : CollisionKind,
      F (pairIndexOfNe i j (ne_of_lt hij)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe i j (ne_of_lt hij), kind)} ∧
      F (pairIndexOfNe j k (ne_of_lt hjk)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp) =
        {(pairIndexOfNe j k (ne_of_lt hjk), kind)} := by
  have hik : i < k := hij.trans hjk
  have hjk_ne : y k ≠ y j := by
    intro hkj
    exact hij_ne (hkj.symm.trans hik_eq)
  let pijS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i j (ne_of_lt hij), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pjkS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe j k (ne_of_lt hjk), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  let pikS : queryPairSet ({i, j, k} : Finset (Fin q)) :=
    ⟨pairIndexOfNe i k (ne_of_lt hik), by rw [queryPairSet_orderedTriple hij hjk]; simp⟩
  rcases pairChoice_mem_pi_nonempty hF pikS with ⟨eik, heikF⟩
  have hsub_pik := pairChoice_mem_pi_subset_pairEvents hF pikS
  have heik_pair : eik.1 = pikS.1 :=
    collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hsub_pik heikF)
  let kik : CollisionKind := eik.2
  have heik_eq : eik = (pikS.1, kik) := by
    cases eik with
    | mk p kind =>
        simp only at heik_pair
        subst p
        rfl
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pijS) (by
        simpa [pijS, pairIndexOfNe, hij] using hij_ne) with ⟨kij, hkij⟩
  rcases exists_pairChoice_mem_pi_eq_singleton_of_visible_ne_of_global_cycleConsistent
      (G := G) (q := q) (S := queryPairSet ({i, j, k} : Finset (Fin q)))
      (y := y) (F := F) hF hglobal (p := pjkS) (by
        simpa [pjkS, pairIndexOfNe, hjk] using hjk_ne) with ⟨kjk, hkjk⟩
  let U := collisionSubfamilyPairChoiceUnion
    (S := queryPairSet ({i, j, k} : Finset (Fin q)))
    (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2)
  have heij_mem : (pijS.1, kij) ∈ F pijS.1 pijS.2 := by
    rw [hkij]
    simp
  have hejk_mem : (pjkS.1, kjk) ∈ F pjkS.1 pjkS.2 := by
    rw [hkjk]
    simp
  have heik_mem : (pikS.1, kik) ∈ F pikS.1 pikS.2 := by
    simpa [heik_eq] using heikF
  have heij : (pijS.1, kij) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pijS, Finset.mem_attach _ _, heij_mem⟩
  have hejk : (pjkS.1, kjk) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pjkS, Finset.mem_attach _ _, hejk_mem⟩
  have heik : (pikS.1, kik) ∈ U := by
    unfold U collisionSubfamilyPairChoiceUnion
    exact Finset.mem_biUnion.mpr ⟨pikS, Finset.mem_attach _ _, heik_mem⟩
  have hlabel : collisionEventLabel y (pairIndexOfNe i k (ne_of_lt hik), kik) =
        collisionEventLabel y (pairIndexOfNe i j (ne_of_lt hij), kij) +
          collisionEventLabel y (pairIndexOfNe j k (ne_of_lt hjk), kjk) := by
    have hraw := collisionSubfamilyCycleConsistent_triangle_label_eq_add
      (G := G) (q := q) (y := y) (T := U)
      (i := i) (j := j) (k := k)
      (eij := (pijS.1, kij)) (ejk := (pjkS.1, kjk)) (eik := (pikS.1, kik))
      hglobal heij hejk heik
      (by simp [pijS, pairIndexOfNe, hij, collisionEventLeft])
      (by simp [pijS, pairIndexOfNe, hij, collisionEventRight])
      (by simp [pjkS, pairIndexOfNe, hjk, collisionEventLeft])
      (by simp [pjkS, pairIndexOfNe, hjk, collisionEventRight])
      (by simp [pikS, pairIndexOfNe, hik, collisionEventLeft])
      (by simp [pikS, pairIndexOfNe, hik, collisionEventRight])
    simpa [pijS, pjkS, pikS] using hraw
  have hsame : kij = kjk :=
    triangle_singletonKinds_unequal_edges_eq_of_outer_visible_eq
      (G := G) (q := q) y hij hjk hik_eq hij_ne hlabel
  refine ⟨kij, hkij, ?_⟩
  simpa [hsame] using hkjk

/-- Candidate summand for the one-collision ordered-triangle branch with
`y i = y j`: keep an arbitrary nonempty local choice on the visibly equal
edge `(i,j)`, and choose the same singleton kind on the two visibly unequal
edges `(j,k)` and `(i,k)`. -/
noncomputable def orderedTriangle_oneCollisionChoice {q : Nat} {i j k : Fin q}
    (hij : i < j) (hjk : j < k) (U : Finset (CollisionEvent q))
    (kind : CollisionKind) :
    (p : PairIndex q) →
      p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q) :=
  fun p _hp =>
    if p = pairIndexOfNe i j (ne_of_lt hij) then
      U
    else if p = pairIndexOfNe j k (ne_of_lt hjk) then
      {(p, kind)}
    else
      {(p, kind)}

/-- The one-collision candidate summand is a valid point of the pair-local
product domain whenever the equal-edge local choice is nonempty and pair-local. -/
theorem orderedTriangle_oneCollisionChoice_mem_pi
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    {U : Finset (CollisionEvent q)} {kind : CollisionKind}
    (hU : U ∈ (collisionPairEvents (q := q) (pairIndexOfNe i j (ne_of_lt hij))).powerset.filter
      (fun T => T.Nonempty)) :
    orderedTriangle_oneCollisionChoice hij hjk U kind ∈
      (queryPairSet ({i, j, k} : Finset (Fin q))).pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  apply Finset.mem_pi.mpr
  intro p hp
  rw [queryPairSet_orderedTriple hij hjk] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hpij | hpjk | hpik
  · subst p
    simp [orderedTriangle_oneCollisionChoice, hU]
  · subst p
    cases kind <;>
      simp [orderedTriangle_oneCollisionChoice, hij_jk.symm, collisionPairEvents]
  · subst p
    cases kind <;>
      simp [orderedTriangle_oneCollisionChoice, hij_ik.symm, hjk_ik.symm, collisionPairEvents]

/-- The one-collision candidate summands are cycle-consistent.  For hidden
unequal edges the zero assignment works; for shifted unequal edges the
assignment `a t = - y t` works.  On the visibly equal edge, both hidden and
shifted events have zero label. -/
theorem orderedTriangle_oneCollisionChoice_cycleConsistent
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hij_eq : y j = y i) {U : Finset (CollisionEvent q)}
    (hUsub : U ⊆ collisionPairEvents (q := q) (pairIndexOfNe i j (ne_of_lt hij)))
    (kind : CollisionKind) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) =>
          orderedTriangle_oneCollisionChoice hij hjk U kind p.1 p.2)) := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, _hij_ik, _hjk_ik⟩
  rw [← collisionSubfamilyConsistent_iff_cycleConsistent]
  cases kind
  · refine ⟨fun _ => 0, ?_⟩
    intro e he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, heF⟩
    unfold orderedTriangle_oneCollisionChoice at heF
    by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
    · simp [hpij] at heF
      have hePair := hUsub heF
      have hlabel : collisionEventLabel y e = 0 := by
        have hp_eq := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hePair
        cases e with
        | mk pe ke =>
            cases ke
            · simp [collisionEventLabel]
            · simp only at hp_eq
              subst pe
              simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft,
                collisionEventRight, hij_eq]
      unfold collisionEventEquation
      simp [hlabel]
    · by_cases hpjk : p.1 = pairIndexOfNe j k (ne_of_lt hjk)
      · simp [hpjk, hij_jk.symm] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [collisionEventLabel]
      · simp [hpij, hpjk] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [collisionEventLabel]
  · refine ⟨fun t => -y t, ?_⟩
    intro e he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, heF⟩
    unfold orderedTriangle_oneCollisionChoice at heF
    by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
    · simp [hpij] at heF
      have hePair := hUsub heF
      unfold collisionEventEquation
      have hp_eq := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hePair
      cases e with
      | mk pe ke =>
          cases ke
          · simp only at hp_eq
            subst pe
            simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft,
              collisionEventRight, hij_eq]
          · simp only at hp_eq
            subst pe
            simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft,
              collisionEventRight, hij_eq]
    · by_cases hpjk : p.1 = pairIndexOfNe j k (ne_of_lt hjk)
      · simp [hpjk, hij_jk.symm] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft,
          collisionEventRight]
        abel
      · simp [hpij, hpjk] at heF
        rcases heF with rfl
        have hik : i < k := hij.trans hjk
        have hp_mem :
            p.1 ∈ ({pairIndexOfNe i j (ne_of_lt hij),
                pairIndexOfNe j k (ne_of_lt hjk),
                pairIndexOfNe i k (ne_of_lt hik)} : Finset (PairIndex q)) := by
          simpa [queryPairSet_orderedTriple hij hjk] using p.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
        rcases hp_mem with hpbad | hpbad | hpik
        · exact False.elim (hpij hpbad)
        · exact False.elim (hpjk hpbad)
        · have hpik_val : p.1 = pairIndexOfNe i k (ne_of_lt hik) := hpik
          unfold collisionEventEquation
          simp [hpik_val, pairIndexOfNe, hik, collisionEventLabel, collisionEventLeft,
            collisionEventRight]
          abel

/-- Reassembling a one-collision candidate gives the equal-edge local choice
plus the two singleton choices on the visibly unequal edges. -/
theorem orderedTriangle_oneCollisionChoiceUnion_eq
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (U : Finset (CollisionEvent q)) (kind : CollisionKind) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionChoice hij hjk U kind p.1 p.2
    collisionSubfamilyPairChoiceUnion (S := S) F =
      (U ∪ ({(pairIndexOfNe j k (ne_of_lt hjk), kind),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
        Finset (CollisionEvent q))) := by
  intro S F
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  ext e
  constructor
  · intro he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, hp⟩
    have hpS : p.1 ∈ S := p.2
    change p.1 ∈ queryPairSet ({i, j, k} : Finset (Fin q)) at hpS
    rw [queryPairSet_orderedTriple hij hjk] at hpS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpS
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    unfold F at hp
    unfold orderedTriangle_oneCollisionChoice at hp
    by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
    · simp [hpij] at hp
      exact Or.inl hp
    · by_cases hpjk : p.1 = pairIndexOfNe j k (ne_of_lt hjk)
      · simp [hpjk, hij_jk.symm] at hp
        exact Or.inr (Or.inl hp)
      · simp [hpij, hpjk] at hp
        rcases hp with rfl
        rcases hpS with hpbad | hpbad | hpik
        · exact False.elim (hpij hpbad)
        · exact False.elim (hpjk hpbad)
        · exact Or.inr (Or.inr (Prod.ext hpik rfl))
  · intro he
    unfold collisionSubfamilyPairChoiceUnion
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with hU | hjk_mem | hik_mem
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe i j (ne_of_lt hij), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe i j (ne_of_lt hij) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionChoice
        simp [hU]
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe j k (ne_of_lt hjk), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe j k (ne_of_lt hjk) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionChoice
        simp [hij_jk.symm, hjk_mem]
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), ?_⟩,
          Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe i k (ne_of_lt (hij.trans hjk)) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionChoice
        simp [hij_ik.symm, hjk_ik.symm, hik_mem]

/-- The one-collision candidate has cardinality equal to the equal-edge local
choice plus the two forced singleton choices. -/
theorem orderedTriangle_oneCollisionChoiceUnion_card
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    {U : Finset (CollisionEvent q)} (kind : CollisionKind)
    (hUsub : U ⊆ collisionPairEvents (q := q) (pairIndexOfNe i j (ne_of_lt hij))) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionChoice hij hjk U kind p.1 p.2
    (collisionSubfamilyPairChoiceUnion (S := S) F).card = U.card + 2 := by
  intro S F
  rw [orderedTriangle_oneCollisionChoiceUnion_eq (q := q) hij hjk U kind]
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  have hdisjU : Disjoint U ({(pairIndexOfNe j k (ne_of_lt hjk), kind),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
        Finset (CollisionEvent q)) := by
    rw [Finset.disjoint_left]
    intro e heU heS
    have hePair := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hUsub heU)
    simp only [Finset.mem_insert, Finset.mem_singleton] at heS
    rcases heS with rfl | rfl
    · exact hij_jk hePair.symm
    · exact hij_ik hePair.symm
  rw [Finset.card_union_of_disjoint hdisjU]
  have htwo : ({(pairIndexOfNe j k (ne_of_lt hjk), kind),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
        Finset (CollisionEvent q)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp [hjk_ik]
  rw [htwo]

/-- Each one-collision candidate contributes the alternating sign attached to
the arbitrary equal-edge local fiber.  The two visibly unequal singleton edges
contribute \((-1)^2=1\). -/
theorem orderedTriangle_oneCollisionChoiceTerm_eq_neg_one_pow_card
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hij_eq : y j = y i) {U : Finset (CollisionEvent q)} {kind : CollisionKind}
    (hU : U ∈ (collisionPairEvents (q := q) (pairIndexOfNe i j (ne_of_lt hij))).powerset.filter
      (fun T => T.Nonempty)) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionChoice hij hjk U kind p.1 p.2
    (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) F) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S) F).card
    else
      0) = (-1 : ℤ) ^ U.card := by
  intro S F
  have hUsub : U ⊆ collisionPairEvents (q := q) (pairIndexOfNe i j (ne_of_lt hij)) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
  have hcyc := orderedTriangle_oneCollisionChoice_cycleConsistent (G := G) (q := q) y
    hij hjk hij_eq (U := U) hUsub kind
  have hcard := orderedTriangle_oneCollisionChoiceUnion_card
    (q := q) hij hjk (U := U) kind hUsub
  change collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := S) F) at hcyc
  change (collisionSubfamilyPairChoiceUnion (S := S) F).card = U.card + 2 at hcard
  rw [if_pos hcyc, hcard, pow_add]
  norm_num

/-- Summing the canonical one-collision candidates over the remaining
equal-edge local fiber and the two possible unequal-edge singleton kinds gives
the expected local triangle contribution `-2`. -/
theorem orderedTriangle_oneCollisionCandidateTermSum_eq_neg_two
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hij_eq : y j = y i) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let A := (collisionPairEvents (q := q) (pairIndexOfNe i j (ne_of_lt hij))).powerset.filter
      (fun T => T.Nonempty)
    ∑ U ∈ A, ∑ kind : CollisionKind,
      (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
          (collisionSubfamilyPairChoiceUnion (S := S)
            (fun p : S => orderedTriangle_oneCollisionChoice hij hjk U kind p.1 p.2)) then
        (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S)
            (fun p : S => orderedTriangle_oneCollisionChoice hij hjk U kind p.1 p.2)).card
      else
        0) = -2 := by
  intro S A
  trans ∑ U ∈ A, ∑ _kind : CollisionKind, (-1 : ℤ) ^ U.card
  · apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro kind _hkind
    exact orderedTriangle_oneCollisionChoiceTerm_eq_neg_one_pow_card
      (G := G) (q := q) y hij hjk hij_eq (U := U) (kind := kind) hU
  · simp_rw [show ∀ n : Nat, (∑ _kind : CollisionKind, (-1 : ℤ) ^ n) =
        2 * ((-1 : ℤ) ^ n) from by
      intro n
      rw [Finset.sum_const]
      simp [collisionKind_card]]
    rw [← Finset.mul_sum]
    dsimp [A]
    rw [collisionPairEvents_localNonemptyPowersetAlternatingCard]
    norm_num

/-- In the one-collision ordered-triangle branch, every globally consistent
pair-choice summand is one of the canonical candidates: the arbitrary local
fiber on the visibly equal edge, together with a common singleton kind on the
two visibly unequal edges. -/
theorem orderedTriangle_pairChoice_eq_oneCollisionChoice_of_left_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hij_eq : y j = y i) (hjk_ne : y k ≠ y j)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    ∃ kind : CollisionKind,
      F = orderedTriangle_oneCollisionChoice hij hjk
        (F (pairIndexOfNe i j (ne_of_lt hij)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp)) kind := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  rcases orderedTriangle_pairChoice_oneCollision_unequalSingletons_sameKind_of_left_visible_eq
      (G := G) (q := q) y hij hjk hij_eq hjk_ne hF hglobal with ⟨kind, hkjk, hik⟩
  refine ⟨kind, ?_⟩
  funext p hp
  by_cases hpij : p = pairIndexOfNe i j (ne_of_lt hij)
  · subst p
    simp [orderedTriangle_oneCollisionChoice]
  · by_cases hpjk : p = pairIndexOfNe j k (ne_of_lt hjk)
    · subst p
      simpa [orderedTriangle_oneCollisionChoice, hij_jk.symm] using hkjk
    · have hp_mem : p ∈ ({pairIndexOfNe i j (ne_of_lt hij),
          pairIndexOfNe j k (ne_of_lt hjk),
          pairIndexOfNe i k (ne_of_lt (hij.trans hjk))} : Finset (PairIndex q)) := by
        simpa [queryPairSet_orderedTriple hij hjk] using hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      rcases hp_mem with hpbad | hpbad | hpik
      · exact False.elim (hpij hpbad)
      · exact False.elim (hpjk hpbad)
      · subst p
        simpa [orderedTriangle_oneCollisionChoice, hij_ik.symm, hjk_ik.symm] using hik

/-- The one-collision ordered-triangle no-rank coefficient is exactly `-2`.
The visibly equal edge contributes its full pair-local alternating sum, while
the two visibly unequal edges force a common singleton kind. -/
theorem rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_left_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hij_eq : y j = y i) (hjk_ne : y k ≠ y j) :
    rankTwoPairSupportPiUnionCoefficientInt G q y
      (queryPairSet ({i, j, k} : Finset (Fin q))) = -2 := by
  let S := queryPairSet ({i, j, k} : Finset (Fin q))
  let A := (collisionPairEvents (q := q) (pairIndexOfNe i j (ne_of_lt hij))).powerset.filter
      (fun T => T.Nonempty)
  let P := S.pi (fun p =>
    (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty))
  let term : ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)) → ℤ := fun F =>
    if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S)
        (fun p : S => F p.1 p.2)).card
    else
      0
  let C : Finset ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)) :=
    A.biUnion fun U => (Finset.univ : Finset CollisionKind).image fun kind =>
      orderedTriangle_oneCollisionChoice hij hjk U kind
  change ∑ F ∈ P, term F = -2
  have hC_subset_P : C ⊆ P := by
    intro F hF
    dsimp [C] at hF
    simp only [Finset.mem_biUnion] at hF
    rcases hF with ⟨U, hU, hFimg⟩
    rcases Finset.mem_image.mp hFimg with ⟨kind, _hkind, hEq⟩
    subst F
    dsimp [P, S]
    exact orderedTriangle_oneCollisionChoice_mem_pi (q := q) hij hjk
      (U := U) (kind := kind) hU
  have hzero : ∀ F ∈ P, F ∉ C → term F = 0 := by
    intro F hFP hnot
    dsimp [term]
    by_cases hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2))
    · exfalso
      have hclass := orderedTriangle_pairChoice_eq_oneCollisionChoice_of_left_visible_eq
        (G := G) (q := q) y hij hjk hij_eq hjk_ne
        (F := F) (by simpa [P, S] using hFP) hglobal
      rcases hclass with ⟨kind, hEq⟩
      let pij := pairIndexOfNe i j (ne_of_lt hij)
      have hpij : pij ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pij]
      let U := F pij hpij
      have hU : U ∈ A := by
        have hlocal := Finset.mem_pi.mp hFP pij hpij
        simpa [A, U] using hlocal
      apply hnot
      dsimp [C]
      exact Finset.mem_biUnion.mpr ⟨U, hU,
        Finset.mem_image.mpr ⟨kind, Finset.mem_univ kind, by
          simpa [U, pij] using hEq.symm⟩⟩
    · simp [hglobal]
  have hsum_subset := Finset.sum_subset (s₁ := C) (s₂ := P) (f := term) hC_subset_P hzero
  rw [← hsum_subset]
  have hCsum : (∑ F ∈ C, term F) =
      ∑ U ∈ A, ∑ kind : CollisionKind,
        term (orderedTriangle_oneCollisionChoice hij hjk U kind) := by
    dsimp [C]
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_image]
      intro a _ b _ h
      let pjk := pairIndexOfNe j k (ne_of_lt hjk)
      have hpjk : pjk ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pjk]
      have hval := congrFun (congrFun h pjk) hpjk
      rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, _hij_ik, _hjk_ik⟩
      have hsingleton : ({(pjk, a)} : Finset (CollisionEvent q)) = {(pjk, b)} := by
        simpa [pjk, orderedTriangle_oneCollisionChoice, hij_jk.symm] using hval
      exact congrArg Prod.snd (Finset.singleton_inj.mp hsingleton)
    · intro U _hU U' _hU' hne
      change Disjoint ((Finset.univ : Finset CollisionKind).image
          (fun kind => orderedTriangle_oneCollisionChoice hij hjk U kind))
        ((Finset.univ : Finset CollisionKind).image
          (fun kind => orderedTriangle_oneCollisionChoice hij hjk U' kind))
      rw [Finset.disjoint_left]
      intro F hF hF'
      rcases Finset.mem_image.mp hF with ⟨kind, _hkind, rfl⟩
      rcases Finset.mem_image.mp hF' with ⟨_kind', _hkind', hEq⟩
      let pij := pairIndexOfNe i j (ne_of_lt hij)
      have hpij : pij ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pij]
      have hval := congrFun (congrFun hEq.symm pij) hpij
      have hUeq : U = U' := by
        simpa [pij, orderedTriangle_oneCollisionChoice] using hval
      exact hne hUeq
  rw [hCsum]
  exact orderedTriangle_oneCollisionCandidateTermSum_eq_neg_two
    (G := G) (q := q) y hij hjk hij_eq

/-- Candidate summand for the one-collision ordered-triangle branch with
`y j = y k`: keep an arbitrary nonempty local choice on the visibly equal
edge `(j,k)`, and choose the same singleton kind on the two visibly unequal
edges `(i,j)` and `(i,k)`. -/
noncomputable def orderedTriangle_oneCollisionRightChoice {q : Nat} {i j k : Fin q}
    (hij : i < j) (hjk : j < k) (U : Finset (CollisionEvent q))
    (kind : CollisionKind) :
    (p : PairIndex q) →
      p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q) :=
  fun p _hp =>
    if p = pairIndexOfNe j k (ne_of_lt hjk) then
      U
    else if p = pairIndexOfNe i j (ne_of_lt hij) then
      {(p, kind)}
    else
      {(p, kind)}

/-- The right one-collision candidate summand is a valid point of the
pair-local product domain whenever the equal-edge local choice is nonempty and
pair-local. -/
theorem orderedTriangle_oneCollisionRightChoice_mem_pi
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    {U : Finset (CollisionEvent q)} {kind : CollisionKind}
    (hU : U ∈ (collisionPairEvents (q := q) (pairIndexOfNe j k (ne_of_lt hjk))).powerset.filter
      (fun T => T.Nonempty)) :
    orderedTriangle_oneCollisionRightChoice hij hjk U kind ∈
      (queryPairSet ({i, j, k} : Finset (Fin q))).pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  apply Finset.mem_pi.mpr
  intro p hp
  rw [queryPairSet_orderedTriple hij hjk] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hpij | hpjk | hpik
  · subst p
    cases kind <;>
      simp [orderedTriangle_oneCollisionRightChoice, hij_jk, collisionPairEvents]
  · subst p
    simp [orderedTriangle_oneCollisionRightChoice, hU]
  · subst p
    cases kind <;>
      simp [orderedTriangle_oneCollisionRightChoice, hjk_ik.symm, hij_ik.symm,
        collisionPairEvents]

/-- The right one-collision candidate summands are cycle-consistent. -/
theorem orderedTriangle_oneCollisionRightChoice_cycleConsistent
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hjk_eq : y k = y j) {U : Finset (CollisionEvent q)}
    (hUsub : U ⊆ collisionPairEvents (q := q) (pairIndexOfNe j k (ne_of_lt hjk)))
    (kind : CollisionKind) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) =>
          orderedTriangle_oneCollisionRightChoice hij hjk U kind p.1 p.2)) := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, _hij_ik, hjk_ik⟩
  rw [← collisionSubfamilyConsistent_iff_cycleConsistent]
  cases kind
  · refine ⟨fun _ => 0, ?_⟩
    intro e he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, heF⟩
    unfold orderedTriangle_oneCollisionRightChoice at heF
    by_cases hpjk : p.1 = pairIndexOfNe j k (ne_of_lt hjk)
    · simp [hpjk] at heF
      have hePair := hUsub heF
      have hlabel : collisionEventLabel y e = 0 := by
        have hp_eq := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hePair
        cases e with
        | mk pe ke =>
            cases ke
            · simp [collisionEventLabel]
            · simp only at hp_eq
              subst pe
              simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft,
                collisionEventRight, hjk_eq]
      unfold collisionEventEquation
      simp [hlabel]
    · by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
      · simp [hpij, hij_jk] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [collisionEventLabel]
      · simp [hpjk, hpij] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [collisionEventLabel]
  · refine ⟨fun t => -y t, ?_⟩
    intro e he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, heF⟩
    unfold orderedTriangle_oneCollisionRightChoice at heF
    by_cases hpjk : p.1 = pairIndexOfNe j k (ne_of_lt hjk)
    · simp [hpjk] at heF
      have hePair := hUsub heF
      unfold collisionEventEquation
      have hp_eq := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hePair
      cases e with
      | mk pe ke =>
          cases ke
          · simp only at hp_eq
            subst pe
            simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft,
              collisionEventRight, hjk_eq]
          · simp only at hp_eq
            subst pe
            simp [pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft,
              collisionEventRight, hjk_eq]
    · by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
      · simp [hpij, hij_jk] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft,
          collisionEventRight]
        abel
      · simp [hpjk, hpij] at heF
        rcases heF with rfl
        have hik : i < k := hij.trans hjk
        have hp_mem :
            p.1 ∈ ({pairIndexOfNe i j (ne_of_lt hij),
                pairIndexOfNe j k (ne_of_lt hjk),
                pairIndexOfNe i k (ne_of_lt hik)} : Finset (PairIndex q)) := by
          simpa [queryPairSet_orderedTriple hij hjk] using p.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
        rcases hp_mem with hpbad | hpbad | hpik
        · exact False.elim (hpij hpbad)
        · exact False.elim (hpjk hpbad)
        · have hpik_val : p.1 = pairIndexOfNe i k (ne_of_lt hik) := hpik
          unfold collisionEventEquation
          simp [hpik_val, pairIndexOfNe, hik, collisionEventLabel, collisionEventLeft,
            collisionEventRight, hjk_eq]
          abel

/-- Reassembling a right one-collision candidate gives the equal-edge local
choice plus the two singleton choices on the visibly unequal edges. -/
theorem orderedTriangle_oneCollisionRightChoiceUnion_eq
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (U : Finset (CollisionEvent q)) (kind : CollisionKind) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionRightChoice hij hjk U kind p.1 p.2
    collisionSubfamilyPairChoiceUnion (S := S) F =
      (U ∪ ({(pairIndexOfNe i j (ne_of_lt hij), kind),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
        Finset (CollisionEvent q))) := by
  intro S F
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  ext e
  constructor
  · intro he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, hp⟩
    have hpS : p.1 ∈ S := p.2
    change p.1 ∈ queryPairSet ({i, j, k} : Finset (Fin q)) at hpS
    rw [queryPairSet_orderedTriple hij hjk] at hpS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpS
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    unfold F at hp
    unfold orderedTriangle_oneCollisionRightChoice at hp
    by_cases hpjk : p.1 = pairIndexOfNe j k (ne_of_lt hjk)
    · simp [hpjk] at hp
      exact Or.inl hp
    · by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
      · simp [hpij, hij_jk] at hp
        exact Or.inr (Or.inl hp)
      · simp [hpjk, hpij] at hp
        rcases hp with rfl
        rcases hpS with hpbad | hpbad | hpik
        · exact False.elim (hpij hpbad)
        · exact False.elim (hpjk hpbad)
        · exact Or.inr (Or.inr (Prod.ext hpik rfl))
  · intro he
    unfold collisionSubfamilyPairChoiceUnion
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with hU | hij_mem | hik_mem
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe j k (ne_of_lt hjk), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe j k (ne_of_lt hjk) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionRightChoice
        simp [hU]
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe i j (ne_of_lt hij), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe i j (ne_of_lt hij) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionRightChoice
        simp [hij_jk, hij_mem]
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), ?_⟩,
          Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe i k (ne_of_lt (hij.trans hjk)) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionRightChoice
        simp [hjk_ik.symm, hij_ik.symm, hik_mem]

/-- The right one-collision candidate has cardinality equal to the equal-edge
local choice plus the two forced singleton choices. -/
theorem orderedTriangle_oneCollisionRightChoiceUnion_card
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    {U : Finset (CollisionEvent q)} (kind : CollisionKind)
    (hUsub : U ⊆ collisionPairEvents (q := q) (pairIndexOfNe j k (ne_of_lt hjk))) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionRightChoice hij hjk U kind p.1 p.2
    (collisionSubfamilyPairChoiceUnion (S := S) F).card = U.card + 2 := by
  intro S F
  rw [orderedTriangle_oneCollisionRightChoiceUnion_eq (q := q) hij hjk U kind]
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  have hdisjU : Disjoint U ({(pairIndexOfNe i j (ne_of_lt hij), kind),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
        Finset (CollisionEvent q)) := by
    rw [Finset.disjoint_left]
    intro e heU heS
    have hePair := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hUsub heU)
    simp only [Finset.mem_insert, Finset.mem_singleton] at heS
    rcases heS with rfl | rfl
    · exact hij_jk hePair
    · exact hjk_ik hePair.symm
  rw [Finset.card_union_of_disjoint hdisjU]
  have htwo : ({(pairIndexOfNe i j (ne_of_lt hij), kind),
        (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), kind)} :
        Finset (CollisionEvent q)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp [hij_ik]
  rw [htwo]

/-- Each right one-collision candidate contributes the alternating sign
attached to the arbitrary equal-edge local fiber. -/
theorem orderedTriangle_oneCollisionRightChoiceTerm_eq_neg_one_pow_card
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hjk_eq : y k = y j) {U : Finset (CollisionEvent q)} {kind : CollisionKind}
    (hU : U ∈ (collisionPairEvents (q := q) (pairIndexOfNe j k (ne_of_lt hjk))).powerset.filter
      (fun T => T.Nonempty)) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionRightChoice hij hjk U kind p.1 p.2
    (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) F) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S) F).card
    else
      0) = (-1 : ℤ) ^ U.card := by
  intro S F
  have hUsub : U ⊆ collisionPairEvents (q := q) (pairIndexOfNe j k (ne_of_lt hjk)) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
  have hcyc := orderedTriangle_oneCollisionRightChoice_cycleConsistent (G := G) (q := q) y
    hij hjk hjk_eq (U := U) hUsub kind
  have hcard := orderedTriangle_oneCollisionRightChoiceUnion_card
    (q := q) hij hjk (U := U) kind hUsub
  change collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := S) F) at hcyc
  change (collisionSubfamilyPairChoiceUnion (S := S) F).card = U.card + 2 at hcard
  rw [if_pos hcyc, hcard, pow_add]
  norm_num

/-- Summing the canonical right one-collision candidates gives the local
triangle contribution `-2`. -/
theorem orderedTriangle_oneCollisionRightCandidateTermSum_eq_neg_two
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hjk_eq : y k = y j) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let A := (collisionPairEvents (q := q) (pairIndexOfNe j k (ne_of_lt hjk))).powerset.filter
      (fun T => T.Nonempty)
    ∑ U ∈ A, ∑ kind : CollisionKind,
      (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
          (collisionSubfamilyPairChoiceUnion (S := S)
            (fun p : S => orderedTriangle_oneCollisionRightChoice hij hjk U kind p.1 p.2)) then
        (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S)
            (fun p : S => orderedTriangle_oneCollisionRightChoice hij hjk U kind p.1 p.2)).card
      else
        0) = -2 := by
  intro S A
  trans ∑ U ∈ A, ∑ _kind : CollisionKind, (-1 : ℤ) ^ U.card
  · apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro kind _hkind
    exact orderedTriangle_oneCollisionRightChoiceTerm_eq_neg_one_pow_card
      (G := G) (q := q) y hij hjk hjk_eq (U := U) (kind := kind) hU
  · simp_rw [show ∀ n : Nat, (∑ _kind : CollisionKind, (-1 : ℤ) ^ n) =
        2 * ((-1 : ℤ) ^ n) from by
      intro n
      rw [Finset.sum_const]
      simp [collisionKind_card]]
    rw [← Finset.mul_sum]
    dsimp [A]
    rw [collisionPairEvents_localNonemptyPowersetAlternatingCard]
    norm_num

/-- In the right one-collision branch, every globally consistent pair-choice
summand is one of the canonical right candidates. -/
theorem orderedTriangle_pairChoice_eq_oneCollisionRightChoice_of_right_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hjk_eq : y k = y j) (hij_ne : y j ≠ y i)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    ∃ kind : CollisionKind,
      F = orderedTriangle_oneCollisionRightChoice hij hjk
        (F (pairIndexOfNe j k (ne_of_lt hjk)) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp)) kind := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  rcases orderedTriangle_pairChoice_oneCollision_unequalSingletons_sameKind_of_right_visible_eq
      (G := G) (q := q) y hij hjk hjk_eq hij_ne hF hglobal with ⟨kind, hkij, hik⟩
  refine ⟨kind, ?_⟩
  funext p hp
  by_cases hpjk : p = pairIndexOfNe j k (ne_of_lt hjk)
  · subst p
    simp [orderedTriangle_oneCollisionRightChoice]
  · by_cases hpij : p = pairIndexOfNe i j (ne_of_lt hij)
    · subst p
      simpa [orderedTriangle_oneCollisionRightChoice, hij_jk] using hkij
    · have hp_mem : p ∈ ({pairIndexOfNe i j (ne_of_lt hij),
          pairIndexOfNe j k (ne_of_lt hjk),
          pairIndexOfNe i k (ne_of_lt (hij.trans hjk))} : Finset (PairIndex q)) := by
        simpa [queryPairSet_orderedTriple hij hjk] using hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      rcases hp_mem with hpbad | hpbad | hpik
      · exact False.elim (hpij hpbad)
      · exact False.elim (hpjk hpbad)
      · subst p
        simpa [orderedTriangle_oneCollisionRightChoice, hjk_ik.symm, hij_ik.symm] using hik

/-- The right one-collision ordered-triangle no-rank coefficient is exactly
`-2`. -/
theorem rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_right_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hjk_eq : y k = y j) (hij_ne : y j ≠ y i) :
    rankTwoPairSupportPiUnionCoefficientInt G q y
      (queryPairSet ({i, j, k} : Finset (Fin q))) = -2 := by
  let S := queryPairSet ({i, j, k} : Finset (Fin q))
  let A := (collisionPairEvents (q := q) (pairIndexOfNe j k (ne_of_lt hjk))).powerset.filter
      (fun T => T.Nonempty)
  let P := S.pi (fun p =>
    (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty))
  let term : ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)) → ℤ := fun F =>
    if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S)
        (fun p : S => F p.1 p.2)).card
    else
      0
  let C : Finset ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)) :=
    A.biUnion fun U => (Finset.univ : Finset CollisionKind).image fun kind =>
      orderedTriangle_oneCollisionRightChoice hij hjk U kind
  change ∑ F ∈ P, term F = -2
  have hC_subset_P : C ⊆ P := by
    intro F hF
    dsimp [C] at hF
    simp only [Finset.mem_biUnion] at hF
    rcases hF with ⟨U, hU, hFimg⟩
    rcases Finset.mem_image.mp hFimg with ⟨kind, _hkind, hEq⟩
    subst F
    dsimp [P, S]
    exact orderedTriangle_oneCollisionRightChoice_mem_pi (q := q) hij hjk
      (U := U) (kind := kind) hU
  have hzero : ∀ F ∈ P, F ∉ C → term F = 0 := by
    intro F hFP hnot
    dsimp [term]
    by_cases hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2))
    · exfalso
      have hclass := orderedTriangle_pairChoice_eq_oneCollisionRightChoice_of_right_visible_eq
        (G := G) (q := q) y hij hjk hjk_eq hij_ne
        (F := F) (by simpa [P, S] using hFP) hglobal
      rcases hclass with ⟨kind, hEq⟩
      let pjk := pairIndexOfNe j k (ne_of_lt hjk)
      have hpjk : pjk ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pjk]
      let U := F pjk hpjk
      have hU : U ∈ A := by
        have hlocal := Finset.mem_pi.mp hFP pjk hpjk
        simpa [A, U] using hlocal
      apply hnot
      dsimp [C]
      exact Finset.mem_biUnion.mpr ⟨U, hU,
        Finset.mem_image.mpr ⟨kind, Finset.mem_univ kind, by
          simpa [U, pjk] using hEq.symm⟩⟩
    · simp [hglobal]
  have hsum_subset := Finset.sum_subset (s₁ := C) (s₂ := P) (f := term) hC_subset_P hzero
  rw [← hsum_subset]
  have hCsum : (∑ F ∈ C, term F) =
      ∑ U ∈ A, ∑ kind : CollisionKind,
        term (orderedTriangle_oneCollisionRightChoice hij hjk U kind) := by
    dsimp [C]
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_image]
      intro a _ b _ h
      let pij := pairIndexOfNe i j (ne_of_lt hij)
      have hpij : pij ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pij]
      have hval := congrFun (congrFun h pij) hpij
      rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, _hij_ik, _hjk_ik⟩
      have hsingleton : ({(pij, a)} : Finset (CollisionEvent q)) = {(pij, b)} := by
        simpa [pij, orderedTriangle_oneCollisionRightChoice, hij_jk] using hval
      exact congrArg Prod.snd (Finset.singleton_inj.mp hsingleton)
    · intro U _hU U' _hU' hne
      change Disjoint ((Finset.univ : Finset CollisionKind).image
          (fun kind => orderedTriangle_oneCollisionRightChoice hij hjk U kind))
        ((Finset.univ : Finset CollisionKind).image
          (fun kind => orderedTriangle_oneCollisionRightChoice hij hjk U' kind))
      rw [Finset.disjoint_left]
      intro F hF hF'
      rcases Finset.mem_image.mp hF with ⟨kind, _hkind, rfl⟩
      rcases Finset.mem_image.mp hF' with ⟨_kind', _hkind', hEq⟩
      let pjk := pairIndexOfNe j k (ne_of_lt hjk)
      have hpjk : pjk ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pjk]
      have hval := congrFun (congrFun hEq.symm pjk) hpjk
      have hUeq : U = U' := by
        simpa [pjk, orderedTriangle_oneCollisionRightChoice] using hval
      exact hne hUeq
  rw [hCsum]
  exact orderedTriangle_oneCollisionRightCandidateTermSum_eq_neg_two
    (G := G) (q := q) y hij hjk hjk_eq

/-- Candidate summand for the one-collision ordered-triangle branch with
`y i = y k`: keep an arbitrary nonempty local choice on the visibly equal
edge `(i,k)`, and choose the same singleton kind on the two visibly unequal
edges `(i,j)` and `(j,k)`. -/
noncomputable def orderedTriangle_oneCollisionOuterChoice {q : Nat} {i j k : Fin q}
    (hij : i < j) (hjk : j < k) (U : Finset (CollisionEvent q))
    (kind : CollisionKind) :
    (p : PairIndex q) →
      p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q) :=
  fun p _hp =>
    if p = pairIndexOfNe i k (ne_of_lt (hij.trans hjk)) then
      U
    else if p = pairIndexOfNe i j (ne_of_lt hij) then
      {(p, kind)}
    else
      {(p, kind)}

/-- The outer one-collision candidate summand is a valid point of the
pair-local product domain whenever the equal-edge local choice is nonempty and
pair-local. -/
theorem orderedTriangle_oneCollisionOuterChoice_mem_pi
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    {U : Finset (CollisionEvent q)} {kind : CollisionKind}
    (hU : U ∈ (collisionPairEvents (q := q)
      (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)))).powerset.filter
      (fun T => T.Nonempty)) :
    orderedTriangle_oneCollisionOuterChoice hij hjk U kind ∈
      (queryPairSet ({i, j, k} : Finset (Fin q))).pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  apply Finset.mem_pi.mpr
  intro p hp
  rw [queryPairSet_orderedTriple hij hjk] at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hpij | hpjk | hpik
  · subst p
    cases kind <;>
      simp [orderedTriangle_oneCollisionOuterChoice, hij_ik, collisionPairEvents]
  · subst p
    cases kind <;>
      simp [orderedTriangle_oneCollisionOuterChoice, hjk_ik, hij_jk.symm,
        collisionPairEvents]
  · subst p
    simp [orderedTriangle_oneCollisionOuterChoice, hU]

/-- The outer one-collision candidate summands are cycle-consistent. -/
theorem orderedTriangle_oneCollisionOuterChoice_cycleConsistent
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hik_eq : y k = y i) {U : Finset (CollisionEvent q)}
    (hUsub : U ⊆ collisionPairEvents (q := q)
      (pairIndexOfNe i k (ne_of_lt (hij.trans hjk))))
    (kind : CollisionKind) :
    collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) =>
          orderedTriangle_oneCollisionOuterChoice hij hjk U kind p.1 p.2)) := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  rw [← collisionSubfamilyConsistent_iff_cycleConsistent]
  cases kind
  · refine ⟨fun _ => 0, ?_⟩
    intro e he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, heF⟩
    unfold orderedTriangle_oneCollisionOuterChoice at heF
    by_cases hpik : p.1 = pairIndexOfNe i k (ne_of_lt (hij.trans hjk))
    · simp [hpik] at heF
      have hePair := hUsub heF
      have hlabel : collisionEventLabel y e = 0 := by
        have hp_eq := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hePair
        cases e with
        | mk pe ke =>
            cases ke
            · simp [collisionEventLabel]
            · simp only at hp_eq
              subst pe
              simp [pairIndexOfNe, hij.trans hjk, collisionEventLabel, collisionEventLeft,
                collisionEventRight, hik_eq]
      unfold collisionEventEquation
      simp [hlabel]
    · by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
      · simp [hpij, hij_ik] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [collisionEventLabel]
      · simp [hpik, hpij] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [collisionEventLabel]
  · refine ⟨fun t => -y t, ?_⟩
    intro e he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, heF⟩
    unfold orderedTriangle_oneCollisionOuterChoice at heF
    by_cases hpik : p.1 = pairIndexOfNe i k (ne_of_lt (hij.trans hjk))
    · simp [hpik] at heF
      have hePair := hUsub heF
      unfold collisionEventEquation
      have hp_eq := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) hePair
      cases e with
      | mk pe ke =>
          cases ke
          · simp only at hp_eq
            subst pe
            simp [pairIndexOfNe, hij.trans hjk, collisionEventLabel, collisionEventLeft,
              collisionEventRight, hik_eq]
          · simp only at hp_eq
            subst pe
            simp [pairIndexOfNe, hij.trans hjk, collisionEventLabel, collisionEventLeft,
              collisionEventRight, hik_eq]
    · by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
      · simp [hpij, hij_ik] at heF
        rcases heF with rfl
        unfold collisionEventEquation
        simp [pairIndexOfNe, hij, collisionEventLabel, collisionEventLeft,
          collisionEventRight]
        abel
      · simp [hpik, hpij] at heF
        rcases heF with rfl
        have hik : i < k := hij.trans hjk
        have hp_mem :
            p.1 ∈ ({pairIndexOfNe i j (ne_of_lt hij),
                pairIndexOfNe j k (ne_of_lt hjk),
                pairIndexOfNe i k (ne_of_lt hik)} : Finset (PairIndex q)) := by
          simpa [queryPairSet_orderedTriple hij hjk] using p.2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
        rcases hp_mem with hpbad | hpjk | hpbad
        · exact False.elim (hpij hpbad)
        · have hpjk_val : p.1 = pairIndexOfNe j k (ne_of_lt hjk) := hpjk
          unfold collisionEventEquation
          simp [hpjk_val, pairIndexOfNe, hjk, collisionEventLabel, collisionEventLeft,
            collisionEventRight, hik_eq]
          abel
        · exact False.elim (hpik hpbad)

/-- Reassembling an outer one-collision candidate gives the equal-edge local
choice plus the two singleton choices on the visibly unequal edges. -/
theorem orderedTriangle_oneCollisionOuterChoiceUnion_eq
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (U : Finset (CollisionEvent q)) (kind : CollisionKind) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionOuterChoice hij hjk U kind p.1 p.2
    collisionSubfamilyPairChoiceUnion (S := S) F =
      (U ∪ ({(pairIndexOfNe i j (ne_of_lt hij), kind),
        (pairIndexOfNe j k (ne_of_lt hjk), kind)} :
        Finset (CollisionEvent q))) := by
  intro S F
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  ext e
  constructor
  · intro he
    unfold collisionSubfamilyPairChoiceUnion at he
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and] at he
    rcases he with ⟨p, hp⟩
    have hpS : p.1 ∈ S := p.2
    change p.1 ∈ queryPairSet ({i, j, k} : Finset (Fin q)) at hpS
    rw [queryPairSet_orderedTriple hij hjk] at hpS
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpS
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    unfold F at hp
    unfold orderedTriangle_oneCollisionOuterChoice at hp
    by_cases hpik : p.1 = pairIndexOfNe i k (ne_of_lt (hij.trans hjk))
    · simp [hpik] at hp
      exact Or.inl hp
    · by_cases hpij : p.1 = pairIndexOfNe i j (ne_of_lt hij)
      · simp [hpij, hij_ik] at hp
        exact Or.inr (Or.inl hp)
      · simp [hpik, hpij] at hp
        rcases hp with rfl
        rcases hpS with hpbad | hpjk | hpbad
        · exact False.elim (hpij hpbad)
        · exact Or.inr (Or.inr (Prod.ext hpjk rfl))
        · exact False.elim (hpik hpbad)
  · intro he
    unfold collisionSubfamilyPairChoiceUnion
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with hU | hij_mem | hjk_mem
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe i k (ne_of_lt (hij.trans hjk)), ?_⟩,
          Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe i k (ne_of_lt (hij.trans hjk)) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionOuterChoice
        simp [hU]
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe i j (ne_of_lt hij), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe i j (ne_of_lt hij) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionOuterChoice
        simp [hij_ik, hij_mem]
    · refine Finset.mem_biUnion.mpr
        ⟨⟨pairIndexOfNe j k (ne_of_lt hjk), ?_⟩, Finset.mem_attach _ _, ?_⟩
      · change pairIndexOfNe j k (ne_of_lt hjk) ∈
          queryPairSet ({i, j, k} : Finset (Fin q))
        rw [queryPairSet_orderedTriple hij hjk]
        simp
      · unfold F orderedTriangle_oneCollisionOuterChoice
        simp [hjk_ik, hij_jk.symm, hjk_mem]

/-- The outer one-collision candidate has cardinality equal to the equal-edge
local choice plus the two forced singleton choices. -/
theorem orderedTriangle_oneCollisionOuterChoiceUnion_card
    {q : Nat} {i j k : Fin q} (hij : i < j) (hjk : j < k)
    {U : Finset (CollisionEvent q)} (kind : CollisionKind)
    (hUsub : U ⊆ collisionPairEvents (q := q)
      (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)))) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionOuterChoice hij hjk U kind p.1 p.2
    (collisionSubfamilyPairChoiceUnion (S := S) F).card = U.card + 2 := by
  intro S F
  rw [orderedTriangle_oneCollisionOuterChoiceUnion_eq (q := q) hij hjk U kind]
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  have hdisjU : Disjoint U ({(pairIndexOfNe i j (ne_of_lt hij), kind),
        (pairIndexOfNe j k (ne_of_lt hjk), kind)} :
        Finset (CollisionEvent q)) := by
    rw [Finset.disjoint_left]
    intro e heU heS
    have hePair := collisionEvent_pairIndex_eq_of_mem_collisionPairEvents (q := q) (hUsub heU)
    simp only [Finset.mem_insert, Finset.mem_singleton] at heS
    rcases heS with rfl | rfl
    · exact hij_ik hePair
    · exact hjk_ik hePair
  rw [Finset.card_union_of_disjoint hdisjU]
  have htwo : ({(pairIndexOfNe i j (ne_of_lt hij), kind),
        (pairIndexOfNe j k (ne_of_lt hjk), kind)} :
        Finset (CollisionEvent q)).card = 2 := by
    rw [Finset.card_insert_of_notMem]
    · simp
    · simp [hij_jk]
  rw [htwo]

/-- Each outer one-collision candidate contributes the alternating sign
attached to the arbitrary equal-edge local fiber. -/
theorem orderedTriangle_oneCollisionOuterChoiceTerm_eq_neg_one_pow_card
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hik_eq : y k = y i) {U : Finset (CollisionEvent q)} {kind : CollisionKind}
    (hU : U ∈ (collisionPairEvents (q := q)
      (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)))).powerset.filter
      (fun T => T.Nonempty)) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let F : (p : S) → Finset (CollisionEvent q) := fun p =>
      orderedTriangle_oneCollisionOuterChoice hij hjk U kind p.1 p.2
    (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) F) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S) F).card
    else
      0) = (-1 : ℤ) ^ U.card := by
  intro S F
  have hUsub : U ⊆ collisionPairEvents (q := q)
      (pairIndexOfNe i k (ne_of_lt (hij.trans hjk))) :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
  have hcyc := orderedTriangle_oneCollisionOuterChoice_cycleConsistent (G := G) (q := q) y
    hij hjk hik_eq (U := U) hUsub kind
  have hcard := orderedTriangle_oneCollisionOuterChoiceUnion_card
    (q := q) hij hjk (U := U) kind hUsub
  change collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := S) F) at hcyc
  change (collisionSubfamilyPairChoiceUnion (S := S) F).card = U.card + 2 at hcard
  rw [if_pos hcyc, hcard, pow_add]
  norm_num

/-- Summing the canonical outer one-collision candidates gives the local
triangle contribution `-2`. -/
theorem orderedTriangle_oneCollisionOuterCandidateTermSum_eq_neg_two
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hik_eq : y k = y i) :
    let S := queryPairSet ({i, j, k} : Finset (Fin q))
    let A := (collisionPairEvents (q := q)
      (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)))).powerset.filter
      (fun T => T.Nonempty)
    ∑ U ∈ A, ∑ kind : CollisionKind,
      (if collisionSubfamilyCycleConsistent (G := G) (q := q) y
          (collisionSubfamilyPairChoiceUnion (S := S)
            (fun p : S => orderedTriangle_oneCollisionOuterChoice hij hjk U kind p.1 p.2)) then
        (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S)
            (fun p : S => orderedTriangle_oneCollisionOuterChoice hij hjk U kind p.1 p.2)).card
      else
        0) = -2 := by
  intro S A
  trans ∑ U ∈ A, ∑ _kind : CollisionKind, (-1 : ℤ) ^ U.card
  · apply Finset.sum_congr rfl
    intro U hU
    apply Finset.sum_congr rfl
    intro kind _hkind
    exact orderedTriangle_oneCollisionOuterChoiceTerm_eq_neg_one_pow_card
      (G := G) (q := q) y hij hjk hik_eq (U := U) (kind := kind) hU
  · simp_rw [show ∀ n : Nat, (∑ _kind : CollisionKind, (-1 : ℤ) ^ n) =
        2 * ((-1 : ℤ) ^ n) from by
      intro n
      rw [Finset.sum_const]
      simp [collisionKind_card]]
    rw [← Finset.mul_sum]
    dsimp [A]
    rw [collisionPairEvents_localNonemptyPowersetAlternatingCard]
    norm_num

/-- In the outer one-collision branch, every globally consistent pair-choice
summand is one of the canonical outer candidates. -/
theorem orderedTriangle_pairChoice_eq_oneCollisionOuterChoice_of_outer_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q} (hij : i < j) (hjk : j < k)
    (hik_eq : y k = y i) (hij_ne : y j ≠ y i)
    {F : (p : PairIndex q) →
        p ∈ queryPairSet ({i, j, k} : Finset (Fin q)) → Finset (CollisionEvent q)}
    (hF : F ∈ (queryPairSet ({i, j, k} : Finset (Fin q))).pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)))
    (hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
      (collisionSubfamilyPairChoiceUnion (S := queryPairSet ({i, j, k} : Finset (Fin q)))
        (fun p : queryPairSet ({i, j, k} : Finset (Fin q)) => F p.1 p.2))) :
    ∃ kind : CollisionKind,
      F = orderedTriangle_oneCollisionOuterChoice hij hjk
        (F (pairIndexOfNe i k (ne_of_lt (hij.trans hjk))) (by
          rw [queryPairSet_orderedTriple hij hjk]; simp)) kind := by
  rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨hij_jk, hij_ik, hjk_ik⟩
  rcases orderedTriangle_pairChoice_oneCollision_unequalSingletons_sameKind_of_outer_visible_eq
      (G := G) (q := q) y hij hjk hik_eq hij_ne hF hglobal with ⟨kind, hkij, hkjk⟩
  refine ⟨kind, ?_⟩
  funext p hp
  by_cases hpik : p = pairIndexOfNe i k (ne_of_lt (hij.trans hjk))
  · subst p
    simp [orderedTriangle_oneCollisionOuterChoice]
  · by_cases hpij : p = pairIndexOfNe i j (ne_of_lt hij)
    · subst p
      simpa [orderedTriangle_oneCollisionOuterChoice, hij_ik] using hkij
    · have hp_mem : p ∈ ({pairIndexOfNe i j (ne_of_lt hij),
          pairIndexOfNe j k (ne_of_lt hjk),
          pairIndexOfNe i k (ne_of_lt (hij.trans hjk))} : Finset (PairIndex q)) := by
        simpa [queryPairSet_orderedTriple hij hjk] using hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      rcases hp_mem with hpbad | hpjk | hpbad
      · exact False.elim (hpij hpbad)
      · subst p
        simpa [orderedTriangle_oneCollisionOuterChoice, hjk_ik, hij_jk.symm] using hkjk
      · exact False.elim (hpik hpbad)

/-- The outer one-collision ordered-triangle no-rank coefficient is exactly
`-2`. -/
theorem rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_outer_visible_eq
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {i j k : Fin q}
    (hij : i < j) (hjk : j < k)
    (hik_eq : y k = y i) (hij_ne : y j ≠ y i) :
    rankTwoPairSupportPiUnionCoefficientInt G q y
      (queryPairSet ({i, j, k} : Finset (Fin q))) = -2 := by
  let S := queryPairSet ({i, j, k} : Finset (Fin q))
  let A := (collisionPairEvents (q := q)
    (pairIndexOfNe i k (ne_of_lt (hij.trans hjk)))).powerset.filter
      (fun T => T.Nonempty)
  let P := S.pi (fun p =>
    (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty))
  let term : ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)) → ℤ := fun F =>
    if collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)) then
      (-1 : ℤ) ^ (collisionSubfamilyPairChoiceUnion (S := S)
        (fun p : S => F p.1 p.2)).card
    else
      0
  let C : Finset ((p : PairIndex q) → p ∈ S → Finset (CollisionEvent q)) :=
    A.biUnion fun U => (Finset.univ : Finset CollisionKind).image fun kind =>
      orderedTriangle_oneCollisionOuterChoice hij hjk U kind
  change ∑ F ∈ P, term F = -2
  have hC_subset_P : C ⊆ P := by
    intro F hF
    dsimp [C] at hF
    simp only [Finset.mem_biUnion] at hF
    rcases hF with ⟨U, hU, hFimg⟩
    rcases Finset.mem_image.mp hFimg with ⟨kind, _hkind, hEq⟩
    subst F
    dsimp [P, S]
    exact orderedTriangle_oneCollisionOuterChoice_mem_pi (q := q) hij hjk
      (U := U) (kind := kind) hU
  have hzero : ∀ F ∈ P, F ∉ C → term F = 0 := by
    intro F hFP hnot
    dsimp [term]
    by_cases hglobal : collisionSubfamilyCycleConsistent (G := G) (q := q) y
        (collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2))
    · exfalso
      have hclass := orderedTriangle_pairChoice_eq_oneCollisionOuterChoice_of_outer_visible_eq
        (G := G) (q := q) y hij hjk hik_eq hij_ne
        (F := F) (by simpa [P, S] using hFP) hglobal
      rcases hclass with ⟨kind, hEq⟩
      let pik := pairIndexOfNe i k (ne_of_lt (hij.trans hjk))
      have hpik : pik ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pik]
      let U := F pik hpik
      have hU : U ∈ A := by
        have hlocal := Finset.mem_pi.mp hFP pik hpik
        simpa [A, U] using hlocal
      apply hnot
      dsimp [C]
      exact Finset.mem_biUnion.mpr ⟨U, hU,
        Finset.mem_image.mpr ⟨kind, Finset.mem_univ kind, by
          simpa [U, pik] using hEq.symm⟩⟩
    · simp [hglobal]
  have hsum_subset := Finset.sum_subset (s₁ := C) (s₂ := P) (f := term) hC_subset_P hzero
  rw [← hsum_subset]
  have hCsum : (∑ F ∈ C, term F) =
      ∑ U ∈ A, ∑ kind : CollisionKind,
        term (orderedTriangle_oneCollisionOuterChoice hij hjk U kind) := by
    dsimp [C]
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro U _hU
      rw [Finset.sum_image]
      intro a _ b _ h
      let pij := pairIndexOfNe i j (ne_of_lt hij)
      have hpij : pij ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pij]
      have hval := congrFun (congrFun h pij) hpij
      rcases pairIndexOfNe_orderedTriple_pairwise_ne hij hjk with ⟨_hij_jk, hij_ik, _hjk_ik⟩
      have hsingleton : ({(pij, a)} : Finset (CollisionEvent q)) = {(pij, b)} := by
        simpa [pij, orderedTriangle_oneCollisionOuterChoice, hij_ik] using hval
      exact congrArg Prod.snd (Finset.singleton_inj.mp hsingleton)
    · intro U _hU U' _hU' hne
      change Disjoint ((Finset.univ : Finset CollisionKind).image
          (fun kind => orderedTriangle_oneCollisionOuterChoice hij hjk U kind))
        ((Finset.univ : Finset CollisionKind).image
          (fun kind => orderedTriangle_oneCollisionOuterChoice hij hjk U' kind))
      rw [Finset.disjoint_left]
      intro F hF hF'
      rcases Finset.mem_image.mp hF with ⟨kind, _hkind, rfl⟩
      rcases Finset.mem_image.mp hF' with ⟨_kind', _hkind', hEq⟩
      let pik := pairIndexOfNe i k (ne_of_lt (hij.trans hjk))
      have hpik : pik ∈ S := by
        dsimp [S]
        rw [queryPairSet_orderedTriple hij hjk]
        simp [pik]
      have hval := congrFun (congrFun hEq.symm pik) hpik
      have hUeq : U = U' := by
        simpa [pik, orderedTriangle_oneCollisionOuterChoice] using hval
      exact hne hUeq
  rw [hCsum]
  exact orderedTriangle_oneCollisionOuterCandidateTermSum_eq_neg_two
    (G := G) (q := q) y hij hjk hik_eq

/-- Number of three-coordinate visible transcript subsets whose values are all
equal.  This is the rank-two triangle statistic that survives after the
universal `-2` triangle contribution is separated. -/
noncomputable def visibleAllEqualTripleCountNat
    (G : Type*) [DecidableEq G] {q : Nat} (y : Fin q → G) : Nat := by
  classical
  exact (((Finset.univ : Finset (Fin q)).powersetCard 3).filter
    (fun S => visibleAllEqualOn G y S)).card

/-- The all-equal triple count is bounded by the total number of triples. -/
theorem visibleAllEqualTripleCountNat_le_choose
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    visibleAllEqualTripleCountNat G y ≤ q.choose 3 := by
  classical
  unfold visibleAllEqualTripleCountNat
  calc
    (((Finset.univ : Finset (Fin q)).powersetCard 3).filter
        (fun S => visibleAllEqualOn G y S)).card ≤
        ((Finset.univ : Finset (Fin q)).powersetCard 3).card :=
          Finset.card_filter_le _ _
    _ = q.choose 3 := by simp [Finset.card_powersetCard]

/-- The total all-equal-triple count over all visible transcripts is
`choose q 3 * |G|^(q - 2)`. -/
theorem sum_visibleAllEqualTripleCountNat_eq_choose_mul_card_pow
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    (∑ y : Fin q → G, visibleAllEqualTripleCountNat G y) =
      q.choose 3 * Fintype.card G ^ (q - 2) := by
  classical
  let A : Finset (Finset (Fin q)) := (Finset.univ : Finset (Fin q)).powersetCard 3
  have hswap :
      (∑ y : Fin q → G, (A.filter (fun S => visibleAllEqualOn G y S)).card) =
        ∑ S ∈ A, ((Finset.univ : Finset (Fin q → G)).filter
          (fun y => visibleAllEqualOn G y S)).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simpa using (Finset.sum_comm
      (s := (Finset.univ : Finset (Fin q → G)))
      (t := A)
      (f := fun y S => if visibleAllEqualOn G y S then (1 : Nat) else 0))
  unfold visibleAllEqualTripleCountNat
  change (∑ y : Fin q → G, (A.filter (fun S => visibleAllEqualOn G y S)).card) =
      q.choose 3 * Fintype.card G ^ (q - 2)
  rw [hswap]
  calc
    (∑ S ∈ A, ((Finset.univ : Finset (Fin q → G)).filter
          (fun y => visibleAllEqualOn G y S)).card) =
        ∑ S ∈ A, Fintype.card G ^ (q - 2) := by
          apply Finset.sum_congr rfl
          intro S hS
          have hcard : S.card = 3 := (Finset.mem_powersetCard.mp hS).2
          exact visibleAllEqualOn_fiber_card_of_card_eq_three (G := G) hcard
    _ = A.card * Fintype.card G ^ (q - 2) := by
          simp [Finset.sum_const]
    _ = q.choose 3 * Fintype.card G ^ (q - 2) := by
          simp [A, Finset.card_powersetCard]

/-- The uniform first moment of the all-equal-triple statistic is
`choose q 3 / |G|^2`. -/
theorem uniformAverage_visibleAllEqualTripleCountNat_eq_choose_div_card_sq
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) :
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y => (visibleAllEqualTripleCountNat G y : ℝ)) =
      (q.choose 3 : ℝ) / (Fintype.card G : ℝ) ^ 2 := by
  unfold XoP.ANOVA.uniformAverage
  have hsumNat := sum_visibleAllEqualTripleCountNat_eq_choose_mul_card_pow (G := G) q
  have hsumReal :
      (∑ y : Fin q → G, (visibleAllEqualTripleCountNat G y : ℝ)) =
        (q.choose 3 * Fintype.card G ^ (q - 2) : Nat) := by
    exact_mod_cast hsumNat
  have hcardFun : Fintype.card (Fin q → G) = Fintype.card G ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [hsumReal, hcardFun]
  have hN_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hN_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hpow : q - 2 + 2 = q := Nat.sub_add_cancel hq2
  have hpowNat : Fintype.card G ^ q =
      Fintype.card G ^ (q - 2) * Fintype.card G ^ 2 := by
    rw [← pow_add, hpow]
  rw [hpowNat]
  simp only [Nat.cast_mul, Nat.cast_pow]
  field_simp [hN_ne]

/-- Cardinality of one joint fiber for the two equality-pattern statistics
used by the rank-two scalar density: visible pair-collision count and
all-equal-triple count. -/
def rankTwoEqualityStatsFiberCard (G : Type*) [Fintype G] [DecidableEq G]
    (q k t : Nat) : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter
    (fun y => pairCollisionCountNat G q y = k ∧
      visibleAllEqualTripleCountNat G y = t)).card

/-- Uniform averages of functions of the two rank-two equality statistics can
be collapsed to a finite two-dimensional sum over their joint fibers. -/
theorem uniformAverage_of_rankTwoEqualityStats
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (F : Nat → Nat → ℝ) :
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y => F (pairCollisionCountNat G q y) (visibleAllEqualTripleCountNat G y)) =
      (∑ kt ∈ Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
          Finset.range (q.choose 3 + 1),
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) * F kt.1 kt.2) /
        (Fintype.card (Fin q → G) : ℝ) := by
  unfold XoP.ANOVA.uniformAverage
  let R : Finset (Nat × Nat) :=
    Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
      Finset.range (q.choose 3 + 1)
  let stat : (Fin q → G) → Nat × Nat := fun y =>
    (pairCollisionCountNat G q y, visibleAllEqualTripleCountNat G y)
  have hmap : ∀ y ∈ (Finset.univ : Finset (Fin q → G)), stat y ∈ R := by
    intro y _hy
    dsimp [stat, R]
    simp only [Finset.mem_product, Finset.mem_range]
    exact
      ⟨Nat.lt_succ_of_le
          (pairCollisionCountNat_le_pairIndex_card (G := G) (q := q) y),
        Nat.lt_succ_of_le (visibleAllEqualTripleCountNat_le_choose (G := G) (y := y))⟩
  have hfiber :
      (∑ kt ∈ R,
        ∑ y ∈ (Finset.univ : Finset (Fin q → G)).filter (fun y => stat y = kt),
          F (pairCollisionCountNat G q y) (visibleAllEqualTripleCountNat G y)) =
        ∑ y : Fin q → G,
          F (pairCollisionCountNat G q y) (visibleAllEqualTripleCountNat G y) := by
    simpa using Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin q → G)))
      (t := R) (g := stat) hmap
      (fun y : Fin q → G =>
        F (pairCollisionCountNat G q y) (visibleAllEqualTripleCountNat G y))
  rw [← hfiber]
  apply congrArg (fun s : ℝ => s / (Fintype.card (Fin q → G) : ℝ))
  apply Finset.sum_congr rfl
  intro kt _hkt
  have hfilter_eq :
      (Finset.univ : Finset (Fin q → G)).filter (fun y => stat y = kt) =
        (Finset.univ : Finset (Fin q → G)).filter
          (fun y => pairCollisionCountNat G q y = kt.1 ∧
            visibleAllEqualTripleCountNat G y = kt.2) := by
    ext y
    dsimp [stat]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h
    · exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · exact Prod.ext h.1 h.2
  calc
    (∑ y ∈ (Finset.univ : Finset (Fin q → G)).filter (fun y => stat y = kt),
      F (pairCollisionCountNat G q y) (visibleAllEqualTripleCountNat G y)) =
        ∑ _y ∈ (Finset.univ : Finset (Fin q → G)).filter (fun y => stat y = kt),
          F kt.1 kt.2 := by
          apply Finset.sum_congr rfl
          intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have h1 : pairCollisionCountNat G q y = kt.1 := congrArg Prod.fst hy
          have h2 : visibleAllEqualTripleCountNat G y = kt.2 := congrArg Prod.snd hy
          rw [h1, h2]
    _ = (((Finset.univ : Finset (Fin q → G)).filter
          (fun y => pairCollisionCountNat G q y = kt.1 ∧
            visibleAllEqualTripleCountNat G y = kt.2)).card : ℝ) *
          F kt.1 kt.2 := by
          rw [hfilter_eq, Finset.sum_const, nsmul_eq_mul]
    _ = (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) * F kt.1 kt.2 := by
          rfl

/-- Triangle correction in the rank-two layer.  For a three-coordinate support,
the full triangle contributes `-2`; if all three visible outputs are equal,
the parallel hidden/shifted cycles collapse and the contribution is `-1`.

This is the equality-pattern term predicted by the gain-graph analysis. -/
def rankTwoTriangleCorrectionInt (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) : ℤ := by
  classical
  exact
    ∑ S ∈ (Finset.univ : Finset (Fin q)).powerset with S.card = 3,
      (-2 + (if visibleAllEqualOn G y S then 1 else 0) : ℤ)

/-- Closed statistic form of the rank-two triangle correction.  It is the
universal \(-2\) contribution for every coordinate triple plus one unit for
each all-equal visible triple. -/
theorem rankTwoTriangleCorrectionInt_eq_choose_add_allEqualTripleCount
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    rankTwoTriangleCorrectionInt G q y =
      -2 * ((q.choose 3 : Nat) : ℤ) +
        (visibleAllEqualTripleCountNat G y : ℤ) := by
  classical
  have hcardForm :
      rankTwoTriangleCorrectionInt G q y =
        -2 * ((((Finset.univ : Finset (Fin q)).powersetCard 3).card : Nat) : ℤ) +
          (visibleAllEqualTripleCountNat G y : ℤ) := by
    let A := (Finset.univ : Finset (Fin q)).powersetCard 3
    have hcorr : rankTwoTriangleCorrectionInt G q y =
        ∑ S ∈ A, (-2 + (if visibleAllEqualOn G y S then 1 else 0) : ℤ) := by
      unfold rankTwoTriangleCorrectionInt
      rw [← Finset.powersetCard_eq_filter]
    rw [hcorr]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_const]
    rw [Finset.sum_boole]
    simp [A, visibleAllEqualTripleCountNat, mul_comm]
  rw [hcardForm, Finset.card_powersetCard]
  simp

/-- The averaged triangle correction is the universal `-2 * choose q 3`
term plus the first moment of the all-equal-triple statistic. -/
theorem uniformAverage_rankTwoTriangleCorrectionInt_eq
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) :
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y => ((rankTwoTriangleCorrectionInt G q y : ℤ) : ℝ)) =
      -2 * (q.choose 3 : ℝ) +
        (q.choose 3 : ℝ) / (Fintype.card G : ℝ) ^ 2 := by
  have hpoint : ∀ y : Fin q → G,
      ((rankTwoTriangleCorrectionInt G q y : ℤ) : ℝ) =
        -2 * (q.choose 3 : ℝ) + (visibleAllEqualTripleCountNat G y : ℝ) := by
    intro y
    rw [rankTwoTriangleCorrectionInt_eq_choose_add_allEqualTripleCount]
    norm_num
  calc
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y => ((rankTwoTriangleCorrectionInt G q y : ℤ) : ℝ)) =
        XoP.ANOVA.uniformAverage (Fin q → G)
          (fun y => -2 * (q.choose 3 : ℝ) +
            (visibleAllEqualTripleCountNat G y : ℝ)) := by
          apply congrArg
          funext y
          exact hpoint y
    _ = XoP.ANOVA.uniformAverage (Fin q → G) (fun _ => -2 * (q.choose 3 : ℝ)) +
        XoP.ANOVA.uniformAverage (Fin q → G)
          (fun y => (visibleAllEqualTripleCountNat G y : ℝ)) := by
          rw [XoP.ANOVA.uniformAverage_add]
    _ = -2 * (q.choose 3 : ℝ) +
        (q.choose 3 : ℝ) / (Fintype.card G : ℝ) ^ 2 := by
          rw [XoP.ANOVA.uniformAverage_const]
          rw [uniformAverage_visibleAllEqualTripleCountNat_eq_choose_div_card_sq (G := G) q hq2]

/-- Candidate signed equality-pattern coefficient for the full graphic-rank-two
layer.  The intended identity is
`rank-two layer = |G|^(q-2) * rankTwoEqualityCoefficientInt`.

Unlike `rankTwoLayerErrorBound`, this object preserves cancellation: it is a
signed equality-pattern statistic rather than an absolute count of rank-two
subfamilies. -/
def rankTwoEqualityCoefficientInt (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) : ℤ :=
  rankTwoForestCoefficientInt G q y + rankTwoTriangleCorrectionInt G q y

/-- Numeric scalar form of the equality-pattern rank-two coefficient.  Here
`k` is the visible pair-collision count and `t` is the all-equal-triple count. -/
def rankTwoEqualityCoefficientFromStatsInt (q k t : Nat) : ℤ :=
  2 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
    (((k.choose 2 : Nat) : ℤ)) +
    2 * (((((Fintype.card (PairIndex q) - k).choose 2 : Nat) : ℤ))) -
    2 * ((q.choose 3 : Nat) : ℤ) + (t : ℤ)

/-- At zero visible pair collisions and zero all-equal triples, the scalar
rank-two coefficient is already positive at the `1 / |G|^2` scale.  This is a
sanity check for the proof strategy: the isolated quadratic-positive term
`Q_2^+` is not the final lower-order target; the low-rank and rank-two pieces
must be kept together before taking positive parts. -/
theorem rankTwoEqualityCoefficientFromStatsInt_zero_zero
    (q : Nat) :
    rankTwoEqualityCoefficientFromStatsInt q 0 0 =
      4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
        2 * ((q.choose 3 : Nat) : ℤ) := by
  unfold rankTwoEqualityCoefficientFromStatsInt
  norm_num
  ring

/-- Concrete instance of `rankTwoEqualityCoefficientFromStatsInt_zero_zero`:
for four queries the all-distinct equality-statistic fiber has coefficient
`52`. -/
theorem rankTwoEqualityCoefficientFromStatsInt_four_zero_zero :
    rankTwoEqualityCoefficientFromStatsInt 4 0 0 = 52 := by
  native_decide

/-- Equality-pattern rank-two coefficient after separating the universal
triangle term from the all-equal-triple correction.  The remaining non-scalar
statistics are the forest coefficient and the all-equal triple count. -/
theorem rankTwoEqualityCoefficientInt_eq_forest_sub_choose_add_allEqualTripleCount
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    rankTwoEqualityCoefficientInt G q y =
      rankTwoForestCoefficientInt G q y - 2 * ((q.choose 3 : Nat) : ℤ) +
        (visibleAllEqualTripleCountNat G y : ℤ) := by
  unfold rankTwoEqualityCoefficientInt
  rw [rankTwoTriangleCorrectionInt_eq_choose_add_allEqualTripleCount]
  ring

/-- Equality-pattern rank-two coefficient in closed collision-statistic form:
the forest term is now a scalar function of the visible collision-pair set,
and the triangle term is the universal `-2 * choose q 3` plus the all-equal
triple correction. -/
theorem rankTwoEqualityCoefficientInt_eq_collisionCount_sub_choose_add_allEqualTripleCount
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    rankTwoEqualityCoefficientInt G q y =
      rankTwoForestCollisionCountCoefficientInt (pairCollisionSet G y) -
        2 * ((q.choose 3 : Nat) : ℤ) +
        (visibleAllEqualTripleCountNat G y : ℤ) := by
  rw [rankTwoEqualityCoefficientInt_eq_forest_sub_choose_add_allEqualTripleCount]
  rw [rankTwoForestCoefficientInt_eq_collisionSet]
  rw [rankTwoForestCollisionSetCoefficientInt_eq_count]

/-- Fully numeric equality-pattern form of the rank-two coefficient.  The
coefficient depends on the visible transcript only through the number of
visible colliding query pairs and the number of all-equal visible triples. -/
theorem rankTwoEqualityCoefficientInt_eq_pairCollisionCount_sub_choose_add_allEqualTripleCount
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    rankTwoEqualityCoefficientInt G q y =
      rankTwoEqualityCoefficientFromStatsInt q
        (pairCollisionCountNat G q y) (visibleAllEqualTripleCountNat G y) := by
  rw [rankTwoEqualityCoefficientInt_eq_collisionCount_sub_choose_add_allEqualTripleCount]
  rw [rankTwoForestCollisionCountCoefficientInt_pairCollisionSet_eq_pairCollisionCount]
  unfold rankTwoEqualityCoefficientFromStatsInt
  rfl

/-- The rank-two index in the gain-graph rank stratification. -/
def collisionSubfamilyGraphicRankTwoFin (q : Nat) (hq2 : 2 ≤ q) : Fin (q + 1) :=
  ⟨2, Nat.lt_succ_of_le hq2⟩

/-- The rank-three index in the gain-graph rank stratification. -/
def collisionSubfamilyGraphicRankThreeFin (q : Nat) (hq3 : 3 ≤ q) : Fin (q + 1) :=
  ⟨3, Nat.lt_succ_of_le hq3⟩

/-- The pure signed alternating coefficient of the graphic-rank-two layer,
with the common field-size factor `|G|^(q-2)` removed. -/
def rankTwoAlternatingCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyGraphicRank (q := q) T = 2,
    if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
      (-1 : ℤ) ^ T.card
    else
      0

/-- The pure signed alternating coefficient of the graphic-rank-three layer,
with the common field-size factor `|G|^(q-3)` removed.  This is the
combinatorial object whose sign regions must be controlled to close the
rank-three obstruction. -/
def rankThreeAlternatingCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyGraphicRank (q := q) T = 3,
    if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
      (-1 : ℤ) ^ T.card
    else
      0

/-- The rank-three alternating coefficient restricted to subfamilies whose
query-pair support has a fixed cardinality. -/
def rankThreeAlternatingCoefficientSupportCardEqInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (m : Nat) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyGraphicRank (q := q) T = 3,
    if (collisionSubfamilyPairSupport q T).card = m then
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
        (-1 : ℤ) ^ T.card
      else
        0
    else
      0

/-- Rank-three alternating coefficient restricted to an exact query-pair
support set.  This is the reindexing layer for the low-support rank-three
analysis. -/
def rankThreeAlternatingCoefficientPairSupportEqInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyPairSupport q T = S,
    if collisionSubfamilyGraphicRank (q := q) T = 3 then
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
        (-1 : ℤ) ^ T.card
      else
        0
    else
      0

/-- The rank-three alternating coefficient restricted to subfamilies whose
query-pair support cardinality is at least `m`. -/
def rankThreeAlternatingCoefficientSupportCardGeInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (m : Nat) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyGraphicRank (q := q) T = 3,
    if m ≤ (collisionSubfamilyPairSupport q T).card then
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
        (-1 : ℤ) ^ T.card
      else
        0
    else
      0

/-- The rank-two alternating coefficient restricted to subfamilies whose
query-pair support has a fixed cardinality. -/
def rankTwoAlternatingCoefficientSupportCardEqInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (m : Nat) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyGraphicRank (q := q) T = 2,
    if (collisionSubfamilyPairSupport q T).card = m then
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
        (-1 : ℤ) ^ T.card
      else
        0
    else
      0

/-- Rank-two alternating coefficient restricted to an exact query-pair support
set.  This is the first reindexing layer for support-cardinality two. -/
def rankTwoAlternatingCoefficientPairSupportEqInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyPairSupport q T = S,
    if collisionSubfamilyGraphicRank (q := q) T = 2 then
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
        (-1 : ℤ) ^ T.card
      else
        0
    else
      0

/-- Exact-support alternating coefficient after the graphic-rank test has been
removed.  For two-element query-pair supports this is equivalent to
`rankTwoAlternatingCoefficientPairSupportEqInt` once rank automaticity is
proved. -/
def rankTwoAlternatingCoefficientPairSupportEqNoRankInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q)) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyPairSupport q T = S,
    if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
      (-1 : ℤ) ^ T.card
    else
      0

/-- Exact-support no-rank coefficients are pair-local choice sums with the
global cycle-consistency predicate retained.  This is the non-factorized
reindexing used for triangle supports. -/
theorem rankTwoAlternatingCoefficientPairSupportEqNoRankInt_eq_piUnion
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q)) :
    rankTwoAlternatingCoefficientPairSupportEqNoRankInt G q y S =
      rankTwoPairSupportPiUnionCoefficientInt G q y S := by
  unfold rankTwoAlternatingCoefficientPairSupportEqNoRankInt
    rankTwoPairSupportPiUnionCoefficientInt
  refine Finset.sum_bij'
    (fun T _hT => fun p hp => collisionSubfamilyPairFiber (q := q) T p)
    (fun F _hF => collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2))
    ?hi ?hj ?left ?right ?term
  · intro T hT
    simp only [Finset.mem_filter] at hT
    have hsupport : collisionSubfamilyPairSupport q T = S := hT.2
    apply Finset.mem_pi.mpr
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · exact collisionSubfamilyPairFiber_subset_pairEvents (q := q) T p
    · exact (collisionSubfamilyPairFiber_nonempty_iff (q := q) (T := T) (p := p)).mpr
        (by simpa [hsupport] using hp)
  · intro F hF
    have hFmem : F ∈ S.pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
      hF
    have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact pairChoice_mem_pi_subset_pairEvents hFmem p
    have hne : ∀ p : S, (F p.1 p.2).Nonempty := by
      intro p
      exact pairChoice_mem_pi_nonempty hFmem p
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro e he
      simp
    · exact collisionSubfamilyPairSupport_pairChoiceUnion_eq
        (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub hne
  · intro T hT
    simp only [Finset.mem_filter] at hT
    exact collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
      (q := q) (T := T) (S := S) hT.2
  · intro F hF
    have hFmem : F ∈ S.pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
      hF
    have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact pairChoice_mem_pi_subset_pairEvents hFmem p
    funext p hp
    exact collisionSubfamilyPairFiber_pairChoiceUnion_eq
      (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub ⟨p, hp⟩
  · intro T hT
    simp only [Finset.mem_filter] at hT
    have hT_eq : collisionSubfamilyPairChoiceUnion
        (S := S) (fun p : S => collisionSubfamilyPairFiber (q := q) T p.1) = T :=
      collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
        (q := q) (T := T) (S := S) hT.2
    simp [hT_eq]

/-- Exact-support rank-two coefficients are pair-local choice sums with both the
rank test and the global cycle-consistency predicate retained.  This is the
ranked companion to
`rankTwoAlternatingCoefficientPairSupportEqNoRankInt_eq_piUnion`. -/
theorem rankTwoAlternatingCoefficientPairSupportEqInt_eq_piUnionRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q)) :
    rankTwoAlternatingCoefficientPairSupportEqInt G q y S =
      rankTwoPairSupportPiUnionRankCoefficientInt G q y S := by
  unfold rankTwoAlternatingCoefficientPairSupportEqInt
    rankTwoPairSupportPiUnionRankCoefficientInt
  refine Finset.sum_bij'
    (fun T _hT => fun p hp => collisionSubfamilyPairFiber (q := q) T p)
    (fun F _hF => collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2))
    ?hi ?hj ?left ?right ?term
  · intro T hT
    simp only [Finset.mem_filter] at hT
    have hsupport : collisionSubfamilyPairSupport q T = S := hT.2
    apply Finset.mem_pi.mpr
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · exact collisionSubfamilyPairFiber_subset_pairEvents (q := q) T p
    · exact (collisionSubfamilyPairFiber_nonempty_iff (q := q) (T := T) (p := p)).mpr
        (by simpa [hsupport] using hp)
  · intro F hF
    have hFmem : F ∈ S.pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
      hF
    have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact pairChoice_mem_pi_subset_pairEvents hFmem p
    have hne : ∀ p : S, (F p.1 p.2).Nonempty := by
      intro p
      exact pairChoice_mem_pi_nonempty hFmem p
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro e he
      simp
    · exact collisionSubfamilyPairSupport_pairChoiceUnion_eq
        (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub hne
  · intro T hT
    simp only [Finset.mem_filter] at hT
    exact collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
      (q := q) (T := T) (S := S) hT.2
  · intro F hF
    have hFmem : F ∈ S.pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
      hF
    have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact pairChoice_mem_pi_subset_pairEvents hFmem p
    funext p hp
    exact collisionSubfamilyPairFiber_pairChoiceUnion_eq
      (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub ⟨p, hp⟩
  · intro T hT
    simp only [Finset.mem_filter] at hT
    have hT_eq : collisionSubfamilyPairChoiceUnion
        (S := S) (fun p : S => collisionSubfamilyPairFiber (q := q) T p.1) = T :=
      collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
        (q := q) (T := T) (S := S) hT.2
    simp [hT_eq]

/-- The support-cardinality-two rank-two coefficient regrouped by exact
query-pair support. -/
theorem rankTwoAlternatingCoefficientSupportCardEq_two_eq_sum_pairSupportEq
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoAlternatingCoefficientSupportCardEqInt G q y 2 =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = 2),
        rankTwoAlternatingCoefficientPairSupportEqInt G q y S := by
  unfold rankTwoAlternatingCoefficientSupportCardEqInt
    rankTwoAlternatingCoefficientPairSupportEqInt
  rw [Finset.sum_filter]
  trans ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset,
      if (collisionSubfamilyPairSupport q T).card = 2 then
        if collisionSubfamilyGraphicRank (q := q) T = 2 then
          if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (-1 : ℤ) ^ T.card
          else
            0
        else
          0
      else
        0
  · apply Finset.sum_congr rfl
    intro T _hT
    by_cases hrank : collisionSubfamilyGraphicRank (q := q) T = 2 <;>
      by_cases hsupport : (collisionSubfamilyPairSupport q T).card = 2 <;>
        simp [hrank, hsupport]
  rw [← Finset.sum_filter]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext T
    simp
  · intro T hT
    simp only [Finset.mem_filter] at hT
    by_cases hrank : collisionSubfamilyGraphicRank (q := q) T = 2
    · simp [hrank]
    · simp [hrank]

/-- The support-cardinality-three rank-two coefficient regrouped by exact
query-pair support.  This is the first, purely finite-sum, reindexing step for
the triangle correction. -/
theorem rankTwoAlternatingCoefficientSupportCardEq_three_eq_sum_pairSupportEq
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoAlternatingCoefficientSupportCardEqInt G q y 3 =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = 3),
        rankTwoAlternatingCoefficientPairSupportEqInt G q y S := by
  unfold rankTwoAlternatingCoefficientSupportCardEqInt
    rankTwoAlternatingCoefficientPairSupportEqInt
  rw [Finset.sum_filter]
  trans ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset,
      if (collisionSubfamilyPairSupport q T).card = 3 then
        if collisionSubfamilyGraphicRank (q := q) T = 2 then
          if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (-1 : ℤ) ^ T.card
          else
            0
        else
          0
      else
        0
  · apply Finset.sum_congr rfl
    intro T _hT
    by_cases hrank : collisionSubfamilyGraphicRank (q := q) T = 2 <;>
      by_cases hsupport : (collisionSubfamilyPairSupport q T).card = 3 <;>
        simp [hrank, hsupport]
  rw [← Finset.sum_filter]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext T
    simp
  · intro T hT
    simp only [Finset.mem_filter] at hT
    by_cases hrank : collisionSubfamilyGraphicRank (q := q) T = 2
    · simp [hrank]
    · simp [hrank]

/-- Graph-only rank automaticity for exact two-pair supports.  Once a
collision-event subfamily touches exactly two query pairs, its support graph has
graphic rank two. -/
def RankTwoPairSupportRankAutomatic (q : Nat) : Prop :=
  ∀ T : Finset (CollisionEvent q),
    (collisionSubfamilyPairSupport q T).card = 2 →
      collisionSubfamilyGraphicRank (q := q) T = 2

/-- General graph inequality that would imply rank automaticity: the graphic
rank is bounded by the number of distinct query pairs touched by the subfamily. -/
def GraphicRankLePairSupportCard (q : Nat) : Prop :=
  ∀ T : Finset (CollisionEvent q),
    collisionSubfamilyGraphicRank (q := q) T ≤
      (collisionSubfamilyPairSupport q T).card

/-- Bounding the graphic rank of canonical hidden representatives implies the
rank-versus-pair-support inequality for arbitrary hidden/shifted subfamilies. -/
theorem GraphicRankLePairSupportCard.of_hiddenRepresentative
    {q : Nat} (hhidden : HiddenRepresentativeGraphicRankLeCard q) :
    GraphicRankLePairSupportCard q := by
  intro T
  let S := collisionSubfamilyPairSupport q T
  have hsupport :
      collisionSubfamilyPairSupport q
          (collisionPairSupportHiddenRepresentative (q := q) S) =
        collisionSubfamilyPairSupport q T := by
    simpa [S] using collisionSubfamilyPairSupport_hiddenRepresentative (q := q) S
  have hrank_eq :
      collisionSubfamilyGraphicRank (q := q)
          (collisionPairSupportHiddenRepresentative (q := q) S) =
        collisionSubfamilyGraphicRank (q := q) T :=
    collisionSubfamilyGraphicRank_eq_of_pairSupport_eq (q := q) hsupport
  rw [← hrank_eq]
  exact hhidden S

/-- The exact two-edge canonical graph endpoint implies rank automaticity for
arbitrary exact two-pair hidden/shifted subfamilies. -/
theorem RankTwoPairSupportRankAutomatic.of_hiddenRepresentative_card_two
    {q : Nat} (hhiddenTwo : HiddenRepresentativeGraphicRankLeTwoOnCardTwo q) :
    RankTwoPairSupportRankAutomatic q := by
  intro T hsupport
  let S := collisionSubfamilyPairSupport q T
  have hsupport_hidden :
      collisionSubfamilyPairSupport q
          (collisionPairSupportHiddenRepresentative (q := q) S) =
        collisionSubfamilyPairSupport q T := by
    simpa [S] using collisionSubfamilyPairSupport_hiddenRepresentative (q := q) S
  have hrank_eq :
      collisionSubfamilyGraphicRank (q := q)
          (collisionPairSupportHiddenRepresentative (q := q) S) =
        collisionSubfamilyGraphicRank (q := q) T :=
    collisionSubfamilyGraphicRank_eq_of_pairSupport_eq (q := q) hsupport_hidden
  have hle_rank : collisionSubfamilyGraphicRank (q := q) T ≤ 2 := by
    rw [← hrank_eq]
    exact hhiddenTwo S hsupport
  have hne : T.Nonempty := by
    by_contra hempty
    have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    subst T
    simp [collisionSubfamilyPairSupport] at hsupport
  have hpos : 0 < collisionSubfamilyGraphicRank (q := q) T :=
    collisionSubfamilyGraphicRank_pos_of_nonempty (q := q) hne
  by_contra hnot
  have hrank_one : collisionSubfamilyGraphicRank (q := q) T = 1 := by omega
  have hsupport_one :
      (collisionSubfamilyPairSupport q T).card = 1 :=
    collisionSubfamilyPairSupport_card_eq_one_of_graphicRank_eq_one (q := q) hrank_one
  omega

/-- Exact two-pair support subfamilies are automatically graphic-rank two. -/
theorem rankTwoPairSupportRankAutomatic (q : Nat) :
    RankTwoPairSupportRankAutomatic q :=
  RankTwoPairSupportRankAutomatic.of_hiddenRepresentative_card_two
    (hiddenRepresentativeGraphicRankLeTwoOnCardTwo q)

/-- Graphic-rank-three subfamilies must touch at least three query pairs. -/
theorem collisionSubfamilyPairSupport_three_le_of_graphicRank_eq_three
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 3) :
    3 ≤ (collisionSubfamilyPairSupport q T).card := by
  by_contra hlt
  have hcard_le_two : (collisionSubfamilyPairSupport q T).card ≤ 2 := by omega
  have hne : T.Nonempty := by
    by_contra hempty
    have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    subst T
    simp [collisionSubfamilyGraphicRank_empty] at hrank
  have hsupport_ne := collisionSubfamilyPairSupport_nonempty_of_nonempty (q := q) hne
  have hsupport_card_pos : 0 < (collisionSubfamilyPairSupport q T).card :=
    Finset.card_pos.mpr hsupport_ne
  have hcases :
      (collisionSubfamilyPairSupport q T).card = 1 ∨
        (collisionSubfamilyPairSupport q T).card = 2 := by
    omega
  rcases hcases with hcard_one | hcard_two
  · rcases Finset.card_eq_one.mp hcard_one with ⟨p, hsupport⟩
    have hsubset :
        T ⊆ collisionPairEvents (q := q) p :=
      collisionSubfamily_subset_collisionPairEvents_of_pairSupport_eq_singleton
        (q := q) (T := T) hsupport
    have hrank_one :
        collisionSubfamilyGraphicRank (q := q) T = 1 :=
      collisionSubfamilyGraphicRank_eq_one_of_nonempty_subset_collisionPairEvents
        (q := q) p hne hsubset
    omega
  · have hrank_two :
        collisionSubfamilyGraphicRank (q := q) T = 2 :=
      rankTwoPairSupportRankAutomatic q T hcard_two
    omega

/-- Exact support-size decomposition of the rank-three alternating coefficient.
The support lower bound leaves support sizes `3`, `4`, and `>= 5`. -/
theorem rankThreeAlternatingCoefficientInt_eq_supportCard_three_add_four_add_ge_five
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankThreeAlternatingCoefficientInt G q y =
      rankThreeAlternatingCoefficientSupportCardEqInt G q y 3 +
        rankThreeAlternatingCoefficientSupportCardEqInt G q y 4 +
        rankThreeAlternatingCoefficientSupportCardGeInt G q y 5 := by
  unfold rankThreeAlternatingCoefficientInt
    rankThreeAlternatingCoefficientSupportCardEqInt
    rankThreeAlternatingCoefficientSupportCardGeInt
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter] at hT
  have hthree :
      3 ≤ (collisionSubfamilyPairSupport q T).card :=
    collisionSubfamilyPairSupport_three_le_of_graphicRank_eq_three (q := q) hT.2
  by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
  · by_cases h3 : (collisionSubfamilyPairSupport q T).card = 3
    · simp [hcyc, h3]
    · by_cases h4 : (collisionSubfamilyPairSupport q T).card = 4
      · simp [hcyc, h4]
      · have h5 : 5 ≤ (collisionSubfamilyPairSupport q T).card := by omega
        simp [hcyc, h3, h4, h5]
  · simp [hcyc]

/-- A fixed-support-cardinality rank-three coefficient can be regrouped by the
exact query-pair support. -/
theorem rankThreeAlternatingCoefficientSupportCardEq_eq_sum_pairSupportEq
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (m : Nat) :
    rankThreeAlternatingCoefficientSupportCardEqInt G q y m =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = m),
        rankThreeAlternatingCoefficientPairSupportEqInt G q y S := by
  unfold rankThreeAlternatingCoefficientSupportCardEqInt
    rankThreeAlternatingCoefficientPairSupportEqInt
  rw [Finset.sum_filter]
  trans ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset,
      if (collisionSubfamilyPairSupport q T).card = m then
        if collisionSubfamilyGraphicRank (q := q) T = 3 then
          if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (-1 : ℤ) ^ T.card
          else
            0
        else
          0
      else
        0
  · apply Finset.sum_congr rfl
    intro T _hT
    by_cases hrank : collisionSubfamilyGraphicRank (q := q) T = 3 <;>
      by_cases hsupport : (collisionSubfamilyPairSupport q T).card = m <;>
        simp [hrank, hsupport]
  rw [← Finset.sum_filter]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr
  · ext T
    simp
  · intro T hT
    simp only [Finset.mem_filter] at hT
    by_cases hrank : collisionSubfamilyGraphicRank (q := q) T = 3
    · simp [hrank]
    · simp [hrank]

/-- Exact-support rank-three coefficients are pair-local choice sums with both
the rank test and the global cycle-consistency predicate retained. -/
theorem rankThreeAlternatingCoefficientPairSupportEqInt_eq_piUnionRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q)) :
    rankThreeAlternatingCoefficientPairSupportEqInt G q y S =
      rankThreePairSupportPiUnionRankCoefficientInt G q y S := by
  unfold rankThreeAlternatingCoefficientPairSupportEqInt
    rankThreePairSupportPiUnionRankCoefficientInt
  refine Finset.sum_bij'
    (fun T _hT => fun p hp => collisionSubfamilyPairFiber (q := q) T p)
    (fun F _hF => collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2))
    ?hi ?hj ?left ?right ?term
  · intro T hT
    simp only [Finset.mem_filter] at hT
    have hsupport : collisionSubfamilyPairSupport q T = S := hT.2
    apply Finset.mem_pi.mpr
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · exact collisionSubfamilyPairFiber_subset_pairEvents (q := q) T p
    · exact (collisionSubfamilyPairFiber_nonempty_iff (q := q) (T := T) (p := p)).mpr
        (by simpa [hsupport] using hp)
  · intro F hF
    have hFmem : F ∈ S.pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
      hF
    have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact pairChoice_mem_pi_subset_pairEvents hFmem p
    have hne : ∀ p : S, (F p.1 p.2).Nonempty := by
      intro p
      exact pairChoice_mem_pi_nonempty hFmem p
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro e he
      simp
    · exact collisionSubfamilyPairSupport_pairChoiceUnion_eq
        (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub hne
  · intro T hT
    simp only [Finset.mem_filter] at hT
    exact collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
      (q := q) (T := T) (S := S) hT.2
  · intro F hF
    have hFmem : F ∈ S.pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
      hF
    have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact pairChoice_mem_pi_subset_pairEvents hFmem p
    funext p hp
    exact collisionSubfamilyPairFiber_pairChoiceUnion_eq
      (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub ⟨p, hp⟩
  · intro T hT
    simp only [Finset.mem_filter] at hT
    have hT_eq : collisionSubfamilyPairChoiceUnion
        (S := S) (fun p : S => collisionSubfamilyPairFiber (q := q) T p.1) = T :=
      collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
        (q := q) (T := T) (S := S) hT.2
    simp [hT_eq]

/-- Support-cardinality-three rank-three coefficients regrouped as pair-local
choice sums with the rank-three test retained. -/
theorem rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_piUnionRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankThreeAlternatingCoefficientSupportCardEqInt G q y 3 =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = 3),
        rankThreePairSupportPiUnionRankCoefficientInt G q y S := by
  rw [rankThreeAlternatingCoefficientSupportCardEq_eq_sum_pairSupportEq]
  apply Finset.sum_congr rfl
  intro S _hS
  exact rankThreeAlternatingCoefficientPairSupportEqInt_eq_piUnionRank G q y S

/-- Support-cardinality-four rank-three coefficients regrouped as pair-local
choice sums with the rank-three test retained. -/
theorem rankThreeAlternatingCoefficientSupportCardEq_four_eq_sum_piUnionRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankThreeAlternatingCoefficientSupportCardEqInt G q y 4 =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = 4),
        rankThreePairSupportPiUnionRankCoefficientInt G q y S := by
  rw [rankThreeAlternatingCoefficientSupportCardEq_eq_sum_pairSupportEq]
  apply Finset.sum_congr rfl
  intro S _hS
  exact rankThreeAlternatingCoefficientPairSupportEqInt_eq_piUnionRank G q y S

/-- If the exact query-pair support has graphic rank three, the pair-local
rank-three sum can drop the per-choice rank test. -/
theorem rankThreePairSupportPiUnionRankCoefficientInt_eq_noRank_of_pairSupportGraphicRank_eq_three
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q))
    (hSrank : pairSupportGraphicRank q S = 3) :
    rankThreePairSupportPiUnionRankCoefficientInt G q y S =
      rankThreePairSupportPiUnionCoefficientInt G q y S := by
  unfold rankThreePairSupportPiUnionRankCoefficientInt
    rankThreePairSupportPiUnionCoefficientInt rankTwoPairSupportPiUnionCoefficientInt
  apply Finset.sum_congr rfl
  intro F hF
  have hFmem : F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
    hF
  have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
    intro p
    exact pairChoice_mem_pi_subset_pairEvents hFmem p
  have hne : ∀ p : S, (F p.1 p.2).Nonempty := by
    intro p
    exact pairChoice_mem_pi_nonempty hFmem p
  let U := collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)
  have hsupport : collisionSubfamilyPairSupport q U = S :=
    collisionSubfamilyPairSupport_pairChoiceUnion_eq
      (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub hne
  have hrank : collisionSubfamilyGraphicRank (q := q) U = 3 := by
    rw [collisionSubfamilyGraphicRank_eq_pairSupportGraphicRank (q := q) U]
    simpa [hsupport] using hSrank
  simp [U, hrank]

/-- If the exact query-pair support does not have graphic rank three, its
rank-three pair-local sum is zero. -/
theorem rankThreePairSupportPiUnionRankCoefficientInt_eq_zero_of_pairSupportGraphicRank_ne_three
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q))
    (hSrank : pairSupportGraphicRank q S ≠ 3) :
    rankThreePairSupportPiUnionRankCoefficientInt G q y S = 0 := by
  unfold rankThreePairSupportPiUnionRankCoefficientInt
  apply Finset.sum_eq_zero
  intro F hF
  have hFmem : F ∈ S.pi
      (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
    hF
  have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
    intro p
    exact pairChoice_mem_pi_subset_pairEvents hFmem p
  have hne : ∀ p : S, (F p.1 p.2).Nonempty := by
    intro p
    exact pairChoice_mem_pi_nonempty hFmem p
  let U := collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2)
  have hsupport : collisionSubfamilyPairSupport q U = S :=
    collisionSubfamilyPairSupport_pairChoiceUnion_eq
      (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub hne
  have hrank_ne : collisionSubfamilyGraphicRank (q := q) U ≠ 3 := by
    rw [collisionSubfamilyGraphicRank_eq_pairSupportGraphicRank (q := q) U]
    simpa [hsupport] using hSrank
  simp [U, hrank_ne]

/-- Fixed-support-cardinality rank-three coefficients reduce to exact supports
whose support graph itself has graphic rank three. -/
theorem rankThreeAlternatingCoefficientSupportCardEq_eq_sum_supportRankThree_noRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (m : Nat) :
    rankThreeAlternatingCoefficientSupportCardEqInt G q y m =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = m ∧ pairSupportGraphicRank q S = 3),
        rankThreePairSupportPiUnionCoefficientInt G q y S := by
  rw [rankThreeAlternatingCoefficientSupportCardEq_eq_sum_pairSupportEq]
  let A : Finset (Finset (PairIndex q)) :=
    (Finset.univ : Finset (Finset (PairIndex q))).filter (fun S => S.card = m)
  let fRank : Finset (PairIndex q) → ℤ := fun S =>
    rankThreeAlternatingCoefficientPairSupportEqInt G q y S
  let fNoRank : Finset (PairIndex q) → ℤ := fun S =>
    rankThreePairSupportPiUnionCoefficientInt G q y S
  have hpoint : ∀ S ∈ A,
      fRank S = if pairSupportGraphicRank q S = 3 then fNoRank S else 0 := by
    intro S _hS
    dsimp [fRank]
    rw [rankThreeAlternatingCoefficientPairSupportEqInt_eq_piUnionRank]
    by_cases hSrank : pairSupportGraphicRank q S = 3
    · rw [rankThreePairSupportPiUnionRankCoefficientInt_eq_noRank_of_pairSupportGraphicRank_eq_three
        (G := G) (q := q) (y := y) (S := S) hSrank]
      simp [fNoRank, hSrank]
    · rw [rankThreePairSupportPiUnionRankCoefficientInt_eq_zero_of_pairSupportGraphicRank_ne_three
        (G := G) (q := q) (y := y) (S := S) hSrank]
      simp [fNoRank, hSrank]
  change (∑ S ∈ A, fRank S) =
    ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
      (fun S => S.card = m ∧ pairSupportGraphicRank q S = 3), fNoRank S
  trans ∑ S ∈ A, if pairSupportGraphicRank q S = 3 then fNoRank S else 0
  · apply Finset.sum_congr rfl
    intro S hS
    exact hpoint S hS
  · rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext S
      simp [A]
    · intro S _hS
      rfl

/-- Support-cardinality-three rank-three coefficients reduce to exact supports
whose support graph itself has graphic rank three.  This is the size-three
boundary after triangle supports have been excluded by the rank filter. -/
theorem rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_supportRankThree_noRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankThreeAlternatingCoefficientSupportCardEqInt G q y 3 =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = 3 ∧ pairSupportGraphicRank q S = 3),
        rankThreePairSupportPiUnionCoefficientInt G q y S := by
  exact rankThreeAlternatingCoefficientSupportCardEq_eq_sum_supportRankThree_noRank
    (G := G) (q := q) (y := y) (m := 3)

/-- Support-size-three rank-three supports have factorizing cycle consistency.
This is the remaining graph-label obligation needed to turn the exact
support-size-three rank-three layer into a product of pair-local coefficients. -/
def RankThreeSupportCardThreeCycleConsistentFactors
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat) : Prop :=
  ∀ (y : Fin q → G) (S : Finset (PairIndex q)),
    S.card = 3 → pairSupportGraphicRank q S = 3 →
      PairSupportCycleConsistentFactors G y S

/-- If the exact support-size-three rank-three supports have factorizing cycle
consistency, the whole support-size-three rank-three coefficient is a sum of
product-form local coefficients. -/
theorem rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_product
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G)
    (hfactor : RankThreeSupportCardThreeCycleConsistentFactors G q) :
    rankThreeAlternatingCoefficientSupportCardEqInt G q y 3 =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = 3 ∧ pairSupportGraphicRank q S = 3),
        rankTwoPairSupportProductCoefficientInt G q y S := by
  rw [rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_supportRankThree_noRank]
  apply Finset.sum_congr rfl
  intro S hS
  have hmem := (Finset.mem_filter.mp hS).2
  rw [show rankThreePairSupportPiUnionCoefficientInt G q y S =
      rankTwoPairSupportPiUnionCoefficientInt G q y S by rfl]
  exact rankTwoPairSupportPiUnionCoefficientInt_eq_product_of_cycleConsistentFactors
    (G := G) (q := q) (y := y) (S := S) (hfactor y S hmem.1 hmem.2)

/-- Under the same factorization obligation, the support-size-three rank-three
coefficient is a sum of products of the explicit pair-local collision
coefficients. -/
theorem rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_pairCollisionProduct
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G)
    (hfactor : RankThreeSupportCardThreeCycleConsistentFactors G q) :
    rankThreeAlternatingCoefficientSupportCardEqInt G q y 3 =
      ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
          (fun S => S.card = 3 ∧ pairSupportGraphicRank q S = 3),
        ∏ p ∈ S, pairCollisionCoefficientInt G q y p := by
  rw [rankThreeAlternatingCoefficientSupportCardEq_three_eq_sum_product
    (hfactor := hfactor)]
  apply Finset.sum_congr rfl
  intro S _hS
  exact rankTwoPairSupportProductCoefficientInt_eq_prod_pairCollisionCoefficientInt G q y S

/-- A visible fiber forcing two query-pair collisions has exactly two degrees
of freedom removed. -/
theorem pairPairCollisionFiberCard_eq_card_pow_of_card_eq_two
    (G : Type*) [Fintype G] [DecidableEq G] {q : Nat}
    {S : Finset (PairIndex q)} (hS : S.card = 2) :
    pairPairCollisionFiberCard G S = Fintype.card G ^ (q - 2) := by
  rw [pairPairCollisionFiberCard_eq_componentConstant_card (G := G) (q := q) S]
  rw [card_collisionSubfamilyComponentConstant (G := G) (q := q)
    (collisionPairSupportHiddenRepresentative (q := q) S)]
  have hrank :
      collisionSubfamilyGraphicRank (q := q)
        (collisionPairSupportHiddenRepresentative (q := q) S) = 2 := by
    exact rankTwoPairSupportRankAutomatic q
      (collisionPairSupportHiddenRepresentative (q := q) S) (by
        rw [collisionSubfamilyPairSupport_hiddenRepresentative, hS])
  rw [collisionSubfamilyComponentCount_eq_query_sub_graphicRank
    (q := q) (collisionPairSupportHiddenRepresentative (q := q) S), hrank]

/-- Every two-pair visible-collision fiber has the uniform cardinality
`|G|^(q-2)`. -/
theorem pairPairCollisionFiberUniform
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    PairPairCollisionFiberUniform G q := by
  intro S hS
  exact pairPairCollisionFiberCard_eq_card_pow_of_card_eq_two (G := G) (q := q)
    (S := S) (Finset.mem_powersetCard.mp hS).2

/-- Closed second factorial moment of the visible pair-collision count. -/
theorem uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq_closed
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) :
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y => ((pairCollisionCountNat G q y).choose 2 : ℝ)) =
      ((Fintype.card (PairIndex q)).choose 2 : ℝ) /
        (Fintype.card G : ℝ) ^ 2 :=
  uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq
    (G := G) (q := q) hq2 (pairPairCollisionFiberUniform G q)

/-- The general rank-versus-support-cardinality inequality implies exact
two-pair rank automaticity.  The lower bound uses the already-formalized
rank-zero and rank-one exclusions. -/
theorem RankTwoPairSupportRankAutomatic.of_graphicRank_le_pairSupportCard
    {q : Nat} (hle : GraphicRankLePairSupportCard q) :
    RankTwoPairSupportRankAutomatic q := by
  intro T hsupport
  have hle_rank : collisionSubfamilyGraphicRank (q := q) T ≤ 2 := by
    rw [← hsupport]
    exact hle T
  have hne : T.Nonempty := by
    by_contra hempty
    have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    subst T
    simp [collisionSubfamilyPairSupport] at hsupport
  have hpos : 0 < collisionSubfamilyGraphicRank (q := q) T :=
    collisionSubfamilyGraphicRank_pos_of_nonempty (q := q) hne
  by_contra hnot
  have hrank_one : collisionSubfamilyGraphicRank (q := q) T = 1 := by omega
  have hsupport_one :
      (collisionSubfamilyPairSupport q T).card = 1 :=
    collisionSubfamilyPairSupport_card_eq_one_of_graphicRank_eq_one (q := q) hrank_one
  omega

/-- Under rank automaticity, the exact-support rank-two coefficient can drop its
explicit rank test on two-element supports. -/
theorem rankTwoAlternatingCoefficientPairSupportEqInt_eq_noRank_of_rankAutomatic
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q))
    (hrankAuto : RankTwoPairSupportRankAutomatic q)
    (hS : S.card = 2) :
    rankTwoAlternatingCoefficientPairSupportEqInt G q y S =
      rankTwoAlternatingCoefficientPairSupportEqNoRankInt G q y S := by
  unfold rankTwoAlternatingCoefficientPairSupportEqInt
    rankTwoAlternatingCoefficientPairSupportEqNoRankInt
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter] at hT
  have hsupport_card : (collisionSubfamilyPairSupport q T).card = 2 := by
    rw [hT.2, hS]
  have hrank : collisionSubfamilyGraphicRank (q := q) T = 2 :=
    hrankAuto T hsupport_card
  simp [hrank]

/-- Exact-support rank automaticity for one fixed query-pair support is enough
to drop the rank test on that exact-support coefficient. -/
theorem rankTwoAlternatingCoefficientPairSupportEqInt_eq_noRank_of_pairSupport
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (S : Finset (PairIndex q))
    (hrankAuto : ∀ T : Finset (CollisionEvent q),
      collisionSubfamilyPairSupport q T = S →
        collisionSubfamilyGraphicRank (q := q) T = 2) :
    rankTwoAlternatingCoefficientPairSupportEqInt G q y S =
      rankTwoAlternatingCoefficientPairSupportEqNoRankInt G q y S := by
  unfold rankTwoAlternatingCoefficientPairSupportEqInt
    rankTwoAlternatingCoefficientPairSupportEqNoRankInt
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter] at hT
  have hrank : collisionSubfamilyGraphicRank (q := q) T = 2 :=
    hrankAuto T hT.2
  simp [hrank]

/-- The rank-two alternating coefficient restricted to subfamilies whose
query-pair support has cardinality at least `m`. -/
def rankTwoAlternatingCoefficientSupportCardGeInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (m : Nat) : ℤ :=
  ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
    collisionSubfamilyGraphicRank (q := q) T = 2,
    if m ≤ (collisionSubfamilyPairSupport q T).card then
      if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
        (-1 : ℤ) ^ T.card
      else
        0
    else
      0

/-- Exact support-size decomposition of the rank-two alternating coefficient.
The proved lower bound `2 <= pairSupport.card` leaves only support sizes `2`,
`3`, and `>= 4`.  The desired upper-bound half of rank-two classification is
equivalent to showing the last summand vanishes. -/
theorem rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three_add_ge_four
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoAlternatingCoefficientInt G q y =
      rankTwoAlternatingCoefficientSupportCardEqInt G q y 2 +
        rankTwoAlternatingCoefficientSupportCardEqInt G q y 3 +
        rankTwoAlternatingCoefficientSupportCardGeInt G q y 4 := by
  unfold rankTwoAlternatingCoefficientInt
    rankTwoAlternatingCoefficientSupportCardEqInt
    rankTwoAlternatingCoefficientSupportCardGeInt
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  simp only [Finset.mem_filter] at hT
  have htwo :
      2 ≤ (collisionSubfamilyPairSupport q T).card :=
    collisionSubfamilyPairSupport_two_le_of_graphicRank_eq_two (q := q) hT.2
  by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
  · by_cases h2 : (collisionSubfamilyPairSupport q T).card = 2
    · simp [hcyc, h2]
    · by_cases h3 : (collisionSubfamilyPairSupport q T).card = 3
      · simp [hcyc, h3]
      · have h4 : 4 ≤ (collisionSubfamilyPairSupport q T).card := by omega
        simp [hcyc, h2, h3, h4]
  · simp [hcyc]

/-- Pure graph obligation for the remaining rank-two support classification:
every graphic-rank-two collision-event subfamily touches at most three query
pairs.  This is deliberately independent of the group and the transcript
values; it is the graph-theoretic endpoint needed to remove the
support-cardinality `>= 4` rank-two summand. -/
def RankTwoPairSupportUpperBound (q : Nat) : Prop :=
  ∀ T : Finset (CollisionEvent q),
    collisionSubfamilyGraphicRank (q := q) T = 2 →
      (collisionSubfamilyPairSupport q T).card ≤ 3

/-- Component-cardinality form of the rank-two graph endpoint: the union of
component-internal query-pair sets has at most three pairs. -/
def RankTwoComponentPairUnionBound (q : Nat) : Prop :=
  ∀ T : Finset (CollisionEvent q),
    collisionSubfamilyGraphicRank (q := q) T = 2 →
      ((Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
        (fun c => collisionSubfamilyComponentPairSet (q := q) T c)).card ≤ 3

/-- Local component-pair counting obligation: within each connected component,
the number of internal query pairs is bounded by choosing two vertices of that
component. -/
def ComponentPairSetChooseBound (q : Nat) : Prop :=
  ∀ (T : Finset (CollisionEvent q)) (c : collisionSubfamilyComponent (q := q) T),
    (collisionSubfamilyComponentPairSet (q := q) T c).card ≤
      (collisionSubfamilyComponentVertexSet (q := q) T c).card.choose 2

/-- The local component-pair counting obligation holds by injecting each
component-internal query pair into the two-element subset of its endpoints. -/
theorem componentPairSetChooseBound (q : Nat) :
    ComponentPairSetChooseBound q := by
  intro T c
  exact collisionSubfamilyComponentPairSet_card_le_choose (q := q) T c

/-- Pure finite-partition arithmetic endpoint for rank two: the component
vertex blocks have total internal-pair capacity at most three. -/
def RankTwoComponentChooseSumBound (q : Nat) : Prop :=
  ∀ T : Finset (CollisionEvent q),
    collisionSubfamilyGraphicRank (q := q) T = 2 →
      (∑ c : collisionSubfamilyComponent (q := q) T,
        (collisionSubfamilyComponentVertexSet (q := q) T c).card.choose 2) ≤ 3

/-- Final arithmetic form of the rank-two component-size bound.  The component
vertex sets are already known to be nonempty and to have total excess equal to
the graphic rank; this obligation is the remaining finite arithmetic statement:
if the total excess is two, then the sum of internal pair capacities is at most
three. -/
def ComponentChooseSumBoundFromExcessTwo (q : Nat) : Prop :=
  ∀ T : Finset (CollisionEvent q),
    (∑ c : collisionSubfamilyComponent (q := q) T,
      ((collisionSubfamilyComponentVertexSet (q := q) T c).card - 1)) = 2 →
      (∑ c : collisionSubfamilyComponent (q := q) T,
        (collisionSubfamilyComponentVertexSet (q := q) T c).card.choose 2) ≤ 3

/-- The excess-two arithmetic statement implies the rank-two component choose
sum bound, because the component-excess sum is the graphic rank. -/
theorem RankTwoComponentChooseSumBound.of_excessTwo
    {q : Nat} (hexcess : ComponentChooseSumBoundFromExcessTwo q) :
    RankTwoComponentChooseSumBound q := by
  intro T hrank
  apply hexcess T
  rw [sum_componentVertexSet_card_sub_one_eq_graphicRank (q := q) T, hrank]

/-- Pointwise arithmetic used in the rank-two component-size endpoint: once a
component's excess `n - 1` is at most two, twice its internal pair capacity is
bounded by three times its excess. -/
theorem two_mul_choose_two_le_three_mul_sub_one_of_sub_one_le_two
    (n : Nat) (h : n - 1 ≤ 2) :
    2 * n.choose 2 ≤ 3 * (n - 1) := by
  have hn : n ≤ 3 := by omega
  interval_cases n <;> norm_num

/-- When a component has at most two vertices, its internal pair capacity is at
most its component excess. -/
theorem choose_two_le_sub_one_of_le_two (n : Nat) (hn : n ≤ 2) :
    n.choose 2 ≤ n - 1 := by
  interval_cases n <;> norm_num

/-- Finite arithmetic core of the rank-two support classification.  A finite
family of nonnegative component excesses summing to two has total internal-pair
capacity at most three. -/
theorem sum_choose_two_le_three_of_sum_sub_one_eq_two
    {ι : Type*} [Fintype ι] (n : ι → Nat)
    (hsum : (∑ i, (n i - 1)) = 2) :
    (∑ i, (n i).choose 2) ≤ 3 := by
  have hpoint : ∀ i, 2 * (n i).choose 2 ≤ 3 * (n i - 1) := by
    intro i
    apply two_mul_choose_two_le_three_mul_sub_one_of_sub_one_le_two
    rw [← hsum]
    exact Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun j => n j - 1)
      (fun _j _hj => Nat.zero_le _)
      (Finset.mem_univ i)
  have hsumineq :
      (∑ i, 2 * (n i).choose 2) ≤ (∑ i, 3 * (n i - 1)) := by
    exact Finset.sum_le_sum (fun i _hi => hpoint i)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsumineq
  rw [hsum] at hsumineq
  omega

/-- The component-excess arithmetic endpoint holds for every rank-two support
graph. -/
theorem componentChooseSumBoundFromExcessTwo (q : Nat) :
    ComponentChooseSumBoundFromExcessTwo q := by
  intro T hsum
  exact sum_choose_two_le_three_of_sum_sub_one_eq_two
    (fun c : collisionSubfamilyComponent (q := q) T =>
      (collisionSubfamilyComponentVertexSet (q := q) T c).card)
    hsum

/-- The rank-two component choose-sum bound is now unconditional. -/
theorem rankTwoComponentChooseSumBound (q : Nat) :
    RankTwoComponentChooseSumBound q := by
  exact RankTwoComponentChooseSumBound.of_excessTwo
    (componentChooseSumBoundFromExcessTwo q)

/-- The local component-pair count and rank-two component arithmetic imply the
component-union graph endpoint. -/
theorem RankTwoComponentPairUnionBound.of_componentChooseBounds
    {q : Nat}
    (hpair : ComponentPairSetChooseBound q)
    (hsum : RankTwoComponentChooseSumBound q) :
    RankTwoComponentPairUnionBound q := by
  intro T hrank
  calc
    ((Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
        (fun c => collisionSubfamilyComponentPairSet (q := q) T c)).card ≤
        ∑ c : collisionSubfamilyComponent (q := q) T,
          (collisionSubfamilyComponentPairSet (q := q) T c).card := by
          simpa using (Finset.card_biUnion_le
            (s := (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)))
            (t := fun c => collisionSubfamilyComponentPairSet (q := q) T c))
    _ ≤ ∑ c : collisionSubfamilyComponent (q := q) T,
          (collisionSubfamilyComponentVertexSet (q := q) T c).card.choose 2 := by
          exact Finset.sum_le_sum (fun c _hc => hpair T c)
    _ ≤ 3 := hsum T hrank

/-- After the local component-pair count is discharged, only the rank-two
component-size arithmetic remains. -/
theorem RankTwoComponentPairUnionBound.of_componentChooseSumBound
    {q : Nat} (hsum : RankTwoComponentChooseSumBound q) :
    RankTwoComponentPairUnionBound q :=
  RankTwoComponentPairUnionBound.of_componentChooseBounds
    (componentPairSetChooseBound q) hsum

/-- The rank-two component-union graph endpoint is now unconditional. -/
theorem rankTwoComponentPairUnionBound (q : Nat) :
    RankTwoComponentPairUnionBound q := by
  exact RankTwoComponentPairUnionBound.of_componentChooseSumBound
    (rankTwoComponentChooseSumBound q)

/-- The component-union cardinality bound implies the original pair-support
upper bound, because pair support is contained in the component-internal
pair union. -/
theorem RankTwoPairSupportUpperBound.of_componentPairUnionBound
    {q : Nat} (hbound : RankTwoComponentPairUnionBound q) :
    RankTwoPairSupportUpperBound q := by
  intro T hrank
  exact (Finset.card_le_card
    (collisionSubfamilyPairSupport_subset_biUnion_componentPairSet (q := q) T)).trans
      (hbound T hrank)

/-- The pure graph rank-two pair-support endpoint is now unconditional:
graphic-rank-two collision-event subfamilies touch at most three query pairs. -/
theorem rankTwoPairSupportUpperBound (q : Nat) :
    RankTwoPairSupportUpperBound q := by
  exact RankTwoPairSupportUpperBound.of_componentPairUnionBound
    (rankTwoComponentPairUnionBound q)

/-- If a rank-two support touches three query pairs, then it fills the whole
component-internal pair union.  This is the first graph-classification step
toward identifying support-cardinality-three terms with triangles. -/
theorem collisionSubfamilyPairSupport_eq_componentPairUnion_of_graphicRank_eq_two_card_eq_three
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 2)
    (hcard : (collisionSubfamilyPairSupport q T).card = 3) :
    collisionSubfamilyPairSupport q T =
      (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
        (fun c => collisionSubfamilyComponentPairSet (q := q) T c) := by
  apply Finset.eq_of_subset_of_card_le
    (collisionSubfamilyPairSupport_subset_biUnion_componentPairSet (q := q) T)
  have hbound := rankTwoComponentPairUnionBound q T hrank
  simpa [hcard] using hbound

/-- A rank-two support touching three query pairs has a component on exactly
three query coordinates.  Otherwise every component has at most two vertices,
so the total internal pair capacity is at most the rank-two excess `2`, which
cannot contain three touched query pairs. -/
theorem exists_componentVertexSet_card_three_of_graphicRank_eq_two_pairSupport_card_three
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 2)
    (hcard : (collisionSubfamilyPairSupport q T).card = 3) :
    ∃ c : collisionSubfamilyComponent (q := q) T,
      (collisionSubfamilyComponentVertexSet (q := q) T c).card = 3 := by
  by_contra hnot
  have hsum :
      (∑ c : collisionSubfamilyComponent (q := q) T,
        ((collisionSubfamilyComponentVertexSet (q := q) T c).card - 1)) = 2 := by
    rw [sum_componentVertexSet_card_sub_one_eq_graphicRank (q := q) T, hrank]
  have hcard_le_two :
      ∀ c : collisionSubfamilyComponent (q := q) T,
        (collisionSubfamilyComponentVertexSet (q := q) T c).card ≤ 2 := by
    intro c
    have hexcess_le :
        (collisionSubfamilyComponentVertexSet (q := q) T c).card - 1 ≤ 2 := by
      rw [← hsum]
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)))
        (f := fun d => (collisionSubfamilyComponentVertexSet (q := q) T d).card - 1)
        (fun _d _hd => Nat.zero_le _)
        (Finset.mem_univ c)
    have hle_three : (collisionSubfamilyComponentVertexSet (q := q) T c).card ≤ 3 := by
      omega
    by_contra hgt
    have hge_three : 3 ≤ (collisionSubfamilyComponentVertexSet (q := q) T c).card := by
      omega
    have heq_three : (collisionSubfamilyComponentVertexSet (q := q) T c).card = 3 := by
      omega
    exact hnot ⟨c, heq_three⟩
  have hchoose_le :
      (∑ c : collisionSubfamilyComponent (q := q) T,
        (collisionSubfamilyComponentVertexSet (q := q) T c).card.choose 2) ≤ 2 := by
    calc
      (∑ c : collisionSubfamilyComponent (q := q) T,
        (collisionSubfamilyComponentVertexSet (q := q) T c).card.choose 2) ≤
          ∑ c : collisionSubfamilyComponent (q := q) T,
            ((collisionSubfamilyComponentVertexSet (q := q) T c).card - 1) := by
            exact Finset.sum_le_sum (fun c _hc =>
              choose_two_le_sub_one_of_le_two
                (collisionSubfamilyComponentVertexSet (q := q) T c).card
                (hcard_le_two c))
      _ = 2 := hsum
  have hsupport_subset :=
    collisionSubfamilyPairSupport_subset_biUnion_componentPairSet (q := q) T
  have hsupport_card_le_union :
      (collisionSubfamilyPairSupport q T).card ≤
        ((Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
          (fun c => collisionSubfamilyComponentPairSet (q := q) T c)).card :=
    Finset.card_le_card hsupport_subset
  have hunion_le_two :
      ((Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
        (fun c => collisionSubfamilyComponentPairSet (q := q) T c)).card ≤ 2 := by
    calc
      ((Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
        (fun c => collisionSubfamilyComponentPairSet (q := q) T c)).card ≤
          ∑ c : collisionSubfamilyComponent (q := q) T,
            (collisionSubfamilyComponentPairSet (q := q) T c).card := by
            simpa using (Finset.card_biUnion_le
              (s := (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)))
              (t := fun c => collisionSubfamilyComponentPairSet (q := q) T c))
      _ ≤ ∑ c : collisionSubfamilyComponent (q := q) T,
            (collisionSubfamilyComponentVertexSet (q := q) T c).card.choose 2 := by
            exact Finset.sum_le_sum (fun c _hc =>
              collisionSubfamilyComponentPairSet_card_le_choose (q := q) T c)
      _ ≤ 2 := hchoose_le
  omega

/-- In a rank-two support graph, once one component has three vertices, every
other component is a singleton. -/
theorem collisionSubfamilyComponentVertexSet_card_eq_one_of_graphicRank_eq_two_of_ne_card_three
    {q : Nat} {T : Finset (CollisionEvent q)}
    {c₀ c : collisionSubfamilyComponent (q := q) T}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 2)
    (hc₀ : (collisionSubfamilyComponentVertexSet (q := q) T c₀).card = 3)
    (hne : c ≠ c₀) :
    (collisionSubfamilyComponentVertexSet (q := q) T c).card = 1 := by
  have hsum :
      (∑ d : collisionSubfamilyComponent (q := q) T,
        ((collisionSubfamilyComponentVertexSet (q := q) T d).card - 1)) = 2 := by
    rw [sum_componentVertexSet_card_sub_one_eq_graphicRank (q := q) T, hrank]
  have hc₀excess :
      (collisionSubfamilyComponentVertexSet (q := q) T c₀).card - 1 = 2 := by
    omega
  have hc_nonempty :
      0 < (collisionSubfamilyComponentVertexSet (q := q) T c).card :=
    Finset.card_pos.mpr (collisionSubfamilyComponentVertexSet_nonempty (q := q) T c)
  by_contra hnot
  have hc_excess_pos :
      1 ≤ (collisionSubfamilyComponentVertexSet (q := q) T c).card - 1 := by
    omega
  have hc_mem_erase :
      c ∈ (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).erase c₀ := by
    simp [hne]
  have herase_lower :
      1 ≤ ∑ d ∈ (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).erase c₀,
        ((collisionSubfamilyComponentVertexSet (q := q) T d).card - 1) := by
    exact hc_excess_pos.trans
      (Finset.single_le_sum
        (s := (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).erase c₀)
        (f := fun d => (collisionSubfamilyComponentVertexSet (q := q) T d).card - 1)
        (fun _d _hd => Nat.zero_le _)
        hc_mem_erase)
  have hsum_split :
      (∑ d : collisionSubfamilyComponent (q := q) T,
        ((collisionSubfamilyComponentVertexSet (q := q) T d).card - 1)) =
      (∑ d ∈ (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).erase c₀,
        ((collisionSubfamilyComponentVertexSet (q := q) T d).card - 1)) +
        ((collisionSubfamilyComponentVertexSet (q := q) T c₀).card - 1) := by
    simpa [Finset.sdiff_singleton_eq_erase] using
      (Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ c₀)
        (fun d : collisionSubfamilyComponent (q := q) T =>
          (collisionSubfamilyComponentVertexSet (q := q) T d).card - 1))
  rw [hsum_split, hc₀excess] at hsum
  omega

/-- In a rank-two support graph with a three-vertex component, the union of all
component-internal query-pair sets is exactly the pair set of that component. -/
theorem collisionSubfamilyComponentPairUnion_eq_componentPairSet_of_graphicRank_eq_two_card_three
    {q : Nat} {T : Finset (CollisionEvent q)}
    {c₀ : collisionSubfamilyComponent (q := q) T}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 2)
    (hc₀ : (collisionSubfamilyComponentVertexSet (q := q) T c₀).card = 3) :
    (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).biUnion
        (fun c => collisionSubfamilyComponentPairSet (q := q) T c) =
      collisionSubfamilyComponentPairSet (q := q) T c₀ := by
  ext p
  constructor
  · intro hp
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨c, hpc⟩
    by_cases hc : c = c₀
    · simpa [hc] using hpc
    · have hcard_one :
          (collisionSubfamilyComponentVertexSet (q := q) T c).card = 1 :=
        collisionSubfamilyComponentVertexSet_card_eq_one_of_graphicRank_eq_two_of_ne_card_three
          (q := q) (T := T) (c₀ := c₀) (c := c) hrank hc₀ hc
      have hempty :
          collisionSubfamilyComponentPairSet (q := q) T c = ∅ :=
        collisionSubfamilyComponentPairSet_eq_empty_of_vertexSet_card_le_one
          (q := q) (T := T) (c := c) (by omega)
      rw [hempty] at hpc
      simp at hpc
  · intro hp
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨c₀, hp⟩

/-- A rank-two support touching three query pairs is exactly the set of query
pairs internal to one three-vertex component. -/
theorem exists_component_card_three_pairSupport_eq_componentPairSet_of_graphicRank_eq_two_card_three
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 2)
    (hcard : (collisionSubfamilyPairSupport q T).card = 3) :
    ∃ c : collisionSubfamilyComponent (q := q) T,
      (collisionSubfamilyComponentVertexSet (q := q) T c).card = 3 ∧
      collisionSubfamilyPairSupport q T =
        collisionSubfamilyComponentPairSet (q := q) T c := by
  rcases exists_componentVertexSet_card_three_of_graphicRank_eq_two_pairSupport_card_three
      (q := q) (T := T) hrank hcard with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  rw [collisionSubfamilyPairSupport_eq_componentPairUnion_of_graphicRank_eq_two_card_eq_three
    (q := q) (T := T) hrank hcard]
  rw [collisionSubfamilyComponentPairUnion_eq_componentPairSet_of_graphicRank_eq_two_card_three
    (q := q) (T := T) (c₀ := c) hrank hc]

/-- Component-free version of the three-pair rank-two support classification:
such a support is `queryPairSet V` for a three-element vertex set `V`. -/
theorem exists_vertexSet_card_three_pairSupport_eq_queryPairSet_of_graphicRank_eq_two_card_three
    {q : Nat} {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 2)
    (hcard : (collisionSubfamilyPairSupport q T).card = 3) :
    ∃ V : Finset (Fin q), V.card = 3 ∧
      collisionSubfamilyPairSupport q T = queryPairSet V := by
  rcases exists_component_card_three_pairSupport_eq_componentPairSet_of_graphicRank_eq_two_card_three
      (q := q) (T := T) hrank hcard with ⟨c, hc, hsupport⟩
  exact ⟨collisionSubfamilyComponentVertexSet (q := q) T c, hc, hsupport⟩

/-- A query-pair support is a triangle support when it is exactly the set of
all query pairs internal to some three-coordinate vertex set. -/
def IsQueryTriangleSupport {q : Nat} (S : Finset (PairIndex q)) : Prop :=
  ∃ V : Finset (Fin q), V.card = 3 ∧ S = queryPairSet V

/-- Three-coordinate vertex sets. -/
noncomputable def queryTriangleVertexSet (q : Nat) : Finset (Finset (Fin q)) := by
  classical
  exact (Finset.univ : Finset (Finset (Fin q))).filter (fun V => V.card = 3)

/-- Query-pair supports that are genuine three-coordinate triangle supports. -/
noncomputable def queryTriangleSupportSet (q : Nat) : Finset (Finset (PairIndex q)) := by
  classical
  exact (Finset.univ : Finset (Finset (PairIndex q))).filter
    (fun S => S.card = 3 ∧ IsQueryTriangleSupport S)

/-- Triangle supports have support cardinality three. -/
theorem IsQueryTriangleSupport.card_eq_three
    {q : Nat} {S : Finset (PairIndex q)}
    (hS : IsQueryTriangleSupport S) :
    S.card = 3 := by
  rcases hS with ⟨V, hV, rfl⟩
  exact queryPairSet_card_eq_three_of_card_eq_three hV

/-- Genuine triangle supports are exactly the image of three-coordinate vertex
sets under `queryPairSet`. -/
theorem queryTriangleSupportSet_eq_image_queryPairSet (q : Nat) :
    queryTriangleSupportSet q =
      (queryTriangleVertexSet q).image (fun V => queryPairSet V) := by
  classical
  ext S
  constructor
  · intro hS
    simp only [queryTriangleSupportSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hS
    rcases hS.2 with ⟨V, hV, rfl⟩
    exact Finset.mem_image.mpr
      ⟨V, by
        simp only [queryTriangleVertexSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hV, rfl⟩
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨V, hV, hSV⟩
    subst S
    simp only [queryTriangleVertexSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hV
    simp only [queryTriangleSupportSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨queryPairSet_card_eq_three_of_card_eq_three hV, ⟨V, hV, rfl⟩⟩

/-- Exact three-pair supports that are not triangle supports carry no rank-two
mass.  This is the support-filtering step before evaluating the local triangle
coefficient. -/
theorem rankTwoAlternatingCoefficientPairSupportEqInt_eq_zero_of_not_triangleSupport
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    {q : Nat} (y : Fin q → G) {S : Finset (PairIndex q)}
    (hS_card : S.card = 3) (hnot : ¬ IsQueryTriangleSupport S) :
    rankTwoAlternatingCoefficientPairSupportEqInt G q y S = 0 := by
  unfold rankTwoAlternatingCoefficientPairSupportEqInt
  apply Finset.sum_eq_zero
  intro T hT
  simp only [Finset.mem_filter] at hT
  by_cases hrank : collisionSubfamilyGraphicRank (q := q) T = 2
  · have hsupport_card : (collisionSubfamilyPairSupport q T).card = 3 := by
      rw [hT.2, hS_card]
    rcases exists_vertexSet_card_three_pairSupport_eq_queryPairSet_of_graphicRank_eq_two_card_three
        (q := q) (T := T) hrank hsupport_card with ⟨V, hV, hsupport⟩
    exfalso
    apply hnot
    exact ⟨V, hV, by rw [← hT.2, hsupport]⟩
  · simp [hrank]

/-- The support-cardinality-three coefficient after deleting exact supports that
are not genuine query triangles. -/
noncomputable def rankTwoTriangleSupportFilteredCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℤ := by
  classical
  exact
    ∑ S ∈ queryTriangleSupportSet q,
      rankTwoAlternatingCoefficientPairSupportEqInt G q y S

/-- The support-cardinality-three coefficient indexed directly by
three-coordinate vertex sets. -/
noncomputable def rankTwoTriangleVertexSupportCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℤ := by
  classical
  exact
    ∑ V ∈ queryTriangleVertexSet q,
      rankTwoAlternatingCoefficientPairSupportEqInt G q y (queryPairSet V)

/-- The triangle-support layer after reindexing each exact triangle support by
its three pair-local nonempty fibers, while retaining the rank test. -/
noncomputable def rankTwoTriangleVertexPiUnionRankCoefficientInt
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℤ := by
  classical
  exact
    ∑ V ∈ queryTriangleVertexSet q,
      rankTwoPairSupportPiUnionRankCoefficientInt G q y (queryPairSet V)

/-- Vertex-indexed triangle coefficients can be rewritten pointwise into the
rank-retaining pair-fiber choice form.  This is the global triangle-layer
handoff to the local three-fiber calculation. -/
theorem rankTwoTriangleVertexSupportCoefficientInt_eq_piUnionRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoTriangleVertexSupportCoefficientInt G q y =
      rankTwoTriangleVertexPiUnionRankCoefficientInt G q y := by
  unfold rankTwoTriangleVertexSupportCoefficientInt
    rankTwoTriangleVertexPiUnionRankCoefficientInt
  apply Finset.sum_congr rfl
  intro V _hV
  exact rankTwoAlternatingCoefficientPairSupportEqInt_eq_piUnionRank G q y (queryPairSet V)

/-- Local ranked pair-fiber form of the triangle correction.  This is the
remaining finite three-coordinate calculation: for each vertex triple `V`, the
rank-retaining pair-fiber choice sum over `queryPairSet V` should be `-2`,
except that the all-visible-equal case restores one unit. -/
def RankTwoTriangleVertexPiUnionRankIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) : Prop := by
  classical
  exact
    ∀ (y : Fin q → G) (V : Finset (Fin q)),
      V.card = 3 →
        rankTwoPairSupportPiUnionRankCoefficientInt G q y (queryPairSet V) =
          (-2 + (if visibleAllEqualOn G y V then 1 else 0) : ℤ)

/-- Exact triangle supports are rank automatic when every subfamily with pair
support `queryPairSet V` has graphic rank two.  This is the graph-only part of
the remaining local triangle calculation. -/
def RankTwoTriangleSupportRankAutomatic (q : Nat) : Prop :=
  ∀ T : Finset (CollisionEvent q), ∀ V : Finset (Fin q),
    V.card = 3 →
      collisionSubfamilyPairSupport q T = queryPairSet V →
        collisionSubfamilyGraphicRank (q := q) T = 2

/-- Exact triangle supports are graphic-rank automatic.  The support graph has
one component on the three vertices of `V`; every vertex outside `V` is
isolated because all touched query pairs are internal to `V`. -/
theorem rankTwoTriangleSupportRankAutomatic (q : Nat) :
    RankTwoTriangleSupportRankAutomatic q := by
  intro T V hV hsupport
  have hVnonempty : V.Nonempty := Finset.card_pos.mp (by omega)
  rcases hVnonempty with ⟨i, hi⟩
  let c₀ : collisionSubfamilyComponent (q := q) T :=
    Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) i
  have hc₀ : collisionSubfamilyComponentVertexSet (q := q) T c₀ = V :=
    collisionSubfamilyComponentVertexSet_eq_of_mem_of_pairSupport_eq_queryPairSet
      (q := q) (T := T) (S := V) hsupport (c := c₀) (i := i) rfl hi
  have hcard_c₀ : (collisionSubfamilyComponentVertexSet (q := q) T c₀).card = 3 := by
    rw [hc₀, hV]
  have hother_card :
      ∀ c : collisionSubfamilyComponent (q := q) T, c ≠ c₀ →
        (collisionSubfamilyComponentVertexSet (q := q) T c).card = 1 := by
    intro c hc_ne
    rcases collisionSubfamilyComponentVertexSet_nonempty (q := q) T c with ⟨j, hjc⟩
    have hj_not : j ∉ V := by
      intro hjV
      have hconn : collisionSubfamilyConnected (q := q) T i j :=
        collisionSubfamilyConnected_of_mem_of_mem_of_pairSupport_eq_queryPairSet
          (q := q) (T := T) (S := V) hsupport hi hjV
      have hc_eq : c₀ = c := by
        have hq : c₀ =
            Quotient.mk (collisionSubfamilyConnectedSetoid (q := q) T) j := by
          exact Quotient.sound (by
            simpa [collisionSubfamilyConnectedSetoid] using hconn)
        simp only [collisionSubfamilyComponentVertexSet, Finset.mem_filter,
          Finset.mem_univ, true_and] at hjc
        exact hq.trans hjc
      exact hc_ne hc_eq.symm
    have hsingleton :
        collisionSubfamilyComponentVertexSet (q := q) T c = {j} :=
      collisionSubfamilyComponentVertexSet_eq_singleton_of_not_mem_of_pairSupport_subset_queryPairSet
        (q := q) (T := T) (S := V) (by rw [hsupport]) (c := c) (i := j) (by
          simpa [collisionSubfamilyComponentVertexSet] using hjc) hj_not
    rw [hsingleton, Finset.card_singleton]
  have hsum :
      (∑ c : collisionSubfamilyComponent (q := q) T,
        ((collisionSubfamilyComponentVertexSet (q := q) T c).card - 1)) = 2 := by
    rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ c₀)]
    have herase_zero :
        (∑ c ∈ (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)).erase c₀,
          ((collisionSubfamilyComponentVertexSet (q := q) T c).card - 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      have hc_ne : c ≠ c₀ := by
        exact (Finset.mem_erase.mp hc).1
      rw [hother_card c hc_ne]
      omega
    have hdiff_zero :
        (∑ c ∈ (Finset.univ : Finset (collisionSubfamilyComponent (q := q) T)) \ {c₀},
          ((collisionSubfamilyComponentVertexSet (q := q) T c).card - 1)) = 0 := by
      simpa [Finset.sdiff_singleton_eq_erase] using herase_zero
    rw [hdiff_zero, hcard_c₀]
  rw [← sum_componentVertexSet_card_sub_one_eq_graphicRank (q := q) T]
  exact hsum

/-- Triangle query-pair supports have support graphic rank two.  This packages
the rank-automatic triangle-support theorem for the canonical hidden-event
representative used by `pairSupportGraphicRank`. -/
theorem pairSupportGraphicRank_eq_two_of_isQueryTriangleSupport
    {q : Nat} {S : Finset (PairIndex q)}
    (hS : IsQueryTriangleSupport S) :
    pairSupportGraphicRank q S = 2 := by
  rcases hS with ⟨V, hV, rfl⟩
  unfold pairSupportGraphicRank
  exact rankTwoTriangleSupportRankAutomatic q
    (collisionPairSupportHiddenRepresentative (q := q) (queryPairSet V)) V hV
    (collisionSubfamilyPairSupport_hiddenRepresentative (q := q) (queryPairSet V))

/-- Triangle query-pair supports never contribute to the rank-three layer. -/
theorem pairSupportGraphicRank_ne_three_of_isQueryTriangleSupport
    {q : Nat} {S : Finset (PairIndex q)}
    (hS : IsQueryTriangleSupport S) :
    pairSupportGraphicRank q S ≠ 3 := by
  rw [pairSupportGraphicRank_eq_two_of_isQueryTriangleSupport hS]
  norm_num

/-- Rank-three query-pair supports are not genuine three-coordinate triangle
supports. -/
theorem not_isQueryTriangleSupport_of_pairSupportGraphicRank_eq_three
    {q : Nat} {S : Finset (PairIndex q)}
    (hSrank : pairSupportGraphicRank q S = 3) :
    ¬ IsQueryTriangleSupport S := by
  intro htri
  exact pairSupportGraphicRank_ne_three_of_isQueryTriangleSupport htri hSrank

/-- Exact size-three supports that survive the rank-three support filter are not
rank-two triangle supports. -/
theorem not_isQueryTriangleSupport_of_mem_rankThree_supportCard_three_filter
    {q : Nat} {S : Finset (PairIndex q)}
    (hS : S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
        (fun S => S.card = 3 ∧ pairSupportGraphicRank q S = 3)) :
    ¬ IsQueryTriangleSupport S := by
  exact not_isQueryTriangleSupport_of_pairSupportGraphicRank_eq_three
    (q := q) (S := S) (Finset.mem_filter.mp hS).2.2

/-- No-rank local pair-fiber form of the triangle correction.  This is the
signed finite three-fiber calculation after the graph-rank test has been
removed. -/
def RankTwoTriangleVertexPiUnionNoRankIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) : Prop := by
  classical
  exact
    ∀ (y : Fin q → G) (V : Finset (Fin q)),
      V.card = 3 →
        rankTwoPairSupportPiUnionCoefficientInt G q y (queryPairSet V) =
          (-2 + (if visibleAllEqualOn G y V then 1 else 0) : ℤ)

/-- The no-rank local triangle identity.  This is the signed finite
three-fiber calculation for every equality pattern on the three visible
outputs: all equal contributes `-1`, while all distinct and each one-collision
placement contributes `-2`. -/
theorem rankTwoTriangleVertexPiUnionNoRankIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) :
    RankTwoTriangleVertexPiUnionNoRankIdentity G q := by
  classical
  intro y V hV
  rcases exists_orderedTriple_eq_of_card_eq_three (q := q) (V := V) hV with
    ⟨i, j, k, hij, hjk, rfl⟩
  have hik : i < k := hij.trans hjk
  have hVcard : ({i, j, k} : Finset (Fin q)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨i, j, k, ne_of_lt hij, ne_of_lt hik, ne_of_lt hjk, rfl⟩
  by_cases hij_eq : y j = y i
  · by_cases hjk_eq : y k = y j
    · have hall : visibleAllEqualOn G y ({i, j, k} : Finset (Fin q)) := by
        intro a ha b hb
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        all_goals try rfl
        · exact hij_eq.symm
        · exact (hjk_eq.trans hij_eq).symm
        · exact hij_eq
        · exact hjk_eq.symm
        · exact hjk_eq.trans hij_eq
        · exact hjk_eq
      rw [rankTwoPairSupportPiUnionCoefficientInt_eq_neg_one_of_visibleAllEqualOn
        (G := G) (q := q) y (V := ({i, j, k} : Finset (Fin q))) hVcard hall]
      rw [if_pos hall]
      norm_num
    · have hnot : ¬ visibleAllEqualOn G y ({i, j, k} : Finset (Fin q)) := by
        intro hall
        exact hjk_eq (hall k (by simp) j (by simp))
      rw [rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_left_visible_eq
        (G := G) (q := q) y hij hjk hij_eq hjk_eq]
      rw [if_neg hnot]
      norm_num
  · by_cases hjk_eq : y k = y j
    · have hnot : ¬ visibleAllEqualOn G y ({i, j, k} : Finset (Fin q)) := by
        intro hall
        exact hij_eq (hall j (by simp) i (by simp))
      rw [rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_right_visible_eq
        (G := G) (q := q) y hij hjk hjk_eq hij_eq]
      rw [if_neg hnot]
      norm_num
    · by_cases hik_eq : y k = y i
      · have hnot : ¬ visibleAllEqualOn G y ({i, j, k} : Finset (Fin q)) := by
          intro hall
          exact hij_eq (hall j (by simp) i (by simp))
        rw [rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_outer_visible_eq
          (G := G) (q := q) y hij hjk hik_eq hij_eq]
        rw [if_neg hnot]
        norm_num
      · have hnot : ¬ visibleAllEqualOn G y ({i, j, k} : Finset (Fin q)) := by
          intro hall
          exact hij_eq (hall j (by simp) i (by simp))
        rw [rankTwoPairSupportPiUnionCoefficientInt_eq_neg_two_of_orderedTriple_pairwise_visible_ne
          (G := G) (q := q) y hij hjk hij_eq hjk_eq hik_eq]
        rw [if_neg hnot]
        norm_num

/-- Triangle support rank automaticity plus the no-rank signed three-fiber
calculation imply the ranked local triangle identity. -/
theorem RankTwoTriangleVertexPiUnionRankIdentity.of_rankAutomatic_noRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (hrank : RankTwoTriangleSupportRankAutomatic q)
    (hnorank : RankTwoTriangleVertexPiUnionNoRankIdentity G q) :
    RankTwoTriangleVertexPiUnionRankIdentity G q := by
  classical
  intro y V hV
  calc
    rankTwoPairSupportPiUnionRankCoefficientInt G q y (queryPairSet V)
        = rankTwoAlternatingCoefficientPairSupportEqInt G q y (queryPairSet V) := by
            exact (rankTwoAlternatingCoefficientPairSupportEqInt_eq_piUnionRank
              G q y (queryPairSet V)).symm
    _ = rankTwoAlternatingCoefficientPairSupportEqNoRankInt G q y (queryPairSet V) := by
            exact rankTwoAlternatingCoefficientPairSupportEqInt_eq_noRank_of_pairSupport
              (G := G) (q := q) (y := y) (S := queryPairSet V)
              (fun T hsupport => hrank T V hV hsupport)
    _ = rankTwoPairSupportPiUnionCoefficientInt G q y (queryPairSet V) := by
            exact rankTwoAlternatingCoefficientPairSupportEqNoRankInt_eq_piUnion
              G q y (queryPairSet V)
    _ = (-2 + (if visibleAllEqualOn G y V then 1 else 0) : ℤ) :=
            hnorank y V hV

/-- Since triangle-support rank automaticity is now unconditional, the ranked
local triangle identity is reduced to the no-rank signed three-fiber
calculation. -/
theorem RankTwoTriangleVertexPiUnionRankIdentity.of_noRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (hnorank : RankTwoTriangleVertexPiUnionNoRankIdentity G q) :
    RankTwoTriangleVertexPiUnionRankIdentity G q :=
  RankTwoTriangleVertexPiUnionRankIdentity.of_rankAutomatic_noRank
    (G := G) (q := q) (rankTwoTriangleSupportRankAutomatic q) hnorank

/-- The ranked local triangle identity is now unconditional. -/
theorem rankTwoTriangleVertexPiUnionRankIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) :
    RankTwoTriangleVertexPiUnionRankIdentity G q :=
  RankTwoTriangleVertexPiUnionRankIdentity.of_noRank
    (G := G) (q := q) (rankTwoTriangleVertexPiUnionNoRankIdentity G q)

/-- Sum-level support filter for the triangle layer: after regrouping by exact
three-pair support, only supports of the form `queryPairSet V` for a
three-coordinate set `V` can contribute. -/
theorem rankTwoAlternatingCoefficientSupportCardEq_three_eq_sum_triangleSupport
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoAlternatingCoefficientSupportCardEqInt G q y 3 =
      rankTwoTriangleSupportFilteredCoefficientInt G q y := by
  classical
  rw [rankTwoAlternatingCoefficientSupportCardEq_three_eq_sum_pairSupportEq]
  trans ∑ S ∈ (Finset.univ : Finset (Finset (PairIndex q))).filter
      (fun S => S.card = 3),
      if IsQueryTriangleSupport S then
        rankTwoAlternatingCoefficientPairSupportEqInt G q y S
      else
        0
  · apply Finset.sum_congr rfl
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    by_cases htri : IsQueryTriangleSupport S
    · simp [htri]
    · have hzero :=
        rankTwoAlternatingCoefficientPairSupportEqInt_eq_zero_of_not_triangleSupport
          (G := G) (q := q) y hS htri
      simp [htri, hzero]
  · rw [← Finset.sum_filter]
    unfold rankTwoTriangleSupportFilteredCoefficientInt
    apply Finset.sum_congr
    · ext S
      simp only [queryTriangleSupportSet, Finset.mem_filter, Finset.mem_univ, true_and]
    · intro S _hS
      rfl

/-- The triangle-support filtered sum can be indexed by the underlying
three-coordinate vertex set. -/
theorem rankTwoTriangleSupportFilteredCoefficientInt_eq_vertexSupport
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoTriangleSupportFilteredCoefficientInt G q y =
      rankTwoTriangleVertexSupportCoefficientInt G q y := by
  classical
  unfold rankTwoTriangleSupportFilteredCoefficientInt
    rankTwoTriangleVertexSupportCoefficientInt
  rw [queryTriangleSupportSet_eq_image_queryPairSet]
  have hinj : Set.InjOn (fun V : Finset (Fin q) => queryPairSet V)
      (queryTriangleVertexSet q) := by
    intro V hV W hW hquery
    have hVcard : V.card = 3 := by
      simpa [queryTriangleVertexSet] using hV
    have hWcard : W.card = 3 := by
      simpa [queryTriangleVertexSet] using hW
    exact queryPairSet_injective_on_card_three hVcard hWcard hquery
  rw [Finset.sum_image hinj]

/-- The support-cardinality-three rank-two coefficient is now indexed by
three-coordinate vertex sets. -/
theorem rankTwoAlternatingCoefficientSupportCardEq_three_eq_vertexSupport
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoAlternatingCoefficientSupportCardEqInt G q y 3 =
      rankTwoTriangleVertexSupportCoefficientInt G q y := by
  rw [rankTwoAlternatingCoefficientSupportCardEq_three_eq_sum_triangleSupport,
    rankTwoTriangleSupportFilteredCoefficientInt_eq_vertexSupport]

/-- Combining the proved lower bound with the remaining graph upper-bound
obligation, every rank-two subfamily has support size exactly two or exactly
three. -/
theorem collisionSubfamilyPairSupport_card_eq_two_or_three_of_graphicRank_eq_two
    {q : Nat} (hub : RankTwoPairSupportUpperBound q)
    {T : Finset (CollisionEvent q)}
    (hrank : collisionSubfamilyGraphicRank (q := q) T = 2) :
    (collisionSubfamilyPairSupport q T).card = 2 ∨
      (collisionSubfamilyPairSupport q T).card = 3 := by
  have hle : (collisionSubfamilyPairSupport q T).card ≤ 3 := hub T hrank
  have hge : 2 ≤ (collisionSubfamilyPairSupport q T).card :=
    collisionSubfamilyPairSupport_two_le_of_graphicRank_eq_two (q := q) hrank
  omega

/-- Under the pure graph support upper bound, the rank-two coefficient carried
by subfamilies touching four or more query pairs is exactly zero. -/
theorem rankTwoAlternatingCoefficientSupportCardGe_four_eq_zero_of_pairSupportUpperBound
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G)
    (hub : RankTwoPairSupportUpperBound q) :
    rankTwoAlternatingCoefficientSupportCardGeInt G q y 4 = 0 := by
  unfold rankTwoAlternatingCoefficientSupportCardGeInt
  apply Finset.sum_eq_zero
  intro T hT
  simp only [Finset.mem_filter] at hT
  have hle : (collisionSubfamilyPairSupport q T).card ≤ 3 := hub T hT.2
  have hnot : ¬ 4 ≤ (collisionSubfamilyPairSupport q T).card := by omega
  simp [hnot]

/-- The support-cardinality `>= 4` rank-two summand vanishes unconditionally. -/
theorem rankTwoAlternatingCoefficientSupportCardGe_four_eq_zero
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoAlternatingCoefficientSupportCardGeInt G q y 4 = 0 := by
  exact rankTwoAlternatingCoefficientSupportCardGe_four_eq_zero_of_pairSupportUpperBound
    (G := G) (q := q) (y := y) (rankTwoPairSupportUpperBound q)

/-- Once the pure graph support upper bound is available, the rank-two
alternating coefficient has only the two expected support classes: two touched
query pairs and three touched query pairs. -/
theorem rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three_of_pairSupportUpperBound
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G)
    (hub : RankTwoPairSupportUpperBound q) :
    rankTwoAlternatingCoefficientInt G q y =
      rankTwoAlternatingCoefficientSupportCardEqInt G q y 2 +
        rankTwoAlternatingCoefficientSupportCardEqInt G q y 3 := by
  rw [rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three_add_ge_four]
  rw [rankTwoAlternatingCoefficientSupportCardGe_four_eq_zero_of_pairSupportUpperBound
    (G := G) (q := q) (y := y) hub]
  simp

/-- The rank-two alternating coefficient is now reduced unconditionally to
the two structurally meaningful support classes. -/
theorem rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    rankTwoAlternatingCoefficientInt G q y =
      rankTwoAlternatingCoefficientSupportCardEqInt G q y 2 +
        rankTwoAlternatingCoefficientSupportCardEqInt G q y 3 := by
  exact rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three_of_pairSupportUpperBound
    (G := G) (q := q) (y := y) (rankTwoPairSupportUpperBound q)

/-- Coefficient-level form of the rank-two equality-pattern target.  Once this
is proved, the field-size-scaled identity follows by the rank-two layer
factorization below. -/
def RankTwoAlternatingCoefficientIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) : Prop :=
  ∀ y : Fin q → G,
    rankTwoAlternatingCoefficientInt G q y =
      rankTwoEqualityCoefficientInt G q y

/-- Support-cardinality two should be exactly the forest product part of the
rank-two equality-pattern coefficient. -/
def RankTwoSupportCardTwoCoefficientIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) : Prop :=
  ∀ y : Fin q → G,
    rankTwoAlternatingCoefficientSupportCardEqInt G q y 2 =
      rankTwoForestCoefficientInt G q y

/-- Reindexing form of the support-cardinality-two identity: the raw rank-two
sum over collision-event subfamilies whose pair support has cardinality two
equals the product over the two pair-local nonempty fiber sums. -/
def RankTwoSupportCardTwoPairFiberProductIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) : Prop :=
  ∀ y : Fin q → G,
    rankTwoAlternatingCoefficientSupportCardEqInt G q y 2 =
      rankTwoForestPairFiberProductCoefficientInt G q y

/-- Pointwise exact-support form of the support-cardinality-two identity.  This
is the remaining local statement after regrouping both sides by the two touched
query pairs. -/
def RankTwoPairSupportEqProductIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) : Prop :=
  ∀ (y : Fin q → G) (S : Finset (PairIndex q)),
    S.card = 2 →
      rankTwoAlternatingCoefficientPairSupportEqInt G q y S =
        rankTwoPairSupportProductCoefficientInt G q y S

/-- Exact-support fiber-product expansion after the rank test has been removed.
This is the genuinely local product/bijection statement for two touched
query-pair fibers. -/
def RankTwoPairSupportNoRankProductIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) : Prop :=
  ∀ (y : Fin q → G) (S : Finset (PairIndex q)),
    S.card = 2 →
      rankTwoAlternatingCoefficientPairSupportEqNoRankInt G q y S =
        rankTwoPairSupportProductCoefficientInt G q y S

/-- The exact-support no-rank two-pair coefficient factors into the product of
the two pair-local coefficients.  The proof is a bijective reindexing between
global collision subfamilies with exact support `S` and nonempty pair-local
choices over the two elements of `S`; the labelled content is exactly
`collisionSubfamilyPairChoiceUnion_signedTerm_eq_prod_of_card_eq_two`. -/
theorem rankTwoPairSupportNoRankProductIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) :
    RankTwoPairSupportNoRankProductIdentity G q := by
  intro y S hS
  rw [rankTwoPairSupportProductCoefficientInt_eq_piProduct]
  unfold rankTwoAlternatingCoefficientPairSupportEqNoRankInt
    rankTwoPairSupportPiProductCoefficientInt
  refine Finset.sum_bij'
    (fun T _hT => fun p hp => collisionSubfamilyPairFiber (q := q) T p)
    (fun F _hF => collisionSubfamilyPairChoiceUnion (S := S) (fun p : S => F p.1 p.2))
    ?hi ?hj ?left ?right ?term
  · intro T hT
    simp only [Finset.mem_filter] at hT
    have hsupport : collisionSubfamilyPairSupport q T = S := hT.2
    apply Finset.mem_pi.mpr
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · exact collisionSubfamilyPairFiber_subset_pairEvents (q := q) T p
    · exact (collisionSubfamilyPairFiber_nonempty_iff (q := q) (T := T) (p := p)).mpr
        (by simpa [hsupport] using hp)
  · intro F hF
    have hFmem : F ∈ S.pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
      hF
    have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact pairChoice_mem_pi_subset_pairEvents hFmem p
    have hne : ∀ p : S, (F p.1 p.2).Nonempty := by
      intro p
      exact pairChoice_mem_pi_nonempty hFmem p
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro e he
      simp
    · exact collisionSubfamilyPairSupport_pairChoiceUnion_eq
        (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub hne
  · intro T hT
    simp only [Finset.mem_filter] at hT
    exact collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
      (q := q) (T := T) (S := S) hT.2
  · intro F hF
    have hFmem : F ∈ S.pi
        (fun p => (collisionPairEvents (q := q) p).powerset.filter (fun T => T.Nonempty)) :=
      hF
    have hsub : ∀ p : S, F p.1 p.2 ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact pairChoice_mem_pi_subset_pairEvents hFmem p
    funext p hp
    exact collisionSubfamilyPairFiber_pairChoiceUnion_eq
      (q := q) (S := S) (F := fun p : S => F p.1 p.2) hsub ⟨p, hp⟩
  · intro T hT
    simp only [Finset.mem_filter] at hT
    have hsupport : collisionSubfamilyPairSupport q T = S := hT.2
    let F : ∀ _p : S, Finset (CollisionEvent q) :=
      fun p => collisionSubfamilyPairFiber (q := q) T p.1
    have hsub : ∀ p : S, F p ⊆ collisionPairEvents (q := q) p.1 := by
      intro p
      exact collisionSubfamilyPairFiber_subset_pairEvents (q := q) T p.1
    have hne : ∀ p : S, (F p).Nonempty := by
      intro p
      exact (collisionSubfamilyPairFiber_nonempty_iff (q := q) (T := T) (p := p.1)).mpr
        (by simp [hsupport, p.2])
    have hT_eq : collisionSubfamilyPairChoiceUnion F = T :=
      collisionSubfamilyPairChoiceUnion_fibers_eq_of_pairSupport_eq
        (q := q) (T := T) (S := S) hsupport
    have hfact := collisionSubfamilyPairChoiceUnion_signedTerm_eq_prod_of_card_eq_two
      (G := G) (q := q) (S := S) (y := y) F hsub hne hS
    simpa [F, hT_eq] using hfact

/-- Rank automaticity plus the no-rank fiber-product expansion imply the
pointwise exact-support product identity. -/
theorem RankTwoPairSupportEqProductIdentity.of_rankAutomatic_noRankProduct
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (hrankAuto : RankTwoPairSupportRankAutomatic q)
    (hprod : RankTwoPairSupportNoRankProductIdentity G q) :
    RankTwoPairSupportEqProductIdentity G q := by
  intro y S hS
  rw [rankTwoAlternatingCoefficientPairSupportEqInt_eq_noRank_of_rankAutomatic
    (G := G) (q := q) (y := y) (S := S) hrankAuto hS]
  exact hprod y S hS

/-- The pointwise exact-support product identity implies the global pair-fiber
product identity by summing over all two-element query-pair supports. -/
theorem RankTwoSupportCardTwoPairFiberProductIdentity.of_pairSupportProduct
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (hpoint : RankTwoPairSupportEqProductIdentity G q) :
    RankTwoSupportCardTwoPairFiberProductIdentity G q := by
  intro y
  rw [rankTwoAlternatingCoefficientSupportCardEq_two_eq_sum_pairSupportEq,
    rankTwoForestPairFiberProductCoefficientInt_eq_sum_pairSupportProduct]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [Finset.mem_filter] at hS
  exact hpoint y S hS.2

/-- The pair-fiber product reindexing implies the support-cardinality-two
forest identity, because the product form evaluates to the existing forest
coefficient by the pair-local rank-one calculation. -/
theorem RankTwoSupportCardTwoCoefficientIdentity.of_pairFiberProduct
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (hprod : RankTwoSupportCardTwoPairFiberProductIdentity G q) :
    RankTwoSupportCardTwoCoefficientIdentity G q := by
  intro y
  rw [hprod y, rankTwoForestPairFiberProductCoefficientInt_eq_forest]

/-- The pointwise exact-support product identity is enough to discharge the
support-cardinality-two forest identity. -/
theorem RankTwoSupportCardTwoCoefficientIdentity.of_pairSupportProduct
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (hpoint : RankTwoPairSupportEqProductIdentity G q) :
    RankTwoSupportCardTwoCoefficientIdentity G q := by
  exact RankTwoSupportCardTwoCoefficientIdentity.of_pairFiberProduct
    (G := G) (q := q)
    (RankTwoSupportCardTwoPairFiberProductIdentity.of_pairSupportProduct
      (G := G) (q := q) hpoint)

/-- Rank automaticity and the no-rank exact-support product expansion together
discharge the support-cardinality-two forest identity. -/
theorem RankTwoSupportCardTwoCoefficientIdentity.of_rankAutomatic_noRankProduct
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (hrankAuto : RankTwoPairSupportRankAutomatic q)
    (hprod : RankTwoPairSupportNoRankProductIdentity G q) :
    RankTwoSupportCardTwoCoefficientIdentity G q := by
  exact RankTwoSupportCardTwoCoefficientIdentity.of_pairSupportProduct
    (G := G) (q := q)
    (RankTwoPairSupportEqProductIdentity.of_rankAutomatic_noRankProduct
      (G := G) (q := q) hrankAuto hprod)

/-- Once exact two-pair supports are known to be graphic-rank-two automatically,
the support-cardinality-two rank-two coefficient is fully closed. -/
theorem RankTwoSupportCardTwoCoefficientIdentity.of_rankAutomatic
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (hrankAuto : RankTwoPairSupportRankAutomatic q) :
    RankTwoSupportCardTwoCoefficientIdentity G q := by
  exact RankTwoSupportCardTwoCoefficientIdentity.of_rankAutomatic_noRankProduct
    (G := G) (q := q) hrankAuto (rankTwoPairSupportNoRankProductIdentity G q)

/-- The specialized two-edge hidden-representative graph endpoint is enough to
close the support-cardinality-two coefficient identity. -/
theorem RankTwoSupportCardTwoCoefficientIdentity.of_hiddenRepresentative_card_two
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat)
    (hhiddenTwo : HiddenRepresentativeGraphicRankLeTwoOnCardTwo q) :
    RankTwoSupportCardTwoCoefficientIdentity G q := by
  exact RankTwoSupportCardTwoCoefficientIdentity.of_rankAutomatic
    (G := G) (q := q)
    (RankTwoPairSupportRankAutomatic.of_hiddenRepresentative_card_two hhiddenTwo)

/-- The support-cardinality-two rank-two coefficient is fully closed
unconditionally. -/
theorem rankTwoSupportCardTwoCoefficientIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G] (q : Nat) :
    RankTwoSupportCardTwoCoefficientIdentity G q :=
  RankTwoSupportCardTwoCoefficientIdentity.of_hiddenRepresentative_card_two
    (G := G) (q := q) (hiddenRepresentativeGraphicRankLeTwoOnCardTwo q)

/-- Support-cardinality three should be exactly the triangle-correction part
of the rank-two equality-pattern coefficient. -/
def RankTwoSupportCardThreeCoefficientIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) : Prop :=
  ∀ y : Fin q → G,
    rankTwoAlternatingCoefficientSupportCardEqInt G q y 3 =
      rankTwoTriangleCorrectionInt G q y

/-- The global support-cardinality-three identity follows from the local
ranked pair-fiber triangle calculation on every three-coordinate vertex set. -/
theorem RankTwoSupportCardThreeCoefficientIdentity.of_vertexPiUnionRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (hlocal : RankTwoTriangleVertexPiUnionRankIdentity G q) :
    RankTwoSupportCardThreeCoefficientIdentity G q := by
  intro y
  rw [rankTwoAlternatingCoefficientSupportCardEq_three_eq_vertexSupport,
    rankTwoTriangleVertexSupportCoefficientInt_eq_piUnionRank]
  unfold rankTwoTriangleVertexPiUnionRankCoefficientInt rankTwoTriangleCorrectionInt
  apply Finset.sum_congr rfl
  intro V hV
  have hVcard : V.card = 3 := by
    simpa [queryTriangleVertexSet] using hV
  exact hlocal y V hVcard

/-- The three rank-two classification facts imply the coefficient-level
equality-pattern identity: no rank-two support with four or more query pairs,
support size two is the forest term, and support size three is the triangle
term. -/
theorem RankTwoAlternatingCoefficientIdentity.of_supportCardIdentities
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (hupper : RankTwoPairSupportUpperBound q)
    (htwo : RankTwoSupportCardTwoCoefficientIdentity G q)
    (hthree : RankTwoSupportCardThreeCoefficientIdentity G q) :
    RankTwoAlternatingCoefficientIdentity G q := by
  intro y
  rw [rankTwoAlternatingCoefficientInt_eq_supportCard_two_add_three_of_pairSupportUpperBound
    (G := G) (q := q) (y := y) hupper]
  rw [htwo y, hthree y]
  rfl

/-- With the pure support upper bound proved, the two support-cardinality
identities are the only remaining rank-two classification inputs. -/
theorem RankTwoAlternatingCoefficientIdentity.of_supportCardIdentities'
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (htwo : RankTwoSupportCardTwoCoefficientIdentity G q)
    (hthree : RankTwoSupportCardThreeCoefficientIdentity G q) :
    RankTwoAlternatingCoefficientIdentity G q := by
  exact RankTwoAlternatingCoefficientIdentity.of_supportCardIdentities
    (G := G) (q := q) (rankTwoPairSupportUpperBound q) htwo hthree

/-- Since the support-cardinality-two coefficient is now closed
unconditionally, the full rank-two alternating-coefficient identity is reduced
to the support-cardinality-three triangle identity. -/
theorem RankTwoAlternatingCoefficientIdentity.of_supportCardThree
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (hthree : RankTwoSupportCardThreeCoefficientIdentity G q) :
    RankTwoAlternatingCoefficientIdentity G q := by
  exact RankTwoAlternatingCoefficientIdentity.of_supportCardIdentities'
    (G := G) (q := q)
    (rankTwoSupportCardTwoCoefficientIdentity G q) hthree

/-- The full rank-two equality-pattern coefficient identity is reduced to the
local ranked pair-fiber triangle identity. -/
theorem RankTwoAlternatingCoefficientIdentity.of_triangleVertexPiUnionRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (hlocal : RankTwoTriangleVertexPiUnionRankIdentity G q) :
    RankTwoAlternatingCoefficientIdentity G q := by
  exact RankTwoAlternatingCoefficientIdentity.of_supportCardThree
    (G := G) (q := q)
    (RankTwoSupportCardThreeCoefficientIdentity.of_vertexPiUnionRank
      (G := G) (q := q) hlocal)

/-- Coefficient-level rank-two equality-pattern identity from the two remaining
local triangle obligations: graph-rank automaticity of triangle supports and
the no-rank signed three-fiber evaluation. -/
theorem RankTwoAlternatingCoefficientIdentity.of_triangleRankAutomatic_noRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (hrank : RankTwoTriangleSupportRankAutomatic q)
    (hnorank : RankTwoTriangleVertexPiUnionNoRankIdentity G q) :
    RankTwoAlternatingCoefficientIdentity G q := by
  exact RankTwoAlternatingCoefficientIdentity.of_triangleVertexPiUnionRank
    (G := G) (q := q)
    (RankTwoTriangleVertexPiUnionRankIdentity.of_rankAutomatic_noRank
      (G := G) (q := q) hrank hnorank)

/-- Coefficient-level rank-two equality-pattern identity from the remaining
no-rank signed three-fiber triangle calculation. -/
theorem RankTwoAlternatingCoefficientIdentity.of_triangleNoRank
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat)
    (hnorank : RankTwoTriangleVertexPiUnionNoRankIdentity G q) :
    RankTwoAlternatingCoefficientIdentity G q :=
  RankTwoAlternatingCoefficientIdentity.of_triangleRankAutomatic_noRank
    (G := G) (q := q) (rankTwoTriangleSupportRankAutomatic q) hnorank

/-- The exact rank-two cancellation identity targeted next.  It states that
the graphic-rank-two gain-graph layer is not an arbitrary rank-two absolute
tail: it is `|G|^(q-2)` times a signed equality-pattern coefficient made from
two-edge forests and triangle corrections. -/
def RankTwoEqualityPatternIdentity
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : Prop :=
  ∀ y : Fin q → G,
    (∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
      collisionSubfamilyGraphicRank (q := q) T = 2,
      (-1 : ℤ) ^ T.card *
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - 2)
          else
            0) : ℤ)) =
      ((Fintype.card G) ^ (q - 2) : ℤ) *
        rankTwoEqualityCoefficientInt G q y

/-- The rank-two layer factors as the common count scale `|G|^(q-2)` times a
pure signed alternating coefficient.  This isolates the remaining rank-two
work as a field-size-free combinatorial identity. -/
theorem collisionSubfamily_rankTwoLayer_eq_card_pow_mul_alternatingCoefficient
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (y : Fin q → G) :
    collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankTwoFin q hq2) =
      ((Fintype.card G) ^ (q - 2) : ℤ) *
        rankTwoAlternatingCoefficientInt G q y := by
  unfold collisionSubfamilyRankLayerInt rankTwoAlternatingCoefficientInt
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · ext T
    simp [collisionSubfamilyGraphicRankFin, collisionSubfamilyGraphicRankTwoFin]
  · intro T hT
    simp only [Finset.mem_filter] at hT
    by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
    · simp [hcyc, collisionSubfamilyGraphicRankTwoFin, mul_comm]
    · simp [hcyc]

/-- The rank-three layer factors as the common count scale `|G|^(q-3)` times a
pure signed alternating coefficient.  This is the rank-three analogue of
`collisionSubfamily_rankTwoLayer_eq_card_pow_mul_alternatingCoefficient`. -/
theorem collisionSubfamily_rankThreeLayer_eq_card_pow_mul_alternatingCoefficient
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq3 : 3 ≤ q) (y : Fin q → G) :
    collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankThreeFin q hq3) =
      ((Fintype.card G) ^ (q - 3) : ℤ) *
        rankThreeAlternatingCoefficientInt G q y := by
  unfold collisionSubfamilyRankLayerInt rankThreeAlternatingCoefficientInt
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · ext T
    simp [collisionSubfamilyGraphicRankFin, collisionSubfamilyGraphicRankThreeFin]
  · intro T hT
    simp only [Finset.mem_filter] at hT
    by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
    · simp [hcyc, collisionSubfamilyGraphicRankThreeFin, mul_comm]
    · simp [hcyc]

/-- The coefficient-level rank-two target implies the original scaled
rank-two equality-pattern identity. -/
theorem RankTwoEqualityPatternIdentity.of_alternatingCoefficient
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q)
    (hcoeff : RankTwoAlternatingCoefficientIdentity G q) :
    RankTwoEqualityPatternIdentity G q := by
  intro y
  rw [← hcoeff y]
  rw [← collisionSubfamily_rankTwoLayer_eq_card_pow_mul_alternatingCoefficient
    (G := G) (q := q) hq2 y]
  unfold collisionSubfamilyRankLayerInt
  apply Finset.sum_congr
  · ext T
    simp [collisionSubfamilyGraphicRankFin, collisionSubfamilyGraphicRankTwoFin]
  · intro T hT
    simp only [Finset.mem_filter] at hT
    by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
    · simp [hcyc, collisionSubfamilyGraphicRankTwoFin]
    · simp [hcyc]

/-- The scaled rank-two equality-pattern identity is now reduced to the
support-cardinality-three triangle identity. -/
theorem RankTwoEqualityPatternIdentity.of_supportCardThree
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q)
    (hthree : RankTwoSupportCardThreeCoefficientIdentity G q) :
    RankTwoEqualityPatternIdentity G q :=
  RankTwoEqualityPatternIdentity.of_alternatingCoefficient
    (G := G) (q := q) hq2
    (RankTwoAlternatingCoefficientIdentity.of_supportCardThree
      (G := G) (q := q) hthree)

/-- Scaled rank-two equality-pattern identity from the two remaining local
triangle obligations. -/
theorem RankTwoEqualityPatternIdentity.of_triangleRankAutomatic_noRank
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q)
    (hrank : RankTwoTriangleSupportRankAutomatic q)
    (hnorank : RankTwoTriangleVertexPiUnionNoRankIdentity G q) :
    RankTwoEqualityPatternIdentity G q :=
  RankTwoEqualityPatternIdentity.of_alternatingCoefficient
    (G := G) (q := q) hq2
    (RankTwoAlternatingCoefficientIdentity.of_triangleRankAutomatic_noRank
      (G := G) (q := q) hrank hnorank)

/-- Scaled rank-two equality-pattern identity from the remaining no-rank signed
three-fiber triangle calculation. -/
theorem RankTwoEqualityPatternIdentity.of_triangleNoRank
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q)
    (hnorank : RankTwoTriangleVertexPiUnionNoRankIdentity G q) :
    RankTwoEqualityPatternIdentity G q :=
  RankTwoEqualityPatternIdentity.of_triangleRankAutomatic_noRank
    (G := G) (q := q) hq2 (rankTwoTriangleSupportRankAutomatic q) hnorank

/-- The support-cardinality-three rank-two coefficient identity is now
unconditional: genuine triangle supports contribute exactly the
equality-pattern triangle correction. -/
theorem rankTwoSupportCardThreeCoefficientIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) :
    RankTwoSupportCardThreeCoefficientIdentity G q :=
  RankTwoSupportCardThreeCoefficientIdentity.of_vertexPiUnionRank
    (G := G) (q := q) (rankTwoTriangleVertexPiUnionRankIdentity G q)

/-- The full signed rank-two alternating coefficient is now the
equality-pattern coefficient, with no absolute rank-two slack. -/
theorem rankTwoAlternatingCoefficientIdentity
    (G : Type*) [AddCommGroup G] [DecidableEq G]
    (q : Nat) :
    RankTwoAlternatingCoefficientIdentity G q :=
  RankTwoAlternatingCoefficientIdentity.of_supportCardThree
    (G := G) (q := q) (rankTwoSupportCardThreeCoefficientIdentity G q)

/-- Scaled rank-two equality-pattern identity with all local triangle
obligations discharged. -/
theorem rankTwoEqualityPatternIdentity
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) :
    RankTwoEqualityPatternIdentity G q :=
  RankTwoEqualityPatternIdentity.of_alternatingCoefficient
    (G := G) (q := q) hq2 (rankTwoAlternatingCoefficientIdentity G q)

/-- The low-rank compatible count depends on the visible transcript only
through its number of coordinate-pair collisions. -/
theorem compatibleCountLowRankInt_eq_card_pow_add_collisionCount
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (y : Fin q → G) :
    compatibleCountLowRankInt (G := G) (q := q) y =
      ((Fintype.card G) ^ q : ℤ) +
        ((Fintype.card G) ^ (q - 1) : ℤ) *
          (pairCollisionCountInt G q y -
            2 * (Fintype.card (PairIndex q) : ℤ)) := by
  unfold compatibleCountLowRankInt
  rw [pairCoefficient_sum_eq_pairCollisionCountInt_sub_two_pairIndex
    (G := G) (q := q) y]

/-- Low-rank density written as a scalar function of the visible pair-collision
count. -/
def lowRankDensityFromCollisionCountReal (G : Type*) [Fintype G] (q : Nat)
    (k : ℤ) : ℝ :=
  (((Fintype.card G) ^ q : ℤ) +
      ((Fintype.card G) ^ (q - 1) : ℤ) *
        (k - 2 * (Fintype.card (PairIndex q) : ℤ)) : ℝ) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Scalar low-rank density in normalizer-slack form. -/
theorem lowRankDensityFromCollisionCountReal_eq_slack_mul
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G] (q : Nat)
    (hq0 : 0 < q) (hq : q ≤ Fintype.card G) (k : ℤ) :
    lowRankDensityFromCollisionCountReal G q k =
      XoP.ANOVA.visibleNormalizerSlackReal G q *
        (1 + (((k - 2 * (Fintype.card (PairIndex q) : ℤ)) : ℝ) /
          (Fintype.card G : ℝ))) := by
  unfold lowRankDensityFromCollisionCountReal XoP.ANOVA.visibleNormalizerSlackReal
  let N : ℝ := Fintype.card G
  let x : ℝ := ((k - 2 * (Fintype.card (PairIndex q) : ℤ)) : ℝ)
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hpow : q - 1 + 1 = q := Nat.sub_add_cancel hq0
  field_simp [hN_ne, hZ_ne]
  norm_num [Nat.cast_pow]
  have hpowR : (Fintype.card G : ℝ) ^ q =
      (Fintype.card G : ℝ) ^ (q - 1) * (Fintype.card G : ℝ) := by
    rw [← pow_succ, hpow]
  rw [hpowR]
  ring

/-- Closed form of the scalar low-rank density at the largest possible visible
pair-collision count. -/
theorem lowRankDensityFromCollisionCountReal_pairIndex_card_eq
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G] (q : Nat)
    (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    lowRankDensityFromCollisionCountReal G q
        (Fintype.card (PairIndex q) : ℤ) =
      XoP.ANOVA.visibleNormalizerSlackReal G q *
        (1 - (Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ)) := by
  rw [lowRankDensityFromCollisionCountReal_eq_slack_mul (G := G) (q := q) hq0 hq]
  congr 1
  ring_nf
  simp [mul_comm]

/-- Scalar arithmetic bridge used in the low-collision endpoint checks. -/
theorem one_sub_two_mul_le_sq_one_sub (x : ℝ) :
    1 - 2 * x ≤ (1 - x) ^ 2 := by
  nlinarith [sq_nonneg x]

/-- Normalized high-collision scalar bridge.

This lemma separates the remaining low-rank coefficient estimate into two
parts.  If `r` is the normalized falling-factorial ratio and
`1 - P / N <= r`, then the real density/slope term is bounded by the simpler
first-order scalar inequality with `r` replaced by `1 - P / N`.

The later paper-grade coefficient estimate can therefore focus on the pure
rational inequality in `N`, `P`, and `k`; this lemma handles the positive-part,
inverse-square slack, and slope monotonicity mechanics. -/
theorem highCollisionNormalizedPositivePart_le_inv_sq_of_scalar
    {N P k r c : ℝ} (hN2 : 2 ≤ N) (hPsmall : 2 * P ≤ N)
    (hk2 : 2 ≤ k) (hkP : k ≤ P) (hr : 1 - P / N ≤ r) (hc : 0 ≤ c)
    (hscalar :
      (1 + (k - 2 * P) / N) / (1 - P / N) ^ 2 - 1 -
          k * (1 - P / N) * N / (N - 1) ^ 2 ≤
        c * (k * (k - 1) / 2) / N ^ 2) :
    (max ((1 / r ^ 2) * (1 + (k - 2 * P) / N) - 1) 0 -
        k * r * N / (N - 1) ^ 2) / (k * (k - 1) / 2) ≤ c / N ^ 2 := by
  have hNpos : 0 < N := by linarith
  have hNm1pos : 0 < N - 1 := by linarith
  have ha_pos : 0 < 1 - P / N := by
    have hhalf : P / N ≤ 1 / 2 := by
      rw [div_le_iff₀ hNpos]
      linarith
    linarith
  have hr_pos : 0 < r := lt_of_lt_of_le ha_pos hr
  have hA_nonneg : 0 ≤ 1 + (k - 2 * P) / N := by
    rw [show 1 + (k - 2 * P) / N = (N + k - 2 * P) / N by
      field_simp [hNpos.ne']
      ring]
    exact div_nonneg (by linarith) (le_of_lt hNpos)
  have hinv_sq : 1 / r ^ 2 ≤ 1 / (1 - P / N) ^ 2 := by
    have hsquares : (1 - P / N) ^ 2 ≤ r ^ 2 := by
      nlinarith [sq_nonneg (r - (1 - P / N))]
    exact one_div_le_one_div_of_le (sq_pos_of_pos ha_pos) hsquares
  have hdens_le :
      (1 / r ^ 2) * (1 + (k - 2 * P) / N) ≤
        (1 + (k - 2 * P) / N) / (1 - P / N) ^ 2 := by
    calc
      (1 / r ^ 2) * (1 + (k - 2 * P) / N) ≤
          (1 / (1 - P / N) ^ 2) * (1 + (k - 2 * P) / N) := by
            exact mul_le_mul_of_nonneg_right hinv_sq hA_nonneg
      _ = (1 + (k - 2 * P) / N) / (1 - P / N) ^ 2 := by ring
  have hslope_lower :
      k * (1 - P / N) * N / (N - 1) ^ 2 ≤
        k * r * N / (N - 1) ^ 2 := by
    have hcoef_nonneg : 0 ≤ k * N / (N - 1) ^ 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hr hcoef_nonneg
    ring_nf at hmul ⊢
    exact hmul
  have hmain :
      (1 / r ^ 2) * (1 + (k - 2 * P) / N) - 1 ≤
        k * r * N / (N - 1) ^ 2 + c * (k * (k - 1) / 2) / N ^ 2 := by
    calc
      (1 / r ^ 2) * (1 + (k - 2 * P) / N) - 1 ≤
          (1 + (k - 2 * P) / N) / (1 - P / N) ^ 2 - 1 := by linarith
      _ ≤ k * (1 - P / N) * N / (N - 1) ^ 2 +
            c * (k * (k - 1) / 2) / N ^ 2 := by linarith
      _ ≤ k * r * N / (N - 1) ^ 2 +
            c * (k * (k - 1) / 2) / N ^ 2 := by linarith
  have hchoose_pos : 0 < k * (k - 1) / 2 := by
    nlinarith
  have hrhs_nonneg :
      0 ≤ k * r * N / (N - 1) ^ 2 + c * (k * (k - 1) / 2) / N ^ 2 := by
    positivity
  have hmax :
      max ((1 / r ^ 2) * (1 + (k - 2 * P) / N) - 1) 0 ≤
        k * r * N / (N - 1) ^ 2 + c * (k * (k - 1) / 2) / N ^ 2 := by
    exact max_le hmain hrhs_nonneg
  have hsub :
      max ((1 / r ^ 2) * (1 + (k - 2 * P) / N) - 1) 0 -
          k * r * N / (N - 1) ^ 2 ≤ c * (k * (k - 1) / 2) / N ^ 2 := by
    linarith
  rw [div_le_iff₀ hchoose_pos]
  calc
    max ((1 / r ^ 2) * (1 + (k - 2 * P) / N) - 1) 0 -
        k * r * N / (N - 1) ^ 2 ≤ c * (k * (k - 1) / 2) / N ^ 2 := hsub
    _ = (c / N ^ 2) * (k * (k - 1) / 2) := by ring

/-- Nonnegative polynomial certificate for the constant-`12` first-order
high-collision scalar bound.

This is the only genuinely polynomial part of the finite scalar estimate.  The
variables are the nonnegative slack coordinates
`a = N - 2P`, `b = P - k`, and `c = k - 2`; all later denominator clearing
reduces to this certificate. -/
theorem firstOrderHighCollisionScalarClearedTwelve_nonneg
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤
      a ^ 4 * (b ^ 2 - b * c - 2 * b + 4 * c ^ 2 + 12 * c + 8)
        + 8 * a ^ 3 * b ^ 3
        + 3 * a ^ 3 * b ^ 2 * c
        + 4 * a ^ 3 * b ^ 2
        + 18 * a ^ 3 * b * c ^ 2
        + 48 * a ^ 3 * b * c
        + 24 * a ^ 3 * b
        + 23 * a ^ 3 * c ^ 3
        + 104 * a ^ 3 * c ^ 2
        + 151 * a ^ 3 * c
        + 70 * a ^ 3
        + 24 * a ^ 2 * b ^ 4
        + 41 * a ^ 2 * b ^ 3 * c
        + 70 * a ^ 2 * b ^ 3
        + 57 * a ^ 2 * b ^ 2 * c ^ 2
        + 162 * a ^ 2 * b ^ 2 * c
        + 97 * a ^ 2 * b ^ 2
        + 87 * a ^ 2 * b * c ^ 3
        + 378 * a ^ 2 * b * c ^ 2
        + 512 * a ^ 2 * b * c
        + 208 * a ^ 2 * b
        + 47 * a ^ 2 * c ^ 4
        + 286 * a ^ 2 * c ^ 3
        + 637 * a ^ 2 * c ^ 2
        + 614 * a ^ 2 * c
        + 216 * a ^ 2
        + 32 * a * b ^ 5
        + 96 * a * b ^ 4 * c
        + 168 * a * b ^ 4
        + 136 * a * b ^ 3 * c ^ 2
        + 440 * a * b ^ 3 * c
        + 340 * a * b ^ 3
        + 152 * a * b ^ 2 * c ^ 3
        + 684 * a * b ^ 2 * c ^ 2
        + 972 * a * b ^ 2 * c
        + 424 * a * b ^ 2
        + 120 * a * b * c ^ 4
        + 720 * a * b * c ^ 3
        + 1560 * a * b * c ^ 2
        + 1428 * a * b * c
        + 456 * a * b
        + 40 * a * c ^ 5
        + 308 * a * c ^ 4
        + 928 * a * c ^ 3
        + 1364 * a * c ^ 2
        + 976 * a * c
        + 272 * a
        + 16 * b ^ 6
        + 68 * b ^ 5 * c
        + 120 * b ^ 5
        + 124 * b ^ 4 * c ^ 2
        + 424 * b ^ 4 * c
        + 356 * b ^ 4
        + 136 * b ^ 3 * c ^ 3
        + 664 * b ^ 3 * c ^ 2
        + 1056 * b ^ 3 * c
        + 544 * b ^ 3
        + 104 * b ^ 2 * c ^ 4
        + 648 * b ^ 2 * c ^ 3
        + 1470 * b ^ 2 * c ^ 2
        + 1426 * b ^ 2 * c
        + 492 * b ^ 2
        + 52 * b * c ^ 5
        + 400 * b * c ^ 4
        + 1196 * b * c ^ 3
        + 1724 * b * c ^ 2
        + 1184 * b * c
        + 304 * b
        + 12 * c ^ 6
        + 112 * c ^ 5
        + 426 * c ^ 4
        + 842 * c ^ 3
        + 908 * c ^ 2
        + 504 * c
        + 112 := by
  have hquad : 0 ≤ b ^ 2 - b * c - 2 * b + 4 * c ^ 2 + 12 * c + 8 := by
    nlinarith [sq_nonneg (b - (c + 2) / 2)]
  positivity

/-- Constant-`12` first-order high-collision scalar inequality.

This is the pure rational estimate left by
`highCollisionNormalizedPositivePart_le_inv_sq_of_scalar`.  The hypotheses are
exactly the small-query/high-collision scalar regime:
`2P <= N`, `2 <= k <= P`. -/
theorem firstOrderHighCollisionScalar_le_twelve
    {N P k : ℝ} (hN2 : 2 ≤ N) (hPsmall : 2 * P ≤ N)
    (hk2 : 2 ≤ k) (hkP : k ≤ P) :
    (1 + (k - 2 * P) / N) / (1 - P / N) ^ 2 - 1 -
        k * (1 - P / N) * N / (N - 1) ^ 2 ≤
      12 * (k * (k - 1) / 2) / N ^ 2 := by
  let a : ℝ := N - 2 * P
  let b : ℝ := P - k
  let c : ℝ := k - 2
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hNabc : N = a + 2 * (b + c + 2) := by dsimp [a, b, c]; ring
  have hPabc : P = b + c + 2 := by dsimp [b, c]; ring
  have hkabc : k = c + 2 := by dsimp [c]; ring
  have hDpos : 0 < N ^ 2 * (N - 1) ^ 2 * (N - P) ^ 2 := by
    have hNpos : 0 < N := by linarith
    have hNm1pos : 0 < N - 1 := by linarith
    have hNPpos : 0 < N - P := by linarith
    positivity
  rw [← sub_nonneg]
  apply (mul_nonneg_iff_of_pos_right hDpos).mp
  rw [hNabc, hPabc, hkabc]
  have hNsubP_ne : a + 2 * (b + c + 2) - (b + c + 2) ≠ 0 := by
    nlinarith
  have hNm1_ne : a + 2 * (b + c + 2) - 1 ≠ 0 := by
    nlinarith
  have hN_ne : a + 2 * (b + c + 2) ≠ 0 := by
    nlinarith
  have hcert := firstOrderHighCollisionScalarClearedTwelve_nonneg
    (a := a) (b := b) (c := c) ha hb hc
  convert hcert using 1
  field_simp [hNsubP_ne, hNm1_ne, hN_ne]
  ring_nf

/-- Scalar inequality behind the one-collision low-rank line check.  The
case split matches the triangular numbers: after `q >= 2`, the pair count is
either `1` (`q = 2`) or at least `3` (`q >= 3`). -/
theorem one_collision_factor_le_first_order_sq_mul_slope_correction
    {N P : ℝ} (hN2 : 2 ≤ N) (hPcase : P = 1 ∨ 3 ≤ P)
    (hPsmall : 2 * P ≤ N) :
    1 + (1 - 2 * P) / N ≤
      (1 - P / N) ^ 2 * (1 + (1 - P / N) * N / (N - 1) ^ 2) := by
  have hNpos : 0 < N := by linarith
  have hNm1pos : 0 < N - 1 := by linarith
  rcases hPcase with hP | hP3
  · subst P
    field_simp [hNpos.ne', hNm1pos.ne']
    ring_nf
    rfl
  · have hNnonzero : N ≠ 0 := ne_of_gt hNpos
    have hNm1nonzero : N - 1 ≠ 0 := ne_of_gt hNm1pos
    field_simp [hNnonzero, hNm1nonzero]
    ring_nf
    have hP1nonneg : 0 ≤ P - 1 := by linarith
    have hP2nonneg : 0 ≤ P - 2 := by linarith
    have hNpnonneg : 0 ≤ N + 1 - P := by linarith
    have hPnonneg : 0 ≤ P := by linarith
    nlinarith [mul_nonneg hP1nonneg hP2nonneg,
      mul_nonneg hPnonneg hPnonneg]

/-- Cardinality of query pairs as the triangular sum.  This is a bridge
between the `PairIndex` notation used in SoP and the falling-factorial
estimates in `XoPANOVA`. -/
theorem pairIndex_card_eq_sum_range (q : Nat) :
    Fintype.card (PairIndex q) = ∑ i ∈ Finset.range q, i := by
  have hpair := pairIndex_card_mul_two (q := q)
  have hsum : (∑ i ∈ Finset.range q, i) * 2 = q * (q - 1) :=
    Finset.sum_range_id_mul_two q
  omega

/-- Real-valued form of `pairIndex_card_eq_sum_range`, normalized by a
positive field size. -/
theorem pairIndex_card_div_eq_sum_range_div (N q : Nat) :
    (Fintype.card (PairIndex q) : ℝ) / (N : ℝ) =
      ∑ i ∈ Finset.range q, (i : ℝ) / (N : ℝ) := by
  rw [pairIndex_card_eq_sum_range]
  simp [Finset.sum_div]

/-- The scalar low-rank density is monotone in the visible collision count on
the finite support `0 <= k <= #PairIndex`. -/
theorem lowRankDensityFromCollisionCountReal_le_pairIndex_card
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G] (q : Nat)
    (hq0 : 0 < q) (hq : q ≤ Fintype.card G)
    (k : Nat) (hk : k ≤ Fintype.card (PairIndex q)) :
    lowRankDensityFromCollisionCountReal G q (k : ℤ) ≤
      lowRankDensityFromCollisionCountReal G q
        (Fintype.card (PairIndex q) : ℤ) := by
  rw [lowRankDensityFromCollisionCountReal_eq_slack_mul (G := G) (q := q) hq0 hq]
  rw [lowRankDensityFromCollisionCountReal_eq_slack_mul (G := G) (q := q) hq0 hq]
  have hslack_nonneg : 0 ≤ XoP.ANOVA.visibleNormalizerSlackReal G q := by
    unfold XoP.ANOVA.visibleNormalizerSlackReal
    positivity
  apply mul_le_mul_of_nonneg_left _ hslack_nonneg
  have hN_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hsub :
      ((((k : Nat) : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) ≤
        (((Fintype.card (PairIndex q) : ℤ) -
            2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) := by
    have hkz : (k : ℤ) ≤ (Fintype.card (PairIndex q) : ℤ) := by
      exact_mod_cast hk
    exact_mod_cast (by
      linarith :
        (k : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) ≤
          (Fintype.card (PairIndex q) : ℤ) -
            2 * (Fintype.card (PairIndex q) : ℤ))
  have hdiv :
      ((((k : Nat) : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
          (Fintype.card G : ℝ) ≤
        (((Fintype.card (PairIndex q) : ℤ) -
            2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
          (Fintype.card G : ℝ) := by
    exact div_le_div_of_nonneg_right hsub (le_of_lt hN_pos)
  simpa [add_comm] using add_le_add_left hdiv (1 : ℝ)

/-- The scalar low-rank positive part is bounded by its endpoint value at the
maximum possible visible collision count. -/
theorem lowRankDensityPositivePart_le_pairIndex_card
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G] (q : Nat)
    (hq0 : 0 < q) (hq : q ≤ Fintype.card G)
    (k : Nat) (hk : k ≤ Fintype.card (PairIndex q)) :
    max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 ≤
      max (lowRankDensityFromCollisionCountReal G q
        (Fintype.card (PairIndex q) : ℤ) - 1) 0 := by
  have h :=
    lowRankDensityFromCollisionCountReal_le_pairIndex_card
      (G := G) (q := q) hq0 hq k hk
  exact max_le_max (sub_le_sub_right h 1) le_rfl

/-- Pointwise scalarization of the low-rank density. -/
theorem compatibleCountLowRankDensityReal_eq_collisionCountScalar
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (y : Fin q → G) :
    compatibleCountLowRankDensityReal G q y =
      lowRankDensityFromCollisionCountReal G q (pairCollisionCountInt G q y) := by
  unfold compatibleCountLowRankDensityReal lowRankDensityFromCollisionCountReal
  rw [compatibleCountLowRankInt_eq_card_pow_add_collisionCount (G := G) (q := q) y]
  norm_num

/-- The low-rank positive error is a one-dimensional average over the visible
pair-collision count. -/
theorem compatibleCountLowRankPositiveErrorReal_eq_collisionCountScalarAverage
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    compatibleCountLowRankPositiveErrorReal G q =
      XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y => max
          (lowRankDensityFromCollisionCountReal G q (pairCollisionCountInt G q y) - 1) 0) := by
  unfold compatibleCountLowRankPositiveErrorReal XoP.ANOVA.uniformAverage
  apply congrArg (fun s : ℝ => s / (Fintype.card (Fin q → G) : ℝ))
  apply Finset.sum_congr rfl
  intro y _hy
  dsimp
  rw [compatibleCountLowRankDensityReal_eq_collisionCountScalar (G := G) (q := q) y]

/-- The scalar low-rank positive error is an exact finite sum over the
collision-count fibers.  This is the occupancy-distribution form of the
remaining low-rank estimate. -/
theorem compatibleCountLowRankPositiveErrorReal_eq_collisionCountFiberSum
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    compatibleCountLowRankPositiveErrorReal G q =
      (∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
        (pairCollisionCountFiberCard G q k : ℝ) *
          max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ) := by
  rw [compatibleCountLowRankPositiveErrorReal_eq_collisionCountScalarAverage
    (G := G) (q := q)]
  rw [← uniformAverage_of_pairCollisionCountNat (G := G) (q := q)
    (F := fun k : Nat =>
      max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0)]
  unfold XoP.ANOVA.uniformAverage
  apply congrArg (fun s : ℝ => s / (Fintype.card (Fin q → G) : ℝ))
  apply Finset.sum_congr rfl
  intro y _hy
  simp [pairCollisionCountInt_eq_pairCollisionCountNat (G := G) (q := q) y]

/-- Exact residual by which the occupancy-fiber low-rank positive part exceeds
the spatial-reconstruction term.  This is a concrete finite error term; later
occupancy estimates should bound it by a simpler closed form. -/
def lowRankCollisionFiberResidualErrorBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : NNReal :=
  Real.toNNReal
    (((∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
        (pairCollisionCountFiberCard G q k : ℝ) *
          max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ)) -
      (spatialReconstructionBound G q : ℝ))

/-- Current explicit finite error term for the unconditional LM20-orbit
endpoint.  It combines the higher-rank gain-graph tail with the exact
low-rank occupancy residual. -/
def finiteOrbitErrorBound (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : NNReal :=
  lowRankCollisionFiberResidualErrorBound G q + rankTailErrorBound G q

/-- Average absolute value of the exact higher-rank gain-graph tail, normalized
as a visible density contribution.  This is sharper than the pointwise
`rankTailErrorBound` because it keeps the actual transcript-dependent
rank-tail sum. -/
def rankTailAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq0 : 0 < q) : NNReal :=
  Real.toNNReal
    (XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y =>
        |((collisionSubfamilyRankTailBeyondOneInt
            (G := G) (q := q) y hq0 : ℤ) : ℝ)| /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)))

/-- Real-valued density ratio obtained by keeping the low-rank layers and the
entire signed graphic-rank-two layer.  This is the cancellation-aware
comparison point for the finite-orbit proof: rank two is not charged as an
absolute error here. -/
def compatibleCountRankTwoDensityReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (y : Fin q → G) : ℝ :=
  (((compatibleCountLowRankInt (G := G) (q := q) y +
      collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Real-valued density ratio obtained by keeping the low-rank layers, the
signed rank-two layer, and the signed graphic-rank-three layer.  This is the
next cancellation-aware comparison point: the rank-three layer is exposed
before any absolute value is taken. -/
def compatibleCountRankThreeDensityReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) (y : Fin q → G) : ℝ :=
  (((compatibleCountLowRankInt (G := G) (q := q) y +
      collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankTwoFin q hq2) +
      collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankThreeFin q hq3) : ℤ) : ℝ)) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- The equality-pattern form of the low-rank-plus-rank-two density.  This is
the expression obtained from `compatibleCountRankTwoDensityReal` once the
rank-two gain-graph layer has been identified with the forest-plus-triangle
coefficient. -/
def compatibleCountRankTwoEqualityDensityReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  (((compatibleCountLowRankInt (G := G) (q := q) y +
      ((Fintype.card G) ^ (q - 2) : ℤ) *
        rankTwoEqualityCoefficientInt G q y : ℤ) : ℝ)) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Coefficient form of the low-rank-plus-rank-two-plus-rank-three density.
The rank-two layer is already reduced to equality-pattern statistics; the
rank-three layer is left as its field-size-free alternating coefficient. -/
def compatibleCountRankThreeCoefficientDensityReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  (((compatibleCountLowRankInt (G := G) (q := q) y +
      ((Fintype.card G) ^ (q - 2) : ℤ) *
        rankTwoEqualityCoefficientInt G q y +
      ((Fintype.card G) ^ (q - 3) : ℤ) *
        rankThreeAlternatingCoefficientInt G q y : ℤ) : ℝ)) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Rank-three coefficient density with only support-size `3` and support-size
`4` rank-three subfamilies retained.  This isolates the support sizes expected
to drive the fourth-order affine-geometry correction. -/
def compatibleCountRankThreeSupportLeFourCoefficientDensityReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  (((compatibleCountLowRankInt (G := G) (q := q) y +
      ((Fintype.card G) ^ (q - 2) : ℤ) *
        rankTwoEqualityCoefficientInt G q y +
      ((Fintype.card G) ^ (q - 3) : ℤ) *
        (rankThreeAlternatingCoefficientSupportCardEqInt G q y 3 +
          rankThreeAlternatingCoefficientSupportCardEqInt G q y 4) : ℤ) : ℝ)) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Rank-three coefficient density with only exact support-size `3`
rank-three subfamilies retained. -/
def compatibleCountRankThreeSupportThreeCoefficientDensityReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  (((compatibleCountLowRankInt (G := G) (q := q) y +
      ((Fintype.card G) ^ (q - 2) : ℤ) *
        rankTwoEqualityCoefficientInt G q y +
      ((Fintype.card G) ^ (q - 3) : ℤ) *
        rankThreeAlternatingCoefficientSupportCardEqInt G q y 3 : ℤ) : ℝ)) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Normalized contribution of exact support-size `4` rank-three
subfamilies. -/
def compatibleCountRankThreeSupportFourDensityReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  ((((Fintype.card G) ^ (q - 3) : ℤ) *
      rankThreeAlternatingCoefficientSupportCardEqInt G q y 4 : ℤ) : ℝ) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Normalized contribution of rank-three subfamilies whose query-pair support
has cardinality at least `5`. -/
def compatibleCountRankThreeSupportGeFiveDensityReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℝ :=
  ((((Fintype.card G) ^ (q - 3) : ℤ) *
      rankThreeAlternatingCoefficientSupportCardGeInt G q y 5 : ℤ) : ℝ) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- Scalar rank-two-adjusted density as a function of the visible
pair-collision count and the all-equal-triple count. -/
def rankTwoEqualityDensityFromStatsReal
    (G : Type*) [Fintype G] (q k t : Nat) : ℝ :=
  ((((Fintype.card G) ^ q : ℤ) +
      ((Fintype.card G) ^ (q - 1) : ℤ) *
        ((k : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ)) +
      ((Fintype.card G) ^ (q - 2) : ℤ) *
        rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ) /
    (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)

/-- The dimensionless polynomial factor in the rank-two equality-statistic
density.  The density is the normalizer slack times this factor. -/
def rankTwoEqualityDensityPolynomialFactorReal
    (G : Type*) [Fintype G] (q k t : Nat) : ℝ :=
  1 + (((k : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
      (Fintype.card G : ℝ) +
    ((rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ) /
      (Fintype.card G : ℝ) ^ 2

/-- Scalar rank-two equality density in normalizer-slack form.  This is the
algebraic normal form used by the residual estimate: the density is the
normalizer slack times a quadratic correction in `1 / |G|`. -/
theorem rankTwoEqualityDensityFromStatsReal_eq_slack_mul
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) (k t : Nat) :
    rankTwoEqualityDensityFromStatsReal G q k t =
      XoP.ANOVA.visibleNormalizerSlackReal G q *
        (1 + (((k : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) +
          ((rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) := by
  unfold rankTwoEqualityDensityFromStatsReal XoP.ANOVA.visibleNormalizerSlackReal
  let N : ℝ := Fintype.card G
  let x : ℝ := (((k : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ)
  let c : ℝ := ((rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ)
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hN_pos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hpow12 : q - 2 + 1 = q - 1 := by omega
  have hpow2 : q - 2 + 2 = q := Nat.sub_add_cancel hq2
  field_simp [hN_ne, hZ_ne]
  norm_num [Nat.cast_pow]
  have hpowR12 : (Fintype.card G : ℝ) ^ (q - 1) =
      (Fintype.card G : ℝ) ^ (q - 2) * (Fintype.card G : ℝ) := by
    rw [← pow_succ, hpow12]
  have hpowR2 : (Fintype.card G : ℝ) ^ q =
      (Fintype.card G : ℝ) ^ (q - 2) * (Fintype.card G : ℝ) ^ 2 := by
    rw [← pow_add, hpow2]
  rw [hpowR12, hpowR2]
  ring_nf

/-- Compact version of `rankTwoEqualityDensityFromStatsReal_eq_slack_mul`
using the named dimensionless polynomial factor. -/
theorem rankTwoEqualityDensityFromStatsReal_eq_slack_mul_factor
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) (k t : Nat) :
    rankTwoEqualityDensityFromStatsReal G q k t =
      XoP.ANOVA.visibleNormalizerSlackReal G q *
        rankTwoEqualityDensityPolynomialFactorReal G q k t := by
  rw [rankTwoEqualityDensityFromStatsReal_eq_slack_mul (G := G) (q := q) hq2 hq]
  rfl

/-- Joint low-rank-plus-rank-two density on the zero-collision,
zero-all-equal-triple statistics.  This is the first sign-region target:
unlike the isolated quadratic-positive term, this expression keeps the
low-rank linear correction before the positive part is taken. -/
theorem rankTwoEqualityDensityFromStatsReal_zero_zero_eq_slack_mul
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTwoEqualityDensityFromStatsReal G q 0 0 =
      XoP.ANOVA.visibleNormalizerSlackReal G q *
        (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) +
          ((4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
            2 * ((q.choose 3 : Nat) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) := by
  rw [rankTwoEqualityDensityFromStatsReal_eq_slack_mul (G := G) (q := q) hq2 hq]
  rw [rankTwoEqualityCoefficientFromStatsInt_zero_zero]
  simp

/-- Rank two adds a scalar quadratic correction to the low-rank density. -/
theorem rankTwoEqualityDensityFromStatsReal_eq_lowRank_add_quadratic
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) (k t : Nat) :
    rankTwoEqualityDensityFromStatsReal G q k t =
      lowRankDensityFromCollisionCountReal G q (k : ℤ) +
        XoP.ANOVA.visibleNormalizerSlackReal G q *
          (((rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  rw [rankTwoEqualityDensityFromStatsReal_eq_slack_mul
    (G := G) (q := q) hq2 hq]
  rw [lowRankDensityFromCollisionCountReal_eq_slack_mul
    (G := G) (q := q) hq0 hq]
  norm_num
  ring_nf

/-- The equality-pattern rank-two density is a scalar function of the visible
pair-collision count and the all-equal-triple count. -/
theorem compatibleCountRankTwoEqualityDensityReal_eq_stats
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    compatibleCountRankTwoEqualityDensityReal G q y =
      rankTwoEqualityDensityFromStatsReal G q
        (pairCollisionCountNat G q y) (visibleAllEqualTripleCountNat G y) := by
  unfold compatibleCountRankTwoEqualityDensityReal rankTwoEqualityDensityFromStatsReal
  rw [compatibleCountLowRankInt_eq_card_pow_add_collisionCount]
  rw [rankTwoEqualityCoefficientInt_eq_pairCollisionCount_sub_choose_add_allEqualTripleCount]
  simp [pairCollisionCountInt_eq_pairCollisionCountNat]

/-- The rank-two equality-pattern identity rewrites the signed rank-two
density into the scalar equality-pattern density.  This is the bridge needed
for the next sign-control step. -/
theorem compatibleCountRankTwoDensityReal_eq_equalityDensity_of_rankTwoEqualityPattern
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q)
    (hpattern : RankTwoEqualityPatternIdentity G q)
    (y : Fin q → G) :
    compatibleCountRankTwoDensityReal G q hq2 y =
      compatibleCountRankTwoEqualityDensityReal G q y := by
  have hlayer :
      collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) =
        ((Fintype.card G) ^ (q - 2) : ℤ) *
          rankTwoEqualityCoefficientInt G q y := by
    unfold collisionSubfamilyRankLayerInt
    rw [← hpattern y]
    apply Finset.sum_congr
    · ext T
      simp [collisionSubfamilyGraphicRankFin, collisionSubfamilyGraphicRankTwoFin]
    · intro T hT
      simp only [Finset.mem_filter] at hT
      by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
      · simp [hcyc, collisionSubfamilyGraphicRankTwoFin]
      · simp [hcyc]
  unfold compatibleCountRankTwoDensityReal compatibleCountRankTwoEqualityDensityReal
  rw [hlayer]

/-- The signed rank-two-adjusted density is now unconditionally equal to the
equality-pattern density. -/
theorem compatibleCountRankTwoDensityReal_eq_equalityDensity
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q)
    (y : Fin q → G) :
    compatibleCountRankTwoDensityReal G q hq2 y =
      compatibleCountRankTwoEqualityDensityReal G q y :=
  compatibleCountRankTwoDensityReal_eq_equalityDensity_of_rankTwoEqualityPattern
    (G := G) (q := q) hq2 (rankTwoEqualityPatternIdentity G q hq2) y

/-- The signed rank-three-adjusted density is pointwise equal to the
coefficient density obtained by factoring the rank-three layer and using the
rank-two equality-pattern identity. -/
theorem compatibleCountRankThreeDensityReal_eq_coefficientDensity
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (y : Fin q → G) :
    compatibleCountRankThreeDensityReal G q hq2 hq3 y =
      compatibleCountRankThreeCoefficientDensityReal G q y := by
  have htwo :
      collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) =
        ((Fintype.card G) ^ (q - 2) : ℤ) *
          rankTwoEqualityCoefficientInt G q y := by
    rw [collisionSubfamily_rankTwoLayer_eq_card_pow_mul_alternatingCoefficient
      (G := G) (q := q) hq2 y]
    rw [rankTwoAlternatingCoefficientIdentity (G := G) (q := q) y]
  have hthree :
      collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankThreeFin q hq3) =
        ((Fintype.card G) ^ (q - 3) : ℤ) *
          rankThreeAlternatingCoefficientInt G q y :=
    collisionSubfamily_rankThreeLayer_eq_card_pow_mul_alternatingCoefficient
      (G := G) (q := q) hq3 y
  unfold compatibleCountRankThreeDensityReal compatibleCountRankThreeCoefficientDensityReal
  rw [htwo, hthree]

/-- The rank-three coefficient density splits into the support-size `3`/`4`
part and the normalized support-size-at-least-`5` remainder. -/
theorem compatibleCountRankThreeCoefficientDensityReal_eq_supportLeFour_add_geFive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    compatibleCountRankThreeCoefficientDensityReal G q y =
      compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y +
        compatibleCountRankThreeSupportGeFiveDensityReal G q y := by
  unfold compatibleCountRankThreeCoefficientDensityReal
    compatibleCountRankThreeSupportLeFourCoefficientDensityReal
    compatibleCountRankThreeSupportGeFiveDensityReal
  rw [rankThreeAlternatingCoefficientInt_eq_supportCard_three_add_four_add_ge_five]
  norm_num [Int.cast_add, Int.cast_mul]
  ring_nf

/-- The support-size `3`/`4` rank-three coefficient density splits into the
exact support-size `3` density plus the normalized exact support-size `4`
contribution. -/
theorem compatibleCountRankThreeSupportLeFourCoefficientDensityReal_eq_supportThree_add_four
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y =
      compatibleCountRankThreeSupportThreeCoefficientDensityReal G q y +
        compatibleCountRankThreeSupportFourDensityReal G q y := by
  unfold compatibleCountRankThreeSupportLeFourCoefficientDensityReal
    compatibleCountRankThreeSupportThreeCoefficientDensityReal
    compatibleCountRankThreeSupportFourDensityReal
  norm_num [Int.cast_add, Int.cast_mul]
  ring_nf

/-- Positive-error contribution of the equality-pattern rank-two density.
This is the post-classification form of `compatibleCountRankTwoPositiveErrorReal`.
-/
def compatibleCountRankTwoEqualityPositiveErrorReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max (compatibleCountRankTwoEqualityDensityReal G q y - 1) 0)

/-- Positive-error contribution of the rank-three coefficient density.  This
is the post-factorization form of `compatibleCountRankThreePositiveErrorReal`.
-/
def compatibleCountRankThreeCoefficientPositiveErrorReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max (compatibleCountRankThreeCoefficientDensityReal G q y - 1) 0)

/-- Positive-error contribution after retaining only support-size `3` and `4`
rank-three coefficient terms. -/
def compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y =>
      max (compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y - 1) 0)

/-- Positive-error contribution after retaining only exact support-size `3`
rank-three coefficient terms. -/
def compatibleCountRankThreeSupportThreeCoefficientPositiveErrorReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y =>
      max (compatibleCountRankThreeSupportThreeCoefficientDensityReal G q y - 1) 0)

/-- Average absolute normalized contribution of exact support-size `4`
rank-three coefficient terms. -/
def compatibleCountRankThreeSupportFourAverageErrorReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => |compatibleCountRankThreeSupportFourDensityReal G q y|)

/-- Average absolute normalized contribution of rank-three coefficient terms
with support cardinality at least `5`. -/
def compatibleCountRankThreeSupportGeFiveAverageErrorReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => |compatibleCountRankThreeSupportGeFiveDensityReal G q y|)

/-- The rank-three coefficient positive error is bounded by the support-size
`3`/`4` positive error plus the average absolute contribution of support-size
at least `5` rank-three terms. -/
theorem compatibleCountRankThreeCoefficientPositiveErrorReal_le_supportLeFour_add_geFive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) :
    compatibleCountRankThreeCoefficientPositiveErrorReal G q ≤
      compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal G q +
        compatibleCountRankThreeSupportGeFiveAverageErrorReal G q := by
  unfold compatibleCountRankThreeCoefficientPositiveErrorReal
    compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal
    compatibleCountRankThreeSupportGeFiveAverageErrorReal
    XoP.ANOVA.uniformAverage
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _hy
  have hsplit := compatibleCountRankThreeCoefficientDensityReal_eq_supportLeFour_add_geFive
    (G := G) (q := q) y
  calc
    max (compatibleCountRankThreeCoefficientDensityReal G q y - 1) 0 ≤
        max (compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y - 1) 0 +
          |compatibleCountRankThreeCoefficientDensityReal G q y -
            compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y| :=
      max_sub_one_le_max_sub_one_add_abs_sub
        (compatibleCountRankThreeCoefficientDensityReal G q y)
        (compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y)
    _ = max (compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y - 1) 0 +
          |compatibleCountRankThreeSupportGeFiveDensityReal G q y| := by
        rw [hsplit]
        ring_nf

/-- The support-size `3`/`4` positive error is bounded by the exact
support-size `3` positive error plus the average absolute contribution of
exact support-size `4` rank-three terms. -/
theorem compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal_le_supportThree_add_four
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) :
    compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal G q ≤
      compatibleCountRankThreeSupportThreeCoefficientPositiveErrorReal G q +
        compatibleCountRankThreeSupportFourAverageErrorReal G q := by
  unfold compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal
    compatibleCountRankThreeSupportThreeCoefficientPositiveErrorReal
    compatibleCountRankThreeSupportFourAverageErrorReal
    XoP.ANOVA.uniformAverage
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _hy
  have hsplit := compatibleCountRankThreeSupportLeFourCoefficientDensityReal_eq_supportThree_add_four
    (G := G) (q := q) y
  calc
    max (compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y - 1) 0 ≤
        max (compatibleCountRankThreeSupportThreeCoefficientDensityReal G q y - 1) 0 +
          |compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y -
            compatibleCountRankThreeSupportThreeCoefficientDensityReal G q y| :=
      max_sub_one_le_max_sub_one_add_abs_sub
        (compatibleCountRankThreeSupportLeFourCoefficientDensityReal G q y)
        (compatibleCountRankThreeSupportThreeCoefficientDensityReal G q y)
    _ = max (compatibleCountRankThreeSupportThreeCoefficientDensityReal G q y - 1) 0 +
          |compatibleCountRankThreeSupportFourDensityReal G q y| := by
        rw [hsplit]
        ring_nf

/-- Positive-error contribution of the scalar two-statistic rank-two equality
density. -/
def rankTwoEqualityStatsPositiveErrorReal
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max
      (rankTwoEqualityDensityFromStatsReal G q
        (pairCollisionCountNat G q y) (visibleAllEqualTripleCountNat G y) - 1) 0)

/-- Positive part of the scalar rank-two quadratic correction.  This is a
cancellation-aware replacement target for the old absolute rank-two layer:
only the positive part of the scalar coefficient contributes. -/
def rankTwoEqualityQuadraticPositiveErrorReal
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max
      (XoP.ANOVA.visibleNormalizerSlackReal G q *
        (((rankTwoEqualityCoefficientFromStatsInt q
            (pairCollisionCountNat G q y)
            (visibleAllEqualTripleCountNat G y) : ℤ) : ℝ) /
          (Fintype.card G : ℝ) ^ 2)) 0)

/-- Nonnegativity of the scalar rank-two quadratic positive part. -/
theorem rankTwoEqualityQuadraticPositiveErrorReal_nonneg
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    0 ≤ rankTwoEqualityQuadraticPositiveErrorReal G q := by
  unfold rankTwoEqualityQuadraticPositiveErrorReal XoP.ANOVA.uniformAverage
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro y _hy
  exact le_max_right _ _

/-- NNReal wrapper for the scalar rank-two quadratic positive part. -/
def rankTwoEqualityQuadraticPositiveErrorBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : NNReal :=
  Real.toNNReal (rankTwoEqualityQuadraticPositiveErrorReal G q)

/-- Coercing the NNReal wrapper recovers the scalar rank-two quadratic
positive part. -/
theorem rankTwoEqualityQuadraticPositiveErrorBound_coe
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) =
      rankTwoEqualityQuadraticPositiveErrorReal G q := by
  unfold rankTwoEqualityQuadraticPositiveErrorBound
  rw [Real.coe_toNNReal _ (rankTwoEqualityQuadraticPositiveErrorReal_nonneg
    (G := G) (q := q))]

/-- The scalar rank-two quadratic positive part as an explicit finite sum over
the two equality-pattern statistics. -/
theorem rankTwoEqualityQuadraticPositiveErrorReal_eq_fiberSum
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    rankTwoEqualityQuadraticPositiveErrorReal G q =
      (∑ kt ∈ Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
          Finset.range (q.choose 3 + 1),
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          max (XoP.ANOVA.visibleNormalizerSlackReal G q *
            (((rankTwoEqualityCoefficientFromStatsInt q kt.1 kt.2 : ℤ) : ℝ) /
              (Fintype.card G : ℝ) ^ 2)) 0) /
        (Fintype.card (Fin q → G) : ℝ) := by
  unfold rankTwoEqualityQuadraticPositiveErrorReal
  exact uniformAverage_of_rankTwoEqualityStats (G := G) (q := q)
    (F := fun k t =>
      max (XoP.ANOVA.visibleNormalizerSlackReal G q *
        (((rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ) /
          (Fintype.card G : ℝ) ^ 2)) 0)

/-- NNReal form of the scalar rank-two quadratic positive fiber sum. -/
theorem rankTwoEqualityQuadraticPositiveErrorBound_eq_fiberSum
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    rankTwoEqualityQuadraticPositiveErrorBound G q =
      Real.toNNReal
        ((∑ kt ∈ Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
            Finset.range (q.choose 3 + 1),
          (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
            max (XoP.ANOVA.visibleNormalizerSlackReal G q *
              (((rankTwoEqualityCoefficientFromStatsInt q kt.1 kt.2 : ℤ) : ℝ) /
                (Fintype.card G : ℝ) ^ 2)) 0) /
          (Fintype.card (Fin q → G) : ℝ)) := by
  unfold rankTwoEqualityQuadraticPositiveErrorBound
  rw [rankTwoEqualityQuadraticPositiveErrorReal_eq_fiberSum]

/-- If a two-statistic rank-two density is at most the ideal density `1`, its
positive-part fiber contribution is zero.  This is the local sign-control
lemma used to remove whole fibers from the residual sum. -/
theorem rankTwoEqualityStatsPositiveFiberTerm_eq_zero_of_density_le_one
    (G : Type*) [Fintype G] (q k t : Nat)
    (h : rankTwoEqualityDensityFromStatsReal G q k t ≤ 1) :
    max (rankTwoEqualityDensityFromStatsReal G q k t - 1) 0 = 0 := by
  rw [max_eq_right]
  linarith

/-- Zero-collision specialization of the fiber sign-control lemma, stated in
the explicit normal form for the joint low-rank-plus-rank-two density. -/
theorem rankTwoEqualityStatsPositiveFiberTerm_zero_zero_eq_zero_of_slack_mul_le_one
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (h : XoP.ANOVA.visibleNormalizerSlackReal G q *
        (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) +
          ((4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
            2 * ((q.choose 3 : Nat) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) ≤ 1) :
    max (rankTwoEqualityDensityFromStatsReal G q 0 0 - 1) 0 = 0 := by
  apply rankTwoEqualityStatsPositiveFiberTerm_eq_zero_of_density_le_one
  rw [rankTwoEqualityDensityFromStatsReal_zero_zero_eq_slack_mul
    (G := G) (q := q) hq2 hq]
  exact h

/-- Descending-factorial form of the zero-collision sign deletion condition.
This moves the analytic obligation from the abstract normalizer slack to the
exact polynomial inequality involving `(N)_q^2`. -/
theorem rankTwoEqualityStatsPositiveFiberTerm_zero_zero_eq_zero_of_descFactorial_le
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (h : (Fintype.card G : ℝ) ^ (2 * q) *
        (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) +
          ((4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
            2 * ((q.choose 3 : Nat) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)) :
    max (rankTwoEqualityDensityFromStatsReal G q 0 0 - 1) 0 = 0 := by
  apply rankTwoEqualityStatsPositiveFiberTerm_zero_zero_eq_zero_of_slack_mul_le_one
    (G := G) (q := q) hq2 hq
  rw [XoP.ANOVA.visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq
    (G := G) (q := q) hq]
  let A : ℝ := 1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) +
          ((4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
            2 * ((q.choose 3 : Nat) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2
  let D : ℝ := (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)
  change (Fintype.card G : ℝ) ^ (2 * q) / D * A ≤ 1
  have hD_pos : 0 < D := by
    dsimp [D]
    have hdesc : 0 < (Fintype.card G).descFactorial q :=
      Nat.descFactorial_pos.mpr hq
    positivity
  rw [div_mul_eq_mul_div]
  rw [div_le_one hD_pos]
  simpa [A, D] using h

/-- The equality-pattern positive error is exactly the scalar two-statistic
positive error. -/
theorem compatibleCountRankTwoEqualityPositiveErrorReal_eq_statsPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) :
    compatibleCountRankTwoEqualityPositiveErrorReal G q =
      rankTwoEqualityStatsPositiveErrorReal G q := by
  unfold compatibleCountRankTwoEqualityPositiveErrorReal
    rankTwoEqualityStatsPositiveErrorReal
  apply congrArg
  funext y
  exact congrArg (fun x => max (x - 1) 0)
    (compatibleCountRankTwoEqualityDensityReal_eq_stats (G := G) (q := q) y)

/-- The scalar rank-two positive error is bounded by the low-rank positive
error plus the positive part of the scalar quadratic correction.  This keeps
rank-two cancellation: it does not charge every rank-two gain-graph subfamily
by absolute value. -/
theorem rankTwoEqualityStatsPositiveErrorReal_le_lowRank_add_quadraticPositive
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTwoEqualityStatsPositiveErrorReal G q ≤
      compatibleCountLowRankPositiveErrorReal G q +
        rankTwoEqualityQuadraticPositiveErrorReal G q := by
  rw [compatibleCountLowRankPositiveErrorReal_eq_collisionCountScalarAverage
    (G := G) (q := q)]
  unfold rankTwoEqualityStatsPositiveErrorReal
    rankTwoEqualityQuadraticPositiveErrorReal XoP.ANOVA.uniformAverage
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro y _hy
  let k := pairCollisionCountNat G q y
  let t := visibleAllEqualTripleCountNat G y
  have hdens :=
    rankTwoEqualityDensityFromStatsReal_eq_lowRank_add_quadratic
      (G := G) (q := q) hq2 hq k t
  calc
    max (rankTwoEqualityDensityFromStatsReal G q k t - 1) 0 =
        max ((lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) +
          XoP.ANOVA.visibleNormalizerSlackReal G q *
            (((rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ) /
              (Fintype.card G : ℝ) ^ 2)) 0 := by
          rw [hdens]
          ring_nf
    _ ≤ max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 +
        max (XoP.ANOVA.visibleNormalizerSlackReal G q *
          (((rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2)) 0 := by
          exact max_add_zero_le_max_zero_add_max_zero
            (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1)
            (XoP.ANOVA.visibleNormalizerSlackReal G q *
              (((rankTwoEqualityCoefficientFromStatsInt q k t : ℤ) : ℝ) /
                (Fintype.card G : ℝ) ^ 2))
    _ = max (lowRankDensityFromCollisionCountReal G q (pairCollisionCountInt G q y) - 1) 0 +
        max (XoP.ANOVA.visibleNormalizerSlackReal G q *
          (((rankTwoEqualityCoefficientFromStatsInt q
              (pairCollisionCountNat G q y)
              (visibleAllEqualTripleCountNat G y) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2)) 0 := by
          simp [k, t, pairCollisionCountInt_eq_pairCollisionCountNat (G := G) (q := q) y]

/-- The scalar rank-two equality positive error as a finite two-dimensional
sum over the equality-statistic fibers. -/
theorem rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    rankTwoEqualityStatsPositiveErrorReal G q =
      (∑ kt ∈ Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
          Finset.range (q.choose 3 + 1),
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ) := by
  unfold rankTwoEqualityStatsPositiveErrorReal
  exact uniformAverage_of_rankTwoEqualityStats (G := G) (q := q)
    (F := fun k t => max (rankTwoEqualityDensityFromStatsReal G q k t - 1) 0)

/-- If the zero-collision sign inequality holds, the `(K,T_)=(0,0)` fiber can
be deleted from the two-statistic rank-two positive-error sum.  This is the
first concrete fiber-level cancellation step for the joint sign-region
residual. -/
theorem rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum_erase_zero_zero
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (h : (Fintype.card G : ℝ) ^ (2 * q) *
        (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) +
          ((4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
            2 * ((q.choose 3 : Nat) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)) :
    rankTwoEqualityStatsPositiveErrorReal G q =
      (∑ kt ∈ (Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
          Finset.range (q.choose 3 + 1)).erase (0, 0),
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ) := by
  rw [rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum]
  let R : Finset (Nat × Nat) := Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
          Finset.range (q.choose 3 + 1)
  let F : Nat × Nat → ℝ := fun kt =>
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0
  change (∑ kt ∈ R, F kt) / (Fintype.card (Fin q → G) : ℝ) =
      (∑ kt ∈ R.erase (0, 0), F kt) / (Fintype.card (Fin q → G) : ℝ)
  congr 1
  have hmem : (0, 0) ∈ R := by
    dsimp [R]
    simp
  have hzero : F (0, 0) = 0 := by
    dsimp [F]
    rw [rankTwoEqualityStatsPositiveFiberTerm_zero_zero_eq_zero_of_descFactorial_le
      (G := G) (q := q) hq2 hq h]
    simp
  rw [← Finset.add_sum_erase R F hmem]
  simp [hzero]

/-- General fiber-set deletion for the two-statistic positive-error sum.
Any certified nonpositive sign-region fiber may be removed from the finite
rank-two residual sum.  This packages the `Finset.sum_subset` argument once,
so later analytic sign lemmas only need to prove pointwise density conditions
for the fibers they want to delete. -/
theorem rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum_sdiff
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (S : Finset (Nat × Nat))
    (hzero : ∀ kt ∈ S,
      max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0 = 0) :
    rankTwoEqualityStatsPositiveErrorReal G q =
      (∑ kt ∈ (Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
          Finset.range (q.choose 3 + 1)) \ S,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ) := by
  rw [rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum]
  let R : Finset (Nat × Nat) :=
    Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
      Finset.range (q.choose 3 + 1)
  let F : Nat × Nat → ℝ := fun kt =>
    (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
      max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0
  change (∑ kt ∈ R, F kt) / (Fintype.card (Fin q → G) : ℝ) =
      (∑ kt ∈ R \ S, F kt) / (Fintype.card (Fin q → G) : ℝ)
  congr 1
  have hsubset : R \ S ⊆ R := Finset.sdiff_subset
  have hzero_out : ∀ kt ∈ R, kt ∉ R \ S → F kt = 0 := by
    intro kt hktR hktnot
    have hktS : kt ∈ S := by
      by_contra hnotS
      exact hktnot (Finset.mem_sdiff.mpr ⟨hktR, hnotS⟩)
    dsimp [F]
    rw [hzero kt hktS]
    simp
  exact (Finset.sum_subset (s₁ := R \ S) (s₂ := R) (f := F)
    hsubset hzero_out).symm

/-- Density-condition wrapper for general fiber-set deletion.  This is the
form used by analytic estimates: every fiber in `S` whose joint
low-rank-plus-rank-two density is at most the ideal density can be erased from
the positive-error residual. -/
theorem rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum_sdiff_of_density_le_one
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (S : Finset (Nat × Nat))
    (hdens : ∀ kt ∈ S,
      rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 ≤ 1) :
    rankTwoEqualityStatsPositiveErrorReal G q =
      (∑ kt ∈ (Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
          Finset.range (q.choose 3 + 1)) \ S,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ) := by
  apply rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum_sdiff
  intro kt hkt
  exact rankTwoEqualityStatsPositiveFiberTerm_eq_zero_of_density_le_one
    (G := G) (q := q) kt.1 kt.2 (hdens kt hkt)

/-- Positive-error contribution of the low-rank-plus-rank-two density
approximation.  The remaining proof target is to compare this signed
rank-two-adjusted quantity to `spatialReconstructionBound`; the tail bridge
below then only pays ranks three and higher. -/
def compatibleCountRankTwoPositiveErrorReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max (compatibleCountRankTwoDensityReal G q hq2 y - 1) 0)

/-- Positive-error contribution of the rank-three-adjusted signed density. -/
def compatibleCountRankThreePositiveErrorReal
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) : ℝ :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max (compatibleCountRankThreeDensityReal G q hq2 hq3 y - 1) 0)

/-- The rank-two positive part can now be evaluated using only the
equality-pattern density. -/
theorem compatibleCountRankTwoPositiveErrorReal_eq_equalityPositiveError
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) :
    compatibleCountRankTwoPositiveErrorReal G q hq2 =
      compatibleCountRankTwoEqualityPositiveErrorReal G q := by
  unfold compatibleCountRankTwoPositiveErrorReal
    compatibleCountRankTwoEqualityPositiveErrorReal
  apply congrArg
  funext y
  exact congrArg (fun x => max (x - 1) 0)
    (compatibleCountRankTwoDensityReal_eq_equalityDensity (G := G) (q := q) hq2 y)

/-- The rank-three positive part can be evaluated using the coefficient
density.  This is the formal handoff from layer sums to rank-three sign-region
analysis. -/
theorem compatibleCountRankThreePositiveErrorReal_eq_coefficientPositiveError
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) :
    compatibleCountRankThreePositiveErrorReal G q hq2 hq3 =
      compatibleCountRankThreeCoefficientPositiveErrorReal G q := by
  unfold compatibleCountRankThreePositiveErrorReal
    compatibleCountRankThreeCoefficientPositiveErrorReal
  apply congrArg
  funext y
  exact congrArg (fun x => max (x - 1) 0)
    (compatibleCountRankThreeDensityReal_eq_coefficientDensity
      (G := G) (q := q) hq2 hq3 y)

/-- The genuinely higher-rank tail, after ranks zero, one, and two have been
separated.  This is the object whose cardinality bound has `|G|^(q-3)` scale.
-/
def collisionSubfamilyRankTailBeyondTwoInt
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℤ :=
  ∑ r ∈ (Finset.univ.filter (fun r : Fin (q + 1) => 3 ≤ r.val)),
    collisionSubfamilyRankLayerInt (G := G) (q := q) y r

/-- The genuinely higher-rank tail after graphic rank three has also been
separated.  This is the rank-four-and-higher signed tail. -/
def collisionSubfamilyRankTailBeyondThreeInt
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) : ℤ :=
  ∑ r ∈ (Finset.univ.filter (fun r : Fin (q + 1) => 4 ≤ r.val)),
    collisionSubfamilyRankLayerInt (G := G) (q := q) y r

/-- The rank tail beyond rank one decomposes into the rank-two layer plus the
rank tail beyond rank two.  This is the formal boundary where the proof should
eventually use the universality of rank two and reserve gain-graph value
dependence for rank three and higher. -/
theorem collisionSubfamilyRankTailBeyondOneInt_eq_rankTwo_add_tailBeyondTwo
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (hq0 : 0 < q) (hq2 : 2 ≤ q) :
    collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq0 =
      collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankTwoFin q hq2) +
      collisionSubfamilyRankTailBeyondTwoInt (G := G) q y := by
  rw [collisionSubfamilyRankTailBeyondOneInt_eq_sum_rank_ge_two
    (G := G) (q := q) y hq0]
  unfold collisionSubfamilyRankTailBeyondTwoInt
  let r2 : Fin (q + 1) := collisionSubfamilyGraphicRankTwoFin q hq2
  have hr2_mem : r2 ∈ Finset.univ.filter (fun r : Fin (q + 1) => 2 ≤ r.val) := by
    simp [r2, collisionSubfamilyGraphicRankTwoFin]
  rw [← Finset.add_sum_erase _
    (fun r => collisionSubfamilyRankLayerInt (G := G) (q := q) y r) hr2_mem]
  have herase :
      (Finset.univ.filter (fun r : Fin (q + 1) => 2 ≤ r.val)).erase r2 =
        Finset.univ.filter (fun r : Fin (q + 1) => 3 ≤ r.val) := by
    ext r
    simp [r2, collisionSubfamilyGraphicRankTwoFin]
    constructor
    · intro h
      have hvne : r.val ≠ 2 := by
        intro hv
        apply h.1
        exact Fin.ext hv
      omega
    · intro h
      constructor
      · intro hr
        have hv : r.val = 2 := congrArg Fin.val hr
        omega
      · omega
  rw [herase]

/-- The rank tail beyond rank two decomposes into the signed rank-three layer
plus the rank-four-and-higher tail.  This is the next cancellation boundary:
rank three can now be analyzed before taking an absolute-value tail bound. -/
theorem collisionSubfamilyRankTailBeyondTwoInt_eq_rankThree_add_tailBeyondThree
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) (hq3 : 3 ≤ q) :
    collisionSubfamilyRankTailBeyondTwoInt (G := G) q y =
      collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankThreeFin q hq3) +
      collisionSubfamilyRankTailBeyondThreeInt (G := G) q y := by
  unfold collisionSubfamilyRankTailBeyondTwoInt collisionSubfamilyRankTailBeyondThreeInt
  let r3 : Fin (q + 1) := collisionSubfamilyGraphicRankThreeFin q hq3
  have hr3_mem : r3 ∈ Finset.univ.filter (fun r : Fin (q + 1) => 3 ≤ r.val) := by
    simp [r3, collisionSubfamilyGraphicRankThreeFin]
  rw [← Finset.add_sum_erase _
    (fun r => collisionSubfamilyRankLayerInt (G := G) (q := q) y r) hr3_mem]
  have herase :
      (Finset.univ.filter (fun r : Fin (q + 1) => 3 ≤ r.val)).erase r3 =
        Finset.univ.filter (fun r : Fin (q + 1) => 4 ≤ r.val) := by
    ext r
    simp [r3, collisionSubfamilyGraphicRankThreeFin]
    constructor
    · intro h
      have hvne : r.val ≠ 3 := by
        intro hv
        apply h.1
        exact Fin.ext hv
      omega
    · intro h
      constructor
      · intro hr
        have hv : r.val = 3 := congrArg Fin.val hr
        omega
      · omega
  rw [herase]

/-- The rank-three-and-higher tail as a single inclusion-exclusion sum over
collision subfamilies whose graphic rank is at least three. -/
theorem collisionSubfamilyRankTailBeyondTwoInt_eq_subfamily_sum_rank_ge_three
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    collisionSubfamilyRankTailBeyondTwoInt (G := G) q y =
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        3 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ) := by
  unfold collisionSubfamilyRankTailBeyondTwoInt collisionSubfamilyRankLayerInt
  calc
    (∑ r ∈ Finset.univ.filter (fun r : Fin (q + 1) => 3 ≤ r.val),
        ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          collisionSubfamilyGraphicRankFin (q := q) T = r,
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^ (q - r.val)
              else
                0) : ℤ)) =
      ∑ r ∈ Finset.univ.filter (fun r : Fin (q + 1) => 3 ≤ r.val),
        ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          collisionSubfamilyGraphicRankFin (q := q) T = r,
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro r _hr
        apply Finset.sum_congr rfl
        intro T hT
        simp only [Finset.mem_filter] at hT
        rw [hT.2]
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        collisionSubfamilyGraphicRankFin (q := q) T ∈
          (Finset.univ.filter (fun r : Fin (q + 1) => 3 ≤ r.val)),
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ) := by
        exact Finset.sum_fiberwise_eq_sum_filter
          ((Finset.univ : Finset (CollisionEvent q)).powerset)
          (Finset.univ.filter (fun r : Fin (q + 1) => 3 ≤ r.val))
          (collisionSubfamilyGraphicRankFin (q := q))
          (fun T => (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ))
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        3 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ) := by
        apply Finset.sum_congr
        · ext T
          simp [collisionSubfamilyGraphicRankFin]
        · intro T _hT
          simp [collisionSubfamilyGraphicRankFin]

/-- The rank-four-and-higher tail as a single inclusion-exclusion sum over
collision subfamilies whose graphic rank is at least four. -/
theorem collisionSubfamilyRankTailBeyondThreeInt_eq_subfamily_sum_rank_ge_four
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    collisionSubfamilyRankTailBeyondThreeInt (G := G) q y =
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        4 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ) := by
  unfold collisionSubfamilyRankTailBeyondThreeInt collisionSubfamilyRankLayerInt
  calc
    (∑ r ∈ Finset.univ.filter (fun r : Fin (q + 1) => 4 ≤ r.val),
        ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          collisionSubfamilyGraphicRankFin (q := q) T = r,
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^ (q - r.val)
              else
                0) : ℤ)) =
      ∑ r ∈ Finset.univ.filter (fun r : Fin (q + 1) => 4 ≤ r.val),
        ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          collisionSubfamilyGraphicRankFin (q := q) T = r,
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro r _hr
        apply Finset.sum_congr rfl
        intro T hT
        simp only [Finset.mem_filter] at hT
        rw [hT.2]
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        collisionSubfamilyGraphicRankFin (q := q) T ∈
          (Finset.univ.filter (fun r : Fin (q + 1) => 4 ≤ r.val)),
          (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ) := by
        exact Finset.sum_fiberwise_eq_sum_filter
          ((Finset.univ : Finset (CollisionEvent q)).powerset)
          (Finset.univ.filter (fun r : Fin (q + 1) => 4 ≤ r.val))
          (collisionSubfamilyGraphicRankFin (q := q))
          (fun T => (-1 : ℤ) ^ T.card *
            ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
                (Fintype.card G) ^
                  (q - (collisionSubfamilyGraphicRankFin (q := q) T).val)
              else
                0) : ℤ))
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        4 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ) := by
        apply Finset.sum_congr
        · ext T
          simp [collisionSubfamilyGraphicRankFin]
        · intro T _hT
          simp [collisionSubfamilyGraphicRankFin]

/-- Triangle-inequality bound for the rank-three-and-higher tail, retaining the
cycle-consistency filter. -/
theorem abs_collisionSubfamilyRankTailBeyondTwoInt_le_sum_consistent_terms
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    |collisionSubfamilyRankTailBeyondTwoInt (G := G) q y| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        3 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
  rw [collisionSubfamilyRankTailBeyondTwoInt_eq_subfamily_sum_rank_ge_three
    (G := G) (q := q) y]
  calc
    |∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        3 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        3 ≤ collisionSubfamilyGraphicRank (q := q) T,
        |(-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        3 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro T _hT
        by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
        · simp [hcyc, abs_mul]
        · simp [hcyc]

/-- Triangle-inequality bound for the rank-four-and-higher tail, retaining the
cycle-consistency filter. -/
theorem abs_collisionSubfamilyRankTailBeyondThreeInt_le_sum_consistent_terms
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    |collisionSubfamilyRankTailBeyondThreeInt (G := G) q y| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        4 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
  rw [collisionSubfamilyRankTailBeyondThreeInt_eq_subfamily_sum_rank_ge_four
    (G := G) (q := q) y]
  calc
    |∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        4 ≤ collisionSubfamilyGraphicRank (q := q) T,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        4 ≤ collisionSubfamilyGraphicRank (q := q) T,
        |(-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        4 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro T _hT
        by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
        · simp [hcyc, abs_mul]
        · simp [hcyc]

/-- Pointwise normalized form of
`abs_collisionSubfamilyRankTailBeyondTwoInt_le_sum_consistent_terms`. -/
theorem rankTailBeyondTwoPointwise_le_consistentTerms
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) ≤
      (((∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          3 ≤ collisionSubfamilyGraphicRank (q := q) T,
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)) : ℤ) : ℝ) /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  have htailZ := abs_collisionSubfamilyRankTailBeyondTwoInt_le_sum_consistent_terms
    (G := G) (q := q) y
  have htailR :
      |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| ≤
        (((∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          3 ≤ collisionSubfamilyGraphicRank (q := q) T,
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)) : ℤ) : ℝ) := by
    exact_mod_cast htailZ
  exact div_le_div_of_nonneg_right htailR (by positivity)

/-- Pointwise normalized form of
`abs_collisionSubfamilyRankTailBeyondThreeInt_le_sum_consistent_terms`. -/
theorem rankTailBeyondThreePointwise_le_consistentTerms
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q → G) :
    |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) ≤
      (((∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          4 ≤ collisionSubfamilyGraphicRank (q := q) T,
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)) : ℤ) : ℝ) /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  have htailZ := abs_collisionSubfamilyRankTailBeyondThreeInt_le_sum_consistent_terms
    (G := G) (q := q) y
  have htailR :
      |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| ≤
        (((∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          4 ≤ collisionSubfamilyGraphicRank (q := q) T,
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)) : ℤ) : ℝ) := by
    exact_mod_cast htailZ
  exact div_le_div_of_nonneg_right htailR (by positivity)

/-- Coarse closed-form count bound for the rank-three-and-higher tail.  The
important point is the `|G|^(q-3)` scale, one power better than the old
rank-two-and-higher fallback. -/
theorem abs_collisionSubfamilyRankTailBeyondTwoInt_le_powersetCard_mul_card_pow
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq3 : 3 ≤ q) (y : Fin q → G) :
    |collisionSubfamilyRankTailBeyondTwoInt (G := G) q y| ≤
      (((2 ^ (q * (q - 1))) * (Fintype.card G) ^ (q - 3) : Nat) : ℤ) := by
  calc
    |collisionSubfamilyRankTailBeyondTwoInt (G := G) q y| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        3 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
        exact abs_collisionSubfamilyRankTailBeyondTwoInt_le_sum_consistent_terms
          (G := G) (q := q) y
    _ ≤ ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        3 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((Fintype.card G) ^ (q - 3) : ℤ) := by
        apply Finset.sum_le_sum
        intro T hT
        simp only [Finset.mem_filter] at hT
        by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
        · simp only [hcyc, ↓reduceIte]
          have hle_exp : q - collisionSubfamilyGraphicRank (q := q) T ≤ q - 3 := by
            omega
          exact_mod_cast Nat.pow_le_pow_right
            (Nat.succ_le_of_lt Fintype.card_pos) hle_exp
        · simp [hcyc]
    _ = (((((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => 3 ≤ collisionSubfamilyGraphicRank (q := q) T)).card : Nat) *
        (Fintype.card G) ^ (q - 3) : Nat) : ℤ) := by
        simp
    _ ≤ (((2 ^ (q * (q - 1))) * (Fintype.card G) ^ (q - 3) : Nat) : ℤ) := by
        exact_mod_cast Nat.mul_le_mul_right ((Fintype.card G) ^ (q - 3)) (by
          calc
            ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
              (fun T => 3 ≤ collisionSubfamilyGraphicRank (q := q) T)).card ≤
                ((Finset.univ : Finset (CollisionEvent q)).powerset).card := by
                    exact Finset.card_filter_le _ _
              _ = 2 ^ (q * (q - 1)) := by
                    rw [collisionEvent_univ_powerset_card, collisionEvent_card_eq_query_pair_twice])

/-- Coarse closed-form count bound for the rank-four-and-higher tail after the
signed rank-three layer has been separated. -/
theorem abs_collisionSubfamilyRankTailBeyondThreeInt_le_powersetCard_mul_card_pow
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq4 : 4 ≤ q) (y : Fin q → G) :
    |collisionSubfamilyRankTailBeyondThreeInt (G := G) q y| ≤
      (((2 ^ (q * (q - 1))) * (Fintype.card G) ^ (q - 4) : Nat) : ℤ) := by
  calc
    |collisionSubfamilyRankTailBeyondThreeInt (G := G) q y| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        4 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
            (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
          else
            0) : ℤ) := by
        exact abs_collisionSubfamilyRankTailBeyondThreeInt_le_sum_consistent_terms
          (G := G) (q := q) y
    _ ≤ ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        4 ≤ collisionSubfamilyGraphicRank (q := q) T,
        ((Fintype.card G) ^ (q - 4) : ℤ) := by
        apply Finset.sum_le_sum
        intro T hT
        simp only [Finset.mem_filter] at hT
        by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
        · simp only [hcyc, ↓reduceIte]
          have hle_exp : q - collisionSubfamilyGraphicRank (q := q) T ≤ q - 4 := by
            omega
          exact_mod_cast Nat.pow_le_pow_right
            (Nat.succ_le_of_lt Fintype.card_pos) hle_exp
        · simp [hcyc]
    _ = (((((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => 4 ≤ collisionSubfamilyGraphicRank (q := q) T)).card : Nat) *
        (Fintype.card G) ^ (q - 4) : Nat) : ℤ) := by
        simp
    _ ≤ (((2 ^ (q * (q - 1))) * (Fintype.card G) ^ (q - 4) : Nat) : ℤ) := by
        exact_mod_cast Nat.mul_le_mul_right ((Fintype.card G) ^ (q - 4)) (by
          calc
            ((Finset.univ : Finset (CollisionEvent q)).powerset.filter
              (fun T => 4 ≤ collisionSubfamilyGraphicRank (q := q) T)).card ≤
                ((Finset.univ : Finset (CollisionEvent q)).powerset).card := by
                  exact Finset.card_filter_le _ _
            _ = 2 ^ (q * (q - 1)) := by
                  rw [collisionEvent_univ_powerset_card, collisionEvent_card_eq_query_pair_twice])

/-- Coarse closed-form count bound for the rank-two layer using the exact
number of rank-two collision-event subfamilies. -/
theorem abs_collisionSubfamilyRankLayerTwo_le_rankTwoSubfamilyCount_mul_card_pow
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (y : Fin q → G) :
    |collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankTwoFin q hq2)| ≤
      (((rankTwoSubfamilyCount q) * (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
  unfold collisionSubfamilyRankLayerInt
  calc
    |∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        collisionSubfamilyGraphicRankFin (q := q) T = collisionSubfamilyGraphicRankTwoFin q hq2,
        (-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - (collisionSubfamilyGraphicRankTwoFin q hq2).val)
            else
              0) : ℤ)| ≤
      ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        collisionSubfamilyGraphicRankFin (q := q) T = collisionSubfamilyGraphicRankTwoFin q hq2,
        |(-1 : ℤ) ^ T.card *
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - (collisionSubfamilyGraphicRankTwoFin q hq2).val)
            else
              0) : ℤ)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
        collisionSubfamilyGraphicRankFin (q := q) T = collisionSubfamilyGraphicRankTwoFin q hq2,
        ((Fintype.card G) ^ (q - 2) : ℤ) := by
        apply Finset.sum_le_sum
        intro T hT
        by_cases hcyc : collisionSubfamilyCycleConsistent (G := G) (q := q) y T
        · simp [hcyc, collisionSubfamilyGraphicRankTwoFin]
        · simp [hcyc]
    _ = (((((Finset.univ : Finset (CollisionEvent q)).powerset.filter
          (fun T => collisionSubfamilyGraphicRankFin (q := q) T =
            collisionSubfamilyGraphicRankTwoFin q hq2)).card : Nat) *
        (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
        simp
    _ = (((rankTwoSubfamilyCount q) * (Fintype.card G) ^ (q - 2) : Nat) : ℤ) := by
        congr 2
        unfold rankTwoSubfamilyCount
        congr 1
        ext T
        simp [collisionSubfamilyGraphicRankFin, collisionSubfamilyGraphicRankTwoFin]

/-- Exact average absolute contribution of the rank-two layer. -/
def rankTwoLayerAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) : NNReal :=
  Real.toNNReal
    (XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y =>
        |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
            (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)))

/-- Exact average absolute contribution of ranks three and higher. -/
def rankTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  Real.toNNReal
    (XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y =>
        |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)))

/-- Exact average absolute contribution of ranks four and higher, after the
signed rank-three layer has been separated. -/
def rankTailBeyondThreeAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  Real.toNNReal
    (XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y =>
        |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)))

/-- Average high-rank tail bound that keeps the gain-graph consistency filter.
This is a structured replacement for the closed powerset-cardinality fallback:
the remaining analytic task is to bound the average probability that a
rank-three-or-higher labelled subgraph is cycle-consistent. -/
def rankTailBeyondTwoConsistentAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  Real.toNNReal
    (XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y =>
        (((∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          3 ≤ collisionSubfamilyGraphicRank (q := q) T,
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)) : ℤ) : ℝ) /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)))

/-- Average rank-four-and-higher tail bound that keeps the gain-graph
consistency filter after the signed rank-three layer has been exposed. -/
def rankTailBeyondThreeConsistentAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  Real.toNNReal
    (XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y =>
        (((∑ T ∈ (Finset.univ : Finset (CollisionEvent q)).powerset with
          4 ≤ collisionSubfamilyGraphicRank (q := q) T,
          ((if collisionSubfamilyCycleConsistent (G := G) (q := q) y T then
              (Fintype.card G) ^ (q - collisionSubfamilyGraphicRank (q := q) T)
            else
              0) : ℤ)) : ℤ) : ℝ) /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)))

/-- The exact high-rank average tail is bounded by the consistency-filtered
average.  This theorem keeps the gain-graph consistency predicate available
for the next rarity estimate, instead of immediately discarding it with the
closed powerset bound. -/
theorem rankTailBeyondTwoAverageErrorBound_le_consistentAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) :
    rankTailBeyondTwoAverageErrorBound G q ≤
      rankTailBeyondTwoConsistentAverageErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  unfold rankTailBeyondTwoAverageErrorBound
    rankTailBeyondTwoConsistentAverageErrorBound
  exact_mod_cast Real.toNNReal_mono (by
    unfold XoP.ANOVA.uniformAverage
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine Finset.sum_le_sum ?_
    intro y _hy
    simpa [Int.cast_abs] using
      rankTailBeyondTwoPointwise_le_consistentTerms (G := G) (q := q) y)

/-- After the signed rank-three layer is exposed, the exact rank-four-and-higher
average tail is bounded by the rank-four-and-higher consistency-filtered
average. -/
theorem rankTailBeyondThreeAverageErrorBound_le_consistentAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) :
    rankTailBeyondThreeAverageErrorBound G q ≤
      rankTailBeyondThreeConsistentAverageErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  unfold rankTailBeyondThreeAverageErrorBound
    rankTailBeyondThreeConsistentAverageErrorBound
  exact_mod_cast Real.toNNReal_mono (by
    unfold XoP.ANOVA.uniformAverage
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    refine Finset.sum_le_sum ?_
    intro y _hy
    simpa [Int.cast_abs] using
      rankTailBeyondThreePointwise_le_consistentTerms (G := G) (q := q) y)

/-- Exact residual by which the signed rank-two-adjusted positive part exceeds
the spatial reconstruction term.  This replaces the old absolute rank-two
fallback in the sharper proof boundary. -/
def rankTwoPositiveResidualErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) : NNReal :=
  Real.toNNReal
    (compatibleCountRankTwoPositiveErrorReal G q hq2 -
      (spatialReconstructionBound G q : ℝ))

/-- Exact residual by which the signed rank-three-adjusted positive part
exceeds the spatial reconstruction term.  This is the next signed-layer
analogue of `rankTwoPositiveResidualErrorBound`. -/
def rankThreePositiveResidualErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) : NNReal :=
  Real.toNNReal
    (compatibleCountRankThreePositiveErrorReal G q hq2 hq3 -
      (spatialReconstructionBound G q : ℝ))

/-- Real-valued bound interface for the signed rank-three residual.  The
rank-three positive part is first rewritten through the coefficient density,
so the remaining estimate can target the explicit rank-three alternating
coefficient rather than the rank-layer expression. -/
theorem rankThreePositiveResidualErrorBound_le_of_coefficient_real_bound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) (ε : NNReal)
    (h : compatibleCountRankThreeCoefficientPositiveErrorReal G q -
        (spatialReconstructionBound G q : ℝ) ≤ (ε : ℝ)) :
    rankThreePositiveResidualErrorBound G q hq2 hq3 ≤ ε := by
  rw [← NNReal.coe_le_coe]
  unfold rankThreePositiveResidualErrorBound
  rw [compatibleCountRankThreePositiveErrorReal_eq_coefficientPositiveError
    (G := G) (q := q) hq2 hq3]
  calc
    (Real.toNNReal
      (compatibleCountRankThreeCoefficientPositiveErrorReal G q -
        (spatialReconstructionBound G q : ℝ)) : ℝ) ≤
        (Real.toNNReal (ε : ℝ) : ℝ) := by
          exact_mod_cast Real.toNNReal_mono h
    _ = (ε : ℝ) := by simp

/-- The same rank-two-positive residual after reducing the rank-two density to
the two scalar equality statistics: visible pair collisions and visible
all-equal triples.  This is the finite sign-control target for replacing the
opaque transcript average by a two-dimensional occupancy sum. -/
def rankTwoEqualityStatsPositiveResidualErrorBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : NNReal :=
  Real.toNNReal
    (rankTwoEqualityStatsPositiveErrorReal G q -
      (spatialReconstructionBound G q : ℝ))

/-- The signed-rank-two residual used by the current endpoint is exactly the
two-statistic equality-pattern residual. -/
theorem rankTwoPositiveResidualErrorBound_eq_statsResidual
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) :
    rankTwoPositiveResidualErrorBound G q hq2 =
      rankTwoEqualityStatsPositiveResidualErrorBound G q := by
  unfold rankTwoPositiveResidualErrorBound
    rankTwoEqualityStatsPositiveResidualErrorBound
  rw [compatibleCountRankTwoPositiveErrorReal_eq_equalityPositiveError]
  rw [compatibleCountRankTwoEqualityPositiveErrorReal_eq_statsPositive]

/-- The two-statistic residual as an explicit finite fiber sum. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBound_eq_fiberSum
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    rankTwoEqualityStatsPositiveResidualErrorBound G q =
      Real.toNNReal
        (((∑ kt ∈ Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
            Finset.range (q.choose 3 + 1),
          (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
            max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
          (Fintype.card (Fin q → G) : ℝ)) -
        (spatialReconstructionBound G q : ℝ)) := by
  unfold rankTwoEqualityStatsPositiveResidualErrorBound
  rw [rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum]

/-- Erased-support version of the two-statistic rank-two residual.  The finite
set `S` is intended to contain sign-certified fibers whose density is at most
the ideal density; after those fibers are deleted, the residual only charges
the remaining sign-unknown region. -/
def rankTwoEqualityStatsPositiveResidualErrorBoundSdiff
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (S : Finset (Nat × Nat)) : NNReal :=
  Real.toNNReal
    (((∑ kt ∈ (Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
        Finset.range (q.choose 3 + 1)) \ S,
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
      (Fintype.card (Fin q → G) : ℝ)) -
    (spatialReconstructionBound G q : ℝ))

/-- Finite support of the two scalar equality statistics:
visible pair collisions and visible all-equal triples. -/
def rankTwoEqualityStatsSupport (G : Type*) [Fintype G] (q : Nat) :
    Finset (Nat × Nat) :=
  Finset.range (Fintype.card (PairIndex q) + 1) ×ˢ
    Finset.range (q.choose 3 + 1)

/-- Membership in the two-statistic support is the pair of endpoint bounds. -/
theorem mem_rankTwoEqualityStatsSupport_iff
    (G : Type*) [Fintype G] (q : Nat) (kt : Nat × Nat) :
    kt ∈ rankTwoEqualityStatsSupport G q ↔
      kt.1 ≤ Fintype.card (PairIndex q) ∧ kt.2 ≤ q.choose 3 := by
  simp [rankTwoEqualityStatsSupport]

/-- The maximal two-statistic sign-certified region visible to the current
rank-two equality-pattern abstraction: all fibers whose joint
low-rank-plus-rank-two density is at most the ideal density. -/
def rankTwoEqualityStatsNonpositiveFiberSet
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Finset (Nat × Nat) :=
  (rankTwoEqualityStatsSupport G q).filter
      (fun kt => rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 ≤ 1)

/-- Membership in the nonpositive sign-certified region. -/
theorem mem_rankTwoEqualityStatsNonpositiveFiberSet_iff
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (kt : Nat × Nat) :
    kt ∈ rankTwoEqualityStatsNonpositiveFiberSet G q ↔
      kt ∈ rankTwoEqualityStatsSupport G q ∧
        rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 ≤ 1 := by
  simp [rankTwoEqualityStatsNonpositiveFiberSet]

/-- Exact complement of the nonpositive sign-certified region inside the
two-statistic support.  This is the residual sign region still requiring
analytic control: all surviving fibers have density strictly above the ideal
density. -/
def rankTwoEqualityStatsPositiveFiberSet
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Finset (Nat × Nat) :=
  rankTwoEqualityStatsSupport G q \ rankTwoEqualityStatsNonpositiveFiberSet G q

/-- Residual over an explicitly supplied remaining two-statistic region.  This
is the same expression as the erased-support residual, but with the region to
charge named positively rather than as the complement of a deleted set. -/
def rankTwoEqualityStatsPositiveResidualErrorBoundOn
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (R : Finset (Nat × Nat)) : NNReal :=
  Real.toNNReal
    (((∑ kt ∈ R,
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
      (Fintype.card (Fin q → G) : ℝ)) -
    (spatialReconstructionBound G q : ℝ))

/-- Membership in the positive residual sign region is exactly support
membership plus strict density excess. -/
theorem mem_rankTwoEqualityStatsPositiveFiberSet_iff
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (kt : Nat × Nat) :
    kt ∈ rankTwoEqualityStatsPositiveFiberSet G q ↔
      kt ∈ rankTwoEqualityStatsSupport G q ∧
        1 < rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 := by
  constructor
  · intro hkt
    have hsupport : kt ∈ rankTwoEqualityStatsSupport G q :=
      (Finset.mem_sdiff.mp hkt).1
    have hnot : kt ∉ rankTwoEqualityStatsNonpositiveFiberSet G q :=
      (Finset.mem_sdiff.mp hkt).2
    refine ⟨hsupport, not_le.mp ?_⟩
    intro hdensity
    exact hnot ((mem_rankTwoEqualityStatsNonpositiveFiberSet_iff
      (G := G) (q := q) kt).mpr ⟨hsupport, hdensity⟩)
  · rintro ⟨hsupport, hgt⟩
    exact Finset.mem_sdiff.mpr ⟨hsupport, fun hnonpos =>
      (not_le_of_gt hgt)
        ((mem_rankTwoEqualityStatsNonpositiveFiberSet_iff
          (G := G) (q := q) kt).mp hnonpos).2⟩

/-- On the strict positive sign region, the positive part is just the density
excess. -/
theorem rankTwoEqualityStatsPositiveFiberTerm_eq_density_sub_one_of_mem_positiveFiberSet
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (kt : Nat × Nat)
    (hkt : kt ∈ rankTwoEqualityStatsPositiveFiberSet G q) :
    max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0 =
      rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1 := by
  have hgt := ((mem_rankTwoEqualityStatsPositiveFiberSet_iff
    (G := G) (q := q) kt).mp hkt).2
  exact max_eq_left (sub_nonneg.mpr (le_of_lt hgt))

/-- The exact sign-region erased-support residual is the residual charged on
the strict positive two-statistic region. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_nonpositive_eq_on_positiveSet
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
        (rankTwoEqualityStatsNonpositiveFiberSet G q) =
      rankTwoEqualityStatsPositiveResidualErrorBoundOn G q
        (rankTwoEqualityStatsPositiveFiberSet G q) := by
  rfl

/-- The rank-two equality-statistic density excess as one normalized
falling-factorial numerator. -/
theorem rankTwoEqualityDensityFromStatsReal_sub_one_eq_factorial_excess_div
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) (k t : Nat) :
    rankTwoEqualityDensityFromStatsReal G q k t - 1 =
      (((Fintype.card G : ℝ) ^ (2 * q) *
          rankTwoEqualityDensityPolynomialFactorReal G q k t) -
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)) /
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ) := by
  let D : ℝ := (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)
  have hD_pos : 0 < D := by
    dsimp [D]
    have hdesc : 0 < (Fintype.card G).descFactorial q :=
      Nat.descFactorial_pos.mpr hq
    positivity
  have hD_ne : D ≠ 0 := ne_of_gt hD_pos
  have hdensity :
      rankTwoEqualityDensityFromStatsReal G q k t =
        ((Fintype.card G : ℝ) ^ (2 * q) *
          rankTwoEqualityDensityPolynomialFactorReal G q k t) / D := by
    rw [rankTwoEqualityDensityFromStatsReal_eq_slack_mul_factor
      (G := G) (q := q) hq2 hq]
    rw [XoP.ANOVA.visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq
      (G := G) (q := q) hq]
    rw [div_mul_eq_mul_div]
  rw [hdensity]
  field_simp [D, hD_ne]
  ring

/-- On the strict positive sign region, the weighted positive-part sum is an
explicit weighted sum of normalized falling-factorial excesses. -/
theorem rankTwoEqualityStatsPositiveRegionSum_eq_factorialExcessSum
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    (∑ kt ∈ rankTwoEqualityStatsPositiveFiberSet G q,
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) =
    (∑ kt ∈ rankTwoEqualityStatsPositiveFiberSet G q,
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        ((((Fintype.card G : ℝ) ^ (2 * q) *
            rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2) -
          (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : Nat) : ℝ)) /
          (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : Nat) : ℝ))) := by
  apply Finset.sum_congr rfl
  intro kt hkt
  rw [rankTwoEqualityStatsPositiveFiberTerm_eq_density_sub_one_of_mem_positiveFiberSet
    (G := G) (q := q) kt hkt]
  rw [rankTwoEqualityDensityFromStatsReal_sub_one_eq_factorial_excess_div
    (G := G) (q := q) hq2 hq]

/-- The positive-region residual itself is exactly the finite
falling-factorial excess over the strict positive two-statistic region.  This
is the paper-facing form of the remaining rank-two sign-region obligation. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBoundOn_positiveSet_eq_factorialExcess
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTwoEqualityStatsPositiveResidualErrorBoundOn G q
        (rankTwoEqualityStatsPositiveFiberSet G q) =
      Real.toNNReal
        (((∑ kt ∈ rankTwoEqualityStatsPositiveFiberSet G q,
          (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
            ((((Fintype.card G : ℝ) ^ (2 * q) *
                rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2) -
              (((Fintype.card G).descFactorial q *
                (Fintype.card G).descFactorial q : Nat) : ℝ)) /
              (((Fintype.card G).descFactorial q *
                (Fintype.card G).descFactorial q : Nat) : ℝ))) /
          (Fintype.card (Fin q → G) : ℝ)) -
        (spatialReconstructionBound G q : ℝ)) := by
  unfold rankTwoEqualityStatsPositiveResidualErrorBoundOn
  rw [rankTwoEqualityStatsPositiveRegionSum_eq_factorialExcessSum
    (G := G) (q := q) hq2 hq]

/-- The canonical erased-support sign-region residual is the same
falling-factorial excess over the strict positive region.  This combines the
exact sign-region complement with the factorial-excess normal form. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_nonpositive_eq_factorialExcess
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
        (rankTwoEqualityStatsNonpositiveFiberSet G q) =
      Real.toNNReal
        (((∑ kt ∈ rankTwoEqualityStatsPositiveFiberSet G q,
          (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
            ((((Fintype.card G : ℝ) ^ (2 * q) *
                rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2) -
              (((Fintype.card G).descFactorial q *
                (Fintype.card G).descFactorial q : Nat) : ℝ)) /
              (((Fintype.card G).descFactorial q *
                (Fintype.card G).descFactorial q : Nat) : ℝ))) /
          (Fintype.card (Fin q → G) : ℝ)) -
        (spatialReconstructionBound G q : ℝ)) := by
  rw [rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_nonpositive_eq_on_positiveSet]
  exact rankTwoEqualityStatsPositiveResidualErrorBoundOn_positiveSet_eq_factorialExcess
    (G := G) (q := q) hq2 hq

/-- Weighted positive-part contribution of a named two-statistic region.  This
is the region average before subtracting the spatial reconstruction term. -/
def rankTwoEqualityStatsPositiveRegionContributionReal
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (R : Finset (Nat × Nat)) : ℝ :=
  (∑ kt ∈ R,
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
    (Fintype.card (Fin q → G) : ℝ)

/-- Low-collision part of the strict positive two-statistic sign region.  This
contains the fibers that must account for the main spatial term. -/
def rankTwoEqualityStatsLowCollisionPositiveFiberSet
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Finset (Nat × Nat) :=
  (rankTwoEqualityStatsPositiveFiberSet G q).filter (fun kt => kt.1 < 2)

/-- High-collision part of the strict positive two-statistic sign region.  This
is the part intended to be bounded by the second factorial moment of the
visible pair-collision count. -/
def rankTwoEqualityStatsHighCollisionPositiveFiberSet
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Finset (Nat × Nat) :=
  (rankTwoEqualityStatsPositiveFiberSet G q).filter (fun kt => 2 ≤ kt.1)

/-- The strict positive sign region splits into low- and high-collision
subregions. -/
theorem rankTwoEqualityStatsPositiveRegionContributionReal_eq_low_add_high
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    rankTwoEqualityStatsPositiveRegionContributionReal G q
        (rankTwoEqualityStatsPositiveFiberSet G q) =
      rankTwoEqualityStatsPositiveRegionContributionReal G q
        (rankTwoEqualityStatsLowCollisionPositiveFiberSet G q) +
      rankTwoEqualityStatsPositiveRegionContributionReal G q
        (rankTwoEqualityStatsHighCollisionPositiveFiberSet G q) := by
  unfold rankTwoEqualityStatsPositiveRegionContributionReal
    rankTwoEqualityStatsLowCollisionPositiveFiberSet
    rankTwoEqualityStatsHighCollisionPositiveFiberSet
  rw [← add_div]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := rankTwoEqualityStatsPositiveFiberSet G q)
    (p := fun kt => kt.1 < 2)
    (f := fun kt =>
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0)]
  congr 1
  apply Finset.sum_congr
  · ext kt
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hpos, hnot⟩
      exact ⟨hpos, Nat.le_of_not_lt hnot⟩
    · rintro ⟨hpos, hle⟩
      exact ⟨hpos, not_lt_of_ge hle⟩
  · intro kt _hkt
    rfl

/-- Joint two-statistic fibers recover the closed second factorial moment when
the summand depends only on the visible pair-collision count. -/
theorem rankTwoEqualityStatsSupport_chooseTwoContribution_eq_pairIndex_chooseTwo_div_card_sq
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) :
    (∑ kt ∈ rankTwoEqualityStatsSupport G q,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          (((kt.1.choose 2 : Nat) : ℝ))) /
      (Fintype.card (Fin q → G) : ℝ) =
      (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
        (Fintype.card G : ℝ) ^ 2 := by
  have hstats := uniformAverage_of_rankTwoEqualityStats (G := G) (q := q)
    (F := fun k _t => (((k.choose 2 : Nat) : ℝ)))
  have hclosed :=
    uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq_closed
      (G := G) (q := q) hq2
  unfold XoP.ANOVA.uniformAverage at hstats hclosed
  rw [rankTwoEqualityStatsSupport]
  exact hstats.symm.trans hclosed

/-- Pointwise `choose K 2` control on the high-collision positive fibers turns
into a fourth-order averaged contribution via the existing second factorial
moment. -/
theorem rankTwoEqualityStatsHighCollisionPositiveRegionContributionReal_le_chooseTwo
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (ε : NNReal)
    (hpoint : ∀ kt ∈ rankTwoEqualityStatsHighCollisionPositiveFiberSet G q,
      max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0 ≤
        (ε : ℝ) * (((kt.1.choose 2 : Nat) : ℝ))) :
    rankTwoEqualityStatsPositiveRegionContributionReal G q
        (rankTwoEqualityStatsHighCollisionPositiveFiberSet G q) ≤
      (ε : ℝ) * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
        (Fintype.card G : ℝ) ^ 2 := by
  unfold rankTwoEqualityStatsPositiveRegionContributionReal
  have hden_nonneg : 0 ≤ (Fintype.card (Fin q → G) : ℝ) := by positivity
  calc
    (∑ kt ∈ rankTwoEqualityStatsHighCollisionPositiveFiberSet G q,
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
      (Fintype.card (Fin q → G) : ℝ) ≤
      (∑ kt ∈ rankTwoEqualityStatsHighCollisionPositiveFiberSet G q,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          ((ε : ℝ) * (((kt.1.choose 2 : Nat) : ℝ)))) /
      (Fintype.card (Fin q → G) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hden_nonneg
        apply Finset.sum_le_sum
        intro kt hkt
        exact mul_le_mul_of_nonneg_left (hpoint kt hkt) (by positivity)
    _ ≤ (∑ kt ∈ rankTwoEqualityStatsSupport G q,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          ((ε : ℝ) * (((kt.1.choose 2 : Nat) : ℝ)))) /
      (Fintype.card (Fin q → G) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hden_nonneg
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro kt hkt
          have hpos := (Finset.mem_filter.mp hkt).1
          exact ((mem_rankTwoEqualityStatsPositiveFiberSet_iff
            (G := G) (q := q) kt).mp hpos).1
        · intro kt _hsupport _hnot
          positivity
    _ = (ε : ℝ) *
        ((∑ kt ∈ rankTwoEqualityStatsSupport G q,
          (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
            (((kt.1.choose 2 : Nat) : ℝ))) /
          (Fintype.card (Fin q → G) : ℝ)) := by
        have hnum :
            (∑ kt ∈ rankTwoEqualityStatsSupport G q,
              (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
                ((ε : ℝ) * (((kt.1.choose 2 : Nat) : ℝ)))) =
              (ε : ℝ) * (∑ kt ∈ rankTwoEqualityStatsSupport G q,
                (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
                  (((kt.1.choose 2 : Nat) : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro kt _hkt
          ring
        rw [hnum]
        ring
    _ = (ε : ℝ) * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
        (Fintype.card G : ℝ) ^ 2 := by
        rw [rankTwoEqualityStatsSupport_chooseTwoContribution_eq_pairIndex_chooseTwo_div_card_sq
          (G := G) (q := q) hq2]
        ring

/-- Closed averaged high-collision error obtained from a pointwise
`choose K 2` bound with coefficient `ε`. -/
def rankTwoEqualityStatsHighCollisionChooseTwoErrorBound
    (G : Type*) [Fintype G] (q : Nat) (ε : NNReal) : NNReal :=
  Real.toNNReal
    ((ε : ℝ) * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
      (Fintype.card G : ℝ) ^ 2)

/-- Coercion form of `rankTwoEqualityStatsHighCollisionChooseTwoErrorBound`. -/
theorem rankTwoEqualityStatsHighCollisionChooseTwoErrorBound_coe
    (G : Type*) [Fintype G] (q : Nat) (ε : NNReal) :
    (rankTwoEqualityStatsHighCollisionChooseTwoErrorBound G q ε : ℝ) =
      (ε : ℝ) * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
        (Fintype.card G : ℝ) ^ 2 := by
  unfold rankTwoEqualityStatsHighCollisionChooseTwoErrorBound
  rw [Real.coe_toNNReal]
  positivity

/-- Finite scalar envelope for the high-collision part of the rank-two
positive sign region.  It is the maximum normalized excess over all supported
two-statistic fibers with `2 <= K`; unsupported and low-collision fibers
contribute zero to the finite maximum. -/
noncomputable def rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : ℝ :=
  ((rankTwoEqualityStatsSupport G q).image (fun kt : Nat × Nat =>
    if 2 ≤ kt.1 then
      max ((max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (((kt.1.choose 2 : Nat) : ℝ))) 0
    else 0)).max' (by simp [rankTwoEqualityStatsSupport])

/-- Each normalized high-collision fiber term is bounded by the finite envelope
coefficient. -/
theorem rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal_term_le
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (kt : Nat × Nat)
    (hkt : kt ∈ rankTwoEqualityStatsSupport G q) :
    (if 2 ≤ kt.1 then
      max ((max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (((kt.1.choose 2 : Nat) : ℝ))) 0
    else 0) ≤ rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal G q := by
  unfold rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal
  exact Finset.le_max'
    ((rankTwoEqualityStatsSupport G q).image (fun kt : Nat × Nat =>
      if 2 ≤ kt.1 then
        max ((max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
          (((kt.1.choose 2 : Nat) : ℝ))) 0
      else 0))
    _ (Finset.mem_image.mpr ⟨kt, hkt, rfl⟩)

/-- The high-collision finite envelope coefficient is nonnegative. -/
theorem rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal_nonneg
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    0 ≤ rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal G q := by
  unfold rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal
  have hzero_mem : (0 : ℝ) ∈
      (rankTwoEqualityStatsSupport G q).image (fun kt : Nat × Nat =>
        if 2 ≤ kt.1 then
          max ((max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
            (((kt.1.choose 2 : Nat) : ℝ))) 0
        else 0) := by
    refine Finset.mem_image.mpr ⟨(0, 0), ?_, ?_⟩
    · simp [rankTwoEqualityStatsSupport]
    · simp
  exact Finset.le_max' _ _ hzero_mem

/-- NNReal wrapper for the high-collision finite envelope coefficient. -/
def rankTwoEqualityStatsHighCollisionEnvelopeCoefficientBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : NNReal :=
  Real.toNNReal (rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal G q)

/-- Coercing the NNReal high-collision finite envelope recovers the real
coefficient. -/
theorem rankTwoEqualityStatsHighCollisionEnvelopeCoefficientBound_coe
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    (rankTwoEqualityStatsHighCollisionEnvelopeCoefficientBound G q : ℝ) =
      rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal G q := by
  unfold rankTwoEqualityStatsHighCollisionEnvelopeCoefficientBound
  rw [Real.coe_toNNReal _ (rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal_nonneg
    (G := G) (q := q))]

/-- The finite high-collision envelope coefficient gives the pointwise
`choose K 2` control required by
`rankTwoEqualityStatsHighCollisionPositiveRegionContributionReal_le_chooseTwo`.
-/
theorem rankTwoEqualityStatsHighCollisionPositiveFiberTerm_le_envelope_mul_chooseTwo
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (kt : Nat × Nat)
    (hkt : kt ∈ rankTwoEqualityStatsHighCollisionPositiveFiberSet G q) :
    max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0 ≤
      rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal G q *
        (((kt.1.choose 2 : Nat) : ℝ)) := by
  have hpos := (Finset.mem_filter.mp hkt).1
  have hge := (Finset.mem_filter.mp hkt).2
  have hsupport :=
    ((mem_rankTwoEqualityStatsPositiveFiberSet_iff (G := G) (q := q) kt).mp hpos).1
  have hterm :=
    rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal_term_le
      (G := G) (q := q) kt hsupport
  simp [hge] at hterm
  have hratio :
      (max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (((kt.1.choose 2 : Nat) : ℝ)) ≤
      rankTwoEqualityStatsHighCollisionEnvelopeCoefficientReal G q := hterm.1
  have hchoose_pos_nat : 0 < kt.1.choose 2 := Nat.choose_pos hge
  have hchoose_nonneg : 0 ≤ (((kt.1.choose 2 : Nat) : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hratio hchoose_nonneg
  have hchoose_pos : 0 < (((kt.1.choose 2 : Nat) : ℝ)) := by
    exact_mod_cast hchoose_pos_nat
  simpa [div_eq_mul_inv, hchoose_pos.ne', mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The nonpositive sign-certified region can be tested without the abstract
normalizer: after rewriting the normalizer slack, `rho <=2(k,t) <= 1` is
equivalent to a single falling-factorial inequality. -/
theorem mem_rankTwoEqualityStatsNonpositiveFiberSet_iff_pow_mul_factor_le_descFactorial_sq
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) (kt : Nat × Nat) :
    kt ∈ rankTwoEqualityStatsNonpositiveFiberSet G q ↔
      kt ∈ rankTwoEqualityStatsSupport G q ∧
        (Fintype.card G : ℝ) ^ (2 * q) *
            rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2 ≤
          (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : Nat) : ℝ) := by
  let D : ℝ := (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)
  have hD_pos : 0 < D := by
    dsimp [D]
    have hdesc : 0 < (Fintype.card G).descFactorial q :=
      Nat.descFactorial_pos.mpr hq
    positivity
  have hdensity :
      rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 =
        ((Fintype.card G : ℝ) ^ (2 * q) *
          rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2) / D := by
    rw [rankTwoEqualityDensityFromStatsReal_eq_slack_mul_factor
      (G := G) (q := q) hq2 hq]
    rw [XoP.ANOVA.visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq
      (G := G) (q := q) hq]
    rw [div_mul_eq_mul_div]
  rw [mem_rankTwoEqualityStatsNonpositiveFiberSet_iff]
  constructor
  · rintro ⟨hsupport, hdensity_le⟩
    refine ⟨hsupport, ?_⟩
    rw [hdensity] at hdensity_le
    exact (div_le_one hD_pos).mp hdensity_le
  · rintro ⟨hsupport, hle⟩
    refine ⟨hsupport, ?_⟩
    rw [hdensity]
    exact (div_le_one hD_pos).mpr hle

/-- The strict positive sign region can be tested without the abstract
normalizer: after rewriting the normalizer slack, `rho <=2(k,t) > 1` is
equivalent to a single falling-factorial inequality. -/
theorem mem_rankTwoEqualityStatsPositiveFiberSet_iff_descFactorial_sq_lt
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) (kt : Nat × Nat) :
    kt ∈ rankTwoEqualityStatsPositiveFiberSet G q ↔
      kt ∈ rankTwoEqualityStatsSupport G q ∧
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ) <
          (Fintype.card G : ℝ) ^ (2 * q) *
            rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2 := by
  let D : ℝ := (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)
  have hD_pos : 0 < D := by
    dsimp [D]
    have hdesc : 0 < (Fintype.card G).descFactorial q :=
      Nat.descFactorial_pos.mpr hq
    positivity
  have hdensity :
      rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 =
        ((Fintype.card G : ℝ) ^ (2 * q) *
          rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2) / D := by
    rw [rankTwoEqualityDensityFromStatsReal_eq_slack_mul_factor
      (G := G) (q := q) hq2 hq]
    rw [XoP.ANOVA.visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq
      (G := G) (q := q) hq]
    rw [div_mul_eq_mul_div]
  rw [mem_rankTwoEqualityStatsPositiveFiberSet_iff]
  constructor
  · rintro ⟨hsupport, hgt⟩
    refine ⟨hsupport, ?_⟩
    rw [hdensity] at hgt
    exact (one_lt_div hD_pos).mp hgt
  · rintro ⟨hsupport, hlt⟩
    refine ⟨hsupport, ?_⟩
    rw [hdensity]
    exact (one_lt_div hD_pos).mpr hlt

/-- If the factorial sign inequality holds on every supported two-statistic
fiber, the strict positive sign region is empty. -/
theorem rankTwoEqualityStatsPositiveFiberSet_eq_empty_of_forall_pow_mul_factor_le_descFactorial_sq
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (h : ∀ kt, kt ∈ rankTwoEqualityStatsSupport G q →
      (Fintype.card G : ℝ) ^ (2 * q) *
          rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2 ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)) :
    rankTwoEqualityStatsPositiveFiberSet G q = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro kt hkt
  have hpos :=
    (mem_rankTwoEqualityStatsPositiveFiberSet_iff_descFactorial_sq_lt
      (G := G) (q := q) hq2 hq kt).mp hkt
  exact not_lt_of_ge (h kt hpos.1) hpos.2

/-- The positive-region residual is zero on the empty region. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBoundOn_empty
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    rankTwoEqualityStatsPositiveResidualErrorBoundOn G q ∅ = 0 := by
  unfold rankTwoEqualityStatsPositiveResidualErrorBoundOn
  rw [Finset.sum_empty, zero_div]
  exact Real.toNNReal_eq_zero.mpr (sub_nonpos.mpr (by positivity))

/-- Real-valued bound interface for the positive-region residual.  This is the
form intended for the final analytic estimate: prove one scalar inequality for
the weighted density excess over a region `R`, and obtain the corresponding
`NNReal` residual bound. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBoundOn_le_of_real_bound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (R : Finset (Nat × Nat)) (ε : NNReal)
    (h : (((∑ kt ∈ R,
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
      (Fintype.card (Fin q → G) : ℝ)) -
    (spatialReconstructionBound G q : ℝ)) ≤ (ε : ℝ)) :
    rankTwoEqualityStatsPositiveResidualErrorBoundOn G q R ≤ ε := by
  rw [← NNReal.coe_le_coe]
  unfold rankTwoEqualityStatsPositiveResidualErrorBoundOn
  calc
    (Real.toNNReal
      (((∑ kt ∈ R,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ)) -
      (spatialReconstructionBound G q : ℝ)) : ℝ)
        ≤ (Real.toNNReal (ε : ℝ) : ℝ) := by
          exact_mod_cast Real.toNNReal_mono h
    _ = (ε : ℝ) := by simp

/-- Under a pointwise positive-part zero proof on `S`, the original
two-statistic residual equals the erased-support residual. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBound_eq_sdiff
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (S : Finset (Nat × Nat))
    (hzero : ∀ kt ∈ S,
      max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0 = 0) :
    rankTwoEqualityStatsPositiveResidualErrorBound G q =
      rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q S := by
  unfold rankTwoEqualityStatsPositiveResidualErrorBound
    rankTwoEqualityStatsPositiveResidualErrorBoundSdiff
  rw [rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum_sdiff (G := G) (q := q) S hzero]

/-- Density-condition wrapper for erased-support residual equality. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBound_eq_sdiff_of_density_le_one
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (S : Finset (Nat × Nat))
    (hdens : ∀ kt ∈ S,
      rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 ≤ 1) :
    rankTwoEqualityStatsPositiveResidualErrorBound G q =
      rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q S := by
  apply rankTwoEqualityStatsPositiveResidualErrorBound_eq_sdiff
  intro kt hkt
  exact rankTwoEqualityStatsPositiveFiberTerm_eq_zero_of_density_le_one
    (G := G) (q := q) kt.1 kt.2 (hdens kt hkt)

/-- Deleting any rank-two equality-statistic fibers can only decrease the
positive residual.  This is the monotonicity fact behind the sign-region
endpoint: once a fiber has been certified nonpositive, removing it from the
positive-part sum is a genuine improvement, not just a repackaging. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_le
    (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (S : Finset (Nat × Nat)) :
    rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q S ≤
      rankTwoEqualityStatsPositiveResidualErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  unfold rankTwoEqualityStatsPositiveResidualErrorBoundSdiff
    rankTwoEqualityStatsPositiveResidualErrorBound
  rw [rankTwoEqualityStatsPositiveErrorReal_eq_fiberSum (G := G) (q := q)]
  apply Real.toNNReal_mono
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_right
  · let f : Nat × Nat → ℝ := fun kt =>
      (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
        max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0
    have hsubset :
        S ∩ rankTwoEqualityStatsSupport G q ⊆ rankTwoEqualityStatsSupport G q := by
      intro kt hkt
      exact (Finset.mem_inter.mp hkt).2
    have hsum := Finset.sum_sdiff
      (s₁ := S ∩ rankTwoEqualityStatsSupport G q)
      (s₂ := rankTwoEqualityStatsSupport G q) (f := f) hsubset
    have hnonneg : 0 ≤ ∑ kt ∈ S ∩ rankTwoEqualityStatsSupport G q, f kt := by
      apply Finset.sum_nonneg
      intro kt _hkt
      dsimp [f]
      positivity
    have hsdiff_eq :
        rankTwoEqualityStatsSupport G q \ (S ∩ rankTwoEqualityStatsSupport G q) =
          rankTwoEqualityStatsSupport G q \ S := by
      ext kt
      by_cases hsupport : kt ∈ rankTwoEqualityStatsSupport G q <;>
        by_cases hS : kt ∈ S <;> simp [hsupport, hS]
    change (∑ kt ∈ rankTwoEqualityStatsSupport G q \ S, f kt) ≤
      ∑ kt ∈ rankTwoEqualityStatsSupport G q, f kt
    rw [← hsdiff_eq, ← hsum]
    exact le_add_of_nonneg_right hnonneg
  · positivity

/-- The exact average tail beyond rank one is bounded by the sum of the exact
rank-two average contribution and the exact average contribution of ranks
three and higher. -/
theorem rankTailAverageErrorBound_le_rankTwo_add_tailBeyondTwoAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) :
    rankTailAverageErrorBound G q hq0 ≤
      rankTwoLayerAverageErrorBound G q hq2 +
        rankTailBeyondTwoAverageErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  unfold rankTailAverageErrorBound rankTwoLayerAverageErrorBound
    rankTailBeyondTwoAverageErrorBound
  have hnonneg_tail :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankTailBeyondOneInt
              (G := G) (q := q) y hq0 : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  have hnonneg_two :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
              (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  have hnonneg_beyond :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  simp only [NNReal.coe_add]
  rw [Real.coe_toNNReal _ hnonneg_tail, Real.coe_toNNReal _ hnonneg_two,
    Real.coe_toNNReal _ hnonneg_beyond]
  unfold XoP.ANOVA.uniformAverage
  rw [← add_div]
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _hy
  have hdecomp := collisionSubfamilyRankTailBeyondOneInt_eq_rankTwo_add_tailBeyondTwo
    (G := G) (q := q) y hq0 hq2
  have hZ_nonneg : 0 ≤ (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
    positivity
  calc
    |((collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq0 : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) =
      |(((collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ) +
        ((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ))| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
          rw [hdecomp]
          norm_num
    _ ≤ (|((collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| +
        |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)|) /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
          exact div_le_div_of_nonneg_right (abs_add_le _ _) hZ_nonneg
    _ = |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) +
        |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
          rw [add_div]

/-- Pointwise normalized density bound for the rank-three-and-higher tail. -/
theorem rankTailBeyondTwoPointwise_le_rankTailBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq3 : 3 ≤ q) (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) ≤
      (rankTailBeyondTwoErrorBound G q : ℝ) := by
  let N : Nat := Fintype.card G
  let T : Nat := 2 ^ (q * (q - 1))
  let D : Nat := N.descFactorial q * N.descFactorial q
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have htailZ := abs_collisionSubfamilyRankTailBeyondTwoInt_le_powersetCard_mul_card_pow
    (G := G) (q := q) hq3 y
  have htailR :
      |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| ≤
        ((T * N ^ (q - 3) : Nat) : ℝ) := by
    dsimp [T, N]
    exact_mod_cast htailZ
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hZ_pos : 0 < Z := by
    have hZ_nonneg : 0 ≤ Z := by positivity
    exact lt_of_le_of_ne hZ_nonneg (Ne.symm hZ_ne)
  calc
    |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| / Z ≤
        ((T * N ^ (q - 3) : Nat) : ℝ) / Z := by
          exact div_le_div_of_nonneg_right htailR (le_of_lt hZ_pos)
    _ = (rankTailBeyondTwoErrorBound G q : ℝ) := by
          have hN_pos_nat : 0 < N := by
            dsimp [N]
            exact Fintype.card_pos
          have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN_pos_nat
          have hdesc_pos : 0 < N.descFactorial q := by
            exact Nat.descFactorial_pos.mpr (by simpa [N] using hq)
          have hD_ne : (D : ℝ) ≠ 0 := by
            dsimp [D]
            exact_mod_cast Nat.mul_ne_zero (ne_of_gt hdesc_pos) (ne_of_gt hdesc_pos)
          have hZ_eq : Z = (D : ℝ) / (N : ℝ) ^ q := by
            dsimp [Z, D, N, XoP.ANOVA.visibleNormalizerNNReal]
            simp only [Nat.cast_mul, Nat.cast_pow]
            norm_num
          have hpow : q - 3 + q = 2 * q - 3 := by omega
          unfold rankTailBeyondTwoErrorBound
          change ((T * N ^ (q - 3) : Nat) : ℝ) / Z =
            ((((T * N ^ (2 * q - 3) : Nat) : NNReal) / ((D : Nat) : NNReal) : NNReal) : ℝ)
          rw [hZ_eq]
          simp only [NNReal.coe_div, Nat.cast_mul, Nat.cast_pow]
          change ((T : ℝ) * (N : ℝ) ^ (q - 3)) / ((D : ℝ) / (N : ℝ) ^ q) =
            ((T : ℝ) * (N : ℝ) ^ (2 * q - 3)) / (D : ℝ)
          field_simp [hD_ne, hN_ne]
          rw [mul_assoc, ← pow_add, hpow]

/-- Pointwise normalized density bound for the rank-four-and-higher tail. -/
theorem rankTailBeyondThreePointwise_le_rankTailBeyondThreeErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq4 : 4 ≤ q) (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) ≤
      (rankTailBeyondThreeErrorBound G q : ℝ) := by
  let N : Nat := Fintype.card G
  let T : Nat := 2 ^ (q * (q - 1))
  let D : Nat := N.descFactorial q * N.descFactorial q
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have htailZ := abs_collisionSubfamilyRankTailBeyondThreeInt_le_powersetCard_mul_card_pow
    (G := G) (q := q) hq4 y
  have htailR :
      |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| ≤
        ((T * N ^ (q - 4) : Nat) : ℝ) := by
    dsimp [T, N]
    exact_mod_cast htailZ
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hZ_pos : 0 < Z := by
    have hZ_nonneg : 0 ≤ Z := by positivity
    exact lt_of_le_of_ne hZ_nonneg (Ne.symm hZ_ne)
  calc
    |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| / Z ≤
        ((T * N ^ (q - 4) : Nat) : ℝ) / Z := by
          exact div_le_div_of_nonneg_right htailR (le_of_lt hZ_pos)
    _ = (rankTailBeyondThreeErrorBound G q : ℝ) := by
          have hN_pos_nat : 0 < N := by
            dsimp [N]
            exact Fintype.card_pos
          have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN_pos_nat
          have hdesc_pos : 0 < N.descFactorial q := by
            exact Nat.descFactorial_pos.mpr (by simpa [N] using hq)
          have hD_ne : (D : ℝ) ≠ 0 := by
            dsimp [D]
            exact_mod_cast Nat.mul_ne_zero (ne_of_gt hdesc_pos) (ne_of_gt hdesc_pos)
          have hZ_eq : Z = (D : ℝ) / (N : ℝ) ^ q := by
            dsimp [Z, D, N, XoP.ANOVA.visibleNormalizerNNReal]
            simp only [Nat.cast_mul, Nat.cast_pow]
            norm_num
          have hpow : q - 4 + q = 2 * q - 4 := by omega
          unfold rankTailBeyondThreeErrorBound
          change ((T * N ^ (q - 4) : Nat) : ℝ) / Z =
            ((((T * N ^ (2 * q - 4) : Nat) : NNReal) / ((D : Nat) : NNReal) : NNReal) : ℝ)
          rw [hZ_eq]
          simp only [NNReal.coe_div, Nat.cast_mul, Nat.cast_pow]
          change ((T : ℝ) * (N : ℝ) ^ (q - 4)) / ((D : ℝ) / (N : ℝ) ^ q) =
            ((T : ℝ) * (N : ℝ) ^ (2 * q - 4)) / (D : ℝ)
          field_simp [hD_ne, hN_ne]
          rw [mul_assoc, ← pow_add, hpow]

/-- The exact average rank-three-and-higher tail is bounded by the closed
pointwise rank-three-and-higher fallback. -/
theorem rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq3 : 3 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTailBeyondTwoAverageErrorBound G q ≤ rankTailBeyondTwoErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  unfold rankTailBeyondTwoAverageErrorBound
  have hnonneg :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  rw [Real.coe_toNNReal _ hnonneg]
  unfold XoP.ANOVA.uniformAverage
  calc
    (∑ y : Fin q → G,
        |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) /
        ↑(Fintype.card (Fin q → G)) ≤
      (∑ _y : Fin q → G, (rankTailBeyondTwoErrorBound G q : ℝ)) /
        ↑(Fintype.card (Fin q → G)) := by
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun y _hy =>
            rankTailBeyondTwoPointwise_le_rankTailBeyondTwoErrorBound
              (G := G) q hq3 hq y))
          (Nat.cast_nonneg _)
      _ = (rankTailBeyondTwoErrorBound G q : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul]

/-- The exact average rank-four-and-higher tail is bounded by the closed
pointwise rank-four-and-higher fallback. -/
theorem rankTailBeyondThreeAverageErrorBound_le_rankTailBeyondThreeErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq4 : 4 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTailBeyondThreeAverageErrorBound G q ≤ rankTailBeyondThreeErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  unfold rankTailBeyondThreeAverageErrorBound
  have hnonneg :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  rw [Real.coe_toNNReal _ hnonneg]
  unfold XoP.ANOVA.uniformAverage
  calc
    (∑ y : Fin q → G,
        |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) /
        ↑(Fintype.card (Fin q → G)) ≤
      (∑ _y : Fin q → G, (rankTailBeyondThreeErrorBound G q : ℝ)) /
        ↑(Fintype.card (Fin q → G)) := by
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun y _hy =>
            rankTailBeyondThreePointwise_le_rankTailBeyondThreeErrorBound
              (G := G) q hq4 hq y))
          (Nat.cast_nonneg _)
    _ = (rankTailBeyondThreeErrorBound G q : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- Pointwise normalized density bound for the rank-two layer. -/
theorem rankTwoLayerPointwise_le_rankTwoLayerErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) ≤
      (rankTwoLayerErrorBound G q : ℝ) := by
  let N : Nat := Fintype.card G
  let T : Nat := rankTwoSubfamilyCount q
  let D : Nat := N.descFactorial q * N.descFactorial q
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have htailZ :=
    abs_collisionSubfamilyRankLayerTwo_le_rankTwoSubfamilyCount_mul_card_pow
      (G := G) (q := q) hq2 y
  have htailR :
      |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| ≤
        ((T * N ^ (q - 2) : Nat) : ℝ) := by
    dsimp [T, N]
    exact_mod_cast htailZ
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hZ_pos : 0 < Z := by
    have hZ_nonneg : 0 ≤ Z := by positivity
    exact lt_of_le_of_ne hZ_nonneg (Ne.symm hZ_ne)
  calc
    |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
        (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| / Z ≤
        ((T * N ^ (q - 2) : Nat) : ℝ) / Z := by
          exact div_le_div_of_nonneg_right htailR (le_of_lt hZ_pos)
    _ = (rankTwoLayerErrorBound G q : ℝ) := by
          have hN_pos_nat : 0 < N := by
            dsimp [N]
            exact Fintype.card_pos
          have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN_pos_nat
          have hdesc_pos : 0 < N.descFactorial q := by
            exact Nat.descFactorial_pos.mpr (by simpa [N] using hq)
          have hD_ne : (D : ℝ) ≠ 0 := by
            dsimp [D]
            exact_mod_cast Nat.mul_ne_zero (ne_of_gt hdesc_pos) (ne_of_gt hdesc_pos)
          have hZ_eq : Z = (D : ℝ) / (N : ℝ) ^ q := by
            dsimp [Z, D, N, XoP.ANOVA.visibleNormalizerNNReal]
            simp only [Nat.cast_mul, Nat.cast_pow]
            norm_num
          have hpow : q - 2 + q = 2 * q - 2 := by omega
          unfold rankTwoLayerErrorBound
          change ((T * N ^ (q - 2) : Nat) : ℝ) / Z =
            ((((T * N ^ (2 * q - 2) : Nat) : NNReal) / ((D : Nat) : NNReal) : NNReal) : ℝ)
          rw [hZ_eq]
          simp only [NNReal.coe_div, Nat.cast_mul, Nat.cast_pow]
          change ((T : ℝ) * (N : ℝ) ^ (q - 2)) / ((D : ℝ) / (N : ℝ) ^ q) =
            ((T : ℝ) * (N : ℝ) ^ (2 * q - 2)) / (D : ℝ)
          field_simp [hD_ne, hN_ne]
          rw [mul_assoc, ← pow_add, hpow]

/-- The exact average rank-two layer is bounded by the closed pointwise
rank-two fallback. -/
theorem rankTwoLayerAverageErrorBound_le_rankTwoLayerErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTwoLayerAverageErrorBound G q hq2 ≤ rankTwoLayerErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  unfold rankTwoLayerAverageErrorBound
  have hnonneg :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
              (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  rw [Real.coe_toNNReal _ hnonneg]
  unfold XoP.ANOVA.uniformAverage
  calc
    (∑ y : Fin q → G,
        |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) /
        ↑(Fintype.card (Fin q → G)) ≤
      (∑ _y : Fin q → G, (rankTwoLayerErrorBound G q : ℝ)) /
        ↑(Fintype.card (Fin q → G)) := by
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun y _hy =>
            rankTwoLayerPointwise_le_rankTwoLayerErrorBound
              (G := G) q hq2 hq y))
          (Nat.cast_nonneg _)
    _ = (rankTwoLayerErrorBound G q : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- Sharper finite error term using the exact average rank-tail contribution
instead of the pointwise powerset tail bound. -/
def finiteOrbitAverageTailErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq0 : 0 < q) : NNReal :=
  lowRankCollisionFiberResidualErrorBound G q + rankTailAverageErrorBound G q hq0

/-- Finite error term after splitting the exact average tail into the rank-two
layer and the ranks-three-and-higher tail.  This is the next theorem boundary
for the gain-graph proof: rank two can be treated separately, while genuine
high-rank value dependence is isolated in `rankTailBeyondTwoAverageErrorBound`.
-/
def finiteOrbitRankTwoTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) : NNReal :=
  lowRankCollisionFiberResidualErrorBound G q +
    rankTwoLayerAverageErrorBound G q hq2 +
    rankTailBeyondTwoAverageErrorBound G q

/-- Finite error term with an exact rank-two average and the closed pointwise
fallback for ranks three and higher. -/
def finiteOrbitRankTwoClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) : NNReal :=
  lowRankCollisionFiberResidualErrorBound G q +
    rankTwoLayerAverageErrorBound G q hq2 +
    rankTailBeyondTwoErrorBound G q

/-- Sharper finite error term after absorbing the signed rank-two layer into
the main density approximation.  The only exact residual is the positive-part
excess of that rank-two-adjusted density over `B_q(N)`, plus the exact average
absolute ranks-three-and-higher tail. -/
def finiteOrbitRankTwoPositiveTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) : NNReal :=
  rankTwoPositiveResidualErrorBound G q hq2 +
    rankTailBeyondTwoAverageErrorBound G q

/-- Closed fallback for the sharper rank-two-positive endpoint: signed rank
two is kept in the main positive part, and only ranks three and higher use the
closed pointwise cardinality bound. -/
def finiteOrbitRankTwoPositiveClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) : NNReal :=
  rankTwoPositiveResidualErrorBound G q hq2 +
    rankTailBeyondTwoErrorBound G q

/-- Exact-average finite error after exposing the signed rank-three layer:
rank three is kept in the main positive part, and only ranks four and higher
remain in the absolute average tail. -/
def finiteOrbitRankThreePositiveTailBeyondThreeAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) : NNReal :=
  rankThreePositiveResidualErrorBound G q hq2 hq3 +
    rankTailBeyondThreeAverageErrorBound G q

/-- Exact-average finite error after exposing the signed rank-three layer and
retaining the cycle-consistency predicate in the rank-four-and-higher tail. -/
def finiteOrbitRankThreePositiveConsistentBeyondThreeAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) : NNReal :=
  rankThreePositiveResidualErrorBound G q hq2 hq3 +
    rankTailBeyondThreeConsistentAverageErrorBound G q

/-- Closed finite error after exposing the signed rank-three layer: only the
rank-three positive residual and the closed rank-four-and-higher tail remain. -/
def finiteOrbitRankThreePositiveClosedBeyondThreeErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) : NNReal :=
  rankThreePositiveResidualErrorBound G q hq2 hq3 +
    rankTailBeyondThreeErrorBound G q

/-- Exact-average finite error after rewriting the rank-two-positive residual
as a two-statistic equality-pattern sum. -/
def finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  rankTwoEqualityStatsPositiveResidualErrorBound G q +
    rankTailBeyondTwoAverageErrorBound G q

/-- Exact-average finite error after deleting the first certified
two-statistic rank-two sign region, namely the zero-collision
`(K,T_)=(0,0)` fiber.  This is a genuinely smaller proof obligation than
`finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound` once the
zero-collision sign inequality is available. -/
def finiteOrbitRankTwoStatsPositiveEraseZeroZeroTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
    ({(0, 0)} : Finset (Nat × Nat)) +
    rankTailBeyondTwoAverageErrorBound G q

/-- Exact-average finite error after deleting every nonpositive
two-statistic fiber visible to the rank-two equality-pattern density.  The
remaining residual is supported only on fibers with density strictly above
the ideal density. -/
def finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
    (rankTwoEqualityStatsNonpositiveFiberSet G q) +
    rankTailBeyondTwoAverageErrorBound G q

/-- Exact sign-region rank-two residual plus the consistency-filtered
rank-three-and-higher average tail.  This is the next structured Track A
target: prove a rarity bound for the consistency-filtered high-rank term. -/
def finiteOrbitRankTwoStatsPositiveSignRegionConsistentBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
    (rankTwoEqualityStatsNonpositiveFiberSet G q) +
    rankTailBeyondTwoConsistentAverageErrorBound G q

/-- Closed-tail finite error after rewriting the rank-two-positive residual as
a two-statistic equality-pattern sum. -/
def finiteOrbitRankTwoStatsPositiveClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  rankTwoEqualityStatsPositiveResidualErrorBound G q +
    rankTailBeyondTwoErrorBound G q

/-- Closed-tail variant after deleting the zero-collision `(K,T_)=(0,0)`
fiber from the two-statistic residual. -/
def finiteOrbitRankTwoStatsPositiveEraseZeroZeroClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
    ({(0, 0)} : Finset (Nat × Nat)) +
    rankTailBeyondTwoErrorBound G q

/-- Closed-tail variant after deleting every nonpositive two-statistic fiber
visible to the rank-two equality-pattern density. -/
def finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
    (rankTwoEqualityStatsNonpositiveFiberSet G q) +
    rankTailBeyondTwoErrorBound G q

/-- Cancellation-aware finite error with the low-rank occupancy residual, the
positive part of the scalar rank-two quadratic correction, and the exact
average ranks-three-and-higher tail. -/
def finiteOrbitRankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  lowRankCollisionFiberResidualErrorBound G q +
    rankTwoEqualityQuadraticPositiveErrorBound G q +
    rankTailBeyondTwoAverageErrorBound G q

/-- Constant-`12` fourth-order low-rank remainder from the closed quadratic
collision certificate. -/
def twelveClosedQuadraticCollisionErrorBound
    (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  Real.toNNReal
    (12 * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
      (Fintype.card G : ℝ) ^ 4)

/-- Constant-`12` finite error with no low-rank residual: the fourth-order
closed quadratic-collision term, the scalar rank-two quadratic positive part,
and the exact average ranks-three-and-higher tail. -/
def finiteOrbitRankTwoTwelveQuadraticPositiveTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  twelveClosedQuadraticCollisionErrorBound G q +
    rankTwoEqualityQuadraticPositiveErrorBound G q +
    rankTailBeyondTwoAverageErrorBound G q

/-- Closed-tail variant of the scalar rank-two quadratic-positive finite
error. -/
def finiteOrbitRankTwoQuadraticPositiveClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  lowRankCollisionFiberResidualErrorBound G q +
    rankTwoEqualityQuadraticPositiveErrorBound G q +
    rankTailBeyondTwoErrorBound G q

/-- Closed finite error after the gain-graph rank split:
exact low-rank residual, closed rank-two fallback, and closed rank-three-and
higher fallback. -/
def finiteOrbitClosedRankSplitErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : NNReal :=
  lowRankCollisionFiberResidualErrorBound G q +
    rankTwoLayerErrorBound G q +
    rankTailBeyondTwoErrorBound G q

/-- Closed rank-split tail without the low-rank occupancy residual.  This is
the target tail once the low-rank positive part has been bounded directly by
the spatial-reconstruction term. -/
def rankSplitTailErrorBound (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  rankTwoLayerErrorBound G q + rankTailBeyondTwoErrorBound G q

/-- Closed-form fallback for the low-rank occupancy residual.  It replaces the
exact collision-count fiber average by the largest scalar low-rank positive
part possible on the finite support `0 <= k <= #PairIndex`.  This is cruder
than `lowRankCollisionFiberResidualErrorBound`, but it exposes a simple
finite-\(q,N\) expression. -/
def lowRankCollisionMaxResidualErrorBound (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  Real.toNNReal
    (max (lowRankDensityFromCollisionCountReal G q
        (Fintype.card (PairIndex q) : ℤ) - 1) 0 -
      (spatialReconstructionBound G q : ℝ))

/-- Finite error term using the closed-form low-rank residual fallback and the
exact average higher-rank gain-graph tail. -/
def finiteOrbitAverageTailMaxResidualErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq0 : 0 < q) : NNReal :=
  lowRankCollisionMaxResidualErrorBound G q + rankTailAverageErrorBound G q hq0

/-- Fully closed fallback finite error term: the endpoint low-rank residual
plus the existing closed-form pointwise rank-tail bound.  This is the most
concrete current `B_q(N)+E(q,N)` RHS because neither summand refers to
occupancy fibers or an average over transcripts. -/
def finiteOrbitMaxResidualErrorBound
    (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  lowRankCollisionMaxResidualErrorBound G q + rankTailErrorBound G q

/-- Fully closed gain-graph rank-split fallback: closed low-rank residual,
closed rank-two fallback, and closed rank-three-and-higher fallback. -/
def finiteOrbitMaxResidualClosedRankSplitErrorBound
    (G : Type*) [Fintype G] (q : Nat) : NNReal :=
  lowRankCollisionMaxResidualErrorBound G q +
    rankTwoLayerErrorBound G q +
    rankTailBeyondTwoErrorBound G q

/-- Closed slack-form value of the max low-rank residual fallback. -/
theorem lowRankCollisionMaxResidualErrorBound_eq_slack
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G] (q : Nat)
    (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    lowRankCollisionMaxResidualErrorBound G q =
      Real.toNNReal
        (max (XoP.ANOVA.visibleNormalizerSlackReal G q *
            (1 - (Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ)) - 1) 0 -
          (spatialReconstructionBound G q : ℝ)) := by
  unfold lowRankCollisionMaxResidualErrorBound
  rw [lowRankDensityFromCollisionCountReal_pairIndex_card_eq
    (G := G) (q := q) hq0 hq]

/-- A real number is bounded by a baseline plus its positive residual over that
baseline. -/
theorem le_add_positive_residual (x b : ℝ) :
    x ≤ b + max (x - b) 0 := by
  by_cases h : 0 ≤ x - b
  · rw [max_eq_left h]
    linarith
  · have hle : x - b ≤ 0 := le_of_not_ge h
    rw [max_eq_right hle]
    linarith

/-- The rank-two-adjusted positive part is bounded by the spatial term plus
its exact positive residual over that term. -/
theorem compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_residual
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) :
    compatibleCountRankTwoPositiveErrorReal G q hq2 ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankTwoPositiveResidualErrorBound G q hq2 : ℝ) := by
  unfold rankTwoPositiveResidualErrorBound
  let x : ℝ := compatibleCountRankTwoPositiveErrorReal G q hq2
  let b : ℝ := (spatialReconstructionBound G q : ℝ)
  change x ≤ b + ↑(Real.toNNReal (x - b))
  rw [Real.coe_toNNReal']
  exact le_add_positive_residual x b

/-- The low-rank positive part is bounded by the spatial term plus the exact
occupancy-fiber residual. -/
theorem compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) :
    compatibleCountLowRankPositiveErrorReal G q ≤
      (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) := by
  rw [compatibleCountLowRankPositiveErrorReal_eq_collisionCountFiberSum
    (G := G) (q := q)]
  unfold lowRankCollisionFiberResidualErrorBound
  let x : ℝ :=
    (∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
      (pairCollisionCountFiberCard G q k : ℝ) *
        max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0) /
      (Fintype.card (Fin q → G) : ℝ)
  let b : ℝ := (spatialReconstructionBound G q : ℝ)
  change x ≤ b + ↑(Real.toNNReal (x - b))
  rw [Real.coe_toNNReal']
  exact le_add_positive_residual x b

/-- Absorbing the signed rank-two layer into the density is never worse than
charging rank two by its average absolute layer contribution.  This is the
formal comparison between the cancellation-aware rank-two-positive endpoint
and the older termwise rank-two split. -/
theorem compatibleCountRankTwoPositiveErrorReal_le_lowRank_add_rankTwoLayerAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) :
    compatibleCountRankTwoPositiveErrorReal G q hq2 ≤
      compatibleCountLowRankPositiveErrorReal G q +
        (rankTwoLayerAverageErrorBound G q hq2 : ℝ) := by
  let avgRankTwo : ℝ :=
    XoP.ANOVA.uniformAverage (Fin q → G)
      (fun y =>
        |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
            (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| /
          (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ))
  have havg_nonneg : 0 ≤ avgRankTwo := by
    unfold avgRankTwo XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (NNReal.coe_nonneg _)
  have hrankTwo_coe :
      (rankTwoLayerAverageErrorBound G q hq2 : ℝ) = avgRankTwo := by
    unfold rankTwoLayerAverageErrorBound
    rw [Real.coe_toNNReal _ havg_nonneg]
  rw [hrankTwo_coe]
  unfold compatibleCountRankTwoPositiveErrorReal compatibleCountLowRankPositiveErrorReal
    XoP.ANOVA.uniformAverage
  dsimp [avgRankTwo]
  unfold XoP.ANOVA.uniformAverage
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro y _hy
  have hdiff :
      |compatibleCountRankTwoDensityReal G q hq2 y -
        compatibleCountLowRankDensityReal G q y| =
      |((collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)| /
        (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
    unfold compatibleCountRankTwoDensityReal compatibleCountLowRankDensityReal
    rw [← sub_div, abs_div]
    rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    have hnum :
        ((compatibleCountLowRankInt (G := G) (q := q) y +
            collisionSubfamilyRankLayerInt (G := G) (q := q) y
              (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ) -
          ((compatibleCountLowRankInt (G := G) (q := q) y : ℤ) : ℝ) =
        ((collisionSubfamilyRankLayerInt (G := G) (q := q) y
          (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ) := by
      rw [Int.cast_add]
      ring
    rw [hnum]
  simpa [hdiff] using
    max_sub_one_le_max_sub_one_add_abs_sub
      (compatibleCountRankTwoDensityReal G q hq2 y)
      (compatibleCountLowRankDensityReal G q y)

/-- Residual-level comparison: after subtracting the spatial reconstruction
term, the signed rank-two-positive residual is bounded by the old low-rank
residual plus the average absolute rank-two layer. -/
theorem rankTwoPositiveResidualErrorBound_le_lowRank_add_rankTwoLayerAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) :
    rankTwoPositiveResidualErrorBound G q hq2 ≤
      lowRankCollisionFiberResidualErrorBound G q +
        rankTwoLayerAverageErrorBound G q hq2 := by
  rw [← NNReal.coe_le_coe]
  unfold rankTwoPositiveResidualErrorBound
  let x : ℝ := compatibleCountRankTwoPositiveErrorReal G q hq2
  let b : ℝ := (spatialReconstructionBound G q : ℝ)
  let e : ℝ :=
    (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
      (rankTwoLayerAverageErrorBound G q hq2 : ℝ)
  have hmain :
      x ≤ compatibleCountLowRankPositiveErrorReal G q +
        (rankTwoLayerAverageErrorBound G q hq2 : ℝ) := by
    dsimp [x]
    exact compatibleCountRankTwoPositiveErrorReal_le_lowRank_add_rankTwoLayerAverage
      (G := G) (q := q) hq2
  have hlow :
      compatibleCountLowRankPositiveErrorReal G q ≤
        b + (lowRankCollisionFiberResidualErrorBound G q : ℝ) := by
    dsimp [b]
    exact compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual
      (G := G) (q := q)
  have hx : x - b ≤ e := by
    dsimp [e]
    linarith
  calc
    (Real.toNNReal (x - b) : ℝ) ≤ (Real.toNNReal e : ℝ) := by
      exact_mod_cast Real.toNNReal_mono hx
    _ = e := by
      rw [Real.coe_toNNReal]
      positivity
    _ = (lowRankCollisionFiberResidualErrorBound G q +
        rankTwoLayerAverageErrorBound G q hq2 : NNReal) := by
      simp [e]

/-- The rank-two-adjusted positive part is bounded by the spatial term, the
exact low-rank occupancy residual, and only the positive part of the scalar
rank-two quadratic correction.  This is the cancellation-aware replacement
for charging rank two by an absolute-value layer. -/
theorem compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual_add_quadraticPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    compatibleCountRankTwoPositiveErrorReal G q hq2 ≤
      (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) := by
  have hstats :=
    rankTwoEqualityStatsPositiveErrorReal_le_lowRank_add_quadraticPositive
      (G := G) q hq2 hq
  have hlow :=
    compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual
      (G := G) (q := q)
  calc
    compatibleCountRankTwoPositiveErrorReal G q hq2 =
        rankTwoEqualityStatsPositiveErrorReal G q := by
          rw [compatibleCountRankTwoPositiveErrorReal_eq_equalityPositiveError
            (G := G) (q := q) hq2]
          rw [compatibleCountRankTwoEqualityPositiveErrorReal_eq_statsPositive
            (G := G) (q := q)]
    _ ≤ compatibleCountLowRankPositiveErrorReal G q +
        rankTwoEqualityQuadraticPositiveErrorReal G q := hstats
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          (lowRankCollisionFiberResidualErrorBound G q : ℝ)) +
        rankTwoEqualityQuadraticPositiveErrorReal G q := by
          exact add_le_add hlow le_rfl
    _ = (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) := by
          rw [rankTwoEqualityQuadraticPositiveErrorBound_coe]

/-- The exact two-statistic rank-two residual is controlled by the older
quadratic-positive route.  This records the comparison at the residual level:
the sign-region/statistics endpoint is never worse than the scalar
quadratic-positive endpoint. -/
theorem rankTwoEqualityStatsPositiveResidualErrorBound_le_lowRank_add_quadraticPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTwoEqualityStatsPositiveResidualErrorBound G q ≤
      lowRankCollisionFiberResidualErrorBound G q +
        rankTwoEqualityQuadraticPositiveErrorBound G q := by
  rw [← rankTwoPositiveResidualErrorBound_eq_statsResidual (G := G) (q := q) hq2]
  rw [← NNReal.coe_le_coe]
  unfold rankTwoPositiveResidualErrorBound
  let x : ℝ := compatibleCountRankTwoPositiveErrorReal G q hq2
  let b : ℝ := (spatialReconstructionBound G q : ℝ)
  let e : ℝ :=
    (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
      (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ)
  have hmain :=
    compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual_add_quadraticPositive
      (G := G) q hq2 hq
  have hx : x - b ≤ e := by
    dsimp [x, b, e]
    linarith
  calc
    (Real.toNNReal (x - b) : ℝ) ≤ (Real.toNNReal e : ℝ) := by
      exact_mod_cast Real.toNNReal_mono hx
    _ = e := by
      rw [Real.coe_toNNReal]
      positivity
    _ = (lowRankCollisionFiberResidualErrorBound G q +
        rankTwoEqualityQuadraticPositiveErrorBound G q : NNReal) := by
      simp [e]

/-- The exact two-statistic finite-error endpoint is bounded by the scalar
quadratic-positive finite-error endpoint.  This comparison lets later
arguments use the sharper sign-region/statistics RHS while still inheriting
any closed estimate proved for the quadratic-positive RHS. -/
theorem finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound_le_quadraticPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound G q ≤
      finiteOrbitRankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound G q := by
  unfold finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound
    finiteOrbitRankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound
  simpa [add_assoc] using
    add_le_add
      (rankTwoEqualityStatsPositiveResidualErrorBound_le_lowRank_add_quadraticPositive
        (G := G) q hq2 hq)
      (le_rfl : rankTailBeyondTwoAverageErrorBound G q ≤ rankTailBeyondTwoAverageErrorBound G q)

/-- The exact sign-region endpoint is never worse than the unfiltered
two-statistic endpoint: it deletes precisely the rank-two fibers whose
two-statistic density is at most the ideal density. -/
theorem finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound_le_statsPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) :
    finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound G q ≤
      finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound G q := by
  unfold finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound
    finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound
  exact add_le_add
    (rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_le
      (G := G) (q := q) (S := rankTwoEqualityStatsNonpositiveFiberSet G q))
    (le_rfl : rankTailBeyondTwoAverageErrorBound G q ≤ rankTailBeyondTwoAverageErrorBound G q)

/-- Consequently, the sign-region finite endpoint inherits every scalar
quadratic-positive bound while keeping a smaller rank-two residual. -/
theorem finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound_le_quadraticPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound G q ≤
      finiteOrbitRankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound G q :=
  (finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound_le_statsPositive
    (G := G) (q := q)).trans
    (finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound_le_quadraticPositive
      (G := G) q hq2 hq)

/-- Closed-tail analogue of the sign-region comparison: the exact
sign-region closed endpoint is never worse than the unfiltered two-statistic
closed endpoint. -/
theorem finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound_le_statsPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) :
    finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound G q ≤
      finiteOrbitRankTwoStatsPositiveClosedBeyondTwoErrorBound G q := by
  unfold finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound
    finiteOrbitRankTwoStatsPositiveClosedBeyondTwoErrorBound
  exact add_le_add
    (rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_le
      (G := G) (q := q) (S := rankTwoEqualityStatsNonpositiveFiberSet G q))
    (le_rfl : rankTailBeyondTwoErrorBound G q ≤ rankTailBeyondTwoErrorBound G q)

/-- Closed-tail analogue of the scalar fallback comparison: the exact
sign-region closed endpoint inherits the older scalar quadratic-positive
closed estimate while keeping the smaller rank-two proof obligation. -/
theorem finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound_le_quadraticPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound G q ≤
      finiteOrbitRankTwoQuadraticPositiveClosedBeyondTwoErrorBound G q := by
  unfold finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound
    finiteOrbitRankTwoQuadraticPositiveClosedBeyondTwoErrorBound
  exact add_le_add
    ((rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_le
      (G := G) (q := q) (S := rankTwoEqualityStatsNonpositiveFiberSet G q)).trans
      (rankTwoEqualityStatsPositiveResidualErrorBound_le_lowRank_add_quadraticPositive
        (G := G) q hq2 hq))
    (le_rfl : rankTailBeyondTwoErrorBound G q ≤ rankTailBeyondTwoErrorBound G q)

/-- If the low-rank positive-error bound is discharged, the signed-rank-two
quadratic route no longer needs the separate low-rank occupancy residual. -/
theorem compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_quadraticPositive_of_lowRank
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q) :
    compatibleCountRankTwoPositiveErrorReal G q hq2 ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) := by
  have hstats :=
    rankTwoEqualityStatsPositiveErrorReal_le_lowRank_add_quadraticPositive
      (G := G) q hq2 hq
  rw [compatibleCountRankTwoPositiveErrorReal_eq_equalityPositiveError
    (G := G) q hq2]
  rw [compatibleCountRankTwoEqualityPositiveErrorReal_eq_statsPositive
    (G := G) q]
  unfold CompatibleCountLowRankPositiveErrorBound at hlow
  calc
    rankTwoEqualityStatsPositiveErrorReal G q ≤
        compatibleCountLowRankPositiveErrorReal G q +
          rankTwoEqualityQuadraticPositiveErrorReal G q := hstats
    _ ≤ (spatialReconstructionBound G q : ℝ) +
          rankTwoEqualityQuadraticPositiveErrorReal G q := by
          simpa [add_comm] using add_le_add_right hlow
            (rankTwoEqualityQuadraticPositiveErrorReal G q)
    _ = (spatialReconstructionBound G q : ℝ) +
          (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) := by
          rw [rankTwoEqualityQuadraticPositiveErrorBound_coe]

/-- The low-rank positive part is bounded by evaluating the scalar
collision-count expression at the maximum possible visible pair-collision
count.  This is the closed-form fallback for the exact occupancy fiber average.
-/
theorem compatibleCountLowRankPositiveErrorReal_le_pairIndex_card_positivePart
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    compatibleCountLowRankPositiveErrorReal G q ≤
      max (lowRankDensityFromCollisionCountReal G q
        (Fintype.card (PairIndex q) : ℤ) - 1) 0 := by
  rw [compatibleCountLowRankPositiveErrorReal_eq_collisionCountScalarAverage
    (G := G) (q := q)]
  unfold XoP.ANOVA.uniformAverage
  let m : ℝ := max
    (lowRankDensityFromCollisionCountReal G q
      (Fintype.card (PairIndex q) : ℤ) - 1) 0
  calc
    (∑ x : Fin q → G,
        max (lowRankDensityFromCollisionCountReal G q
          (pairCollisionCountInt G q x) - 1) 0) /
        ↑(Fintype.card (Fin q → G)) ≤
      (∑ _x : Fin q → G, m) / ↑(Fintype.card (Fin q → G)) := by
        apply div_le_div_of_nonneg_right
        · apply Finset.sum_le_sum
          intro y _hy
          have hk :
              pairCollisionCountNat G q y ≤ Fintype.card (PairIndex q) :=
            pairCollisionCountNat_le_pairIndex_card (G := G) (q := q) y
          have hdens :
              lowRankDensityFromCollisionCountReal G q
                  (pairCollisionCountInt G q y) ≤
                lowRankDensityFromCollisionCountReal G q
                  (Fintype.card (PairIndex q) : ℤ) := by
            rw [pairCollisionCountInt_eq_pairCollisionCountNat (G := G) (q := q) y]
            exact lowRankDensityFromCollisionCountReal_le_pairIndex_card
              (G := G) (q := q) hq0 hq (pairCollisionCountNat G q y) hk
          exact max_le_max (sub_le_sub_right hdens 1) le_rfl
        · exact Nat.cast_nonneg _
    _ = m := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The exact occupancy-fiber residual is bounded by the closed-form residual
obtained from the endpoint collision-count value. -/
theorem lowRankCollisionFiberResidualErrorBound_le_lowRankCollisionMaxResidualErrorBound
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    lowRankCollisionFiberResidualErrorBound G q ≤
      lowRankCollisionMaxResidualErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  unfold lowRankCollisionFiberResidualErrorBound lowRankCollisionMaxResidualErrorBound
  let x : ℝ :=
    (∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
      (pairCollisionCountFiberCard G q k : ℝ) *
        max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0) /
      (Fintype.card (Fin q → G) : ℝ)
  let b : ℝ := (spatialReconstructionBound G q : ℝ)
  let m : ℝ := max
    (lowRankDensityFromCollisionCountReal G q
      (Fintype.card (PairIndex q) : ℤ) - 1) 0
  have hx : x ≤ m := by
    change
      (∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
        (pairCollisionCountFiberCard G q k : ℝ) *
          max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ) ≤ m
    rw [← compatibleCountLowRankPositiveErrorReal_eq_collisionCountFiberSum
      (G := G) (q := q)]
    exact compatibleCountLowRankPositiveErrorReal_le_pairIndex_card_positivePart
      (G := G) (q := q) hq0 hq
  change Real.toNNReal (x - b) ≤ Real.toNNReal (m - b)
  exact Real.toNNReal_mono (sub_le_sub_right hx b)

/-- The collision slope whose product with the visible pair-collision count
should dominate the low-rank positive part pointwise. -/
def lowRankCollisionSlopeReal (G : Type*) [Fintype G] (q : Nat) : ℝ :=
  (((Fintype.card G).descFactorial q : Nat) : ℝ) /
    ((Fintype.card G : ℝ) ^ (q - 1) *
      (((Fintype.card G - 1 : Nat) : ℝ) ^ 2))

/-- Descending-factorial form of the low-rank zero-collision line check.
This is the `k = 0` analogue of the rank-two zero-fiber sign deletion
condition: once the exact normalizer inequality is known, the positive part at
zero visible pair-collisions is already covered by the spatial line. -/
theorem lowRankDensityZeroPositivePart_le_zero_of_descFactorial_le
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G)
    (h : (Fintype.card G : ℝ) ^ (2 * q) *
        (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
          (Fintype.card G : ℝ))) ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)) :
    max (lowRankDensityFromCollisionCountReal G q (0 : ℤ) - 1) 0 ≤
      lowRankCollisionSlopeReal G q * (0 : ℝ) := by
  rw [mul_zero]
  rw [max_le_iff]
  constructor
  · have hdens : lowRankDensityFromCollisionCountReal G q (0 : ℤ) ≤ 1 := by
      rw [lowRankDensityFromCollisionCountReal_eq_slack_mul
        (G := G) (q := q) hq0 hq]
      rw [XoP.ANOVA.visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq
        (G := G) (q := q) hq]
      have hD_pos :
          0 < (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : Nat) : ℝ) := by
        have hdesc : 0 < (Fintype.card G).descFactorial q :=
          Nat.descFactorial_pos.mpr hq
        positivity
      rw [div_mul_eq_mul_div]
      rw [div_le_one hD_pos]
      simpa using h
    linarith
  · rfl

/-- Small-query discharge of the low-rank zero-collision line check.  This
uses the existing falling-factorial lower bound rather than re-proving the
product estimate. -/
theorem lowRankDensityZeroPositivePart_le_zero_of_queryPair_le_card
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G)
    (hsmall : q * (q - 1) ≤ Fintype.card G) :
    max (lowRankDensityFromCollisionCountReal G q (0 : ℤ) - 1) 0 ≤
      lowRankCollisionSlopeReal G q * (0 : ℝ) := by
  apply lowRankDensityZeroPositivePart_le_zero_of_descFactorial_le
    (G := G) (q := q) hq0 hq
  let N : Nat := Fintype.card G
  let S : ℝ := ∑ i ∈ Finset.range q, (i : ℝ) / (N : ℝ)
  let d : ℝ := ((N.descFactorial q : Nat) : ℝ)
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact Fintype.card_pos
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hqN : q ≤ N := by
    dsimp [N]
    exact hq
  have hlower : 1 - S ≤ d / (N : ℝ) ^ q := by
    dsimp [S, d]
    exact XoP.ANOVA.descFactorial_div_pow_ge_one_sub_sum N q hN_pos_nat hqN
  have hsum_le : S ≤ (1 / 2 : ℝ) := by
    dsimp [S, N]
    exact XoP.ANOVA.sum_range_div_card_le_half_of_queryPair_le_card
      (Fintype.card G) q (Fintype.card_pos) hsmall
  have hfactor :
      1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
          (Fintype.card G : ℝ)) ≤
        (d / (N : ℝ) ^ q) ^ 2 := by
    have hfactor_eq :
        1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) =
          1 - 2 * S := by
      dsimp [S, N]
      norm_num
      rw [← pairIndex_card_div_eq_sum_range_div (Fintype.card G) q]
      ring
    rw [hfactor_eq]
    have h1S_nonneg : 0 ≤ 1 - S := by linarith
    have hr_nonneg : 0 ≤ d / (N : ℝ) ^ q := le_trans h1S_nonneg hlower
    have hsquare : (1 - S) ^ 2 ≤ (d / (N : ℝ) ^ q) ^ 2 := by
      nlinarith [sq_nonneg (d / (N : ℝ) ^ q - (1 - S))]
    have hbase : 1 - 2 * S ≤ (1 - S) ^ 2 := one_sub_two_mul_le_sq_one_sub S
    exact le_trans hbase hsquare
  have hmul :
      (N : ℝ) ^ (2 * q) *
          (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ))) ≤ d * d := by
    have hpow_nonneg : 0 ≤ (N : ℝ) ^ (2 * q) := by positivity
    calc
      (N : ℝ) ^ (2 * q) *
          (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ))) ≤
          (N : ℝ) ^ (2 * q) * (d / (N : ℝ) ^ q) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hfactor hpow_nonneg
      _ = d * d := by
        have hpow_pos : 0 < (N : ℝ) ^ q := pow_pos hN_pos q
        field_simp [hpow_pos.ne']
        ring
  simpa [N, d, Nat.cast_mul] using hmul

/-- Descending-factorial form of the low-rank one-collision line check.  This
packages the positive-part mechanics separately from the analytic inequality
that must compare the one-collision low-rank density with the spatial slope. -/
theorem lowRankDensityOnePositivePart_le_slope_of_descFactorial_le
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G)
    (h : (Fintype.card G : ℝ) ^ (2 * q) *
        (1 + ((((1 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
          (Fintype.card G : ℝ))) ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ) *
          (1 + lowRankCollisionSlopeReal G q)) :
    max (lowRankDensityFromCollisionCountReal G q (1 : ℤ) - 1) 0 ≤
      lowRankCollisionSlopeReal G q * (1 : ℝ) := by
  rw [mul_one]
  rw [max_le_iff]
  constructor
  · have hdens :
        lowRankDensityFromCollisionCountReal G q (1 : ℤ) ≤
          1 + lowRankCollisionSlopeReal G q := by
      rw [lowRankDensityFromCollisionCountReal_eq_slack_mul
        (G := G) (q := q) hq0 hq]
      rw [XoP.ANOVA.visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq
        (G := G) (q := q) hq]
      have hD_pos :
          0 < (((Fintype.card G).descFactorial q *
            (Fintype.card G).descFactorial q : Nat) : ℝ) := by
        have hdesc : 0 < (Fintype.card G).descFactorial q :=
          Nat.descFactorial_pos.mpr hq
        positivity
      rw [div_mul_eq_mul_div]
      rw [div_le_iff₀ hD_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    linarith
  · unfold lowRankCollisionSlopeReal
    positivity

/-- Small-query discharge of the low-rank one-collision line check. -/
theorem lowRankDensityOnePositivePart_le_slope_of_queryPair_le_card
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (hsmall : q * (q - 1) ≤ Fintype.card G) :
    max (lowRankDensityFromCollisionCountReal G q (1 : ℤ) - 1) 0 ≤
      lowRankCollisionSlopeReal G q * (1 : ℝ) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hN2 : 2 ≤ Fintype.card G := le_trans hq2 hq
  apply lowRankDensityOnePositivePart_le_slope_of_descFactorial_le
    (G := G) (q := q) hq0 hq
  let N : Nat := Fintype.card G
  let P : Nat := Fintype.card (PairIndex q)
  let S : ℝ := (P : ℝ) / (N : ℝ)
  let d : ℝ := ((N.descFactorial q : Nat) : ℝ)
  let r : ℝ := d / (N : ℝ) ^ q
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact Fintype.card_pos
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hN2_real : 2 ≤ (N : ℝ) := by
    dsimp [N]
    exact_mod_cast hN2
  have hNm1_pos : 0 < (N : ℝ) - 1 := by linarith
  have hqN : q ≤ N := by
    dsimp [N]
    exact hq
  have hPcase_nat : P = 1 ∨ 3 ≤ P := by
    dsimp [P]
    by_cases hq3 : 3 ≤ q
    · right
      have hpair := pairIndex_card_mul_two (q := q)
      have hsix : 6 ≤ P * 2 := by
        dsimp [P]
        rw [hpair]
        calc
          6 = 3 * 2 := rfl
          _ ≤ q * (q - 1) := Nat.mul_le_mul hq3 (by omega)
      omega
    · left
      have hqeq : q = 2 := by omega
      subst q
      norm_num [pairIndex_card_eq_sum_range]
  have hPcase_real : (P : ℝ) = 1 ∨ 3 ≤ (P : ℝ) := by
    rcases hPcase_nat with hP | hP
    · left
      exact_mod_cast hP
    · right
      exact_mod_cast hP
  have hPsmall_real : 2 * (P : ℝ) ≤ (N : ℝ) := by
    have hpair := pairIndex_card_mul_two (q := q)
    have hnat : 2 * P ≤ N := by
      dsimp [P, N]
      omega
    exact_mod_cast hnat
  have hS_eq_sum :
      S = ∑ i ∈ Finset.range q, (i : ℝ) / (N : ℝ) := by
    dsimp [S, P]
    rw [pairIndex_card_div_eq_sum_range_div]
  have hlower : 1 - S ≤ r := by
    rw [hS_eq_sum]
    dsimp [r, d]
    exact XoP.ANOVA.descFactorial_div_pow_ge_one_sub_sum N q hN_pos_nat hqN
  have hsum_le : S ≤ (1 / 2 : ℝ) := by
    rw [hS_eq_sum]
    exact XoP.ANOVA.sum_range_div_card_le_half_of_queryPair_le_card
      N q hN_pos_nat (by simpa [N] using hsmall)
  have ha_nonneg : 0 ≤ 1 - S := by linarith
  have hr_nonneg : 0 ≤ r := le_trans ha_nonneg hlower
  have hfactor_scalar :
      1 + (1 - 2 * (P : ℝ)) / (N : ℝ) ≤
        (1 - S) ^ 2 *
          (1 + (1 - S) * (N : ℝ) / ((N : ℝ) - 1) ^ 2) := by
    dsimp [S]
    exact one_collision_factor_le_first_order_sq_mul_slope_correction
      (N := (N : ℝ)) (P := (P : ℝ)) hN2_real hPcase_real hPsmall_real
  have hsquare : (1 - S) ^ 2 ≤ r ^ 2 := by
    nlinarith [sq_nonneg (r - (1 - S))]
  have hcoef_nonneg : 0 ≤ (N : ℝ) / ((N : ℝ) - 1) ^ 2 := by positivity
  have hsecond :
      1 + (1 - S) * (N : ℝ) / ((N : ℝ) - 1) ^ 2 ≤
        1 + r * (N : ℝ) / ((N : ℝ) - 1) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hlower hcoef_nonneg
    simpa [mul_div_assoc] using add_le_add_left hmul (1 : ℝ)
  have hsecond_nonneg :
      0 ≤ 1 + (1 - S) * (N : ℝ) / ((N : ℝ) - 1) ^ 2 := by
    have hterm : 0 ≤ (1 - S) * (N : ℝ) / ((N : ℝ) - 1) ^ 2 := by
      exact div_nonneg (mul_nonneg ha_nonneg (le_of_lt hN_pos)) (sq_nonneg _)
    linarith
  have htarget_factor :
      1 + (1 - 2 * (P : ℝ)) / (N : ℝ) ≤
        r ^ 2 * (1 + r * (N : ℝ) / ((N : ℝ) - 1) ^ 2) := by
    calc
      1 + (1 - 2 * (P : ℝ)) / (N : ℝ) ≤
          (1 - S) ^ 2 *
            (1 + (1 - S) * (N : ℝ) / ((N : ℝ) - 1) ^ 2) := hfactor_scalar
      _ ≤ r ^ 2 * (1 + r * (N : ℝ) / ((N : ℝ) - 1) ^ 2) := by
          exact mul_le_mul hsquare hsecond hsecond_nonneg (sq_nonneg r)
  have hslope :
      r * (N : ℝ) / ((N : ℝ) - 1) ^ 2 = lowRankCollisionSlopeReal G q := by
    dsimp [r, d, N]
    unfold lowRankCollisionSlopeReal
    have hN_ne : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt Fintype.card_pos
    have hNm1_ne : ((Fintype.card G : ℝ) - 1) ≠ 0 := ne_of_gt (by
      have hgt : (1 : ℝ) < Fintype.card G := by exact_mod_cast hN2
      linarith)
    have hpow : q - 1 + 1 = q := Nat.sub_add_cancel hq0
    have hpowR :
        (Fintype.card G : ℝ) ^ q =
          (Fintype.card G : ℝ) ^ (q - 1) * (Fintype.card G : ℝ) := by
      rw [← pow_succ, hpow]
    have hsub_cast :
        ((Fintype.card G - 1 : Nat) : ℝ) = (Fintype.card G : ℝ) - 1 := by
      have hone : 1 ≤ Fintype.card G := by omega
      norm_num [Nat.cast_sub hone]
    rw [hsub_cast, hpowR]
    field_simp [hN_ne, hNm1_ne]
  have hfactor :
      1 + ((((1 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
          (Fintype.card G : ℝ)) ≤
        r ^ 2 * (1 + lowRankCollisionSlopeReal G q) := by
    have hfactor_eq :
        1 + ((((1 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) =
          1 + (1 - 2 * (P : ℝ)) / (N : ℝ) := by
      dsimp [P, N]
      norm_num
    rw [hfactor_eq, ← hslope]
    exact htarget_factor
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ (2 * q) := by positivity
  calc
    (Fintype.card G : ℝ) ^ (2 * q) *
        (1 + ((((1 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
          (Fintype.card G : ℝ))) =
        (N : ℝ) ^ (2 * q) *
          (1 + ((((1 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ))) := by simp [N]
    _ ≤ (N : ℝ) ^ (2 * q) *
        (r ^ 2 * (1 + lowRankCollisionSlopeReal G q)) := by
          exact mul_le_mul_of_nonneg_left hfactor hpow_nonneg
    _ = (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ) *
        (1 + lowRankCollisionSlopeReal G q) := by
          dsimp [r, d, N]
          have hpow_pos : 0 < (Fintype.card G : ℝ) ^ q := by
            exact pow_pos (by exact_mod_cast Fintype.card_pos (α := G)) q
          field_simp [hpow_pos.ne']
          rw [show 2 * q = q + q by omega, pow_add]
          norm_num [pow_two, Nat.cast_mul]
          ring

/-- Pointwise low-rank collision-envelope obligation.  This is the remaining
algebraic inequality needed to turn the rank-zero plus rank-one layer into the
spatial-reconstruction term. -/
def CompatibleCountLowRankPointwiseCollisionBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Prop :=
  ∀ y : Fin q → G,
    max (compatibleCountLowRankDensityReal G q y - 1) 0 ≤
      lowRankCollisionSlopeReal G q * pairCollisionCountReal G q y

/-- Average low-rank collision-envelope obligation.  This is weaker than the
pointwise envelope and is the right remaining target: high-collision
transcripts can violate the pointwise line while still being controlled after
averaging under the ideal visible law. -/
def CompatibleCountLowRankAverageCollisionBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Prop :=
  compatibleCountLowRankPositiveErrorReal G q ≤
    lowRankCollisionSlopeReal G q *
      XoP.ANOVA.uniformAverage (Fin q → G) (pairCollisionCountReal G q)

/-- Scalarized version of the average low-rank collision-envelope obligation.
This is the same target after rewriting the low-rank density as a function of
the visible pair-collision count. -/
def CompatibleCountLowRankScalarCollisionBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Prop :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => max
      (lowRankDensityFromCollisionCountReal G q (pairCollisionCountInt G q y) - 1) 0) ≤
    lowRankCollisionSlopeReal G q *
      XoP.ANOVA.uniformAverage (Fin q → G) (pairCollisionCountReal G q)

/-- One-dimensional fiber-sum version of the remaining scalar collision
obligation.  The only transcript-distribution data left here is the occupancy
fiber size for each possible value of the visible pair-collision count. -/
def CompatibleCountLowRankCollisionFiberBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) : Prop :=
  (∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
    (pairCollisionCountFiberCard G q k : ℝ) *
      max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0) /
    (Fintype.card (Fin q → G) : ℝ) ≤
  lowRankCollisionSlopeReal G q *
    XoP.ANOVA.uniformAverage (Fin q → G) (pairCollisionCountReal G q)

/-- Quadratic collision-envelope obligation for the low-rank positive part.
The linear term gives exactly `spatialReconstructionBound`; the quadratic term
is intended to be discharged using the second factorial moment of the visible
pair-collision count. -/
def CompatibleCountLowRankQuadraticCollisionBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (ε : ℝ) : Prop :=
  ∀ y : Fin q → G,
    max (lowRankDensityFromCollisionCountReal G q
      (pairCollisionCountInt G q y) - 1) 0 ≤
      lowRankCollisionSlopeReal G q * pairCollisionCountReal G q y +
        ε * (((pairCollisionCountNat G q y).choose 2 : Nat) : ℝ)

/-- Finite scalar certificate for the quadratic collision envelope.  It is the
maximum, over possible visible pair-collision counts `k`, of the normalized
positive excess after subtracting the spatial-reconstruction line.

The value is intentionally a finite expression, not an asymptotic estimate:
later analytic work can upper-bound it by a closed form such as `O(N^-2)`,
while the theorem below already turns this finite certificate into the named
quadratic-envelope obligation. -/
noncomputable def lowRankQuadraticEnvelopeCoefficient
    (G : Type*) [Fintype G] (q : Nat) : ℝ :=
  ((Finset.range (Fintype.card (PairIndex q) + 1)).image
    (fun k : Nat =>
      if 2 ≤ k then
        max
          ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
              lowRankCollisionSlopeReal G q * (k : ℝ)) /
            (((k.choose 2 : Nat) : ℝ))) 0
      else 0)).max'
    (by simp)

/-- The finite scalar certificate bounds each normalized high-collision
excess term in its defining range. -/
theorem lowRankQuadraticEnvelopeCoefficient_term_le
    (G : Type*) [Fintype G] (q k : Nat)
    (hk : k ∈ Finset.range (Fintype.card (PairIndex q) + 1)) :
    (if 2 ≤ k then
        max
          ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
              lowRankCollisionSlopeReal G q * (k : ℝ)) /
            (((k.choose 2 : Nat) : ℝ))) 0
      else 0) ≤ lowRankQuadraticEnvelopeCoefficient G q := by
  unfold lowRankQuadraticEnvelopeCoefficient
  have hmem :
      (if 2 ≤ k then
        max
          ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
              lowRankCollisionSlopeReal G q * (k : ℝ)) /
            (((k.choose 2 : Nat) : ℝ))) 0
      else 0) ∈
        (Finset.range (Fintype.card (PairIndex q) + 1)).image
          (fun k : Nat =>
            if 2 ≤ k then
              max
                ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
                    lowRankCollisionSlopeReal G q * (k : ℝ)) /
                  (((k.choose 2 : Nat) : ℝ))) 0
            else 0) := by
    exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
  exact Finset.le_max' _ _ hmem

/-- The only scalar facts not encoded by the quadratic coefficient are the
low-collision counts `k = 0, 1`, where `choose k 2 = 0`.  This predicate
records that those counts are already covered by the spatial line. -/
def LowRankLowCollisionLineCovered
    (G : Type*) [Fintype G] (q : Nat) : Prop :=
  ∀ k ∈ Finset.range (Fintype.card (PairIndex q) + 1), k < 2 →
    max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 ≤
      lowRankCollisionSlopeReal G q * (k : ℝ)

/-- The low-collision line-coverage obligation is exactly the two scalar
checks `k = 0` and `k = 1`. -/
theorem lowRankLowCollisionLineCovered_of_zero_one
    (G : Type*) [Fintype G] (q : Nat)
    (h0 : max (lowRankDensityFromCollisionCountReal G q (0 : ℤ) - 1) 0 ≤
      lowRankCollisionSlopeReal G q * (0 : ℝ))
    (h1 : max (lowRankDensityFromCollisionCountReal G q (1 : ℤ) - 1) 0 ≤
      lowRankCollisionSlopeReal G q * (1 : ℝ)) :
    LowRankLowCollisionLineCovered G q := by
  intro k _hk hklt
  interval_cases k
  · simpa using h0
  · simpa using h1

/-- In the small-query regime, the two exceptional low-collision scalar
checks are both covered by the spatial line. -/
theorem lowRankLowCollisionLineCovered_of_queryPair_le_card
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (hsmall : q * (q - 1) ≤ Fintype.card G) :
    LowRankLowCollisionLineCovered G q := by
  apply lowRankLowCollisionLineCovered_of_zero_one
  · exact lowRankDensityZeroPositivePart_le_zero_of_queryPair_le_card
      (G := G) (q := q) (lt_of_lt_of_le (by norm_num) hq2) hq hsmall
  · exact lowRankDensityOnePositivePart_le_slope_of_queryPair_le_card
      (G := G) (q := q) hq2 hq hsmall

/-- The finite scalar coefficient, together with the explicit `k = 0,1`
line-coverage check, instantiates the named pointwise quadratic collision
envelope. -/
theorem compatibleCountLowRankQuadraticCollisionBound_of_finiteCoefficient
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (hlow : LowRankLowCollisionLineCovered G q) :
    CompatibleCountLowRankQuadraticCollisionBound G q
      (lowRankQuadraticEnvelopeCoefficient G q) := by
  unfold CompatibleCountLowRankQuadraticCollisionBound
  intro y
  let k : Nat := pairCollisionCountNat G q y
  have hk_le : k ≤ Fintype.card (PairIndex q) := by
    dsimp [k]
    exact pairCollisionCountNat_le_pairIndex_card (G := G) (q := q) y
  have hk_mem : k ∈ Finset.range (Fintype.card (PairIndex q) + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le)
  have hk_int : pairCollisionCountInt G q y = (k : ℤ) := by
    dsimp [k]
    exact pairCollisionCountInt_eq_pairCollisionCountNat (G := G) (q := q) y
  have hk_real : pairCollisionCountReal G q y = (k : ℝ) := by
    dsimp [k]
    exact pairCollisionCountReal_eq_pairCollisionCountNat (G := G) (q := q) y
  by_cases h2 : 2 ≤ k
  · have hterm :=
      lowRankQuadraticEnvelopeCoefficient_term_le (G := G) (q := q) (k := k) hk_mem
    have hchoose_pos_nat : 0 < k.choose 2 := Nat.choose_pos h2
    have hchoose_pos : 0 < (((k.choose 2 : Nat) : ℝ)) := by exact_mod_cast hchoose_pos_nat
    have hratio_le :
        ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
            lowRankCollisionSlopeReal G q * (k : ℝ)) /
          (((k.choose 2 : Nat) : ℝ))) ≤
          lowRankQuadraticEnvelopeCoefficient G q := by
      have hleft :
          ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
              lowRankCollisionSlopeReal G q * (k : ℝ)) /
            (((k.choose 2 : Nat) : ℝ))) ≤
            max
              ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
                  lowRankCollisionSlopeReal G q * (k : ℝ)) /
                (((k.choose 2 : Nat) : ℝ))) 0 := by
        exact le_max_left _ _
      have hterm' :
          max
            ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
                lowRankCollisionSlopeReal G q * (k : ℝ)) /
              (((k.choose 2 : Nat) : ℝ))) 0 ≤
            lowRankQuadraticEnvelopeCoefficient G q := by
        simpa [h2] using hterm
      exact le_trans hleft hterm'
    have hmul :
        max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
            lowRankCollisionSlopeReal G q * (k : ℝ) ≤
          lowRankQuadraticEnvelopeCoefficient G q *
            (((k.choose 2 : Nat) : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hratio_le (le_of_lt hchoose_pos)
      simpa [div_eq_mul_inv, mul_assoc, hchoose_pos.ne'] using this
    have hfinal :
        max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 ≤
          lowRankCollisionSlopeReal G q * (k : ℝ) +
            lowRankQuadraticEnvelopeCoefficient G q *
              (((k.choose 2 : Nat) : ℝ)) := by
      linarith
    simpa [hk_int, hk_real, k] using hfinal
  · have hk_lt : k < 2 := Nat.lt_of_not_ge h2
    have hline := hlow k hk_mem hk_lt
    have hchoose_zero : k.choose 2 = 0 := Nat.choose_eq_zero_of_lt hk_lt
    have hfinal :
        max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 ≤
          lowRankCollisionSlopeReal G q * (k : ℝ) +
            lowRankQuadraticEnvelopeCoefficient G q *
              (((k.choose 2 : Nat) : ℝ)) := by
      rw [hchoose_zero]
      simpa using hline
    simpa [hk_int, hk_real, k] using hfinal

/-- To upper-bound the finite quadratic coefficient it is enough to
upper-bound each scalar term in its defining finite range.  This is the
`Finset.max'_le` direction dual to `lowRankQuadraticEnvelopeCoefficient_term_le`.

The hypothesis is deliberately phrased over the exact scalar expression in the
definition so that later analytic work can focus only on the one-variable
collision-count inequality. -/
theorem lowRankQuadraticEnvelopeCoefficient_le_of_forall_term_le
    (G : Type*) [Fintype G] (q : Nat) (B : ℝ)
    (hB :
      ∀ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
        (if 2 ≤ k then
          max
            ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
                lowRankCollisionSlopeReal G q * (k : ℝ)) /
              (((k.choose 2 : Nat) : ℝ))) 0
        else 0) ≤ B) :
    lowRankQuadraticEnvelopeCoefficient G q ≤ B := by
  unfold lowRankQuadraticEnvelopeCoefficient
  refine Finset.max'_le _ _ _ ?_
  intro x hx
  rw [Finset.mem_image] at hx
  rcases hx with ⟨k, hk, rfl⟩
  exact hB k hk

/-- Closed-form target version of
`lowRankQuadraticEnvelopeCoefficient_le_of_forall_term_le`.

This packages the remaining low-rank analytic obligation in the paper-shaped
form needed by
`visibleStatDist_le_spatialReconstructionBound_add_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage_of_queryPair_le_card`:
prove that every high-collision scalar excess is at most `c / N^2`, while the
`k = 0, 1` terms are zero by construction of the coefficient. -/
theorem lowRankQuadraticEnvelopeCoefficient_le_inv_sq_of_forall_high_collision
    (G : Type*) [Fintype G] (q : Nat) (c : ℝ)
    (hc : 0 ≤ c)
    (h :
      ∀ k ∈ Finset.range (Fintype.card (PairIndex q) + 1), 2 ≤ k →
        ((max (lowRankDensityFromCollisionCountReal G q (k : ℤ) - 1) 0 -
            lowRankCollisionSlopeReal G q * (k : ℝ)) /
          (((k.choose 2 : Nat) : ℝ))) ≤
          c / (Fintype.card G : ℝ) ^ 2) :
    lowRankQuadraticEnvelopeCoefficient G q ≤
      c / (Fintype.card G : ℝ) ^ 2 := by
  refine lowRankQuadraticEnvelopeCoefficient_le_of_forall_term_le
    (G := G) (q := q) (B := c / (Fintype.card G : ℝ) ^ 2) ?_
  intro k hk
  by_cases hk2 : 2 ≤ k
  · have hterm := h k hk hk2
    simpa [hk2] using max_le hterm (div_nonneg hc (sq_nonneg _))
  · simp [hk2, div_nonneg hc (sq_nonneg _)]

/-- Small-query bridge from the normalized first-order scalar inequality to
the closed fourth-order coefficient estimate.

This theorem connects the abstract high-collision scalar obligation to the
actual RS low-rank coefficient.  The remaining analytic work is the pure
rational inequality in the hypothesis `hscalar`; all visible-normalizer slack,
falling-factorial lower bound, slope monotonicity, and `choose 2`
normalization have been discharged here. -/
theorem lowRankQuadraticEnvelopeCoefficient_le_inv_sq_of_first_order_scalar
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (c : ℝ) (hc : 0 ≤ c) (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) (hsmall : q * (q - 1) ≤ Fintype.card G)
    (hscalar :
      ∀ k ∈ Finset.range (Fintype.card (PairIndex q) + 1), 2 ≤ k →
        let N : ℝ := Fintype.card G
        let P : ℝ := Fintype.card (PairIndex q)
        (1 + ((k : ℝ) - 2 * P) / N) / (1 - P / N) ^ 2 - 1 -
            (k : ℝ) * (1 - P / N) * N / (N - 1) ^ 2 ≤
          c * ((k : ℝ) * ((k : ℝ) - 1) / 2) / N ^ 2) :
    lowRankQuadraticEnvelopeCoefficient G q ≤ c / (Fintype.card G : ℝ) ^ 2 := by
  refine lowRankQuadraticEnvelopeCoefficient_le_inv_sq_of_forall_high_collision
    (G := G) (q := q) (c := c) hc ?_
  intro k hk hk2
  let N : Nat := Fintype.card G
  let P : Nat := Fintype.card (PairIndex q)
  let d : ℝ := ((N.descFactorial q : Nat) : ℝ)
  let r : ℝ := d / (N : ℝ) ^ q
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact Fintype.card_pos
  have hN2_nat : 2 ≤ N := by
    dsimp [N]
    exact le_trans hq2 hq
  have hN2_real : 2 ≤ (N : ℝ) := by exact_mod_cast hN2_nat
  have hqN : q ≤ N := by
    dsimp [N]
    exact hq
  have hk_le_nat : k ≤ P := by
    dsimp [P]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkP_real : (k : ℝ) ≤ (P : ℝ) := by exact_mod_cast hk_le_nat
  have hPsmall_real : 2 * (P : ℝ) ≤ (N : ℝ) := by
    have hpair := pairIndex_card_mul_two (q := q)
    have hnat : 2 * P ≤ N := by
      dsimp [P, N]
      omega
    exact_mod_cast hnat
  have hS_eq : (P : ℝ) / (N : ℝ) =
      ∑ i ∈ Finset.range q, (i : ℝ) / (N : ℝ) := by
    dsimp [P]
    exact pairIndex_card_div_eq_sum_range_div N q
  have hr_lower : 1 - (P : ℝ) / (N : ℝ) ≤ r := by
    rw [hS_eq]
    dsimp [r, d]
    exact XoP.ANOVA.descFactorial_div_pow_ge_one_sub_sum N q hN_pos_nat hqN
  have hchoose_eq :
      (((k.choose 2 : Nat) : ℝ)) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have hslack_eq :
      XoP.ANOVA.visibleNormalizerSlackReal G q = 1 / r ^ 2 := by
    rw [XoP.ANOVA.visibleNormalizerSlackReal_eq_pow_sq_div_descFactorial_sq
      (G := G) (q := q) hq]
    dsimp [r, d, N]
    have hdesc : 0 < (Fintype.card G).descFactorial q :=
      Nat.descFactorial_pos.mpr hq
    have hdesc_real : 0 < (((Fintype.card G).descFactorial q : Nat) : ℝ) := by
      exact_mod_cast hdesc
    have hpow_pos : 0 < (Fintype.card G : ℝ) ^ q := by
      exact pow_pos (by exact_mod_cast Fintype.card_pos (α := G)) q
    field_simp [hdesc_real.ne', hpow_pos.ne']
    norm_num [pow_two, Nat.cast_mul]
    ring_nf
  have hdens_eq :
      lowRankDensityFromCollisionCountReal G q (k : ℤ) =
        (1 / r ^ 2) * (1 + ((k : ℝ) - 2 * (P : ℝ)) / (N : ℝ)) := by
    rw [lowRankDensityFromCollisionCountReal_eq_slack_mul
      (G := G) (q := q) hq0 hq]
    rw [hslack_eq]
    dsimp [P, N]
    norm_num
  have hslope_eq :
      lowRankCollisionSlopeReal G q * (k : ℝ) =
        (k : ℝ) * r * (N : ℝ) / ((N : ℝ) - 1) ^ 2 := by
    have hslope :
        r * (N : ℝ) / ((N : ℝ) - 1) ^ 2 = lowRankCollisionSlopeReal G q := by
      dsimp [r, d, N]
      unfold lowRankCollisionSlopeReal
      have hN_ne : (Fintype.card G : ℝ) ≠ 0 := by
        exact_mod_cast ne_of_gt Fintype.card_pos
      have hNm1_ne : ((Fintype.card G : ℝ) - 1) ≠ 0 := ne_of_gt (by
        have hgt : (1 : ℝ) < Fintype.card G := by exact_mod_cast hN2_nat
        linarith)
      have hpow : q - 1 + 1 = q := Nat.sub_add_cancel hq0
      have hpowR :
          (Fintype.card G : ℝ) ^ q =
            (Fintype.card G : ℝ) ^ (q - 1) * (Fintype.card G : ℝ) := by
        rw [← pow_succ, hpow]
      have hsub_cast :
          ((Fintype.card G - 1 : Nat) : ℝ) = (Fintype.card G : ℝ) - 1 := by
        have hone : 1 ≤ Fintype.card G := by omega
        norm_num [Nat.cast_sub hone]
      rw [hsub_cast, hpowR]
      field_simp [hN_ne, hNm1_ne]
    rw [← hslope]
    ring
  have hpure := highCollisionNormalizedPositivePart_le_inv_sq_of_scalar
    (N := (N : ℝ)) (P := (P : ℝ)) (k := (k : ℝ)) (r := r) (c := c)
    hN2_real hPsmall_real (by exact_mod_cast hk2) hkP_real hr_lower hc (by
      simpa [N, P] using hscalar k hk hk2)
  simpa [hdens_eq, hslope_eq, hchoose_eq, N, P, mul_comm, mul_left_comm, mul_assoc]
    using hpure

/-- Constant-`12` fourth-order coefficient estimate in the small-query regime.

This discharges the low-rank scalar coefficient task used by the paper-shaped
endpoint: the remaining low-rank quadratic envelope is at most `12 / N^2`,
so its contribution is `12 * choose(#PairIndex, 2) / N^4`. -/
theorem lowRankQuadraticEnvelopeCoefficient_le_twelve_inv_sq_of_queryPair_le_card
    (G : Type*) [AddGroup G] [Fintype G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (hsmall : q * (q - 1) ≤ Fintype.card G) :
    lowRankQuadraticEnvelopeCoefficient G q ≤
      12 / (Fintype.card G : ℝ) ^ 2 := by
  refine lowRankQuadraticEnvelopeCoefficient_le_inv_sq_of_first_order_scalar
    (G := G) (q := q) (c := 12) (by norm_num) hq2 hq hsmall ?_
  intro k hk hk2
  let N : Nat := Fintype.card G
  let P : Nat := Fintype.card (PairIndex q)
  have hN2_real : 2 ≤ (N : ℝ) := by
    dsimp [N]
    exact_mod_cast le_trans hq2 hq
  have hk_le_nat : k ≤ P := by
    dsimp [P]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hkP_real : (k : ℝ) ≤ (P : ℝ) := by exact_mod_cast hk_le_nat
  have hPsmall_real : 2 * (P : ℝ) ≤ (N : ℝ) := by
    have hpair := pairIndex_card_mul_two (q := q)
    have hnat : 2 * P ≤ N := by
      dsimp [P, N]
      omega
    exact_mod_cast hnat
  exact firstOrderHighCollisionScalar_le_twelve
    (N := (N : ℝ)) (P := (P : ℝ)) (k := (k : ℝ))
    hN2_real hPsmall_real (by exact_mod_cast hk2) hkP_real

/-- The occupancy fiber-sum bound is exactly the scalar collision-count
obligation after expanding the low-rank positive part by collision-count
fibers. -/
theorem compatibleCountLowRankScalarCollisionBound_of_fiberBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (hfiber : CompatibleCountLowRankCollisionFiberBound G q) :
    CompatibleCountLowRankScalarCollisionBound G q := by
  unfold CompatibleCountLowRankScalarCollisionBound
  rw [← compatibleCountLowRankPositiveErrorReal_eq_collisionCountScalarAverage
    (G := G) (q := q)]
  rw [compatibleCountLowRankPositiveErrorReal_eq_collisionCountFiberSum
    (G := G) (q := q)]
  exact hfiber

/-- The scalarized collision-count bound implies the average low-rank
collision-envelope obligation. -/
theorem compatibleCountLowRankAverageCollisionBound_of_scalarCollision
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (hscalar : CompatibleCountLowRankScalarCollisionBound G q) :
    CompatibleCountLowRankAverageCollisionBound G q := by
  unfold CompatibleCountLowRankAverageCollisionBound
  rw [compatibleCountLowRankPositiveErrorReal_eq_collisionCountScalarAverage
    (G := G) q]
  exact hscalar

/-- The uniform average visible pair-collision count is `#PairIndex / |G|`. -/
theorem uniformAverage_pairCollisionCountReal_eq_pairIndex_card_div_card
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) :
    XoP.ANOVA.uniformAverage (Fin q → G) (pairCollisionCountReal G q) =
      (Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ) := by
  unfold XoP.ANOVA.uniformAverage pairCollisionCountReal
  have hsumNat :=
    sum_pairCollisionIndicators_eq_pairIndex_card_mul_card_pow (G := G) (q := q)
  have hcardFun : Fintype.card (Fin q → G) = Fintype.card G ^ q := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hsumReal :
      (∑ x : Fin q → G,
        ((∑ p : PairIndex q,
          (if x p.1.2 = x p.1.1 then 1 else 0 : Nat)) : ℝ)) =
        (Fintype.card (PairIndex q) * Fintype.card G ^ (q - 1) : Nat) := by
    exact_mod_cast hsumNat
  rw [hsumReal, hcardFun]
  have hN_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hN_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hpow : q - 1 + 1 = q := Nat.sub_add_cancel hq0
  have hpowNat : Fintype.card G ^ q =
      Fintype.card G ^ (q - 1) * Fintype.card G := by
    rw [← pow_succ, hpow]
  rw [hpowNat]
  simp only [Nat.cast_mul, Nat.cast_pow]
  field_simp [hN_ne]

/-- First moment of the occupancy fiber distribution for the visible
pair-collision count. -/
theorem pairCollisionCountFiberCard_weightedAverage_eq_pairIndex_card_div_card
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) :
    (∑ k ∈ Finset.range (Fintype.card (PairIndex q) + 1),
      (pairCollisionCountFiberCard G q k : ℝ) * (k : ℝ)) /
        (Fintype.card (Fin q → G) : ℝ) =
      (Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ) := by
  rw [← uniformAverage_of_pairCollisionCountNat (G := G) (q := q)
    (F := fun k : Nat => (k : ℝ))]
  rw [← uniformAverage_pairCollisionCountReal_eq_pairIndex_card_div_card
    (G := G) q hq0]
  unfold XoP.ANOVA.uniformAverage
  apply congrArg (fun s : ℝ => s / (Fintype.card (Fin q → G) : ℝ))
  apply Finset.sum_congr rfl
  intro y _hy
  rw [pairCollisionCountReal_eq_pairCollisionCountNat (G := G) (q := q) y]

/-- The collision-slope normalization times the first visible-collision moment
is exactly the spatial-reconstruction bound. -/
theorem lowRankCollisionSlope_mul_pairIndex_card_div_card_eq_spatialReconstructionBound
    (G : Type*) [Fintype G] (q : Nat) (hq0 : 0 < q)
    (hN2 : 2 ≤ Fintype.card G) :
    lowRankCollisionSlopeReal G q *
        ((Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ)) =
      (spatialReconstructionBound G q : ℝ) := by
  unfold lowRankCollisionSlopeReal spatialReconstructionBound
  simp only [NNReal.coe_div, Nat.cast_mul, Nat.cast_pow]
  change
    ((((Fintype.card G).descFactorial q : Nat) : ℝ) /
        ((Fintype.card G : ℝ) ^ (q - 1) *
          (((Fintype.card G - 1 : Nat) : ℝ) ^ 2))) *
        ((Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ)) =
      (((Fintype.card (PairIndex q) : ℝ) *
          (((Fintype.card G).descFactorial q : Nat) : ℝ)) /
        (((Fintype.card G : ℝ) ^ q) *
          (((Fintype.card G - 1 : Nat) : ℝ) ^ 2)))
  have hN_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hN2)
  have hN_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hNm1_ne : ((Fintype.card G - 1 : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt hN2)
  have hpow : q - 1 + 1 = q := Nat.sub_add_cancel hq0
  field_simp [hN_ne, hNm1_ne]
  have hpowR :
      (Fintype.card G : ℝ) ^ q =
        (Fintype.card G : ℝ) ^ (q - 1) * (Fintype.card G : ℝ) := by
    rw [← pow_succ, hpow]
  rw [hpowR]
  ring

/-- A quadratic collision envelope for the low-rank positive part converts, by
the first and second occupancy moments, into `B_q(N)` plus a second-moment
remainder. -/
theorem compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_quadraticCollision
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (ε : ℝ) (hq0 : 0 < q) (hq2 : 2 ≤ q)
    (hN2 : 2 ≤ Fintype.card G)
    (hquad : CompatibleCountLowRankQuadraticCollisionBound G q ε) :
    compatibleCountLowRankPositiveErrorReal G q ≤
      (spatialReconstructionBound G q : ℝ) +
        ε * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 2 := by
  rw [compatibleCountLowRankPositiveErrorReal_eq_collisionCountScalarAverage
    (G := G) (q := q)]
  calc
    (XoP.ANOVA.uniformAverage (Fin q → G) fun y =>
        max (lowRankDensityFromCollisionCountReal G q
          (pairCollisionCountInt G q y) - 1) 0) ≤
      XoP.ANOVA.uniformAverage (Fin q → G) (fun y =>
        lowRankCollisionSlopeReal G q * pairCollisionCountReal G q y +
          ε * (((pairCollisionCountNat G q y).choose 2 : Nat) : ℝ)) := by
        unfold XoP.ANOVA.uniformAverage
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun y _hy => hquad y))
          (Nat.cast_nonneg _)
    _ = (spatialReconstructionBound G q : ℝ) +
        ε * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 2 := by
        rw [XoP.ANOVA.uniformAverage_add]
        rw [XoP.ANOVA.uniformAverage_const_mul]
        rw [XoP.ANOVA.uniformAverage_const_mul]
        rw [uniformAverage_pairCollisionCountReal_eq_pairIndex_card_div_card
          (G := G) (q := q) hq0]
        rw [uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq_closed
          (G := G) (q := q) hq2]
        rw [lowRankCollisionSlope_mul_pairIndex_card_div_card_eq_spatialReconstructionBound
          (G := G) (q := q) hq0 hN2]
        ring

/-- The rank-two-adjusted positive part is bounded by the spatial term, a
quadratic-collision low-rank remainder, and only the positive part of the
scalar rank-two quadratic correction. -/
theorem compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_quadraticCollision_add_quadraticPositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (ε : ℝ) (hq0 : 0 < q) (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hquad : CompatibleCountLowRankQuadraticCollisionBound G q ε) :
    compatibleCountRankTwoPositiveErrorReal G q hq2 ≤
      (spatialReconstructionBound G q : ℝ) +
        ε * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 2 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) := by
  have hN2 : 2 ≤ Fintype.card G := le_trans hq2 hq
  have hstats :=
    rankTwoEqualityStatsPositiveErrorReal_le_lowRank_add_quadraticPositive
      (G := G) q hq2 hq
  have hlow :=
    compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_quadraticCollision
      (G := G) (q := q) (ε := ε) hq0 hq2 hN2 hquad
  calc
    compatibleCountRankTwoPositiveErrorReal G q hq2 =
        rankTwoEqualityStatsPositiveErrorReal G q := by
          rw [compatibleCountRankTwoPositiveErrorReal_eq_equalityPositiveError
            (G := G) (q := q) hq2]
          rw [compatibleCountRankTwoEqualityPositiveErrorReal_eq_statsPositive
            (G := G) (q := q)]
    _ ≤ compatibleCountLowRankPositiveErrorReal G q +
        rankTwoEqualityQuadraticPositiveErrorReal G q := hstats
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          ε * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) +
        rankTwoEqualityQuadraticPositiveErrorReal G q := by
          exact add_le_add hlow le_rfl
    _ = (spatialReconstructionBound G q : ℝ) +
        ε * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 2 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) := by
          rw [rankTwoEqualityQuadraticPositiveErrorBound_coe]

/-- A pointwise collision envelope for the low-rank positive part implies the
named low-rank positive-error bound. -/
theorem compatibleCountLowRankPositiveErrorBound_of_pointwiseCollision
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hN2 : 2 ≤ Fintype.card G)
    (hpoint : CompatibleCountLowRankPointwiseCollisionBound G q) :
    CompatibleCountLowRankPositiveErrorBound G q := by
  unfold CompatibleCountLowRankPositiveErrorBound
    compatibleCountLowRankPositiveErrorReal XoP.ANOVA.uniformAverage
  calc
    (∑ x : Fin q → G, max (compatibleCountLowRankDensityReal G q x - 1) 0) /
        ↑(Fintype.card (Fin q → G)) ≤
      (∑ x : Fin q → G,
          lowRankCollisionSlopeReal G q * pairCollisionCountReal G q x) /
        ↑(Fintype.card (Fin q → G)) := by
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun y _hy => hpoint y))
          (Nat.cast_nonneg _)
    _ = lowRankCollisionSlopeReal G q *
        XoP.ANOVA.uniformAverage (Fin q → G) (pairCollisionCountReal G q) := by
        unfold XoP.ANOVA.uniformAverage
        rw [← Finset.mul_sum]
        ring
    _ = lowRankCollisionSlopeReal G q *
        ((Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ)) := by
        rw [uniformAverage_pairCollisionCountReal_eq_pairIndex_card_div_card
          (G := G) q hq0]
    _ = (spatialReconstructionBound G q : ℝ) := by
        unfold lowRankCollisionSlopeReal spatialReconstructionBound
        simp only [NNReal.coe_div, Nat.cast_mul, Nat.cast_pow]
        change
          ((((Fintype.card G).descFactorial q : Nat) : ℝ) /
              ((Fintype.card G : ℝ) ^ (q - 1) *
                (((Fintype.card G - 1 : Nat) : ℝ) ^ 2))) *
              ((Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ)) =
            (((Fintype.card (PairIndex q) : ℝ) *
                (((Fintype.card G).descFactorial q : Nat) : ℝ)) /
              (((Fintype.card G : ℝ) ^ q) *
                (((Fintype.card G - 1 : Nat) : ℝ) ^ 2)))
        have hN_pos : 0 < (Fintype.card G : ℝ) := by
          exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
        have hN_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hN_pos
        have hNm1_ne : ((Fintype.card G - 1 : Nat) : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.sub_ne_zero_of_lt hN2)
        have hpow : q - 1 + 1 = q := Nat.sub_add_cancel hq0
        field_simp [hN_ne, hNm1_ne]
        have hpowR :
            (Fintype.card G : ℝ) ^ q =
              (Fintype.card G : ℝ) ^ (q - 1) * (Fintype.card G : ℝ) := by
          rw [← pow_succ, hpow]
        rw [hpowR]
        ring

/-- The average collision-envelope obligation implies the named low-rank
positive-error bound. -/
theorem compatibleCountLowRankPositiveErrorBound_of_averageCollision
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hN2 : 2 ≤ Fintype.card G)
    (havg : CompatibleCountLowRankAverageCollisionBound G q) :
    CompatibleCountLowRankPositiveErrorBound G q := by
  unfold CompatibleCountLowRankPositiveErrorBound
  refine le_trans havg ?_
  rw [uniformAverage_pairCollisionCountReal_eq_pairIndex_card_div_card
    (G := G) q hq0]
  rw [show lowRankCollisionSlopeReal G q *
      ((Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ)) =
      (spatialReconstructionBound G q : ℝ) by
    unfold lowRankCollisionSlopeReal spatialReconstructionBound
    simp only [NNReal.coe_div, Nat.cast_mul, Nat.cast_pow]
    change
      ((((Fintype.card G).descFactorial q : Nat) : ℝ) /
          ((Fintype.card G : ℝ) ^ (q - 1) *
            (((Fintype.card G - 1 : Nat) : ℝ) ^ 2))) *
          ((Fintype.card (PairIndex q) : ℝ) / (Fintype.card G : ℝ)) =
        (((Fintype.card (PairIndex q) : ℝ) *
            (((Fintype.card G).descFactorial q : Nat) : ℝ)) /
          (((Fintype.card G : ℝ) ^ q) *
            (((Fintype.card G - 1 : Nat) : ℝ) ^ 2)))
    have hN_pos : 0 < (Fintype.card G : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
    have hN_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hN_pos
    have hNm1_ne : ((Fintype.card G - 1 : Nat) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.sub_ne_zero_of_lt hN2)
    have hpow : q - 1 + 1 = q := Nat.sub_add_cancel hq0
    field_simp [hN_ne, hNm1_ne]
    have hpowR :
        (Fintype.card G : ℝ) ^ q =
          (Fintype.card G : ℝ) ^ (q - 1) * (Fintype.card G : ℝ) := by
      rw [← pow_succ, hpow]
    rw [hpowR]
    ring]

/-- Named bridge obligation comparing the true visible positive error to the
low-rank positive error plus the explicit rank-tail error. -/
def VisibleStatDistLowRankTailBridge
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) : Prop :=
  (visibleStatDist (G := G) (q := q) : ℝ) ≤
    compatibleCountLowRankPositiveErrorReal G q +
      (rankTailErrorBound G q : ℝ)

/-- Named average tail obligation: the uniform average of the density-ratio
difference between the true compatible count and the low-rank approximation is
bounded by the explicit rank-tail error. -/
def CompatibleCountAverageTailBound
    (G : Type*) [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) : Prop :=
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
      compatibleCountLowRankDensityReal G q y|) ≤
    (rankTailErrorBound G q : ℝ)

/-- Named final residual obligation for the rank-zero/rank-one/rank-two
positive part after scalarizing rank two by equality statistics. -/
def RankTwoEqualityStatsPositiveResidualBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (ε : NNReal) : Prop :=
  rankTwoEqualityStatsPositiveResidualErrorBound G q ≤ ε

/-- Named final residual obligation after deleting sign-certified
two-statistic fibers.  This is the cancellation-aware version of
`RankTwoEqualityStatsPositiveResidualBound`: the finite set `S` is removed
before the residual is bounded. -/
def RankTwoEqualityStatsPositiveResidualSdiffBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat)
    (S : Finset (Nat × Nat)) (ε : NNReal) : Prop :=
  rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q S ≤ ε

/-- Named scalar rank-two quadratic-positive obligation.  The theorem
`rankTwoEqualityQuadraticPositiveErrorBound_eq_fiberSum` rewrites this as a
finite two-statistic fiber inequality. -/
def RankTwoEqualityQuadraticPositiveBound
    (G : Type*) [Fintype G] [DecidableEq G] (q : Nat) (ε : NNReal) : Prop :=
  rankTwoEqualityQuadraticPositiveErrorBound G q ≤ ε

/-- Named signed-rank-three residual obligation.  This is the post-rank-two
cancellation target: after the rank-two equality-pattern layer has been
absorbed into the approximation, only the positive part of the signed
rank-three-adjusted density remains. -/
def RankThreePositiveResidualBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) (ε : NNReal) : Prop :=
  rankThreePositiveResidualErrorBound G q hq2 hq3 ≤ ε

/-- Named final average-tail obligation for ranks three and higher. -/
def RankTailBeyondTwoAverageBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (ε : NNReal) : Prop :=
  rankTailBeyondTwoAverageErrorBound G q ≤ ε

/-- Named consistency-filtered average-tail obligation for ranks three and
higher.  This is the gain-graph rarity target: bound only the average mass of
cycle-consistent high-rank labelled subgraphs. -/
def RankTailBeyondTwoConsistentAverageBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (ε : NNReal) : Prop :=
  rankTailBeyondTwoConsistentAverageErrorBound G q ≤ ε

/-- Named average-tail obligation for ranks four and higher, after the signed
rank-three layer has been exposed. -/
def RankTailBeyondThreeAverageBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (ε : NNReal) : Prop :=
  rankTailBeyondThreeAverageErrorBound G q ≤ ε

/-- Named consistency-filtered average-tail obligation for ranks four and
higher.  This is the gain-graph rarity target after rank-three sign control. -/
def RankTailBeyondThreeConsistentAverageBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (ε : NNReal) : Prop :=
  rankTailBeyondThreeConsistentAverageErrorBound G q ≤ ε

/-- A pointwise density-tail estimate implies the average density-tail
obligation. -/
theorem compatibleCountAverageTailBound_of_pointwise
    (q : Nat)
    (hpoint : ∀ y : Fin q → G,
      |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
        compatibleCountLowRankDensityReal G q y| ≤
        (rankTailErrorBound G q : ℝ)) :
    CompatibleCountAverageTailBound G q := by
  dsimp [CompatibleCountAverageTailBound, XoP.ANOVA.uniformAverage]
  calc
    (∑ x : Fin q → G,
        |XoP.ANOVA.visibleDensityRatioReal x - compatibleCountLowRankDensityReal G q x|) /
        ↑(Fintype.card (Fin q → G)) ≤
      (∑ _x : Fin q → G, (rankTailErrorBound G q : ℝ)) /
        ↑(Fintype.card (Fin q → G)) := by
        exact div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun y _hy => hpoint y))
          (Nat.cast_nonneg _)
    _ = (rankTailErrorBound G q : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- Convert the integer compatible-count tail estimate into the normalized
pointwise density-tail estimate.  The `2 <= q` hypothesis is the regime where
the current explicit tail expression has the intended `N^(q-2)` count scale. -/
theorem compatibleCountDensityTailPointwise_le_rankTailErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
      compatibleCountLowRankDensityReal G q y| ≤
      (rankTailErrorBound G q : ℝ) := by
  let N : Nat := Fintype.card G
  let T : Nat := 2 ^ (q * (q - 1)) - (1 + 3 * Fintype.card (PairIndex q))
  let D : Nat := N.descFactorial q * N.descFactorial q
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have htailZ :=
    abs_compatibleCountNat_sub_lowRank_le_explicitTailCard_mul_card_pow
      (G := G) (q := q) y hq0
  have htailR :
      |((XoP.Combinatorics.compatibleCountNat (G := G) (q := q) y : ℤ) : ℝ) -
          ((compatibleCountLowRankInt (G := G) (q := q) y : ℤ) : ℝ)| ≤
        ((T * N ^ (q - 2) : Nat) : ℝ) := by
    dsimp [T, N]
    exact_mod_cast htailZ
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hZ_pos : 0 < Z := by
    have hZ_nonneg : 0 ≤ Z := by positivity
    exact lt_of_le_of_ne hZ_nonneg (Ne.symm hZ_ne)
  have hleft :
      |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
        compatibleCountLowRankDensityReal G q y| =
        |((XoP.Combinatorics.compatibleCountNat (G := G) (q := q) y : ℤ) : ℝ) -
          ((compatibleCountLowRankInt (G := G) (q := q) y : ℤ) : ℝ)| / Z := by
    rw [XoP.ANOVA.visibleDensityRatioReal_eq]
    unfold compatibleCountLowRankDensityReal
    simp only [XoP.Combinatorics.compatibleCountNNReal_eq_coe_nat, NNReal.coe_div]
    rw [← sub_div, abs_div, abs_of_pos hZ_pos]
    norm_num
  rw [hleft]
  calc
    |((XoP.Combinatorics.compatibleCountNat (G := G) (q := q) y : ℤ) : ℝ) -
        ((compatibleCountLowRankInt (G := G) (q := q) y : ℤ) : ℝ)| / Z ≤
        ((T * N ^ (q - 2) : Nat) : ℝ) / Z := by
          exact div_le_div_of_nonneg_right htailR (le_of_lt hZ_pos)
    _ = (rankTailErrorBound G q : ℝ) := by
          have hN_pos_nat : 0 < N := by
            dsimp [N]
            exact Fintype.card_pos
          have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN_pos_nat
          have hdesc_pos : 0 < N.descFactorial q := by
            exact Nat.descFactorial_pos.mpr (by simpa [N] using hq)
          have hD_ne : (D : ℝ) ≠ 0 := by
            dsimp [D]
            exact_mod_cast Nat.mul_ne_zero (ne_of_gt hdesc_pos) (ne_of_gt hdesc_pos)
          have hZ_eq : Z = (D : ℝ) / (N : ℝ) ^ q := by
            dsimp [Z, D, N, XoP.ANOVA.visibleNormalizerNNReal]
            simp only [Nat.cast_mul, Nat.cast_pow]
            norm_num
          have hpow : q - 2 + q = 2 * q - 2 := by omega
          unfold rankTailErrorBound
          change ((T * N ^ (q - 2) : Nat) : ℝ) / Z =
            ((((T * N ^ (2 * q - 2) : Nat) : NNReal) / ((D : Nat) : NNReal) : NNReal) : ℝ)
          rw [hZ_eq]
          simp only [NNReal.coe_div, Nat.cast_mul, Nat.cast_pow]
          change ((T : ℝ) * (N : ℝ) ^ (q - 2)) / ((D : ℝ) / (N : ℝ) ^ q) =
            ((T : ℝ) * (N : ℝ) ^ (2 * q - 2)) / (D : ℝ)
          field_simp [hD_ne, hN_ne]
          rw [mul_assoc, ← pow_add, hpow]

/-- Exact pointwise expression for the density-tail difference in terms of the
higher-rank gain-graph tail. -/
theorem compatibleCountDensityTailPointwise_eq_rankTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
      compatibleCountLowRankDensityReal G q y| =
    |((collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq0 : ℤ) : ℝ)| /
      (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hZ_pos : 0 < Z := by
    have hZ_nonneg : 0 ≤ Z := by positivity
    exact lt_of_le_of_ne hZ_nonneg (Ne.symm hZ_ne)
  rw [XoP.ANOVA.visibleDensityRatioReal_eq]
  unfold compatibleCountLowRankDensityReal
  simp only [XoP.Combinatorics.compatibleCountNNReal_eq_coe_nat, NNReal.coe_div]
  rw [← sub_div, abs_div, abs_of_pos hZ_pos]
  apply congrArg (fun t : ℝ => |t| / Z)
  have htailR :
      ((XoP.Combinatorics.compatibleCountNat (G := G) (q := q) y : ℤ) : ℝ) -
        ((compatibleCountLowRankInt (G := G) (q := q) y : ℤ) : ℝ) =
      ((collisionSubfamilyRankTailBeyondOneInt (G := G) (q := q) y hq0 : ℤ) : ℝ) := by
    have htail := compatibleCountNat_eq_lowRank_add_tail (G := G) (q := q) y hq0
    norm_num
    exact_mod_cast (by
      simpa [compatibleCountNat] using congrArg
        (fun z : ℤ => z - compatibleCountLowRankInt (G := G) (q := q) y) htail)
  simpa using htailR

/-- Comparing the true density to the rank-two-adjusted density leaves exactly
the ranks-three-and-higher gain-graph tail.  This is the cancellation-aware
replacement for the older `rankTail = rankTwo + tailBeyondTwo` absolute-value
bridge. -/
theorem compatibleCountDensityTailPointwise_eq_tailBeyondTwo
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (y : Fin q → G) :
    |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
      compatibleCountRankTwoDensityReal G q hq2 y| =
    |((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ)| /
      (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hZ_pos : 0 < Z := by
    have hZ_nonneg : 0 ≤ Z := by positivity
    exact lt_of_le_of_ne hZ_nonneg (Ne.symm hZ_ne)
  rw [XoP.ANOVA.visibleDensityRatioReal_eq]
  unfold compatibleCountRankTwoDensityReal
  simp only [XoP.Combinatorics.compatibleCountNNReal_eq_coe_nat, NNReal.coe_div]
  rw [← sub_div, abs_div, abs_of_pos hZ_pos]
  apply congrArg (fun t : ℝ => |t| / Z)
  have htailR :
      ((XoP.Combinatorics.compatibleCountNat (G := G) (q := q) y : ℤ) : ℝ) -
        (((compatibleCountLowRankInt (G := G) (q := q) y +
            collisionSubfamilyRankLayerInt (G := G) (q := q) y
              (collisionSubfamilyGraphicRankTwoFin q hq2) : ℤ) : ℝ)) =
      ((collisionSubfamilyRankTailBeyondTwoInt (G := G) q y : ℤ) : ℝ) := by
    have htail := compatibleCountNat_eq_lowRank_add_tail (G := G) (q := q) y hq0
    have hdecomp := collisionSubfamilyRankTailBeyondOneInt_eq_rankTwo_add_tailBeyondTwo
      (G := G) (q := q) y hq0 hq2
    have htailInt :
        (XoP.Combinatorics.compatibleCountNat (G := G) (q := q) y : ℤ) -
          (compatibleCountLowRankInt (G := G) (q := q) y +
            collisionSubfamilyRankLayerInt (G := G) (q := q) y
              (collisionSubfamilyGraphicRankTwoFin q hq2)) =
        collisionSubfamilyRankTailBeyondTwoInt (G := G) q y := by
      rw [htail, hdecomp]
      ring
    norm_num
    exact_mod_cast htailInt
  simpa using htailR

/-- Comparing the true density to the rank-three-adjusted density leaves
exactly the rank-four-and-higher gain-graph tail. -/
theorem compatibleCountDensityTailPointwise_eq_tailBeyondThree
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
      compatibleCountRankThreeDensityReal G q hq2 hq3 y| =
    |((collisionSubfamilyRankTailBeyondThreeInt (G := G) q y : ℤ) : ℝ)| /
      (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ) := by
  let Z : ℝ := (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)
  have hZ_ne : Z ≠ 0 := by
    dsimp [Z]
    exact_mod_cast XoP.ANOVA.visibleNormalizerNNReal_ne_zero (G := G) (q := q) hq
  have hZ_pos : 0 < Z := by
    have hZ_nonneg : 0 ≤ Z := by positivity
    exact lt_of_le_of_ne hZ_nonneg (Ne.symm hZ_ne)
  rw [XoP.ANOVA.visibleDensityRatioReal_eq]
  unfold compatibleCountRankThreeDensityReal
  simp only [XoP.Combinatorics.compatibleCountNNReal_eq_coe_nat, NNReal.coe_div]
  rw [← sub_div, abs_div, abs_of_pos hZ_pos]
  apply congrArg (fun t : ℝ => |t| / Z)
  have htail := compatibleCountNat_eq_lowRank_add_tail (G := G) (q := q) y hq0
  have hdecomp2 := collisionSubfamilyRankTailBeyondOneInt_eq_rankTwo_add_tailBeyondTwo
    (G := G) (q := q) y hq0 hq2
  have hdecomp3 := collisionSubfamilyRankTailBeyondTwoInt_eq_rankThree_add_tailBeyondThree
    (G := G) (q := q) y hq3
  have htailInt :
      (XoP.Combinatorics.compatibleCountNat (G := G) (q := q) y : ℤ) -
        (compatibleCountLowRankInt (G := G) (q := q) y +
          collisionSubfamilyRankLayerInt (G := G) (q := q) y
            (collisionSubfamilyGraphicRankTwoFin q hq2) +
          collisionSubfamilyRankLayerInt (G := G) (q := q) y
            (collisionSubfamilyGraphicRankThreeFin q hq3)) =
      collisionSubfamilyRankTailBeyondThreeInt (G := G) q y := by
    rw [htail, hdecomp2, hdecomp3]
    ring
  norm_num
  exact_mod_cast htailInt

/-- Comparing the true density to the rank-two-adjusted density reduces
positive error to the rank-two-adjusted positive error plus the uniform
average of the ranks-three-and-higher density difference. -/
theorem compatibleCountTruePositiveErrorReal_le_rankTwo_add_average_abs_diff
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) :
    compatibleCountTruePositiveErrorReal G q ≤
      compatibleCountRankTwoPositiveErrorReal G q hq2 +
        XoP.ANOVA.uniformAverage (Fin q → G)
          (fun y => |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
            compatibleCountRankTwoDensityReal G q hq2 y|) := by
  unfold compatibleCountTruePositiveErrorReal compatibleCountRankTwoPositiveErrorReal
    XoP.ANOVA.uniformAverage
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro y _hy
  exact max_sub_one_le_max_sub_one_add_abs_sub
    (XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y)
    (compatibleCountRankTwoDensityReal G q hq2 y)

/-- Comparing the true density to the rank-three-adjusted density leaves only
the rank-four-and-higher density difference. -/
theorem compatibleCountTruePositiveErrorReal_le_rankThree_add_average_abs_diff
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) :
    compatibleCountTruePositiveErrorReal G q ≤
      compatibleCountRankThreePositiveErrorReal G q hq2 hq3 +
        XoP.ANOVA.uniformAverage (Fin q → G)
          (fun y => |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
            compatibleCountRankThreeDensityReal G q hq2 hq3 y|) := by
  unfold compatibleCountTruePositiveErrorReal compatibleCountRankThreePositiveErrorReal
    XoP.ANOVA.uniformAverage
  rw [← add_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro y _hy
  exact max_sub_one_le_max_sub_one_add_abs_sub
    (XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y)
    (compatibleCountRankThreeDensityReal G q hq2 hq3 y)

/-- The average density-tail contribution is bounded by the exact normalized
average of the absolute higher-rank gain-graph tail. -/
theorem compatibleCountAverageTail_le_rankTailAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
      compatibleCountLowRankDensityReal G q y|) ≤
    (rankTailAverageErrorBound G q hq0 : ℝ) := by
  unfold rankTailAverageErrorBound
  have hnonneg :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankTailBeyondOneInt
              (G := G) (q := q) y hq0 : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  rw [Real.coe_toNNReal _ hnonneg]
  unfold XoP.ANOVA.uniformAverage
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro y _hy
  rw [compatibleCountDensityTailPointwise_eq_rankTail
    (G := G) (q := q) hq0 hq y]

/-- The average density difference from the rank-two-adjusted comparison point
is bounded by the exact normalized average absolute ranks-three-and-higher
tail. -/
theorem compatibleCountAverageTailBeyondTwo_le_rankTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
      compatibleCountRankTwoDensityReal G q hq2 y|) ≤
    (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  unfold rankTailBeyondTwoAverageErrorBound
  have hnonneg :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankTailBeyondTwoInt
              (G := G) q y : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  rw [Real.coe_toNNReal _ hnonneg]
  unfold XoP.ANOVA.uniformAverage
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro y _hy
  rw [compatibleCountDensityTailPointwise_eq_tailBeyondTwo
    (G := G) (q := q) hq0 hq2 hq y]

/-- The average density difference from the rank-three-adjusted comparison
point is bounded by the exact normalized average absolute rank-four-and-higher
tail. -/
theorem compatibleCountAverageTailBeyondThree_le_rankTailBeyondThreeAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
  XoP.ANOVA.uniformAverage (Fin q → G)
    (fun y => |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
      compatibleCountRankThreeDensityReal G q hq2 hq3 y|) ≤
    (rankTailBeyondThreeAverageErrorBound G q : ℝ) := by
  unfold rankTailBeyondThreeAverageErrorBound
  have hnonneg :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankTailBeyondThreeInt
              (G := G) q y : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  rw [Real.coe_toNNReal _ hnonneg]
  unfold XoP.ANOVA.uniformAverage
  apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro y _hy
  rw [compatibleCountDensityTailPointwise_eq_tailBeyondThree
    (G := G) (q := q) hq0 hq2 hq3 hq y]

/-- The exact average rank-tail error is precisely the uniform average of the
density-tail difference. -/
theorem rankTailAverageErrorBound_toReal_eq_averageDensityTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    (rankTailAverageErrorBound G q hq0 : ℝ) =
      XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y => |XoP.ANOVA.visibleDensityRatioReal (G := G) (q := q) y -
          compatibleCountLowRankDensityReal G q y|) := by
  unfold rankTailAverageErrorBound
  have hnonneg :
      0 ≤ XoP.ANOVA.uniformAverage (Fin q → G)
        (fun y =>
          |((collisionSubfamilyRankTailBeyondOneInt
              (G := G) (q := q) y hq0 : ℤ) : ℝ)| /
            (XoP.ANOVA.visibleNormalizerNNReal (G := G) (q := q) : ℝ)) := by
    unfold XoP.ANOVA.uniformAverage
    refine div_nonneg ?_ (Nat.cast_nonneg _)
    apply Finset.sum_nonneg
    intro y _hy
    exact div_nonneg (abs_nonneg _) (by positivity)
  rw [Real.coe_toNNReal _ hnonneg]
  unfold XoP.ANOVA.uniformAverage
  apply congrArg (fun s : ℝ => s / (Fintype.card (Fin q → G) : ℝ))
  apply Finset.sum_congr rfl
  intro y _hy
  dsimp
  rw [← compatibleCountDensityTailPointwise_eq_rankTail
    (G := G) (q := q) hq0 hq y]

/-- The exact average rank-tail error is no larger than the older pointwise
closed-form rank-tail bound. -/
theorem rankTailAverageErrorBound_le_rankTailErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    rankTailAverageErrorBound G q (lt_of_lt_of_le (by norm_num) hq2) ≤
      rankTailErrorBound G q := by
  rw [← NNReal.coe_le_coe]
  rw [rankTailAverageErrorBound_toReal_eq_averageDensityTail
    (G := G) (q := q) (hq0 := lt_of_lt_of_le (by norm_num) hq2) hq]
  apply compatibleCountAverageTailBound_of_pointwise (G := G) q
  intro y
  exact compatibleCountDensityTailPointwise_le_rankTailErrorBound
    (G := G) q hq2 hq y

/-- The average-tail finite error refines the previous finite error term that
used the pointwise closed-form rank-tail bound. -/
theorem finiteOrbitAverageTailErrorBound_le_finiteOrbitErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    finiteOrbitAverageTailErrorBound G q (lt_of_lt_of_le (by norm_num) hq2) ≤
      finiteOrbitErrorBound G q := by
  unfold finiteOrbitAverageTailErrorBound finiteOrbitErrorBound
  simpa [add_comm] using add_le_add_left
    (rankTailAverageErrorBound_le_rankTailErrorBound (G := G) q hq2 hq)
    (lowRankCollisionFiberResidualErrorBound G q)

/-- The average-tail error with exact occupancy residual is bounded by the
average-tail error with the closed-form endpoint residual. -/
theorem finiteOrbitAverageTailErrorBound_le_finiteOrbitAverageTailMaxResidualErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    finiteOrbitAverageTailErrorBound G q hq0 ≤
      finiteOrbitAverageTailMaxResidualErrorBound G q hq0 := by
  unfold finiteOrbitAverageTailErrorBound finiteOrbitAverageTailMaxResidualErrorBound
  simpa [add_comm] using add_le_add_right
    (lowRankCollisionFiberResidualErrorBound_le_lowRankCollisionMaxResidualErrorBound
      (G := G) (q := q) hq0 hq)
    (rankTailAverageErrorBound G q hq0)

/-- Splitting the average tail into rank two plus ranks three and higher gives
a (potentially looser, but structurally sharper) finite error boundary. -/
theorem finiteOrbitAverageTailErrorBound_le_rankTwoTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) :
    finiteOrbitAverageTailErrorBound G q hq0 ≤
      finiteOrbitRankTwoTailBeyondTwoAverageErrorBound G q hq2 := by
  unfold finiteOrbitAverageTailErrorBound
    finiteOrbitRankTwoTailBeyondTwoAverageErrorBound
  have htail :=
    rankTailAverageErrorBound_le_rankTwo_add_tailBeyondTwoAverage
      (G := G) q hq0 hq2
  calc
    lowRankCollisionFiberResidualErrorBound G q + rankTailAverageErrorBound G q hq0 ≤
      lowRankCollisionFiberResidualErrorBound G q +
        (rankTwoLayerAverageErrorBound G q hq2 +
          rankTailBeyondTwoAverageErrorBound G q) := by
        exact add_le_add le_rfl htail
    _ = lowRankCollisionFiberResidualErrorBound G q +
        rankTwoLayerAverageErrorBound G q hq2 +
        rankTailBeyondTwoAverageErrorBound G q := by
        rw [add_assoc]

/-- Replacing the exact rank-three-and-higher average by its closed pointwise
fallback gives the current rank-split closed finite error. -/
theorem finiteOrbitRankTwoTailBeyondTwoAverageErrorBound_le_rankTwoClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) (hq : q ≤ Fintype.card G) :
    finiteOrbitRankTwoTailBeyondTwoAverageErrorBound G q hq2 ≤
      finiteOrbitRankTwoClosedBeyondTwoErrorBound G q hq2 := by
  unfold finiteOrbitRankTwoTailBeyondTwoAverageErrorBound
    finiteOrbitRankTwoClosedBeyondTwoErrorBound
  have htail :=
    rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound
      (G := G) q hq3 hq
  exact add_le_add le_rfl htail

/-- The cancellation-aware rank-two-positive finite error is bounded by the
older termwise rank-two split.  This formally records that moving the signed
rank-two layer into the comparison density cannot worsen the finite RHS. -/
theorem finiteOrbitRankTwoPositiveTailBeyondTwoAverageErrorBound_le_rankTwoTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) :
    finiteOrbitRankTwoPositiveTailBeyondTwoAverageErrorBound G q hq2 ≤
      finiteOrbitRankTwoTailBeyondTwoAverageErrorBound G q hq2 := by
  unfold finiteOrbitRankTwoPositiveTailBeyondTwoAverageErrorBound
    finiteOrbitRankTwoTailBeyondTwoAverageErrorBound
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add
      (rankTwoPositiveResidualErrorBound_le_lowRank_add_rankTwoLayerAverage
        (G := G) (q := q) hq2)
      (le_rfl : rankTailBeyondTwoAverageErrorBound G q ≤
        rankTailBeyondTwoAverageErrorBound G q)

/-- Replacing the exact rank-two average by its closed pointwise fallback gives
the closed gain-graph rank-split finite error. -/
theorem finiteOrbitRankTwoClosedBeyondTwoErrorBound_le_closedRankSplitErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    finiteOrbitRankTwoClosedBeyondTwoErrorBound G q hq2 ≤
      finiteOrbitClosedRankSplitErrorBound G q := by
  unfold finiteOrbitRankTwoClosedBeyondTwoErrorBound
    finiteOrbitClosedRankSplitErrorBound
  have htwo :=
    rankTwoLayerAverageErrorBound_le_rankTwoLayerErrorBound
      (G := G) q hq2 hq
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right
      (add_le_add_left htwo (lowRankCollisionFiberResidualErrorBound G q))
      (rankTailBeyondTwoErrorBound G q)

/-- The exact average-tail finite error is bounded by the rank-two plus closed
rank-three-and-higher finite error. -/
theorem finiteOrbitAverageTailErrorBound_le_rankTwoClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    finiteOrbitAverageTailErrorBound G q hq0 ≤
      finiteOrbitRankTwoClosedBeyondTwoErrorBound G q hq2 :=
  le_trans
    (finiteOrbitAverageTailErrorBound_le_rankTwoTailBeyondTwoAverageErrorBound
      (G := G) (q := q) hq0 hq2)
    (finiteOrbitRankTwoTailBeyondTwoAverageErrorBound_le_rankTwoClosedBeyondTwoErrorBound
      (G := G) (q := q) hq2 hq3 hq)

/-- The exact average-tail finite error is bounded by the fully closed
gain-graph rank-split finite error. -/
theorem finiteOrbitAverageTailErrorBound_le_closedRankSplitErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    finiteOrbitAverageTailErrorBound G q hq0 ≤
      finiteOrbitClosedRankSplitErrorBound G q :=
  le_trans
    (finiteOrbitAverageTailErrorBound_le_rankTwoClosedBeyondTwoErrorBound
      (G := G) (q := q) hq0 hq2 hq3 hq)
    (finiteOrbitRankTwoClosedBeyondTwoErrorBound_le_closedRankSplitErrorBound
      (G := G) (q := q) hq2 hq)

/-- The exact average tail is bounded by the closed rank-split tail once rank
two and rank three-and-higher are bounded separately. -/
theorem rankTailAverageErrorBound_le_rankSplitTailErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    rankTailAverageErrorBound G q hq0 ≤ rankSplitTailErrorBound G q := by
  have hsplit :=
    rankTailAverageErrorBound_le_rankTwo_add_tailBeyondTwoAverage
      (G := G) q hq0 hq2
  have htwo :=
    rankTwoLayerAverageErrorBound_le_rankTwoLayerErrorBound
      (G := G) q hq2 hq
  have hthree :=
    rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound
      (G := G) q hq3 hq
  unfold rankSplitTailErrorBound
  exact le_trans hsplit (add_le_add htwo hthree)

/-- The finite error with exact occupancy residual is bounded by the fully
closed fallback finite error. -/
theorem finiteOrbitErrorBound_le_finiteOrbitMaxResidualErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    finiteOrbitErrorBound G q ≤ finiteOrbitMaxResidualErrorBound G q := by
  unfold finiteOrbitErrorBound finiteOrbitMaxResidualErrorBound
  simpa [add_comm] using add_le_add_right
    (lowRankCollisionFiberResidualErrorBound_le_lowRankCollisionMaxResidualErrorBound
      (G := G) (q := q) hq0 hq)
    (rankTailErrorBound G q)

/-- The finite error with exact occupancy residual is bounded by the fully
closed max-residual gain-graph rank-split finite error. -/
theorem finiteOrbitClosedRankSplitErrorBound_le_maxResidualClosedRankSplitErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    finiteOrbitClosedRankSplitErrorBound G q ≤
      finiteOrbitMaxResidualClosedRankSplitErrorBound G q := by
  unfold finiteOrbitClosedRankSplitErrorBound
    finiteOrbitMaxResidualClosedRankSplitErrorBound
  have hlow :=
    lowRankCollisionFiberResidualErrorBound_le_lowRankCollisionMaxResidualErrorBound
      (G := G) (q := q) hq0 hq
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right
      (add_le_add_right hlow (rankTwoLayerErrorBound G q))
      (rankTailBeyondTwoErrorBound G q)

/-- Visible low-rank/tail bridge using the exact average rank-tail error
instead of the current pointwise cardinality tail. -/
theorem visibleStatDistLowRankTailBridge_of_rankTailAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      compatibleCountLowRankPositiveErrorReal G q +
        (rankTailAverageErrorBound G q hq0 : ℝ) := by
  rw [visibleStatDist_toReal_eq_compatibleCountTruePositiveErrorReal
    (G := G) q hq]
  exact le_trans
    (compatibleCountTruePositiveErrorReal_le_lowRank_add_average_abs_diff
      (G := G) (q := q))
    (add_le_add le_rfl
      (compatibleCountAverageTail_le_rankTailAverageErrorBound
        (G := G) q hq0 hq))

/-- Visible bridge from the rank-two-adjusted density to the true density.
Unlike the low-rank bridge, this pays only the ranks-three-and-higher
gain-graph tail. -/
theorem visibleStatDistRankTwoTailBridge_of_tailBeyondTwoAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      compatibleCountRankTwoPositiveErrorReal G q hq2 +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  rw [visibleStatDist_toReal_eq_compatibleCountTruePositiveErrorReal
    (G := G) q hq]
  exact le_trans
    (compatibleCountTruePositiveErrorReal_le_rankTwo_add_average_abs_diff
      (G := G) (q := q) hq2)
    (add_le_add le_rfl
      (compatibleCountAverageTailBeyondTwo_le_rankTailBeyondTwoAverageErrorBound
        (G := G) q hq0 hq2 hq))

/-- Visible bridge from the rank-three-adjusted density to the true density.
This pays only the rank-four-and-higher gain-graph tail. -/
theorem visibleStatDistRankThreeTailBridge_of_tailBeyondThreeAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      compatibleCountRankThreePositiveErrorReal G q hq2 hq3 +
        (rankTailBeyondThreeAverageErrorBound G q : ℝ) := by
  rw [visibleStatDist_toReal_eq_compatibleCountTruePositiveErrorReal
    (G := G) q hq]
  exact le_trans
    (compatibleCountTruePositiveErrorReal_le_rankThree_add_average_abs_diff
      (G := G) (q := q) hq2 hq3)
    (add_le_add le_rfl
      (compatibleCountAverageTailBeyondThree_le_rankTailBeyondThreeAverageErrorBound
        (G := G) q hq0 hq2 hq3 hq))

/-- Visible bound using the signed rank-two-adjusted positive residual and the
exact average ranks-three-and-higher tail.  This is the first formal endpoint
that removes the `E_2` absolute-value slack from the RHS. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_rankTwoResidual_add_tailBeyondTwoAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankTwoPositiveResidualErrorBound G q hq2 : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  have hbridge := visibleStatDistRankTwoTailBridge_of_tailBeyondTwoAverage
    (G := G) q hq0 hq2 hq
  have hrankTwo :=
    compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_residual
      (G := G) (q := q) hq2
  calc
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountRankTwoPositiveErrorReal G q hq2 +
          (rankTailBeyondTwoAverageErrorBound G q : ℝ) := hbridge
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          (rankTwoPositiveResidualErrorBound G q hq2 : ℝ)) +
          (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hrankTwo
              (rankTailBeyondTwoAverageErrorBound G q : ℝ)
    _ = (spatialReconstructionBound G q : ℝ) +
        (rankTwoPositiveResidualErrorBound G q hq2 : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by ring

/-- Visible bound using the signed rank-three-adjusted positive residual and
the exact average ranks-four-and-higher tail.  This exposes the next
cancellation layer instead of charging all rank-three subfamilies in the
absolute tail. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_tailBeyondThreeAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankThreePositiveResidualErrorBound G q hq2 hq3 : ℝ) +
        (rankTailBeyondThreeAverageErrorBound G q : ℝ) := by
  have hbridge := visibleStatDistRankThreeTailBridge_of_tailBeyondThreeAverage
    (G := G) q hq0 hq2 hq3 hq
  let x : ℝ := compatibleCountRankThreePositiveErrorReal G q hq2 hq3
  let b : ℝ := (spatialReconstructionBound G q : ℝ)
  have hrankThree : x ≤ b + (rankThreePositiveResidualErrorBound G q hq2 hq3 : ℝ) := by
    unfold rankThreePositiveResidualErrorBound
    dsimp [x, b]
    change x ≤ b + ↑(Real.toNNReal (x - b))
    rw [Real.coe_toNNReal']
    exact le_add_positive_residual x b
  calc
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountRankThreePositiveErrorReal G q hq2 hq3 +
          (rankTailBeyondThreeAverageErrorBound G q : ℝ) := hbridge
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          (rankThreePositiveResidualErrorBound G q hq2 hq3 : ℝ)) +
          (rankTailBeyondThreeAverageErrorBound G q : ℝ) := by
          simpa [x] using
            add_le_add_right hrankThree
              (rankTailBeyondThreeAverageErrorBound G q : ℝ)
    _ = (spatialReconstructionBound G q : ℝ) +
        (rankThreePositiveResidualErrorBound G q hq2 hq3 : ℝ) +
        (rankTailBeyondThreeAverageErrorBound G q : ℝ) := by ring

/-- Visible bound after exposing signed rank three and keeping the
cycle-consistency predicate in the rank-four-and-higher tail. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_consistentBeyondThreeAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankThreePositiveResidualErrorBound G q hq2 hq3 : ℝ) +
        (rankTailBeyondThreeConsistentAverageErrorBound G q : ℝ) := by
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_tailBeyondThreeAverage
      (G := G) q hq0 hq2 hq3 hq
  have htail :=
    rankTailBeyondThreeAverageErrorBound_le_consistentAverageErrorBound
      (G := G) q
  exact le_trans hvisible (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left
        (add_le_add_left (show
          (rankTailBeyondThreeAverageErrorBound G q : ℝ) ≤
            (rankTailBeyondThreeConsistentAverageErrorBound G q : ℝ) by
            exact_mod_cast htail)
          (rankThreePositiveResidualErrorBound G q hq2 hq3 : ℝ))
        (spatialReconstructionBound G q : ℝ))

/-- Visible closed-tail bound after exposing signed rank three.  The remaining
closed tail has rank-four scale. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_tailBeyondThreeClosed
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q) (hq4 : 4 ≤ q)
    (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankThreePositiveResidualErrorBound G q hq2 hq3 : ℝ) +
        (rankTailBeyondThreeErrorBound G q : ℝ) := by
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_tailBeyondThreeAverage
      (G := G) q hq0 hq2 hq3 hq
  have htail :=
    rankTailBeyondThreeAverageErrorBound_le_rankTailBeyondThreeErrorBound
      (G := G) q hq4 hq
  exact le_trans hvisible (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left
        (add_le_add_left (show
          (rankTailBeyondThreeAverageErrorBound G q : ℝ) ≤
            (rankTailBeyondThreeErrorBound G q : ℝ) by
            exact_mod_cast htail)
          (rankThreePositiveResidualErrorBound G q hq2 hq3 : ℝ))
        (spatialReconstructionBound G q : ℝ))

/-- Visible bound using the signed rank-two-adjusted residual and the closed
pointwise fallback for the ranks-three-and-higher tail. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_rankTwoResidual_add_tailBeyondTwoClosed
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankTwoPositiveResidualErrorBound G q hq2 : ℝ) +
        (rankTailBeyondTwoErrorBound G q : ℝ) := by
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_rankTwoResidual_add_tailBeyondTwoAverage
      (G := G) q hq0 hq2 hq
  have htail :=
    rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound
      (G := G) q hq3 hq
  exact le_trans hvisible (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (by exact_mod_cast htail)
        ((spatialReconstructionBound G q : ℝ) +
          (rankTwoPositiveResidualErrorBound G q hq2 : ℝ)))

/-- Visible bound using the scalar rank-two quadratic positive part.  Compared
with the two-statistic residual endpoint, this exposes the next algebraic
target directly: control the low-rank residual together with the scalar
quadratic positive part. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_quadraticPositive_add_tailBeyondTwoAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  have hbridge := visibleStatDistRankTwoTailBridge_of_tailBeyondTwoAverage
    (G := G) q hq0 hq2 hq
  have hrankTwo :=
    compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual_add_quadraticPositive
      (G := G) q hq2 hq
  calc
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountRankTwoPositiveErrorReal G q hq2 +
          (rankTailBeyondTwoAverageErrorBound G q : ℝ) := hbridge
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
          (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ)) +
          (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hrankTwo
              (rankTailBeyondTwoAverageErrorBound G q : ℝ)
    _ = (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by ring

/-- Visible bound using a quadratic collision envelope for the low-rank
positive part.  The low-rank residual is now a second-factorial-moment
remainder rather than the exact or max collision-fiber residual. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_quadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (ε : ℝ) (hq0 : 0 < q) (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hquad : CompatibleCountLowRankQuadraticCollisionBound G q ε) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        ε * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 2 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  have hbridge := visibleStatDistRankTwoTailBridge_of_tailBeyondTwoAverage
    (G := G) q hq0 hq2 hq
  have hrankTwo :=
    compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_quadraticCollision_add_quadraticPositive
      (G := G) (q := q) (ε := ε) hq0 hq2 hq hquad
  calc
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountRankTwoPositiveErrorReal G q hq2 +
          (rankTailBeyondTwoAverageErrorBound G q : ℝ) := hbridge
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          ε * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2 +
          (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ)) +
          (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hrankTwo
              (rankTailBeyondTwoAverageErrorBound G q : ℝ)
    _ = (spatialReconstructionBound G q : ℝ) +
        ε * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 2 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by ring

/-- Visible bound obtained by instantiating the low-rank quadratic envelope
with its finite collision-count certificate.  This is the current fully
finite, non-asymptotic endpoint for the low-rank part: the only remaining work
is to upper-bound the scalar certificate and the rank-two/tail average terms by
closed forms. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_finiteQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : LowRankLowCollisionLineCovered G q) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        lowRankQuadraticEnvelopeCoefficient G q *
          (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  exact
    visibleStatDist_le_spatialReconstructionBound_add_quadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
      (G := G) (q := q) (ε := lowRankQuadraticEnvelopeCoefficient G q)
      hq0 hq2 hq
      (compatibleCountLowRankQuadraticCollisionBound_of_finiteCoefficient
        (G := G) (q := q) hlow)

/-- Small-query version of the finite-certificate endpoint.  The exceptional
`k = 0,1` line-coverage hypothesis is discharged from `q(q-1) <= |G|`. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_finiteQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage_of_queryPair_le_card
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hsmall : q * (q - 1) ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        lowRankQuadraticEnvelopeCoefficient G q *
          (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  exact
    visibleStatDist_le_spatialReconstructionBound_add_finiteQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
      (G := G) (q := q) (lt_of_lt_of_le (by norm_num) hq2) hq2 hq
      (lowRankLowCollisionLineCovered_of_queryPair_le_card
        (G := G) (q := q) hq2 hq hsmall)

/-- Paper-shaped variant of the finite-certificate endpoint.  Once the scalar
certificate is bounded by `c / N^2`, the low-rank quadratic remainder has the
desired fourth-order form
\[
  c\binom{|\operatorname{PairIndex}(q)|}{2}/N^4.
\]
This theorem isolates the exact remaining scalar analytic task. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (c : ℝ) (hq0 : 0 < q) (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : LowRankLowCollisionLineCovered G q)
    (hcoeff : lowRankQuadraticEnvelopeCoefficient G q ≤
      c / (Fintype.card G : ℝ) ^ 2) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        c * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 4 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  have hfinite :=
    visibleStatDist_le_spatialReconstructionBound_add_finiteQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
      (G := G) (q := q) hq0 hq2 hq hlow
  have hN_pos : 0 < (Fintype.card G : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hN_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hchoose_nonneg :
      0 ≤ (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) := by positivity
  have hden_nonneg : 0 ≤ (Fintype.card G : ℝ) ^ 2 := by positivity
  have hquad :
      lowRankQuadraticEnvelopeCoefficient G q *
          (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2 ≤
        c * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 4 := by
    calc
      lowRankQuadraticEnvelopeCoefficient G q *
          (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2 ≤
        (c / (Fintype.card G : ℝ) ^ 2) *
          (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
            (Fintype.card G : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoeff hchoose_nonneg)
            hden_nonneg
      _ = c * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 4 := by
          field_simp [hN_ne]
  exact le_trans hfinite (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_right
        (add_le_add_right
          (add_le_add_left hquad (spatialReconstructionBound G q : ℝ))
          (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ))
        (rankTailBeyondTwoAverageErrorBound G q : ℝ))

/-- Small-query paper-shaped variant of the finite-certificate endpoint.  The
only remaining low-rank analytic input is the coefficient estimate
`lowRankQuadraticEnvelopeCoefficient G q <= c / N^2`; the low-collision line
coverage is now proved from `q(q-1) <= |G|`. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage_of_queryPair_le_card
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (c : ℝ) (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hsmall : q * (q - 1) ≤ Fintype.card G)
    (hcoeff : lowRankQuadraticEnvelopeCoefficient G q ≤
      c / (Fintype.card G : ℝ) ^ 2) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        c * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 4 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  exact
    visibleStatDist_le_spatialReconstructionBound_add_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
      (G := G) (q := q) (c := c) (lt_of_lt_of_le (by norm_num) hq2) hq2 hq
      (lowRankLowCollisionLineCovered_of_queryPair_le_card
        (G := G) (q := q) hq2 hq hsmall)
      hcoeff

/-- Constant-`12` paper-shaped small-query endpoint.

Compared with the preceding finite-certificate endpoint, this version has no
open low-rank coefficient hypothesis: the scalar high-collision coefficient has
been discharged and contributes only the explicit fourth-order term
`12 * choose(#PairIndex, 2) / N^4`. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_twelve_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (hsmall : q * (q - 1) ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        12 * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
          (Fintype.card G : ℝ) ^ 4 +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  exact
    visibleStatDist_le_spatialReconstructionBound_add_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage_of_queryPair_le_card
      (G := G) (q := q) (c := 12) hq2 hq hsmall
      (lowRankQuadraticEnvelopeCoefficient_le_twelve_inv_sq_of_queryPair_le_card
        (G := G) (q := q) hq2 hq hsmall)

/-- Closed-tail variant of the scalar rank-two quadratic-positive visible
endpoint. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_quadraticPositive_add_tailBeyondTwoClosed
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoErrorBound G q : ℝ) := by
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_quadraticPositive_add_tailBeyondTwoAverage
      (G := G) q hq0 hq2 hq
  have htail :=
    rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound
      (G := G) q hq3 hq
  exact le_trans hvisible (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (by exact_mod_cast htail)
        ((spatialReconstructionBound G q : ℝ) +
          (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
          (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ)))

/-- Visible bound for the scalar rank-two quadratic route after the low-rank
positive-error bound has been discharged.  This removes the explicit
`lowRankCollisionFiberResidualErrorBound` term from the sharper signed-rank-two
endpoint. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_quadraticPositive_add_tailBeyondTwoAverage_of_lowRank
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
  have hbridge := visibleStatDistRankTwoTailBridge_of_tailBeyondTwoAverage
    (G := G) q hq0 hq2 hq
  have hrankTwo :=
    compatibleCountRankTwoPositiveErrorReal_le_spatialReconstructionBound_add_quadraticPositive_of_lowRank
      (G := G) q hq2 hq hlow
  calc
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountRankTwoPositiveErrorReal G q hq2 +
          (rankTailBeyondTwoAverageErrorBound G q : ℝ) := hbridge
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ)) +
          (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hrankTwo
            (rankTailBeyondTwoAverageErrorBound G q : ℝ)
    _ = (spatialReconstructionBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoAverageErrorBound G q : ℝ) := by ring

/-- Closed-tail variant of the scalar rank-two quadratic route after the
low-rank positive-error bound has been discharged. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_quadraticPositive_add_tailBeyondTwoClosed_of_lowRank
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq2 : 2 ≤ q) (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ) +
        (rankTailBeyondTwoErrorBound G q : ℝ) := by
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_quadraticPositive_add_tailBeyondTwoAverage_of_lowRank
      (G := G) q hq0 hq2 hq hlow
  have htail :=
    rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound
      (G := G) q hq3 hq
  exact le_trans hvisible (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (by exact_mod_cast htail)
        ((spatialReconstructionBound G q : ℝ) +
          (rankTwoEqualityQuadraticPositiveErrorBound G q : ℝ)))

/-- The formal count-tail estimate implies the average density-tail obligation
in the nontrivial query regime. -/
theorem compatibleCountAverageTailBound_of_count_tail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    CompatibleCountAverageTailBound G q := by
  apply compatibleCountAverageTailBound_of_pointwise (G := G) q
  intro y
  exact compatibleCountDensityTailPointwise_le_rankTailErrorBound
    (G := G) q hq2 hq y

/-- The visible low-rank/tail bridge follows from identifying `visibleStatDist`
with the true positive-error expression and bounding the average density tail.
-/
theorem visibleStatDistLowRankTailBridge_of_truePositiveError_and_averageTail
    (q : Nat)
    (htrue :
      (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountTruePositiveErrorReal G q)
    (htail : CompatibleCountAverageTailBound G q) :
    VisibleStatDistLowRankTailBridge G q := by
  dsimp [VisibleStatDistLowRankTailBridge]
  exact le_trans htrue
      (le_trans
      (compatibleCountTruePositiveErrorReal_le_lowRank_add_average_abs_diff
        (G := G) (q := q))
      (add_le_add le_rfl htail))

/-- The visible low-rank/tail bridge follows from the average density-tail
bound; the identification of visible statistical distance with the true
positive-error expression is proved by
`visibleStatDist_toReal_eq_compatibleCountTruePositiveErrorReal`. -/
theorem visibleStatDistLowRankTailBridge_of_averageTail
    (q : Nat)
    (hq : q ≤ Fintype.card G)
    (htail : CompatibleCountAverageTailBound G q) :
    VisibleStatDistLowRankTailBridge G q := by
  apply visibleStatDistLowRankTailBridge_of_truePositiveError_and_averageTail
    (G := G) q
  · rw [visibleStatDist_toReal_eq_compatibleCountTruePositiveErrorReal
      (G := G) q hq]
  · exact htail

/-- The visible low-rank/tail bridge follows directly from the formal
compatible-count tail estimate in the nontrivial query regime. -/
theorem visibleStatDistLowRankTailBridge_of_count_tail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    VisibleStatDistLowRankTailBridge G q := by
  exact visibleStatDistLowRankTailBridge_of_averageTail (G := G) q hq
    (compatibleCountAverageTailBound_of_count_tail (G := G) q hq2 hq)

/-- Unconditional visible bound with the exact low-rank occupancy-fiber
residual and the current rank-tail error. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_rankTailErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 ≤ q) (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTailErrorBound G q : ℝ) := by
  have hbridge := visibleStatDistLowRankTailBridge_of_count_tail (G := G) q hq2 hq
  dsimp [VisibleStatDistLowRankTailBridge] at hbridge
  have hlow :=
    compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual
      (G := G) (q := q)
  calc
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountLowRankPositiveErrorReal G q +
          (rankTailErrorBound G q : ℝ) := hbridge
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          (lowRankCollisionFiberResidualErrorBound G q : ℝ)) +
          (rankTailErrorBound G q : ℝ) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hlow (rankTailErrorBound G q : ℝ)
    _ = (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTailErrorBound G q : ℝ) := by ring

/-- Unconditional visible bound with the exact low-rank occupancy residual and
the exact average absolute higher-rank gain-graph tail. -/
theorem visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_rankTailAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q ≤ Fintype.card G) :
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
      (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTailAverageErrorBound G q hq0 : ℝ) := by
  have hbridge := visibleStatDistLowRankTailBridge_of_rankTailAverage (G := G) q hq0 hq
  have hlow :=
    compatibleCountLowRankPositiveErrorReal_le_spatialReconstructionBound_add_fiberResidual
      (G := G) (q := q)
  calc
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountLowRankPositiveErrorReal G q +
          (rankTailAverageErrorBound G q hq0 : ℝ) := hbridge
    _ ≤ ((spatialReconstructionBound G q : ℝ) +
          (lowRankCollisionFiberResidualErrorBound G q : ℝ)) +
          (rankTailAverageErrorBound G q hq0 : ℝ) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hlow (rankTailAverageErrorBound G q hq0 : ℝ)
    _ = (spatialReconstructionBound G q : ℝ) +
        (lowRankCollisionFiberResidualErrorBound G q : ℝ) +
        (rankTailAverageErrorBound G q hq0 : ℝ) := by ring

/-- RS-style endpoint for the finite-bound proof target.

Once the visible/orbit counting argument proves
`visibleStatDist <= B_q(N) + E_tail(q,N)`, the already-formalized LM20/adaptive
bridge immediately gives the unrestricted adaptive XoP bound with the same
right-hand side. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound
    (q : Nat)
    (hq : q ≤ Fintype.card G)
    (hvisible :
      visibleStatDist (G := G) (q := q) ≤
        spatialReconstructionBound G q + rankTailErrorBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankTailErrorBound G q := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  exact hvisible

/-- Unconditional RS-style endpoint with a fully explicit finite error term:
the current rank-tail error plus the exact occupancy-fiber residual by which
the low-rank positive part exceeds the spatial-reconstruction term. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_fiberResidual_add_rankTailErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        lowRankCollisionFiberResidualErrorBound G q +
        rankTailErrorBound G q := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  exact
    visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_rankTailErrorBound
      (G := G) q hq2 hq

/-- Unconditional RS-style endpoint in `B_q(N)+E(q,N)` form, where
`finiteOrbitErrorBound` is the current explicit finite error term. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + finiteOrbitErrorBound G q := by
  have h :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_fiberResidual_add_rankTailErrorBound
      (G := G) q hq2 hq
  unfold finiteOrbitErrorBound
  simpa [add_assoc] using h

/-- Unconditional RS-style endpoint with the fully closed current finite error:
the endpoint low-rank residual fallback plus the closed pointwise rank-tail
bound. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitMaxResidualErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + finiteOrbitMaxResidualErrorBound G q := by
  exact le_trans
    (xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitErrorBound
      (G := G) q hq2 hq)
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (finiteOrbitErrorBound_le_finiteOrbitMaxResidualErrorBound
            (G := G) (q := q) (lt_of_lt_of_le (by norm_num) hq2) hq)
          (spatialReconstructionBound G q))

/-- Unconditional RS-style endpoint with the sharper average rank-tail error
term. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitAverageTailErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + finiteOrbitAverageTailErrorBound G q hq0 := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_rankTailAverageErrorBound
      (G := G) q hq0 hq
  unfold finiteOrbitAverageTailErrorBound
  simpa [add_assoc] using hvisible

/-- Unconditional RS-style endpoint after splitting the exact average tail into
the rank-two layer and the ranks-three-and-higher tail.  This exposes the next
mathematical target: prove a closed, cancellation-aware estimate for the
rank-two average and for the genuine high-rank tail separately. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoTailBeyondTwoAverageErrorBound G q hq2 := by
  exact le_trans
    (xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitAverageTailErrorBound
      (G := G) q hq0 hq)
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (finiteOrbitAverageTailErrorBound_le_rankTwoTailBeyondTwoAverageErrorBound
            (G := G) (q := q) hq0 hq2)
          (spatialReconstructionBound G q))

/-- Unconditional RS-style endpoint with exact rank-two average and a closed
pointwise fallback for the ranks-three-and-higher tail. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoClosedBeyondTwoErrorBound G q hq2 := by
  exact le_trans
    (xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitAverageTailErrorBound
      (G := G) q hq0 hq)
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (finiteOrbitAverageTailErrorBound_le_rankTwoClosedBeyondTwoErrorBound
            (G := G) (q := q) hq0 hq2 hq3 hq)
          (spatialReconstructionBound G q))

/-- Sharper RS-style endpoint after absorbing the signed rank-two layer into
the main density approximation.  Compared with the earlier rank split, the RHS
no longer contains an absolute rank-two tail term. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoPositiveTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoPositiveTailBeyondTwoAverageErrorBound G q hq2 := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_rankTwoResidual_add_tailBeyondTwoAverage
      (G := G) q hq0 hq2 hq
  unfold finiteOrbitRankTwoPositiveTailBeyondTwoAverageErrorBound
  simpa [add_assoc] using hvisible

/-- Sharper RS-style endpoint after also absorbing the signed graphic-rank-three
layer into the main density approximation.  Compared with the rank-two-positive
endpoint, the absolute average tail starts at graphic rank four. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreePositiveTailBeyondThreeAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankThreePositiveTailBeyondThreeAverageErrorBound G q hq2 hq3 := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_tailBeyondThreeAverage
      (G := G) q hq0 hq2 hq3 hq
  unfold finiteOrbitRankThreePositiveTailBeyondThreeAverageErrorBound
  simpa [add_assoc] using hvisible

/-- RS-style endpoint after exposing signed rank three and retaining
cycle-consistency in the rank-four-and-higher tail. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreePositiveConsistentBeyondThreeAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankThreePositiveConsistentBeyondThreeAverageErrorBound G q hq2 hq3 := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_consistentBeyondThreeAverage
      (G := G) q hq0 hq2 hq3 hq
  unfold finiteOrbitRankThreePositiveConsistentBeyondThreeAverageErrorBound
  simpa [add_assoc] using hvisible

/-- Plug-in endpoint for the post-rank-two-cancellation route.  Once the
signed rank-three positive residual and the rank-four-and-higher
consistency-filtered gain-graph tail are bounded by explicit finite
expressions, the adaptive advantage bound follows without reopening the
rank-two layer. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeResidual_add_consistentTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (ε₃ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hrank3 : RankThreePositiveResidualBound G q hq2 hq3 ε₃)
    (htail : RankTailBeyondThreeConsistentAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₃ + εtail) := by
  have hmain :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreePositiveConsistentBeyondThreeAverageErrorBound
      (G := G) q hq0 hq2 hq3 hq
  have herr :
      finiteOrbitRankThreePositiveConsistentBeyondThreeAverageErrorBound G q hq2 hq3 ≤
        ε₃ + εtail := by
    unfold finiteOrbitRankThreePositiveConsistentBeyondThreeAverageErrorBound
    unfold RankThreePositiveResidualBound at hrank3
    unfold RankTailBeyondThreeConsistentAverageBound at htail
    exact add_le_add hrank3 htail
  exact le_trans hmain (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left herr (spatialReconstructionBound G q))

/-- Coefficient-real-bound endpoint for the post-rank-two-cancellation route.
The rank-three residual hypothesis is stated directly on the explicit
coefficient positive error, avoiding the opaque rank-layer density in the
paper-facing analytic obligation. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeCoefficientRealBound_add_consistentTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (ε₃ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hrank3 :
      compatibleCountRankThreeCoefficientPositiveErrorReal G q -
        (spatialReconstructionBound G q : ℝ) ≤ (ε₃ : ℝ))
    (htail : RankTailBeyondThreeConsistentAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₃ + εtail) := by
  apply
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeResidual_add_consistentTail
      (G := G) (q := q) (ε₃ := ε₃) (εtail := εtail)
      hq0 hq2 hq3 hq
  · exact rankThreePositiveResidualErrorBound_le_of_coefficient_real_bound
      (G := G) (q := q) hq2 hq3 ε₃ hrank3
  · exact htail

/-- Support-split coefficient endpoint for the post-rank-two-cancellation
route.  The rank-three coefficient obligation is reduced to the support-size
`3`/`4` positive region plus an average absolute support-size-at-least-`5`
remainder. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeSupportLeFourRealBound_add_geFiveRealBound_add_consistentTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (εle4 εge5 εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hle4 : compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal G q -
        (spatialReconstructionBound G q : ℝ) ≤ (εle4 : ℝ))
    (hge5 : compatibleCountRankThreeSupportGeFiveAverageErrorReal G q ≤ (εge5 : ℝ))
    (htail : RankTailBeyondThreeConsistentAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + ((εle4 + εge5) + εtail) := by
  apply
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeCoefficientRealBound_add_consistentTail
      (G := G) (q := q) (ε₃ := εle4 + εge5) (εtail := εtail)
      hq0 hq2 hq3 hq
  · have hsplit := compatibleCountRankThreeCoefficientPositiveErrorReal_le_supportLeFour_add_geFive
      (G := G) (q := q)
    calc
      compatibleCountRankThreeCoefficientPositiveErrorReal G q -
          (spatialReconstructionBound G q : ℝ) ≤
        (compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal G q +
            compatibleCountRankThreeSupportGeFiveAverageErrorReal G q) -
          (spatialReconstructionBound G q : ℝ) := by
          exact sub_le_sub_right hsplit _
      _ = (compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal G q -
            (spatialReconstructionBound G q : ℝ)) +
            compatibleCountRankThreeSupportGeFiveAverageErrorReal G q := by ring
      _ ≤ (εle4 : ℝ) + (εge5 : ℝ) := by
          exact add_le_add hle4 hge5
      _ = ((εle4 + εge5 : NNReal) : ℝ) := by simp
  · exact htail

/-- Exact-support low-rank rank-three endpoint.  This is the current
low-support boundary: exact support-size `3` carries the remaining positive
region, while support-size `4` and support-size-at-least-`5` are separated as
average absolute remainders. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeSupportThreeRealBound_add_fourRealBound_add_geFiveRealBound_add_consistentTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (ε3 ε4 εge5 εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (h3 : compatibleCountRankThreeSupportThreeCoefficientPositiveErrorReal G q -
        (spatialReconstructionBound G q : ℝ) ≤ (ε3 : ℝ))
    (h4 : compatibleCountRankThreeSupportFourAverageErrorReal G q ≤ (ε4 : ℝ))
    (hge5 : compatibleCountRankThreeSupportGeFiveAverageErrorReal G q ≤ (εge5 : ℝ))
    (htail : RankTailBeyondThreeConsistentAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (((ε3 + ε4) + εge5) + εtail) := by
  apply
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreeSupportLeFourRealBound_add_geFiveRealBound_add_consistentTail
      (G := G) (q := q) (εle4 := ε3 + ε4) (εge5 := εge5) (εtail := εtail)
      hq0 hq2 hq3 hq
  · have hsplit := compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal_le_supportThree_add_four
      (G := G) (q := q)
    calc
      compatibleCountRankThreeSupportLeFourCoefficientPositiveErrorReal G q -
          (spatialReconstructionBound G q : ℝ) ≤
        (compatibleCountRankThreeSupportThreeCoefficientPositiveErrorReal G q +
            compatibleCountRankThreeSupportFourAverageErrorReal G q) -
          (spatialReconstructionBound G q : ℝ) := by
          exact sub_le_sub_right hsplit _
      _ = (compatibleCountRankThreeSupportThreeCoefficientPositiveErrorReal G q -
            (spatialReconstructionBound G q : ℝ)) +
            compatibleCountRankThreeSupportFourAverageErrorReal G q := by ring
      _ ≤ (ε3 : ℝ) + (ε4 : ℝ) := by exact add_le_add h3 h4
      _ = ((ε3 + ε4 : NNReal) : ℝ) := by simp
  · exact hge5
  · exact htail

/-- RS-style closed-tail endpoint after exposing signed rank three.  Once the
rank-three positive residual is controlled, the remaining closed tail already
has rank-four scale. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankThreePositiveClosedBeyondThreeErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq4 : 4 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankThreePositiveClosedBeyondThreeErrorBound G q hq2 hq3 := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_rankThreeResidual_add_tailBeyondThreeClosed
      (G := G) q hq0 hq2 hq3 hq4 hq
  unfold finiteOrbitRankThreePositiveClosedBeyondThreeErrorBound
  simpa [add_assoc] using hvisible

/-- Closed fallback for the sharper signed-rank-two endpoint: the rank-two
absolute-value slack is gone; only the exact rank-two positive residual and
the closed ranks-three-and-higher tail remain. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoPositiveClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoPositiveClosedBeyondTwoErrorBound G q hq2 := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_rankTwoResidual_add_tailBeyondTwoClosed
      (G := G) q hq0 hq2 hq3 hq
  unfold finiteOrbitRankTwoPositiveClosedBeyondTwoErrorBound
  simpa [add_assoc] using hvisible

/-- RS-style endpoint with the scalar rank-two quadratic positive part exposed
separately from the low-rank residual.  This is the cancellation-aware
rank-two route: it uses the sign of the scalar equality-pattern coefficient
before taking a positive part. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound G q := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_quadraticPositive_add_tailBeyondTwoAverage
      (G := G) q hq0 hq2 hq
  unfold finiteOrbitRankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound
  simpa [add_assoc] using hvisible

/-- Small-query adaptive endpoint with no low-rank residual.  The low-rank
part is charged only by the explicit fourth-order constant-`12` quadratic
collision certificate; the remaining terms are the scalar rank-two quadratic
positive part and the exact average ranks-three-and-higher tail. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoTwelveQuadraticPositiveTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hsmall : q * (q - 1) ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoTwelveQuadraticPositiveTailBeyondTwoAverageErrorBound G q := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  unfold finiteOrbitRankTwoTwelveQuadraticPositiveTailBeyondTwoAverageErrorBound
    twelveClosedQuadraticCollisionErrorBound
  simp only [NNReal.coe_add]
  have htwelve_nonneg :
      0 ≤ 12 * (((Fintype.card (PairIndex q)).choose 2 : Nat) : ℝ) /
        (Fintype.card G : ℝ) ^ 4 := by
    positivity
  rw [Real.coe_toNNReal _ htwelve_nonneg]
  simpa [add_assoc] using
    visibleStatDist_le_spatialReconstructionBound_add_twelve_closedQuadraticCollision_add_quadraticPositive_add_tailBeyondTwoAverage
      (G := G) (q := q) hq2 hq hsmall

/-- Closed-tail variant of the scalar rank-two quadratic-positive endpoint. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoQuadraticPositiveClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoQuadraticPositiveClosedBeyondTwoErrorBound G q := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hvisible :=
    visibleStatDist_le_spatialReconstructionBound_add_fiberResidual_add_quadraticPositive_add_tailBeyondTwoClosed
      (G := G) q hq0 hq2 hq3 hq
  unfold finiteOrbitRankTwoQuadraticPositiveClosedBeyondTwoErrorBound
  simpa [add_assoc] using hvisible

/-- Quadratic-positive endpoint after discharging the low-rank positive-error
bound.  Compared with
`xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound`,
the RHS has no `lowRankCollisionFiberResidualErrorBound` term. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoAverage_of_lowRank
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        rankTwoEqualityQuadraticPositiveErrorBound G q +
        rankTailBeyondTwoAverageErrorBound G q := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  exact visibleStatDist_le_spatialReconstructionBound_add_quadraticPositive_add_tailBeyondTwoAverage_of_lowRank
    (G := G) q hq0 hq2 hq hlow

/-- Closed-tail quadratic-positive endpoint after discharging the low-rank
positive-error bound. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoClosed_of_lowRank
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        rankTwoEqualityQuadraticPositiveErrorBound G q +
        rankTailBeyondTwoErrorBound G q := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  exact visibleStatDist_le_spatialReconstructionBound_add_quadraticPositive_add_tailBeyondTwoClosed_of_lowRank
    (G := G) q hq0 hq2 hq3 hq hlow

/-- Collision-fiber version of the low-rank-discharged quadratic-positive
endpoint.  This keeps the final low-rank premise in the existing scalar
one-dimensional RS form. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoAverage_of_collisionFiber
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hfiber : CompatibleCountLowRankCollisionFiberBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        rankTwoEqualityQuadraticPositiveErrorBound G q +
        rankTailBeyondTwoAverageErrorBound G q := by
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoAverage_of_lowRank
      (G := G) q hq0 hq2 hq
      (compatibleCountLowRankPositiveErrorBound_of_averageCollision
        (G := G) q hq0 (le_trans hq2 hq)
        (compatibleCountLowRankAverageCollisionBound_of_scalarCollision
          (G := G) q
          (compatibleCountLowRankScalarCollisionBound_of_fiberBound
            (G := G) q hfiber)))

/-- Collision-fiber version of the closed-tail low-rank-discharged
quadratic-positive endpoint. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoClosed_of_collisionFiber
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hfiber : CompatibleCountLowRankCollisionFiberBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        rankTwoEqualityQuadraticPositiveErrorBound G q +
        rankTailBeyondTwoErrorBound G q := by
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_quadraticPositive_tailBeyondTwoClosed_of_lowRank
      (G := G) q hq0 hq2 hq3 hq
      (compatibleCountLowRankPositiveErrorBound_of_averageCollision
        (G := G) q hq0 (le_trans hq2 hq)
        (compatibleCountLowRankAverageCollisionBound_of_scalarCollision
          (G := G) q
          (compatibleCountLowRankScalarCollisionBound_of_fiberBound
            (G := G) q hfiber)))

/-- Plug-in endpoint for the quadratic-positive route.  Once the low-rank
fiber residual, scalar rank-two quadratic positive part, and rank-three-plus
average tail are bounded by explicit finite expressions, the adaptive
advantage bound follows without revisiting the LM20/transcript bridge. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_lowRankResidual_add_quadraticPositive_add_tail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (εlow εquad εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : lowRankCollisionFiberResidualErrorBound G q ≤ εlow)
    (hquad : RankTwoEqualityQuadraticPositiveBound G q εquad)
    (htail : RankTailBeyondTwoAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (εlow + εquad + εtail) := by
  have hmain :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound
      (G := G) q hq0 hq2 hq
  have herr :
      finiteOrbitRankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound G q ≤
        εlow + εquad + εtail := by
    unfold finiteOrbitRankTwoQuadraticPositiveTailBeyondTwoAverageErrorBound
    exact add_le_add (add_le_add hlow hquad) htail
  exact le_trans hmain (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left herr (spatialReconstructionBound G q))

/-- Same endpoint as
`xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoPositiveTailBeyondTwoAverageErrorBound`,
but with the residual exposed as the exact two-statistic equality-pattern
residual.  This is the current sharp finite target: prove this residual plus
the rank-three-and-higher average tail is `O(q^4/N^4)`. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound G q := by
  have h :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoPositiveTailBeyondTwoAverageErrorBound
      (G := G) q hq0 hq2 hq
  simpa [finiteOrbitRankTwoPositiveTailBeyondTwoAverageErrorBound,
    finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound,
    rankTwoPositiveResidualErrorBound_eq_statsResidual (G := G) (q := q) hq2] using h

/-- Final plug-in endpoint for the current proof strategy.  Once the
two-statistic rank-two residual and the rank-three-and-higher average tail are
bounded by explicit finite expressions, the adaptive advantage bound follows
without revisiting the transcript/LM20 reduction. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsResidual_add_tail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (ε₂ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hres : RankTwoEqualityStatsPositiveResidualBound G q ε₂)
    (htail : RankTailBeyondTwoAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₂ + εtail) := by
  have hmain :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveTailBeyondTwoAverageErrorBound
      (G := G) q hq0 hq2 hq
  have herr :
      finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound G q ≤
        ε₂ + εtail := by
    unfold finiteOrbitRankTwoStatsPositiveTailBeyondTwoAverageErrorBound
    exact add_le_add hres htail
  exact le_trans hmain (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left herr (spatialReconstructionBound G q))

/-- Erased-fiber version of the final plug-in endpoint.  If all fibers in `S`
are sign-certified below the ideal density, the rank-two residual obligation
only needs to bound the complement of `S`.  This is the theorem boundary that
turns fiber sign-control into an actually smaller RHS. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsSdiffResidual_add_tail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (S : Finset (Nat × Nat))
    (ε₂ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hdens : ∀ kt ∈ S,
      rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 ≤ 1)
    (hres : RankTwoEqualityStatsPositiveResidualSdiffBound G q S ε₂)
    (htail : RankTailBeyondTwoAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₂ + εtail) := by
  apply xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsResidual_add_tail
    (G := G) (q := q) (ε₂ := ε₂) (εtail := εtail) hq0 hq2 hq
  · unfold RankTwoEqualityStatsPositiveResidualSdiffBound at hres
    unfold RankTwoEqualityStatsPositiveResidualBound
    rw [rankTwoEqualityStatsPositiveResidualErrorBound_eq_sdiff_of_density_le_one
      (G := G) (q := q) S hdens]
    exact hres
  · exact htail

/-- Erased-fiber endpoint using positive-part zero proofs directly.  This
variant is convenient when the analytic sign lemma naturally produces
`max (rho - 1) 0 = 0` rather than `rho <= 1`. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsSdiffResidual_add_tail_of_positivePart_zero
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (S : Finset (Nat × Nat))
    (ε₂ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hzero : ∀ kt ∈ S,
      max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0 = 0)
    (hres : RankTwoEqualityStatsPositiveResidualSdiffBound G q S ε₂)
    (htail : RankTailBeyondTwoAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₂ + εtail) := by
  apply xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsResidual_add_tail
    (G := G) (q := q) (ε₂ := ε₂) (εtail := εtail) hq0 hq2 hq
  · unfold RankTwoEqualityStatsPositiveResidualSdiffBound at hres
    unfold RankTwoEqualityStatsPositiveResidualBound
    rw [rankTwoEqualityStatsPositiveResidualErrorBound_eq_sdiff
      (G := G) (q := q) S hzero]
    exact hres
  · exact htail

/-- Concrete first sign-deletion endpoint: if the zero-collision
descending-factorial sign inequality holds, the final residual bound may be
stated over the rank-two two-statistic support with the `(K,T_)=(0,0)` fiber
deleted. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsResidualEraseZeroZero_add_tail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (ε₂ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hzeroSign : (Fintype.card G : ℝ) ^ (2 * q) *
        (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) +
          ((4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
            2 * ((q.choose 3 : Nat) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ))
    (hres : RankTwoEqualityStatsPositiveResidualSdiffBound G q
      ({(0, 0)} : Finset (Nat × Nat)) ε₂)
    (htail : RankTailBeyondTwoAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₂ + εtail) := by
  apply
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsSdiffResidual_add_tail_of_positivePart_zero
      (G := G) (q := q) (S := ({(0, 0)} : Finset (Nat × Nat)))
      (ε₂ := ε₂) (εtail := εtail) hq0 hq2 hq
  · intro kt hkt
    simp at hkt
    subst kt
    exact rankTwoEqualityStatsPositiveFiberTerm_zero_zero_eq_zero_of_descFactorial_le
      (G := G) (q := q) hq2 hq hzeroSign
  · exact hres
  · exact htail

/-- Concrete finite-error endpoint after deleting the `(K,T_)=(0,0)` fiber
from the rank-two two-statistic residual.  This packages the previous plug-in
endpoint with the exact erased residual and exact average rank-three-plus
tail. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveEraseZeroZeroTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hzeroSign : (Fintype.card G : ℝ) ^ (2 * q) *
        (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) +
          ((4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
            2 * ((q.choose 3 : Nat) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoStatsPositiveEraseZeroZeroTailBeyondTwoAverageErrorBound G q := by
  unfold finiteOrbitRankTwoStatsPositiveEraseZeroZeroTailBeyondTwoAverageErrorBound
  apply xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsResidualEraseZeroZero_add_tail
    (G := G) (q := q)
      (ε₂ := rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
        ({(0, 0)} : Finset (Nat × Nat)))
      (εtail := rankTailBeyondTwoAverageErrorBound G q)
      hq0 hq2 hq hzeroSign
  · unfold RankTwoEqualityStatsPositiveResidualSdiffBound
    exact le_rfl
  · unfold RankTailBeyondTwoAverageBound
    exact le_rfl

/-- Closed-tail concrete finite-error endpoint after deleting the
`(K,T_)=(0,0)` fiber from the rank-two two-statistic residual. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveEraseZeroZeroClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hzeroSign : (Fintype.card G : ℝ) ^ (2 * q) *
        (1 + ((((0 : ℤ) - 2 * (Fintype.card (PairIndex q) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ)) +
          ((4 * ((((Fintype.card (PairIndex q)).choose 2 : Nat) : ℤ)) -
            2 * ((q.choose 3 : Nat) : ℤ) : ℤ) : ℝ) /
            (Fintype.card G : ℝ) ^ 2) ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoStatsPositiveEraseZeroZeroClosedBeyondTwoErrorBound G q := by
  have havg :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveEraseZeroZeroTailBeyondTwoAverageErrorBound
      (G := G) q hq0 hq2 hq hzeroSign
  have htail :=
    rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound
      (G := G) q hq3 hq
  exact le_trans havg (by
    unfold finiteOrbitRankTwoStatsPositiveEraseZeroZeroTailBeyondTwoAverageErrorBound
      finiteOrbitRankTwoStatsPositiveEraseZeroZeroClosedBeyondTwoErrorBound
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left
        (add_le_add_left htail
          (rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
            ({(0, 0)} : Finset (Nat × Nat))))
        (spatialReconstructionBound G q))

/-- Concrete finite-error endpoint using the exact sign region of the
two-statistic rank-two equality-pattern density.  No separate sign hypothesis
is needed: the erased set is defined to contain precisely the fibers with
density at most `1`. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound G q := by
  classical
  unfold finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound
  apply xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsSdiffResidual_add_tail
    (G := G) (q := q) (S := rankTwoEqualityStatsNonpositiveFiberSet G q)
      (ε₂ := rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
        (rankTwoEqualityStatsNonpositiveFiberSet G q))
      (εtail := rankTailBeyondTwoAverageErrorBound G q)
      hq0 hq2 hq
  · intro kt hkt
    exact ((mem_rankTwoEqualityStatsNonpositiveFiberSet_iff
      (G := G) (q := q) kt).mp hkt).2
  · unfold RankTwoEqualityStatsPositiveResidualSdiffBound
    exact le_rfl
  · unfold RankTailBeyondTwoAverageBound
    exact le_rfl

/-- Structured high-rank-tail variant of the exact two-statistic sign-region
endpoint.  Compared with the closed high-rank fallback, this keeps the
cycle-consistency predicate in the RHS so the next proof can charge only
balanced rank-three-and-higher gain subgraphs. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionConsistentBeyondTwoAverageErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoStatsPositiveSignRegionConsistentBeyondTwoAverageErrorBound G q := by
  have havg :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound
      (G := G) q hq0 hq2 hq
  have htail :=
    rankTailBeyondTwoAverageErrorBound_le_consistentAverageErrorBound
      (G := G) q
  exact le_trans havg (by
    unfold finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound
      finiteOrbitRankTwoStatsPositiveSignRegionConsistentBeyondTwoAverageErrorBound
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left
        (add_le_add_left htail
          (rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
            (rankTwoEqualityStatsNonpositiveFiberSet G q)))
        (spatialReconstructionBound G q))

/-- If every supported rank-two equality-statistic fiber is sign-certified
below the ideal density, then the rank-two sign-region residual vanishes.
The adaptive endpoint is therefore just the spatial term plus the
consistency-filtered ranks-three-and-higher gain-graph average. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_consistentTail_of_rankTwoStats_nonpositive
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hnonpos : ∀ kt, kt ∈ rankTwoEqualityStatsSupport G q →
      (Fintype.card G : ℝ) ^ (2 * q) *
          rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2 ≤
        (((Fintype.card G).descFactorial q *
          (Fintype.card G).descFactorial q : Nat) : ℝ)) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        rankTailBeyondTwoConsistentAverageErrorBound G q := by
  have hmain :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionConsistentBeyondTwoAverageErrorBound
      (G := G) q hq0 hq2 hq
  have hempty :=
    rankTwoEqualityStatsPositiveFiberSet_eq_empty_of_forall_pow_mul_factor_le_descFactorial_sq
      (G := G) (q := q) hq2 hq hnonpos
  have hres_zero :
      rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
          (rankTwoEqualityStatsNonpositiveFiberSet G q) = 0 := by
    rw [rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_nonpositive_eq_on_positiveSet]
    rw [hempty]
    exact rankTwoEqualityStatsPositiveResidualErrorBoundOn_empty G q
  refine le_trans hmain ?_
  unfold finiteOrbitRankTwoStatsPositiveSignRegionConsistentBeyondTwoAverageErrorBound
  rw [hres_zero]
  simp

/-- Real-inequality plug-in endpoint for the exact rank-two sign region.  To
use this theorem, it is enough to prove one real-valued estimate for the
weighted density excess over the strict positive two-statistic region. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionRealBound_add_tail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (ε₂ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hregion :
      (((∑ kt ∈ rankTwoEqualityStatsPositiveFiberSet G q,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0) /
        (Fintype.card (Fin q → G) : ℝ)) -
      (spatialReconstructionBound G q : ℝ)) ≤ (ε₂ : ℝ))
    (htail : RankTailBeyondTwoAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₂ + εtail) := by
  apply xop_adaptiveAdvantage_le_spatialReconstructionBound_add_statsSdiffResidual_add_tail
    (G := G) (q := q) (S := rankTwoEqualityStatsNonpositiveFiberSet G q)
      (ε₂ := ε₂) (εtail := εtail) hq0 hq2 hq
  · intro kt hkt
    exact ((mem_rankTwoEqualityStatsNonpositiveFiberSet_iff
      (G := G) (q := q) kt).mp hkt).2
  · unfold RankTwoEqualityStatsPositiveResidualSdiffBound
    rw [rankTwoEqualityStatsPositiveResidualErrorBoundSdiff_nonpositive_eq_on_positiveSet
      (G := G) (q := q)]
    exact rankTwoEqualityStatsPositiveResidualErrorBoundOn_le_of_real_bound
      (G := G) (q := q) (R := rankTwoEqualityStatsPositiveFiberSet G q)
      (ε := ε₂) hregion
  · exact htail

/-- Split positive-region endpoint.  The low-collision part of the rank-two
positive sign region is compared directly with `B_q(N)`, while the
high-collision part is reduced to a pointwise `choose K 2` estimate and the
existing second factorial moment. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_lowCollisionPositiveRegionBound_add_highCollisionChooseTwoBound_add_consistentTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (εlow εhigh εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : rankTwoEqualityStatsPositiveRegionContributionReal G q
        (rankTwoEqualityStatsLowCollisionPositiveFiberSet G q) -
        (spatialReconstructionBound G q : ℝ) ≤ (εlow : ℝ))
    (hhigh : ∀ kt ∈ rankTwoEqualityStatsHighCollisionPositiveFiberSet G q,
      max (rankTwoEqualityDensityFromStatsReal G q kt.1 kt.2 - 1) 0 ≤
        (εhigh : ℝ) * (((kt.1.choose 2 : Nat) : ℝ)))
    (htail : RankTailBeyondTwoConsistentAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        (εlow + rankTwoEqualityStatsHighCollisionChooseTwoErrorBound G q εhigh +
          εtail) := by
  apply xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionRealBound_add_tail
    (G := G) (q := q)
    (ε₂ := εlow + rankTwoEqualityStatsHighCollisionChooseTwoErrorBound G q εhigh)
    (εtail := εtail) hq0 hq2 hq
  · change rankTwoEqualityStatsPositiveRegionContributionReal G q
        (rankTwoEqualityStatsPositiveFiberSet G q) -
        (spatialReconstructionBound G q : ℝ) ≤
      ((εlow + rankTwoEqualityStatsHighCollisionChooseTwoErrorBound G q εhigh :
        NNReal) : ℝ)
    have hsplit := rankTwoEqualityStatsPositiveRegionContributionReal_eq_low_add_high
      (G := G) (q := q)
    have hhigh_le :=
      rankTwoEqualityStatsHighCollisionPositiveRegionContributionReal_le_chooseTwo
        (G := G) (q := q) hq2 εhigh hhigh
    rw [hsplit]
    simp only [NNReal.coe_add]
    rw [rankTwoEqualityStatsHighCollisionChooseTwoErrorBound_coe]
    linarith
  · unfold RankTailBeyondTwoAverageBound
    exact (rankTailBeyondTwoAverageErrorBound_le_consistentAverageErrorBound
      (G := G) q).trans htail

/-- Split positive-region endpoint with the high-collision coefficient
instantiated by its exact finite envelope.  The remaining rank-two analytic
obligation is the low-collision residual over `K < 2`; the high-collision
residual is now a closed finite coefficient times the second factorial moment.
-/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_lowCollisionPositiveRegionBound_add_highCollisionEnvelopeBound_add_consistentTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (εlow εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : rankTwoEqualityStatsPositiveRegionContributionReal G q
        (rankTwoEqualityStatsLowCollisionPositiveFiberSet G q) -
        (spatialReconstructionBound G q : ℝ) ≤ (εlow : ℝ))
    (htail : RankTailBeyondTwoConsistentAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        (εlow +
          rankTwoEqualityStatsHighCollisionChooseTwoErrorBound G q
            (rankTwoEqualityStatsHighCollisionEnvelopeCoefficientBound G q) +
          εtail) := by
  apply
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_lowCollisionPositiveRegionBound_add_highCollisionChooseTwoBound_add_consistentTail
      (G := G) (q := q) (εlow := εlow)
      (εhigh := rankTwoEqualityStatsHighCollisionEnvelopeCoefficientBound G q)
      (εtail := εtail) hq0 hq2 hq hlow
  · intro kt hkt
    rw [rankTwoEqualityStatsHighCollisionEnvelopeCoefficientBound_coe]
    exact rankTwoEqualityStatsHighCollisionPositiveFiberTerm_le_envelope_mul_chooseTwo
      (G := G) (q := q) kt hkt
  · exact htail

/-- Factorial-excess plug-in endpoint for the exact rank-two sign region.  This
is the same as
`xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionRealBound_add_tail`,
but the region estimate is stated after rewriting the positive part to the
explicit falling-factorial numerator. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionFactorialExcessBound_add_tail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (ε₂ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hregion :
      (((∑ kt ∈ rankTwoEqualityStatsPositiveFiberSet G q,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          ((((Fintype.card G : ℝ) ^ (2 * q) *
              rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2) -
            (((Fintype.card G).descFactorial q *
              (Fintype.card G).descFactorial q : Nat) : ℝ)) /
            (((Fintype.card G).descFactorial q *
              (Fintype.card G).descFactorial q : Nat) : ℝ))) /
        (Fintype.card (Fin q → G) : ℝ)) -
      (spatialReconstructionBound G q : ℝ)) ≤ (ε₂ : ℝ))
    (htail : RankTailBeyondTwoAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₂ + εtail) := by
  apply xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionRealBound_add_tail
    (G := G) (q := q) (ε₂ := ε₂) (εtail := εtail) hq0 hq2 hq
  · rw [rankTwoEqualityStatsPositiveRegionSum_eq_factorialExcessSum
      (G := G) (q := q) hq2 hq]
    exact hregion
  · exact htail

/-- Paper-shaped plug-in endpoint: the rank-two obligation is the exact
positive sign region, rewritten as a falling-factorial excess, and the
rank-three-and-higher obligation is the consistency-filtered gain-graph
average. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionFactorialExcessBound_add_consistentTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (ε₂ εtail : NNReal)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hregion :
      (((∑ kt ∈ rankTwoEqualityStatsPositiveFiberSet G q,
        (rankTwoEqualityStatsFiberCard G q kt.1 kt.2 : ℝ) *
          ((((Fintype.card G : ℝ) ^ (2 * q) *
              rankTwoEqualityDensityPolynomialFactorReal G q kt.1 kt.2) -
            (((Fintype.card G).descFactorial q *
              (Fintype.card G).descFactorial q : Nat) : ℝ)) /
            (((Fintype.card G).descFactorial q *
              (Fintype.card G).descFactorial q : Nat) : ℝ))) /
        (Fintype.card (Fin q → G) : ℝ)) -
      (spatialReconstructionBound G q : ℝ)) ≤ (ε₂ : ℝ))
    (htail : RankTailBeyondTwoConsistentAverageBound G q εtail) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + (ε₂ + εtail) := by
  apply
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_positiveRegionFactorialExcessBound_add_tail
      (G := G) (q := q) (ε₂ := ε₂) (εtail := εtail) hq0 hq2 hq hregion
  unfold RankTailBeyondTwoAverageBound
  exact (rankTailBeyondTwoAverageErrorBound_le_consistentAverageErrorBound (G := G) q).trans htail

/-- Closed-tail variant of the exact two-statistic sign-region endpoint. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound G q := by
  have havg :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound
      (G := G) q hq0 hq2 hq
  have htail :=
    rankTailBeyondTwoAverageErrorBound_le_rankTailBeyondTwoErrorBound
      (G := G) q hq3 hq
  exact le_trans havg (by
    unfold finiteOrbitRankTwoStatsPositiveSignRegionTailBeyondTwoAverageErrorBound
      finiteOrbitRankTwoStatsPositiveSignRegionClosedBeyondTwoErrorBound
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left
        (add_le_add_left htail
          (rankTwoEqualityStatsPositiveResidualErrorBoundSdiff G q
            (rankTwoEqualityStatsNonpositiveFiberSet G q)))
        (spatialReconstructionBound G q))

/-- Closed-tail variant of the two-statistic residual endpoint. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoStatsPositiveClosedBeyondTwoErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitRankTwoStatsPositiveClosedBeyondTwoErrorBound G q := by
  have h :=
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoPositiveClosedBeyondTwoErrorBound
      (G := G) q hq0 hq2 hq3 hq
  simpa [finiteOrbitRankTwoPositiveClosedBeyondTwoErrorBound,
    finiteOrbitRankTwoStatsPositiveClosedBeyondTwoErrorBound,
    rankTwoPositiveResidualErrorBound_eq_statsResidual (G := G) (q := q) hq2] using h

/-- Unconditional RS-style endpoint with a fully closed gain-graph rank-split
tail: exact low-rank residual, closed rank-two fallback, and closed
rank-three-and-higher fallback. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_closedRankSplitErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitClosedRankSplitErrorBound G q := by
  exact le_trans
    (xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTwoClosedBeyondTwoErrorBound
      (G := G) q hq0 hq2 hq3 hq)
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (finiteOrbitRankTwoClosedBeyondTwoErrorBound_le_closedRankSplitErrorBound
            (G := G) (q := q) hq2 hq)
          (spatialReconstructionBound G q))

/-- Rank-split endpoint without the low-rank residual.  The remaining premise
is exactly the low-rank positive-error bound; after that, the only finite tail
is the closed rank-two plus rank-three-and-higher gain-graph split. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankSplitTailErrorBound_of_lowRank
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankSplitTailErrorBound G q := by
  rw [XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist (G := G) (q := q) hq]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add]
  have hbridge := visibleStatDistLowRankTailBridge_of_rankTailAverage
    (G := G) q hq0 hq
  have htail :=
    rankTailAverageErrorBound_le_rankSplitTailErrorBound
      (G := G) q hq0 hq2 hq3 hq
  calc
    (visibleStatDist (G := G) (q := q) : ℝ) ≤
        compatibleCountLowRankPositiveErrorReal G q +
          (rankTailAverageErrorBound G q hq0 : ℝ) := hbridge
    _ ≤ (spatialReconstructionBound G q : ℝ) +
          (rankSplitTailErrorBound G q : ℝ) := by
          exact add_le_add hlow (by exact_mod_cast htail)

/-- Rank-split endpoint reduced to the one-dimensional collision-fiber
low-rank inequality.  This removes `R_low` from the rank-split theorem
boundary whenever the existing scalar low-rank obligation is discharged. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankSplitTailErrorBound_of_collisionFiber
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hfiber : CompatibleCountLowRankCollisionFiberBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankSplitTailErrorBound G q := by
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankSplitTailErrorBound_of_lowRank
      (G := G) q hq0 hq2 hq3 hq
      (compatibleCountLowRankPositiveErrorBound_of_averageCollision
        (G := G) q hq0 (le_trans hq2 hq)
        (compatibleCountLowRankAverageCollisionBound_of_scalarCollision
          (G := G) q
          (compatibleCountLowRankScalarCollisionBound_of_fiberBound
            (G := G) q hfiber)))

/-- Fully closed max-residual version of the gain-graph rank-split endpoint:
no occupancy-fiber residual and no transcript-average tail term remain. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_maxResidualClosedRankSplitErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq2 : 2 ≤ q)
    (hq3 : 3 ≤ q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitMaxResidualClosedRankSplitErrorBound G q := by
  exact le_trans
    (xop_adaptiveAdvantage_le_spatialReconstructionBound_add_closedRankSplitErrorBound
      (G := G) q hq0 hq2 hq3 hq)
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (finiteOrbitClosedRankSplitErrorBound_le_maxResidualClosedRankSplitErrorBound
            (G := G) (q := q) hq0 hq)
          (spatialReconstructionBound G q))

/-- Unconditional RS-style endpoint with a closed-form fallback for the
low-rank occupancy residual and the exact average higher-rank gain-graph tail.
This is weaker than
`xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitAverageTailErrorBound`,
but its low-rank error term no longer contains the collision-count fiber
distribution. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitAverageTailMaxResidualErrorBound
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq0 : 0 < q)
    (hq : q ≤ Fintype.card G) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q +
        finiteOrbitAverageTailMaxResidualErrorBound G q hq0 := by
  exact le_trans
    (xop_adaptiveAdvantage_le_spatialReconstructionBound_add_finiteOrbitAverageTailErrorBound
      (G := G) q hq0 hq)
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (finiteOrbitAverageTailErrorBound_le_finiteOrbitAverageTailMaxResidualErrorBound
            (G := G) q hq0 hq)
          (spatialReconstructionBound G q))

/-- Decomposed RS-style endpoint for the finite-bound proof target.

This replaces the broad visible-side premise by the two theorem-shaped
obligations that remain after the rank expansion:

* the low-rank positive part is bounded by `B_q(N)`;
* the true visible distance is bounded by the low-rank positive part plus the
  explicit rank-tail error. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank
    (q : Nat)
    (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q)
    (hbridge : VisibleStatDistLowRankTailBridge G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankTailErrorBound G q := by
  apply xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound
    (G := G) q hq
  rw [← NNReal.coe_le_coe]
  exact le_trans hbridge (add_le_add hlow le_rfl)

/-- Decomposed endpoint using the average density-tail obligation directly. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank_averageTail
    (q : Nat)
    (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q)
    (htail : CompatibleCountAverageTailBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankTailErrorBound G q := by
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank
      (G := G) q hq hlow
      (visibleStatDistLowRankTailBridge_of_averageTail (G := G) q hq htail)

/-- Decomposed endpoint using the already-formalized compatible-count tail
estimate directly.  The remaining mathematical obligation is the low-rank
positive-error bound by `spatialReconstructionBound`. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank_countTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hlow : CompatibleCountLowRankPositiveErrorBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankTailErrorBound G q := by
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank
      (G := G) q hq hlow
      (visibleStatDistLowRankTailBridge_of_count_tail (G := G) q hq2 hq)

/-- Endpoint reduced to the final pointwise low-rank collision-envelope
inequality plus the already-formalized count-tail estimate. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_pointwiseCollision_countTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hpoint : CompatibleCountLowRankPointwiseCollisionBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankTailErrorBound G q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hN2 : 2 ≤ Fintype.card G := le_trans hq2 hq
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank_countTail
      (G := G) q hq2 hq
      (compatibleCountLowRankPositiveErrorBound_of_pointwiseCollision
        (G := G) q hq0 hN2 hpoint)

/-- Endpoint reduced to the average low-rank collision-envelope inequality plus
the already-formalized count-tail estimate. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_averageCollision_countTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (havg : CompatibleCountLowRankAverageCollisionBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankTailErrorBound G q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq2
  have hN2 : 2 ≤ Fintype.card G := le_trans hq2 hq
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_lowRank_countTail
      (G := G) q hq2 hq
      (compatibleCountLowRankPositiveErrorBound_of_averageCollision
        (G := G) q hq0 hN2 havg)

/-- Endpoint reduced to the scalar collision-count positive-part bound plus the
already-formalized count-tail estimate. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_scalarCollision_countTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hscalar : CompatibleCountLowRankScalarCollisionBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankTailErrorBound G q := by
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_averageCollision_countTail
      (G := G) q hq2 hq
      (compatibleCountLowRankAverageCollisionBound_of_scalarCollision
        (G := G) q hscalar)

/-- Endpoint reduced to the one-dimensional collision-fiber inequality plus
the already-formalized count-tail estimate. -/
theorem xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_collisionFiber_countTail
    (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat)
    (hq2 : 2 ≤ q)
    (hq : q ≤ Fintype.card G)
    (hfiber : CompatibleCountLowRankCollisionFiberBound G q) :
    advantageAdaptive (XoP.Model.xopRealPDS (G := G) (q := q))
        (XoP.Model.xopIdealPDS (G := G) (q := q)) ≤
      spatialReconstructionBound G q + rankTailErrorBound G q := by
  exact
    xop_adaptiveAdvantage_le_spatialReconstructionBound_add_rankTailErrorBound_of_scalarCollision_countTail
      (G := G) q hq2 hq
      (compatibleCountLowRankScalarCollisionBound_of_fiberBound
        (G := G) q hfiber)

end SoP
end Applications
end RandomSystems
