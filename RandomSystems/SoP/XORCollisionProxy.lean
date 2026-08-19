/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.SoP2
import RandomSystems.Legacy.Applications.SoP.SmallQ

/-!
# The planted-collision representative for XOR of two permutations

This file formalizes the representative-facing part of the collision-proxy
proof.  For a uniformly random visible tape, `K` is the number of equal
coordinate pairs and `M = choose q 2`.  The proxy density is

`1 + N / (N - 1)^2 * (K - M/N)`.

Equivalently, it is the mixture which, with weight `M/(N-1)^2`, plants one
uniformly chosen output collision and otherwise samples an ordinary uniform
tape.  The exact SoP density is compared to this proxy before any absolute
value is taken.  The XOR-specific higher-order estimate is developed below
this distribution-independent layer.

The more general gain-graph-only core estimate is intentionally not stated
here: it remains a separate open generalization.
-/

noncomputable section

open scoped BigOperators NNReal
open RandomSystems.CR18

namespace RandomSystems.SoP.CollisionProxy

open RandomSystems.Applications.SoP
open RandomSystems.Applications.XoP.ANOVA

variable {G : Type*} {q : Nat}

/-! ## Uniform finite averages -/

/-- The elementary identity behind the positive-part/half-`L1` conversion. -/
theorem max_zero_eq_add_abs_div_two (x : Real) :
    max x 0 = (x + |x|) / 2 := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, abs_of_nonpos hx]
    ring
  · rw [max_eq_left hx, abs_of_nonneg hx]
    ring

/-- A centered finite function has equal positive and negative mass, so its
positive part is one half of its uniform `L1` norm. -/
theorem uniformAverage_max_zero_eq_half_l1
    {A : Type*} [Fintype A] [Nonempty A] (f : A -> Real)
    (hmean : uniformAverage A f = 0) :
    uniformAverage A (fun x => max (f x) 0) =
      (1 / 2 : Real) * uniformAverage A (fun x => |f x|) := by
  simp_rw [max_zero_eq_add_abs_div_two]
  unfold uniformAverage at hmean ⊢
  have hcard : (Fintype.card A : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  have hsum : (∑ x : A, f x) = 0 := by
    apply (div_eq_zero_iff).mp hmean |>.resolve_right hcard
  have hsplit :
      (∑ x : A, (f x + |f x|) / 2) =
        ((∑ x : A, f x) + ∑ x : A, |f x|) / 2 := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, Finset.sum_add_distrib]
  rw [hsplit, hsum]
  ring

/-- Reverse triangle inequality after uniform averaging. -/
theorem abs_uniformL1_sub_uniformL1_le
    {A : Type*} [Fintype A] [Nonempty A] (f g : A -> Real) :
    |uniformAverage A (fun x => |f x|) -
        uniformAverage A (fun x => |g x|)| <=
      uniformAverage A (fun x => |f x - g x|) := by
  unfold uniformAverage
  have hcard : 0 <= (Fintype.card A : Real) := by positivity
  rw [<- sub_div, abs_div, abs_of_nonneg hcard]
  apply div_le_div_of_nonneg_right _ hcard
  calc
    abs ((∑ x : A, |f x|) - ∑ x : A, |g x|) =
        abs (∑ x : A, (|f x| - |g x|)) := by rw [Finset.sum_sub_distrib]
    _ <= ∑ x : A, abs (|f x| - |g x|) := Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ x : A, |f x - g x| := by
      apply Finset.sum_le_sum
      intro x _hx
      exact abs_abs_sub_abs_le_abs_sub (f x) (g x)

/-- Monotonicity of the uniform finite average. -/
theorem uniformAverage_mono
    {A : Type*} [Fintype A] [Nonempty A] {f g : A -> Real}
    (h : forall x, f x <= g x) :
    uniformAverage A f <= uniformAverage A g := by
  unfold uniformAverage
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro x _hx
  exact h x

/-- Finite Cauchy--Schwarz in expectation form. -/
theorem uniformAverage_abs_le_sqrt_uniformAverage_sq
    {A : Type*} [Fintype A] [Nonempty A] (f : A -> Real) :
    uniformAverage A (fun x => |f x|) <=
      Real.sqrt (uniformAverage A (fun x => (f x) ^ 2)) := by
  have hs := sum_div_card_sq_le_sum_sq_div_card
    (s := (Finset.univ : Finset A)) (f := fun x => |f x|)
  have hs' :
      (uniformAverage A (fun x => |f x|)) ^ 2 <=
        uniformAverage A (fun x => (f x) ^ 2) := by
    simpa [uniformAverage, sq_abs] using hs
  exact Real.le_sqrt_of_sq_le hs'

/-- A nonnegative random variable differs from its mean in `L1` by at most
twice that mean. -/
theorem uniformAverage_abs_sub_mean_le_two_mul
    {A : Type*} [Fintype A] [Nonempty A] (f : A -> Real) (m : Real)
    (hf : forall x, 0 <= f x) (hm : 0 <= m)
    (hmean : uniformAverage A f = m) :
    uniformAverage A (fun x => |f x - m|) <= 2 * m := by
  calc
    uniformAverage A (fun x => |f x - m|) <=
        uniformAverage A (fun x => f x + m) := by
      apply uniformAverage_mono
      intro x
      calc
        |f x - m| <= |f x| + |m| := abs_sub _ _
        _ = f x + m := by rw [abs_of_nonneg (hf x), abs_of_nonneg hm]
    _ = uniformAverage A f + uniformAverage A (fun _x : A => m) := by
      rw [uniformAverage_add]
    _ = 2 * m := by rw [hmean, uniformAverage_const]; ring

/-! ## Collision statistic and proxy -/

/-- Number of unordered query-coordinate pairs. -/
def pairCount (q : Nat) : Nat := Fintype.card (PairIndex q)

/-- Number of visible answer collisions, as a real-valued statistic. -/
abbrev collisionCount [DecidableEq G] (q : Nat) (y : Fin q -> G) : Real :=
  pairCollisionCountReal G q y

/-- Mean number of visible collisions under a uniform tape. -/
def collisionMean (G : Type*) [Fintype G] (q : Nat) : Real :=
  (pairCount q : Real) / (Fintype.card G : Real)

/-- Centered visible collision count. -/
def centeredCollisionCount (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q -> G) : Real :=
  collisionCount q y - collisionMean G q

/-- The degree-two collision contribution to the SoP likelihood ratio. -/
def collisionKernel (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q -> G) : Real :=
  (Fintype.card G : Real) /
      ((Fintype.card G - 1 : Nat) : Real) ^ 2 *
    centeredCollisionCount G q y

/-- Density of the planted-collision proxy relative to a uniform tape. -/
def proxyDensity (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q -> G) : Real :=
  1 + collisionKernel G q y

/-- Half the uniform `L1` norm of the proxy's centered density. -/
def collisionAdvantage (G : Type*) [Fintype G] [DecidableEq G]
    (q : Nat) : Real :=
  (1 / 2 : Real) *
    uniformAverage (Fin q -> G) (fun y => |collisionKernel G q y|)

/-- Exact SoP likelihood minus the planted-collision proxy likelihood. -/
def remainderDensity [AddGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) (y : Fin q -> G) : Real :=
  visibleDensityRatioReal (G := G) (q := q) y - proxyDensity G q y

/-- Statistical-distance cost of the higher-order correction. -/
def remainderAdvantage [AddGroup G] [Fintype G] [DecidableEq G]
    (q : Nat) : Real :=
  (1 / 2 : Real) *
    uniformAverage (Fin q -> G) (fun y => |remainderDensity (G := G) q y|)

/-- Sparse-regime envelope of the planted-collision proxy. -/
def sparseBound (G : Type*) [Fintype G] (q : Nat) : Real :=
  (pairCount q : Real) / ((Fintype.card G - 1 : Nat) : Real) ^ 2

/-- Dense-regime envelope of the planted-collision proxy.  This is the
terminal-readable form `sqrt(M)/(2 (N-1) sqrt(N-1))`. -/
def denseBound (G : Type*) [Fintype G] (q : Nat) : Real :=
  Real.sqrt (pairCount q : Real) /
    (2 * ((Fintype.card G - 1 : Nat) : Real) *
      Real.sqrt ((Fintype.card G - 1 : Nat) : Real))

@[simp]
theorem pairCount_eq (q : Nat) : pairCount q = q.choose 2 := by
  unfold pairCount
  have hpair := pairIndex_card_mul_two (q := q)
  rw [Nat.choose_two_right]
  omega

/-- The collision statistic has its occupancy-theoretic mean `M/N`. -/
theorem uniformAverage_collisionCount
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq : 0 < q) :
    uniformAverage (Fin q -> G) (collisionCount (G := G) q) =
      collisionMean G q := by
  simpa [collisionMean, pairCount] using
    uniformAverage_pairCollisionCountReal_eq_pairIndex_card_div_card
      G q hq

/-- Centering removes the first collision moment exactly. -/
theorem uniformAverage_centeredCollisionCount
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq : 0 < q) :
    uniformAverage (Fin q -> G) (centeredCollisionCount G q) = 0 := by
  unfold centeredCollisionCount
  rw [uniformAverage_sub, uniformAverage_collisionCount (G := G) q hq,
    uniformAverage_const]
  ring

/-- The collision kernel has mean zero. -/
theorem uniformAverage_collisionKernel
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq : 0 < q) :
    uniformAverage (Fin q -> G) (collisionKernel G q) = 0 := by
  unfold collisionKernel
  rw [uniformAverage_const_mul,
    uniformAverage_centeredCollisionCount (G := G) q hq]
  ring

/-- The proxy density is normalized. -/
theorem uniformAverage_proxyDensity
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq : 0 < q) :
    uniformAverage (Fin q -> G) (proxyDensity G q) = 1 := by
  unfold proxyDensity
  rw [uniformAverage_add, uniformAverage_const,
    uniformAverage_collisionKernel (G := G) q hq]
  ring

/-- The exact higher-order correction is centered. -/
theorem uniformAverage_remainderDensity
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq0 : 0 < q) (hq : q <= Fintype.card G) :
    uniformAverage (Fin q -> G) (remainderDensity (G := G) q) = 0 := by
  unfold remainderDensity
  rw [uniformAverage_sub,
    uniformAverage_visibleDensityRatioReal_eq_one (G := G) (q := q) hq,
    uniformAverage_proxyDensity (G := G) q hq0]
  ring

/-! ## Exact proxy distance and the two elementary regimes -/

/-- Exact mean-absolute-deviation formula for the collision proxy. -/
theorem collisionAdvantage_eq
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hN : 2 <= Fintype.card G) :
    collisionAdvantage G q =
      (Fintype.card G : Real) /
          (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) *
        uniformAverage (Fin q -> G)
          (fun y => |centeredCollisionCount G q y|) := by
  unfold collisionAdvantage collisionKernel
  have hN0 : 0 <= (Fintype.card G : Real) := by positivity
  have hNm1 : 0 <= ((Fintype.card G - 1 : Nat) : Real) := by positivity
  rw [show (fun y : Fin q -> G =>
      |(Fintype.card G : Real) /
          ((Fintype.card G - 1 : Nat) : Real) ^ 2 *
        centeredCollisionCount G q y|) =
      (fun y => ((Fintype.card G : Real) /
          ((Fintype.card G - 1 : Nat) : Real) ^ 2) *
        |centeredCollisionCount G q y|) by
      funext y
      rw [abs_mul, abs_of_nonneg (div_nonneg hN0 (sq_nonneg _))]]
  rw [uniformAverage_const_mul]
  have hNm1_ne : ((Fintype.card G - 1 : Nat) : Real) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hN
  field_simp [hNm1_ne]

/-! The exact variance calculation is deliberately stated separately.  It is
useful beyond the present proxy and reuses the already-formalized first and
second factorial moments of `K`. -/

/-- Exact second moment of the visible collision count. -/
theorem uniformAverage_collisionCount_sq
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 <= q) :
    uniformAverage (Fin q -> G)
        (fun y => (collisionCount (G := G) q y) ^ 2) =
      2 * ((pairCount q).choose 2 : Real) /
          (Fintype.card G : Real) ^ 2 +
        (pairCount q : Real) / (Fintype.card G : Real) := by
  have hchoose :=
    uniformAverage_pairCollisionCountNat_choose_two_eq_pairIndex_choose_two_div_card_sq_closed
      G q hq2
  have hfirst := uniformAverage_collisionCount (G := G) q (by omega)
  have hpoint : forall y : Fin q -> G,
      (collisionCount (G := G) q y) ^ 2 =
        2 * ((pairCollisionCountNat G q y).choose 2 : Real) +
          collisionCount q y := by
    intro y
    change (pairCollisionCountReal G q y) ^ 2 =
      2 * ((pairCollisionCountNat G q y).choose 2 : Real) +
        pairCollisionCountReal G q y
    rw [pairCollisionCountReal_eq_pairCollisionCountNat]
    rw [Nat.cast_choose_two]
    ring
  calc
    uniformAverage (Fin q -> G)
        (fun y => (collisionCount (G := G) q y) ^ 2) =
      uniformAverage (Fin q -> G)
        (fun y => 2 * ((pairCollisionCountNat G q y).choose 2 : Real) +
          collisionCount q y) := by
            congr 1
            funext y
            exact hpoint y
    _ = 2 * uniformAverage (Fin q -> G)
          (fun y => ((pairCollisionCountNat G q y).choose 2 : Real)) +
        uniformAverage (Fin q -> G) (collisionCount (G := G) q) := by
          rw [uniformAverage_add, uniformAverage_const_mul]
    _ = 2 * ((Fintype.card (PairIndex q)).choose 2 : Real) /
          (Fintype.card G : Real) ^ 2 +
        (Fintype.card (PairIndex q) : Real) /
          (Fintype.card G : Real) := by
            rw [hchoose, hfirst]
            simp only [collisionMean, pairCount]
            ring
    _ = _ := by rfl

/-- Exact variance of the visible collision count. -/
theorem uniformAverage_centeredCollisionCount_sq
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 <= q) :
    uniformAverage (Fin q -> G)
        (fun y => (centeredCollisionCount G q y) ^ 2) =
      (pairCount q : Real) * ((Fintype.card G - 1 : Nat) : Real) /
        (Fintype.card G : Real) ^ 2 := by
  have hmean := uniformAverage_collisionCount (G := G) q (by omega)
  have hsecond := uniformAverage_collisionCount_sq (G := G) q hq2
  have hN : (Fintype.card G : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  rw [show (fun y : Fin q -> G => (centeredCollisionCount G q y) ^ 2) =
      (fun y =>
        (collisionCount (G := G) q y) ^ 2 -
          2 * collisionMean G q * collisionCount q y +
          (collisionMean G q) ^ 2) by
      funext y
      unfold centeredCollisionCount
      ring]
  rw [uniformAverage_add, uniformAverage_sub,
    uniformAverage_const_mul, uniformAverage_const]
  rw [hsecond, hmean]
  unfold collisionMean
  rw [Nat.cast_choose_two]
  have hNm1_cast :
      (((Fintype.card G - 1 : Nat) : Real)) =
        (Fintype.card G : Real) - 1 := by
    rw [Nat.cast_sub (by exact Fintype.card_pos)]
    norm_num
  rw [hNm1_cast]
  field_simp [hN]
  ring

/-- Uniform mean absolute deviation of the collision count: elementary
nonnegativity gives the sparse estimate `E|K-EK| <= 2 EK`. -/
theorem uniformAverage_abs_centeredCollisionCount_le
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq : 0 < q) :
    uniformAverage (Fin q -> G)
        (fun y => |centeredCollisionCount G q y|) <=
      2 * collisionMean G q := by
  apply uniformAverage_abs_sub_mean_le_two_mul
  · intro y
    change 0 <= pairCollisionCountReal G q y
    rw [pairCollisionCountReal_eq_pairCollisionCountNat]
    positivity
  · unfold collisionMean
    positivity
  · exact uniformAverage_collisionCount (G := G) q hq

/-- Sparse proxy bound.  It is sharp to first order because a planted
collision is almost perfectly visible below the birthday scale. -/
theorem collisionAdvantage_le_sparseBound
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 <= q) (hN : 2 <= Fintype.card G) :
    collisionAdvantage G q <= sparseBound G q := by
  rw [collisionAdvantage_eq (G := G) q hN]
  have hcoef :
      0 <= (Fintype.card G : Real) /
        (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) := by positivity
  calc
    (Fintype.card G : Real) /
          (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) *
        uniformAverage (Fin q -> G)
          (fun y => |centeredCollisionCount G q y|) <=
      (Fintype.card G : Real) /
          (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) *
        (2 * collisionMean G q) :=
      mul_le_mul_of_nonneg_left
        (uniformAverage_abs_centeredCollisionCount_le (G := G) q (by omega)) hcoef
    _ = sparseBound G q := by
      unfold collisionMean sparseBound
      have hN0 : (Fintype.card G : Real) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
      have hNm1 : ((Fintype.card G - 1 : Nat) : Real) ≠ 0 := by
        exact_mod_cast Nat.sub_ne_zero_of_lt hN
      field_simp [hN0, hNm1]

/-- Cauchy--Schwarz turns the exact collision variance into the raw dense
envelope. -/
theorem collisionAdvantage_le_denseBound_raw
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 <= q) (hN : 2 <= Fintype.card G) :
    collisionAdvantage G q <=
      (Fintype.card G : Real) /
          (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) *
        Real.sqrt
          ((pairCount q : Real) * ((Fintype.card G - 1 : Nat) : Real) /
            (Fintype.card G : Real) ^ 2) := by
  rw [collisionAdvantage_eq (G := G) q hN]
  have hcoef :
      0 <= (Fintype.card G : Real) /
        (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) := by positivity
  apply mul_le_mul_of_nonneg_left _ hcoef
  calc
    uniformAverage (Fin q -> G)
        (fun y => |centeredCollisionCount G q y|) <=
      Real.sqrt (uniformAverage (Fin q -> G)
        (fun y => (centeredCollisionCount G q y) ^ 2)) :=
      uniformAverage_abs_le_sqrt_uniformAverage_sq _
    _ = Real.sqrt
          ((pairCount q : Real) * ((Fintype.card G - 1 : Nat) : Real) /
            (Fintype.card G : Real) ^ 2) := by
      rw [uniformAverage_centeredCollisionCount_sq (G := G) q hq2]

/-- Algebraic normalization of the raw variance envelope. -/
theorem denseBound_raw_eq
    [Fintype G] [Nonempty G]
    (q : Nat) (hN : 2 <= Fintype.card G) :
    (Fintype.card G : Real) /
          (2 * ((Fintype.card G - 1 : Nat) : Real) ^ 2) *
        Real.sqrt
          ((pairCount q : Real) * ((Fintype.card G - 1 : Nat) : Real) /
            (Fintype.card G : Real) ^ 2) = denseBound G q := by
  let N : Real := Fintype.card G
  let A : Real := ((Fintype.card G - 1 : Nat) : Real)
  let M : Real := pairCount q
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hApos : 0 < A := by
    dsimp [A]
    exact_mod_cast Nat.sub_pos_of_lt hN
  have hM : 0 <= M := by dsimp [M]; positivity
  have hsqrtA : Real.sqrt A ≠ 0 := Real.sqrt_ne_zero'.2 hApos
  have hsqrt : Real.sqrt (M * A / N ^ 2) =
      Real.sqrt M * Real.sqrt A / N := by
    rw [Real.sqrt_div (mul_nonneg hM hApos.le),
      Real.sqrt_mul hM, Real.sqrt_sq_eq_abs, abs_of_pos hNpos]
  change N / (2 * A ^ 2) * Real.sqrt (M * A / N ^ 2) =
    Real.sqrt M / (2 * A * Real.sqrt A)
  rw [hsqrt]
  have hsquare : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hApos.le
  field_simp [hNpos.ne', hApos.ne', hsqrtA]
  rw [hsquare]
  ring

/-- Dense proxy bound in its closed square-root form. -/
theorem collisionAdvantage_le_denseBound
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 <= q) (hN : 2 <= Fintype.card G) :
    collisionAdvantage G q <= denseBound G q := by
  rw [← denseBound_raw_eq (G := G) q hN]
  exact collisionAdvantage_le_denseBound_raw (G := G) q hq2 hN

/-- The planted-collision proxy automatically selects the better of its
sparse and dense regimes. -/
theorem collisionAdvantage_le_min
    [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq2 : 2 <= q) (hN : 2 <= Fintype.card G) :
    collisionAdvantage G q <= min (sparseBound G q) (denseBound G q) := by
  exact le_min
    (collisionAdvantage_le_sparseBound (G := G) q hq2 hN)
    (collisionAdvantage_le_denseBound (G := G) q hq2 hN)

/-! ## Comparison with the exact SoP law -/

/-- The maximum adaptive SoP advantage is exactly half the uniform `L1` norm
of its centered compatible-count density. -/
theorem advantage_eq_half_uniformL1
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq : q <= Fintype.card G) :
    PFunPDS.Prob.adaptiveTranscriptAdvantage
        (q := q) (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) =
      (1 / 2 : Real) *
        uniformAverage (Fin q -> G)
          (fun y => |visibleDensityErrorReal (G := G) (q := q) y|) := by
  rw [RandomSystems.SoP.adv_prf_eq_visible_stat_dist_of_le_card G q hq]
  calc
    (visibleStatDist (G := G) (q := q) : Real) =
        compatibleCountTruePositiveErrorReal G q :=
      visibleStatDist_toReal_eq_compatibleCountTruePositiveErrorReal
        (G := G) q hq
    _ = (1 / 2 : Real) *
        uniformAverage (Fin q -> G)
          (fun y => |visibleDensityErrorReal (G := G) (q := q) y|) := by
      unfold compatibleCountTruePositiveErrorReal
      rw [uniformAverage_max_zero_eq_half_l1]
      · rfl
      · exact uniformAverage_xopError_eq_zero (G := G) (q := q) hq

/-- Exact two-sided proxy comparison.  All later XOR analysis has only one
obligation: bound `remainderAdvantage`. -/
theorem abs_advantage_sub_collisionAdvantage_le_remainder
    [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) (hq : q <= Fintype.card G) :
    |PFunPDS.Prob.adaptiveTranscriptAdvantage
          (q := q) (RandomSystems.SoP.xop G) (RandomSystems.SoP.urf G) -
        collisionAdvantage G q| <= remainderAdvantage (G := G) q := by
  rw [advantage_eq_half_uniformL1 (G := G) q hq]
  unfold collisionAdvantage remainderAdvantage
  let f : (Fin q -> G) -> Real :=
    visibleDensityErrorReal (G := G) (q := q)
  let g : (Fin q -> G) -> Real := collisionKernel G q
  have hreverse := abs_uniformL1_sub_uniformL1_le f g
  have hhalf : (0 : Real) <= 1 / 2 := by norm_num
  calc
    |(1 / 2 : Real) * uniformAverage (Fin q -> G) (fun y => |f y|) -
        (1 / 2 : Real) * uniformAverage (Fin q -> G) (fun y => |g y|)| =
      (1 / 2 : Real) *
        |uniformAverage (Fin q -> G) (fun y => |f y|) -
          uniformAverage (Fin q -> G) (fun y => |g y|)| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg hhalf]
    _ <= (1 / 2 : Real) *
        uniformAverage (Fin q -> G) (fun y => |f y - g y|) :=
      mul_le_mul_of_nonneg_left hreverse hhalf
    _ = (1 / 2 : Real) *
        uniformAverage (Fin q -> G)
          (fun y => |remainderDensity (G := G) q y|) := by
      congr 2
      funext y
      congr 1
      dsimp [f, g]
      unfold remainderDensity visibleDensityErrorReal proxyDensity
      ring

end RandomSystems.SoP.CollisionProxy
