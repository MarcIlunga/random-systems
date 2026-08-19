/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.SoP.CollisionCountNormal
import RandomSystems.CompatibleCount
import RandomSystems.Counting
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Sparse and birthday-scale collision-count asymptotics

This is the elementary Poisson side of the collision-count argument.  Below
Poisson rate one, the mean absolute deviation of any nonnegative
integer-valued variable is determined just by its mean and its zero atom.
For the uniform coloring collision count, that zero atom is the exact
birthday product.

The terminal convergence theorem therefore needs no black-box Poisson limit:
the logarithm of the birthday product differs from minus its rate by a
vanishing elementary remainder.
-/

noncomputable section

open scoped BigOperators
open Filter

namespace RandomSystems.SoP.CollisionCountPoisson

open RandomSystems.SoP.CollisionStein
open RandomSystems.SoP.CollisionCountNormal
open RandomSystems.SoP.XORFourier

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- Natural-valued version of the collision count. -/
def collisionCountNat (G : Type*) [DecidableEq G] (q : Nat)
    (y : Fin q → G) : Nat :=
  ∑ e : Edge q,
    if y (edgeRight e) = y (edgeLeft e) then 1 else 0

theorem collisionCount_eq_natCast
    (G : Type*) [DecidableEq G] (q : Nat) (y : Fin q → G) :
    collisionCount G q y = (collisionCountNat G q y : ℝ) := by
  unfold collisionCount collisionCountNat edgeIndicator
  push_cast
  rfl

theorem collisionCountNat_eq_zero_of_injective
    (G : Type*) [DecidableEq G] {q : Nat} {y : Fin q → G}
    (hy : Function.Injective y) :
    collisionCountNat G q y = 0 := by
  unfold collisionCountNat
  apply Finset.sum_eq_zero
  intro e _he
  have hne : y (edgeRight e) ≠ y (edgeLeft e) := by
    intro h
    exact edgeLeft_ne_right e (hy h).symm
  simp [hne]

theorem one_le_collisionCountNat_of_not_injective
    (G : Type*) [DecidableEq G] {q : Nat} {y : Fin q → G}
    (hy : ¬Function.Injective y) :
    1 ≤ collisionCountNat G q y := by
  simp only [Function.Injective] at hy
  push Not at hy
  obtain ⟨i, j, hij, hyij⟩ := hy
  rcases lt_or_gt_of_ne hyij with hijlt | hjilt
  · let e : Edge q := ⟨(i, j), hijlt⟩
    unfold collisionCountNat
    calc
      1 = (if y (edgeRight e) = y (edgeLeft e) then 1 else 0 : Nat) := by
        rw [if_pos]
        change y j = y i
        exact hij.symm
      _ ≤ ∑ f : Edge q,
          (if y (edgeRight f) = y (edgeLeft f) then 1 else 0 : Nat) := by
        exact Finset.single_le_sum
          (f := fun f : Edge q =>
            if y (edgeRight f) = y (edgeLeft f) then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
  · let e : Edge q := ⟨(j, i), hjilt⟩
    unfold collisionCountNat
    calc
      1 = (if y (edgeRight e) = y (edgeLeft e) then 1 else 0 : Nat) := by
        rw [if_pos]
        change y i = y j
        exact hij
      _ ≤ ∑ f : Edge q,
          (if y (edgeRight f) = y (edgeLeft f) then 1 else 0 : Nat) := by
        exact Finset.single_le_sum
          (f := fun f : Edge q =>
            if y (edgeRight f) = y (edgeLeft f) then 1 else 0)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)

theorem uniformAverage_centeredCollisionCount_eq_zero
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    (q : Nat) :
    uniformAverage (Fin q → G) (centeredCollisionCount G q) = 0 := by
  rw [show centeredCollisionCount G q =
      (fun y => ∑ e : Edge q, centeredEdge G e y) by
        funext y
        exact centeredCollisionCount_eq_sum_centeredEdge G q y]
  rw [uniformAverage_finset_sum]
  apply Finset.sum_eq_zero
  intro e _he
  exact uniformAverage_centeredEdge_eq_zero G e

/-- Probability that a uniform coloring has no repeated color. -/
def collisionFreeProbability
    (G : Type*) [Fintype G] (q : Nat) : ℝ :=
  uniformAverage (Fin q → G)
    (fun y => if Function.Injective y then 1 else 0)

theorem abs_centeredCollisionCount_pointwise_of_mean_le_one
    (G : Type*) [Fintype G] [DecidableEq G]
    {q : Nat} (hmean0 : 0 ≤ collisionMean G q)
    (hmean1 : collisionMean G q ≤ 1) (y : Fin q → G) :
    |centeredCollisionCount G q y| =
      centeredCollisionCount G q y +
        2 * collisionMean G q *
          (if Function.Injective y then 1 else 0) := by
  by_cases hy : Function.Injective y
  · have hcount : collisionCount G q y = 0 := by
      rw [collisionCount_eq_natCast,
        collisionCountNat_eq_zero_of_injective G hy]
      norm_num
    rw [centeredCollisionCount, hcount, if_pos hy,
      abs_of_nonpos (by linarith)]
    ring
  · have hcountNat := one_le_collisionCountNat_of_not_injective G hy
    have hcount : 1 ≤ collisionCount G q y := by
      rw [collisionCount_eq_natCast]
      exact_mod_cast hcountNat
    rw [centeredCollisionCount, if_neg hy,
      abs_of_nonneg (by linarith)]
    ring

/-- Below rate one, collision MAD is exactly twice the mean times the
collision-free probability. -/
theorem collisionMAD_eq_two_mul_mean_mul_collisionFree
    (G : Type*) [Fintype G] [DecidableEq G] [Nonempty G]
    {q : Nat} (hmean : collisionMean G q ≤ 1) :
    uniformAverage (Fin q → G)
        (fun y => |centeredCollisionCount G q y|) =
      2 * collisionMean G q * collisionFreeProbability G q := by
  have hmean0 : 0 ≤ collisionMean G q := by
    unfold collisionMean
    positivity
  rw [show (fun y : Fin q → G => |centeredCollisionCount G q y|) =
      (fun y => centeredCollisionCount G q y +
        2 * collisionMean G q *
          (if Function.Injective y then 1 else 0)) by
        funext y
        exact abs_centeredCollisionCount_pointwise_of_mean_le_one
          G hmean0 hmean y]
  rw [uniformAverage_add,
    uniformAverage_centeredCollisionCount_eq_zero G q,
    show (fun y : Fin q → G =>
        2 * collisionMean G q *
          (if Function.Injective y then 1 else 0)) =
      (fun y => (2 * collisionMean G q) *
        (if Function.Injective y then 1 else 0)) by rfl,
    uniformAverage_const_mul]
  unfold collisionFreeProbability
  ring

/-- Exact finite birthday product. -/
def birthdayProduct (N q : Nat) : ℝ :=
  ∏ k ∈ Finset.range q, (1 - (k : ℝ) / (N : ℝ))

theorem collisionFreeProbability_eq_birthdayProduct
    (G : Type*) [Fintype G] [Nonempty G] (q : Nat) :
    collisionFreeProbability G q = birthdayProduct (Fintype.card G) q := by
  unfold collisionFreeProbability uniformAverage average birthdayProduct
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  have hsumNat :
      (∑ y : Fin q → G,
          (if Function.Injective y then 1 else 0 : Nat)) =
        (Fintype.card G).descFactorial q := by
    rw [← RandomSystems.CompatibleCount.injectiveTupleCount_descFactorial]
    unfold RandomSystems.CompatibleCount.injectiveTupleCount
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y _hy
    unfold RandomSystems.CompatibleCount.InjectiveTuple
    by_cases h : Function.Injective y <;> simp [h]
  have hsum :
      (∑ y : Fin q → G,
          (if Function.Injective y then 1 else 0 : ℝ)) =
        ((Fintype.card G).descFactorial q : ℝ) := by
    exact_mod_cast hsumNat
  rw [hsum]
  simp only [Fintype.card_fun, Fintype.card_fin]
  by_cases hqN : q ≤ Fintype.card G
  · rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hfactor :
        (∏ k ∈ Finset.range q,
            (((Fintype.card G - k : Nat) : ℝ))) =
          (Fintype.card G : ℝ) ^ q *
            ∏ k ∈ Finset.range q,
              (1 - (k : ℝ) / (Fintype.card G : ℝ)) := by
      calc
        (∏ k ∈ Finset.range q,
            (((Fintype.card G - k : Nat) : ℝ))) =
          ∏ k ∈ Finset.range q,
            ((Fintype.card G : ℝ) *
              (1 - (k : ℝ) / (Fintype.card G : ℝ))) := by
            apply Finset.prod_congr rfl
            intro k hk
            rw [Nat.cast_sub (le_of_lt
              (lt_of_lt_of_le (Finset.mem_range.mp hk) hqN))]
            field_simp [hcard]
        _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_range]
    rw [hfactor]
    rw [Nat.cast_pow]
    field_simp [hcard]
  · have hNq : Fintype.card G < q := lt_of_not_ge hqN
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hNq]
    simp only [Nat.cast_zero, zero_div]
    symm
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hNq)
    field_simp [hcard]
    ring

/-- The birthday-product exponent, equal to `choose(q,2) / N`. -/
def birthdayRate (N q : Nat) : ℝ :=
  (edgeCount q : ℝ) / (N : ℝ)

theorem birthdayRate_eq_sum
    {N q : Nat} (hN : 0 < N) :
    birthdayRate N q =
      ∑ k ∈ Finset.range q, (k : ℝ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [RandomSystems.CR18.Counting.sum_div_range N q hNR]
  unfold birthdayRate
  have hcount : (edgeCount q : ℝ) * 2 =
      (q : ℝ) * ((q : ℝ) - 1) := by
    calc
      (edgeCount q : ℝ) * 2 = (edgeCount q * 2 : Nat) := by norm_num
      _ = (q * (q - 1) : Nat) := by rw [edgeCount_mul_two]
      _ = (q : ℝ) * ((q : ℝ) - 1) := by
        rcases q with _ | q
        · norm_num
        · push_cast
          ring
  field_simp [hNR.ne']
  linarith

theorem abs_log_one_sub_add_le_two_sq
    {x : ℝ} (hxhalf : x ≤ 1 / 2) :
    |Real.log (1 - x) + x| ≤ 2 * x ^ 2 := by
  have hpos : 0 < 1 - x := by linarith
  have hupper : Real.log (1 - x) ≤ -x := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlowerBase : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) :=
    Real.one_sub_inv_le_log_of_pos hpos
  have hlowerAux : -x - 2 * x ^ 2 ≤ 1 - (1 - x)⁻¹ := by
    rw [show 1 - (1 - x)⁻¹ = -x / (1 - x) by
      field_simp [hpos.ne']
      ring]
    rw [le_div_iff₀ hpos]
    have hsquare : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hsquare (by linarith : 2 * x - 1 ≤ 0)]
  rw [abs_le]
  constructor
  · linarith
  · nlinarith [sq_nonneg x]

/-- Finite logarithmic remainder for the birthday product. -/
theorem abs_log_birthdayProduct_add_rate_le
    {N q : Nat} (hN : 0 < N) (h2q : 2 * q ≤ N) :
    |Real.log (birthdayProduct N q) + birthdayRate N q| ≤
      2 * ((q : ℝ) / (N : ℝ)) * birthdayRate N q := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hqN : q ≤ N := by omega
  have hfactor0 (k : Nat) (hk : k ∈ Finset.range q) :
      0 ≤ (k : ℝ) / (N : ℝ) := by positivity
  have hfactorHalf (k : Nat) (hk : k ∈ Finset.range q) :
      (k : ℝ) / (N : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hNR]
    have hkq : k < q := Finset.mem_range.mp hk
    have hcast : (2 * k : ℝ) ≤ N := by
      exact_mod_cast (Nat.mul_le_mul_left 2 hkq.le |>.trans h2q)
    linarith
  have hfactorPos (k : Nat) (hk : k ∈ Finset.range q) :
      0 < 1 - (k : ℝ) / (N : ℝ) := by
    linarith [hfactorHalf k hk]
  rw [birthdayProduct, Real.log_prod
    (fun k hk => (hfactorPos k hk).ne')]
  nth_rewrite 1 [birthdayRate_eq_sum hN]
  rw [← Finset.sum_add_distrib]
  calc
    |∑ k ∈ Finset.range q,
        (Real.log (1 - (k : ℝ) / (N : ℝ)) +
          (k : ℝ) / (N : ℝ))| ≤
        ∑ k ∈ Finset.range q,
          |Real.log (1 - (k : ℝ) / (N : ℝ)) +
            (k : ℝ) / (N : ℝ)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range q,
          2 * ((k : ℝ) / (N : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_log_one_sub_add_le_two_sq
        (hfactorHalf k hk)
    _ ≤ ∑ k ∈ Finset.range q,
          2 * ((q : ℝ) / (N : ℝ)) *
            ((k : ℝ) / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkq : (k : ℝ) ≤ q := by
        exact_mod_cast (Finset.mem_range.mp hk).le
      have hkdiv : (k : ℝ) / (N : ℝ) ≤
          (q : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right hkq hNR.le
      have hk0 := hfactor0 k hk
      nlinarith
    _ = 2 * ((q : ℝ) / (N : ℝ)) * birthdayRate N q := by
      rw [birthdayRate_eq_sum hN, Finset.mul_sum]

/-- Elementary Poisson limit for the zero-collision atom. -/
theorem tendsto_birthdayProduct_exp_neg
    (N q : ℕ → ℕ) (r : ℝ)
    (hN : Tendsto N atTop atTop)
    (h2q : ∀ᶠ k in atTop, 2 * q k ≤ N k)
    (hrate : Tendsto (fun k => birthdayRate (N k) (q k))
      atTop (nhds r))
    (hsmall : Tendsto
      (fun k => (q k : ℝ) / (N k : ℝ)) atTop (nhds 0)) :
    Tendsto (fun k => birthdayProduct (N k) (q k))
      atTop (nhds (Real.exp (-r))) := by
  have hNpos : ∀ᶠ k in atTop, 0 < N k := by
    have hge : ∀ᶠ k in atTop, 1 ≤ N k :=
      hN (eventually_ge_atTop 1)
    filter_upwards [hge] with k hk
    omega
  have hbound : Tendsto
      (fun k => 2 * ((q k : ℝ) / (N k : ℝ)) *
        birthdayRate (N k) (q k)) atTop (nhds 0) := by
    have htwo : Tendsto (fun _k : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    convert (htwo.mul hsmall).mul hrate using 1
    ring
  have habsError : Tendsto
      (fun k =>
        |Real.log (birthdayProduct (N k) (q k)) +
          birthdayRate (N k) (q k)|) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun k => abs_nonneg _)
    · filter_upwards [hNpos, h2q] with k hNk h2qk
      exact abs_log_birthdayProduct_add_rate_le hNk h2qk
    · exact hbound
  have herror : Tendsto
      (fun k => Real.log (birthdayProduct (N k) (q k)) +
        birthdayRate (N k) (q k)) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using habsError
  have hlog : Tendsto
      (fun k => Real.log (birthdayProduct (N k) (q k)))
      atTop (nhds (-r)) := by
    simpa only [add_sub_cancel_right, zero_sub] using herror.sub hrate
  have hexp : Tendsto
      (fun k => Real.exp (Real.log (birthdayProduct (N k) (q k))))
      atTop (nhds (Real.exp (-r))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlog
  apply hexp.congr'
  filter_upwards [hNpos, h2q] with k hNk h2qk
  apply Real.exp_log
  unfold birthdayProduct
  apply Finset.prod_pos
  intro i hi
  have hiq : i < q k := Finset.mem_range.mp hi
  have hiN : (i : ℝ) < N k := by
    exact_mod_cast (lt_of_lt_of_le hiq (by omega : q k ≤ N k))
  have hNR : (0 : ℝ) < N k := by exact_mod_cast hNk
  rw [sub_pos, div_lt_one hNR]
  exact hiN

/-- The unnormalized mean absolute deviation of the finite collision count. -/
def finiteCollisionMAD (N q : Nat) : ℝ :=
  uniformAverage (Fin q → Fin N)
    (fun y => |centeredCollisionCount (Fin N) q y|)

/-- Poisson mean absolute deviation at a rate below one.  In this range the
general formula `2*r*Pr[Poisson(r)=floor r]` reduces to `2*r*exp(-r)`. -/
def subunitPoissonMAD (r : ℝ) : ℝ :=
  2 * r * Real.exp (-r)

/-- The collision-proxy advantage, separated from the heavier SoP model. -/
def finiteCollisionProxyAdvantage (N q : Nat) : ℝ :=
  (N : ℝ) / (2 * ((N - 1 : Nat) : ℝ) ^ 2) *
    finiteCollisionMAD N q

def finiteSparseLeading (N q : Nat) : ℝ :=
  (edgeCount q : ℝ) / ((N - 1 : Nat) : ℝ) ^ 2

/-- Natural dense scale of the collision proxy. -/
def finiteCollisionDenseScale (N q : Nat) : ℝ :=
  (N : ℝ) / (2 * ((N - 1 : Nat) : ℝ) ^ 2) *
    collisionSigma (Fin N) q

theorem finiteCollisionDenseScale_eq_closed
    {N q : Nat} (hN : 2 ≤ N) :
    finiteCollisionDenseScale N q =
      Real.sqrt (edgeCount q : ℝ) /
        (2 * ((N - 1 : Nat) : ℝ) *
          Real.sqrt ((N - 1 : Nat) : ℝ)) := by
  let n : ℝ := N
  let A : ℝ := (N - 1 : Nat)
  let M : ℝ := edgeCount q
  have hn : 0 < n := by dsimp [n]; positivity
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast Nat.sub_pos_of_lt hN
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hsqrtA : Real.sqrt A ≠ 0 := Real.sqrt_ne_zero'.2 hA
  have hsqrt : Real.sqrt (M * A / n ^ 2) =
      Real.sqrt M * Real.sqrt A / n := by
    rw [Real.sqrt_div (mul_nonneg hM hA.le),
      Real.sqrt_mul hM, Real.sqrt_sq_eq_abs, abs_of_pos hn]
  unfold finiteCollisionDenseScale collisionSigma collisionVariance
  simp only [Fintype.card_fin]
  change n / (2 * A ^ 2) * Real.sqrt (M * A / n ^ 2) =
    Real.sqrt M / (2 * A * Real.sqrt A)
  rw [hsqrt]
  have hsquare : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA.le
  field_simp [hn.ne', hA.ne', hsqrtA]
  rw [hsquare]
  ring

/-- Exact finite normal target for the collision proxy. -/
def finiteNormalProxyTarget (N q : Nat) : ℝ :=
  finiteCollisionDenseScale N q * normalAbsConstant

theorem finiteNormalProxyTarget_eq_closed
    {N q : Nat} (hN : 2 ≤ N) :
    finiteNormalProxyTarget N q =
      Real.sqrt (edgeCount q : ℝ) * Real.sqrt (2 / Real.pi) /
        (2 * ((N - 1 : Nat) : ℝ) *
          Real.sqrt ((N - 1 : Nat) : ℝ)) := by
  unfold finiteNormalProxyTarget normalAbsConstant
  rw [finiteCollisionDenseScale_eq_closed hN]
  ring

theorem finiteCollisionMAD_eq_sigma_mul_standardizedMAD
    {N q : Nat} (hN : 2 ≤ N) (hq : 2 ≤ q) :
    finiteCollisionMAD N q =
      collisionSigma (Fin N) q *
        uniformAverage (Fin q → Fin N) (fun y =>
          |standardizedCollisionCount (Fin N) q y|) := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  have hs : 0 < collisionSigma (Fin N) q :=
    collisionSigma_pos (Fin N) hq (by simpa using hN)
  unfold finiteCollisionMAD
  rw [show (fun y : Fin q → Fin N =>
      |centeredCollisionCount (Fin N) q y|) =
      (fun y => collisionSigma (Fin N) q *
        |standardizedCollisionCount (Fin N) q y|) by
      funext y
      unfold standardizedCollisionCount
      rw [abs_div, abs_of_pos hs]
      field_simp [hs.ne']]
  exact uniformAverage_const_mul _ _

theorem finiteCollisionProxyAdvantage_eq_denseScale_mul_standardizedMAD
    {N q : Nat} (hN : 2 ≤ N) (hq : 2 ≤ q) :
    finiteCollisionProxyAdvantage N q =
      finiteCollisionDenseScale N q *
        uniformAverage (Fin q → Fin N) (fun y =>
          |standardizedCollisionCount (Fin N) q y|) := by
  unfold finiteCollisionProxyAdvantage finiteCollisionDenseScale
  rw [finiteCollisionMAD_eq_sigma_mul_standardizedMAD hN hq]
  ring

/-- Fully explicit finite transfer from the collision proxy to its sharp
normal target. -/
theorem abs_finiteCollisionProxyAdvantage_sub_normalTarget_le
    {N q : Nat} (hN : 2 ≤ N) (hq : 2 ≤ q) :
    |finiteCollisionProxyAdvantage N q - finiteNormalProxyTarget N q| ≤
      finiteCollisionDenseScale N q *
        collisionNormalErrorBound (Fin N) q := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  have hscale : 0 ≤ finiteCollisionDenseScale N q := by
    unfold finiteCollisionDenseScale collisionSigma
    exact mul_nonneg
      (div_nonneg (by positivity)
        (mul_nonneg (by norm_num) (sq_nonneg _)))
      (Real.sqrt_nonneg _)
  rw [finiteCollisionProxyAdvantage_eq_denseScale_mul_standardizedMAD
    hN hq]
  unfold finiteNormalProxyTarget
  rw [← mul_sub, abs_mul, abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_left
    (standardizedCollisionMAD_sub_normal_le_errorBound
      (Fin N) hq (by simpa using hN)) hscale

/-- Exact sparse/birthday formula for the collision proxy.  It is the leading
term `choose(q,2)/(N-1)^2` multiplied by the exact no-collision probability. -/
theorem finiteCollisionProxyAdvantage_eq_birthday_main
    {N q : Nat} (hN : 2 ≤ N) (hrate : birthdayRate N q ≤ 1) :
    finiteCollisionProxyAdvantage N q =
      (edgeCount q : ℝ) / ((N - 1 : Nat) : ℝ) ^ 2 *
        birthdayProduct N q := by
  letI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (by omega)
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hm : collisionMean (Fin N) q ≤ 1 := by
    simpa [collisionMean, birthdayRate] using hrate
  unfold finiteCollisionProxyAdvantage finiteCollisionMAD
  rw [collisionMAD_eq_two_mul_mean_mul_collisionFree (Fin N) hm]
  rw [collisionFreeProbability_eq_birthdayProduct]
  simp only [Fintype.card_fin]
  unfold collisionMean
  simp only [Fintype.card_fin]
  field_simp [hNR]

/-- Sharp low-query asymptotic: when the birthday rate tends to zero, the
collision proxy is asymptotic to `choose(q,2)/(N-1)^2`. -/
theorem tendsto_finiteCollisionProxyAdvantage_div_sparseLeading
    (N q : ℕ → ℕ)
    (hq : ∀ᶠ k in atTop, 2 ≤ q k)
    (hN : Tendsto N atTop atTop)
    (h2q : ∀ᶠ k in atTop, 2 * q k ≤ N k)
    (hrate : Tendsto (fun k => birthdayRate (N k) (q k))
      atTop (nhds 0))
    (hsmall : Tendsto
      (fun k => (q k : ℝ) / (N k : ℝ)) atTop (nhds 0)) :
    Tendsto
      (fun k => finiteCollisionProxyAdvantage (N k) (q k) /
        finiteSparseLeading (N k) (q k))
      atTop (nhds 1) := by
  have hproduct : Tendsto (fun k => birthdayProduct (N k) (q k))
      atTop (nhds 1) := by
    simpa using tendsto_birthdayProduct_exp_neg N q 0 hN h2q hrate hsmall
  have hNtwo : ∀ᶠ k in atTop, 2 ≤ N k :=
    hN (eventually_ge_atTop 2)
  have hrateOne : ∀ᶠ k in atTop, birthdayRate (N k) (q k) ≤ 1 := by
    have hlt : ∀ᶠ k in atTop, birthdayRate (N k) (q k) < 1 :=
      hrate (Iio_mem_nhds zero_lt_one)
    exact hlt.mono (fun _ hk => hk.le)
  apply hproduct.congr'
  filter_upwards [hq, hNtwo, hrateOne] with k hqk hNk hrk
  have hlead : finiteSparseLeading (N k) (q k) ≠ 0 := by
    unfold finiteSparseLeading
    have hM : (edgeCount (q k) : ℝ) ≠ 0 := by
      exact_mod_cast (edgeCount_pos hqk).ne'
    have hNm1 : ((N k - 1 : Nat) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.sub_ne_zero_of_lt hNk
    exact div_ne_zero hM (pow_ne_zero _ hNm1)
  rw [finiteCollisionProxyAdvantage_eq_birthday_main hNk hrk]
  change birthdayProduct (N k) (q k) =
    (finiteSparseLeading (N k) (q k) * birthdayProduct (N k) (q k)) /
      finiteSparseLeading (N k) (q k)
  field_simp [hlead]

/-- Birthday-scale Poisson MAD convergence for every limiting rate strictly
below one.  In particular this includes the central crossover `q ~ sqrt N`,
whose rate is `1/2`. -/
theorem tendsto_finiteCollisionMAD_subunitPoisson
    (N q : ℕ → ℕ) (r : ℝ)
    (hN : Tendsto N atTop atTop)
    (h2q : ∀ᶠ k in atTop, 2 * q k ≤ N k)
    (hrate : Tendsto (fun k => birthdayRate (N k) (q k))
      atTop (nhds r))
    (hsmall : Tendsto
      (fun k => (q k : ℝ) / (N k : ℝ)) atTop (nhds 0))
    (hr1 : r < 1) :
    Tendsto (fun k => finiteCollisionMAD (N k) (q k))
      atTop (nhds (subunitPoissonMAD r)) := by
  have hNpos : ∀ᶠ k in atTop, 0 < N k := by
    have hge : ∀ᶠ k in atTop, 1 ≤ N k :=
      hN (eventually_ge_atTop 1)
    filter_upwards [hge] with k hk
    omega
  have hrateOne : ∀ᶠ k in atTop, birthdayRate (N k) (q k) ≤ 1 := by
    have hlt : ∀ᶠ k in atTop, birthdayRate (N k) (q k) < 1 :=
      hrate (Iio_mem_nhds hr1)
    exact hlt.mono (fun _ hk => hk.le)
  have hproduct := tendsto_birthdayProduct_exp_neg
    N q r hN h2q hrate hsmall
  have htarget : Tendsto
      (fun k => 2 * birthdayRate (N k) (q k) *
        birthdayProduct (N k) (q k))
      atTop (nhds (subunitPoissonMAD r)) := by
    unfold subunitPoissonMAD
    have htwo : Tendsto (fun _k : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    exact (htwo.mul hrate).mul hproduct
  apply htarget.congr'
  filter_upwards [hNpos, hrateOne] with k hNk hrk
  letI : Nonempty (Fin (N k)) :=
    Fin.pos_iff_nonempty.mp hNk
  unfold finiteCollisionMAD
  rw [collisionMAD_eq_two_mul_mean_mul_collisionFree
    (Fin (N k)) (by simpa [collisionMean, birthdayRate] using hrk)]
  rw [collisionFreeProbability_eq_birthdayProduct]
  simp only [Fintype.card_fin]
  unfold collisionMean birthdayRate
  simp only [Fintype.card_fin]

/-- The collision proxy divided by its exact dense scale converges to the
standard-normal MAD.  Multiplying back by the closed dense scale is the sharp
`1 / (2*sqrt pi)` SoP leading constant. -/
theorem tendsto_finiteCollisionProxyAdvantage_div_denseScale
    (N q : ℕ → ℕ)
    (hq : ∀ᶠ k in atTop, 2 ≤ q k)
    (hN : ∀ᶠ k in atTop, 2 ≤ N k)
    (hcard : Tendsto N atTop atTop)
    (hsigma : Tendsto
      (fun k => collisionSigma (Fin (N k)) (q k)) atTop atTop) :
    Tendsto
      (fun k => finiteCollisionProxyAdvantage (N k) (q k) /
        finiteCollisionDenseScale (N k) (q k))
      atTop (nhds normalAbsConstant) := by
  have hnormal :=
    tendsto_standardizedCollisionMAD_fin_of_card_and_sigma
      N q hq hN hcard hsigma
  apply hnormal.congr'
  filter_upwards [hq, hN] with k hqk hNk
  letI : Nonempty (Fin (N k)) := Fin.pos_iff_nonempty.mp (by omega)
  have hs : collisionSigma (Fin (N k)) (q k) ≠ 0 :=
    (collisionSigma_pos (Fin (N k)) hqk (by simpa using hNk)).ne'
  have hNm1 : ((N k - 1 : Nat) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_ne_zero_of_lt hNk)
  have hscale : finiteCollisionDenseScale (N k) (q k) ≠ 0 := by
    unfold finiteCollisionDenseScale
    positivity
  rw [finiteCollisionProxyAdvantage_eq_denseScale_mul_standardizedMAD
    hNk hqk]
  field_simp [hscale]

end RandomSystems.SoP.CollisionCountPoisson
