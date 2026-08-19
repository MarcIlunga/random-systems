/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.Counting
import RandomSystems.CompatibleCount
import RandomSystems.DistSimp
import RandomSystems.StatDist

/-!
# Migrated SoP visible law

This module ports the fixed visible-output law from the old
`RandomSystems.Applications.SoP.Transcript` / `TV` layer to the `RandomSystems`
H-technique migration surface.

Source status:

* source theorem object: compatible hidden-state counts for a fixed visible
  output tuple;
* source theorem object: real and ideal visible-output masses;
* support lemma forced by formalization: expose those mass functions as
  `RandomSystems.Dist`s via the generic finite-mass adapter.

The compatible hidden-state counting core is owned by the dependency-light
shared module `RandomSystems.CompatibleCount`; this file aliases it under the
migration names and builds the visible-output laws on top.  The anti-drift
pins in `LegacyVisibleEquiv` certify that the aliased layer coincides with the
legacy `RandomSystems.Applications.SoP` objects.

This file deliberately does not import the old `RandomSystems.Applications.SoP`
modules.  The next layer connects these visible laws to concrete
`PFunPDE.transcriptLaw` instances.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace HTechnique
namespace SoP

attribute [local instance] Classical.propDecidable

export RandomSystems.CompatibleCount (
  InjectiveTuple
  injectiveTupleCount
  injectiveTupleCount_descFactorial
  InjectiveTupleSubtype
  injectiveTupleSubtype_card
  shifted
  CompatibleHiddenState
  CompatiblePair
  compatiblePairEquivInjectiveProduct
  compatiblePairEquivSigma
  compatiblePair_card
  compatibleCountNat
  compatibleCountNat_eq_card_filter
  compatibleCountNat_lower_bound
  compatibleFiber_card
  sum_compatibleCountNat_eq_compatiblePair_card
  sum_compatibleCountNat_eq_injectiveTupleCount_sq
  sum_compatibleCountNat_eq_descFactorial_sq
  compatibleCountNNReal
  compatibleCountNNReal_eq_coe_nat
  sum_compatibleCountNNReal_eq_descFactorial_sq)

variable {G : Type*} {q : Nat}

/-- **Source theorem object.** Denominator for the real SoP visible-output law:
the number of pairs of injective hidden tuples, `(N)_q^2`. -/
def realVisibleDenominator [Fintype G] (q : Nat) : NNReal :=
  (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
    NNReal)

/-- **Source theorem object.** Exact real visible-output mass for a fixed tuple
`y`: `Z(y) / (N)_q^2`. -/
def realVisibleMass [AddGroup G] [Fintype G] (y : Fin q → G) : NNReal :=
  compatibleCountNNReal y / realVisibleDenominator (G := G) q

/-- **Source theorem object.** Exact ideal visible-output mass for a fixed tuple,
written as the uniform finite distribution.

The `Dist` carrier is the signed reals, so the uniform law's value is packaged
with `Dist.uniform_nonNeg` to land in the counting layer's `NNReal`. -/
def idealVisibleMass [Fintype G] [Nonempty G] (y : Fin q → G) : NNReal :=
  ⟨RandomSystems.Dist.uniform (Fin q → G) y, RandomSystems.Dist.uniform_nonNeg y⟩

/-- **Source theorem object.** Real visible mass in closed numerator/denominator
form. -/
theorem realVisibleMass_eq [AddGroup G] [Fintype G] (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) y =
      compatibleCountNNReal y /
        (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          NNReal) := by
  rfl

/-- **Source theorem object.** Ideal visible mass in closed form, `1 / N^q`. -/
theorem idealVisibleMass_eq [Fintype G] [Nonempty G] (y : Fin q → G) :
    idealVisibleMass (G := G) (q := q) y =
      1 / ((Fintype.card G ^ q : Nat) : NNReal) := by
  apply NNReal.coe_injective
  simp [idealVisibleMass, RandomSystems.Dist.uniform_apply]

/-- **Source theorem object.** The expectation normalizer `E_I[Z] =
((N)_q)^2 / N^q`.  The `q <= N` assumption is kept at the use sites that need
nonzero denominators. -/
def expectationNormalizer [Fintype G] (q : Nat) : NNReal :=
  realVisibleDenominator (G := G) q / ((Fintype.card G ^ q : Nat) : NNReal)

/-- **Source theorem object.** Visible density ratio `Z(y) / E_I[Z]`. -/
def visibleDensityRatio [AddGroup G] [Fintype G] (y : Fin q → G) : NNReal :=
  compatibleCountNNReal y / expectationNormalizer (G := G) q

/-- **Source theorem bridge.** Visible density identity: real mass is density
ratio times ideal mass. -/
theorem realVisibleMass_eq_densityRatio_mul_ideal [AddGroup G] [Fintype G]
    [Nonempty G] (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) y =
      visibleDensityRatio (G := G) (q := q) y *
        idealVisibleMass (G := G) (q := q) y := by
  have hpow : (((Fintype.card G ^ q : Nat) : NNReal)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero q (Nat.ne_of_gt Fintype.card_pos))
  have hdesc_pos : 0 < (Fintype.card G).descFactorial q :=
    Nat.descFactorial_pos.mpr hq
  have hden : realVisibleDenominator (G := G) q ≠ 0 := by
    unfold realVisibleDenominator
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hdesc_pos) (Nat.ne_of_gt hdesc_pos))
  rw [idealVisibleMass_eq]
  simp [realVisibleMass, realVisibleDenominator, visibleDensityRatio, expectationNormalizer]
  rw [div_div_eq_mul_div]
  field_simp [hpow, hden]

/-- **Source theorem bridge.** Pointwise visible-law ratio bound for SoP:
under the paper's cubic query condition, every visible output has real mass at
least `(1 - q^3 / |G|^2)` times its ideal mass. -/
theorem realVisibleMass_lower_bound [AddGroup G] [Fintype G] [Nonempty G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) (y : Fin q → G) :
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
        idealVisibleMass (G := G) (q := q) y ≤
      realVisibleMass (G := G) (q := q) y := by
  have h_pos : 0 < Fintype.card G := Fintype.card_pos
  calc
    (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
        idealVisibleMass (G := G) (q := q) y
        = (1 - (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2) *
            (1 / ((Fintype.card G : NNReal) ^ q)) := by
          rw [idealVisibleMass_eq]
          norm_num [Nat.cast_pow]
    _ ≤ ((((((Fintype.card G - q).factorial) ^ 2 *
            ∏ k ∈ Finset.range q, (Fintype.card G - 2 * k)) : Nat) : NNReal) /
          (((Fintype.card G).factorial : NNReal) ^ 2)) :=
          Counting.sop_ratio_counting_bound
            (size := Fintype.card G) (q := q) h_pos h_bound
    _ ≤ realVisibleMass (G := G) (q := q) y := by
          have hq_le : q ≤ Fintype.card G :=
            RandomSystems.CR18.Counting.q_le_of_cube_le_sq h_bound
          have h_count :
              ((∏ k ∈ Finset.range q, (Fintype.card G - 2 * k) : Nat) : NNReal) ≤
                compatibleCountNNReal (G := G) (q := q) y := by
            rw [compatibleCountNNReal_eq_coe_nat]
            exact_mod_cast compatibleCountNat_lower_bound (G := G) (q := q) y
          have hfact_nat :
              (Fintype.card G - q).factorial * (Fintype.card G).descFactorial q =
                (Fintype.card G).factorial :=
            Nat.factorial_mul_descFactorial hq_le
          have hfact :
              (((Fintype.card G - q).factorial : Nat) : NNReal) *
                  (((Fintype.card G).descFactorial q : Nat) : NNReal) =
                (((Fintype.card G).factorial : Nat) : NNReal) := by
            exact_mod_cast hfact_nat
          have hfac_ne : (((Fintype.card G - q).factorial : Nat) : NNReal) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero (Fintype.card G - q)
          have hdesc_pos : 0 < (Fintype.card G).descFactorial q :=
            Nat.descFactorial_pos.mpr hq_le
          have hdesc_ne : (((Fintype.card G).descFactorial q : Nat) : NNReal) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt hdesc_pos
          calc
            ((((((Fintype.card G - q).factorial) ^ 2 *
                    ∏ k ∈ Finset.range q, (Fintype.card G - 2 * k)) : Nat) : NNReal) /
                (((Fintype.card G).factorial : NNReal) ^ 2))
                = ((∏ k ∈ Finset.range q, (Fintype.card G - 2 * k) : Nat) : NNReal) /
                    ((((Fintype.card G).descFactorial q : Nat) : NNReal) ^ 2) := by
                  norm_num [Nat.cast_mul, Nat.cast_pow]
                  rw [← hfact]
                  field_simp [hfac_ne, hdesc_ne]
            _ ≤ compatibleCountNNReal (G := G) (q := q) y /
                ((((Fintype.card G).descFactorial q : Nat) : NNReal) ^ 2) := by
                  exact div_le_div_of_nonneg_right h_count (by positivity)
            _ = realVisibleMass (G := G) (q := q) y := by
                  rw [realVisibleMass_eq]
                  norm_num [Nat.cast_mul, pow_two]

/-- **Support lemma forced by formalization.** Real visible-output distribution
as a finite distribution. -/
abbrev realVisibleDist [AddGroup G] [Fintype G] :
    RandomSystems.Dist (Fin q → G) :=
  RandomSystems.Dist.ofFiniteMassFunction
    (fun y : Fin q → G => (realVisibleMass (G := G) (q := q) y : ℝ))

/-- **Support lemma forced by formalization.** Ideal visible-output distribution
as a finite distribution. -/
abbrev idealVisibleDist [Fintype G] [Nonempty G] :
    RandomSystems.Dist (Fin q → G) :=
  RandomSystems.Dist.ofFiniteMassFunction
    (fun y : Fin q → G => (idealVisibleMass (G := G) (q := q) y : ℝ))

@[simp]
theorem realVisibleDist_apply [AddGroup G] [Fintype G] (y : Fin q → G) :
    realVisibleDist (G := G) (q := q) y =
      realVisibleMass (G := G) (q := q) y := by
  simp [realVisibleDist]

@[simp]
theorem idealVisibleDist_apply [Fintype G] [Nonempty G] (y : Fin q → G) :
    idealVisibleDist (G := G) (q := q) y =
      idealVisibleMass (G := G) (q := q) y := by
  simp [idealVisibleDist]

/-- **Support lemma forced by formalization.** The real visible law has total
mass one when `(N)_q` is nonzero, i.e. `q <= N`. -/
theorem realVisibleDist_weight [AddGroup G] [Fintype G] (hq : q ≤ Fintype.card G) :
    (realVisibleDist (G := G) (q := q)).weight = 1 := by
  have hdesc_pos : 0 < (Fintype.card G).descFactorial q :=
    Nat.descFactorial_pos.mpr hq
  have hden : realVisibleDenominator (G := G) q ≠ 0 := by
    unfold realVisibleDenominator
    exact_mod_cast (Nat.mul_ne_zero (Nat.ne_of_gt hdesc_pos) (Nat.ne_of_gt hdesc_pos))
  have hsum : (∑ y : Fin q → G, realVisibleMass (G := G) (q := q) y) = 1 := by
    calc
      (∑ y : Fin q → G, realVisibleMass (G := G) (q := q) y)
          = (∑ y : Fin q → G, compatibleCountNNReal (G := G) (q := q) y) /
              realVisibleDenominator (G := G) q := by
                simp [realVisibleMass, Finset.sum_div]
      _ = realVisibleDenominator (G := G) q / realVisibleDenominator (G := G) q := by
                rw [sum_compatibleCountNNReal_eq_descFactorial_sq]
                rfl
      _ = 1 := div_self hden
  calc
    (realVisibleDist (G := G) (q := q)).weight
        = ∑ y : Fin q → G, ((realVisibleMass (G := G) (q := q) y : NNReal) : ℝ) := by
            simp [realVisibleDist, RandomSystems.Dist.weight_ofFiniteMassFunction]
    _ = ((∑ y : Fin q → G, realVisibleMass (G := G) (q := q) y : NNReal) : ℝ) :=
            (NNReal.coe_sum _ _).symm
    _ = 1 := by rw [hsum, NNReal.coe_one]

/-- **Support lemma forced by formalization.** The ideal visible law has total
mass one. -/
theorem idealVisibleDist_weight [Fintype G] [Nonempty G] :
    (idealVisibleDist (G := G) (q := q)).weight = 1 := by
  have hdist :
      idealVisibleDist (G := G) (q := q) =
        RandomSystems.Dist.uniform (Fin q → G) := by
    ext y
    simp [idealVisibleDist, idealVisibleMass]
  rw [hdist]
  simp only [dist_simp]

/-- **Support lemma forced by formalization.** The real and ideal visible laws
have equal total mass. -/
theorem realVisibleDist_weight_eq_ideal [AddGroup G] [Fintype G] [Nonempty G]
    (hq : q ≤ Fintype.card G) :
    (realVisibleDist (G := G) (q := q)).weight =
      (idealVisibleDist (G := G) (q := q)).weight := by
  rw [realVisibleDist_weight (G := G) (q := q) hq, idealVisibleDist_weight]

/-- **Source theorem object.** Exact visible-output statistical distance for the
SoP fixed transcript law. -/
def visibleStatDist [AddGroup G] [Fintype G] [Nonempty G] : NNReal :=
  ⟨RandomSystems.statDist (realVisibleDist (G := G) (q := q))
      (idealVisibleDist (G := G) (q := q)),
    RandomSystems.statDist_nonneg _ _⟩

/-- **Source theorem object.** Expanded `statDist` formula for the exact visible
laws.  The `max (· - ·) 0` on the right is what the `NNReal` truncated
subtraction of the counting layer denotes on the signed carrier. -/
theorem visibleStatDist_eq_sum [AddGroup G] [Fintype G] [Nonempty G] :
    (visibleStatDist (G := G) (q := q) : ℝ) =
      ∑ y : Fin q → G,
        max ((realVisibleMass (G := G) (q := q) y : ℝ) -
          (idealVisibleMass (G := G) (q := q) y : ℝ)) 0 := by
  simp [visibleStatDist, RandomSystems.statDist_eq_sum_univ]

end SoP
end HTechnique
end RandomSystems
