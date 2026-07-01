/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Applications.SoP.Basic
import Mathlib.Tactic

/-!
# SoP Fixed-Input Transcript Objects

This file gives SoP-specific names to the exact visible-output masses used by
the transcript-counting proof.  It deliberately reuses the XoP-compatible count
infrastructure instead of defining another counting layer.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace SoP

variable {G : Type*} {q : Nat}

/-- Denominator for the real SoP visible-output law: the number of pairs of
injective hidden tuples, `(N)_q^2`. -/
def realVisibleDenominator [Fintype G] (q : Nat) : NNReal :=
  (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
    NNReal)

/-- Exact real visible-output mass for a fixed tuple `y`.

This is `Z(y) / (N)_q^2`, where `Z(y)` is the compatible hidden-state count. -/
def realVisibleMass [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) : NNReal :=
  compatibleCountNNReal y / realVisibleDenominator (G := G) q

/-- Exact ideal visible-output mass for a fixed tuple `y`, written as the
repository's uniform finite distribution. -/
def idealVisibleMass [Fintype G] [Nonempty G] (y : Fin q → G) : NNReal :=
  Dist.uniform (Fin q → G) y

/-- The expectation normalizer `E_I[Z] = (N)_q^2 / N^q`, packaged in the same
form as the existing XoP counting bridge. -/
def expectationNormalizer [AddGroup G] [Fintype G] (hq : q ≤ Fintype.card G) :
    XoP.Counting.FallingFactorialNormalizer G q :=
  compatibleExpectationNormalizer (G := G) (q := q) hq

/-- Visible density ratio `Z(y) / E_I[Z]`. -/
def visibleDensityRatio [AddGroup G] [Fintype G] [DecidableEq G]
    (hq : q ≤ Fintype.card G) (y : Fin q → G) : NNReal :=
  compatibleCountNNReal y / (expectationNormalizer (G := G) (q := q) hq).value

/-- Real visible mass written as `Z(y) / (N)_q^2`. -/
theorem realVisibleMass_eq [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) y =
      compatibleCountNNReal y /
        (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          NNReal) := by
  rfl

/-- The expectation normalizer has the intended closed form. -/
theorem expectationNormalizer_value [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) :
    (expectationNormalizer (G := G) (q := q) hq).value =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          NNReal) /
        ((Fintype.card G ^ q : Nat) : NNReal) :=
  XoP.Combinatorics.compatibleCountWithExpectationNormalizer_normalizer
    (G := G) (q := q) hq

/-- Ideal visible mass written as `1 / N^q`. -/
theorem idealVisibleMass_eq [Fintype G] [Nonempty G] (y : Fin q → G) :
    idealVisibleMass (G := G) (q := q) y =
      1 / ((Fintype.card G ^ q : Nat) : NNReal) := by
  simp [idealVisibleMass, Dist.uniform_apply]

/-- Visible density identity: real mass is density ratio times ideal mass. -/
theorem realVisibleMass_eq_densityRatio_mul_ideal [AddGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (hq : q ≤ Fintype.card G) (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) y =
      visibleDensityRatio (G := G) (q := q) hq y *
        idealVisibleMass (G := G) (q := q) y := by
  have hpow : (((Fintype.card G ^ q : Nat) : NNReal)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero q (Nat.ne_of_gt Fintype.card_pos))
  simp [realVisibleMass, realVisibleDenominator, visibleDensityRatio, expectationNormalizer_value,
    idealVisibleMass, Dist.uniform_apply]
  rw [div_div_eq_mul_div]
  field_simp [hpow]

end SoP
end Applications
end RandomSystems
