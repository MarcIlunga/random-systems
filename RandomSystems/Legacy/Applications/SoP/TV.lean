/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Applications.SoP.Transcript

/-!
# SoP Visible Statistical Distance

This file packages the exact visible-output real and ideal laws as
`RandomSystems.Dist`s, then states their statistical distance using the
repository's `statDist` convention:

`δ(X,Y) = ∑ y, (X y - Y y)`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace SoP

variable {G : Type*} {q : Nat}

/-- Real visible-output distribution induced by the compatible hidden-state
count. -/
def realVisibleDist [AddGroup G] [Fintype G] [DecidableEq G] :
    Dist (Fin q → G) :=
  Finsupp.equivFunOnFinite.invFun
    (fun y : Fin q → G => realVisibleMass (G := G) (q := q) y)

/-- Ideal visible-output distribution, uniform over output tuples. -/
def idealVisibleDist [Fintype G] [Nonempty G] :
    Dist (Fin q → G) :=
  Dist.uniform (Fin q → G)

/-- Exact visible-output statistical distance for the SoP transcript law. -/
def visibleStatDist [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] :
    NNReal :=
  ⟨statDist (realVisibleDist (G := G) (q := q))
      (idealVisibleDist (G := G) (q := q)),
    statDist_nonneg _ _⟩

/-- Pointwise evaluation of the real visible distribution. -/
theorem realVisibleDist_apply [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) :
    realVisibleDist (G := G) (q := q) y =
      realVisibleMass (G := G) (q := q) y := by
  simp [realVisibleDist, Finsupp.equivFunOnFinite]

/-- Pointwise evaluation of the ideal visible distribution. -/
theorem idealVisibleDist_apply [Fintype G] [Nonempty G] (y : Fin q → G) :
    idealVisibleDist (G := G) (q := q) y =
      idealVisibleMass (G := G) (q := q) y := by
  rfl

/-- Expanded `statDist` formula for the exact visible laws. -/
theorem visibleStatDist_eq_sum [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G] :
    (visibleStatDist (G := G) (q := q) : ℝ) =
      ∑ y : Fin q → G,
        max ((realVisibleMass (G := G) (q := q) y : ℝ) -
          (idealVisibleMass (G := G) (q := q) y : ℝ)) 0 := by
  simp [visibleStatDist, statDist_eq_sum_univ, realVisibleDist_apply,
    idealVisibleDist_apply]

end SoP
end Applications
end RandomSystems
