/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.SoP.VisibleLaw
import RandomSystems.Legacy.Applications.SoP.TV

/-!
# Anti-drift equivalences: migrated SoP visible law vs legacy SoP `Transcript`/`TV`

This module is compatibility-only.  It pins the semantics of the migrated SoP
visible-output layer to the legacy `RandomSystems.Applications.SoP` objects
before any legacy code is deprecated or the duplicated counting layer is
extracted: the migrated visible masses, visible distributions, and visible
statistical distance are proved *equal* to their legacy counterparts, so the
normalized presentation cannot drift from the existing application semantics.

These are regression pins, not new mathematics.  When the shared
compatible-count core is extracted (migration plan P4.7), these theorems keep
holding by construction; if a refactor breaks one of them, the refactor changed
the mathematics.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace HTechnique
namespace SoP

attribute [local instance] Classical.propDecidable

variable {G : Type*} {q : Nat}

/-- Anti-drift pin: the migrated hidden-state compatibility predicate is the
legacy XoP one. -/
theorem compatibleHiddenState_iff_legacy [AddGroup G] (y a : Fin q → G) :
    CompatibleHiddenState y a ↔
      RandomSystems.Applications.XoP.Combinatorics.CompatibleHiddenState y a :=
  Iff.rfl

/-- Anti-drift pin: the migrated compatible hidden-state count agrees with the
legacy SoP/XoP count. -/
theorem compatibleCountNat_eq_legacy [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) :
    compatibleCountNat (G := G) (q := q) y =
      RandomSystems.Applications.SoP.compatibleCountNat (G := G) (q := q) y := by
  rfl

/-- Anti-drift pin: `NNReal` form of the compatible-count agreement. -/
theorem compatibleCountNNReal_eq_legacy [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) :
    compatibleCountNNReal (G := G) (q := q) y =
      RandomSystems.Applications.SoP.compatibleCountNNReal (G := G) (q := q) y := by
  rfl

/-- Anti-drift pin: the migrated real visible-output mass agrees with the
legacy `RandomSystems.Applications.SoP.realVisibleMass`. -/
theorem realVisibleMass_eq_legacy [AddGroup G] [Fintype G] [DecidableEq G]
    (y : Fin q → G) :
    realVisibleMass (G := G) (q := q) y =
      RandomSystems.Applications.SoP.realVisibleMass (G := G) (q := q) y := by
  rfl

/-- Anti-drift pin: the migrated ideal visible-output mass agrees with the
legacy `RandomSystems.Applications.SoP.idealVisibleMass`. -/
theorem idealVisibleMass_eq_legacy [Fintype G] [Nonempty G] (y : Fin q → G) :
    idealVisibleMass (G := G) (q := q) y =
      RandomSystems.Applications.SoP.idealVisibleMass (G := G) (q := q) y := by
  rfl

/-- Anti-drift pin: the migrated real visible distribution is the legacy one
as a `RandomSystems.Dist`. -/
theorem realVisibleDist_eq_legacy [AddGroup G] [Fintype G] [DecidableEq G] :
    realVisibleDist (G := G) (q := q) =
      RandomSystems.Applications.SoP.realVisibleDist (G := G) (q := q) := by
  ext y
  rw [realVisibleDist_apply,
    RandomSystems.Applications.SoP.realVisibleDist_apply,
    realVisibleMass_eq_legacy]

/-- Anti-drift pin: the migrated ideal visible distribution is the legacy
uniform one as a `RandomSystems.Dist`. -/
theorem idealVisibleDist_eq_legacy [Fintype G] [Nonempty G] :
    idealVisibleDist (G := G) (q := q) =
      RandomSystems.Applications.SoP.idealVisibleDist (G := G) (q := q) := by
  ext y
  rw [idealVisibleDist_apply,
    RandomSystems.Applications.SoP.idealVisibleDist_apply,
    idealVisibleMass_eq_legacy]

/-- Anti-drift pin: the migrated exact visible statistical distance is the
legacy `RandomSystems.Applications.SoP.visibleStatDist`. -/
theorem visibleStatDist_eq_legacy [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] :
    visibleStatDist (G := G) (q := q) =
      RandomSystems.Applications.SoP.visibleStatDist (G := G) (q := q) := by
  -- both sides now package `statDist` with its non-negativity proof, and that
  -- proof mentions the distributions, so the rewrite cannot happen inside the
  -- subtype; go through the injective coercion first
  apply NNReal.coe_injective
  unfold visibleStatDist RandomSystems.Applications.SoP.visibleStatDist
  simp only [NNReal.coe_mk]
  rw [realVisibleDist_eq_legacy, idealVisibleDist_eq_legacy]

end SoP
end HTechnique
end RandomSystems
