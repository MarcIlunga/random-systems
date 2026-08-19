/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.SoP.LegacyVisibleEquiv
import RandomSystems.Legacy.Applications.XoPModel

/-!
# Legacy XoP endpoints against the migrated fixed-transcript law

This module is compatibility-only.  It is the Phase-5 capstone of the
migration plan (DAG step 6): the legacy in-repo XoP application endpoint —
the unrestricted adaptive XoP advantage — is reproved against the *migrated*
SoP visible law.

The content is a composition of two machine-checked facts:

* `RandomSystems.Applications.XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist`:
  the legacy adaptive XoP advantage equals the legacy SoP
  `visibleStatDist` (the LM20 orbit/counting reduction); and
* `RandomSystems.HTechnique.SoP.visibleStatDist_eq_legacy`: the migrated
  visible statistical distance is (definitionally) the legacy one.

Together they pin the legacy `xop_adaptiveAdvantage_*` family to the migrated
fixed-transcript surface, so deprecating the legacy SoP `Transcript`/`TV`
carriers cannot silently change the XoP endpoint's meaning.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace HTechnique
namespace SoP

/-- **Phase-5 capstone.** The legacy unrestricted adaptive XoP advantage is
exactly the migrated SoP visible statistical distance. -/
theorem xop_adaptiveAdvantage_eq_migrated_visibleStatDist
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G] [Nonempty G]
    (hq : q ≤ Fintype.card G) :
    RandomSystems.advantageAdaptive
        (RandomSystems.Applications.XoP.Model.xopRealPDS (G := G) (q := q))
        (RandomSystems.Applications.XoP.Model.xopIdealPDS (G := G) (q := q)) =
      visibleStatDist (G := G) (q := q) := by
  rw [RandomSystems.Applications.XoP.Model.xop_adaptiveAdvantage_eq_sop_visibleStatDist
      (G := G) (q := q) hq,
    visibleStatDist_eq_legacy]

end SoP
end HTechnique
end RandomSystems
