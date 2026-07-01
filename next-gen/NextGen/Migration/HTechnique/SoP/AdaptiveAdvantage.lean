/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.AdaptiveTranscriptAdvantage
import NextGen.Migration.HTechnique.SoP.CompressionLegacy
import NextGen.Migration.HTechnique.SoP.LawAdvantage

/-!
# SoP adaptive transcript advantage

This module packages legacy names for the SoP adaptive transcript advantages.
The full adaptive endpoint is now a compatibility alias for the law-level
`SoP.advPRF` endpoint in `SoP.LawAdvantage`.  The old bounded-chooser endpoint
is still a legacy representative wrapper over the generic law-level bounded
supremum.

Source status:

* source-theorem bridge: CR18/Lanzenberger adaptive advantage is a supremum over
  environments; after the H-technique proof supplies a uniform bound for every
  q-query-total environment, the corresponding adaptive transcript supremum is
  bounded by the same error term.

The legacy bounded `advantageAdaptive` reconciliation now lives generically in
`LegacyBoundedTranscript`.

Migration note: this module is compatibility-only.  New SoP proofs should use
the law-level endpoints in `SoP.LawAdvantage` and `SoPBoundary`.
-/

noncomputable section

open scoped NNReal

namespace NextGen
namespace Migration
namespace HTechnique
namespace SoP

variable {G : Type*} {q : Nat}

/-- **Compatibility alias.** The migrated adaptive transcript advantage for the
normalized SoP system, now routed through the law-level thesis-style PRF
advantage `SoP.advPRF`. -/
noncomputable def adaptiveTranscriptAdvantage
    [AddGroup G] [Fintype G] [DecidableEq G] : ℝ :=
  advPRF (G := G) (q := q)

/-- **Source-theorem bridge.** The migrated bounded-environment adaptive
transcript advantage for the normalized SoP system, restricted to old-style
q-round deterministic choosers.  This legacy name is built from the
representative SoP compatibility adapters, but the generic bounded supremum it
calls is law-level. -/
noncomputable def boundedAdaptiveTranscriptAdvantage
    [AddGroup G] [Fintype G] [DecidableEq G] : ℝ := by
  letI : Nonempty G := ⟨0⟩
  exact
    NextGen.Migration.HTechnique.boundedAdaptiveTranscriptAdvantage
      (q := q)
      (normalizedSoPRepresentative (G := G))
      (urfRepresentative (G := G))

/-- **Source theorem boundary.** The migrated SoP H-technique bound, packaged
as an adaptive transcript supremum over q-query-total deterministic CR18
environments. -/
theorem adaptiveTranscriptAdvantage_bound
    [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    adaptiveTranscriptAdvantage (G := G) (q := q) ≤
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 : ℝ) := by
  exact advPRF_bound (G := G) (q := q) h_bound

/-- **Source theorem boundary.** The same SoP H-technique bound restricted to
old-style bounded deterministic choosers.  The generic bridge from this bounded
transcript supremum to old bounded `advantageAdaptive` lives in
`LegacyBoundedTranscript`. -/
theorem boundedAdaptiveTranscriptAdvantage_bound
    [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    boundedAdaptiveTranscriptAdvantage (G := G) (q := q) ≤
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 : ℝ) := by
  letI : Nonempty G := ⟨0⟩
  unfold boundedAdaptiveTranscriptAdvantage
  exact le_trans
    (NextGen.Migration.HTechnique.boundedAdaptiveTranscriptAdvantage_le_adaptiveTranscriptAdvantage
      (q := q)
      (normalizedSoPRepresentative (G := G))
      (urfRepresentative (G := G)))
    (adaptiveTranscriptAdvantage_bound (G := G) (q := q) h_bound)

end SoP
end HTechnique
end Migration
end NextGen
