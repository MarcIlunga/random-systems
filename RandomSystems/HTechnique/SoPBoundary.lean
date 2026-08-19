/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.SoP.LawAdvantage

/-!
# SoP migration boundary

The active migration goal is not just to port the abstract H-technique lemmas:
the migrated surface must still support applications, especially the SoP/XoP
orbit-counting proof.

This module is the compile gate for the migrated SoP application layer.  It
intentionally does not import the old in-repo `RandomSystems.Applications.SoP`:
that code is still on the old bounded-system surface and currently fails as a
clean dependency under this worktree.  It also does not import the external
`HTechnique` project, because that project already depends on `random-systems`
and would create a package cycle.

The replacement sequence is:

* move application-independent H-technique lemmas to `RandomSystems`;
* rehome the fixed-transcript/visible-law SoP layer over `RandomSystems`'s
  transcript-law API (started in `SoP.VisibleLaw` and lifted to CR18
  transcript-prefixes in `SoP.TranscriptPrefix`);
* port the repeated-query compression layer so arbitrary fixed queries reduce
  to the injective fixed-query theorem;
* make this boundary import the migrated SoP module, then use it as the
  application target.  Representative and old bounded adaptive SoP endpoints
  remain build-checked through `SoPLegacyBoundary`, not through this curated
  public boundary.
-/

open scoped RandomSystems.CR18

namespace RandomSystems
namespace HTechnique

/-- **Source theorem boundary.** Repeated-query SoP bound on the migrated CR18
transcript-law surface, with the paper's concrete error term `q^3 / |G|^2`.

This is the fixed-environment application endpoint corresponding to the source
project's `sop_statDist_rfDist_le`, stated over law-level CR18 transcript
distributions.  The fixed-query environment is constructed from `xs` inside the
`ProbPDS.fixedQueryTranscriptDist` API. -/
theorem sop_fixedQueryTranscript_bound
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (xs : Fin q → G) (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    RandomSystems.statDist
        (ProbPDS.fixedQueryTranscriptDist
          (SoP.normalizedSoPProbPDS (G := G)) xs)
        (ProbPDS.fixedQueryTranscriptDist
          (ProbPDS.urf (X := G) (Y := G)) xs) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  exact SoP.repeatedQuerySoP_fixedQuery_law_bound xs h_bound

/-- **Source-name compatibility.** Migrated spelling of the external core
fixed-query endpoint `sop_prf_advantage`, stated on the CR18 transcript-law
surface.

The old source theorem was restricted to injective query vectors and carried a
separate `0 < |G|` premise.  The migrated law-level theorem is stronger: the
ideal is the true URF fixed-query transcript law, so repeated queries are handled
directly, and group nonemptiness is discharged internally. -/
theorem sop_prf_advantage
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) (xs : Fin q → G) :
    RandomSystems.statDist
        (ProbPDS.fixedQueryTranscriptDist
          (SoP.normalizedSoPProbPDS (G := G)) xs)
        (ProbPDS.fixedQueryTranscriptDist
          (ProbPDS.urf (X := G) (Y := G)) xs) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  exact sop_fixedQueryTranscript_bound xs h_bound

/-- **Source-name compatibility.** Migrated spelling of the external
H-technique endpoint `sop_statDist_rfDist_le`, stated on the CR18 transcript-law
surface.  The old source theorem carried an explicit `0 < |G|` premise; here it
is discharged internally from `[AddGroup G]`. -/
theorem sop_statDist_rfDist_le
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) (xs : Fin q → G) :
    RandomSystems.statDist
        (ProbPDS.fixedQueryTranscriptDist
          (SoP.normalizedSoPProbPDS (G := G)) xs)
        (ProbPDS.fixedQueryTranscriptDist
          (ProbPDS.urf (X := G) (Y := G)) xs) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  exact sop_fixedQueryTranscript_bound xs h_bound

/-- **Source-name compatibility.** Migrated fixed-query SoP advantage: supremum
over query vectors of the CR18 transcript-law statistical distance.  This is the
law-level replacement for the external `sopFixedQueryAdvantage` over
`sopDist`/`rfDist`.

`Finset.sup` needs an `OrderBot`, which the signed carrier's `statDist` no
longer has; the summand is packaged back into `ℝ≥0` by `statDist_nonneg`, so
the advantage keeps both its `ℝ≥0` type and its value. -/
noncomputable def sopFixedQueryAdvantage
    (G : Type*) (q : Nat) [AddGroup G] [Fintype G] [DecidableEq G] : NNReal :=
  Finset.sup Finset.univ
    (fun xs : Fin q → G =>
      (⟨RandomSystems.statDist
          (ProbPDS.fixedQueryTranscriptDist
            (SoP.normalizedSoPProbPDS (G := G)) xs)
          (ProbPDS.fixedQueryTranscriptDist
            (ProbPDS.urf (X := G) (Y := G)) xs),
        RandomSystems.statDist_nonneg _ _⟩ : NNReal))

/-- **Source-name compatibility.** Migrated fixed-query SoP advantage bound,
matching the external endpoint `sopFixedQueryAdvantage_le` on the CR18
transcript-law surface. -/
theorem sopFixedQueryAdvantage_le
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    sopFixedQueryAdvantage G q ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  unfold sopFixedQueryAdvantage
  refine Finset.sup_le (fun xs _ => ?_)
  rw [← NNReal.coe_le_coe]
  push_cast
  exact sop_statDist_rfDist_le h_bound xs

/-- **Source theorem boundary.** Arbitrary-environment SoP bound on the
migrated CR18 transcript-law surface.

This is the adaptive/application endpoint currently available on the migration
surface.  The only environment-side normalization premise is the meaningful one:
every deterministic environment in the law's support must issue `q` concrete
queries.  Representative data is constructed internally from the law-level PDS
and PDE objects. -/
theorem sop_adaptiveTranscript_bound
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (E : ProbPDE G G)
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2)
    (hEtotal : E.KQueryTotal q) :
    RandomSystems.statDist
        (ProbPDS.transcriptDist (q := q) (SoP.normalizedSoPProbPDS (G := G)) E)
        (ProbPDS.transcriptDist (q := q) (ProbPDS.urf (X := G) (Y := G)) E) ≤
      (q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 := by
  exact SoP.repeatedQuerySoP_probPDE_law_bound E h_bound hEtotal

/-- **Source theorem boundary.** Paper-facing adaptive PRF advantage bound for
normalized SoP, matching the external H-technique endpoint `sop_advPRF_le` on
the migrated CR18/thesis transcript-law advantage surface. -/
theorem sop_advPRF_le
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    SoP.advPRF (G := G) (q := q) ≤
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 : ℝ) := by
  exact SoP.advPRF_bound h_bound

/-- **Source theorem boundary.** Raw CR18 filtered distinguishing advantage for
normalized SoP is bounded by the migrated thesis-style transcript-law PRF
advantage.  The filtered systems are constructed in the conclusion as
Maurer's `[q]` restriction of the concrete real and ideal SoP laws. -/
theorem sop_filteredDelta_le_advPRF
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G] :
    (Δ(⌈q⌉ (SoP.normalizedSoPProbPDS (G := G)).val,
        ⌈q⌉ (ProbPDS.urf (X := G) (Y := G)).val) : ℝ) ≤
      SoP.advPRF (G := G) (q := q) := by
  exact SoP.filteredDelta_le_advPRF

/-- **Source theorem boundary.** Raw CR18 filtered distinguishing bound for
normalized SoP, combining the CR18 filtered-`Delta`/transcript-`Adv` bridge with
the migrated SoP H-technique bound. -/
theorem sop_filteredDelta_le
    {G : Type*} {q : Nat} [AddGroup G] [Fintype G] [DecidableEq G]
    (h_bound : q ^ 3 ≤ (Fintype.card G) ^ 2) :
    (Δ(⌈q⌉ (SoP.normalizedSoPProbPDS (G := G)).val,
        ⌈q⌉ (ProbPDS.urf (X := G) (Y := G)).val) : ℝ) ≤
      ((q : NNReal) ^ 3 / ((Fintype.card G : NNReal)) ^ 2 : ℝ) := by
  exact SoP.filteredDelta_bound h_bound

end HTechnique
end RandomSystems
