/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.FixedQueryLaw
import NextGen.Migration.HTechnique.TranscriptLawCore
import NextGen.Migration.HTechnique.TacticsSimpAttr
import NextGen.FixedQueryTactics
import RandomSystems.DistSimp

/-!
# H-technique base proof automation

This module contains the lowest fixed-query transcript-law rewrite bundle.  It
depends only on the law-level fixed-query and transcript-law bridge modules, so
it can be used by `FunctionEvaluator` and by higher bridge layers without import
cycles or representative/sample-space adapters.
-/

namespace NextGen
namespace Migration
namespace HTechnique

attribute [htechnique_dist_simp]
  TranscriptLawBridge.dist_apply
  fixedInputLiftDist_weight
  RandomSystems.CR18.PFunPDS.uniformP_val
  RandomSystems.probBad_const_pair
  Function.comp_apply
  id_eq

/-- Normalize distribution and transcript-law bookkeeping used by migrated
H-technique proofs.  This is intentionally just the curated
`htechnique_dist_simp` set, so it only applies shrinking owner-level facts. -/
macro "htechnique_dist" : tactic =>
  `(tactic|
    (repeat rw [RandomSystems.Dist.fTransform_fst_const_pair]) <;>
    (try cr18_transcript) <;>
    simp only [dist_simp, htechnique_dist_simp])

/-! ### Conservative-extension regression checks -/

section ConservativeExtensionExamples

variable {A U : Type*} [Fintype A] [Fintype U]
variable (real ideal : RandomSystems.Dist A) (Bad : A → Prop) (u : U)

/-- Compile-time check: deterministic terminal side information is an isometric
embedding of transcript laws.  This is the "constant `U` recovers the original
theory" test for extended H-technique arguments. -/
example :
    RandomSystems.statDist
        (RandomSystems.Dist.fTransform (fun a : A => (a, u)) real)
        (RandomSystems.Dist.fTransform (fun a : A => (a, u)) ideal) =
      RandomSystems.statDist real ideal := by
  exact RandomSystems.statDist_fTransform_const_pair real ideal u

/-- Compile-time check: projecting away deterministic terminal side information
recovers the original transcript law before statistical distance is measured. -/
example :
    RandomSystems.statDist
        (RandomSystems.Dist.fTransform (fun p : A × U => p.1)
          (RandomSystems.Dist.fTransform (fun a : A => (a, u)) real))
        (RandomSystems.Dist.fTransform (fun p : A × U => p.1)
          (RandomSystems.Dist.fTransform (fun a : A => (a, u)) ideal)) =
      RandomSystems.statDist real ideal := by
  exact RandomSystems.statDist_project_const_pair real ideal u

/-- Compile-time check: a bad event that ignores deterministic terminal side
information has exactly the original bad probability. -/
example :
    RandomSystems.probBad
        (RandomSystems.Dist.fTransform (fun a : A => (a, u)) ideal)
        (fun p : A × U => Bad p.1) =
      RandomSystems.probBad ideal Bad := by
  exact RandomSystems.probBad_const_pair ideal Bad u

end ConservativeExtensionExamples

/-- Normalize a concrete fixed-query transcript law to the corresponding system
factor, or to zero when the transcript inputs do not match the fixed query. -/
macro "htechnique_fixed_query_base" : tactic =>
  `(tactic| cr18_fixed_query_base)

/-- Normalize a law-level fixed-query PDS transcript distribution for sampled
function evaluators.  This deliberately uses the owner-level CR18 theorem
directly, not the migration compatibility alias. -/
macro "htechnique_fixed_query_pds" : tactic =>
  `(tactic|
    unfold ProbPDS.fixedQueryTranscriptDist <;>
    cr18_fixed_query_pds <;>
    try simp only [htechnique_dist_simp])

/-- Enter the pointwise event-congruence proof for a distribution mass goal,
optionally after exposing a deterministic pushforward application as a mass.
This covers the recurring H-technique bridge pattern
`fTransform_apply_eq_mass; ...; mass_congr` without baking in any
application-specific event theorem. -/
macro "htechnique_mass_congr" : tactic =>
  `(tactic| first
      | apply RandomSystems.Dist.mass_congr
      | unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor
        apply RandomSystems.Dist.mass_congr
      | rw [RandomSystems.Dist.fTransform_apply_eq_mass]
        apply RandomSystems.Dist.mass_congr
      | rw [RandomSystems.Dist.fTransform_apply_eq_mass]
        unfold RandomSystems.CR18.PFunPDE.transcriptSystemFactor
        apply RandomSystems.Dist.mass_congr)

/-- Enter a distribution-mass event-congruence proof and rewrite the source
event by the supplied event equivalence theorem. -/
macro "htechnique_mass_event " h:Lean.Parser.Tactic.rwRule : tactic =>
  `(tactic| (htechnique_mass_congr; intro _; rw [$h]))

end HTechnique
end Migration
end NextGen
