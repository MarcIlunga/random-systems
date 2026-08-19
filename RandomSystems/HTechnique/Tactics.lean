/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.TacticsCore
import RandomSystems.HTechnique.SoP.Compression
import RandomSystems.HTechnique.StrongPRP
import RandomSystems.TotalityTactics

/-!
# H-technique proof automation

This module collects conservative rewrite bundles for the migrated
H-technique/SoP proof surface.  It deliberately lives in the migration folder:
the rewrite names mention fixed-query environments, function-evaluator bridges,
and SoP compression, so they are too application-specific for `RandomSystems.CR18Tactics`.
-/

namespace RandomSystems
namespace HTechnique

/-- Normalize fixed-query transcript-law expressions to the corresponding
system factor or fixed-input lifted law. -/
macro "htechnique_fixed_query" : tactic =>
  `(tactic| htechnique_fixed_query_core <;> simp only [
      SoP.transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_dist_eq_liftedRealVisibleDist,
      SoP.transcriptLaw_fixedQueryEnvironment_urfRV_dist_eq_liftedIdealVisibleDist
    ])

/-- Apply one low-level repeated-query compression rewrite.

This is intentionally one-shot: repeatedly simplifying with the raw
`fTransform_*_expand_compressed` lemmas can keep compressing already-compressed
query tuples. -/
macro "htechnique_compress_once" : tactic =>
  `(tactic| first
      | rw [SoP.fTransform_eval_repeated_eq_expand_compressed]
      | rw [RandomSystems.CR18.fTransform_sampled_eval_repeated_eq_expand_compressedQuery]
      | rw [SoP.liftVisibleDist_expandCompressed]
      | rw [RandomSystems.Dist.fTransform_comp])

/-- Normalize repeated-query H-technique transcript laws by compressing to the
canonical injective query tuple and expanding the resulting transcript law by
deterministic pushforward. -/
macro "htechnique_compress" : tactic =>
  `(tactic| simp only [
      SoP.transcriptLaw_fixedQueryEnvironment_normalizedSoPRV_compress,
      SoP.transcriptLaw_fixedQueryEnvironment_urfRV_compress,
      dist_simp,
      Function.comp
    ])

/-- Conservative H-technique simplifier: first apply CR18 bookkeeping, then the
H-technique fixed-query and compression rewrite bundles, then ordinary `simp`. -/
macro "htechnique_simp" : tactic =>
  `(tactic| (try cr18_simp) <;> (try htechnique_dist) <;>
      (try htechnique_fixed_query) <;> (try htechnique_compress) <;>
      (try htechnique_dist) <;> (try simp))

/-- Heavier H-technique automation pass for local bookkeeping goals. -/
macro "htechnique_grind" : tactic =>
  `(tactic| htechnique_simp <;> try grind)

/-- Advantage-shell reducer for the migrated security endpoints: reduce
`Adv/advPRF/advPRP/fixedQueryAdv ≤ ε` goals to their pointwise transcript
bounds via the `SecurityDefs` supremum shells, falling back to the core CR18
shell. -/
macro "htechnique_adv_le" : tactic =>
  `(tactic| first
      | with_reducible apply SecurityDefs.advPRF_le_of_pointwise
      | with_reducible apply SecurityDefs.advPRP_le_of_pointwise
      | with_reducible apply SecurityDefs.Adv_le_of_pointwise
      | with_reducible apply SecurityDefs.fixedQueryAdv_le_of_pointwise
      | cr18_adv_le)

/-- Discharge totality side conditions for the migrated application models:
first the shared CR18 constructors (`cr18_total`), then the SoP and
strong/tweakable-PRP specializations. -/
macro "htechnique_total" : tactic =>
  `(tactic| first
      | cr18_total
      | with_reducible apply SoP.normalizedSoPProbPDS_KStepTotal
      | with_reducible apply SoP.normalizedSoPProbPDS_totalOnNonempty
      | with_reducible apply strongURP_KStepTotal
      | with_reducible apply strongURP_totalOnNonempty
      | with_reducible apply tweakableURP_KStepTotal
      | with_reducible apply tweakableURP_totalOnNonempty
      | with_reducible apply tweakableStrongURP_KStepTotal
      | with_reducible apply tweakableStrongURP_totalOnNonempty)

end HTechnique
end RandomSystems
