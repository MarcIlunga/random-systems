/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.GameOf
import RandomSystems.DistSimp

/-!
# CR18 proof automation

Small, conservative normalizers for CR18 proofs. These tactics package paper-level bookkeeping:
probability mass under deterministic pushforwards, the `[q]` query filter, `gameOf`/MBO projections,
transcript lengths, and small arithmetic. They intentionally avoid protocol-specific events such as the
switching-lemma collision predicate.
-/

namespace RandomSystems.CR18

/-- Pushforward/distribution normalizer for CR18 proofs.

This delegates to the curated `dist_simp` set, which includes functoriality of deterministic
pushforwards (`Dist.fTransform_comp`) and the standard uniform/weight pushforward facts. -/
macro "cr18_pushforward" : tactic =>
  `(tactic| simp only [dist_simp,
      Dist.mass_fTransform,
      Dist.evalPred_fTransform
    ])

/-- Probability-system bookkeeping for CR18 proofs. -/
macro "cr18_prob" : tactic =>
  `(tactic| simp only [dist_simp,
      Dist.isProbDist_fTransform,
      PFunPDS.isProbDist_ofFunDist_iff,
      PFunPDS.URF_isProbDist,
      PFunPDS.isProbDist_ofPermDist_iff,
      PFunPDS.URP_isProbDist,
      PFunPDS.isProbDist_filterQueries_iff,
      Dist.uniform_isProbDist
    ])

/-- Query-filter normalizer for CR18 proofs. -/
macro "cr18_filter" : tactic =>
  `(tactic| simp only [
      PFunDDS.mem_dom_filterQueries,
      PFunDDS.output_filterQueries,
      PFunDDS.keptPrefix_gameOfDDS,
      PFunDDS.keptPrefix_gameOfDDS_filterQueries_eq_take_of_total,
      PFunDDS.keptPrefix_filterQueries_eq_take_of_total,
      PFunDDS.keptPrefix_filterQueries_functionEvaluator,
      PFunDDS.output_fullyDefined_filterQueries_of_total_ge,
      PFunDDS.output_fullyDefined_filterQueries_of_total_lt,
      PFunDDS.filterQueries_gameOfDDS,
      PFunConverter.queryLimit_filter_apply_eq_filterQueries,
      PFunPDS.filterQueries_gameOf
    ])

/-- Game/MBO constructor normalizer for CR18 proofs. -/
macro "cr18_game" : tactic =>
  `(tactic| simp only [
      PFunDDS.dom_gameOfDDS,
      PFunDDS.output_gameOfDDS,
      PFunDDS.outputBit_gameOfDDS,
      ignoreMBO_gameOf
    ])

/-- Transcript-shape normalizer for CR18 proofs. -/
macro "cr18_transcript" : tactic =>
  `(tactic| simp only [
      PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor,
      PFunPDE.transcriptLawDist_apply,
      PFunPDE.transcriptLawDist_weight,
      PFunPDE.transcriptDist_eq_mass_jointEvent,
      PFunPDS.Prob.transcriptDist_ofDDE,
      PFunDDS.ioTranscript_length,
      transcriptInputs_length,
      transcriptOutputs_length
    ])

/-- Small arithmetic closer for CR18 side conditions. -/
macro "cr18_arith" : tactic =>
  `(tactic| first | omega | linarith | ring | norm_num)

/-- Conservative CR18 simplifier: domain-specific normalizers before ordinary `simp`. -/
macro "cr18_simp" : tactic =>
  `(tactic| (try cr18_pushforward) <;> (try cr18_prob) <;> (try cr18_filter) <;> (try cr18_game) <;>
      (try cr18_transcript) <;> (try simp))

/-- Heavier CR18 automation pass for local bookkeeping goals. -/
macro "cr18_grind" : tactic =>
  `(tactic| cr18_simp <;> try grind)

end RandomSystems.CR18
