/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18TacticsCore
import RandomSystems.GameOf
import RandomSystems.DistSimp

/-!
# CR18 proof automation — game layer

The game/filter/transcript-aware normalizers of the CR18 tactic suite, on top of the
layer-independent core (`RandomSystems.CR18TacticsCore`: `cr18_pushforward`, `cr18_prob`,
`cr18_mass`, `cr18_arith`, `cr18_algebra`, `cr18_routine`, …).  These tactics package paper-level
bookkeeping: the `[q]` query filter, `gameOf`/MBO projections, and transcript lengths.  They
intentionally avoid protocol-specific events such as the switching-lemma collision predicate.
-/

namespace RandomSystems.CR18

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

/-- Conservative CR18 simplifier: domain-specific normalizers before ordinary `simp`. -/
macro "cr18_simp" : tactic =>
  `(tactic| (try cr18_pushforward) <;> (try cr18_prob) <;> (try cr18_filter) <;> (try cr18_game) <;>
      (try cr18_transcript) <;> (try simp))

/-- Heavier CR18 automation pass for local bookkeeping goals. -/
macro "cr18_grind" : tactic =>
  `(tactic| cr18_simp <;> try grind)

/-- **Omnibus finisher** — the "end the proof" tactic for the high-level
workflow: attempt the whole automation arsenal so a lemma body can be just its
top-level argument followed by `cr18_close`.  Ordered cheapest-plausible-first:
direct `grind`, then arithmetic, then a normalize-and-grind pass. -/
macro "cr18_close" : tactic =>
  `(tactic| first
      | grind
      | cr18_arith!
      | cr18_algebra
      | (cr18_simp <;> try grind)
      | (cr18_mass_expand <;> try grind))

end RandomSystems.CR18
