/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.FunctionEvaluator

/-!
# Fixed-query CR18 proof automation

Small owner-side normalizers for the deterministic fixed-query CR18
environment.  H-technique proofs use these through their facade tactics, but
the rewrites here are not H-technique-specific.
-/

namespace RandomSystems.CR18

/-- Normalize a concrete fixed-query transcript law to the corresponding system
factor, or to zero when the transcript inputs do not match the fixed query. -/
macro "cr18_fixed_query_base" : tactic =>
  `(tactic| first
      | rw [transcriptLaw_fixedQueryEnvironment_of_eq]
      | exact transcriptLaw_fixedQueryEnvironment_of_ne _ _ _ _ _ (by assumption))

/-- Normalize application-independent fixed-query transcript-law expressions to
the corresponding system factor or fixed-input lifted law. -/
macro "cr18_fixed_query_function_evaluator" : tactic =>
  `(tactic| first
      | cr18_fixed_query_base
      | rw [transcriptLaw_fixedQueryEnvironment_functionEvaluator_dist_eq_fixedInputLiftDist])

/-- Normalize an owner-level fixed-query PDS transcript distribution for sampled
function evaluators. -/
macro "cr18_fixed_query_pds" : tactic =>
  `(tactic|
    (first
      | rw [PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator]
      | rw [PFunPDS.Prob.fixedQueryTranscriptDist_urf]) <;>
    try simp only [Dist.prodProbDist_val])

end RandomSystems.CR18
