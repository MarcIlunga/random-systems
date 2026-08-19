/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.FixedQuery
import RandomSystems.FunctionEvaluator
import RandomSystems.HTechnique.TranscriptLawPublic

/-!
# Public fixed-query CR18 transcript laws

This module exposes fixed-query transcript distributions without representative
wrappers.  Representative-level fixed-query adapters remain in `FixedQuery`.
-/

noncomputable section

namespace RandomSystems
namespace HTechnique

universe u v w

variable {X : Type u} {Y : Type v} {q : Nat}

export RandomSystems.CR18
  (CR18TranscriptPrefix
   vectorOfFunction
   functionOfVector
   functionOfVector_vectorOfFunction
   vectorOfFunction_functionOfVector
   vectorFunctionEquiv
   vectorFunctionEquiv_apply
   vectorFunctionEquiv_symm_apply
   fixedInputTranscriptPrefix
   fixedInputTranscriptPrefix_injective
   fixedInputLiftDist
   fixedInputLiftDist_apply_fixed
   fixedInputLiftDist_apply_of_input_ne
   fixedInputLiftDist_weight
   fixedInputLiftDist_pointwise_lower_bound
   fixedInputLiftDist_fTransform
   fixedQueryDDE
   fixedQueryEnvironment
   fixedQueryEnvironment_KQueryTotal
   fixedQueryDDE_apply_of_lt
   transcriptEnvironmentEvent_fixedQueryEnvironment_iff
   transcriptEnvironmentFactor_fixedQueryEnvironment_of_eq
   transcriptEnvironmentFactor_fixedQueryEnvironment_of_ne
   transcriptLaw_fixedQueryEnvironment_of_eq
   transcriptLaw_fixedQueryEnvironment_of_ne)

namespace ProbPDS

/-- **Source-theorem bridge; candidate for upstream.** Transcript distribution
for a law-level PDS against the deterministic fixed-query CR18 environment.
The public inputs are the PDS law and the query vector. -/
noncomputable def fixedQueryTranscriptDist [FiniteTranscriptSpace X Y q]
    (S : ProbPDS X Y) (xs : Fin q → X) :
    RandomSystems.Dist (TranscriptPrefix X Y q) :=
  RandomSystems.CR18.PFunPDS.Prob.fixedQueryTranscriptDist S xs

end ProbPDS

end HTechnique
end RandomSystems
