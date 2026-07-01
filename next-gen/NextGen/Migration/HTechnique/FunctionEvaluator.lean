/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.FunctionEvaluator
import NextGen.Migration.HTechnique.FixedQueryLaw

/-!
# Function-evaluator CR18 systems

Compatibility-only export layer for CR18 systems that are sampled function
evaluators.  The application-independent evaluator facts live in
`NextGen.FunctionEvaluator` under `RandomSystems.CR18`; this file only keeps the
migration namespace imports stable while downstream modules move to the core
names.

Source status:

* support lemma forced by formalization; candidate for upstream: a
  function-valued random system embedded via `PFunDDS.functionEvaluator` has a
  transcript system event exactly when the sampled function matches the output
  vector on the input vector.
-/

noncomputable section

namespace NextGen
namespace Migration
namespace HTechnique

export RandomSystems.CR18
  (functionEvaluatorRV
   list_take_succ_eq_take_append_get
   functionEvaluatorRV_eval_append
   functionEvaluatorRV_eval_vector_take_succ
   functionEvaluatorRV_KStepTotal
   transcriptSystemEvent_functionEvaluatorRV_iff
   CR18TranscriptPrefix
   fixedInputLiftDist
   fixedQueryEnvironment)

end HTechnique
end Migration
end NextGen
