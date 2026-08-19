/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TotalityRuleSet
import RandomSystems.FunctionEvaluator
import RandomSystems.BoundedEnvironment
import RandomSystems.AdaptiveLawBridge

/-!
# Totality side-condition automation

`cr18_total` discharges the standing CR18 totality side conditions —
`PFunPDS.Prob.KStepTotal`, `PFunPDE.Prob.KQueryTotal`,
`PFunPDE.DDEKQueryTotal`, `PFunPDE.RV.KQueryTotal`, and
`CondEquiv.TotalOnNonempty` — for the standard system/environment
constructors (function evaluators, the URF/URP ideals, deterministic
environments, bounded choosers, exact-query distinguisher environments).

These are the "obviously total" facts of a paper proof; they should never be
discharged by hand at endpoint sites.  Application layers with their own
constructors (e.g. the migrated SoP and strong-PRP models) extend this tactic
with their specializations (`htechnique_total` in the H-technique migration).
-/

namespace RandomSystems.CR18

/-- Law-level `TotalOnNonempty` for the ideal URF, stated over
`(Prob.urf).val` so tactic heads match without unfolding the law. -/
theorem PFunPDS.Prob.urf_totalOnNonempty {X Y : Type*}
    [Fintype (X → Y)] [Nonempty (X → Y)] :
    CondEquiv.TotalOnNonempty (PFunPDS.Prob.urf (X := X) (Y := Y)).val :=
  PFunPDS.URF_totalOnNonempty

/-- Discharge a CR18 totality side condition for standard constructors.
Tries, in order: a hypothesis, the ideal-URF facts, the shared
function-evaluator facts, the bounded-chooser environment fact, and the
deterministic-environment embeddings (including exact-query admission).

Every branch runs at reducible transparency: system laws are large terms, and
unification against the wrong constructor must fail fast on the head constant
instead of unfolding the law. -/
macro "cr18_total" : tactic =>
  `(tactic| first
      | with_reducible assumption
      | with_reducible apply PFunPDS.Prob.urf_KStepTotal
      | with_reducible apply PFunPDS.Prob.urf_totalOnNonempty
      | with_reducible apply PFunPDS.URF_totalOnNonempty
      | with_reducible apply functionEvaluatorProb_KStepTotal
      | with_reducible apply functionEvaluatorProb_totalOnNonempty
      | with_reducible apply boundedEnvironment_KQueryTotal
      | (with_reducible apply PFunPDE.Prob.ofDDE_KQueryTotal
         first
           | with_reducible assumption
           | (with_reducible apply PFunPDE.DDEKQueryTotal_of_queriesExactly
              with_reducible assumption))
      | (with_reducible apply PFunPDE.DDEKQueryTotal_of_queriesExactly
         with_reducible assumption)
      | aesop (rule_sets := [Cr18Total]))

attribute [aesop safe apply (rule_sets := [Cr18Total])]
  PFunPDS.Prob.urf_KStepTotal
  PFunPDS.Prob.urf_totalOnNonempty
  PFunPDS.URF_totalOnNonempty
  functionEvaluatorProb_KStepTotal
  functionEvaluatorProb_totalOnNonempty
  boundedEnvironment_KQueryTotal

end RandomSystems.CR18
