/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.HTechnique.FixedQueryLaw

/-!
# Fixed-query compatibility aliases

Migration-only compatibility aliases for older H-technique proof scripts.

The clean fixed-query surface lives in `FixedQueryLaw` and exposes only the
law-level `ProbPDS.fixedQueryTranscriptDist` facade.  This module keeps
source-name compatibility for raw sample-space wrappers while making that
boundary explicit.  New proofs should use the owner-level CR18 theorem directly.
-/

noncomputable section

namespace RandomSystems
namespace HTechnique

universe u v w

variable {X : Type u} {Y : Type v} {q : Nat}

namespace ProbPDS

/-- **Migration-only compatibility alias.** New proofs should use
`RandomSystems.CR18.PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator`
directly. -/
theorem fixedQueryTranscriptDist_functionEvaluator
    {Ω : Type w} [FiniteTranscriptSpace X Y q]
    (p : RandomSystems.Dist.ProbDist Ω) (F : Ω → X → Y) (xs : Fin q → X) :
    fixedQueryTranscriptDist
        (RandomSystems.CR18.PFunPDS.Prob.functionEvaluator p F) xs =
      RandomSystems.CR18.fixedInputLiftDist xs
        (RandomSystems.Dist.fTransform (fun ω : Ω => fun i : Fin q => F ω (xs i)) p.val) := by
  exact RandomSystems.CR18.PFunPDS.Prob.fixedQueryTranscriptDist_functionEvaluator
    (p := p) (F := F) (xs := xs)

end ProbPDS

end HTechnique
end RandomSystems
