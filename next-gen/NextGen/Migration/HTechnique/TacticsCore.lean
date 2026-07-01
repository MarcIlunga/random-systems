/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Migration.HTechnique.TacticsBase
import NextGen.FunctionEvaluator

/-!
# H-technique core proof automation

This module contains automation that is independent of the SoP application.  It
can therefore be imported by application bridge files such as `SoP.SystemLaw`
without creating an import cycle.
-/

namespace NextGen
namespace Migration
namespace HTechnique

/-- Normalize application-independent fixed-query transcript-law expressions to
the corresponding system factor or fixed-input lifted law. -/
macro "htechnique_fixed_query_core" : tactic =>
  `(tactic| cr18_fixed_query_function_evaluator)

/-- Conservative core H-technique simplifier: CR18 bookkeeping plus the
application-independent fixed-query bridge rewrites. -/
macro "htechnique_core_simp" : tactic =>
  `(tactic| (try cr18_simp) <;> (try htechnique_dist) <;>
      (try htechnique_fixed_query_core) <;> (try htechnique_dist) <;> (try simp))

end HTechnique
end Migration
end NextGen
