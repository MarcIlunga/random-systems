/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.Complexity.AdvantageSeq
import NextGen.Complexity.BoundedPerf

/-!
# Complexity proof automation

Small tactics for CR18 complexity proofs.  These are intentionally narrow:
they automate finite game-hop bookkeeping and small arithmetic, not protocol
semantics.
-/

namespace RandomSystems.CR18
namespace Complexity

open Lean.Parser.Tactic

/-- Discharge a finite adjacent-hop bound by case-splitting the hop index.
Pass the local trace/bound definitions explicitly, e.g.
`cr18_hop_cases [trace, stepBound]`. -/
syntax "cr18_hop_cases"
  (" [" ((simpErase <|> simpLemma),*,?) "]")? : tactic

macro_rules
  | `(tactic| cr18_hop_cases $[[$rules,*]]?) =>
      `(tactic| (intro i hi; interval_cases i <;> simp_all $[[$rules,*]]?))

/-- Normalize the finite sums produced by short hybrid traces. -/
syntax "cr18_trace_arith" : tactic
syntax "cr18_trace_arith"
  " [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]" : tactic

macro_rules
  | `(tactic| cr18_trace_arith) =>
      `(tactic| norm_num [Finset.sum_range_succ])
  | `(tactic| cr18_trace_arith [$rules,*]) =>
      `(tactic| norm_num [Finset.sum_range_succ, $rules,*])

/-- Build a costed reduction from a named hypothesis of the form
`performance equality ∧ cost bound`.  This is the standard CR18 converter
obligation shape. -/
syntax "cr18_reduction_from " term : tactic
syntax "cr18_reduction_from " term " with "
  "[" ((simpErase <|> simpLemma),*,?) "]" : tactic

macro_rules
  | `(tactic| cr18_reduction_from $h) =>
      `(tactic|
        constructor <;> first
          | exact ($h).2
          | (intro solver
             simpa using le_of_eq (($h).1 solver)))
  | `(tactic| cr18_reduction_from $h with [$rules,*]) =>
      `(tactic|
        constructor <;> first
          | exact ($h).2
          | (intro solver
             simpa [$rules,*] using le_of_eq (($h).1 solver)))

/-- Build a costed reduction from a named hypothesis of the form
`performance bound ∧ cost bound`. -/
syntax "cr18_reduction_bound_from " term : tactic
syntax "cr18_reduction_bound_from " term " with "
  "[" ((simpErase <|> simpLemma),*,?) "]" : tactic

macro_rules
  | `(tactic| cr18_reduction_bound_from $h) =>
      `(tactic|
        constructor <;> first
          | exact ($h).2
          | (intro solver
             simpa using (($h).1 solver)))
  | `(tactic| cr18_reduction_bound_from $h with [$rules,*]) =>
      `(tactic|
        constructor <;> first
          | exact ($h).2
          | (intro solver
             simpa [$rules,*] using (($h).1 solver)))

/-- Turn a named reduction-class-map hypothesis into the corresponding
solver-class map. -/
syntax "cr18_solver_class_map_from " term : tactic

macro_rules
  | `(tactic| cr18_solver_class_map_from $h) =>
      `(tactic| first
        | exact CostedReductionClassMapHyp.mapsSolverClasses $h
        | exact VerifiedCostedReductionClassMapHyp.mapsSolverClasses $h)

/-- Compose two costed reductions with explicit monotonicity proofs for the
second performance map and second cost map. -/
syntax "cr18_comp_reductions " term ", " term " using " term ", " term : tactic

macro_rules
  | `(tactic| cr18_comp_reductions $hPQ, $hQR using $htauQR, $hcostQR) =>
      `(tactic| first
        | exact IsCostedReduction.comp $hPQ $hQR $htauQR $hcostQR
        | exact VerifiedCostedReduction.comp $hPQ $hQR $htauQR $hcostQR)

/-- Compose an identity-performance reduction with a target
bounded-performance theorem. -/
syntax "cr18_bound_transfer_from " term : tactic

macro_rules
  | `(tactic| cr18_bound_transfer_from $h) =>
      `(tactic| first
        | exact IsCostedReduction.BoundTransferHyp.bound $h
        | exact VerifiedCostedReduction.BoundTransferHyp.bound $h)

end Complexity
end RandomSystems.CR18
