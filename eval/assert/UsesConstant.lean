/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# `#uses_constant` — routing assertion for the proof-workflow eval

Grades *which technique a proof actually took*, from the elaborated proof term
rather than from what the agent said it did.

`#uses_constant target dep` succeeds when `dep` is reachable from `target`'s
proof term.  This is the eval's routing check: if the reference proof for a
bound goes through a packaged endpoint, the agent's proof must too, and no
amount of plausible prose in a transcript can fake it.

Search is a bounded BFS over value-dependencies, skipping `Mathlib`/`Init`/`Std`
subtrees — the endpoints we assert on are library declarations a few steps from
the target, while the Mathlib closure is ~200k constants and does not terminate
in useful time.  `depth` is exposed because an agent that routes through a
private wrapper of the endpoint is still routing correctly.

A **failed** lookup of `target` is an error, not a `false`.  A checker that
inspects zero items must fail: reporting "does not use the endpoint" for a
declaration that does not exist would pass a run in which nothing was proved.
-/

open Lean Elab Command Meta

namespace RandomSystems.Eval

private def skipPrefixes : List Name := [`Mathlib, `Init, `Std, `Lean, `Aesop, `Qq]

private def skipped (n : Name) : Bool :=
  n.isInternal || skipPrefixes.any (·.isPrefixOf n)

/-- Direct value-dependencies of a declaration (its proof term's constants). -/
private def directDeps (env : Environment) (n : Name) : Array Name :=
  match (env.find? n).bind ConstantInfo.value? with
  | some v => v.getUsedConstants.filter (!skipped ·)
  | none   => #[]

/-- Is `dep` reachable from `target` within `depth` value-dependency steps? -/
partial def reaches (env : Environment) (target dep : Name) (depth : Nat) : Bool :=
  let rec go (frontier : Array Name) (seen : NameSet) (fuel : Nat) : Bool :=
    if fuel == 0 || frontier.isEmpty then false
    else
      let next := frontier.flatMap (directDeps env)
      if next.contains dep then true
      else
        let fresh := next.filter (!seen.contains ·)
        go fresh (fresh.foldl NameSet.insert seen) (fuel - 1)
  go #[target] (NameSet.empty.insert target) depth

/-- `#uses_constant Foo.bar Baz.qux` — assert `Foo.bar`'s proof reaches `Baz.qux`.

An optional trailing numeral sets the search depth (default 6). Logs `PASS`/`FAIL`
and *errors* on FAIL, so the assertion is a non-zero exit rather than a line in a
log nobody reads. -/
syntax (name := usesConstantCmd)
  "#uses_constant " ident ident (num)? : command

@[command_elab usesConstantCmd]
def elabUsesConstant : CommandElab := fun stx => do
  let env ← getEnv
  let target := stx[1].getId
  let dep := stx[2].getId
  let depth := (stx[3].getOptional?.bind (·.isNatLit?)).getD 6
  -- Resolve both names against the environment BEFORE deciding anything.
  -- An absent target means the run produced nothing; that is a failure, never a `false`.
  let some target ← pure ((env.find? target).map ConstantInfo.name)
    | throwError "ASSERTION ERROR: target {target} does not exist in the environment \
        (nothing was proved, or it was renamed)"
  let some dep ← pure ((env.find? dep).map ConstantInfo.name)
    | throwError "ASSERTION ERROR: expected dependency {dep} does not exist \
        (the assertion itself is stale — fix the expectation, not the run)"
  if reaches env target dep depth then
    logInfo s!"PASS  {target}  reaches  {dep}"
  else
    throwError "FAIL  {target} does NOT reach {dep} within depth {depth}\n\
      The proof did not route through the expected endpoint."

/-- `#count_axioms Foo.bar` — report the axiom footprint; error on `sorryAx` or
any axiom outside the sanctioned three. -/
syntax (name := countAxiomsCmd) "#assert_axiom_clean " ident : command

@[command_elab countAxiomsCmd]
def elabAssertAxiomClean : CommandElab := fun stx => do
  let env ← getEnv
  let n := stx[1].getId
  let some info := env.find? n
    | throwError "ASSERTION ERROR: {n} does not exist in the environment"
  let (_, s) := ((CollectAxioms.collect info.name).run env).run {}
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := s.axioms.filter (!allowed.contains ·)
  if bad.isEmpty then
    logInfo s!"PASS  {n} is axiom-clean"
  else
    throwError "FAIL  {n} rests on {bad.toList}"

end RandomSystems.Eval
