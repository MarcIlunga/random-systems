/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Mathlib.Topology.EMetricSpace.Defs
import RandomSystems.Dist

/-!
# The vocabulary linter: §10.11, enforced

The surface rule — kernel names may appear in definition *bodies*, never in
a surface *statement*, except in registered bridges — has until now been
prose.  This module enforces it:

* `@[cc_surface]` tags a declaration as surface API: its **statement** (the
  stored type; bodies are exempt by construction) must not show kernel
  vocabulary.
* `@[cc_surface_bridge]` registers a sanctioned exception — the Bridges
  section of `Jost/Surface.lean`, and the statements that still await a
  surface name for a kernel notion (listed below).  Bridges are counted and
  reported, never scanned: the exemption is visible at the declaration
  site, which is the rule's own mechanism.
* `#cc_surface_audit` checks every tagged declaration in the environment;
  `#cc_surface_check id` checks one declaration (tagged or not — used for
  spot checks and for this module's negative test).

## Mechanism and honest limitations

The check scans the **stored statement expression** for denylisted
constants.  Two facts make this sound where naive expectations fail:
abbrevs (`Resource`, `ResourceAt`, `Converter`, …) are *not* unfolded in
stored types, so a statement written in surface vocabulary keeps it; and
only `ConstantInfo.type` is scanned, so bodies are exempt exactly as the
rule demands.  Limitations: (1) tactic blocks embedded in a statement
(e.g. transport side conditions) contribute their elaborated constants —
defensible, since the reader sees those blocks too; a statement that trips
this way is a genuine candidate for a bridge tag or a packaged transport.
(2) The denylist is by namespace prefix and deliberately does not include
`Dist` (seed laws are Def 2.2.1's own objects), `Query`/`AnswerAt` (the
address-tagged input and its answer fibre — thesis vocabulary), or the
`Machine` field projections (`.State`/`.init`/`.step` — the realization's
authoring surface); it does include `Machine.toDDS`, whose surface name is
`presents` ("the system a realization presents", `Jost/Surface.lean`).

## The Maurer standard (M4 extension)

Three further entries hold surface statements to the papers' own idiom:
`HEq`, `Function.update`, `EDist.edist` (rationale at the denylist).  A
statement that predates the standard is *demoted*, not deleted:
`@[cc_surface_demoted]` keeps it available to the kernel, requires its
surface successor in the docstring, and the audit counts it in a third
counter so demotion drift stays visible.  One carve-out the other way:
`Finsupp.support` is legal vocabulary ("for every seed in the support" is
the papers' own phrase) even though the `Finsupp` namespace is denylisted.
-/

namespace RandomSystems.CC.Lint

open Lean Elab Command

initialize ccSurfaceAttr : TagAttribute ←
  registerTagAttribute `cc_surface
    "surface declaration: its statement must be kernel-vocabulary-free (§10.11)"

initialize ccSurfaceBridgeAttr : TagAttribute ←
  registerTagAttribute `cc_surface_bridge
    "registered vocabulary bridge: sanctioned kernel names in the statement (§10.11 exception)"

initialize ccSurfaceDemotedAttr : TagAttribute ←
  registerTagAttribute `cc_surface_demoted
    "superseded kernel-facing statement: kept for kernel use; its surface successor is named in its docstring"

/-- Kernel vocabulary that must not show in a surface statement.  Matching
is by exact name or namespace prefix.

The last three entries are the **Maurer standard** (the 2026-08-06 papers
audit): `HEq` (Prop 2.2.3 is a plain equality on the bundled carrier —
Maurer11 Def. 1(i)), `Function.update` (attachment does not move the type —
"again a resource with the same interface set", Maurer11 fn. 9), and
`EDist.edist` (the papers write `d(R,S)`/`≈_ε`, never a mathlib projection
into `ℝ≥0∞`; the surface spelling is `≈[ε]`). -/
def denylist : List Name := [
  `RandomSystems.CR18.TypedResource.SignatureUniverse,
  `RandomSystems.CR18.TypedResource.Boundary,
  `RandomSystems.CR18.TypedResource.DependentDDS,
  `RandomSystems.CR18.TypedResource.DependentPDS,
  `RandomSystems.CR18.TypedResource.DependentRandomSystem,
  `RandomSystems.CR18.TypedResource.replaceBoundary,
  `RandomSystems.CR18.TypedResource.Machine.toDDS,
  `RandomSystems.CR18.PFunPDS,
  `RandomSystems.CR18.PFunDDS,
  `RandomSystems.Dist.fTransform,
  `Finsupp,
  `HEq,
  `Function.update,
  `EDist.edist]

/-- Constants that may appear in a *stored* statement without being
reader-visible: the single-world embedding pair, which unification writes
into implicit arguments whenever the surface abbrevs (`Resource`,
`Interfaces.Query`, …) unfold during elaboration.  The reader's statement
never shows them. -/
def storedFormAllowlist : List Name := [
  `RandomSystems.CR18.TypedResource.SignatureUniverse.ofInterfaces,
  `RandomSystems.CR18.TypedResource.Boundary.ofInterfaces]

/-- Reader-visible names that are nevertheless the papers' own vocabulary,
carved out of a denylisted namespace: the **support** of a (seed) law —
"for every seed in the support" is how the coupling arguments read
(Jost §2.2.6, LM20). -/
def vocabularyAllowlist : List Name := [
  `Finsupp.support]

/-- Does this constant fall under the denylist? -/
def offending (name : Name) : Bool :=
  storedFormAllowlist.all (· != name) &&
    vocabularyAllowlist.all (· != name) &&
    denylist.any fun entry => entry == name || entry.isPrefixOf name

/-- All constants occurring in an expression (binder types included). -/
partial def usedConstants (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const name _ => acc.insert name
  | .app fn arg => usedConstants arg (usedConstants fn acc)
  | .lam _ ty body _ => usedConstants body (usedConstants ty acc)
  | .forallE _ ty body _ => usedConstants body (usedConstants ty acc)
  | .letE _ ty value body _ =>
      usedConstants body (usedConstants value (usedConstants ty acc))
  | .mdata _ body => usedConstants body acc
  | .proj typeName _ body => usedConstants body (acc.insert typeName)
  | _ => acc

/-- The denylisted constants shown by a declaration's statement.  Instance
constants are skipped: they live only in inferred instance-implicit
arguments (e.g. the quotient's `PseudoEMetricSpace` inside `edist`) and are
never reader-visible vocabulary. -/
def statementViolations (env : Environment) (decl : Name) : Option (List Name) :=
  (env.find? decl).map fun info =>
    ((usedConstants info.type).toList.filter fun name =>
        offending name &&
          !(Meta.instanceExtension.getState env).instanceNames.contains name).mergeSort
      (fun a b => a.toString ≤ b.toString)

/-- Every declaration in the environment carrying the given tag. -/
def taggedDecls (attr : TagAttribute) (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun acc name _ =>
    if attr.hasTag env name then acc.push name else acc

private def violationMessage (decl : Name) (shown : List Name) : MessageData :=
  m!"§10.11 violation: the statement of `{decl}` shows kernel vocabulary: \
{shown}.  Kernel names belong in definition bodies or in registered \
bridges — restate through the surface API, or tag as @[cc_surface_bridge] \
with a recorded justification."

/-- Check one declaration against the surface vocabulary rule, tagged or
not.  Used for spot checks and negative tests. -/
elab "#cc_surface_check " id:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverload id
  let env ← getEnv
  match statementViolations env decl with
  | none => throwError "unknown declaration {decl}"
  | some [] => logInfo m!"✓ `{decl}`: statement is surface-clean."
  | some shown => throwError violationMessage decl shown

/-- Audit every `@[cc_surface]` declaration; report registered bridges and
demoted-with-successor statements (the third counter makes demotion drift
visible: a demoted statement is kernel-facing, superseded, and names its
surface successor in its docstring). -/
elab "#cc_surface_audit" : command => do
  let env ← getEnv
  let strict := taggedDecls ccSurfaceAttr env
  let bridges := taggedDecls ccSurfaceBridgeAttr env
  let demoted := taggedDecls ccSurfaceDemotedAttr env
  let mut failures : Array MessageData := #[]
  for decl in strict do
    match statementViolations env decl with
    | some [] => pure ()
    | some shown => failures := failures.push (violationMessage decl shown)
    | none => failures := failures.push m!"unknown declaration {decl}"
  if failures.isEmpty then
    logInfo m!"cc_surface audit: {strict.size} surface statements clean; \
{bridges.size} bridges registered: {bridges.toList.mergeSort
  (fun a b => a.toString ≤ b.toString)}; \
{demoted.size} demoted with successors."
  else
    throwError MessageData.joinSep failures.toList m!"\n\n"

/-! ## Tests

`#cc_surface_check` is tag-independent, so the negative test needs no
attribute (attributes registered in this module become applicable only in
importing modules — Lean's same-file rule; the real surface tags live in
the `Surface*.lean` files). -/

namespace Test

theorem plantedViolation {X Y : Type} (f : X → Y)
    (law : RandomSystems.Dist X) :
    RandomSystems.Dist.fTransform f law = RandomSystems.Dist.fTransform f law :=
  rfl

/-- A clean statement passes; the body may use anything. -/
noncomputable def cleanExample {X : Type}
    (law : RandomSystems.Dist X) : RandomSystems.Dist X :=
  RandomSystems.Dist.fTransform id law

/-- Maurer-standard planted violation: a raw metric projection in the
statement (the surface spelling is `≈[ε]`). -/
theorem plantedEdist {X : Type} [EDist X] (a b : X) :
    edist a b = edist a b :=
  rfl

/-- Maurer-standard planted violation: layout bookkeeping in the statement
(attachment must not move the type — Maurer11 fn. 9). -/
theorem plantedUpdate {X : Type} [DecidableEq X] (f : X → X) (x : X) :
    Function.update f x (f x) = Function.update f x (f x) :=
  rfl

/-- Maurer-standard planted violation: heterogeneous equality in the
statement (Prop 2.2.3 is a plain `=` on the bundled carrier). -/
theorem plantedHEq {X Y : Type} (x : X) (y : Y) (h : HEq x y) : HEq y x :=
  h.symm

end Test

/-- error: §10.11 violation: the statement of `RandomSystems.CC.Lint.Test.plantedViolation` shows kernel vocabulary: [RandomSystems.Dist.fTransform].  Kernel names belong in definition bodies or in registered bridges — restate through the surface API, or tag as @[cc_surface_bridge] with a recorded justification. -/
#guard_msgs in
#cc_surface_check Test.plantedViolation

/-- info: ✓ `RandomSystems.CC.Lint.Test.cleanExample`: statement is surface-clean. -/
#guard_msgs in
#cc_surface_check Test.cleanExample

/-- error: §10.11 violation: the statement of `RandomSystems.CC.Lint.Test.plantedEdist` shows kernel vocabulary: [EDist.edist].  Kernel names belong in definition bodies or in registered bridges — restate through the surface API, or tag as @[cc_surface_bridge] with a recorded justification. -/
#guard_msgs in
#cc_surface_check Test.plantedEdist

/-- error: §10.11 violation: the statement of `RandomSystems.CC.Lint.Test.plantedUpdate` shows kernel vocabulary: [Function.update].  Kernel names belong in definition bodies or in registered bridges — restate through the surface API, or tag as @[cc_surface_bridge] with a recorded justification. -/
#guard_msgs in
#cc_surface_check Test.plantedUpdate

/-- error: §10.11 violation: the statement of `RandomSystems.CC.Lint.Test.plantedHEq` shows kernel vocabulary: [HEq].  Kernel names belong in definition bodies or in registered bridges — restate through the surface API, or tag as @[cc_surface_bridge] with a recorded justification. -/
#guard_msgs in
#cc_surface_check Test.plantedHEq

end RandomSystems.CC.Lint
