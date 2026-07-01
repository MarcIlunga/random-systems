/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.ExprLatex
import Informalization.FTL
import Informalization.Ontology
import Informalization.Serialize

/-!
# Frontend — a REAL `Expr → prose` path (DESIGN §4(A), §7)

The honest "one real path" (Round-1 finding 3): it informalizes a *real* Lean
declaration — its type and its elaborated proof **term** — using the real
`exprToLatex` (no stubs on the load-bearing pieces).

We use the **proof-term decompiler** direction (the talk's core component, slide
65): rather than walking a tactic `InfoTree`, we read the kernel-checked proof
term from the environment and decompile its outer structure (`fun … => …`
binders → Fix/Assume steps; the body's head, a named lemma → a "By …" citation).
Full *tactic*-`InfoTree` recovery that preserves the surface tactic tree is the
documented seam (DESIGN §7); the proof **term** path here is real.

To get readable output, free variables are replaced by named constants of their
user-facing names before rendering (so `g ∘ f` prints as `g \circ f`, not as
internal `_uniq` names).

Entry points:
* `informalizeStatement` / `informalizeProofTerm` / `informalizeConst`
* the `#informalize ident` command — prints the document JSON.
-/

open Lean Meta Elab

namespace Informalization.Frontend

open Informalization

/-- Replace each telescope fvar by a `const` of its user name, so the pure
`exprToLatex` prints readable identifiers. -/
def substNamed (xs : Array Expr) (e : Expr) : MetaM Expr := do
  let mut r := e
  for x in xs do
    let nm := (← x.fvarId!.getDecl).userName
    r := r.replaceFVarId x.fvarId! (mkConst (Name.mkSimple nm.toString))
  return r

/-- LaTeX of an expression, with telescope fvars rendered by their names. -/
def latexOf (xs : Array Expr) (e : Expr) : MetaM String := do
  return exprToLatex (← substNamed xs e)

/-- Binder classification by type. -/
inductive BinderClass | type | func | hyp | data
  deriving DecidableEq, Repr, Inhabited

def classifyBinder (ty : Expr) : MetaM BinderClass := do
  if (← isProp ty) then return .hyp
  if ty.isSort then return .type
  match ty with
  | .forallE _ _ b _ => if !b.hasLooseBVar 0 then return .func else return .data
  | _ => return .data

/-- Recognise `Function.Injective f`, returning `f`. -/
def injectiveArg? (ty : Expr) : Option Expr :=
  match ty.getAppFn with
  | .const ``Function.Injective _ =>
    let args := ty.getAppArgs
    if args.size ≥ 1 then some args[args.size - 1]! else none
  | _ => none

/-- Look up an accumulated adjective list by key in an assoc array. -/
def adjLookup (m : Array (String × Array String)) (key : String) : Array String :=
  (m.find? (·.1 == key)).map (·.2) |>.getD #[]

/-- Informalize a proposition into an `FTL.FStatement`: telescope the binders
into entity introductions (types/functions), attach "injective" as an adjective
when a hypothesis says so, and render the conclusion as a typeset atom. -/
def informalizeStatement (type : Expr) : MetaM FTL.FStatement := do
  -- NON-reducing: keep `Function.Injective f` intact so it becomes an adjective,
  -- and keep the conclusion as `Injective (g ∘ f)` rather than unfolding it.
  forallTelescope type fun xs body => do
    -- pass 1: hypotheses contribute adjectives to their subject (by name)
    let mut adjs : Array (String × Array String) := #[]
    for x in xs do
      let ldecl ← x.fvarId!.getDecl
      if let some f := injectiveArg? ldecl.type then
        let key ← latexOf xs f
        adjs := adjs.push (key, (adjLookup adjs key).push "injective")
    -- pass 2: build intros for type/function binders
    let mut intros : Array Grammar.Intro := #[]
    for x in xs do
      let ldecl ← x.fvarId!.getDecl
      let cls ← classifyBinder ldecl.type
      if cls == .type || cls == .func then
        let (sg, pl) := if cls == .type then ("type", "types") else ("function", "functions")
        let nm := ldecl.userName.toString
        -- for a function binder, surface its arrow type ("f : α → β"), Unicode,
        -- built from domain/codomain so it stays text (matches Kyle's slide).
        let tyStr ←
          if cls == .func then
            match ldecl.type with
            | .forallE _ d c _ => do
                let ds ← latexOf xs d
                let cs ← latexOf xs c
                pure (ds ++ " → " ++ cs)
            | _ => pure ""
          else pure ""
        intros := intros.push
          { name := nm, nounSingular := sg, nounPlural := pl,
            adjectives := (adjLookup adjs nm).toList, typeStr := tyStr }
    -- Render the conclusion as a clean predicate when it is `Injective arg`
    -- (an ontology move: `Injective h` → "h is injective"), else typeset it.
    let concl ←
      match injectiveArg? body with
      | some arg => do
        let a ← latexOf xs arg
        pure (a ++ "\\ \\text{is injective}")
      | none => latexOf xs body
    return FTL.FStatement.implies (FTL.FStatement.lets intros.toList)
      (FTL.FStatement.atom concl none)

/-- Narrate a proof *term* that proves an equation. Recognizes the
injectivity-application pattern `hk eqProof` where `hk : Function.Injective k`:
this de-applies the equation, so it narrates as "Since k is injective, we get
⟨resulting equation⟩". Recurses inner-first; a bare hypothesis contributes no
step (it is the stated assumption); any other term concludes with its goal. -/
partial def narrateProof (xs : Array Expr) (e : Expr) : MetaM (Array FTL.FStep) := do
  let lx : Expr → MetaM String := fun t => return exprToLatex (← substNamed xs t)
  match e.getAppFn with
  | .fvar fid =>
    match injectiveArg? (← fid.getDecl).type with
    | some k =>
      let args := e.getAppArgs
      if args.size ≥ 1 then
        let pre ← narrateProof xs args[args.size - 1]!
        let concl ← lx (← inferType e)
        let kStr ← lx k
        return pre.push
          { frame := FTL.Frame.since #[s!"{kStr} is injective"] concl, salience := .routine }
      else
        return #[]
    | none => return #[]            -- a bare hypothesis: already assumed
  | _ =>
    let concl ← lx (← inferType e)
    return #[{ frame := FTL.Frame.weConclude concl #[], salience := .pivotal }]

/-- Decompile a proof term into proof steps. The statement's own binders (the
first `∀`-binders of the type) are NOT re-introduced — they belong to the
statement. Only the proof-specific binders are narrated (data → "Fix …",
hypotheses → "Assume ⟨type⟩"), then the body via `narrateProof`. -/
def informalizeProofTerm (type val : Expr) : MetaM (Array FTL.FStep) := do
  let nStmt ← forallTelescope type (fun ys _ => pure ys.size)
  lambdaTelescope val fun xs body => do
    let lx : Expr → MetaM String := fun t => return exprToLatex (← substNamed xs t)
    let proofBinders := xs.extract nStmt xs.size
    let mut steps : Array FTL.FStep := #[]
    -- data binders are introduced with their element type ("Let a and b be
    -- elements of α"); hypotheses as "Assume ⟨type⟩".
    let mut dataVars : Array String := #[]
    let mut dataTy : String := ""
    for x in proofBinders do
      let ld ← x.fvarId!.getDecl
      if (← classifyBinder ld.type) == .hyp then
        if !dataVars.isEmpty then
          steps := steps.push { frame := FTL.Frame.letElems dataVars dataTy, salience := .routine }
          dataVars := #[]
        steps := steps.push { frame := FTL.Frame.assume (← lx ld.type), salience := .routine }
      else
        if dataVars.isEmpty then dataTy := (← lx ld.type)
        dataVars := dataVars.push ld.userName.toString
    if !dataVars.isEmpty then
      steps := steps.push { frame := FTL.Frame.letElems dataVars dataTy, salience := .routine }
    steps := steps ++ (← narrateProof xs body)
    return steps

/-- A human-facing title for a declaration: its docstring's first sentence if it
has one, else the de-underscored name (so `inj_comp` reads "inj comp", not the
raw identifier). -/
def declTitle (nm : Name) : MetaM String := do
  match (← findDocString? (← getEnv) nm) with
  | some doc =>
      -- first sentence / first line of the docstring
      let line := (doc.trim.splitOn "\n").headD doc.trim
      let sentence := (line.splitOn ". ").headD line
      return (sentence.replace "`" "").trim
  | none =>
      let pretty := nm.toString.replace "_" " "
      return s!"Theorem  {pretty}"

/-- Informalize a whole declaration by name into an `FTL.FDocument`. -/
def informalizeConst (nm : Name) : MetaM FTL.FDocument := do
  let ci ← getConstInfo nm
  let statement ← informalizeStatement ci.type
  let title ← declTitle nm
  let proof ←
    match ci.value? with
    | some v => informalizeProofTerm ci.type v
    | none   => pure #[{ frame := FTL.Frame.fallback "(no proof term)" }]
  return { title, statement, proof }

end Informalization.Frontend

namespace Informalization

open Lean Elab Command

/-- `#informalize ident` — informalize a declaration and print its document JSON
(ready to paste into `web/index.html`). A real `Expr → prose → JSON` path. -/
syntax (name := informalizeCmd) "#informalize " ident : command

@[command_elab informalizeCmd]
def elabInformalize : CommandElab := fun stx => do
  match stx with
  | `(#informalize $i:ident) => do
    let nm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo i
    let doc ← liftTermElabM <| Frontend.informalizeConst nm
    let expl := FTL.realizeDocument doc
    let json := Lean.Json.mkObj [
      ("title", Lean.Json.str doc.title),
      ("body", expl.toJson)]
    logInfo m!"{json.pretty}"
  | _ => throwUnsupportedSyntax

end Informalization
