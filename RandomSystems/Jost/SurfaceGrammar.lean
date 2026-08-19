/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import RandomSystems.Jost.SurfaceTactics
import RandomSystems.Jost.SurfaceNames

/-!
# The authoring surface, part 4: the pseudocode grammar

`resource` compiles one Fig.-2.2 declaration into the whole stack of
objects an author previously wrote by hand: the interface inductive, one
input inductive per interface, the `Interfaces` record, the computable
realization (`Name.machine`), and the `Resource.ofRealization` /
`Resource.sampleInit` application — tagged `@[cc_surface]`, with the
declared (or default) presentation attributes of `SurfaceNames`.

```
resource Counter where
  interface user
    input ping : Unit
  interface audit
    input read : Nat
  state n : Nat := 0
  on user.ping => do set n := n + 1; return ()
  on audit.read => return n
  display "CNT"
```

**Semantics contract.**  The elaboration produces EXACTLY a
`Resource.ofRealization` (resp. `sampleInit`) term.  `do`/`set`/`return`
are macro sugar for pure state-tuple threading — no `Monad` instance
exists anywhere; `set f := e` becomes a `let`, `return a` becomes
`some (current-state-tuple, a)`.  The partiality contract survives as
grammar: `reject` elaborates to `none` (blocking divergence) and
`require p else v` to the error-value branch with **rollback** semantics
(on failure the state reverts to the query's entry state); nothing is
totalized on the author's behalf, and a missing handler for a declared
input is a compile error naming it.

**Presentation clauses** (all optional, trailing): `display "…"` (the
paper name — glyphs welcome, MaRuTa12 §1.3 names channels `•—→•`),
`latex "…"`, `role assumed|constructed|converter|simulator|game`.  They
are emitted as the `SurfaceNames` attributes on the generated resource;
an omitted `role` defaults to `assumed` (a declared resource is an
assumed functionality until a construction says otherwise).

**Reservation-free parsing.**  The clause keywords (`interface`, `input`,
`state`, `on`, `set`, `require`, `reject`, `sample`, `display`, `latex`,
`role`) are `nonReservedSymbol` parsers: importing files keep every one
of these words as ordinary identifiers (receipts below use `state` and
`interface` as binders).  Two ingredients replace the v1 reservation,
each addressing one recorded failure mode: raw-kind elaborator dispatch
(never quotation patterns — those misparsed soft keywords), and
`many1Indent` clause lists (the enclosing position guard stops a trailing
term from swallowing the next line's clause head — v1's `Unit interface`
application greed).  The only reserved word this module adds is the
command head `resource` itself (command dispatch is token-indexed; an
ident-led command parser is never tried — probed, not assumed).

**v1 scope** (each relaxable later): all inputs of one interface must
declare the same output type (the kernel's answer fibre is per-interface;
declare a shared sum type when they differ — the elaborator says so);
handler bodies are `;`-separated statements; state is threaded as a
right-nested tuple of the `state` lines (no structure is generated);
`sample x : X` draws one uniform seed (`Fintype`/`Nonempty` obligations
surface at the declaration).

**Hygiene note.**  State-field and payload names bind user-written
occurrences by design (they are the author's own idents, spliced
verbatim); the internal state/query binders use reserved `__cc_`-prefixed
names.
-/

namespace RandomSystems.CC.Grammar

open Lean Elab Command

/-! ## Non-reserved keyword parsers

`nonReservedSymbol w true` matches the identifier `w` without entering it
in the token table — importing files keep the word as an identifier. -/

open Lean.Parser in
def interfaceKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "interface" true
open Lean.Parser in
def inputKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "input" true
open Lean.Parser in
def stateKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "state" true
open Lean.Parser in
def onKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "on" true
open Lean.Parser in
def setKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "set" true
open Lean.Parser in
def requireKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "require" true
open Lean.Parser in
def rejectKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "reject" true
open Lean.Parser in
def sampleKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "sample" true
open Lean.Parser in
def displayKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "display" true
open Lean.Parser in
def latexKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "latex" true
open Lean.Parser in
def roleKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "role" true

/-! ## Syntax -/

declare_syntax_cat cc_payload
syntax (name := ccPayload) "(" ident " : " term ")" : cc_payload

declare_syntax_cat cc_input
syntax (name := ccInput) inputKw ident cc_payload* " : " term : cc_input

declare_syntax_cat cc_ifc
syntax (name := ccIfc) interfaceKw ident many1Indent(cc_input) : cc_ifc

declare_syntax_cat cc_stmt
syntax (name := ccStmtSet) setKw ident " := " term : cc_stmt
syntax (name := ccStmtReturn) "return " term : cc_stmt
syntax (name := ccStmtReject) rejectKw : cc_stmt
syntax (name := ccStmtRequire) requireKw term " else " term : cc_stmt

declare_syntax_cat cc_handler
syntax (name := ccHandler) onKw ident ident* " => " ("do")? sepBy1(cc_stmt, ";") : cc_handler

declare_syntax_cat cc_state_decl
syntax (name := ccStateDecl) stateKw ident " : " term " := " term : cc_state_decl

declare_syntax_cat cc_sample_decl
syntax (name := ccSampleDecl) sampleKw ident " : " term : cc_sample_decl

syntax (name := ccResourceCmd)
  (docComment)? "resource " ident " where "
    many1Indent(cc_ifc) manyIndent(cc_state_decl) manyIndent(cc_sample_decl)
    many1Indent(cc_handler)
    (displayKw str)? (latexKw str)? (roleKw ident)? : command

/-! ## Elaboration

Raw-kind dispatch throughout: soft-keyword categories misparse inside
quotation *patterns*, so the sub-syntax is destructured by node kind and
child index (each rule is named; the shapes are fixed by the `syntax`
declarations above). -/

private structure InputDecl where
  name : Ident
  payloads : Array (Ident × Term)
  out : Term
  deriving Inhabited

private structure IfcDecl where
  name : Ident
  inputs : Array InputDecl
  deriving Inhabited

private structure StateDecl where
  name : Ident
  ty : Term
  init : Term
  deriving Inhabited

private structure HandlerDecl where
  ifaceName : Name
  inputName : Name
  payloadIds : Array Ident
  stmts : Array Syntax
  ref : Syntax
  deriving Inhabited

open Lean Elab Command in
/-- Right-nested tuple TYPE of the state fields (`Unit` when none). -/
private def stateTupleTy (states : Array StateDecl) : CommandElabM Term := do
  if states.isEmpty then `(Unit)
  else
    let mut acc : Term := states.back!.ty
    for s in states.pop.reverse do
      acc ← `($(s.ty) × $acc)
    return acc

open Lean Elab Command in
/-- Right-nested tuple TERM from per-field terms (`()` when none). -/
private def stateTuple (parts : Array Term) : CommandElabM Term := do
  if parts.isEmpty then `(())
  else if parts.size == 1 then return parts[0]!
  else `(($(parts[0]!), $(parts[1:].toArray),*))

open Lean Elab Command in
/-- Compile a handler body.  `entry` is the untouched entry state (for
`require` rollback); the current state is carried by the let-bound field
idents, rebuilt as a tuple at `return`. -/
private partial def compileStmts (states : Array StateDecl) (entry : Term) :
    List Syntax → CommandElabM Term
  | [] => throwError "resource: a handler must end with `return …` or `reject`"
  | stmt :: rest => do
    if stmt.getKind == ``ccStmtReturn then
      unless rest.isEmpty do
        throwErrorAt stmt "resource: unreachable statements after `return`"
      let current ← stateTuple (states.map fun s => (s.name : Term))
      let answer : Term := ⟨stmt[1]⟩
      `(some ($current, $answer))
    else if stmt.getKind == ``ccStmtReject then
      unless rest.isEmpty do
        throwErrorAt stmt "resource: unreachable statements after `reject`"
      `((none : Option _))
    else if stmt.getKind == ``ccStmtSet then
      let f : Ident := ⟨stmt[1]⟩
      let e : Term := ⟨stmt[3]⟩
      unless states.any (fun s => s.name.getId == f.getId) do
        throwErrorAt f "resource: `set {f.getId}` — not a declared `state` field"
      let restT ← compileStmts states entry rest
      `(let $f := $e
        $restT)
    else if stmt.getKind == ``ccStmtRequire then
      let p : Term := ⟨stmt[1]⟩
      let v : Term := ⟨stmt[3]⟩
      let restT ← compileStmts states entry rest
      `(if $p then $restT else some ($entry, $v))
    else
      throwErrorAt stmt "resource: unrecognized statement"

open Lean Elab Command in
/-- Emit the `SurfaceNames` presentation attributes from the optional
trailing clauses; `defaultRole` when no `role` clause is given. -/
def emitPresentation (target : Ident) (dispOpt latexOpt roleOpt : Syntax)
    (defaultRole : Name) : CommandElabM Unit := do
  -- each optional clause is `(kw payload)?`: a flattened nullNode
  -- [kwNode, payload] when present, empty when absent
  if dispOpt.getArgs.size > 0 then
    let s : StrLit := ⟨dispOpt.getArgs.back!⟩
    elabCommand (← `(command| attribute [cc_display $s] $target))
  if latexOpt.getArgs.size > 0 then
    let s : StrLit := ⟨latexOpt.getArgs.back!⟩
    elabCommand (← `(command| attribute [cc_latex $s] $target))
  let roleId ←
    if roleOpt.getArgs.size > 0 then pure (⟨roleOpt.getArgs.back!⟩ : Ident)
    else pure (mkIdent defaultRole)
  elabCommand (← `(command| attribute [cc_role $roleId:ident] $target))

open Lean Elab Command in
@[command_elab ccResourceCmd]
def elabCcResource : CommandElab := fun stx => do
  -- shape: [doc?, atom, name, "where", ifcs+, states*, sample?, handlers+,
  --         display?, latex?, role?]
  let name : Ident := ⟨stx[2]⟩
  let base := name.getId
  -- interfaces
  let mut ifcs : Array IfcDecl := #[]
  for i in stx[4].getArgs do
    unless i.getKind == ``ccIfc do throwErrorAt i "resource: malformed interface"
    let iname : Ident := ⟨i[1]⟩
    let mut inputs : Array InputDecl := #[]
    for inp in i[2].getArgs do
      unless inp.getKind == ``ccInput do
        throwErrorAt inp "resource: malformed input"
      let mut payloads : Array (Ident × Term) := #[]
      for pl in inp[2].getArgs do
        payloads := payloads.push (⟨pl[1]⟩, ⟨pl[3]⟩)
      inputs := inputs.push ⟨⟨inp[1]⟩, payloads, ⟨inp[4]⟩⟩
    ifcs := ifcs.push ⟨iname, inputs⟩
  -- per-interface output coherence (the kernel's answer fibre is per-interface)
  for ifc in ifcs do
    let out0 := ifc.inputs[0]!.out
    for inp in ifc.inputs do
      unless toString inp.out == toString out0 do
        throwErrorAt inp.out
          "resource: interface `{ifc.name.getId}` declares inputs with different output types ({toString out0} vs {toString inp.out}); the answer fibre is per-interface — declare one shared output type (e.g. a sum) for this interface"
  -- states
  let mut states : Array StateDecl := #[]
  for st in stx[5].getArgs do
    unless st.getKind == ``ccStateDecl do
      throwErrorAt st "resource: malformed state"
    states := states.push ⟨⟨st[1]⟩, ⟨st[3]⟩, ⟨st[5]⟩⟩
  -- sample? (parsed as an indent-guarded list so the type term cannot
  -- swallow the next clause line; arity is enforced here)
  let sampleArgs := stx[6].getArgs
  if sampleArgs.size > 1 then
    throwErrorAt sampleArgs[1]! "resource: at most one `sample` clause"
  let sampleOpt : Option (Ident × Term) :=
    if h : sampleArgs.size = 1 then
      let sm := sampleArgs[0]
      some (⟨sm[1]⟩, ⟨sm[3]⟩)
    else none
  -- handlers
  let mut handlers : Array HandlerDecl := #[]
  for h in stx[7].getArgs do
    unless h.getKind == ``ccHandler do
      throwErrorAt h "resource: malformed handler"
    let target : Ident := ⟨h[1]⟩
    let comps := target.getId.components
    unless comps.length == 2 do
      throwErrorAt target "resource: handler target must be `interface.input`"
    let payloadIds : Array Ident := h[2].getArgs.map (⟨·⟩)
    let stmts := h[5].getSepArgs
    handlers := handlers.push ⟨comps[0]!, comps[1]!, payloadIds, stmts, h⟩
  -- coverage and arity
  for ifc in ifcs do
    for inp in ifc.inputs do
      let matching := handlers.filter fun h =>
        h.ifaceName == ifc.name.getId && h.inputName == inp.name.getId
      if matching.size == 0 then
        throwError "resource: no handler for declared input `{ifc.name.getId}.{inp.name.getId}` — every input must be decided (partiality contract)"
      else if matching.size > 1 then
        throwError "resource: duplicate handlers for `{ifc.name.getId}.{inp.name.getId}`"
      else
        let h := matching[0]!
        unless h.payloadIds.size == inp.payloads.size do
          throwErrorAt h.ref
            "resource: handler `{ifc.name.getId}.{inp.name.getId}` binds {h.payloadIds.size} payload(s) but the input declares {inp.payloads.size}"
  for h in handlers do
    unless ifcs.any fun ifc =>
        ifc.name.getId == h.ifaceName &&
          ifc.inputs.any (·.name.getId == h.inputName) do
      throwErrorAt h.ref
        "resource: handler `{h.ifaceName}.{h.inputName}` does not match any declared input"
  -- 1. the interface inductive
  let ifcTypeId := mkIdentFrom name (base ++ `Ifc)
  let ifcCtors ← ifcs.mapM fun ifc =>
    `(Lean.Parser.Command.ctor| | $(ifc.name):ident)
  elabCommand (← `(command|
    inductive $ifcTypeId:ident where $ifcCtors:ctor*
      deriving DecidableEq))
  -- 2. per-interface input inductives (constructors as arrow types)
  for ifc in ifcs do
    let inpTypeId := mkIdentFrom ifc.name (base ++ ifc.name.getId)
    let ctors ← ifc.inputs.mapM fun inp => do
      let mut ty : Term := inpTypeId
      for (_, pt) in inp.payloads.reverse do
        ty ← `($pt → $ty)
      `(Lean.Parser.Command.ctor| | $(inp.name):ident : $ty)
    elabCommand (← `(command|
      inductive $inpTypeId:ident where $ctors:ctor*))
  -- 3. the Interfaces record
  let ifacesId := mkIdentFrom name (base ++ `ifaces)
  let inAlts ← ifcs.mapM fun ifc => do
    let ctor := mkIdent (base ++ `Ifc ++ ifc.name.getId)
    let inpTy := mkIdent (base ++ ifc.name.getId)
    `(Lean.Parser.Term.matchAltExpr| | $ctor:ident => $inpTy:ident)
  let outAlts ← ifcs.mapM fun ifc => do
    let ctor := mkIdent (base ++ `Ifc ++ ifc.name.getId)
    `(Lean.Parser.Term.matchAltExpr| | $ctor:ident => $(ifc.inputs[0]!.out))
  elabCommand (← `(command|
    def $ifacesId:ident : RandomSystems.CC.Interfaces :=
      { Iface := $ifcTypeId
        In := fun i => match i with $inAlts:matchAlt*
        Out := fun i => match i with $outAlts:matchAlt* }))
  -- 4. the step function
  let sId := mkIdent `__cc_state
  let qId := mkIdent `__cc_query
  let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for ifc in ifcs do
    for inp in ifc.inputs do
      let h := (handlers.filter fun h =>
        h.ifaceName == ifc.name.getId && h.inputName == inp.name.getId)[0]!
      let ifcCtor := mkIdent (base ++ `Ifc ++ ifc.name.getId)
      let inpCtor := mkIdent (base ++ ifc.name.getId ++ inp.name.getId)
      let pat ←
        if h.payloadIds.isEmpty then
          `(⟨$ifcCtor:ident, $inpCtor:ident⟩)
        else
          let pids := h.payloadIds
          `(⟨$ifcCtor:ident, $inpCtor:ident $pids:ident*⟩)
      let body ← compileStmts states (sId : Term) h.stmts.toList
      let bodyWithFields ←
        if states.isEmpty then pure body
        else if states.size == 1 then
          `(let $(states[0]!.name):ident := $sId
            $body)
        else do
          let pats := states.map fun s => (s.name : Term)
          `(let ($(pats[0]!), $(pats[1:].toArray),*) := $sId
            $body)
      arms := arms.push (← `(Lean.Parser.Term.matchAltExpr|
        | $pat:term => $bodyWithFields))
  let stepFun ← `(fun $sId $qId =>
    match $qId:ident with $arms:matchAlt*)
  -- 5. the resource
  let initParts := states.map fun s => s.init
  let initTerm ← stateTuple initParts
  let stTy ← stateTupleTy states
  -- the underlying computable realization is emitted as `Name.machine`
  -- (a seed-indexed family under a `sample` clause) — `#simulate` and
  -- grammar-less consumers take it directly
  let machineId := mkIdentFrom name (base ++ `machine)
  match sampleOpt with
  | none =>
      elabCommand (← `(command|
        def $machineId:ident : ($ifacesId).Realization :=
          ⟨$stTy, $initTerm, $stepFun⟩))
      elabCommand (← `(command|
        @[cc_surface] noncomputable def $name:ident :
            RandomSystems.CC.Resource $ifacesId :=
          RandomSystems.CC.Resource.ofRealization $machineId))
  | some (sv, sTy) =>
      elabCommand (← `(command|
        def $machineId:ident : ($sTy) → ($ifacesId).Realization :=
          fun $sv:ident => ⟨$stTy, $initTerm, $stepFun⟩))
      elabCommand (← `(command|
        @[cc_surface] noncomputable def $name:ident :
            RandomSystems.CC.Resource $ifacesId :=
          RandomSystems.CC.Resource.sampleInit $machineId
            (RandomSystems.Dist.uniform $sTy)))
  -- 6. the doc comment, when given, lands on the resource itself
  if stx[0].getArgs.size > 0 then
    let dc : TSyntax ``Lean.Parser.Command.docComment := ⟨stx[0][0]⟩
    elabCommand (← `(command| $dc:docComment add_decl_doc $name))
  -- 7. presentation attributes (default role: a declared resource is an
  -- assumed functionality)
  emitPresentation name stx[8] stx[9] stx[10] `assumed

end RandomSystems.CC.Grammar

/-! ## Receipts -/

namespace RandomSystems.CC.GrammarTests

open RandomSystems.CC
open RandomSystems (Dist)

/-! Receipt 0 (reservation-free): every clause keyword is an ordinary
identifier for importers — including `state`, v1's named casualty. -/
example (state : Nat) : Nat := state
example (interface input : Bool) : Bool := interface && input
def on : Nat := 1
def sample : Nat := on
def display : Nat := sample

/-! Receipt 1: the showcase counter, authored in the grammar. -/
/-- The counting resource of Fig. 2.2. -/
resource Counter where
  interface user
    input ping : Unit
  interface audit
    input read : Nat
  state n : Nat := 0
  on user.ping => do set n := n + 1; return ()
  on audit.read => return n

#cc_surface_check Counter

-- the default role lands (`assumed`):
/-- info: some (RandomSystems.CC.Names.Role.assumed) -/
#guard_msgs in
#eval show Lean.CoreM _ from
  return RandomSystems.CC.Names.role? (← Lean.getEnv) ``Counter

-- the doc comment lands on the resource itself:
/-- info: some "The counting resource of Fig. 2.2. " -/
#guard_msgs in
#eval show Lean.CoreM _ from do
  Lean.findDocString? (← Lean.getEnv) ``Counter

/-! Receipt 2: the grammar-authored counter equals a hand-authored twin. -/
noncomputable def twin : Resource Counter.ifaces :=
  Resource.ofState (0 : Nat) fun n query =>
    match query with
    | ⟨.user, .ping⟩ => some (n + 1, ())
    | ⟨.audit, .read⟩ => some (n, n)

theorem counter_eq_twin : Counter = twin := by
  bisim_cases (fun a b => a = b) with [Counter.machine]

/-! Receipt 3: a `sample` clause — the fair coin, with the full
presentation clause set (glyph display name per MaRuTa12 §1.3). -/
resource GrammarCoin where
  interface holder
    input look : Bool
  sample b : Bool
  on holder.look => return b
  display "•══•"
  latex "\\mathsf{KEY}"
  role assumed

#cc_surface_check GrammarCoin

-- the declared presentation attributes land:
/-- info: (some "•══•", some "\\mathsf{KEY}") -/
#guard_msgs in
#eval show Lean.CoreM _ from do
  let env ← Lean.getEnv
  return (RandomSystems.CC.Names.displayName? env ``GrammarCoin,
    RandomSystems.CC.Names.latexName? env ``GrammarCoin)

/-! Receipt 4: `require`/`reject` partiality forms in one cell. -/
resource OneShot where
  interface writer
    input put (v : Bool) : Option Bool
  state stored : Option Bool := none
  on writer.put v => do
    require stored = none else none;
    set stored := some v;
    return some v

#cc_surface_check OneShot

end RandomSystems.CC.GrammarTests
