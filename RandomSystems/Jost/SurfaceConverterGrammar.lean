/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceGrammar
import RandomSystems.Jost.SurfaceAttach

/-!
# The authoring surface, part 5: the converter grammar

`converter` compiles one Def-2.2.2 converter declaration — outer input
clauses, each a fixed sequence of inner `call`s and then an answer — into
`Converter.ofRounds`, with the causality/finiteness judgment **synthesized**:

```
converter maskBit : MaskService.plain ⇒ MaskService.masked over maskServices where
  on send m =>
    let c ← call send (xor m true);
    return c
  display "mask"
```

**Reservation-free parsing** as in `SurfaceGrammar`: `on`, `set`, `call`,
`over`, `state`, `display`, `latex`, `role` are `nonReservedSymbol`
parsers — importers keep them as identifiers; the only word this module
reserves is the command head `converter`.  Because `over` is not a token,
the target-service slot before it is a `term:max` (a dotted service name
parses as one identifier; parenthesize anything larger).  The optional
trailing `display "…"`/`latex "…"`/`role …` clauses are emitted as the
`SurfaceNames` attributes; an omitted `role` defaults to `converter`.

**What is synthesized per clause.**  The elaborator counts the `call` lines
of each clause and emits: the per-input `arity` function (`Name.arity`), the
round script (`Name.script`, a `RoundN` value — see below), the finite
budget with its proof (`Name.arity_le`), and the packaged converter
(`Name := Converter.ofScript …`).  Def 2.2.2's discipline proof is NOT
generated per declaration: it is the once-proven generic lemma
`RoundN.step_inl_iff`, applied inside `Converter.ofScript` — the grammar
produces only data (matches and literals), so a declaration that elaborates
is correct-or-nothing.

**The v1 call discipline, as a type.**  `RoundN X Y A k` is a round of
EXACTLY `k` inner calls: later payloads may use earlier answers, the final
answer may use all of them, but the NUMBER of calls is the index — the
carrier's `ofHistoryStep` boundary condition (`calls` independent of the
answers received) is structural.  An `if … then … else …` STATEMENT between
calls is parsed and rejected with the discipline error (branch inside a
call's payload or the `return` term instead — that is expressiveness the
kernel has; branching the call STRUCTURE is v2, and needs the per-path
`AnswersWithinDepth`/`IsDDCEventually` side of `StepRealization`).

**Converter state is a fold over the outside history.**  Declared `state`
fields are compiled to `Name.stateAt : List (In target) → σ`, a `foldl` of
the clauses' `set`-updates over the PREVIOUS outer inputs.  This is
presentation, not a new object: the kernel converter is history-indexed
(Def 2.2.2's own strength), and a fold is how a state reading of it is
spelled.  Consequently `set` may read the declared fields and the clause's
payload but NOT call answers — `ofHistoryStep` hands each round only its
own answer segment, so answer-dependent state does not exist at this
carrier; the elaborator rejects it with a domain error.

**v1 scope**: clause dispatch is by constructor of the (inductive) input
alphabet; statements are `;`-separated as in `cc_resource`; every input
constructor needs a clause (Lean's exhaustiveness error reports a missing
one on the generated match).
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource

/-! ## Fixed-arity rounds, and the once-proven discipline -/

/-- A round of exactly `k` inner calls: later payloads may depend on
earlier answers, the final outside answer on all of them.  The arity is
the index, so a `RoundN` value CANNOT branch its call count on answers —
v1's discipline as a type. -/
def RoundN (X Y A : Type) : Nat → Type
  | 0 => A
  | k + 1 => X × (Y → RoundN X Y A k)

namespace RoundN

variable {X Y A : Type}

/-- Drive one round: with the answers received so far, the next move —
the next call while answers remain due, the outside answer afterwards. -/
def step : {k : Nat} → RoundN X Y A k → List Y → X ⊕ A
  | 0, answer, _ => Sum.inr answer
  | _ + 1, round, [] => Sum.inl round.1
  | _ + 1, round, y :: ys => step (round.2 y) ys

@[simp] theorem step_zero (answer : A) (ys : List Y) :
    step (X := X) (k := 0) answer ys = Sum.inr answer := rfl

@[simp] theorem step_succ_nil {k : Nat} (round : RoundN X Y A (k + 1)) :
    step round [] = Sum.inl round.1 := rfl

@[simp] theorem step_succ_cons {k : Nat} (round : RoundN X Y A (k + 1))
    (y : Y) (ys : List Y) :
    step round (y :: ys) = step (round.2 y) ys := rfl

/-- **Def 2.2.2's boundary condition, proven once**: a round emits an inner
call exactly while fewer answers than its arity have arrived. -/
theorem step_inl_iff : {k : Nat} → (round : RoundN X Y A k) →
    (ys : List Y) →
    ((∃ query, step round ys = Sum.inl query) ↔ ys.length < k)
  | 0, answer, ys => by simp
  | _ + 1, round, [] => by simp
  | k + 1, round, y :: ys => by
      simpa [Nat.succ_lt_succ_iff] using step_inl_iff (round.2 y) ys

end RoundN

namespace Converter

variable {S : Services} {source target : S.Service}

/-- **The script endpoint the grammar targets**: an arity per outside
input and a `RoundN` script per (previous outside history, current input)
give a converter, with the discipline discharged by `RoundN.step_inl_iff`
and the budget by `arity_le` — no per-declaration proof exists. -/
noncomputable def ofScript (arity : S.In target → Nat)
    (script : (history : List (S.In target)) → (inp : S.In target) →
      RoundN (S.In source) (S.Out source) (S.Out target) (arity inp))
    (budget : Nat) (arity_le : ∀ inp, arity inp ≤ budget) :
    Converter S source target :=
  Converter.ofRounds
    (fun history nonempty answers =>
      RoundN.step (script history.dropLast (history.getLast nonempty)) answers)
    (fun history => (history.getLast?.map arity).getD 0)
    (by
      intro history nonempty answers
      dsimp only
      rw [List.getLast?_eq_some_getLast nonempty]
      simpa using RoundN.step_inl_iff _ answers)
    ⟨budget, fun history => by
      cases hlast : history.getLast? with
      | none => simp [hlast]
      | some inp => simpa [hlast] using arity_le inp⟩

end Converter

end RandomSystems.CC

namespace RandomSystems.CC.Grammar

open Lean Elab Command

/-! ## Syntax

The clause keywords reuse `SurfaceGrammar`'s non-reserved parsers
(`onKw`, `setKw`, …); `call` and `over` get their own here. -/

open Lean.Parser in
def callKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "call" true
open Lean.Parser in
def overKw : Lean.Parser.Parser := leading_parser nonReservedSymbol "over" true

declare_syntax_cat ccv_stmt
syntax (name := ccvCall) "let " ident " ← " callKw ident (term:max)* : ccv_stmt
syntax (name := ccvSet) setKw ident " := " term : ccv_stmt
syntax (name := ccvReturn) "return " term : ccv_stmt
/-- Parsed only to be rejected with the discipline error. -/
syntax (name := ccvIf) "if " term " then " ccv_stmt " else " ccv_stmt : ccv_stmt

declare_syntax_cat ccv_handler
syntax (name := ccvHandler)
  onKw ident ident* " => " ("do")? sepBy1(ccv_stmt, ";") : ccv_handler

syntax (name := ccConverterCmd)
  (docComment)? "converter " ident " : " term " ⇒ " term:max overKw term " where "
    manyIndent(cc_state_decl) many1Indent(ccv_handler)
    (displayKw str)? (latexKw str)? (roleKw ident)? : command

/-! ## Elaboration -/

private structure ConvHandler where
  ctorName : Name
  payloadIds : Array Ident
  stmts : Array Syntax
  ref : Syntax
  deriving Inhabited

private structure ConvState where
  name : Ident
  ty : Term
  init : Term
  deriving Inhabited

/-- Idents occurring anywhere in a syntax tree. -/
private partial def identsOf (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => #[n]
  | .node _ _ args => args.foldl (fun acc a => acc ++ identsOf a) #[]
  | _ => #[]

/-- Split a clause body into (interleaved set/call prefix, return term);
enforce the two domain rules (no structural branching; no answer-reading
`set`). -/
private def analyzeClause (stmts : Array Syntax) :
    CommandElabM (Array Syntax × Term) := do
  let mut prefixStmts : Array Syntax := #[]
  let mut answerIds : Array Name := #[]
  let mut ret? : Option Term := none
  for stmt in stmts do
    if ret?.isSome then
      throwErrorAt stmt "converter: unreachable statements after `return`"
    if stmt.getKind == ``ccvIf then
      throwErrorAt stmt
        "converter: the call structure of a round may not branch — Def 2.2.2's v1 discipline synthesizes the `calls` budget from the clause's call count, so the number of inner calls must be independent of the answers received.  Branch inside a call's payload or the `return` term instead (answer-dependent PAYLOADS are fine); answer-dependent call STRUCTURE is the v2 `AnswersWithinDepth` extension"
    else if stmt.getKind == ``ccvCall then
      prefixStmts := prefixStmts.push stmt
      answerIds := answerIds.push (⟨stmt[1]⟩ : Ident).getId
    else if stmt.getKind == ``ccvSet then
      let rhs := stmt[3]
      for used in identsOf rhs do
        if answerIds.contains used then
          throwErrorAt rhs
            "converter: `set` may not read the call answer `{used}` — converter state is a fold over the outside history only (the kernel's `ofHistoryStep` hands each round just its own answer segment, so answer-dependent state does not exist at this carrier).  Fold the answer into the `return` value instead"
      prefixStmts := prefixStmts.push stmt
    else if stmt.getKind == ``ccvReturn then
      ret? := some ⟨stmt[1]⟩
    else
      throwErrorAt stmt "converter: unrecognized statement"
  match ret? with
  | some r => return (prefixStmts, r)
  | none => throwError "converter: a clause must end with `return …` (a converter always answers at its outside interface)"

/-- The number of `call` lines. -/
private def callCount (stmts : Array Syntax) : Nat :=
  stmts.foldl (fun n s => if s.getKind == ``ccvCall then n + 1 else n) 0

/-- Compile the round body: `call` lines become `RoundN` nodes
`⟨payload, fun answer => …⟩`, `set` lines become `let`s, the return term
closes the round. -/
private partial def compileRound (stmts : List Syntax) (ret : Term) :
    CommandElabM Term := do
  match stmts with
  | [] => return ret
  | stmt :: rest =>
    let restT ← compileRound rest ret
    if stmt.getKind == ``ccvCall then
      let answer : Ident := ⟨stmt[1]⟩
      let ctor : Ident := ⟨stmt[4]⟩
      let args : Array Term := stmt[5].getArgs.map (⟨·⟩)
      let dotted := mkIdent (`_root_ ++ `x) -- placeholder, replaced below
      let _ := dotted
      let payload ←
        if args.isEmpty then `(.$ctor:ident)
        else `(.$ctor:ident $args*)
      `(⟨$payload, fun $answer => $restT⟩)
    else if stmt.getKind == ``ccvSet then
      let f : Ident := ⟨stmt[1]⟩
      let e : Term := ⟨stmt[3]⟩
      `(let $f := $e
        $restT)
    else
      throwErrorAt stmt "converter: unrecognized statement"

open RandomSystems.CC.Grammar in
@[command_elab ccConverterCmd]
def elabCcConverter : CommandElab := fun stx => do
  -- shape: [doc?, atom, name, ":", src, "⇒", tgt, overKw, S, "where",
  --         states*, handlers+, display?, latex?, role?]
  let name : Ident := ⟨stx[2]⟩
  let base := name.getId
  let src : Term := ⟨stx[4]⟩
  let tgt : Term := ⟨stx[6]⟩
  let servicesT : Term := ⟨stx[8]⟩
  -- states
  let mut states : Array ConvState := #[]
  for st in stx[10].getArgs do
    unless st.getKind == ``ccStateDecl do
      throwErrorAt st "converter: malformed state"
    states := states.push ⟨⟨st[1]⟩, ⟨st[3]⟩, ⟨st[5]⟩⟩
  -- handlers
  let mut handlers : Array ConvHandler := #[]
  for h in stx[11].getArgs do
    unless h.getKind == ``ccvHandler do
      throwErrorAt h "converter: malformed clause"
    handlers := handlers.push
      ⟨(⟨h[1]⟩ : Ident).getId, h[2].getArgs.map (⟨·⟩), h[5].getSepArgs, h⟩
  -- duplicate check
  for h in handlers do
    if (handlers.filter (·.ctorName == h.ctorName)).size > 1 then
      throwErrorAt h.ref "converter: duplicate clause for `{h.ctorName}`"
  -- analyze all clauses up front (discipline checks fire here)
  let mut analyzed : Array (ConvHandler × Array Syntax × Term × Nat) := #[]
  for h in handlers do
    let (pre, ret) ← analyzeClause h.stmts
    analyzed := analyzed.push (h, pre, ret, callCount h.stmts)
  let budget := analyzed.foldl (fun b (_, _, _, k) => max b k) 0
  let budgetLit := Syntax.mkNatLit budget
  -- state tuple type / init / stateAt
  let stTy ←
    if states.isEmpty then `(Unit)
    else do
      let mut acc : Term := states.back!.ty
      for s in states.pop.reverse do acc ← `($(s.ty) × $acc)
      pure acc
  let initTerm ←
    if states.isEmpty then `(())
    else if states.size == 1 then pure states[0]!.init
    else `(($(states[0]!.init), $(states[1:].toArray |>.map (·.init)),*))
  -- 1. arity
  let arityId := mkIdentFrom name (base ++ `arity)
  let arityAlts ← analyzed.mapM fun (h, _, _, k) => do
    let ctor := mkIdent h.ctorName
    let wilds ← h.payloadIds.mapM fun _ => `(_)
    let pat ←
      if h.payloadIds.isEmpty then `(.$ctor:ident)
      else `(.$ctor:ident $wilds*)
    `(Lean.Parser.Term.matchAltExpr| | $pat:term => $(Syntax.mkNatLit k))
  elabCommand (← `(command|
    def $arityId:ident : ($servicesT).In $tgt → Nat := fun inp =>
      match inp with $arityAlts:matchAlt*))
  -- 2. updateState + stateAt
  let updId := mkIdentFrom name (base ++ `updateState)
  let stateAtId := mkIdentFrom name (base ++ `stateAt)
  let sId := mkIdent `__cc_state
  let updAlts ← analyzed.mapM fun (h, pre, _, _) => do
    let ctor := mkIdent h.ctorName
    let pat ←
      if h.payloadIds.isEmpty then `(.$ctor:ident)
      else `(.$ctor:ident $(h.payloadIds):ident*)
    -- apply the set-lines in order, then rebuild the tuple
    let fields := states.map fun s => (s.name : Term)
    let finalTuple ←
      if states.isEmpty then `(())
      else if states.size == 1 then pure fields[0]!
      else `(($(fields[0]!), $(fields[1:].toArray),*))
    let mut body : Term := finalTuple
    for stmt in pre.reverse do
      if stmt.getKind == ``ccvSet then
        let f : Ident := ⟨stmt[1]⟩
        let e : Term := ⟨stmt[3]⟩
        body ← `(let $f := $e
          $body)
    `(Lean.Parser.Term.matchAltExpr| | $pat:term => $body)
  let updBody ← `(fun $sId inp =>
    match inp with $updAlts:matchAlt*)
  let updOpen ←
    if states.isEmpty then pure updBody
    else if states.size == 1 then
      `(fun $sId inp =>
        let $(states[0]!.name):ident := $sId
        match inp with $updAlts:matchAlt*)
    else do
      let pats := states.map fun s => (s.name : Term)
      `(fun $sId inp =>
        let ($(pats[0]!), $(pats[1:].toArray),*) := $sId
        match inp with $updAlts:matchAlt*)
  elabCommand (← `(command|
    def $updId:ident : ($stTy) → ($servicesT).In $tgt → ($stTy) := $updOpen))
  elabCommand (← `(command|
    def $stateAtId:ident : List (($servicesT).In $tgt) → ($stTy) :=
      fun history => history.foldl $updId ($initTerm : $stTy)))
  -- 3. the script
  let scriptId := mkIdentFrom name (base ++ `script)
  let histId := mkIdent `__cc_history
  let scriptAlts ← analyzed.mapM fun (h, pre, ret, _) => do
    let ctor := mkIdent h.ctorName
    let pat ←
      if h.payloadIds.isEmpty then `(.$ctor:ident)
      else `(.$ctor:ident $(h.payloadIds):ident*)
    let round ← compileRound pre.toList ret
    let withState ←
      if states.isEmpty then pure round
      else if states.size == 1 then
        `(let $(states[0]!.name):ident := $stateAtId $histId
          $round)
      else do
        let pats := states.map fun s => (s.name : Term)
        `(let ($(pats[0]!), $(pats[1:].toArray),*) := $stateAtId $histId
          $round)
    `(Lean.Parser.Term.matchAltExpr| | $pat:term => $withState)
  elabCommand (← `(command|
    def $scriptId:ident : (history : List (($servicesT).In $tgt)) →
        (inp : ($servicesT).In $tgt) →
        RandomSystems.CC.RoundN (($servicesT).In $src) (($servicesT).Out $src)
          (($servicesT).Out $tgt) ($arityId inp) :=
      fun $histId inp =>
        match inp with $scriptAlts:matchAlt*))
  -- 4. the budget theorem (named)
  let boundId := mkIdentFrom name (base ++ `arity_le)
  elabCommand (← `(command|
    theorem $boundId:ident :
        ∀ inp, $arityId inp ≤ $budgetLit := by
      intro inp
      cases inp <;> simp [$arityId:ident]))
  -- 5. the converter
  elabCommand (← `(command|
    @[cc_surface] noncomputable def $name:ident :
        RandomSystems.CC.Converter $servicesT $src $tgt :=
      RandomSystems.CC.Converter.ofScript $arityId $scriptId $budgetLit $boundId))
  -- 6. the doc comment, when given, lands on the converter itself
  if stx[0].getArgs.size > 0 then
    let dc : TSyntax ``Lean.Parser.Command.docComment := ⟨stx[0][0]⟩
    elabCommand (← `(command| $dc:docComment add_decl_doc $name))
  -- 7. presentation attributes (default role: converter)
  emitPresentation name stx[12] stx[13] stx[14] `converter

end RandomSystems.CC.Grammar

/-! ## Receipts -/

namespace RandomSystems.CC.ConverterGrammarTests

open RandomSystems.CC
open RandomSystems.CR18.TypedResource
open RandomSystems (Dist)

/-! ### Receipt 1: a masking converter, judgment synthesized -/

inductive MaskService | plain | masked
  deriving DecidableEq

inductive BitIn | send (m : Bool)

def maskServices : Services where
  Service := MaskService
  In := fun _ => BitIn
  Out := fun _ => Bool

/-- Masks the transmitted bit. -/
converter maskBit : MaskService.plain ⇒ MaskService.masked over maskServices where
  on send m =>
    let c ← call send (xor m true);
    return c

-- the doc comment lands on the converter itself:
/-- info: some "Masks the transmitted bit. " -/
#guard_msgs in
#eval show Lean.CoreM _ from do
  Lean.findDocString? (← Lean.getEnv) ``maskBit

-- the default role lands (`converter`):
/-- info: some (RandomSystems.CC.Names.Role.converter) -/
#guard_msgs in
#eval show Lean.CoreM _ from
  return RandomSystems.CC.Names.role? (← Lean.getEnv) ``maskBit

/-- The synthesized Def-2.2.2 judgment, by name. -/
example : RandomSystems.CR18.PFunConverter.IsDDC maskBit.protocol :=
  maskBit.isDDC

/-- The synthesized budget theorem, by name. -/
example : ∀ inp, maskBit.arity inp ≤ 1 := maskBit.arity_le

/--
info: 'RandomSystems.CC.ConverterGrammarTests.maskBit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms maskBit

/-! ### Receipt 2: §2.2.6's π_A shape — two calls per round, the second
payload depending on the first answer (fetch the key, send the masked
message), with converter state folded over the outside history. -/

inductive PiService | inner | outer
  deriving DecidableEq

inductive OuterIn | send (m : Bool)
inductive InnerIn | fetch | send (c : Bool)

def piServices : Services where
  Service := PiService
  In := fun s => match s with | .inner => InnerIn | .outer => OuterIn
  Out := fun _ => Bool

converter piA : PiService.inner ⇒ PiService.outer over piServices where
  state count : Nat := 0
  on send m =>
    let k ← call fetch;
    let _c ← call send (xor m k);
    set count := count + 1;
    return true
  display "π_A"
  latex "\\pi_A"

-- the declared presentation attributes land:
/-- info: (some "π_A", some "\\pi_A") -/
#guard_msgs in
#eval show Lean.CoreM _ from do
  let env ← Lean.getEnv
  return (RandomSystems.CC.Names.displayName? env ``piA,
    RandomSystems.CC.Names.latexName? env ``piA)

/--
info: 'RandomSystems.CC.ConverterGrammarTests.piA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms piA

example : ∀ inp, piA.arity inp ≤ 2 := piA.arity_le

/-! ### Receipt 3: the staged discipline error — branching the call
structure on an answer is rejected in domain language. -/

/--
error: converter: the call structure of a round may not branch — Def 2.2.2's v1 discipline synthesizes the `calls` budget from the clause's call count, so the number of inner calls must be independent of the answers received.  Branch inside a call's payload or the `return` term instead (answer-dependent PAYLOADS are fine); answer-dependent call STRUCTURE is the v2 `AnswersWithinDepth` extension
-/
#guard_msgs in
converter cheat : MaskService.plain ⇒ MaskService.masked over maskServices where
  on send m =>
    let c ← call send m;
    if c then return c else return (xor c true)

/-! ### Receipt 4: attach, end to end — the receipt-1 converter applied to
a one-interface resource at the plain service. -/

def plainBoxMachine : Machine maskServices.sig
    (fun _ : Unit => MaskService.plain) where
  State := Unit
  init := ()
  step _ query :=
    match query with
    | ⟨(), .send m⟩ => some ((), m)

noncomputable def plainBox :
    ResourceAt maskServices (fun _ : Unit => MaskService.plain) :=
  DependentRandomSystem.ofProb
    ⟨Finsupp.single plainBoxMachine.toDDS 1, Dist.isProbDist_single _⟩

/-- `π R` typechecks with the grammar-authored converter: the interface's
service moves from `plain` to `masked`. -/
noncomputable def maskedBox :
    ResourceAt maskServices
      (Function.update (fun _ : Unit => MaskService.plain) ()
        MaskService.masked) :=
  ResourceAt.attach () maskBit rfl plainBox

end RandomSystems.CC.ConverterGrammarTests
