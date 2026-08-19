/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceWidgets
import RandomSystems.Jost.SurfaceGamma

/-!
# The authoring surface, part 7: algebraic moves (D3)

D1 folds change only the **view**: the term is untouched.  A **move**
changes the TERM and hands back a proof that the new term equals the old
one.  The set of pictures reachable by moves is therefore exactly the
term's equivalence class under the CC algebra — "manipulating the diagram"
and "applying the algebraic laws" become one act, and the diagram never
stops being a projection of a kernel-checked term.

Every move is a lemma application:

| move | what it does | the lemma |
|---|---|---|
| `lift k` | `α •[i] R ↝ α.word i • R` | `Converter.word_smul` |
| `merge k` | `γ •[i] (δ •[i] R) ↝ (γ * δ) • R` | `Converters.comp_smul` (`mul_smul`) |
| `drop_id k` | `1 • R ↝ R`, `(ofMaps id id) •[i] R ↝ R`, and `(ofMaps id id) ••[γ] R ↝ R.mergeAlong γ` | `Converters.id_smul` (`one_smul`) / `Converter.attachAt_id` / `Converter.attachAlong_id` |
| `commute k` | swap two attachments at DISTINCT interfaces, or two attachments along connections with DISJOINT images | `Converter.attachAt_comm` / `Converter.attachAlong_comm` / `Converters.smul_comm_of_ne` / `ResourceSystem.block_smul_of_ne` |
| `drop_idle k` | `α •[i] R ↝ R` when `i` does not provide `α`'s source | `Converter.attachAt_of_not_provides` |

`k` is the depth on the outer attachment spine (`0` = the root, the
default).  At depth `k > 0` the step is wrapped in `congrArg` through the
`k` enclosing frames, so the emitted `calc` step still speaks about the
whole term.

Applicability is decided by the **term**, never by the label: `merge`
compares the two interfaces with `isDefEq`, `drop_id` asks whether the
scalar is definitionally `1`, `commute` and `drop_idle` discharge their
side conditions with `Decidable.decide` (`mkDecideProof` — a real proof
term, no `native_decide`).  A move whose side condition cannot be decided
is simply **not offered**.

## Commands

* `#cc_moves t` — the move menu: for every spine depth, which moves the
  term licenses there.  This is the matcher's receipt.
* `#cc_rewrite t with [move, …]` — apply the moves in order, log the
  resulting term and its diagram, and emit the whole derivation as a
  `calc` chain (one step per move, each justified by its lemma) as a
  Try-this suggestion that pastes back as a `theorem`.

The composite proof is checked by `Lean.Kernel.check` *inside the
command* — the kernel type-checks the term and `Kernel.isDefEq` confirms
its type is the claimed equation — so a `#cc_rewrite` that prints is a
kernel receipt on its own, before anybody pastes anything.  (A mutation
run confirms the gate bites: making `commute` return the UNswapped term
while keeping `smul_comm_of_ne` as its proof is rejected with
"kernel rejected the derivation", not silently accepted.)

Scope note: this module is the D3 *engine*.  The D3 rendering half —
drawing a law as a Maurer-Fig-3 pair with the law name as a grey
equation-number caption (DESIGN §12 item 12) — is the diagram layer's
business and lives in `Jost/SurfaceWidgets.lean` (`Diagram.pairHtml`,
`#cc_diagram thm`); nothing here draws.

Grammar is reservation-free (`&"merge"`, …, matched as NON-reserved
words) and introduced by `with`, for the D1 reason: `#cc_rewrite t
[merge]` ALREADY parses — `t` applied to the list literal `[merge]`,
`merge` being an ordinary identifier.  `declare_syntax_cat ccMove
(behavior := both)` is what lets a leading identifier find the token
index at all.

## Moves NOT implemented, and the exact lemma each one is missing

* **`par_comm`** (`R ∥ Q ↝ reindex sumComm (Q ∥ R)`) and **`par_assoc`**.
  The LEMMAS are now proved: `ResourceSystem.par_comm` and
  `ResourceSystem.par_assoc` (`Jost/SurfaceShuffle.lean`), plain equalities
  through the surface operation `ResourceSystem.reindex`, with `≈[0]`
  forms beside them.  This header used to record the remaining work as
  *"only the surface operation and the instance"*; that was wrong about
  the instance.  The operation was indeed the easy half — a bijective
  re-indexing is `tagCompatible_of_route` at `route = relabel` — but the
  instance is a four-level theorem of its own: `PFunDDS.par` had to be
  shown symmetric and associative under the swap and associator
  relabellings (`PFunDDS.par_comm`, `par_assoc`, plus the bifunctoriality
  `par_relabel` that a NESTED tensor forces, since `flatten_tensor` puts a
  relabelling *inside* a `par`), and that had to be lifted through
  `DependentDDS` → `DependentPDS` → `DependentRandomSystem` → `Resource`
  (`RandomSystems/TypedTensorShuffle.lean`).  What is missing HERE is only
  the matcher, and the obstruction is structural: `decode?` deliberately
  ends the attachment spine at `∥`, so there is no node for a `∥` move to
  act on — the spine would have to become a tree first.
* **`par_distrib`** (MaRuTa12 §2.1's `(ψ ∥ φ)^I (R ∥ S) = ψ^I R ∥ φ^I S`).
  Delivered as lemmas, in Jost's form rather than Maurer's, at BOTH
  levels: at disjoint interface sets the composite converter is
  unnecessary, because a converter attached at `Sum.inl i` reaches only
  the left component.  `Converter.attachAt_par_left` (Prop. 2.2.3 (2)) is
  the plain equality `α •[Sum.inl i] (R ∥ Q) = (α •[i] R) ∥ Q`; its γ
  analogue `Converter.attachAlong_par_left` (`Jost/SurfaceGamma.lean`) is
  the same law for a converter reaching TWO interfaces of the left factor,
  up to the one renaming the two spellings of the interface set force
  (`(rest ⊕ J) ⊕ Unit` against `(rest ⊕ Unit) ⊕ J`).  Missing for both:
  only the matcher — it would have to recognize a `∥` under the
  attachment, which is the same spine-versus-tree obstruction as above.
* **`block_idem`** (`⊣[i] (⊣[i] R) ↝ ⊣[i] R`) and **`block_comm`**
  (`⊣[i] (⊣[j] R) ↝ ⊣[j] (⊣[i] R)`, `i ≠ j`).  The *lemmas* now exist —
  `ResourceSystem.block_idem` and `ResourceSystem.block_comm`
  (`Jost/SurfaceAlgebra.lean`).  Neither needed what this file previously
  recorded as the obstruction: idempotence is not a behavioural fact
  about an unqueryable interface but the observation that `Converter.bot`
  out of the blocked service *is* `ofMaps id id`
  (`Converter.ofMaps_eq_of_no_input`), and commutation is
  `Converter.attachAt_comm` once `block_eq_attachAt` has named each
  block's member of the `⊥` family.  What is missing is only the move
  itself: a matcher that recognizes the `⊣` head and rebuilds the term,
  which nothing in this file yet does.
* **`merge` across `⊣`** (`⊣[i] (α •[i] R)` into one `Σ`-word).  The
  product exists (`⊣` unfolds to an attachment), but the result cannot be
  spelled with the `⊣` glyph, so it would silently destroy the blocking
  vocabulary; deliberately not offered.
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource
open Lean Elab Command Meta

namespace Move

/-! ## The move set -/

/-- The moves the CC algebra licenses on this carrier.  One constructor
per lemma; the module header records what is deliberately absent. -/
inductive Kind where
  | lift
  | merge
  | dropId
  | commute
  | dropIdle
  deriving DecidableEq, Repr, Inhabited

/-- The surface word of a move — what the grammar accepts and what the
receipts print. -/
def Kind.word : Kind → String
  | .lift => "lift"
  | .merge => "merge"
  | .dropId => "drop_id"
  | .commute => "commute"
  | .dropIdle => "drop_idle"

/-- All moves, in menu order. -/
def allKinds : List Kind := [.lift, .merge, .dropId, .commute, .dropIdle]

/-- A move together with the spine depth it acts at (`0` = the root). -/
structure Request where
  kind : Kind
  depth : Nat := 0
  deriving Inhabited

/-! ## Reading a node off the term

The matcher never looks at a label: it decodes the ELABORATED head
constant, exactly as `Diagram.ofExpr` does, and reuses the same three
attachment heads. -/

/-- The attachment operations the surface offers. -/
inductive Head where
  /-- `α •[i] R` — `Converter.attachAt`. -/
  | attachAt
  /-- `α ••[γ] R` — `Converter.attachAlong`, a converter reaching the two
  interfaces the connection `γ` names (Jost's `π^γ R`). -/
  | attachAlong
  /-- `γ • R` for `γ : Converters S I i` — the `Σ`-word action. -/
  | smul
  /-- `⊣[i] R` — `ResourceSystem.block`. -/
  | block
  deriving DecidableEq, Repr, Inhabited

/-- A decoded attachment node.  `args` is the full argument array of the
head application, so the node can be rebuilt with a different resource
without re-deriving any implicit argument. -/
structure Node where
  head : Head
  fn : Expr
  args : Array Expr
  interface : Expr
  carrier : Expr

/-- Decode an attachment node, or fail: the head constant decides.
A head that is neither of the three is δ-expanded once and retried
(bounded), exactly as `Diagram.ofExpr` looks through a definition to find
composition — so `#cc_rewrite SomeNamedShape` sees the same spine the
diagram draws.  The moves keep working on the ORIGINAL term: the step's
left-hand side is `e`, and δ is defeq. -/
partial def decode? (e : Expr) (fuel : Nat := 6) : MetaM (Option Node) := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const n _ := f
    | return none
  if n != ``RandomSystems.CC.Converter.attachAt ∧
      n != ``RandomSystems.CC.Converter.attachAlong ∧
      n != ``RandomSystems.CC.ResourceSystem.block ∧
      n != ``HSMul.hSMul then
    -- `∥` ends the attachment spine, and a display-named head IS the paper
    -- object (`Diagram.ofExpr`'s own rule): neither is δ-expanded.
    if n == ``RandomSystems.CC.ResourceSystem.par ∨
        n == ``RandomSystems.CC.ResourceAt.par ∨
        n == ``RandomSystems.CC.Resource.par ∨
        (Names.displayName? (← getEnv) n).isSome then
      return none
    match fuel with
    | 0 => return none
    | k + 1 =>
        match ← unfoldDefinition? e with
        | some inner => return ← decode? inner k
        | none => return none
  if n == ``RandomSystems.CC.Converter.attachAt then
    if args.size ≥ 3 then
      return some
        { head := .attachAt, fn := f, args,
          interface := args[args.size - 2]!, carrier := args[args.size - 1]! }
    return none
  else if n == ``RandomSystems.CC.Converter.attachAlong then
    -- Same trailing five arguments as `attachAt` (`source target conv γ R`),
    -- with the CONNECTION where the interface sits.
    if args.size ≥ 3 then
      return some
        { head := .attachAlong, fn := f, args,
          interface := args[args.size - 2]!, carrier := args[args.size - 1]! }
    return none
  else if n == ``RandomSystems.CC.ResourceSystem.block then
    if args.size ≥ 2 then
      return some
        { head := .block, fn := f, args,
          interface := args[args.size - 2]!, carrier := args[args.size - 1]! }
    return none
  else if n == ``HSMul.hSMul then
    if args.size ≥ 6 then
      let scalar := args[args.size - 2]!
      let scalarTy ← instantiateMVars (← inferType scalar)
      let tyArgs := scalarTy.getAppArgs
      if let .const tyHead _ := scalarTy.getAppFn then
        if (tyHead == ``RandomSystems.CC.Converters ∨
            tyHead == ``RandomSystemsCC.TypedFinite.Gamma) ∧ tyArgs.size ≥ 1 then
          return some
            { head := .smul, fn := f, args,
              interface := tyArgs[tyArgs.size - 1]!,
              carrier := args[args.size - 1]! }
      return none
    return none
  return none

/-- Rebuild the node around a different resource. -/
def Node.withResource (nd : Node) (carrier : Expr) : Expr :=
  mkAppN nd.fn (nd.args.set! (nd.args.size - 1) carrier)

/-- The node as a one-argument frame `fun R => …` — the `congrArg`
motive for a move applied below it. -/
def Node.frame (nd : Node) : MetaM Expr := do
  let ty ← inferType nd.carrier
  return .lam `R ty (mkAppN nd.fn (nd.args.set! (nd.args.size - 1) (.bvar 0)))
    .default

/-- The node's converter as an element of `Σ` at its interface: the
scalar itself for `•`, the embedded word `α.word i` for `•[i]`.  A `⊣`
node has no `Σ`-spelling that keeps the glyph, so it has none here. -/
def Node.gamma (nd : Node) : MetaM (Option Expr) := do
  match nd.head with
  | .smul => return some nd.args[nd.args.size - 2]!
  | .attachAt =>
      return some (← mkAppM ``RandomSystems.CC.Converter.word
        #[nd.args[nd.args.size - 3]!, nd.interface])
  | .attachAlong => return none
  | .block => return none

/-- The bare converter of a `•[i]` node (for `attachAt_comm`). -/
def Node.conv? (nd : Node) : Option Expr :=
  if nd.head == .attachAt then some nd.args[nd.args.size - 3]! else none

/-! ## Steps -/

/-- One applied move: the term before, the term after, a proof of their
equality, the lemmas cited, and the pasteable justification text. -/
structure Step where
  before : Expr
  after : Expr
  proof : Expr
  lemmas : List Name
  justification : String

/-- Build a step positionally — the moves below all end in one of these. -/
def mkStep (before after proof : Expr) (lemmas : List Name)
    (justification : String) : Step :=
  { before, after, proof, lemmas, justification }

/-- Pretty-print on one line: a `calc` step must not wrap. -/
def ppLine (e : Expr) : MetaM String := do
  return (← ppExpr e).pretty (width := 1000000)

/-- Pretty-print as an explicit argument: parenthesized when compound,
bare when it is a single atom (so the emitted lemma applications read
like hand-written ones). -/
def ppArg (e : Expr) : MetaM String := do
  let s ← ppLine e
  return if (s.splitOn " ").length == 1 then s else s!"({s})"

/-- A decidable side condition as a real proof term (`Decidable.decide`,
never `native_decide`); `none` when it does not evaluate. -/
def decideSide? (prop : Expr) : MetaM (Option Expr) := do
  try
    let prf ← mkDecideProof prop
    check prf
    return some prf
  catch _ => return none

/-! ## The individual moves, at the root of a term -/

/-- `lift`: `α •[i] R ↝ α.word i • R` (`Converter.word_smul`).  A `••[γ]`
node has no `Σ`-spelling at the resource's OWN interface set — its converter
acts at the merge of two of them — so it does not lift. -/
def liftAt (e : Expr) : MetaM Step := do
  let some nd ← decode? e | throwError "lift: not an attachment node"
  unless nd.head == .attachAt do
    throwError "lift: only `α •[i] R` lifts into Σ (a `•` node is already \
there, and a `••[γ]` node acts at a merge, not at an interface of R)"
  let conv := nd.args[nd.args.size - 3]!
  let word ← mkAppM ``RandomSystems.CC.Converter.word #[conv, nd.interface]
  let after ← mkAppM ``HSMul.hSMul #[word, nd.carrier]
  let base ← mkAppM ``RandomSystems.CC.Converter.word_smul
    #[conv, nd.interface, nd.carrier]
  let proof ← mkExpectedTypeHint (← mkAppM ``Eq.symm #[base]) (← mkEq e after)
  let just := s!"(Converter.word_smul {← ppArg conv} {← ppArg nd.interface} \
{← ppArg nd.carrier}).symm"
  return mkStep e after proof [``RandomSystems.CC.Converter.word_smul] just

/-- `merge`: two serial converters at ONE interface become their `Σ`
product (`Converters.comp_smul`, i.e. `mul_smul`).  Either operand may be
spelled `•[i]` or `•`; a `•[i]` operand is lifted through
`Converter.word_smul` (which is `rfl`, so the composed proof still
carries the user's spelling on the left). -/
def mergeAt (e : Expr) : MetaM Step := do
  let some outer ← decode? e | throwError "merge: not an attachment node"
  let some inner ← decode? outer.carrier
    | throwError "merge: the inner term is not an attachment node"
  if outer.head == .block ∨ inner.head == .block then
    throwError "merge: `⊣` has no Σ-spelling that keeps the glyph — not offered"
  unless ← isDefEq outer.interface inner.interface do
    throwError "merge: the two attachments are at different interfaces"
  let some gammaOuter ← outer.gamma | throwError "merge: no Σ word (outer)"
  let some gammaInner ← inner.gamma | throwError "merge: no Σ word (inner)"
  let product ← mkAppM ``HMul.hMul #[gammaOuter, gammaInner]
  let after ← mkAppM ``HSMul.hSMul #[product, inner.carrier]
  let base ← mkAppM ``RandomSystems.CC.Converters.comp_smul
    #[gammaOuter, gammaInner, inner.carrier]
  let proof ← mkExpectedTypeHint (← mkAppM ``Eq.symm #[base]) (← mkEq e after)
  let lemmas :=
    (if outer.head == .attachAt ∨ inner.head == .attachAt then
      [``RandomSystems.CC.Converter.word_smul] else []) ++
    [``RandomSystems.CC.Converters.comp_smul]
  let just := s!"(Converters.comp_smul {← ppArg gammaOuter} \
{← ppArg gammaInner} {← ppArg inner.carrier}).symm"
  return mkStep e after proof lemmas just

/-- `drop_id` at a `•[i]` node: the converter itself is the memoryless
identity, so the attachment is idle (`Converter.attachAt_id`).  The test is
definitional and total: the lemma's own statement is elaborated at THIS
node's source service and its type is compared with the node by `isDefEq`,
so a converter that renames anything at all simply fails to match and the
move is not offered. -/
def dropIdConverterAt (nd : Node) (e : Expr) : MetaM Step := do
  let source := nd.args[nd.args.size - 5]!
  let target := nd.args[nd.args.size - 4]!
  unless ← isDefEqGuarded source target do
    throwError "drop_id: the converter moves the service, so it is not `ofMaps id id`"
  let expected ← mkEq e nd.carrier
  -- `attachAt`'s argument vector is `S I inst source target conv i R`, so
  -- the development and its interface type come off the node itself; the
  -- lemma's `service` is the node's own source.
  let proof ← mkAppOptM ``RandomSystems.CC.Converter.attachAt_id
    #[some nd.args[nd.args.size - 8]!, some nd.args[nd.args.size - 7]!,
      some nd.args[nd.args.size - 6]!, some source, some nd.interface,
      some nd.carrier]
  unless ← isDefEqGuarded (← inferType proof) expected do
    throwError "drop_id: this converter is not definitionally `Converter.ofMaps id id`"
  let proof ← mkExpectedTypeHint proof expected
  let just := s!"Converter.attachAt_id {← ppArg nd.interface} \
{← ppArg nd.carrier}"
  return mkStep e nd.carrier proof
    [``RandomSystems.CC.Converter.attachAt_id] just

/-- `drop_id` at a `••[γ]` node: the converter is the memoryless identity, so
the ACTION half of the γ-attachment is empty and only its re-addressing half
survives — the two connected interfaces, addressed as one
(`Converter.attachAlong_id`).  The rewritten term is therefore the merge, not
the resource: a connection changes the interface set even when its converter
does nothing.  Same definitional applicability test as at a `•[i]` node. -/
def dropIdAlongAt (nd : Node) (e : Expr) : MetaM Step := do
  -- `attachAlong`'s argument vector ends `source target conv γ R`.
  let source := nd.args[nd.args.size - 5]!
  let target := nd.args[nd.args.size - 4]!
  unless ← isDefEqGuarded source target do
    throwError "drop_id: the converter moves the service, so it is not `ofMaps id id`"
  let merged ← mkAppM ``RandomSystems.CC.ResourceSystem.mergeAlong
    #[nd.interface, nd.carrier]
  let expected ← mkEq e merged
  let proof ← mkAppOptM ``RandomSystems.CC.Converter.attachAlong_id
    #[some nd.args[nd.args.size - 11]!, some nd.args[nd.args.size - 10]!,
      some nd.args[nd.args.size - 9]!, some nd.args[nd.args.size - 8]!,
      some nd.args[nd.args.size - 7]!, some nd.args[nd.args.size - 6]!,
      some source, some nd.interface, some nd.carrier]
  unless ← isDefEqGuarded (← inferType proof) expected do
    throwError "drop_id: this converter is not definitionally `Converter.ofMaps id id`"
  let proof ← mkExpectedTypeHint proof expected
  let just := s!"Converter.attachAlong_id {← ppArg nd.interface} \
{← ppArg nd.carrier}"
  return mkStep e merged proof
    [``RandomSystems.CC.Converter.attachAlong_id] just

/-- `drop_id`: the neutral converter vanishes.  Three lemmas, picked by the
head: `Converters.id_smul` (i.e. `one_smul`) when the scalar is `1` in `Σ`,
`Converter.attachAt_id` when the CONVERTER of a `•[i]` node is the memoryless
identity, and `Converter.attachAlong_id` at a `••[γ]` node, where the unit law
lands on the MERGE rather than on the resource.  The three are genuinely
different facts — `1` is the word monoid's formal unit, `ofMaps id id` is a
converter whose idleness is a theorem about the action, and a connection
re-addresses even when its converter does not act — and every applicability
test is definitional (`isDefEq`), never a reading of the pill's label. -/
def dropIdAt (e : Expr) : MetaM Step := do
  let some nd ← decode? e | throwError "drop_id: not an attachment node"
  if nd.head == .attachAt then
    return ← dropIdConverterAt nd e
  if nd.head == .attachAlong then
    return ← dropIdAlongAt nd e
  unless nd.head == .smul do
    throwError "drop_id: `⊣` is not a unit (it blocks); it has no `drop_id`"
  let scalar := nd.args[nd.args.size - 2]!
  let scalarTy ← inferType scalar
  let one ← mkAppOptM ``One.one #[scalarTy, none]
  unless ← isDefEqGuarded scalar one do
    throwError "drop_id: the scalar is not definitionally `1`"
  -- `id_smul`'s interface is implicit and NOT determined by the resource,
  -- so it is supplied from the node.
  let proof ← mkExpectedTypeHint
    (← mkAppOptM ``RandomSystems.CC.Converters.id_smul
      #[none, none, none, some nd.interface, some nd.carrier])
    (← mkEq e nd.carrier)
  let just := s!"Converters.id_smul {← ppArg nd.carrier}"
  return mkStep e nd.carrier proof [``RandomSystems.CC.Converters.id_smul] just

/-- `commute` at two CONNECTIONS (`Converter.attachAlong_comm`).  The two
attachments do not live at one interface set — `γ₂` is a connection on the
set `γ₁` produced — so the interface-level `i ≠ j` cannot even be written.
What replaces it is Jost's own side condition, *`img γ₂` misses `img γ₁`*,
which at this type level says: `γ₂` must not reach the single interface `γ₁`
produced.  That is one decidable test,
`γ₂.relocate γ₁.produced ≠ γ₂.produced`.

The rewritten term commutes the two converter ACTIONS and leaves `γ₁`'s
re-addressing where it is: a merge changes the interface set, so it has no
order to be exchanged with.  `α` therefore reappears at the ordinary
interface `γ₂` left for it. -/
def commuteAlongAt (outer inner : Node) (e : Expr) : MetaM Step := do
  -- Both nodes' argument vectors end `source target conv γ R`.
  let convOuter := outer.args[outer.args.size - 3]!
  let convInner := inner.args[inner.args.size - 3]!
  let produced ← mkAppM ``RandomSystems.CC.Connection.produced #[inner.interface]
  let relocated ← mkAppM ``RandomSystems.CC.Connection.relocate
    #[outer.interface, produced]
  let outerProduced ← mkAppM ``RandomSystems.CC.Connection.produced
    #[outer.interface]
  let some avoids ← decideSide? (← mkAppM ``Ne #[relocated, outerProduced])
    | throwError "commute: `{← ppLine relocated} ≠ {← ppLine outerProduced}` \
does not decide — the outer connection may reach the interface the inner one \
produced"
  let merged ← mkAppM ``RandomSystems.CC.ResourceSystem.mergeAlong
    #[inner.interface, inner.carrier]
  let inside ← mkAppM ``RandomSystems.CC.Converter.attachAlong
    #[convOuter, outer.interface, merged]
  let after ← mkAppM ``RandomSystems.CC.Converter.attachAt
    #[convInner, relocated, inside]
  let base ← mkAppM ``RandomSystems.CC.Converter.attachAlong_comm
    #[convInner, convOuter, inner.interface, outer.interface, avoids,
      inner.carrier]
  let proof ← mkExpectedTypeHint base (← mkEq e after)
  let just := s!"Converter.attachAlong_comm {← ppArg convInner} \
{← ppArg convOuter} {← ppArg inner.interface} {← ppArg outer.interface} \
(by decide) {← ppArg inner.carrier}"
  return mkStep e after proof
    [``RandomSystems.CC.Converter.attachAlong_comm] just

/-- `commute`: attachments at DISTINCT interfaces swap.  Four lemmas,
picked by the two heads: `Converter.attachAt_comm` when both are `•[i]`,
`Converter.attachAlong_comm` when both are `••[γ]`,
`ResourceSystem.block_smul_of_ne` when exactly one is `⊣`, and
`Converters.smul_comm_of_ne` otherwise.  The side condition is a `decide`
proof term — `i ≠ j` at interfaces, *`img γ₂` misses `img γ₁`* at
connections; a side condition that does not evaluate is not offered. -/
def commuteAt (e : Expr) : MetaM Step := do
  let some outer ← decode? e | throwError "commute: not an attachment node"
  let some inner ← decode? outer.carrier
    | throwError "commute: the inner term is not an attachment node"
  if outer.head == .block ∧ inner.head == .block then
    throwError "commute: `⊣` past `⊣` needs `ResourceSystem.block_comm` (unproved)"
  if outer.head == .attachAlong ∧ inner.head == .attachAlong then
    return ← commuteAlongAt outer inner e
  if outer.head == .attachAlong ∨ inner.head == .attachAlong then
    throwError "commute: a `••[γ]` node and an interface-level node have no \
common interface set to compare — only two connections commute here"
  let ne ← mkAppM ``Ne #[outer.interface, inner.interface]
  let some neProof ← decideSide? ne
    | throwError "commute: `{← ppLine outer.interface} ≠ \
{← ppLine inner.interface}` does not decide"
  let after := inner.withResource (outer.withResource inner.carrier)
  if outer.head == .block then
    -- `block_smul_of_ne` reads `iC ≠ iB` with `iC` the CONVERTER's
    -- interface and `iB` the blocked one, so the decided `≠` is flipped.
    let some gamma ← inner.gamma | throwError "commute: no Σ word (inner)"
    let neProof ← mkAppM ``Ne.symm #[neProof]
    let base ← mkAppM ``RandomSystems.CC.ResourceSystem.block_smul_of_ne
      #[neProof, gamma, inner.carrier]
    let proof ← mkExpectedTypeHint base (← mkEq e after)
    let just := s!"ResourceSystem.block_smul_of_ne (by decide) \
{← ppArg gamma} {← ppArg inner.carrier}"
    return mkStep e after proof
      [``RandomSystems.CC.ResourceSystem.block_smul_of_ne] just
  else if inner.head == .block then
    -- `γ • (⊣[j] R) = ⊣[j] (γ • R)` is `block_smul_of_ne` read backwards;
    -- here the outer node IS the converter, so the `≠` is already right.
    let some gamma ← outer.gamma | throwError "commute: no Σ word (outer)"
    let base ← mkAppM ``RandomSystems.CC.ResourceSystem.block_smul_of_ne
      #[neProof, gamma, inner.carrier]
    let proof ← mkExpectedTypeHint (← mkAppM ``Eq.symm #[base]) (← mkEq e after)
    let just := s!"(ResourceSystem.block_smul_of_ne (by decide) \
{← ppArg gamma} {← ppArg inner.carrier}).symm"
    return mkStep e after proof
      [``RandomSystems.CC.ResourceSystem.block_smul_of_ne] just
  else if outer.head == .attachAt ∧ inner.head == .attachAt then
    let some convOuter := outer.conv? | throwError "commute: no converter"
    let some convInner := inner.conv? | throwError "commute: no converter"
    let base ← mkAppM ``RandomSystems.CC.Converter.attachAt_comm
      #[neProof, convOuter, convInner, inner.carrier]
    let proof ← mkExpectedTypeHint base (← mkEq e after)
    let just := s!"Converter.attachAt_comm (by decide) {← ppArg convOuter} \
{← ppArg convInner} {← ppArg inner.carrier}"
    return mkStep e after proof
      [``RandomSystems.CC.Converter.attachAt_comm] just
  else
    let some gammaOuter ← outer.gamma | throwError "commute: no Σ word (outer)"
    let some gammaInner ← inner.gamma | throwError "commute: no Σ word (inner)"
    let base ← mkAppM ``RandomSystems.CC.Converters.smul_comm_of_ne
      #[neProof, gammaOuter, gammaInner, inner.carrier]
    let proof ← mkExpectedTypeHint base (← mkEq e after)
    let just := s!"Converters.smul_comm_of_ne (by decide) {← ppArg gammaOuter} \
{← ppArg gammaInner} {← ppArg inner.carrier}"
    return mkStep e after proof
      [``RandomSystems.CC.Converters.smul_comm_of_ne] just

/-- `drop_idle`: a converter attached where the interface does not
provide its source service is the identity
(`Converter.attachAt_of_not_provides`) — totality doing real work.  The
mismatch is decided on the term, so the move is offered exactly when the
layout says so. -/
def dropIdleAlongAt (nd : Node) (e : Expr) : MetaM Step := do
  -- `attachAlong`'s arguments end `source target conv γ R`, as `attachAt`'s
  -- end `source target conv i R`.
  let conv := nd.args[nd.args.size - 3]!
  let source := nd.args[nd.args.size - 5]!
  let faced ← mkAppM ``RandomSystems.CC.ResourceSystem.layoutAlong
    #[nd.carrier, nd.interface]
  let mismatch ← mkAppM ``Ne #[faced, source]
  let some mismatchProof ← decideSide? mismatch
    | throwError "drop_idle: the connection may face `{← ppLine source}` \
(the mismatch does not decide)"
  let merged ← mkAppM ``RandomSystems.CC.ResourceSystem.mergeAlong
    #[nd.interface, nd.carrier]
  let base ← mkAppM ``RandomSystems.CC.Converter.attachAlong_of_not_provides
    #[conv, nd.interface, nd.carrier, mismatchProof]
  let proof ← mkExpectedTypeHint base (← mkEq e merged)
  let just := s!"Converter.attachAlong_of_not_provides {← ppArg conv} \
{← ppArg nd.interface} {← ppArg nd.carrier} (by decide)"
  return mkStep e merged proof
    [``RandomSystems.CC.Converter.attachAlong_of_not_provides] just

/-- `drop_idle`, dispatched by head: `Converter.attachAt_of_not_provides` at
an interface, `Converter.attachAlong_of_not_provides` at a connection (where
what remains is the merge — the two interfaces really were addressed as
one). -/
def dropIdleAt (e : Expr) : MetaM Step := do
  let some nd ← decode? e | throwError "drop_idle: not an attachment node"
  if nd.head == .attachAlong then
    return ← dropIdleAlongAt nd e
  unless nd.head == .attachAt do
    throwError "drop_idle: only `α •[i] R` carries a source service to miss"
  -- `attachAt`'s arguments are `S I inst source target conv i R`.
  let conv := nd.args[nd.args.size - 3]!
  let source := nd.args[nd.args.size - 5]!
  let layoutAt ← mkAppM ``RandomSystems.CC.ResourceSystem.layoutAt
    #[nd.carrier, nd.interface]
  let mismatch ← mkAppM ``Ne #[layoutAt, source]
  let some mismatchProof ← decideSide? mismatch
    | throwError "drop_idle: the interface may provide `{← ppLine source}` \
(the mismatch does not decide)"
  let base ← mkAppM ``RandomSystems.CC.Converter.attachAt_of_not_provides
    #[conv, nd.interface, nd.carrier, mismatchProof]
  let proof ← mkExpectedTypeHint base (← mkEq e nd.carrier)
  let just := s!"Converter.attachAt_of_not_provides {← ppArg conv} \
{← ppArg nd.interface} {← ppArg nd.carrier} (by decide)"
  return mkStep e nd.carrier proof
    [``RandomSystems.CC.Converter.attachAt_of_not_provides] just

/-- Dispatch a move at the root of a term. -/
def rootStep (kind : Kind) (e : Expr) : MetaM Step :=
  match kind with
  | .lift => liftAt e
  | .merge => mergeAt e
  | .dropId => dropIdAt e
  | .commute => commuteAt e
  | .dropIdle => dropIdleAt e

/-! ## Depth: the spine, and `congrArg` back up -/

/-- Descend `k` steps along the outer attachment spine, returning the
subterm and the frames above it (outermost first). -/
partial def descend (e : Expr) : Nat → MetaM (Expr × List Node)
  | 0 => return (e, [])
  | k + 1 => do
      let some nd ← decode? e
        | throwError "depth {k + 1}: the spine ends here (not an attachment node)"
      let (sub, frames) ← descend nd.carrier k
      return (sub, nd :: frames)

/-- Apply a move at its requested depth: the step is proved at the node
and transported to the whole term by `congrArg` through each enclosing
frame. -/
def applyRequest (e : Expr) (req : Request) : MetaM Step := do
  let (sub, frames) ← descend e req.depth
  let step ← rootStep req.kind sub
  let mut before := step.before
  let mut after := step.after
  let mut proof := step.proof
  let mut text := step.justification
  for nd in frames.reverse do
    let frame ← nd.frame
    let before' := nd.withResource before
    let after' := nd.withResource after
    proof ← mkExpectedTypeHint (← mkCongrArg frame proof)
      (← mkEq before' after')
    text := s!"congrArg ({← ppLine frame}) ({text})"
    before := before'
    after := after'
  return { step with before, after, proof, justification := text }

/-- The move menu at one node: every move whose lemma actually applies
to THIS term.  Failures are silent — an unavailable move is simply
absent, which is what a menu means. -/
def menuAt (e : Expr) : MetaM (List Kind) := do
  let mut out : List Kind := []
  for kind in allKinds do
    let ok ← try let _ ← rootStep kind e; pure true catch _ => pure false
    if ok then out := out ++ [kind]
  return out

/-- The move menu of a whole term: one entry per spine depth, each with
the node's converter and interface as the diagram draws them. -/
partial def menu (e : Expr) (depth : Nat := 0) : MetaM (List (Nat × String × List Kind)) := do
  match ← decode? e with
  | none => return []
  | some nd =>
      let shape ← Diagram.ofExpr e
      let headLine ← match shape with
        | .attach conv ifc .. => pure s!"{conv} @ {ifc}"
        | _ => ppLine e
      let here := (depth, headLine, ← menuAt e)
      return here :: (← menu nd.carrier (depth + 1))

/-! ## The derivation -/

/-- Apply a list of moves in order, keeping every step. -/
def run (e : Expr) (reqs : List Request) : MetaM (List Step) := do
  let mut cur := e
  let mut steps : List Step := []
  for req in reqs do
    let step ← applyRequest cur req
    steps := steps ++ [step]
    cur := step.after
  return steps

/-- Chain the steps into one proof `first = last`. -/
def compose (e : Expr) (steps : List Step) : MetaM (Expr × Expr) := do
  match steps with
  | [] => return (e, ← mkAppM ``Eq.refl #[e])
  | first :: rest =>
      let mut proof := first.proof
      let mut last := first.after
      for step in rest do
        proof ← mkAppM ``Eq.trans #[proof, step.proof]
        last := step.after
      return (last, proof)

/-- **The kernel gate.**  Type-check the composite proof with
`Lean.Kernel.check` — the actual kernel, not the elaborator — and confirm
with `Kernel.isDefEq` that the type it returns is the claimed equation.
Metavariables are refused outright (the kernel has none). -/
def kernelCheck (proof expected : Expr) : MetaM Unit := do
  let proof ← instantiateMVars proof
  let expected ← instantiateMVars expected
  if proof.hasExprMVar ∨ expected.hasExprMVar then
    throwError "the derivation left metavariables; the kernel cannot check it"
  let env ← getEnv
  match Kernel.check env {} proof with
  | .error err => throwError "kernel rejected the derivation: {err.toMessageData {}}"
  | .ok ty =>
      match Kernel.isDefEq env {} ty expected with
      | .error err =>
          throwError "kernel could not compare the derived type: {err.toMessageData {}}"
      | .ok true => pure ()
      | .ok false =>
          throwError "the derivation proves{indentExpr ty}\nbut the moves \
claim{indentExpr expected}"

/-- The `calc` chain of a derivation, ready to paste.  The head line is
the user's OWN source text, not a re-pretty-print: an elaborated term can
lose what made it elaborable (a numeral's type ascription, say), and a
suggestion that does not paste back is worthless. -/
def calcChain (head : String) (steps : List Step) : MetaM String := do
  if steps.isEmpty then return "rfl  -- no moves"
  let mut out := s!"calc {head}"
  for step in steps do
    out := out ++ s!"\n  _ = {← ppLine step.after} := {step.justification}"
  return out

end Move

/-! ### The move grammar

Reservation-free: `merge`, `lift`, `drop_id`, `commute`, `drop_idle` are
matched as NON-reserved words, so importers keep all five as ordinary
identifiers (the receipts at the bottom of this file use them as `Nat`s).
`behavior := both` makes the token index reachable from a leading
identifier — without it none of these alternatives is ever tried. -/

declare_syntax_cat ccMove (behavior := both)

syntax (name := ccLiftMove) &"lift" (num)? : ccMove
syntax (name := ccMergeMove) &"merge" (num)? : ccMove
syntax (name := ccDropIdMove) &"drop_id" (num)? : ccMove
syntax (name := ccCommuteMove) &"commute" (num)? : ccMove
syntax (name := ccDropIdleMove) &"drop_idle" (num)? : ccMove

/-- Parse one move from its raw syntax; the optional numeral is the spine
depth (`0` = the root). -/
def Move.parseMove (stx : Syntax) : CommandElabM Move.Request := do
  let depth := if stx[1].isNone then 0 else stx[1][0].toNat
  if stx.isOfKind ``ccLiftMove then return { kind := .lift, depth }
  else if stx.isOfKind ``ccMergeMove then return { kind := .merge, depth }
  else if stx.isOfKind ``ccDropIdMove then return { kind := .dropId, depth }
  else if stx.isOfKind ``ccCommuteMove then return { kind := .commute, depth }
  else if stx.isOfKind ``ccDropIdleMove then return { kind := .dropIdle, depth }
  else throwError "unknown move{indentD stx}"

/-- `#cc_moves t`: the move menu — for every depth on the outer
attachment spine, the moves the TERM licenses there.  Applicability is
decided by the algebra (interfaces compared by `isDefEq`, side conditions
by `decide`), never by what the pill is called. -/
syntax (name := ccMovesCmd) "#cc_moves " term : command

@[command_elab ccMovesCmd] def elabCcMoves : CommandElab := fun stx => do
  let t : TSyntax `term := ⟨stx[1]⟩
  let rows ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    Move.menu (← instantiateMVars e)
  if rows.isEmpty then
    logInfo "no attachment node: no moves"
  else
    logInfo (String.intercalate "\n" (rows.map fun (d, head, kinds) =>
      let names := if kinds.isEmpty then "—"
        else String.intercalate ", " (kinds.map Move.Kind.word)
      s!"{d}  {head}  ⟶  {names}"))

/-- `#cc_rewrite t with [move, …]`: apply the moves in order.  The term
changes and the proof comes with it — each move is one lemma
application, the composite is checked by `Lean.Kernel.check` inside this
command, and the whole derivation is emitted as a `calc` chain the user
can paste as a `theorem`.

The receipt logs the moves with the lemma behind each, the resulting
TERM (`↦ …`), and the diagram of that term (the picture the moves
reached).  `with` is load-bearing for the D1 reason: `#cc_rewrite t
[merge]` already parses as an application to a list literal. -/
syntax (name := ccRewriteCmd) "#cc_rewrite " term
  (" with " "[" ccMove,* "]")? : command

@[command_elab ccRewriteCmd] def elabCcRewrite : CommandElab := fun stx => do
  let t : TSyntax `term := ⟨stx[1]⟩
  let reqs ←
    if stx[2].isNone then pure []
    else stx[2][2].getSepArgs.toList.mapM Move.parseMove
  let raw := ((t.raw.reprint.getD "?").replace "\n" " ").trimAscii.toString
  let head := String.intercalate " " ((raw.splitOn " ").filter (· != ""))
  let (trace, chain) ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let steps ← Move.run e reqs
    let (last, proof) ← Move.compose e steps
    Move.kernelCheck proof (← mkEq e last)
    let trace := String.intercalate "\n" (List.zipWith
      (fun (req : Move.Request) (step : Move.Step) =>
        s!"{req.kind.word} {req.depth}  ⟨{String.intercalate ", "
          (step.lemmas.map fun n => n.toString)}⟩")
      reqs steps)
    let shape ← Diagram.shapeWithDirs last []
    let chain ← Move.calcChain head steps
    return (s!"{trace}\n↦ {← Move.ppLine last}\n{Diagram.ascii shape}", chain)
  logInfo trace
  liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion stx (chain : String)

/-! ## Receipts -/

namespace MoveTests

open CarrierDemo AlgebraDemo
open scoped Converter ResourceSystem

/-! ### The matcher: applicability comes from the term

`toyR` provides `plain` at both parties.  At the root of a double
attachment the algebra licenses `lift`, `merge` and — because the inner
attachment already moved the interface to `masked` — `drop_idle`.  One
level down, only `lift`: there is nothing to merge with, and `u` still
provides `plain`, so that attachment is NOT idle.  Nothing here is read
off a label. -/

/-- info: 0  mask @ Party.u  ⟶  lift, merge, drop_idle
1  mask @ Party.u  ⟶  lift -/
#guard_msgs in
#cc_moves (mask •[Party.u] (mask •[Party.u] toyR))

-- The flagship `dec^{γ^B} enc^{γ^A} [KEY, AUT]`, with Jost's own Fig.-2.3
-- converters: each reaches the TWO interfaces its connection names, and its
-- inner side IS the service that connection faces, so NEITHER attachment is
-- idle.  `lift` and `merge` still want a `Σ`-word at an interface of R and a
-- `••[γ]` node has none; but `commute` now applies, because γ^B leaves alone
-- exactly the interface γ^A produced — Jost's *`img γ^B` misses `img γ^A`*.
-- At depth 1 the spine ends in `∥`, so there is no second attachment to
-- commute with, and the menu there is empty honestly.
/-- info: 0  decB @ gammaV  ⟶  commute
1  encA @ gammaU  ⟶  — -/
#guard_msgs in
#cc_moves CarrierDemo.constructedShape

-- The contrast, on the very same connections: a `.base`-source converter
-- IS idle — a connection faces `.sum plain plain`, which is not `mask`'s
-- source — and the matcher says so at BOTH depths.  `commute` is offered at
-- the root for the same reason as above: applicability of `commute` reads the
-- CONNECTIONS, applicability of `drop_idle` reads the SERVICES, and the two
-- tests are independent.
/-- info: 0  mask @ gammaV  ⟶  commute, drop_idle
1  mask @ gammaU  ⟶  drop_idle -/
#guard_msgs in
#cc_moves CarrierDemo.idleShape

-- One node, both readings: the paired-source converter on a connection
-- licenses no `drop_idle`; the base-source one does.
/-- info: 0  encA @ gammaU  ⟶  — -/
#guard_msgs in
#cc_moves (encA ••[gammaU] (toyR ∥ toyR))

/-- info: 0  mask @ gammaU  ⟶  drop_idle -/
#guard_msgs in
#cc_moves (mask ••[gammaU] (toyR ∥ toyR))

-- The neutral converter of `Σ`: `drop_id`, and nothing else.
/-- info: 0  id @ Party.u  ⟶  drop_id -/
#guard_msgs in
#cc_moves ((1 : Converters demoServices Party Party.u) • toyR)

-- The `∥` scope, as a receipt: a bare stack licenses NO move.  Maurer11
-- eq. (3) is a metric law and a metric law rewrites nothing; `par_comm`,
-- `par_assoc` and `par_distrib` are the module header's open items.
/-- info: no attachment node: no moves -/
#guard_msgs in
#cc_moves (toyR ∥ toyR)

/-! ### `lift` — `Converter.word_smul` -/

/-- info: lift 0  ⟨RandomSystems.CC.Converter.word_smul⟩
↦ mask.word Party.u • toyR
◠ mask @ Party.u
  □ toyR
---
info: Try this:
  [apply] calc (mask •[Party.u] toyR)
    _ = mask.word Party.u • toyR := (Converter.word_smul mask Party.u toyR).symm -/
#guard_msgs in
#cc_rewrite (mask •[Party.u] toyR) with [lift]

/-! ### `merge` — `Converters.comp_smul` (`mul_smul`) -/

/-- info: merge 0  ⟨RandomSystems.CC.Converter.word_smul, RandomSystems.CC.Converters.comp_smul⟩
↦ (mask.word Party.u * mask.word Party.u) • toyR
◠ mask.word Party.u * mask.word Party.u @ Party.u
  □ toyR
---
info: Try this:
  [apply] calc (mask •[Party.u] (mask •[Party.u] toyR))
    _ = (mask.word Party.u * mask.word Party.u) • toyR := (Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm -/
#guard_msgs in
#cc_rewrite (mask •[Party.u] (mask •[Party.u] toyR)) with [merge]

/-! ### `drop_id` — `Converters.id_smul` (`one_smul`) -/

/-- info: drop_id 0  ⟨RandomSystems.CC.Converters.id_smul⟩
↦ toyR
□ toyR
---
info: Try this:
  [apply] calc ((1 : Converters demoServices Party Party.u) • toyR)
    _ = toyR := Converters.id_smul toyR -/
#guard_msgs in
#cc_rewrite ((1 : Converters demoServices Party Party.u) • toyR) with [drop_id]

/-! ### `drop_id` on `•[i]` — `Converter.attachAt_id`

The other `drop_id`: not the `Σ`-unit but the identity CONVERTER.
`ofMaps id id` renames no letter, so attaching it returns the resource —
that is `Converter.attachAt_id`, the `e = f = Equiv.refl` case of "a
memoryless bijection converter is a relabelling"
(`DependentDDS.flatten_attach_ofMaps_eq_relabel`).  Applicability is
definitional, so `mask` — which is `ofMaps id (fun b => !b)` — is NOT
offered the move, at either depth. -/

/-- The memoryless identity converter, spelled as a named constant so the
matcher has to see through the definition rather than read a label. -/
noncomputable def idConv :
    Converter demoServices (.base .plain) (.base .plain) :=
  Converter.ofMaps id id

/-- info: 0  idConv @ Party.u  ⟶  lift, drop_id -/
#guard_msgs in
#cc_moves (idConv •[Party.u] toyR)

-- The contrast: `mask` renames the answer, so `drop_id` is absent even
-- though the node has exactly the same shape.
/-- info: 0  mask @ Party.u  ⟶  lift -/
#guard_msgs in
#cc_moves (mask •[Party.u] toyR)

/-- info: drop_id 0  ⟨RandomSystems.CC.Converter.attachAt_id⟩
↦ toyR
□ toyR
---
info: Try this:
  [apply] calc (idConv •[Party.u] toyR)
    _ = toyR := Converter.attachAt_id Party.u toyR -/
#guard_msgs in
#cc_rewrite (idConv •[Party.u] toyR) with [drop_id]

/-! ### `drop_id` at a CONNECTION — `Converter.attachAlong_id`

The γ-level unit law.  It does NOT return the resource: a connection
re-addresses two interfaces as one, and that half of `••[γ]` survives an
identity converter.  So the rewritten term is the merge, and the interface
set really has changed — which is exactly what `Converter.attachAlong_id`
says. -/

/-- The memoryless identity at the PAIRED service a connection faces: a
converter that reaches two interfaces and does nothing to either. -/
noncomputable def idPair :
    Converter demoServices
      (.sum (.base .plain) (.base .plain))
      (.sum (.base .plain) (.base .plain)) :=
  Converter.ofMaps id id

/-- info: 0  idPair @ gammaU  ⟶  drop_id -/
#guard_msgs in
#cc_moves (idPair ••[gammaU] (toyR ∥ toyR))

-- The contrast at the very same connection: `encA` acts, so it has no unit
-- law; `mask` misses the paired service the connection faces, so it is idle
-- for the OTHER reason (`drop_idle`, which leaves the same merge behind).
/-- info: 0  encA @ gammaU  ⟶  — -/
#guard_msgs in
#cc_moves (encA ••[gammaU] (toyR ∥ toyR))

/-- info: drop_id 0  ⟨RandomSystems.CC.Converter.attachAlong_id⟩
↦ ResourceSystem.mergeAlong gammaU (toyR ∥ toyR)
□ ResourceSystem.mergeAlong gammaU (t…
---
info: Try this:
  [apply] calc (idPair ••[gammaU] (toyR ∥ toyR))
    _ = ResourceSystem.mergeAlong gammaU (toyR ∥ toyR) := Converter.attachAlong_id gammaU (toyR ∥ toyR) -/
#guard_msgs in
#cc_rewrite (idPair ••[gammaU] (toyR ∥ toyR)) with [drop_id]

/-! ### `commute` — `Converter.attachAt_comm` -/

/-- info: commute 0  ⟨RandomSystems.CC.Converter.attachAt_comm⟩
↦ mask •[Party.u] mask •[Party.v] toyR
◠ mask @ Party.u
  ◠ mask @ Party.v
    □ toyR
---
info: Try this:
  [apply] calc (mask •[Party.v] (mask •[Party.u] toyR))
    _ = mask •[Party.u] mask •[Party.v] toyR := Converter.attachAt_comm (by decide) mask mask toyR -/
#guard_msgs in
#cc_rewrite (mask •[Party.v] (mask •[Party.u] toyR)) with [commute]

/-! ### `commute` at two CONNECTIONS — `Converter.attachAlong_comm`

The flagship, rewritten.  Both converters reach two interfaces, so neither
attachment is an interface-level one; what makes them commute is that `γ^B`
does not reach the interface `γ^A` produced.  The rewritten term keeps `γ^A`'s
MERGE where it was — a re-addressing changes the interface set and so has no
order to be exchanged with — and moves only the two ACTIONS past each other,
`encA` reappearing at the ordinary interface `γ^B` leaves for it. -/

/-- info: commute 0  ⟨RandomSystems.CC.Converter.attachAlong_comm⟩
↦ encA •[gammaV.relocate gammaU.produced] decB ••[gammaV] ResourceSystem.mergeAlong gammaU (toyR ∥ toyR)
◠ encA @ gammaV.relocate gammaU.produced
  ◠ decB @ gammaV ⟨Sum.inl Comp.key, Sum.inl Comp.aut⟩
    □ ResourceSystem.mergeAlong gammaU (t…
---
info: Try this:
  [apply] calc (decB ••[gammaV] (encA ••[gammaU] (toyR ∥ toyR)))
    _ = encA •[gammaV.relocate gammaU.produced] decB ••[gammaV] ResourceSystem.mergeAlong gammaU (toyR ∥ toyR) := Converter.attachAlong_comm encA decB gammaU gammaV (by decide) (toyR ∥ toyR) -/
#guard_msgs in
#cc_rewrite (decB ••[gammaV] (encA ••[gammaU] (toyR ∥ toyR))) with [commute]

/-! ### `drop_idle` — `Converter.attachAt_of_not_provides` -/

/-- info: drop_idle 0  ⟨RandomSystems.CC.Converter.attachAt_of_not_provides⟩
↦ mask •[Party.u] toyR
◠ mask @ Party.u
  □ toyR
---
info: Try this:
  [apply] calc (mask •[Party.u] (mask •[Party.u] toyR))
    _ = mask •[Party.u] toyR := Converter.attachAt_of_not_provides mask Party.u (mask •[Party.u] toyR) (by decide) -/
#guard_msgs in
#cc_rewrite (mask •[Party.u] (mask •[Party.u] toyR)) with [drop_idle]

-- …and the same move at a CONNECTION
-- (`Converter.attachAlong_of_not_provides`): what remains is the merge, and
-- it has to remain — the two interfaces really were addressed as one, so the
-- interface set changed even though the resource did not.
/-- info: drop_idle 0  ⟨RandomSystems.CC.Converter.attachAlong_of_not_provides⟩
↦ ResourceSystem.mergeAlong gammaU (toyR ∥ toyR)
□ ResourceSystem.mergeAlong gammaU (t…
---
info: Try this:
  [apply] calc (mask ••[gammaU] (toyR ∥ toyR))
    _ = ResourceSystem.mergeAlong gammaU (toyR ∥ toyR) := Converter.attachAlong_of_not_provides mask gammaU (toyR ∥ toyR) (by decide) -/
#guard_msgs in
#cc_rewrite (mask ••[gammaU] (toyR ∥ toyR)) with [drop_idle]

/-! ### `⊣` past a converter — `ResourceSystem.block_smul_of_ne` -/

/-- A converter on the three-party development, to commute past `⊣`. -/
noncomputable def flip3 : Converter services3 .plain .plain :=
  Converter.ofMaps id (fun b => !b)

/-- info: commute 0  ⟨RandomSystems.CC.ResourceSystem.block_smul_of_ne⟩
↦ flip3.word Party3.a • ⊣[Party3.e] toy3
◠ flip3 @ Party3.a
  ◠ ⊣ @ Party3.e
    □ toy3
---
info: Try this:
  [apply] calc (⊣[Party3.e] (Converter.word flip3 Party3.a • toy3))
    _ = flip3.word Party3.a • ⊣[Party3.e] toy3 := ResourceSystem.block_smul_of_ne (by decide) (flip3.word Party3.a) toy3 -/
#guard_msgs in
#cc_rewrite (⊣[Party3.e] (Converter.word flip3 Party3.a • toy3)) with [commute]

/-! ### Depth: a move below the root travels up by `congrArg` -/

/-- info: commute 1  ⟨RandomSystems.CC.Converter.attachAt_comm⟩
↦ mask •[Party.u] mask •[Party.u] mask •[Party.v] toyR
◠ mask @ Party.u
  ◠ mask @ Party.u
    ◠ mask @ Party.v
      □ toyR
---
info: Try this:
  [apply] calc (mask •[Party.u] (mask •[Party.v] (mask •[Party.u] toyR)))
    _ = mask •[Party.u] mask •[Party.u] mask •[Party.v] toyR := congrArg (fun R => mask •[Party.u] R) (Converter.attachAt_comm (by decide) mask mask toyR) -/
#guard_msgs in
#cc_rewrite (mask •[Party.u] (mask •[Party.v] (mask •[Party.u] toyR)))
  with [commute 1]

/-! ### A chain: several moves, one `calc` -/

/-- info: lift 1  ⟨RandomSystems.CC.Converter.word_smul⟩
merge 0  ⟨RandomSystems.CC.Converter.word_smul, RandomSystems.CC.Converters.comp_smul⟩
↦ (mask.word Party.u * mask.word Party.u) • toyR
◠ mask.word Party.u * mask.word Party.u @ Party.u
  □ toyR
---
info: Try this:
  [apply] calc (mask •[Party.u] (mask •[Party.u] toyR))
    _ = mask •[Party.u] mask.word Party.u • toyR := congrArg (fun R => mask •[Party.u] R) ((Converter.word_smul mask Party.u toyR).symm)
    _ = (mask.word Party.u * mask.word Party.u) • toyR := (Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm -/
#guard_msgs in
#cc_rewrite (mask •[Party.u] (mask •[Party.u] toyR)) with [lift 1, merge]

/-! ### A move the algebra does NOT license is not offered

`⊣` past `⊣` would need `ResourceSystem.block_comm`; asking for it is an
error, not a `sorry`. -/

/-- error: commute: `⊣` past `⊣` needs `ResourceSystem.block_comm` (unproved) -/
#guard_msgs in
#cc_rewrite (⊣[Party3.a] (⊣[Party3.e] toy3)) with [commute]

/-! ### End to end: the emitted `calc`, pasted back

The three theorems below are the suggestions above, copied out of the
`Try this` lines verbatim (only the `[apply]` chrome dropped).  They
compile, so the pictures the moves reached are the pictures of a
kernel-checked term — which is the whole point of D3. -/

theorem pasted_merge :
    mask •[Party.u] (mask •[Party.u] toyR) =
      (mask.word Party.u * mask.word Party.u) • toyR :=
  calc (mask •[Party.u] (mask •[Party.u] toyR))
    _ = (mask.word Party.u * mask.word Party.u) • toyR :=
      (Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm

theorem pasted_commute :
    mask •[Party.v] (mask •[Party.u] toyR) =
      mask •[Party.u] mask •[Party.v] toyR :=
  calc (mask •[Party.v] (mask •[Party.u] toyR))
    _ = mask •[Party.u] mask •[Party.v] toyR :=
      Converter.attachAt_comm (by decide) mask mask toyR

theorem pasted_chain :
    mask •[Party.u] (mask •[Party.u] toyR) =
      (mask.word Party.u * mask.word Party.u) • toyR :=
  calc (mask •[Party.u] (mask •[Party.u] toyR))
    _ = mask •[Party.u] mask.word Party.u • toyR :=
      congrArg (fun R => mask •[Party.u] R) ((Converter.word_smul mask Party.u toyR).symm)
    _ = (mask.word Party.u * mask.word Party.u) • toyR :=
      (Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm

theorem pasted_block :
    ⊣[Party3.e] (Converter.word flip3 Party3.a • toy3) =
      flip3.word Party3.a • ⊣[Party3.e] toy3 :=
  calc (⊣[Party3.e] (Converter.word flip3 Party3.a • toy3))
    _ = flip3.word Party3.a • ⊣[Party3.e] toy3 :=
      ResourceSystem.block_smul_of_ne (by decide) (flip3.word Party3.a) toy3

theorem pasted_drop_id : idConv •[Party.u] toyR = toyR :=
  calc (idConv •[Party.u] toyR)
    _ = toyR := Converter.attachAt_id Party.u toyR

theorem pasted_attachAlong_comm :
    decB ••[gammaV] (encA ••[gammaU] (toyR ∥ toyR)) =
      encA •[gammaV.relocate gammaU.produced]
        decB ••[gammaV] ResourceSystem.mergeAlong gammaU (toyR ∥ toyR) :=
  calc (decB ••[gammaV] (encA ••[gammaU] (toyR ∥ toyR)))
    _ = encA •[gammaV.relocate gammaU.produced] decB ••[gammaV] ResourceSystem.mergeAlong gammaU (toyR ∥ toyR) :=
      Converter.attachAlong_comm encA decB gammaU gammaV (by decide) (toyR ∥ toyR)

theorem pasted_drop_id_along :
    idPair ••[gammaU] (toyR ∥ toyR) =
      ResourceSystem.mergeAlong gammaU (toyR ∥ toyR) :=
  calc (idPair ••[gammaU] (toyR ∥ toyR))
    _ = ResourceSystem.mergeAlong gammaU (toyR ∥ toyR) :=
      Converter.attachAlong_id gammaU (toyR ∥ toyR)

/-- info: 'RandomSystems.CC.MoveTests.pasted_merge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_merge

/-- info: 'RandomSystems.CC.MoveTests.pasted_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_commute

/-- info: 'RandomSystems.CC.MoveTests.pasted_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_chain

/-- info: 'RandomSystems.CC.MoveTests.pasted_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_block

/-- info: 'RandomSystems.CC.MoveTests.pasted_drop_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_drop_id

/-- info: 'RandomSystems.CC.MoveTests.pasted_attachAlong_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_attachAlong_comm

/-- info: 'RandomSystems.CC.MoveTests.pasted_drop_id_along' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_drop_id_along

/-! ### `lift`, `merge`, `drop_id`, `commute`, `drop_idle` are not reserved

The move grammar matches its five words with `&"…"` (non-reserved), so
importers — and this very file — keep all five as plain identifiers. -/

def lift : Nat := 1
def merge : Nat := 2
def drop_id : Nat := 3
def commute : Nat := 4
def drop_idle : Nat := 5

example : lift + merge + drop_id + commute + drop_idle = 15 := rfl

end MoveTests

end RandomSystems.CC
