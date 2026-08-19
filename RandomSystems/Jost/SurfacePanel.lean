/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceGallery
import RandomSystems.Jost.SurfaceMoves
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.MakeEditLink

/-!
# The authoring surface, part 8: the interactive panel (D4) and the ε-rail (D5)

D3 gave the engine: `#cc_moves` says which algebra laws a node licenses and
`#cc_rewrite t with […]` applies them, emitting a kernel-checked `calc`.
D4 is a **user interface over that engine** — clicking a box in the diagram
applies a law and the proof grows — and D5 is the same rail over `≈[ε]`
instead of `=`, whose last line is the running bound, because the running
bound IS the theorem.

## What is live, and how

The one genuinely uncertain piece of the ladder was the round trip.  This
version of ProofWidgets (v0.0.95) supports RPC from a widget back into
Lean (`mk_rpc_widget%`), but such a component **cannot hold React state
and cannot pass closures to its children** (`Component/OfRpcMethod.lean`'s
own limitation list), so "click a node, a menu appears, click a move, the
term changes" cannot be a client-side state machine.

It does not have to be.  The state of a proof belongs in the **source
file**, and ProofWidgets ships `MakeEditLink`: a component whose `onClick`
applies an LSP edit.  So every click here is a *document edit* that
rewrites the `#cc_panel …` command itself, and the panel is a pure
function of the command it re-elaborates from:

* clicking a node writes `at [inner, left]` into the command — the panel
  comes back with that node selected and its move menu open;
* clicking a move writes it into the command's `with […]` list — the
  panel comes back with the term rewritten, the diagram redrawn from the
  NEW term, and one more step on the rail;
* `undo` drops the last move; `write calc below` inserts the finished
  `calc` chain into the file underneath the command.

Every one of those is live: a real click, a real edit, a real
re-elaboration, and the proof is re-checked by `Lean.Kernel.check` on
every one of them (`Move.kernelCheck`, D3's gate, unchanged).  Nothing
here is mocked, and nothing is copy-paste.  The one thing §12's mock asks
for that this mechanism cannot do is a *clipboard* write: a
Lean-authored widget cannot run `navigator.clipboard`, because it cannot
pass a closure to a DOM node.  `copy as calc` therefore ships as
`write calc below`, which inserts the chain into the file — strictly more
useful in an editor, and named for what it does.

The receipts below pin the loop itself, not a description of it: the
`— menu —` block of a `#cc_panel … at […]` prints the exact command source
each row's click writes, and the `— calc —` block prints the exact chain
the button inserts.  The chrome's geometry is measured in a real browser
(`.lake/cc_panel_chrome.html`, §12 item 11's discipline applied to
item 12's chrome), because "the hit target is the box" is a claim about
pixels and deserves a pixel gate — it is how the CSS child-combinator's
silent death inside a `<style>` element got caught.

## Node addressing: paths, not depths

D3 addressed a node by a `Nat` spine depth and its own report flagged that
as a stopgap: `R ∥ Q` has two children and a depth cannot name either.
A **path** (`Move.Path = List Move.Dir`, `inner`/`left`/`right`) can:

* `inner` descends an attachment's carrier (`α •[i] R ↦ R`) — this is
  exactly D3's depth step, so `Path.ofDepth k = replicate k inner`
  reproduces `#cc_rewrite`'s behaviour *including its emitted text* (the
  receipts below pin the two against each other);
* `left`/`right` descend a `∥`, which D3 could not address at all.

A move below the root is transported to the whole term by `congrArg`
through each enclosing frame — an attachment frame `fun R => α •[i] R` as
before, and now also `fun R => R ∥ Q` and `fun R => Q ∥ R`.

The renderer stamps every addressable box with its path in the `class`
attribute (`cc-at-Ril`, alongside the unchanged `cc-box`;
`Jost/SurfaceWidgets.lean`'s `nodeRoot`/`nodeInner`/`nodeLeft`/
`nodeRight`).  The panel reads those stamps back off its own rendered
tree, so a hit target is *by construction* the box the user sees, at the
box's own coordinates, in the box's own coordinate container — no second
layout pass, no coordinate arithmetic that could drift from the emitter.
`Path.encode`/`Path.decode?` are the wire format's two halves and are
pinned against the emitter's stamps below.

Two kinds of box are deliberately **not** addressable:

* a **fold-collapsed** node (D1 `fold`), which stands for several term
  nodes at once, so its path would name the wrong subterm — for the same
  reason `#cc_panel` accepts no view clause at all (a fold in the middle
  of a spine shifts every later node's address);
* a node the D3 matcher cannot decode.  `Diagram.ofExpr` and
  `Move.decode?` are written to mirror each other, but they are not the
  same function — `ResourceAt.attach` (the layout-indexed attachment
  demoted in favour of `•[i]`) draws as an attach node and decodes as
  nothing.  Such a node is drawn, and simply offers no moves; the node
  table in the receipt prints `—` for it.

## D5: the ε-rail

`#cc_close h with […]` chains closeness facts.  Every step is one carrier
lemma, and the composite is kernel-checked exactly as D4's is:

| step | what it does | the lemma |
|---|---|---|
| `attach α at i` | `L ≈[ε] R ↝ α•[i]L ≈[ε] α•[i]R` | `ResourceSystem.close_attachAt` (eq. (4)) |
| `smul γ` | the same for a `Σ` word | `Converters.close_smul` |
| `par h` | `L ≈[ε] R ↝ L∥L' ≈[ε+δ] R∥R'` | `ResourceSystem.close_par` (eq. (3)) |
| `par_left h` | the same with `h` on the left | `ResourceSystem.close_par` |
| `trans h` | chain: `ε ↝ ε + δ` | `ResourceSystem.close_trans` |
| `move m at [p]` | a D4 move on the right endpoint, at zero cost | `ResourceSystem.close_zero_iff` + `close_trans` |

There is no `refl` STEP because none is needed: the rail starts from a
term, and `ResourceSystem.close_refl R : R ≈[0] R` is one.

`move` is the bridge the brief asks for: a `=`-chain embedded in an
ε-chain.  The D4 move produces `M = N`; `close_zero_iff` turns that into
`M ≈[0] N`; `close_trans` appends it.  So the ε-panel's diagram is
clickable in exactly the way D4's is, and the rail's running bound picks
up `+ 0` — which is the honest accounting, not a cosmetic one.

`close_par` and `close_trans` carry `0 ≤ ε` side conditions (and they are
genuinely needed: `close` is `edist ≤ ENNReal.ofReal ε`, and
`ENNReal.ofReal` truncates, so `L ≈[ε] R` does NOT imply `0 ≤ ε`).  They
are discharged by `norm_num`/`positivity` on the ε the step actually
produces; a step whose side condition does not close is **not offered**,
D3's rule.  Consequence, stated rather than hidden: with a *symbolic* ε
and no `0 ≤ ε` in scope — a command has no local context to draw on —
`par` and `trans` are unavailable.

## ε-steps NOT implemented, and the exact lemma each one is missing

* **`block`** (`L ≈[ε] R ↝ ⊣[i]L ≈[ε] ⊣[i]R`).  The *lemma* now exists:
  `ResourceSystem.close_block` (`Jost/SurfaceAlgebra.lean`).  The
  obstruction this file used to record — `⊣[i] L` and `⊣[i] R` attach
  `Converter.bot (L.layoutAt i)` and `Converter.bot (R.layoutAt i)`, two
  different terms — does not survive: `L ≈[ε] R` already forces the two
  layouts to agree (`ResourceSystem.layoutAt_eq_of_close`), so the
  converters coincide and `close_attachAt` applies with no extra
  hypothesis.  Missing is only the panel step that fires it.
* **metric `par_comm` / `par_assoc`** (`L ∥ Q ≈[0] Q ∥ L`).  Not even
  well-typed as stated: at disjoint interface sets the two sides live at
  `I ⊕ J` and `J ⊕ I`.  What is missing is no longer a re-CODING (the old
  merged `∥` needed one because `SumService.sum` is injective and the two
  sides provided different services); it is only a surface
  `ResourceSystem.reindex` along `Equiv.sumComm`, and the kernel already
  has that re-indexing AND its isometry (`DependentRandomSystem.reindex`,
  `edist_reindex`, `TypedTensor.lean`).
* **`par` at the layout-indexed quotient.**  `ResourceAt.close_par`
  exists and is a different carrier (`ResourceAt S layout`); this
  panel speaks the bundled carrier only.  A mixed chain would need the
  `ofLayout` bridge as a rail step, which is not written.

## Grammar

Reservation-free in the D1/D3 sense: `inner`, `left`, `right`, `attach`,
`smul`, `par`, `par_left`, `trans` and `move` are matched as NON-reserved
words (`&"…"`), and the receipts at the bottom of this file use all of
them as ordinary identifiers.  `with` and `at` introduce the two clauses
and reserve nothing new — both are already Lean core tokens (`at` is: a
plain `def at : Nat` does not parse in a stock file).
`declare_syntax_cat … (behavior := both)` is what makes a leading
identifier find the token index, as in D1/D3.
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource
open Lean Elab Command Meta ProofWidgets Server

namespace Move

/-! ## Paths -/

/-- One step of a node address.  `inner` descends an attachment's carrier
(D3's depth step); `inl`/`inr` descend a `∥`, which a depth cannot name. -/
inductive Dir where
  | inner
  | inl
  | inr
  deriving DecidableEq, Repr, Inhabited

/-- A node address: the steps from the root, outermost first. -/
abbrev Path := List Dir

/-- The wire letter of a step — the emitter's `class` stamp alphabet
(`Diagram.nodeInner`/`nodeLeft`/`nodeRight`). -/
def Dir.letter : Dir → Char
  | .inner => 'i'
  | .inl => 'l'
  | .inr => 'r'

/-- The surface word of a step: what the grammar accepts and the receipts
print. -/
def Dir.word : Dir → String
  | .inner => "inner"
  | .inl => "left"
  | .inr => "right"

/-- A path as the emitter stamps it (`R`, `Ri`, `Ril`, …). -/
def Path.encode (path : Path) : String :=
  Diagram.nodeRoot ++ String.ofList (path.map Dir.letter)

/-- Read back an emitter stamp; `none` if it is not one. -/
def Path.decode? (s : String) : Option Path := do
  guard (s.startsWith Diagram.nodeRoot)
  (s.drop Diagram.nodeRoot.length).toString.toList.mapM fun c =>
    if c == 'i' then some Dir.inner
    else if c == 'l' then some Dir.inl
    else if c == 'r' then some Dir.inr
    else none

/-- A path in the grammar's own syntax (`inner, left`). -/
def Path.words (path : Path) : String :=
  String.intercalate ", " (path.map Dir.word)

/-- D3's `Nat` spine depth, as a path: `k` steps down the carrier.  This
is what keeps `#cc_rewrite`'s addressing working unchanged. -/
def Path.ofDepth (depth : Nat) : Path := List.replicate depth .inner

/-! ## Descending a path -/

/-- Decode a `∥` node — the head constants `Diagram.ofExpr` draws as a
stack.  Returns the head and its full argument array, so the node can be
rebuilt with either component replaced. -/
def decodePar? (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
  let f := e.getAppFn
  let args := e.getAppArgs
  let .const n _ := f
    | return none
  if (n == ``RandomSystems.CC.ResourceSystem.par ∨
      n == ``RandomSystems.CC.ResourceAt.par ∨
      n == ``RandomSystems.CC.Resource.par) ∧ args.size ≥ 2 then
    return some (f, args)
  return none

/-- One enclosing context of a node: the frame a move below it travels up
through by `congrArg`. -/
inductive Frame where
  /-- `fun R => α •[i] R` (also `γ • R`, `⊣[i] R`) — D3's frame. -/
  | node (nd : Node)
  /-- `fun R => R ∥ Q`. -/
  | parL (fn : Expr) (args : Array Expr)
  /-- `fun R => Q ∥ R`. -/
  | parR (fn : Expr) (args : Array Expr)

/-- Rebuild the frame around a different subterm. -/
def Frame.rebuild : Frame → Expr → Expr
  | .node nd, x => nd.withResource x
  | .parL fn args, x => mkAppN fn (args.set! (args.size - 2) x)
  | .parR fn args, x => mkAppN fn (args.set! (args.size - 1) x)

/-- The frame as a `congrArg` motive `fun R => …`. -/
def Frame.motive : Frame → MetaM Expr
  | .node nd => nd.frame
  | .parL fn args => do
      let ty ← inferType args[args.size - 2]!
      return .lam `R ty (mkAppN fn (args.set! (args.size - 2) (.bvar 0)))
        .default
  | .parR fn args => do
      let ty ← inferType args[args.size - 1]!
      return .lam `R ty (mkAppN fn (args.set! (args.size - 1) (.bvar 0)))
        .default

/-- Descend a path, returning the subterm and the frames above it
(outermost first).  Fails — loudly — when the path does not describe the
term; the panel only ever hands it paths it read off its own render. -/
partial def descendPath (e : Expr) : Path → MetaM (Expr × List Frame)
  | [] => return (e, [])
  | .inner :: rest => do
      let some nd ← decode? e
        | throwError "path: `inner` here is not an attachment node{indentExpr e}"
      let (sub, frames) ← descendPath nd.carrier rest
      return (sub, .node nd :: frames)
  | .inl :: rest => do
      let some (fn, args) ← decodePar? e
        | throwError "path: `left` here is not a `∥` node{indentExpr e}"
      let (sub, frames) ← descendPath args[args.size - 2]! rest
      return (sub, .parL fn args :: frames)
  | .inr :: rest => do
      let some (fn, args) ← decodePar? e
        | throwError "path: `right` here is not a `∥` node{indentExpr e}"
      let (sub, frames) ← descendPath args[args.size - 1]! rest
      return (sub, .parR fn args :: frames)

/-- Apply a move at a path: proved at the node, transported to the whole
term by `congrArg` through each enclosing frame.  At `Path.ofDepth k` this
is `Move.applyRequest` with `depth := k`, term for term. -/
def applyAt (e : Expr) (kind : Kind) (path : Path) : MetaM Step := do
  let (sub, frames) ← descendPath e path
  let step ← rootStep kind sub
  let mut before := step.before
  let mut after := step.after
  let mut proof := step.proof
  let mut text := step.justification
  for fr in frames.reverse do
    let motive ← fr.motive
    let before' := fr.rebuild before
    let after' := fr.rebuild after
    proof ← mkExpectedTypeHint (← mkCongrArg motive proof)
      (← mkEq before' after')
    text := s!"congrArg ({← ppLine motive}) ({text})"
    before := before'
    after := after'
  return { step with before, after, proof, justification := text }

/-- A move together with the path it acts at. -/
structure PathRequest where
  kind : Kind
  path : Path := []
  deriving Inhabited

/-- The request in the grammar's own syntax — this is the text the panel
writes back into the command. -/
def PathRequest.text (req : PathRequest) : String :=
  if req.path.isEmpty then req.kind.word
  else s!"{req.kind.word} at [{Path.words req.path}]"

/-- Apply a list of path-addressed moves in order, keeping every step. -/
def runPath (e : Expr) (reqs : List PathRequest) : MetaM (List Step) := do
  let mut cur := e
  let mut steps : List Step := []
  for req in reqs do
    let step ← applyAt cur req.kind req.path
    steps := steps ++ [step]
    cur := step.after
  return steps

/-- The move menu at a path: every move the term licenses there, WITH the
lemma each one cites (the menu's right-hand column).  `none` when the path
does not resolve in the term — a node the matcher cannot decode is drawn
but offers nothing. -/
def menuAtPath (e : Expr) (path : Path) :
    MetaM (Option (List (Kind × List Name))) := do
  match ← (try (some <$> descendPath e path) catch _ => pure none) with
  | none => return none
  | some (sub, _) =>
      let mut out : List (Kind × List Name) := []
      for kind in allKinds do
        let step? ← try (some <$> rootStep kind sub) catch _ => pure none
        if let some step := step? then out := out ++ [(kind, step.lemmas)]
      return some out

/-- A cited lemma, as the menu and the rail print it: the surface name,
with the ambient `RandomSystems.CC` prefix dropped. -/
def lawName (n : Name) : String := (n.replacePrefix `RandomSystems.CC .anonymous).toString

/-- The laws of a step, joined — the grey right-hand column. -/
def lawText (ns : List Name) : String :=
  String.intercalate ", " (ns.map lawName)

end Move

/-! ## The ε-rail engine (D5) -/

namespace Close

open Move

/-- A closeness fact in flight: `lhs ≈[eps] rhs`, and its proof. -/
structure Fact where
  eps : Expr
  lhs : Expr
  rhs : Expr
  proof : Expr

/-- Read `L ≈[ε] R` off a type (`ResourceSystem.close ε L R`). -/
def ofType? (ty : Expr) : Option (Expr × Expr × Expr) :=
  let args := ty.getAppArgs
  match ty.getAppFn with
  | .const n _ =>
      if n == ``RandomSystems.CC.ResourceSystem.close ∧ args.size ≥ 3 then
        some (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)
      else none
  | _ => none

/-- The fact a term proves. -/
def Fact.ofProof (proof : Expr) : MetaM Fact := do
  let ty ← instantiateMVars (← inferType proof)
  let some (eps, lhs, rhs) := ofType? ty
    | throwError "expected a closeness fact `L ≈[ε] R`, got{indentExpr ty}"
  return { eps, lhs, rhs, proof }

/-- `0 ≤ ε`, as this carrier's lemmas state it. -/
def nonnegGoal (eps : Expr) : MetaM Expr := do
  let ty ← inferType eps
  let zero ← mkAppOptM ``OfNat.ofNat #[ty, mkRawNatLit 0, none]
  mkAppM ``LE.le #[zero, eps]

/-- Discharge `0 ≤ ε` by `norm_num`, then `positivity`.  `none` when
neither closes it — and then the step is simply not offered, D3's rule.
The side condition is real: `ENNReal.ofReal` truncates, so `L ≈[ε] R` does
not imply `0 ≤ ε`. -/
def nonneg? (eps : Expr) : TermElabM (Option Expr) := do
  try
    let goal ← nonnegGoal eps
    let mv ← mkFreshExprSyntheticOpaqueMVar goal
    let remaining ← Lean.Elab.Tactic.run mv.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic| first | norm_num | positivity))
    if remaining.isEmpty then
      let prf ← instantiateMVars mv
      if prf.hasExprMVar then return none else return some prf
    else return none
  catch _ => return none

/-- One rung of the ε-rail: the fact it reaches, the law it cites, the
surface text of the step that produced it, and the pasteable proof term.
`just` carries the marker `%p` where the PREVIOUS rung's name goes, so
`haveChain` can name the intermediate steps. -/
structure Rung where
  fact : Fact
  lemmas : List Name
  text : String
  just : String

/-- A step of the ε-rail, as the grammar accepts it. -/
inductive CStep where
  /-- `attach α at i` — eq. (4). -/
  | attach (conv iface : Syntax)
  /-- `smul γ` — eq. (4) for all of `Σ`. -/
  | smul (gamma : Syntax)
  /-- `par h` — eq. (3), the current fact on the LEFT. -/
  | par (other : Syntax)
  /-- `par_left h` — eq. (3), the current fact on the RIGHT. -/
  | parLeft (other : Syntax)
  /-- `trans h` — the triangle inequality. -/
  | trans (other : Syntax)
  /-- `move m at [p]` — a D4 move on the right endpoint, at zero cost. -/
  | move (req : PathRequest)

/-- The step in the grammar's own syntax — the text the panel writes back
into the command. -/
def CStep.text : CStep → String
  | .attach c i =>
      s!"attach {(c.reprint.getD "?").trimAscii} at {(i.reprint.getD "?").trimAscii}"
  | .smul g => s!"smul {(g.reprint.getD "?").trimAscii}"
  | .par h => s!"par {(h.reprint.getD "?").trimAscii}"
  | .parLeft h => s!"par_left {(h.reprint.getD "?").trimAscii}"
  | .trans h => s!"trans {(h.reprint.getD "?").trimAscii}"
  | .move req => s!"move {req.text}"

/-- Apply one ε-step to the current fact. -/
def apply (cur : Fact) : CStep → TermElabM Rung
  | .attach convStx ifaceStx => do
      let conv ← Term.elabTerm convStx none
      let iface ← Term.elabTerm ifaceStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← mkAppM ``RandomSystems.CC.ResourceSystem.close_attachAt
        #[← instantiateMVars conv, ← instantiateMVars iface, cur.proof]
      return { fact := ← Fact.ofProof proof,
               lemmas := [``RandomSystems.CC.ResourceSystem.close_attachAt],
               text := CStep.text (.attach convStx ifaceStx),
               just := s!"ResourceSystem.close_attachAt \
{(convStx.reprint.getD "?").trimAscii} \
{(ifaceStx.reprint.getD "?").trimAscii} %p" }
  | .smul gammaStx => do
      let gamma ← Term.elabTerm gammaStx none
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← mkAppM ``RandomSystems.CC.Converters.close_smul
        #[← instantiateMVars gamma, cur.proof]
      return { fact := ← Fact.ofProof proof,
               lemmas := [``RandomSystems.CC.Converters.close_smul],
               text := CStep.text (.smul gammaStx),
               just := s!"Converters.close_smul \
{(gammaStx.reprint.getD "?").trimAscii} %p" }
  | .par otherStx => do
      let other ← Fact.ofProof (← elabFact otherStx)
      let some nl ← nonneg? cur.eps
        | throwError "par: `0 ≤ {← ppLine cur.eps}` does not close \
(norm_num, positivity)"
      let some nr ← nonneg? other.eps
        | throwError "par: `0 ≤ {← ppLine other.eps}` does not close \
(norm_num, positivity)"
      let proof ← mkAppM ``RandomSystems.CC.ResourceSystem.close_par
        #[nl, nr, cur.proof, other.proof]
      return { fact := ← Fact.ofProof proof,
               lemmas := [``RandomSystems.CC.ResourceSystem.close_par],
               text := CStep.text (.par otherStx),
               just := s!"ResourceSystem.close_par (by norm_num) (by norm_num) \
%p {(otherStx.reprint.getD "?").trimAscii}" }
  | .parLeft otherStx => do
      let other ← Fact.ofProof (← elabFact otherStx)
      let some nl ← nonneg? other.eps
        | throwError "par_left: `0 ≤ {← ppLine other.eps}` does not close \
(norm_num, positivity)"
      let some nr ← nonneg? cur.eps
        | throwError "par_left: `0 ≤ {← ppLine cur.eps}` does not close \
(norm_num, positivity)"
      let proof ← mkAppM ``RandomSystems.CC.ResourceSystem.close_par
        #[nl, nr, other.proof, cur.proof]
      return { fact := ← Fact.ofProof proof,
               lemmas := [``RandomSystems.CC.ResourceSystem.close_par],
               text := CStep.text (.parLeft otherStx),
               just := s!"ResourceSystem.close_par (by norm_num) (by norm_num) \
{(otherStx.reprint.getD "?").trimAscii} %p" }
  | .trans otherStx => do
      let other ← Fact.ofProof (← elabFact otherStx)
      let some nl ← nonneg? cur.eps
        | throwError "trans: `0 ≤ {← ppLine cur.eps}` does not close \
(norm_num, positivity)"
      let some nr ← nonneg? other.eps
        | throwError "trans: `0 ≤ {← ppLine other.eps}` does not close \
(norm_num, positivity)"
      let proof ← mkAppM ``RandomSystems.CC.ResourceSystem.close_trans
        #[nl, nr, cur.proof, other.proof]
      return { fact := ← Fact.ofProof proof,
               lemmas := [``RandomSystems.CC.ResourceSystem.close_trans],
               text := CStep.text (.trans otherStx),
               just := s!"ResourceSystem.close_trans (by norm_num) (by norm_num) \
%p {(otherStx.reprint.getD "?").trimAscii}" }
  | .move req => do
      -- the bridge: a D4 `=`-step, embedded in the ε-chain at zero cost
      let step ← applyAt cur.rhs req.kind req.path
      let zero ← mkAppM ``RandomSystems.CC.ResourceSystem.close_zero_iff
        #[step.before, step.after]
      let zeroClose ← mkAppM ``Iff.mpr #[zero, step.proof]
      let some nl ← nonneg? cur.eps
        | throwError "move: `0 ≤ {← ppLine cur.eps}` does not close \
(norm_num, positivity)"
      let zeroEps ← (do
        let some (eps, _, _) := ofType? (← instantiateMVars (← inferType zeroClose))
          | throwError "move: the zero step is not a closeness fact"
        pure eps)
      let some nr ← nonneg? zeroEps
        | throwError "move: `0 ≤ 0` does not close (unreachable)"
      let proof ← mkAppM ``RandomSystems.CC.ResourceSystem.close_trans
        #[nl, nr, cur.proof, zeroClose]
      return { fact := ← Fact.ofProof proof,
               lemmas := step.lemmas ++
                 [``RandomSystems.CC.ResourceSystem.close_zero_iff,
                  ``RandomSystems.CC.ResourceSystem.close_trans],
               text := CStep.text (.move req),
               just := s!"ResourceSystem.close_trans (by norm_num) (by norm_num) \
%p ((ResourceSystem.close_zero_iff _ _).mpr ({step.justification}))" }
where
  elabFact (stx : Syntax) : TermElabM Expr := do
    let e ← Term.elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

/-- Run the whole rail. -/
def run (start : Fact) (steps : List CStep) : TermElabM (List Rung) := do
  let mut cur := start
  let mut out : List Rung := []
  for step in steps do
    let rung ← apply cur step
    out := out ++ [rung]
    cur := rung.fact
  return out

end Close

/-! ## The panel widget

`Diagram.html` already owns the coordinate system: one
`position: relative` container per diagram, every box an absolutely
positioned child at emitter-computed coordinates.  The panel therefore
never computes a coordinate: it appends its hit targets and its menu as
further children of THAT container, reading each hit's rectangle straight
off the box's own `style`.  A hit is the box, by construction, and the
geometry audit cannot be disturbed because nothing the panel adds is a
`cc-box`, `cc-boundary`, `cc-wire` or `cc-tag`. -/

namespace Panel

open Move

/-- **R1's legibility floor and its cap**, in CSS pixels, per label kind
(box label, wire tag, corner name).  The floor is the smallest size at
which a label may render; the cap is the largest size the item-1 grid can
still hold — a 12-codepoint resource label in a 120px box measures ≈101px
at 14px monospace and ≈108px at 15px, and a converter's 8-codepoint budget
in a 76px pill measures 67px at 14px and 72px at 15px, which is the inner
width exactly.  So 14 is the cap, not a taste.

Between them the size follows the READER's own font (`em`), because the
infoview inherits the editor's setting and a hard-coded pixel size is the
actual defect behind "the labels are too small": a reader who raises the
editor font currently gets nothing.

These are the numbers the CSS and the browser gate both read, so the gate
cannot drift from the rule — the same discipline `Diagram.framePad` and
`Diagram.forkPitch` already apply to the geometry audit. -/
def fontScale : List (String × Nat × Nat) :=
  [("box", 13, 14), ("tag", 12, 13), ("corner", 11, 12)]

/-- The R1 declarations: one custom property per kind, floored and capped,
`em`-scaled between. -/
def fontVars : List String :=
  fontScale.map fun (kind, floor, cap) =>
    let scale := if kind == "box" then "0.95" else if kind == "tag" then "0.85"
      else "0.8"
    s!"  --cc-font-{kind}: clamp({floor}px, {scale}em, {cap}px);"

/-- The DESIGN §12 chrome, as one scoped stylesheet.  Every rule is under
`.cc-panel`, so nothing here can reach the rest of the infoview.  Item 12
is literal about the treatment: hover is a 2px ROLE-COLOUR OFFSET OUTLINE
and never a fill (the hit inherits the box's own `color`, so
`currentColor` IS the role colour, and `outline` does not participate in
layout — the geometry beneath is untouched); the menu lists moves with
their law names right-aligned in grey; the rail alternates term lines with
relation lines; buttons are bordered text.  No icons, no shadows, no
gradients; `'JetBrains Mono'` throughout.  Item 20 governs the overlay:
anchored over its object, the diagram left visible beneath and dimmed by
opacity (`color.ui.lensDim`), 1px bordered opaque panel at token radius,
dismissal by a drawn small cross (and by clicking the node again).

**Three media rules ride here** (`sketches/visual-scenarios.md`), because
the infoview is a user-resizable panel and the emitter's natural size is
fixed by item 1:

* **R1, the legibility floor.**  Label sizes are tokens
  (`--cc-font-box`/`--cc-font-tag`/`--cc-font-corner`), floored by
  `clamp` and scaled by the reader's own `em` between the floor and a cap
  the item-1 grid can still hold (a 12-codepoint label in a 120px box at
  14px monospace is ≈101px — it fits; at 15px it does not).  The rules
  carry `!important` for ONE reason: the emitter writes `font-size` as an
  inline style, and an important author declaration is the only thing in
  the cascade that outranks a style attribute.  The moment
  `Jost/SurfaceWidgets.lean` emits `var(--cc-font-box, 13px)` instead of
  `13px`, the three `!important`s can be deleted unchanged — that is the
  whole content of the token request in the report.
* **R3, overflow not scale.**  The stage is a SCROLL CONTAINER at
  `max-width: 100%`; the diagram keeps its emitter-computed natural size
  and the reader pans.  Nothing is ever scaled, so every audited pixel
  survives.  The panel is a WRAPPING flex row, so a rail that no longer
  fits beside the stage goes underneath it rather than shrinking it or
  being painted over.  Chrome that hangs below the diagram (the move
  menu, the open lens) reserves its own room via `:has()` — without it
  the stage merely grows a scrollbar, so the degradation is safe on an
  engine that lacks `:has()`.
* **R2, orientation is semantic**, is honoured by omission: no rule here
  rotates, mirrors, or reflows anything INSIDE a `.cc-diagram`.  Party
  flanks stay left/right, free above, adversary below at every width.

Serializer discipline: this string is emitted as the text of a `style`
element, and `Gallery.htmlString` escapes `&`, `<`, `>` and `"` in text.
A rule containing any of them would silently die as `&gt;` — which is how
the child-combinator bug got in.  Hence descendant combinators only, no
attribute values in double quotes, and a receipt below that checks the
four characters are absent. -/
def css : String := String.intercalate "\n" ([
  -- the media tokens: R1's floor, the lens box (§12 item 25's
  -- `space.lensPad`, `size.lens.maxW`, `size.lens.maxH`), and the room the
  -- hanging chrome reserves in the scroll container
  ".cc-panel { display: flex; flex-direction: row; flex-wrap: wrap;",
  "  align-items: flex-start; column-gap: 16px; row-gap: 12px;",
  "  max-width: 100%; box-sizing: border-box;",
  "  font-family: 'JetBrains Mono', ui-monospace, monospace;"] ++
  fontVars ++ [
  "  --cc-lens-maxw: 340px; --cc-lens-maxh: 220px; --cc-lens-pad: 8px;",
  "  --cc-menu-reserve: 128px; }",
  -- R1: the floor, overriding the emitter's inline `font-size`
  ".cc-panel .cc-box { font-size: var(--cc-font-box) !important; }",
  ".cc-panel .cc-tag { font-size: var(--cc-font-tag) !important; }",
  ".cc-panel .cc-corner { font-size: var(--cc-font-corner) !important; }",
  -- R3: natural size inside a scroll container, never a scale
  ".cc-panel .cc-stage { position: relative; flex: 1 1 auto; min-width: 0;",
  "  max-width: 100%; overflow: auto; overscroll-behavior: contain; }",
  ".cc-panel .cc-stage:has(.cc-ui-menu) {",
  "  padding-bottom: var(--cc-menu-reserve); }",
  ".cc-panel .cc-stage:has(.cc-lens[open]) {",
  "  padding-bottom: var(--cc-lens-maxh); }",
  ".cc-panel .cc-hit { position: absolute; box-sizing: border-box;",
  "  background: transparent; }",
  -- descendant, never a child combinator: `>` inside a `<style>` element
  -- is raw text in HTML, so an escaping serializer would break the rule
  ".cc-panel .cc-hit a { display: block; width: 100%; height: 100%;",
  "  text-decoration: none; opacity: 1; }",
  ".cc-panel .cc-hit:hover, .cc-panel .cc-hit.cc-sel {",
  "  outline: 2px solid currentColor; outline-offset: 2px; }",
  ".cc-panel .cc-dim .cc-box, .cc-panel .cc-dim .cc-wire,",
  ".cc-panel .cc-dim .cc-tag, .cc-panel .cc-dim .cc-boundary,",
  ".cc-panel .cc-dim .cc-deck, .cc-panel .cc-dim .cc-corner { opacity: 0.45; }",
  ".cc-panel .cc-ui-menu { position: absolute; z-index: 5; background: #FFFFFF;",
  "  border: 1px solid #888888; border-radius: 4px; padding: 3px 0;",
  "  font-size: 11px; min-width: 176px; }",
  ".cc-panel .cc-ui-head { display: flex; justify-content: space-between;",
  "  column-gap: 18px; padding: 2px 10px 4px; font-size: 10px; color: #888888;",
  "  border-bottom: 1px solid #888888; }",
  ".cc-panel .cc-ui-menu a { display: block; color: inherit;",
  "  text-decoration: none; opacity: 1; }",
  ".cc-panel .cc-ui-row { display: flex; justify-content: space-between;",
  "  column-gap: 24px; padding: 3px 10px; }",
  ".cc-panel .cc-ui-row:hover { background: #FAFAFA; }",
  ".cc-panel .cc-ui-law { color: #888888; }",
  ".cc-panel .cc-ui-none { padding: 3px 10px; color: #888888; }",
  ".cc-panel .cc-rail { width: 290px; max-width: 100%; flex: 0 1 auto;",
  "  box-sizing: border-box; background: #FAFAFA;",
  "  border: 1px solid #888888; border-radius: 4px; padding: 8px 10px;",
  "  font-size: 11px; }",
  ".cc-panel .cc-rail-cap { font-size: 10px; color: #888888; padding-bottom: 4px; }",
  ".cc-panel .cc-rail-term { white-space: pre; overflow-x: auto; padding: 1px 0; }",
  ".cc-panel .cc-rail-rel { display: flex; justify-content: space-between;",
  "  column-gap: 16px; color: #555555; padding: 1px 0; }",
  ".cc-panel .cc-rail-law { color: #888888; white-space: nowrap; }",
  ".cc-panel .cc-rail-acc { margin-top: 6px; border-top: 1px solid #888888;",
  "  padding-top: 6px; white-space: pre; overflow-x: auto; }",
  ".cc-panel .cc-ui-btn { display: inline-block; border: 1px solid #888888;",
  "  border-radius: 3px; padding: 2px 8px; font-size: 10px; color: inherit;",
  "  text-decoration: none; margin: 8px 6px 0 0; opacity: 1; }",
  -- the lens (§12 items 20 and 21): a `details` whose `summary` IS the
  -- item-21 identity tab, so open, dismiss, and keyboard access are one
  -- native control and no React state is involved
  ".cc-panel .cc-lens { position: absolute; z-index: 6; }",
  ".cc-panel .cc-lens summary { display: inline-block; list-style: none;",
  "  cursor: pointer; background: #EEEEEE; border: 1px solid #888888;",
  "  border-radius: 4px; padding: 0 5px; color: #555555;",
  "  font-size: var(--cc-font-corner); line-height: 15px;",
  "  white-space: nowrap; user-select: none; position: relative;",
  "  max-width: var(--cc-lens-maxw); overflow: hidden;",
  "  text-overflow: ellipsis; z-index: 7; }",
  ".cc-panel .cc-lens summary::-webkit-details-marker { display: none; }",
  ".cc-panel .cc-lens summary::marker { content: ''; }",
  ".cc-panel .cc-lens-x { color: #888888; padding-left: 6px; }",
  ".cc-panel .cc-lens-body { position: absolute; left: 0; top: 9px;",
  "  background: #FFFFFF; border: 1px solid #888888; border-radius: 4px;",
  "  padding: var(--cc-lens-pad); padding-top: 12px;",
  "  max-width: var(--cc-lens-maxw); max-height: var(--cc-lens-maxh);",
  "  overflow: auto; white-space: pre; color: #333333;",
  "  font-size: var(--cc-font-corner); line-height: 15px; }",
  -- item 21: the panel takes the SHAPE of the box it inspects — a
  -- resource is sharp, a converter or simulator rounded
  ".cc-panel .cc-lens-sharp .cc-lens-body { border-radius: 0; }",
  -- closed is closed, on every engine: a `details` that merely skips its
  -- contents is not a measurable state
  ".cc-panel .cc-lens:not([open]) .cc-lens-body { display: none; }",
  -- item 20c: context preserved, dimmed, never hidden.  Same declaration
  -- as `.cc-dim`, fired by the lens's own open state
  ".cc-panel .cc-diagram:has(.cc-lens[open]) .cc-box,",
  ".cc-panel .cc-diagram:has(.cc-lens[open]) .cc-wire,",
  ".cc-panel .cc-diagram:has(.cc-lens[open]) .cc-tag,",
  ".cc-panel .cc-diagram:has(.cc-lens[open]) .cc-boundary,",
  ".cc-panel .cc-diagram:has(.cc-lens[open]) .cc-deck,",
  ".cc-panel .cc-diagram:has(.cc-lens[open]) .cc-corner { opacity: 0.45; }"])

/-! ### Reading the render back

Every addressable box carries its path in `class` (`cc-at-…`).  The panel
finds them by walking the tree it just built, so a hit is never anywhere
but on the box the user sees. -/

/-- The value of an attribute, if present. -/
def attr? (attrs : Array (String × Json)) (key : String) : Option Json :=
  (attrs.find? fun a => a.1 == key).map (·.2)

/-- A field of a React style object, as a CSS string. -/
def styleField? (style : Json) (key : String) : Option String :=
  match style.getObjVal? key with
  | .ok v => v.getStr?.toOption
  | .error _ => none

/-- The `cc-at-…` token of a class string, decoded. -/
def classPath? (cls : String) : Option String :=
  ((cls.splitOn " ").find? fun t => t.startsWith "cc-at-").map
    (fun t => (t.drop 6).toString)

/-- Is this element a diagram's coordinate container? -/
def isDiagramBox (attrs : Array (String × Json)) : Bool :=
  match (attr? attrs "class").bind (fun j => j.getStr?.toOption) with
  | some cls => (cls.splitOn " ").contains "cc-diagram"
  | none => false

/-- Every addressable box of a rendered tree: its encoded path and its
`style` object, in document order. -/
partial def addressed (h : Html) : Array (String × Json) :=
  go #[] h
where
  go (acc : Array (String × Json)) : Html → Array (String × Json)
    | .element _ attrs children =>
        let acc :=
          match (attr? attrs "class").bind (fun j => j.getStr?.toOption) with
          | some cls =>
              match classPath? cls with
              | some p => acc.push (p, (attr? attrs "style").getD Json.null)
              | none => acc
          | none => acc
        children.foldl go acc
    | _ => acc

/-- React wants `className`; the DOM attribute the gallery serializes and
the geometry audit reads is `class`, so the emitter keeps that and the
panel adds the React spelling to its own copy of the tree. -/
partial def reactify : Html → Html
  | .element tag attrs children =>
      let attrs :=
        match attr? attrs "class" with
        | some v => attrs.push ("className", v)
        | none => attrs
      .element tag attrs (children.map reactify)
  | h => h

/-- The LAST `cc-diagram` container of a tree. -/
partial def lastDiagram? : Html → Option Html
  | h@(.element _ attrs children) =>
      if isDiagramBox attrs then some h
      else children.foldr
        (fun c acc => if acc.isSome then acc else lastDiagram? c) none
  | _ => none

/-- The addressable boxes of the tree's LAST `cc-diagram` — the very
container `decorate` injects into, so a hit and its box can never come
from different diagrams.  The figure pair renders two, and only the right
one is clickable. -/
def addressedLast (h : Html) : Array (String × Json) :=
  addressed ((lastDiagram? h).getD h)

/-- Add a class to both spellings — `class` (what the DOM and the geometry
audit read) and `className` (what React reads). -/
def addClass (attrs : Array (String × Json)) (cls : String) :
    Array (String × Json) :=
  attrs.map fun a =>
    if a.1 == "class" ∨ a.1 == "className" then
      (a.1, Json.str ((a.2.getStr?.toOption.getD "") ++ " " ++ cls))
    else a

/-- Append the chrome layer to the LAST `cc-diagram` container of a tree,
optionally dimming it as preserved context (§12 item 20c).  The container
is the `position: relative` element the emitter owns, so the layer shares
the boxes' coordinate system exactly and no coordinate is ever recomputed.
"Last" is what makes one function serve both commands: `#cc_panel` renders
a single diagram, while `#cc_close` renders the §12-item-6 figure PAIR and
the clickable half is the RIGHT one — the endpoint an ε-step acts on. -/
partial def decorate (extra : Array Html) (dim : Bool) : Html → Html × Bool
  | .element tag attrs children =>
      if isDiagramBox attrs then
        (.element tag (if dim then addClass attrs "cc-dim" else attrs)
          (children ++ extra), true)
      else
        let (kids, done) := children.foldr
          (fun c (acc, done) =>
            if done then (#[c] ++ acc, true)
            else
              let (c', d) := decorate extra dim c
              (#[c'] ++ acc, d))
          (#[], false)
        (.element tag attrs kids, done)
  | h => (h, false)

/-- `decorate`, discarding the "found it" flag. -/
def decorateLast (extra : Array Html) (dim : Bool) (h : Html) : Html :=
  (decorate extra dim h).1

end Panel

/-! ### The props and the RPC component

The panel is a `mk_rpc_widget%` component: props go to the Lean server,
which assembles the final tree.  It has to be, because `MakeEditLink`
needs the *document* (uri and version) and a command elaborator has no
`DocumentMeta` — `RequestM.readDoc` does.  Everything else (the diagram,
the moves, the kernel-checked proof, the rail) is computed in the
elaborator and travels as data. -/

/-- A clickable node of the diagram: where it is, what selecting it writes
into the command, and whether it is currently selected. -/
structure PanelHit where
  /-- The node's encoded path, echoed onto the div as `data-path` so the
  live DOM is inspectable and matches the audited static page exactly. -/
  path : String
  /-- The box's own `style` object, straight from the emitter. -/
  style : Json
  /-- The full new source of the command this click writes. -/
  source : String
  /-- The `title` attribute: the node and its available moves. -/
  title : String
  selected : Bool
  deriving RpcEncodable

/-- One row of the move menu: the move, its law, and the command source
choosing it writes. -/
structure PanelRow where
  label : String
  law : String
  source : String
  deriving RpcEncodable

/-- The anchored move menu (§12 items 12 and 20). -/
structure PanelMenu where
  /-- The selected box's `style`, which the menu anchors under. -/
  anchor : Json
  head : String
  rows : Array PanelRow
  /-- Dismissal: the drawn small cross. -/
  dismiss : String
  deriving RpcEncodable

/-- The pseudocode lens over the selected node (§12 items 20 and 21).

A `mk_rpc_widget%` component holds no React state and passes no closures,
so a lens that opens on a click cannot be a state machine — but it does
not have to be one either: `details`/`summary` is a native, keyboard-
operable, DOM-resident toggle, and one `summary` element is BOTH the
item-21 identity tab and item 26(b)'s "drawn cross plus re-click to
close".  The alternative — a hidden checkbox with a sibling selector —
needs a document-unique `id` per lens (several panels share one infoview,
so the ids would collide) and gives the toggle no accessible role.  So:
`details`.

The lens is CHROME.  It is anchored over its object by the box's own
`style` (item 20b), it is absolutely positioned so opening it reflows
nothing (item 20a), it dims rather than hides the diagram beneath (20c),
and it takes the SHAPE of the box it inspects (item 21: resource sharp,
converter rounded), which the emitter already tells us through the
anchor's `borderRadius`. -/
structure PanelLens where
  /-- The inspected box's own `style` — the lens anchors on it and reads
  its `borderRadius` for item 21's shape rule. -/
  anchor : Json
  /-- The item-21 keyword: `Resource`, `Converter`, `Simulator`, … -/
  kind : String
  /-- The item-21 name, at the resource label budget. -/
  name : String
  /-- The body, one line per entry (`white-space: pre`). -/
  lines : Array String
  deriving RpcEncodable

/-- A line of the rail: either a term (or fact) line, or a relation line
carrying its law. -/
structure PanelLine where
  kind : String
  text : String
  law : String
  deriving RpcEncodable

/-- A bordered text button (§12 item 12). -/
structure PanelButton where
  label : String
  source : String
  title : String
  deriving RpcEncodable

/-- Everything the panel draws. -/
structure PanelProps where
  /-- The command's own source range: every click replaces exactly this. -/
  range : Lsp.Range
  diagram : Html
  hits : Array PanelHit
  menu? : Option PanelMenu
  lens? : Option PanelLens
  railCaption : String
  lines : Array PanelLine
  accumulator : String
  buttons : Array PanelButton
  deriving RpcEncodable

namespace Panel

/-- An edit link over arbitrary content: the click applies the LSP edit
that replaces the command with `source`. -/
def link (doc : Server.DocumentMeta) (range : Lsp.Range) (source title : String)
    (body : Array Html) : Html :=
  Html.ofComponent MakeEditLink
    { (MakeEditLinkProps.ofReplaceRange doc range source) with
      title? := some title } body

/-- The style of a hit: the box's rectangle and role colour, verbatim. -/
def hitStyle (style : Json) : Json :=
  let get := fun k => (styleField? style k).getD "0px"
  Json.mkObj
    [("position", "absolute"), ("left", get "left"), ("top", get "top"),
     ("width", get "width"), ("height", get "height"),
     ("borderRadius", get "borderRadius"),
     ("color", (styleField? style "color").getD "#555555"),
     ("cursor", "pointer")]

/-- The menu is anchored under its object: same left edge, one hair below
the box's bottom (§12 item 20b — position carries the relation). -/
def menuStyle (anchor : Json) : Json :=
  let left := (styleField? anchor "left").getD "0px"
  let top := (styleField? anchor "top").getD "0px"
  let height := (styleField? anchor "height").getD "0px"
  Json.mkObj
    [("left", left), ("top", s!"calc({top} + {height} + 6px)")]

/-- The lens sits at the TOP-LEFT of its object, its tab straddling the
box's top border (§12 item 21's grey tab, item 20b's anchoring).  Like
`menuStyle` this is the emitter's own `left`/`top` and a CSS `calc` — the
panel never recomputes a coordinate. -/
def lensStyle (anchor : Json) : Json :=
  let left := (styleField? anchor "left").getD "0px"
  let top := (styleField? anchor "top").getD "0px"
  Json.mkObj [("left", left), ("top", s!"calc({top} - 8px)")]

/-- Item 21's shape rule, read off the emitter: a box drawn with a corner
radius is a converter or simulator and takes a ROUNDED panel; a sharp box
is a resource and takes a SHARP one. -/
def lensRounded (anchor : Json) : Bool :=
  match styleField? anchor "borderRadius" with
  | some r => r != "0px" && r != "0"
  | none => false

/-- The room the hanging chrome reserves in the scroll container, from the
only two numbers that decide it — how many rows the menu has and how many
lines the lens body has.  These are COUNTS, not coordinates: the panel
still never computes a pixel the emitter owns, and the browser gate checks
the reserve is sufficient rather than trusting the arithmetic (a menu whose
foot falls past the stage is `menu-below-the-fold`).

A static reserve was the first version and measured 116px of dead space
under a two-row menu in a 375px infoview — which is the very complaint
this work answers, so it is not left as taste. -/
def reserveStyle (menuRows lensLines : Nat) : Json :=
  Json.mkObj
    [("--cc-menu-reserve", s!"{34 + 20 * menuRows}px"),
     ("--cc-lens-maxh", s!"{min 220 (26 + 15 * lensLines)}px")]

/-- A `div` carrying both class spellings (`class` for the DOM and the
audits, `className` for React). -/
def div (cls : String) (children : Array Html) : Html :=
  Html.element "div" #[("class", cls), ("className", cls)] children

/-- A classed `span` of plain text — the menu's and the rail's cells. -/
def spanText (cls : String) (text : String) : Html :=
  Html.element "span" #[("class", cls), ("className", cls)] #[Html.text text]

/-- The lens as a `details`: the `summary` is item 21's tab (kind keyword,
name, and item 20e's drawn cross), the body is the swapped
representation.  `startOpen` is for the STATIC gate only — the live panel
always ships it closed, because a widget cannot be handed a `Bool` from
the DOM and the reader's peek is not proof state (§12 item 26). -/
def lensHtml (startOpen : Bool) (lens : PanelLens) : Html :=
  let cls := if lensRounded lens.anchor then "cc-lens" else "cc-lens cc-lens-sharp"
  let attrs : Array (String × Json) :=
    #[("class", cls), ("className", cls), ("style", lensStyle lens.anchor),
      ("data-kind", lens.kind)]
  Html.element "details" (if startOpen then attrs.push ("open", "") else attrs)
    #[Html.element "summary" #[("class", "cc-lens-tab"), ("className", "cc-lens-tab"),
        ("title", s!"{lens.kind} {lens.name} — the same object as pseudocode")]
        #[Html.text s!"{lens.kind} {lens.name}", spanText "cc-lens-x" "×"],
      div "cc-lens-body" (lens.lines.map fun l => div "cc-lens-line" #[Html.text l])]

end Panel

open Panel in
/-- The panel's server half: it needs the document to build edit links,
which is exactly what an RPC method has and a command elaborator does
not. -/
@[server_rpc_method]
def CCPanel.rpc (ps : PanelProps) : RequestM (RequestTask Html) :=
  RequestM.asTask do
    let doc := (← RequestM.readDoc).meta
    let hitHtml : Array Html := ps.hits.map fun hit =>
      Html.element "div"
        #[("class", if hit.selected then "cc-hit cc-sel" else "cc-hit"),
          ("className", if hit.selected then "cc-hit cc-sel" else "cc-hit"),
          ("data-path", hit.path), ("style", hitStyle hit.style)]
        #[link doc ps.range hit.source hit.title #[]]
    let menuHtml : Array Html :=
      match ps.menu? with
      | none => #[]
      | some menu =>
          let rows : Array Html :=
            if menu.rows.isEmpty then
              #[div "cc-ui-none" #[Html.text "no move applies here"]]
            else menu.rows.map fun row =>
              link doc ps.range row.source row.law
                #[div "cc-ui-row"
                    #[spanText "cc-ui-move" row.label,
                      spanText "cc-ui-law" row.law]]
          #[Html.element "div"
              #[("class", "cc-ui-menu"), ("className", "cc-ui-menu"),
                ("style", menuStyle menu.anchor)]
              (#[div "cc-ui-head"
                  #[spanText "cc-ui-node" menu.head,
                    link doc ps.range menu.dismiss "close" #[Html.text "×"]]] ++
                rows)]
    -- the lens ships CLOSED: `details` holds its own state in the DOM, and a
    -- widget cannot be handed a `Bool` back from it (§12 item 26)
    let lensLayer : Array Html :=
      match ps.lens? with
      | none => #[]
      | some lens => #[Panel.lensHtml false lens]
    let stage :=
      div "cc-stage"
        #[decorateLast (hitHtml ++ menuHtml ++ lensLayer) ps.menu?.isSome
            (reactify ps.diagram)]
    let railLines : Array Html := ps.lines.map fun line =>
      if line.kind == "term" then
        div "cc-rail-term" #[Html.text line.text]
      else
        div "cc-rail-rel"
          #[spanText "cc-rail-rel-sym" line.text,
            spanText "cc-rail-law" line.law]
    let buttons : Array Html := ps.buttons.map fun b =>
      link doc ps.range b.source b.title
        #[spanText "cc-ui-btn" b.label]
    let rail :=
      div "cc-rail"
        (#[div "cc-rail-cap" #[Html.text ps.railCaption]] ++ railLines ++
          (if ps.accumulator == "" then #[] else
            #[div "cc-rail-acc" #[Html.text ps.accumulator]]) ++
          (if buttons.isEmpty then #[] else #[div "cc-rail-btns" buttons]))
    return Html.element "div"
      #[("class", "cc-panel"), ("className", "cc-panel"),
        ("style", reserveStyle
          ((ps.menu?.map (·.rows.size)).getD 0)
          ((ps.lens?.map (·.lines.size)).getD 0))]
      #[Html.element "style" #[] #[Html.text css], stage, rail]

/-- The D4/D5 panel component. -/
@[widget_module]
def CCPanel : Component PanelProps := mk_rpc_widget% CCPanel.rpc

/-! ## The grammar

`inner`, `left`, `right` (and D5's `attach`, `smul`, `par`, `par_left`,
`trans`, `move`) are matched as NON-reserved words; `with` and `at`
introduce the two clauses and are already core tokens. -/

/-- One step of a node address. -/
declare_syntax_cat ccDir (behavior := both)

syntax (name := ccDirInner) &"inner" : ccDir
syntax (name := ccDirLeft) &"left" : ccDir
syntax (name := ccDirRight) &"right" : ccDir

/-- A move, addressed by a path (or, still, by D3's spine depth). -/
declare_syntax_cat ccPathMove (behavior := both)

syntax (name := ccPLift) &"lift" (num)? (" at " "[" ccDir,* "]")? : ccPathMove
syntax (name := ccPMerge) &"merge" (num)? (" at " "[" ccDir,* "]")? : ccPathMove
syntax (name := ccPDropId) &"drop_id" (num)? (" at " "[" ccDir,* "]")? : ccPathMove
syntax (name := ccPCommute) &"commute" (num)? (" at " "[" ccDir,* "]")? : ccPathMove
syntax (name := ccPDropIdle) &"drop_idle" (num)? (" at " "[" ccDir,* "]")? :
  ccPathMove

/-- Parse one path step. -/
def Move.parseDir (stx : Syntax) : CommandElabM Move.Dir := do
  if stx.isOfKind ``ccDirInner then return .inner
  else if stx.isOfKind ``ccDirLeft then return .inl
  else if stx.isOfKind ``ccDirRight then return .inr
  else throwError "unknown path step{indentD stx}"

/-- Parse a `at [dir, …]` clause (absent = the root). -/
def Move.parsePath (stx : Syntax) : CommandElabM Move.Path := do
  if stx.isNone then return []
  -- the optional group is flattened: `⟨"at", "[", dirs, "]"⟩`
  (stx[2].getSepArgs.toList).mapM Move.parseDir

/-- Parse one path-addressed move.  Both addressings are accepted: D3's
numeral (`commute 1`) and the path (`commute at [inner]`).  They agree —
`Path.ofDepth` is `replicate … inner` — and the receipts pin that. -/
def Move.parsePathMove (stx : Syntax) : CommandElabM Move.PathRequest := do
  let kind : Move.Kind ←
    if stx.isOfKind ``ccPLift then pure .lift
    else if stx.isOfKind ``ccPMerge then pure .merge
    else if stx.isOfKind ``ccPDropId then pure .dropId
    else if stx.isOfKind ``ccPCommute then pure .commute
    else if stx.isOfKind ``ccPDropIdle then pure .dropIdle
    else throwError "unknown move{indentD stx}"
  let depthPath :=
    if stx[1].isNone then [] else Move.Path.ofDepth stx[1][0].toNat
  let atPath ← Move.parsePath stx[2]
  return { kind, path := depthPath ++ atPath }

/-! ## `#cc_panel` -/

/-- The rail's lines for a `=`-chain: term lines alternating with
`≡ lemma` lines (§12 item 12). -/
def Move.railLines (head : String) (steps : List Move.Step) :
    MetaM (Array PanelLine) := do
  let mut out : Array PanelLine := #[{ kind := "term", text := head, law := "" }]
  for step in steps do
    out := out.push { kind := "rel", text := "≡", law := Move.lawText step.lemmas }
    out := out.push { kind := "term", text := ← Move.ppLine step.after, law := "" }
  return out

/-- The node table of a rendered diagram: for every addressable box, the
path and the moves the TERM licenses there.  This is the panel's pinnable
receipt — the ASCII twin's role (§12 item 7) for the interaction layer. -/
def Move.nodeTable (e : Expr) (paths : Array String) : MetaM String := do
  let sorted := paths.qsort fun a b =>
    if a.length == b.length then a < b else a.length < b.length
  let mut lines : Array String := #[]
  for enc in sorted do
    let some path := Move.Path.decode? enc | continue
    let addr := if path.isEmpty then "·" else Move.Path.words path
    match ← Move.menuAtPath e path with
    | none => lines := lines.push s!"[{addr}]  ⟶  (undecodable)"
    | some [] => lines := lines.push s!"[{addr}]  ⟶  —"
    | some menu =>
        lines := lines.push s!"[{addr}]  ⟶  {String.intercalate ", "
          (menu.map fun (k, _) => k.word)}"
  return String.intercalate "\n" lines.toList

/-- The lens over one node: the SAME object in the other representation
this library actually has — its structure twin (§12 item 7) and its term.
§12 item 19 is satisfied by construction: the description is joined to
its object by POSITION, never by a wire.

The kind keyword and the panel shape come from the node itself: a role the
declaration carries wins, and otherwise the emitter's own box radius
decides — a rounded box is a converter pill, a sharp one a resource
(§12 items 13 and 21).  What this is NOT is the `resource … where` source
text: nothing stores it (`Jost/SurfaceGrammar.lean` compiles the block
away), so a true pseudocode lens needs a `cc_pseudocode` store first.

Total, like `Move.menuAtPath` and for the same reason: a stamped box whose
path the matcher cannot decode is DRAWN, and must offer no lens rather
than take the command down with it. -/
def Panel.lensAt (e : Expr) (path : Move.Path) (anchor : Json) :
    MetaM (Option PanelLens) := do
  let some (sub, _) ← (try (some <$> Move.descendPath e path) catch _ => pure none)
    | return none
  let (_, role, _) ← Diagram.labelOf sub
  let shape ← Diagram.shapeWithDirs sub []
  let kind : String :=
    match role with
    | some .simulator => "Simulator"
    | some .converter => "Converter"
    | some .constructed => "Specification"
    | some .game => "Game"
    | _ => if Panel.lensRounded anchor then "Converter" else "Resource"
  -- the tab names the BOX, not the subtree under it: a tab wide enough to
  -- restate the whole term is an annotation, not an identity (measured at
  -- 297px over a 76px pill before this)
  let raw : String :=
    match shape with
    | .attach conv ifc .. => s!"{conv} @ {Diagram.lastComponent ifc}"
    | .leaf label _ _ _ => label
    | .foldBox label _ _ => label
    | .region label _ _ => label
    | s => Diagram.summary s
  let name := Diagram.middleEllipsis (2 * Diagram.resourceBudget) raw
  let lines := (Diagram.ascii shape).splitOn "\n" ++ ["", ← Move.ppLine sub]
  return some { anchor, kind, name, lines := lines.toArray }

/-- `#cc_panel t with [move, …] at [dir, …]`: the D4 interactive panel.
The diagram is drawn from the term the moves reach; every box is a
clickable node; the selected node's menu lists exactly the moves D3's
matcher offers there, each with its law name; choosing one rewrites the
command and the panel comes back with the term rewritten and one more step
on the rail.  The composite proof is kernel-checked (`Move.kernelCheck`)
on every re-elaboration, so a panel that draws is a kernel receipt.

No view clause: a fold collapses several term nodes into one box and would
make every later address name the wrong subterm.  Use `#cc_diagram … with
[fold …]` for views and `#cc_panel` for moves. -/
syntax (name := ccPanelCmd) "#cc_panel " term
  (" with " "[" ccPathMove,* "]")? (" at " "[" ccDir,* "]")? : command

@[command_elab ccPanelCmd] def elabCcPanel : CommandElab := fun stx => do
  let t : TSyntax `term := ⟨stx[1]⟩
  let reqs ←
    if stx[2].isNone then pure []
    else stx[2][2].getSepArgs.toList.mapM Move.parsePathMove
  let selection ← Move.parsePath stx[3]
  let selected := if stx[3].isNone then none else some selection
  let raw := ((t.raw.reprint.getD "?").replace "\n" " ").trimAscii.toString
  let head := String.intercalate " " ((raw.splitOn " ").filter (· != ""))
  -- the command's own source range: every click replaces exactly this
  let fileMap ← getFileMap
  let some srcRange := stx.getRange?
    | throwError "#cc_panel: the command has no source range"
  let range : Lsp.Range :=
    ⟨fileMap.utf8PosToLspPos srcRange.start, fileMap.utf8PosToLspPos srcRange.stop⟩
  let indent := String.ofList (List.replicate range.start.character ' ')
  -- the command source, rebuilt from parts
  let render := fun (rs : List Move.PathRequest) (sel : Option Move.Path) =>
    let withPart :=
      if rs.isEmpty then ""
      else s!" with [{String.intercalate ", " (rs.map Move.PathRequest.text)}]"
    let atPart :=
      match sel with
      | none => ""
      | some p => s!" at [{Move.Path.words p}]"
    s!"#cc_panel {head}{withPart}{atPart}"
  let (log, props) ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let steps ← Move.runPath e reqs
    let (last, proof) ← Move.compose e steps
    Move.kernelCheck proof (← mkEq e last)
    let shape ← Diagram.shapeWithDirs last []
    let diagram := Diagram.html shape
    let boxes := Panel.addressedLast diagram
    -- hits: one per addressable box whose path the TERM also resolves
    let mut hits : Array PanelHit := #[]
    for (enc, style) in boxes do
      let some path := Move.Path.decode? enc | continue
      let some menu ← Move.menuAtPath last path | continue
      let isSel := selected == some path
      let source :=
        if isSel then render reqs none else render reqs (some path)
      let moves :=
        if menu.isEmpty then "no move applies"
        else String.intercalate ", " (menu.map fun (k, _) => k.word)
      hits := hits.push
        { path := enc, style, source, selected := isSel,
          title := s!"[{if path.isEmpty then "·" else Move.Path.words path}] — {moves}" }
    -- the anchored menu of the selected node
    let menu? ← match selected with
      | none => pure none
      | some path => do
          match (boxes.find? fun b => b.1 == Move.Path.encode path) with
          | none => pure none
          | some (_, style) =>
              let rows ← match ← Move.menuAtPath last path with
                | none => pure #[]
                | some menu => pure <| (menu.map fun (k, laws) =>
                    { label := k.word, law := Move.lawText laws,
                      source := render (reqs ++ [{ kind := k, path }]) none
                      : PanelRow }).toArray
              pure (some
                { anchor := style, rows, dismiss := render reqs none,
                  head := if path.isEmpty then "root" else Move.Path.words path })
    -- the lens rides with the selection: one object inspected at a time,
    -- anchored over exactly the box the menu hangs off
    let lens? ← match menu? with
      | none => pure none
      | some menu => Panel.lensAt last selection menu.anchor
    let lines ← Move.railLines head steps
    let chain ← Move.calcChain head steps
    let lastText ← Move.ppLine last
    let buttons : Array PanelButton :=
      (if steps.isEmpty then #[] else
        #[{ label := "write calc below",
            title := "insert the kernel-checked chain into the file \
(a Lean-authored widget cannot reach the clipboard)",
            source := render reqs selected ++ "\n" ++ indent ++
              "example : " ++ head ++ " = " ++ lastText ++ " :=\n" ++
              indent ++ "  " ++ chain.replace "\n" ("\n" ++ indent ++ "  ") },
          { label := "undo",
            title := "drop the last move",
            source := render (reqs.dropLast) none }])
    let props : PanelProps :=
      { range, diagram, hits, menu?, lens?, lines,
        railCaption := if steps.isEmpty then "calc — no moves yet" else "calc",
        accumulator := "", buttons }
    let table ← Move.nodeTable last (boxes.map (·.1))
    let trace :=
      if steps.isEmpty then ""
      else "\n" ++ String.intercalate "\n" (List.zipWith
        (fun (req : Move.PathRequest) (step : Move.Step) =>
          s!"{req.text}  ⟨{Move.lawText step.lemmas}⟩")
        reqs steps) ++ s!"\n↦ {lastText}"
    -- the menu, and what CLICKING each row writes into the file: the live
    -- loop's own receipt, so the interaction is pinned and not just claimed
    let menuLog := match menu? with
      | none => ""
      | some menu =>
          s!"\n— menu ({menu.head}) —\n" ++
          (if menu.rows.isEmpty then "no move applies here"
           else String.intercalate "\n" (menu.rows.toList.map fun (row : PanelRow) =>
             s!"{row.label}  ⟨{row.law}⟩  ↦  {row.source}"))
    let calcLog := if steps.isEmpty then "" else s!"\n— calc —\n{chain}"
    let logText :=
      s!"{Diagram.ascii shape}{trace}\n— nodes —\n{table}{menuLog}{calcLog}"
    return (logText, props)
  logInfo log
  liftCoreM <| Widget.savePanelWidgetInfo (hash CCPanel.javascript)
    (rpcEncode props) stx

/-! ## `#cc_close` — the ε-rail (D5) -/

/-- A step of the ε-rail. -/
declare_syntax_cat ccCloseStep (behavior := both)

syntax (name := ccCAttach) &"attach" term:max " at " term:max : ccCloseStep
syntax (name := ccCSmul) &"smul" term:max : ccCloseStep
syntax (name := ccCPar) &"par" term:max : ccCloseStep
syntax (name := ccCParLeft) &"par_left" term:max : ccCloseStep
syntax (name := ccCTrans) &"trans" term:max : ccCloseStep
syntax (name := ccCMove) &"move" ccPathMove : ccCloseStep

/-- Parse one ε-step. -/
def Close.parseStep (stx : Syntax) : CommandElabM Close.CStep := do
  if stx.isOfKind ``ccCAttach then return .attach stx[1] stx[3]
  else if stx.isOfKind ``ccCSmul then return .smul stx[1]
  else if stx.isOfKind ``ccCPar then return .par stx[1]
  else if stx.isOfKind ``ccCParLeft then return .parLeft stx[1]
  else if stx.isOfKind ``ccCTrans then return .trans stx[1]
  else if stx.isOfKind ``ccCMove then return .move (← Move.parsePathMove stx[1])
  else throwError "unknown ε-step{indentD stx}"

/-- The `have`-chain of an ε-rail, ready to paste.  `≈[ε]` has no `Trans`
instance — `close_trans` carries `0 ≤ ε` side conditions, so it cannot be
one — hence a `have`-chain rather than a `calc`. -/
def Close.haveChain (head : String) (rungs : List Close.Rung) :
    MetaM String := do
  if rungs.isEmpty then return "-- no ε-steps"
  let mut out := ""
  let mut prev := head
  let mut k := 1
  for rung in rungs do
    let lhs ← Move.ppLine rung.fact.lhs
    let eps ← Move.ppLine rung.fact.eps
    let rhs ← Move.ppLine rung.fact.rhs
    out := out ++ s!"have step{k} : {lhs} ≈[{eps}] {rhs} :=\n  \
{rung.just.replace "%p" prev}\n"
    prev := s!"step{k}"
    k := k + 1
  return out ++ prev

/-- `#cc_close h with [step, …] at [dir, …]`: the D5 ε-rail.  `h` is a
proven `L ≈[ε] R`; every step is one carrier lemma applied to the fact in
flight; the rail alternates fact lines with `≈[ε] lemma` lines and its
last line is the RUNNING BOUND, which is the theorem.  The composite is
kernel-checked exactly as D4's is.

The diagram is the figure pair of the current fact (§12 item 6) and its
RIGHT side is clickable: choosing a move there appends
`move m at [path]`, a D4 `=`-step embedded in the ε-chain at zero cost by
`close_zero_iff`. -/
syntax (name := ccCloseCmd) "#cc_close " term
  (" with " "[" ccCloseStep,* "]")? (" at " "[" ccDir,* "]")? : command

@[command_elab ccCloseCmd] def elabCcClose : CommandElab := fun stx => do
  let t : TSyntax `term := ⟨stx[1]⟩
  let steps ←
    if stx[2].isNone then pure []
    else stx[2][2].getSepArgs.toList.mapM Close.parseStep
  let selection ← Move.parsePath stx[3]
  let selected := if stx[3].isNone then none else some selection
  let raw := ((t.raw.reprint.getD "?").replace "\n" " ").trimAscii.toString
  let head := String.intercalate " " ((raw.splitOn " ").filter (· != ""))
  let fileMap ← getFileMap
  let some srcRange := stx.getRange?
    | throwError "#cc_close: the command has no source range"
  let range : Lsp.Range :=
    ⟨fileMap.utf8PosToLspPos srcRange.start, fileMap.utf8PosToLspPos srcRange.stop⟩
  let indent := String.ofList (List.replicate range.start.character ' ')
  let render := fun (ss : List Close.CStep) (sel : Option Move.Path) =>
    let withPart :=
      if ss.isEmpty then ""
      else s!" with [{String.intercalate ", " (ss.map Close.CStep.text)}]"
    let atPart :=
      match sel with
      | none => ""
      | some p => s!" at [{Move.Path.words p}]"
    s!"#cc_close {head}{withPart}{atPart}"
  let (log, props) ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let start ← Close.Fact.ofProof (← instantiateMVars e)
    let rungs ← Close.run start steps
    let final := (rungs.getLast?.map (·.fact)).getD start
    Move.kernelCheck final.proof
      (← mkAppM ``RandomSystems.CC.ResourceSystem.close
        #[final.eps, final.lhs, final.rhs])
    let lShape ← Diagram.shapeWithDirs final.lhs []
    let rShape ← Diagram.shapeWithDirs final.rhs []
    let rHtml := Diagram.html rShape
    let boxes := Panel.addressedLast rHtml
    let mut hits : Array PanelHit := #[]
    for (enc, style) in boxes do
      let some path := Move.Path.decode? enc | continue
      let some menu ← Move.menuAtPath final.rhs path | continue
      let isSel := selected == some path
      let source := if isSel then render steps none else render steps (some path)
      let moves :=
        if menu.isEmpty then "no move applies"
        else String.intercalate ", " (menu.map fun (k, _) => k.word)
      hits := hits.push
        { path := enc, style, source, selected := isSel,
          title := s!"[{if path.isEmpty then "·" else Move.Path.words path}] — {moves}" }
    let menu? ← match selected with
      | none => pure none
      | some path => do
          match (boxes.find? fun b => b.1 == Move.Path.encode path) with
          | none => pure none
          | some (_, style) =>
              let rows ← match ← Move.menuAtPath final.rhs path with
                | none => pure #[]
                | some menu => pure <| (menu.map fun (k, laws) =>
                    { label := k.word, law := Move.lawText laws,
                      source := render (steps ++ [.move { kind := k, path }]) none
                      : PanelRow }).toArray
              pure (some
                { anchor := style, rows, dismiss := render steps none,
                  head := if path.isEmpty then "root" else Move.Path.words path })
    let lens? ← match menu? with
      | none => pure none
      | some menu => Panel.lensAt final.rhs selection menu.anchor
    -- the rail: fact lines with `≈[ε] lemma` lines between them
    let mut lines : Array PanelLine :=
      #[{ kind := "term", text := ← Move.ppLine start.lhs, law := "" },
        { kind := "rel", text := s!"≈[{← Move.ppLine start.eps}]",
          law := head },
        { kind := "term", text := ← Move.ppLine start.rhs, law := "" }]
    for rung in rungs do
      lines := lines.push
        { kind := "rel", text := "⇓", law := Move.lawText rung.lemmas }
      lines := lines.push
        { kind := "term", text := ← Move.ppLine rung.fact.lhs, law := "" }
      lines := lines.push
        { kind := "rel", text := s!"≈[{← Move.ppLine rung.fact.eps}]",
          law := rung.text }
      lines := lines.push
        { kind := "term", text := ← Move.ppLine rung.fact.rhs, law := "" }
    let chain ← Close.haveChain head rungs
    let epsText ← Move.ppLine final.eps
    let lhsText ← Move.ppLine final.lhs
    let rhsText ← Move.ppLine final.rhs
    let accumulator := s!"ε ≤ {epsText}"
    let buttons : Array PanelButton :=
      (if rungs.isEmpty then #[] else
        #[{ label := "write have-chain below",
            title := "insert the kernel-checked ε-chain into the file",
            source := render steps selected ++ "\n" ++ indent ++
              "example : " ++ lhsText ++ " ≈[" ++ epsText ++ "] " ++ rhsText ++
              " :=\n" ++ indent ++ "  " ++
              chain.replace "\n" ("\n" ++ indent ++ "  ") },
          { label := "undo",
            title := "drop the last ε-step",
            source := render (steps.dropLast) none }])
    let props : PanelProps :=
      { range, diagram := Diagram.pairHtml (Diagram.html lShape)
          s!"≈[{epsText}]" rHtml,
        hits, menu?, lens?, lines, railCaption := "ε-rail", accumulator,
        buttons }
    let table ← Move.nodeTable final.rhs (boxes.map (·.1))
    let trace := String.intercalate "\n" (rungs.map fun rung =>
      s!"{rung.text}  ⟨{Move.lawText rung.lemmas}⟩")
    let menuLog := match menu? with
      | none => ""
      | some menu =>
          s!"\n— menu ({menu.head}) —\n" ++
          (if menu.rows.isEmpty then "no move applies here"
           else String.intercalate "\n" (menu.rows.toList.map fun (row : PanelRow) =>
             s!"{row.label}  ⟨{row.law}⟩  ↦  {row.source}"))
    let haveLog := if rungs.isEmpty then "" else s!"\n— have —\n{chain}"
    let log :=
      s!"{Diagram.ascii lShape}\n≈[{epsText}]\n{Diagram.ascii rShape}" ++
      (if trace == "" then "" else s!"\n{trace}") ++
      s!"\nε ≤ {epsText}\n— nodes (right) —\n{table}{menuLog}{haveLog}"
    return (log, props)
  logInfo log
  liftCoreM <| Widget.savePanelWidgetInfo (hash CCPanel.javascript)
    (rpcEncode props) stx



/-! ## Receipts -/

namespace PanelTests

open CarrierDemo AlgebraDemo
open scoped Converter ResourceSystem

/-! ### The path is the address, and it agrees with D3's depth

`Path.encode` and `Path.decode?` are the two halves of the wire format the
renderer stamps; the round trip is the contract between two modules that
cannot import each other. -/

/-- info: R / Ri / Ril / Riir
[] / [inner] / [inner, left] / [inner, inner, right]
round trip: true -/
#guard_msgs in
#eval do
  let ps : List Move.Path :=
    [[], [.inner], [.inner, .inl], [.inner, .inner, .inr]]
  IO.println (String.intercalate " / " (ps.map Move.Path.encode))
  IO.println (String.intercalate " / " (ps.map fun p =>
    s!"[{Move.Path.words p}]"))
  IO.println s!"round trip: {ps.all fun p =>
    Move.Path.decode? (Move.Path.encode p) == some p}"

-- D3's `Nat` depth IS the all-`inner` path; that is what keeps its pins
-- green while the panel addresses `∥` children D3 could not name.
/-- info: depth 0/1/3 ⟶ [] / [inner] / [inner, inner, inner] -/
#guard_msgs in
#eval IO.println s!"depth 0/1/3 ⟶ [{Move.Path.words (Move.Path.ofDepth 0)}] / \
[{Move.Path.words (Move.Path.ofDepth 1)}] / \
[{Move.Path.words (Move.Path.ofDepth 3)}]"

/-! ### The panel: nodes, menus, and the moves the TERM licenses

Every box the renderer stamps is listed with the moves D3's matcher offers
at that node — the panel's menu is exactly this table, never a label
read. -/

/-- info: ◠ mask @ Party.u
  ◠ mask @ Party.u
    □ toyR
— nodes —
[·]  ⟶  lift, merge, drop_idle
[inner]  ⟶  lift
[inner, inner]  ⟶  — -/
#guard_msgs in
#cc_panel (mask •[Party.u] (mask •[Party.u] toyR))

-- The payoff of paths: a `∥` node has TWO children, and each is now
-- addressable.  D3 could reach neither.  (The two spine nodes are Jost
-- CONNECTIONS, `α ••[γ] R`, so they license none of the *interface*-level
-- moves; what they do license at the root is the γ-level `commute`
-- (`Converter.attachAlong_comm`, `Jost/SurfaceGamma.lean`), because γ^B
-- leaves alone exactly the interface γ^A produced.  Each prints the
-- interfaces its connection REACHES in `⟨…⟩`: §12 item 28's fork, which the
-- picture draws and the structure receipt therefore owes a line.)
/-- info: ◠ decB @ gammaV ⟨Sum.inl Comp.key, Sum.inl Comp.aut⟩
  ◠ encA @ gammaU ⟨Sum.inl Party.u, Sum.inr Party.u⟩
    ∥
      □ toyR
      □ toyR
— nodes —
[·]  ⟶  commute
[inner]  ⟶  —
[inner, inner, left]  ⟶  —
[inner, inner, right]  ⟶  — -/
#guard_msgs in
#cc_panel CarrierDemo.constructedShape

/-! ### A move inside a `∥` — the address D3 could not write

`congrArg` now travels through `fun R => R ∥ Q` as well as through an
attachment frame, so a law applied in the left component of a stack still
speaks about the whole term. -/

/-- info: ∥
  ◠ mask.word Party.u * mask.word Party.u @ Party.u
    □ toyR
  □ toyR
merge at [left]  ⟨Converter.word_smul, Converters.comp_smul⟩
↦ (mask.word Party.u * mask.word Party.u) • toyR ∥ toyR
— nodes —
[left]  ⟶  —
[right]  ⟶  —
[left, inner]  ⟶  —
— calc —
calc ((mask •[Party.u] (mask •[Party.u] toyR)) ∥ toyR)
  _ = (mask.word Party.u * mask.word Party.u) • toyR ∥ toyR := congrArg (fun R => R ∥ toyR) ((Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm) -/
#guard_msgs in
#cc_panel ((mask •[Party.u] (mask •[Party.u] toyR)) ∥ toyR)
  with [merge at [left]]

/-- The panel-produced proof, pasted back from `write calc below`.  The
frame's binder carries a type ascription the emitter does not print: `∥` is
overloaded across the three carriers, so a bare `fun R => R ∥ toyR` is
ambiguous outside a position that already fixes `R`'s type. -/
theorem panel_par_left :
    (mask •[Party.u] (mask •[Party.u] toyR)) ∥ toyR =
      (mask.word Party.u * mask.word Party.u) • toyR ∥ toyR :=
  calc ((mask •[Party.u] (mask •[Party.u] toyR)) ∥ toyR)
    _ = (mask.word Party.u * mask.word Party.u) • toyR ∥ toyR :=
      congrArg (fun R : ResourceSystem demoServices Party => R ∥ toyR)
        ((Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm)

/-- info: 'RandomSystems.CC.PanelTests.panel_par_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms panel_par_left

-- The right component too, and a chain of two moves through two different
-- frames — the whole point of addressing by path.
/-- info: ∥
  □ toyR
  ◠ mask.word Party.u * mask.word Party.u @ Party.u
    □ toyR
merge at [right]  ⟨Converter.word_smul, Converters.comp_smul⟩
↦ toyR ∥ (mask.word Party.u * mask.word Party.u) • toyR
— nodes —
[left]  ⟶  —
[right]  ⟶  —
[right, inner]  ⟶  —
— calc —
calc (toyR ∥ (mask •[Party.u] (mask •[Party.u] toyR)))
  _ = toyR ∥ (mask.word Party.u * mask.word Party.u) • toyR := congrArg (fun R => toyR ∥ R) ((Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm) -/
#guard_msgs in
#cc_panel (toyR ∥ (mask •[Party.u] (mask •[Party.u] toyR)))
  with [merge at [right]]

/-! ### D3's addressing still works, unchanged

The same move, written D3's way (a spine depth) and the panel's way (a
path), produces the same term and the same citation. -/

/-- info: ◠ mask @ Party.u
  ◠ mask @ Party.u
    ◠ mask @ Party.v
      □ toyR
commute at [inner]  ⟨Converter.attachAt_comm⟩
↦ mask •[Party.u] mask •[Party.u] mask •[Party.v] toyR
— nodes —
[·]  ⟶  lift, merge, drop_idle
[inner]  ⟶  lift, commute
[inner, inner]  ⟶  lift
[inner, inner, inner]  ⟶  —
— calc —
calc (mask •[Party.u] (mask •[Party.v] (mask •[Party.u] toyR)))
  _ = mask •[Party.u] mask •[Party.u] mask •[Party.v] toyR := congrArg (fun R => mask •[Party.u] R) (Converter.attachAt_comm (by decide) mask mask toyR) -/
#guard_msgs in
#cc_panel (mask •[Party.u] (mask •[Party.v] (mask •[Party.u] toyR)))
  with [commute 1]

/-- info: ◠ mask @ Party.u
  ◠ mask @ Party.u
    ◠ mask @ Party.v
      □ toyR
commute at [inner]  ⟨Converter.attachAt_comm⟩
↦ mask •[Party.u] mask •[Party.u] mask •[Party.v] toyR
— nodes —
[·]  ⟶  lift, merge, drop_idle
[inner]  ⟶  lift, commute
[inner, inner]  ⟶  lift
[inner, inner, inner]  ⟶  —
— calc —
calc (mask •[Party.u] (mask •[Party.v] (mask •[Party.u] toyR)))
  _ = mask •[Party.u] mask •[Party.u] mask •[Party.v] toyR := congrArg (fun R => mask •[Party.u] R) (Converter.attachAt_comm (by decide) mask mask toyR) -/
#guard_msgs in
#cc_panel (mask •[Party.u] (mask •[Party.v] (mask •[Party.u] toyR)))
  with [commute at [inner]]

/-! ### The click loop, in full

Selecting a node writes `at […]` into the command; each menu row writes
its move into `with […]`.  Both are ordinary LSP edits applied by
`MakeEditLink`, so the `— menu —` block below IS the interaction: these
are the exact command sources the clicks produce, and re-elaborating any
of them is what redraws the diagram and grows the rail. -/

/-- info: ◠ mask @ Party.u
  ◠ mask @ Party.u
    □ toyR
— nodes —
[·]  ⟶  lift, merge, drop_idle
[inner]  ⟶  lift
[inner, inner]  ⟶  —
— menu (inner) —
lift  ⟨Converter.word_smul⟩  ↦  #cc_panel (mask •[Party.u] (mask •[Party.u] toyR)) with [lift at [inner]] -/
#guard_msgs in
#cc_panel (mask •[Party.u] (mask •[Party.u] toyR)) at [inner]

/-! ### The chrome takes its coordinates from the emitter, never its own

A hit target is the box: the emitter's own `left`/`top`/`width`/`height`
and `color`, copied verbatim off the rendered `style`, so a click lands on
what the user sees and the hover outline is the box's ROLE colour
(`currentColor`) at 2px offset — never a fill, and `outline` does not
participate in layout, so the audited geometry beneath is untouched.  The
menu anchors under its object by CSS `calc`, for the same reason: no
coordinate is ever recomputed in the panel. -/

/-- info: addresses: Ri, R
hit R: {"width": "76px",
 "top": "27px",
 "position": "absolute",
 "left": "50px",
 "height": "34px",
 "cursor": "pointer",
 "color": "#1e8449",
 "borderRadius": "17px"}
menu at R: {"top": "calc(27px + 34px + 6px)", "left": "50px"} -/
#guard_msgs in
#eval do
  let shape : Diagram.Shape :=
    .attach "mask" "Party.u" (.leaf "toyR" (some .assumed)) (some .converter)
  let boxes := Panel.addressed (Diagram.html shape)
  IO.println s!"addresses: {String.intercalate ", "
    (boxes.toList.map (fun (b : String × Json) => b.1))}"
  for (p, style) in boxes do
    if p == "R" then
      IO.println s!"hit {p}: {(Panel.hitStyle style).pretty}"
      IO.println s!"menu at {p}: {(Panel.menuStyle style).pretty}"

/-! ### The chrome gate, measured in a browser (§12 item 11's discipline)

The style pin above is the emitter's side of the contract.  This is the
BROWSER's side: the same page discipline as the gallery — the panel's own
`Html` tree, serialized by the gallery's own serializer, with a
dependency-free self-audit that measures the RENDERED result and writes
its JSON into `<pre id="chrome-audit">`.  An empty `violations` array is
the gate, read via headless Chrome exactly as the geometry audit is.

The chrome checks: every hit lies on ITS box to 0.51px on all four edges;
the click-through anchor fills the hit (a 0×0 anchor is a dead node, which
is how the CSS `>` combinator's silent death inside a `<style>` element
was caught); the menu is anchored at the selected box's left edge, 6px
under its bottom, opaque; and the context beneath is dimmed rather than
hidden (§12 item 20c).

The MEDIA checks (`sketches/visual-scenarios.md`), each the pixel form of
one rule, because "it fits" is a claim about pixels: the panel never
overflows the medium it was given (R3); the stage really is the scroll
container, so what does not fit is PANNED and never painted over
something else; no label renders below its floor and none is clipped by
its box (R1); tags do not collide once they sit at the floor; and the
lens draws nothing while closed, and while open is anchored on its
object, opaque, and dimming the diagram beneath (§12 items 20 and 21).

**The medium is a fixed-width container, not the window.**  An infoview is
a panel of a given width inside an editor, so the honest model of a
viewport here is a `div` of that width — and it has the practical virtue
that headless Chrome refuses to open a window narrower than 500px, so a
375px window cannot be measured but a 375px medium can.  Five media are
rendered on one page: the two panel shapes (`#cc_panel`'s single diagram
and `#cc_close`'s figure PAIR, whose clickable half is the RIGHT one) at a
narrow and a wide medium, and the lens open.

One honest difference from the live panel: the anchors here are plain
`<a href="#">` rather than `MakeEditLink` components, because a component
cannot be evaluated outside the infoview (the gallery serializer's
documented limit).  Everything the audit measures — `Panel.css`,
`hitStyle`, `menuStyle`, `lensStyle`, `lensHtml`, `decorateLast`,
`addressedLast` — is the code the panel runs. -/

/-- The chrome self-audit: dependency-free JS over the rendered page.  The
legibility floors are interpolated from `Panel.fontScale`, so the gate
reads the RULE's own numbers and cannot drift from them (the discipline
`Diagram.framePad` and `Diagram.forkPitch` already impose on the geometry
audit). -/
def Panel.chromeAudit : String := String.intercalate "\n" [
  "<pre id=\"chrome-audit\"></pre>",
  "<script>",
  "(function(){",
  " const tol = 0.51;",
  " const floors = {" ++ String.intercalate ", "
    (Panel.fontScale.map fun (kind, floor, _) => s!"{kind}: {floor}") ++ "};",
  " const hits2 = function(a, b){ return a.left < b.right - tol &&",
  "   b.left < a.right - tol && a.top < b.bottom - tol && b.top < a.bottom - tol; };",
  " const out = {cases: [], violations: []};",
  " document.querySelectorAll('.cc-panel').forEach(function(panel){",
  "  const name = panel.dataset.case;",
  "  const diags = Array.from(panel.querySelectorAll('.cc-diagram'));",
  "  const host = diags[diags.length-1];",
  "  const hits = Array.from(panel.querySelectorAll('.cc-hit'));",
  "  hits.forEach(function(h){",
  "   if (h.parentElement !== host)",
  "    out.violations.push({case:name, kind:'hit-not-in-host-diagram'});",
  "   const p = h.dataset.path;",
  "   const box = host.querySelector('.cc-box.cc-at-' + p);",
  "   if (!box) { out.violations.push({case:name, kind:'no-box', path:p}); return; }",
  "   const a = h.getBoundingClientRect(), b = box.getBoundingClientRect();",
  "   const d = [a.left-b.left, a.top-b.top, a.width-b.width, a.height-b.height];",
  "   if (d.some(function(x){ return Math.abs(x) > tol; }))",
  "    out.violations.push({case:name, kind:'hit-off-box', path:p, delta:d});",
  "   const link = h.querySelector('a');",
  "   const lr = link.getBoundingClientRect();",
  "   if (Math.abs(lr.width-a.width) > tol || Math.abs(lr.height-a.height) > tol)",
  "    out.violations.push({case:name, kind:'link-does-not-fill', path:p,",
  "      got:[lr.width, lr.height], want:[a.width, a.height]});",
  "  });",
  "  const m = panel.querySelector('.cc-ui-menu');",
  "  const sel = panel.querySelector('.cc-hit.cc-sel');",
  "  let menu = null;",
  "  if (m && sel) {",
  "   const mr = m.getBoundingClientRect(), sr = sel.getBoundingClientRect();",
  "   menu = {dx: Math.round((mr.left-sr.left)*100)/100,",
  "           dy: Math.round((mr.top-sr.bottom)*100)/100,",
  "           w: Math.round(mr.width), h: Math.round(mr.height)};",
  "   if (Math.abs(mr.left-sr.left) > tol)",
  "    out.violations.push({case:name, kind:'menu-not-left-aligned'});",
  "   if (Math.abs((mr.top-sr.bottom) - 6) > tol)",
  "    out.violations.push({case:name, kind:'menu-not-anchored-under'});",
  "   if (getComputedStyle(m).backgroundColor === 'rgba(0, 0, 0, 0)')",
  "    out.violations.push({case:name, kind:'menu-not-opaque'});",
  "  } else out.violations.push({case:name, kind:'menu-missing'});",
  "  const dimmed = getComputedStyle(host.querySelector('.cc-box')).opacity;",
  "  if (host.classList.contains('cc-dim') && dimmed === '1')",
  "   out.violations.push({case:name, kind:'context-not-dimmed'});",
  -- R3: the panel fits the medium, and the stage is what pans
  "  const medium = Math.round(panel.clientWidth);",
  "  const over = panel.scrollWidth - panel.clientWidth;",
  "  if (over > 1)",
  "   out.violations.push({case:name, kind:'panel-overflows-medium', by:over});",
  "  const stage = panel.querySelector('.cc-stage');",
  "  const ox = getComputedStyle(stage).overflowX;",
  "  if (ox !== 'auto' && ox !== 'scroll')",
  "   out.violations.push({case:name, kind:'stage-not-a-scroll-container', got:ox});",
  "  let railOver = 0;",
  "  panel.querySelectorAll('.cc-rail').forEach(function(rl){",
  "   const a = rl.getBoundingClientRect();",
  "   diags.forEach(function(dg){",
  "    if (hits2(a, dg.getBoundingClientRect())) railOver++; }); });",
  "  if (railOver)",
  "   out.violations.push({case:name, kind:'rail-painted-over-diagram', n:railOver});",
  -- the room the hanging chrome reserves is a GUESS until measured: a
  -- menu or an open lens whose foot falls past the stage would need a
  -- vertical scroll to read, which is the defect, not the fix
  "  const sb = stage.getBoundingClientRect().bottom;",
  "  const foot = function(sel, kind){",
  "   const e = panel.querySelector(sel);",
  "   if (!e) return 0;",
  "   const b = e.getBoundingClientRect().bottom;",
  "   if (b > sb + tol) out.violations.push({case:name, kind:kind,",
  "    by: Math.round(b - sb)});",
  "   return Math.round(sb - b); };",
  "  const slack = {menu: foot('.cc-ui-menu', 'menu-below-the-fold'),",
  "   lens: foot('.cc-lens[open] .cc-lens-body', 'lens-below-the-fold')};",
  -- R1: the legibility floor, and no label clipped by its own box
  "  const fonts = {};",
  "  ['box','tag','corner'].forEach(function(k){",
  "   let lo = Infinity;",
  "   panel.querySelectorAll('.cc-' + k).forEach(function(e){",
  "    lo = Math.min(lo, parseFloat(getComputedStyle(e).fontSize)); });",
  "   if (lo === Infinity) return;",
  "   fonts[k] = lo;",
  "   if (lo < floors[k] - 0.01)",
  "    out.violations.push({case:name, kind:'label-below-floor', which:k,",
  "     got:lo, floor:floors[k]}); });",
  "  let clipped = 0;",
  "  panel.querySelectorAll('.cc-box').forEach(function(e){",
  "   if (e.scrollWidth > e.clientWidth + 0.5) clipped++; });",
  "  if (clipped)",
  "   out.violations.push({case:name, kind:'label-clipped-by-box', n:clipped});",
  "  const tags = Array.from(panel.querySelectorAll('.cc-tag'));",
  "  let tagHits = 0;",
  "  for (let i = 0; i < tags.length; i++)",
  "   for (let j = i+1; j < tags.length; j++)",
  "    if (hits2(tags[i].getBoundingClientRect(),",
  "              tags[j].getBoundingClientRect())) tagHits++;",
  "  if (tagHits) out.violations.push({case:name, kind:'tags-collide', n:tagHits});",
  -- the lens (§12 items 20 and 21)
  "  const lens = panel.querySelector('.cc-lens');",
  "  let lensInfo = null;",
  "  if (lens) {",
  "   const body = lens.querySelector('.cc-lens-body');",
  "   const tab = lens.querySelector('summary');",
  "   const open = lens.hasAttribute('open');",
  "   const br = body.getBoundingClientRect();",
  "   const tr = tab.getBoundingClientRect();",
  "   const box = host.querySelector('.cc-box.cc-at-R');",
  "   lensInfo = {open:open, w:Math.round(br.width), h:Math.round(br.height),",
  "    tab:tab.textContent, tabW:Math.round(tr.width),",
  "    radius:getComputedStyle(body).borderTopLeftRadius};",
  "   if (!open && (br.width > 0 || br.height > 0))",
  "    out.violations.push({case:name, kind:'closed-lens-draws'});",
  "   if (tr.width < 1)",
  "    out.violations.push({case:name, kind:'lens-tab-not-drawn'});",
  "   if (open) {",
  "    if (br.width < 1)",
  "     out.violations.push({case:name, kind:'open-lens-empty'});",
  "    if (Math.abs(br.left - box.getBoundingClientRect().left) > tol)",
  "     out.violations.push({case:name, kind:'lens-not-anchored-on-object'});",
  "    if (getComputedStyle(body).backgroundColor === 'rgba(0, 0, 0, 0)')",
  "     out.violations.push({case:name, kind:'lens-not-opaque'});",
  "    lensInfo.contextOpacity = getComputedStyle(box).opacity;",
  "    if (lensInfo.contextOpacity === '1')",
  "     out.violations.push({case:name, kind:'lens-context-not-dimmed'});",
  "   }",
  "  }",
  "  out.cases.push({case:name, medium:medium, hits:hits.length,",
  "   diagrams:diags.length, menu:menu, dimmed:dimmed, fonts:fonts,",
  "   reserveSlack:slack,",
  "   stage:{w:Math.round(stage.clientWidth), content:stage.scrollWidth,",
  "    pans:stage.scrollWidth > stage.clientWidth + 1},",
  "   lens:lensInfo, hostBoxes: host.querySelectorAll('.cc-box').length});",
  " });",
  " document.getElementById('chrome-audit').textContent =",
  "  JSON.stringify(out, null, 1);",
  "})();",
  "</script>"]

/-- One panel's chrome over a rendered diagram, in static form: the same
`hitStyle`, `menuStyle`, `lensStyle`, `lensHtml`, `decorateLast` and `css`
the live panel uses, with plain anchors in place of the `MakeEditLink`
components, inside a `div` of the MEDIUM's width. -/
def Panel.staticPanel (name : String) (medium : Nat) (dim : Bool)
    (lens? : Option (PanelLens × Bool)) (diagram : Html) (rail : Array Html) :
    Html :=
  let boxes := Panel.addressedLast diagram
  let anchor := fun (body : Array Html) =>
    Html.element "a" #[("href", "#")] body
  let hits : Array Html := boxes.map fun (p, style) =>
    Html.element "div"
      #[("class", if p == "R" then "cc-hit cc-sel" else "cc-hit"),
        ("data-path", p), ("style", Panel.hitStyle style)]
      #[anchor #[]]
  let menu : Array Html :=
    match boxes.find? (fun b => b.1 == "R") with
    | none => #[]
    | some (_, style) =>
        #[Html.element "div"
            #[("class", "cc-ui-menu"), ("style", Panel.menuStyle style)]
            #[Panel.div "cc-ui-head"
                #[Panel.spanText "cc-ui-node" "root", anchor #[Html.text "×"]],
              anchor #[Panel.div "cc-ui-row"
                  #[Panel.spanText "cc-ui-move" "merge",
                    Panel.spanText "cc-ui-law" "Converters.comp_smul"]],
              anchor #[Panel.div "cc-ui-row"
                  #[Panel.spanText "cc-ui-move" "drop_idle",
                    Panel.spanText "cc-ui-law"
                      "Converter.attachAt_of_not_provides"]]]]
  let lens : Array Html :=
    match lens? with
    | none => #[]
    | some (l, isOpen) => #[Panel.lensHtml isOpen l]
  Html.element "div"
    #[("class", "cc-medium"), ("style", Json.mkObj [("width", s!"{medium}px")])]
    #[Html.element "div"
        #[("class", "cc-panel"), ("data-case", name),
          ("style", Panel.reserveStyle 2
            ((lens?.map (fun l => l.1.lines.size)).getD 0))]
        #[Html.element "style" #[] #[Html.text Panel.css],
          Panel.div "cc-stage"
            #[Panel.decorateLast (hits ++ menu ++ lens) dim diagram],
          Panel.div "cc-rail" rail]]

/-- info: #cc_panel chrome: 5 media → .lake/cc_panel_chrome.html -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  let shapeOf : Lean.Term → Elab.TermElabM Html := fun t => do
    let e ← Elab.Term.elabTerm t none
    Elab.Term.synthesizeSyntheticMVarsNoPostponing
    return Diagram.html (← Diagram.shapeWithDirs (← instantiateMVars e) [])
  let term ←
    `(term| mask •[Sum.inl Party.u] (mask •[Sum.inl Party.u] (toyR ∥ toyR)))
  let single ← shapeOf term
  let pair := Diagram.pairHtml (← shapeOf (← `(term| toyR ∥ toyR)))
    "≈[ε₁ + ε₂]" single
  -- the lens the live panel would build, at the root of the same term
  let lens ← do
    let e ← instantiateMVars (← Elab.Term.elabTerm term none)
    let some (_, style) := (Panel.addressedLast single).find? (·.1 == "R")
      | throwError "the emitter stamped no root box"
    let some l ← Panel.lensAt e [] style | throwError "no lens at the root"
    pure l
  let rail : Array Html :=
    #[Panel.div "cc-rail-cap" #[Html.text "calc"],
      Panel.div "cc-rail-term"
        #[Html.text "mask •[Sum.inl Party.u] (mask •[Sum.inl Party.u] (toyR ∥ toyR))"],
      Panel.div "cc-rail-rel"
        #[Panel.spanText "cc-rail-rel-sym" "≡",
          Panel.spanText "cc-rail-law" "Converters.comp_smul"],
      Panel.div "cc-rail-term"
        #[Html.text
            "(mask.word (Sum.inl Party.u) * mask.word (Sum.inl Party.u)) • (toyR ∥ toyR)"],
      Panel.div "cc-rail-acc" #[Html.text "ε ≤ ε₁ + ε₂"],
      Panel.div "cc-rail-btns"
        #[Html.element "a" #[("href", "#")]
            #[Panel.spanText "cc-ui-btn" "write calc below"],
          Html.element "a" #[("href", "#")]
            #[Panel.spanText "cc-ui-btn" "undo"]]]
  let cases : List (String × Nat × Bool × Option (PanelLens × Bool) × Html) :=
    [("D4 single, infoview narrow", 375, true, some (lens, false), single),
     ("D4 single, infoview wide", 600, true, some (lens, false), single),
     ("D4 single, lens open", 600, false, some (lens, true), single),
     ("D5 pair, infoview narrow", 375, true, none, pair),
     ("D5 pair, gallery wide", 1200, true, none, pair)]
  let body := String.join (cases.map fun (name, medium, dim, lens?, diagram) =>
    s!"<p class=\"cap\">{name} — medium {medium}px</p>" ++
      Gallery.htmlString (Panel.staticPanel name medium dim lens? diagram rail))
  let page :=
    "<!doctype html><html><head><meta charset=\"utf-8\">" ++
    "<title>CC panel chrome and media (DESIGN §12 items 12, 20, 21)</title>" ++
    "<style>body{margin:24px;} p.cap{font:12px monospace;color:#666;} " ++
    ".cc-medium{outline:1px solid #e6e6e6; margin-bottom:300px;}</style>" ++
    "</head><body>" ++ body ++ Panel.chromeAudit ++ "</body></html>"
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile ".lake/cc_panel_chrome.html" page
  Lean.logInfo "#cc_panel chrome: 5 media → .lake/cc_panel_chrome.html"

/-! ### The stylesheet survives serialization

`Panel.css` is emitted as the TEXT of a `style` element, and both
serializers escape `&`, `<`, `>` and `"` there.  A rule containing one of
them does not error — it silently becomes `&gt;` and stops matching, which
is exactly how a child combinator died once already.  So the alphabet is
the receipt. -/

/-- info: css: 0 escapable characters, 3 legibility floors, 8 `:has(` rules -/
#guard_msgs in
#eval do
  let bad := (Panel.css.toList.filter fun c =>
    c == '<' || c == '>' || c == '&' || c == '"').length
  let occurrences := fun (needle : String) =>
    ((Panel.css.splitOn needle).length - 1)
  IO.println s!"css: {bad} escapable characters, \
{occurrences "!important"} legibility floors, {occurrences ":has("} `:has(` rules"

/-! ### A move the algebra does not license is not offered

The panel refuses exactly what `#cc_rewrite` refuses — the gate is the
term, never the picture. -/

/-- error: commute: `⊣` past `⊣` needs `ResourceSystem.block_comm` (unproved) -/
#guard_msgs in
#cc_panel (⊣[Party3.a] (⊣[Party3.e] toy3)) with [commute]

-- And an address the term does not have is an error, not a silent no-op.
/-- error: path: `left` here is not a `∥` node
  mask •[Party.u] toyR -/
#guard_msgs in
#cc_panel (mask •[Party.u] toyR) with [lift at [left]]

/-! ### The ε-rail (D5)

`toyR ≈[0] toyR` is the exact face; `close_attachAt` is eq. (4) and
`close_par` eq. (3), and the rail's last line is the running bound. -/

theorem toyClose0 : toyR ≈[(0 : ℝ)] toyR :=
  (ResourceSystem.close_zero_iff _ _).mpr rfl

/-- info: □ toyR
≈[0]
□ toyR
ε ≤ 0
— nodes (right) —
[·]  ⟶  — -/
#guard_msgs in
#cc_close toyClose0

-- eq. (4): attachment is non-expanding, so the bound does not move.
/-- info: ◠ mask @ Party.u
  □ toyR
≈[0]
◠ mask @ Party.u
  □ toyR
attach mask at Party.u  ⟨ResourceSystem.close_attachAt⟩
ε ≤ 0
— nodes (right) —
[·]  ⟶  lift
[inner]  ⟶  —
— have —
have step1 : mask •[Party.u] toyR ≈[0] mask •[Party.u] toyR :=
  ResourceSystem.close_attachAt mask Party.u toyClose0
step1 -/
#guard_msgs in
#cc_close toyClose0 with [attach mask at Party.u]

-- eq. (3): the bounds ADD, and the accumulator is the theorem.
/-- info: ∥
  □ toyR
  □ toyR
≈[0 + 0]
∥
  □ toyR
  □ toyR
par toyClose0  ⟨ResourceSystem.close_par⟩
ε ≤ 0 + 0
— nodes (right) —
[left]  ⟶  —
[right]  ⟶  —
— have —
have step1 : toyR ∥ toyR ≈[0 + 0] toyR ∥ toyR :=
  ResourceSystem.close_par (by norm_num) (by norm_num) toyClose0 toyClose0
step1 -/
#guard_msgs in
#cc_close toyClose0 with [par toyClose0]

-- The bridge: a D4 `=`-move on the right endpoint, embedded in the
-- ε-chain at zero cost by `close_zero_iff` — the running bound picks up
-- the `+ 0` the accounting really incurs.
theorem maskClose : (mask •[Party.u] (mask •[Party.u] toyR)) ≈[(0 : ℝ)]
    (mask •[Party.u] (mask •[Party.u] toyR)) :=
  (ResourceSystem.close_zero_iff _ _).mpr rfl

/-- info: ◠ mask @ Party.u
  ◠ mask @ Party.u
    □ toyR
≈[0 + 0]
◠ mask.word Party.u * mask.word Party.u @ Party.u
  □ toyR
move merge  ⟨Converter.word_smul, Converters.comp_smul, ResourceSystem.close_zero_iff, ResourceSystem.close_trans⟩
ε ≤ 0 + 0
— nodes (right) —
[·]  ⟶  —
[inner]  ⟶  —
— have —
have step1 : mask •[Party.u] mask •[Party.u] toyR ≈[0 + 0] (mask.word Party.u * mask.word Party.u) • toyR :=
  ResourceSystem.close_trans (by norm_num) (by norm_num) maskClose ((ResourceSystem.close_zero_iff _ _).mpr ((Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm))
step1 -/
#guard_msgs in
#cc_close maskClose with [move merge]

/-- The eq.-(4) rung, pasted back from `write have-chain below` verbatim. -/
theorem pasted_close : mask •[Party.u] toyR ≈[(0 : ℝ)] mask •[Party.u] toyR :=
  have step1 : mask •[Party.u] toyR ≈[0] mask •[Party.u] toyR :=
    ResourceSystem.close_attachAt mask Party.u toyClose0
  step1

/-- info: 'RandomSystems.CC.PanelTests.pasted_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_close

/-- The `=`-into-ε bridge, pasted back from `write have-chain below`
verbatim: a D3 move under `close_zero_iff`, appended by `close_trans`, and
the running bound is `0 + 0` — the accounting the rail displays. -/
theorem pasted_close_move :
    mask •[Party.u] mask •[Party.u] toyR ≈[(0 : ℝ) + 0]
      (mask.word Party.u * mask.word Party.u) • toyR :=
  have step1 : mask •[Party.u] mask •[Party.u] toyR ≈[0 + 0]
      (mask.word Party.u * mask.word Party.u) • toyR :=
    ResourceSystem.close_trans (by norm_num) (by norm_num) maskClose
      ((ResourceSystem.close_zero_iff _ _).mpr
        ((Converters.comp_smul (mask.word Party.u) (mask.word Party.u) toyR).symm))
  step1

/-- info: 'RandomSystems.CC.PanelTests.pasted_close_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pasted_close_move

/-! ### The words are not reserved

`inner`, `left`, `right`, `attach`, `smul`, `par`, `par_left`, `trans` and
`move` are matched with `&"…"`, so importers — and this very file — keep
all nine as ordinary identifiers. -/

def inner : Nat := 1
def left : Nat := 2
def right : Nat := 3
def attach : Nat := 4
def smul : Nat := 5
def par : Nat := 6
def par_left : Nat := 7
def trans : Nat := 8
def move : Nat := 9

example : inner + left + right + attach + smul + par + par_left + trans + move
    = 45 := rfl

end PanelTests

end RandomSystems.CC
