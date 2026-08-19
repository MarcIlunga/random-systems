/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceBridge
import RandomSystems.Jost.SurfaceDelab
import RandomSystems.Jost.SurfaceNames
import RandomSystems.Jost.SurfaceChannels
import RandomSystems.Jost.SurfaceAlgebra
import RandomSystems.Jost.SurfaceGrammar
import ProofWidgets.Component.HtmlDisplay

/-!
# The authoring surface, part 6: simulation and diagrams

Two interaction commands, inverting the visual-programming trade: pictures
and traces are *projections of checked terms*, never primary artifacts.

* `#simulate m on [q₁, q₂, …]` — run a realization's computable
  deterministic layer on a query list and print the interface-tagged
  answer trace.  A blocking step (`step = none`) prints `⊥` and stops:
  the partiality contract, observed live.  Requirement: a `Repr` family
  for the answer alphabets (`[∀ i, Repr (Out i)]`); the machine itself
  must be computable (the *resource* is noncomputable — simulation is a
  property of the presentation, which is exactly why the command takes a
  realization, not a `Resource`).
* `#cc_diagram t` — render the composition diagram of a term to the
  **DESIGN §12 visual design system**: fixed-grid geometry (labels are
  middle-ellipsized at per-kind budgets and can never stretch layout;
  the full name rides in the `title` attribute), SHAPE coding the kind
  (item 13: resource rectangle, converter and simulator rounded, never
  an ellipse), interface geography (A left, B right, E below, F above —
  Maurer11 Figs. 3–4, MaRuTa12 Fig. 1, Jost Figs. 2.1–2.4 — as the n = 2
  specialization of item 14's numbered party ladder, one converter box
  per party feeding the parallel stack, BBM18 Fig. 4), one simulator per
  dishonest interface each on its own wire with the honest interfaces
  bypassing them (item 16), a FILTERED interface drawn as the wire that
  stops without exiting (item 15), a FREE interface drawn dotted
  (item 18), interface labels on the wires, a dashed boundary only
  where a construction happened, and one rendered nesting level (deeper
  constructions collapse to a compound box).  The message log gets a
  deterministic ASCII *structure tree* (the pinnable receipt — §12
  item 7: deliberately a structure receipt, not a picture, so pins
  survive layout evolution).  Structure is discovered on the elaborated
  term by head-constant analysis (`Resource.par`, `ResourceAt.par`,
  `ResourceSystem.par`, `ResourceAt.attach`, `Converter.attachAt` =
  `•[i]`, `Converter.attachAlong` = `••[γ]` (drawn as Jost Fig. 2.1's
  CONNECTION — §12 item 28: one converter FORKED onto the interfaces γ
  reaches, each branch labelled, the merge underneath never drawn),
  `ResourceSystem.block` = `⊣[i]`, and `Converters`-scalar `•`),
  unfolding definitions only far enough to find composition — leaf boxes
  keep their user-facing names.
* `#cc_diagram thm Name` — render an equality (or `≈[ε]`) theorem as the
  papers' figure pair: both sides drawn, the relation glyph between
  (Maurer11 Fig. 3's top/bottom reading; §12 item 6).
* `#cc_diagram t with [fold …, unfold …]` — the D1 **view clause**: it
  adjusts the PROJECTION, never the term.  `fold α` collapses α's
  maximal same-interface serial run into one pill under the composed
  name (`enc∘enc∘enc`, ellipsized to `enc∘…enc` in the box — never a
  count form); `fold A ∥ B as "N"` collapses a stack to one resource
  box; `unfold N` δ-unfolds a display-named leaf and re-discovers the
  structure inside it (`ofExpr` deliberately stops at display-named
  heads — an `unfold` overrides that per leaf).  Folded elements carry
  the §12-item-12 DECK OUTLINE and otherwise look exactly like ordinary
  boxes: a fold is an abstraction, not an elision, and the full
  structure rides in the `title`.  A collapsed subterm that is
  definitionally a registered `cc_display` constant takes THAT name and
  role (D2 recognition).

Geography is a heuristic and says so (§12 items 2 and 14).  Item 2's
four-way paper geography — A left, B right, E below, F above — is the
**n = 2 specialization** and applies only when the party interfaces are
recognisably {A, B}: then the panel carries `data-geography="classified"`.
Any other *named* interface takes a NUMBERED SLOT on the party flank, one
converter box per party stacked vertically feeding the parallel resource
stack (BBM18 Fig. 4), under `data-geography="indexed"` — an unrecognised
interface never degrades the spine.  `data-geography="fallback"` is left
for the one genuine failure: an interface whose printed form is not a name
at all (a compound term, a `clip`-ellipsized expression) and so has no
stable slot key.

Limitations are documented on each command below.
-/

namespace RandomSystems.CC

open RandomSystems.CR18.TypedResource
open Lean Elab Command Meta ProofWidgets Server

/-! ## `#simulate` -/

namespace Sim

variable {I : Type} {input output : I → Type}

/-- Run a realization over labelled queries, rendering each answer with the
per-interface `Repr` family.  Stops at the first blocking step. -/
def run [inst : ∀ i, Repr (output i)]
    (m : InterfaceMachine input output)
    (steps : List (String × InterfaceQuery input output)) : String :=
  String.intercalate "\n" (go m.init steps)
where
  go : m.State → List (String × InterfaceQuery input output) → List String
    | _, [] => []
    | s, (label, q) :: rest =>
        match m.step s q with
        | some next =>
            s!"{label} ↦ {((inst q.fst).reprPrec next.2 0).pretty}" :: go next.1 rest
        | none =>
            [s!"{label} ↦ ⊥  (outside the domain — simulation blocked)"]

end Sim

/-- `#simulate m on [q₁, …]`: print the answer trace of the computable
realization `m` on the given queries.  Labels are the queries' own source
text.  Requires `[∀ i, Repr (Out i)]` for the machine's answer alphabets —
a missing instance surfaces as the usual synthesis error on that family.

`on` is a **non-reserved** word (`&" on "`): importers keep `on` as an
ordinary identifier.  The machine slot is `term:max` so application greed
cannot swallow the word — parenthesize a compound machine term. -/
syntax (name := simulateCmd) "#simulate " term:max &" on " "[" term,* "]" : command

macro_rules
  | `(command| #simulate $m on [$qs,*]) => do
    let items ← qs.getElems.mapM fun (q : Lean.TSyntax `term) => do
      let display : Lean.Syntax :=
        match q with
        | `(($inner : $_ty)) => inner.raw
        | _ => q.raw
      let label := (display.reprint.getD "«?»").trimAscii.toString
      `(term| ($(Lean.Syntax.mkStrLit label), ($q : _)))
    `(command| #eval IO.println (RandomSystems.CC.Sim.run $m [$items,*]))

/-! ## `#cc_diagram` -/

namespace Diagram

/-- The composition shape of a term: what Fig. 2.1 draws.  Labels carry
their declared roles (`@[cc_role …]`), which drive Maurer11's palette in
the HTML panel and the sigils in the ASCII twin.

Nodes carry their elaborated sub-`Expr` (`expr?`) — the D3 data path: a
view directive or an algebraic move at a node needs the term it stands
for.  The ASCII layer never prints it.  View state (D1) lives in the
tree: `folded` on an attach node marks a fold-collapsed serial run,
`foldBox` is a fold-collapsed stack or recognized subterm (renders as a
named leaf box plus the deck outline — abstraction, not elision), and
`region` is an unfold-expanded named leaf (a dashed role-colored region
with its name at the top-left corner, per Maurer11).  `known?` on an
attach node records D2 recognition: the subterm is definitionally a
registered display-named constant.

`reach` is Jost's CONNECTION (§12 item 28): the interfaces `α ••[γ] R`
reaches at once, empty for an ordinary `α •[i] R`.  It is what the receipt
prints in `⟨…⟩` — TERM structure, `γ.first` and `γ.second` verbatim.

`reachAt` is the same two interfaces read in the BASE resource's own
coordinates (`Diagram.descendInterface`), one entry per `reach` entry, `""`
where the branch reaches no base interface at all.  The two differ exactly
when an inner connection has re-indexed the set, and the difference is the
whole of §12 item 28's targeting problem: `γ.first` of the eq.-(1) shape's
outer connection is `Sum.inl Comp.key`, whose `Sum.inl` is the `rest ⊕ Unit`
tag of the INNER connection and not a step into the `∥` tree.  Only
`reachAt` may be read for a row, a flank, or a branch label.

FIELD ORDER IS LOAD-BEARING, and this is not obvious: Lean applies a
constructor's DEFAULTS INSIDE PATTERNS, so a `match` arm that omits a
trailing defaulted argument silently becomes a CONSTRAINT that the field
equals its default (`.attach a b _ _ _ _ _ _` on a nine-field `attach`
matches only nodes whose ninth field is the default — it does not bind a
wildcard, and with a catch-all arm present it does not even warn).  `folded`
is therefore LAST: it is the one field that is `false` on every node
`ofExpr` discovers, so a consumer written against an older arity keeps
matching all discovered structure and can only ever miss a D1 VIEW state.
New arms should match `.attach conv ifc ..` or spell every field. -/
inductive Shape where
  | leaf (label : String) (role : Option Names.Role := none)
      (decl : Option Lean.Name := none) (expr? : Option Lean.Expr := none)
  | par (left right : Shape) (expr? : Option Lean.Expr := none)
  | attach (converter interface : String) (inner : Shape)
      (role : Option Names.Role := none) (decl : Option Lean.Name := none)
      (reach : List String := [])
      (reachAt : List String := [])
      (known? : Option (String × Option Names.Role) := none)
      (expr? : Option Lean.Expr := none)
      (folded : Bool := false)
  | foldBox (label : String) (role : Option Names.Role) (original : Shape)
  | region (label : String) (role : Option Names.Role) (inner : Shape)

/-- One line, truncated: labels come from `ppExpr` and must stay box-sized. -/
def clip (s : String) : String :=
  let s := (s.replace "
" " ").trimAscii.toString
  if s.length > 38 then s!"{s.take 35}…" else s

/-- Last name component: `Party.u` tags its wire as `u` — the papers
superscript bare interface letters. -/
def lastComponent (s : String) : String := ((s.splitOn ".").getLast?.getD s)

/-- The blocking converter's glyph (`ResourceSystem.block`, `⊣[i]`).  The
structure tree records it as an ordinary attach node — it *is* one — but
the picture never draws it as a box: §12 item 15, absence of output IS the
filter's rendering. -/
def blockGlyph : String := "⊣"

/-- One-line structure summary — a collapsed box's `title` and the
right-hand side of a fold receipt (`▸ NET = KEY ∥ AUT`). -/
partial def summary : Shape → String
  | .leaf label _ _ _ => label
  | .par l r _ => s!"{summary l} ∥ {summary r}"
  | .attach conv ifc inner .. =>
      s!"{conv}^{lastComponent ifc} ({summary inner})"
  | .foldBox label _ _ => label
  | .region label _ _ => label

private def structuralHeads : List Name :=
  [``RandomSystems.CC.ResourceAt.par, ``RandomSystems.CC.Resource.par,
    ``RandomSystems.CC.ResourceSystem.par,
    ``RandomSystems.CC.ResourceAt.attach,
    ``RandomSystems.CC.Converter.attachAt,
    ``RandomSystems.CC.Converter.attachAlong,
    ``RandomSystems.CC.ResourceSystem.block]

private def leafHeads : List Name :=
  [``RandomSystems.CC.Resource.ofState, ``RandomSystems.CC.Resource.ofRealization,
    ``RandomSystems.CC.Resource.sampleInit]

/-- Label, role, and declaration of a sub-term: the declared display name
and role when the head constant carries them (clean glyphs — no guillemets
here, labels are plain strings), else the clipped pretty-printed term.
The declaration name is kept so `#cc_latex` can consult `cc_latex` on the
same shape the diagram drew. -/
def labelOf (e : Expr) : MetaM (String × Option Names.Role × Option Name) := do
  let env ← getEnv
  if let .const n _ := e.getAppFn then
    if let some disp := Names.displayName? env n then
      return (disp, Names.role? env n, some n)
    else
      return (clip (toString (← ppExpr e)), Names.role? env n, some n)
  return (clip (toString (← ppExpr e)), none, none)

/-- Reading a connection's two interfaces is a CONVENIENCE, never a cost
centre — same discipline as D2 recognition: the reduction runs under its own
heartbeat budget and an overrun keeps the unreduced projection. -/
private def reachHeartbeats : Nat := 400

/-- **The interfaces a connection reaches**: `γ.first` and `γ.second`
(`Connection`, `Jost/SurfaceCarrier.lean`), reduced to the names Jost's
Fig. 2.1 hangs on the two inner wires of π_ε^A ("interface A of `Key`",
"interface A of `AuthChan`").  Total: a `split` that does not compute keeps
the unreduced projection as its label, so a diagram is never the reason an
elaboration hangs or fails. -/
private def reduceBudgeted (e : Expr) : MetaM Expr := do
  try
    withCurrHeartbeats <|
      withTheReader Core.Context
        ({ · with maxHeartbeats := reachHeartbeats * 1000 }) do
        Meta.reduce e
  catch _ => pure e

def connectionReach (connection : Expr) : MetaM (List String) := do
  let read (proj : Name) : MetaM String := do
    let raw ← mkAppM proj #[connection]
    return clip (toString (← ppExpr (← reduceBudgeted raw)))
  try
    return [← read ``Connection.first, ← read ``Connection.second]
  catch _ => return []

/-- **An outer index, read in the BASE resource's own coordinates.**

`α ••[γ] R` RE-INDEXES: its result is indexed by `rest ⊕ Unit`, not by `R`'s
own interface set (`Connection.split : K ≃ rest ⊕ (Unit ⊕ Unit)`,
`ResourceSystem.mergeAlong`).  So an index handed to a converter sitting
OUTSIDE a connection is an index into `rest`, and its `Sum.inl` is the merge
tag — not a step into the `∥` tree.  Reading a row out of it directly is the
category error the eq.-(1) shape exhibits: `gammaV.first = Sum.inl Comp.key`
and `gammaV.second = Sum.inl Comp.aut` share a `Sum.inl` and name *different*
components of `toyR ∥ toyR`.  Pushing them back through the inner
`γ.untouched` recovers `Sum.inl Party.v` and `Sum.inr Party.v`, which is what
Jost Fig. 2.1 draws (π_ε^B reaching interface B of `Key` and of `AuthChan`).

`none` is the honest answer for `Sum.inr ()`: that index names the INNER
converter's own outer interface and reaches no base resource at all.
Attachments that do not re-index (`•[i]`, `⊣[i]`, a `Converters` scalar) pass
an index through unchanged.  Total by construction — an index that does not
reduce to a `Sum` constructor stops the descent and is returned as it
stands. -/
partial def descendInterface (carrier index : Expr) :
    MetaM (Option Expr) := do
  let args := carrier.getAppArgs
  match carrier.getAppFn with
  | .const n _ =>
      if n = ``RandomSystems.CC.Converter.attachAlong ∧ args.size ≥ 3 then
        let gamma := args[args.size - 2]!
        let inner := args[args.size - 1]!
        let reduced ← reduceBudgeted index
        if reduced.isAppOfArity ``Sum.inl 3 then
          let untouched ←
            try pure (some (← mkAppM ``Connection.untouched
              #[gamma, reduced.getArg! 2]))
            catch _ => pure none
          match untouched with
          | some u => descendInterface inner u
          | none => return none
        else return none
      else if (n = ``RandomSystems.CC.Converter.attachAt ∧ args.size ≥ 3) ∨
          (n = ``RandomSystems.CC.ResourceSystem.block ∧ args.size ≥ 2) ∨
          (n = ``HSMul.hSMul ∧ args.size ≥ 6) then
        descendInterface args[args.size - 1]! index
      else return some index
  | _ => return some index

/-- The reach of `α ••[γ] R`, in `R`'s BASE interface coordinates: one entry
per branch, `""` for a branch that reaches no base interface (`descendInterface`
answered `none`).  This — never `connectionReach` — is what may be read for a
core row, a flank side, or a branch label. -/
def connectionReachAt (connection carrier : Expr) : MetaM (List String) := do
  let read (proj : Name) : MetaM String := do
    let raw ← mkAppM proj #[connection]
    match ← (try descendInterface carrier raw catch _ => pure none) with
    | none => return ""
    | some e => return clip (toString (← ppExpr (← reduceBudgeted e)))
  try
    return [← read ``Connection.first, ← read ``Connection.second]
  catch _ => return []

/-- Does an `unfold` directive target this constant?  Matches the declared
display name or the declaration's last name component. -/
private def unfoldTargets (env : Environment) (n : Name)
    (unfoldSet : List String) : Bool :=
  unfoldSet.contains (Names.displayOf env n) ||
    (match n with | .str _ s => unfoldSet.contains s | _ => false)

/-- Discover the composition shape: recognize the surface composition
constants; a display-named head is its own identity (no unfolding — the
name IS the paper object) UNLESS an `unfold` directive names it, in which
case it δ-unfolds into a `region` carrying its name and role; otherwise
unfold a definition only when that discovers more structure, keeping the
friendly name as the leaf label.  Every node keeps its sub-`Expr`. -/
partial def ofExpr (e : Expr) (unfoldSet : List String := []) : MetaM Shape := do
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const n _ =>
      let env ← getEnv
      if n = ``RandomSystems.CC.ResourceAt.par ∨
          n = ``RandomSystems.CC.Resource.par ∨
          n = ``RandomSystems.CC.ResourceSystem.par then
        if h : args.size ≥ 2 then
          return .par (← ofExpr args[args.size - 2] unfoldSet)
            (← ofExpr args[args.size - 1] unfoldSet) (some e)
        else return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
      else if n = ``RandomSystems.CC.ResourceAt.attach then
        if h : args.size ≥ 4 then
          let interface := clip (toString (← ppExpr args[args.size - 4]))
          let (converter, role, decl) ← labelOf args[args.size - 3]
          return .attach converter interface
            (← ofExpr args[args.size - 1] unfoldSet) role decl (expr? := some e)
        else return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
      else if n = ``RandomSystems.CC.Converter.attachAt then
        -- `α •[i] R` (part 4): trailing explicit args are
        -- `converter interface resource`.
        if h : args.size ≥ 3 then
          let (converter, role, decl) ← labelOf args[args.size - 3]
          let interface := clip (toString (← ppExpr args[args.size - 2]))
          return .attach converter interface
            (← ofExpr args[args.size - 1] unfoldSet) role decl (expr? := some e)
        else return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
      else if n = ``RandomSystems.CC.Converter.attachAlong then
        -- `α ••[γ] R` (part 4): a converter reaching the TWO interfaces the
        -- connection `γ` names.  Trailing explicit args are
        -- `converter connection resource`.  The node carries BOTH the
        -- connection (its outer identity, which is what crosses the boundary)
        -- and its `reach` — the two interfaces §12 item 28 forks onto.  The
        -- merge underneath is an implementation detail the author never
        -- writes, so it is never drawn.
        if h : args.size ≥ 3 then
          let (converter, role, decl) ← labelOf args[args.size - 3]
          let interface := clip (toString (← ppExpr args[args.size - 2]))
          let reach ← connectionReach args[args.size - 2]
          let reachAt ← connectionReachAt args[args.size - 2] args[args.size - 1]
          return .attach converter interface
            (← ofExpr args[args.size - 1] unfoldSet) role decl
            (reach := reach) (reachAt := reachAt) (expr? := some e)
        else return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
      else if n = ``RandomSystems.CC.ResourceSystem.block then
        -- `⊣[i] R` (part 5): the blocking converter, drawn under its glyph.
        if h : args.size ≥ 2 then
          let interface := clip (toString (← ppExpr args[args.size - 2]))
          return .attach blockGlyph interface
            (← ofExpr args[args.size - 1] unfoldSet) (expr? := some e)
        else return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
      else if n = ``HSMul.hSMul then
        -- `γ • R` for `γ : Converters S I i` (part 5): the interface is the
        -- last argument of the scalar's `Converters`/`Gamma` type.
        if h : args.size ≥ 6 then
          let scalar := args[args.size - 2]
          let scalarTy ← instantiateMVars (← inferType scalar)
          let tyArgs := scalarTy.getAppArgs
          if let .const tyHead _ := scalarTy.getAppFn then
            if (tyHead = ``RandomSystems.CC.Converters ∨
                tyHead = ``RandomSystemsCC.TypedFinite.Gamma) ∧ tyArgs.size ≥ 1 then
              let interface := clip (toString (← ppExpr tyArgs[tyArgs.size - 1]!))
              -- A single embedded converter (`α.word i`) is labelled by `α`
              -- itself; `1` is the papers' `id`.
              let scalar :=
                if let .const wn _ := scalar.getAppFn then
                  if wn = ``RandomSystems.CC.Converter.word ∧
                      scalar.getAppArgs.size ≥ 2 then
                    scalar.getAppArgs[scalar.getAppArgs.size - 2]!
                  else scalar
                else scalar
              let (converter, role, decl) ← labelOf scalar
              let converter := if converter = "1" then "id" else converter
              return .attach converter interface
                (← ofExpr args[args.size - 1] unfoldSet) role decl
                (expr? := some e)
          return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
        else return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
      else if let some disp := Names.displayName? env n then
        if unfoldTargets env n unfoldSet then
          match ← unfoldDefinition? e with
          | some inner =>
              return .region disp (Names.role? env n) (← ofExpr inner unfoldSet)
          | none => return .leaf disp (Names.role? env n) (some n) (some e)
        else return .leaf disp (Names.role? env n) (some n) (some e)
      else if leafHeads.contains n then
        return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
      else if unfoldTargets env n unfoldSet then
        -- an untagged constant named by an `unfold` directive: force the
        -- δ-step and frame the result as a named region
        match ← unfoldDefinition? e with
        | some inner =>
            return .region (Names.displayOf env n) (Names.role? env n)
              (← ofExpr inner unfoldSet)
        | none => return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
      else
        match ← unfoldDefinition? e with
        | some inner =>
            let d ← ofExpr inner unfoldSet
            match d with
            | .leaf _ _ _ _ =>
                -- A bare constant keeps its own (last-component) name —
                -- papers never print namespaces; an applied one shows its
                -- arguments via the pretty-printer.
                let pretty := clip (toString (← ppExpr e))
                let label := if e.isConst then Names.displayOf env n else pretty
                return .leaf label (Names.role? env n) (some n) (some e)
            | structural => return structural
        | none => return .leaf (clip (toString (← ppExpr e))) (expr? := some e)
  | _ => return .leaf (clip (toString (← ppExpr e))) (expr? := some e)

/-- The role sigil of a leaf box: `□` for assumed/untagged resources,
`◆` for constructed/ideal ones (and simulators appearing as leaves),
`▢` for games. -/
def leafSigil : Option Names.Role → String
  | some .constructed => "◆"
  | some .simulator => "◆"
  | some .game => "▢"
  | _ => "□"

/-- Deterministic ASCII rendering — the pinnable receipt.  Deliberately the
*structure tree* (attach spine, `∥` grouping), not the Fig.-1 layout: the
tree is stable under layout heuristics, which is what a pinned receipt
wants.  The Fig.-1 placement lives in the HTML panel.  View state shows
as `▸` (a folded run keeps its composed name; a folded box shows what it
abbreviates) and `◈` (an unfolded named region, expanded below).  A
CONNECTION node prints the interfaces it reaches in `⟨…⟩` after its
connection: the reach is TERM structure (`γ.first`, `γ.second`), so the
structure receipt owes it a line. -/
partial def ascii (s : Shape) (indent : String := "") : String :=
  match s with
  | .leaf label role _ _ => s!"{indent}{leafSigil role} {label}"
  | .par l r _ =>
      s!"{indent}∥\n{ascii l (indent ++ "  ")}\n{ascii r (indent ++ "  ")}"
  | .attach conv ifc inner _ _ reach _ _ _ folded =>
      let along :=
        if reach.isEmpty then ""
        else s!" ⟨{String.intercalate ", " reach}⟩"
      s!"{indent}{if folded then "▸" else "◠"} {conv} @ {ifc}{along}\n{ascii
        inner (indent ++ "  ")}"
  | .foldBox label _ original => s!"{indent}▸ {label} = {summary original}"
  | .region label _ inner =>
      s!"{indent}◈ {label}\n{ascii inner (indent ++ "  ")}"

/- React's `style` prop takes a MAPPING, not a CSS string (invariant #62:
a string here crashes the infoview panel), so the styles are Json objects
with camelCase property names. -/

/-- Maurer11's role palette (eqs. (1)–(2)): assumed resources blue,
constructed/ideal red, converters green, the simulator teal, games
neutral. -/
def roleColor : Option Names.Role → String
  | some .assumed => "#2563c4"
  | some .constructed => "#c0392b"
  | some .converter => "#1e8449"
  | some .simulator => "#0e7c7b"
  | some .game => "#6b7280"
  | none => "#555555"

/-! ### The §12 fixed grid

Geometry is semantic, never typographic (DESIGN §12 item 1): every box has
a constant grid size, labels are middle-ellipsized at per-kind budgets,
and the full name always rides in the `title` attribute.  A pathologically
long name renders at exactly the same box size as a short one. -/

/-- Per-kind label budgets (§12 item 1).  Glyph names (`•══•`, `—→`, …)
never reach a budget — they are short by construction. -/
def resourceBudget : Nat := 12

/-- Converter boxes are the papers' smallest objects: 8 codepoints. -/
def converterBudget : Nat := 8

/-- Interface tags on wires: bare letters on paper, 6 codepoints here. -/
def interfaceBudget : Nat := 6

/-- Middle-ellipsis at a codepoint budget: keeps both the head and the
tail of the name visible (`TheAbsurdly…idth`), never stretches a box. -/
def middleEllipsis (budget : Nat) (s : String) : String :=
  if s.length ≤ budget then s
  else
    let head := budget / 2
    let tail := budget - 1 - head
    s!"{s.take head}…{s.drop (s.length - tail)}"

/-! ### Interface geography (§12 items 2 and 14) -/

/-- Where a spine converter sits.  Item 2's four-way paper geography —
A left, B right, E below, Jost's free interface F above — is the **n = 2
specialization** (§12 item 14) and holds only for the recognisable
interface set {A, B, E, F}.  Every other *named* interface takes a
numbered slot on the party flank (`party k`, the BBM18-Fig.-4 ladder):
`Flank` carries an INDEX precisely so that an unrecognised party never
degrades the spine.  `unnamed` is the sole genuine failure — an interface
whose printed form is not a name (a compound term, a `clip`-ellipsized
expression) and so cannot key a stable slot. -/
inductive Flank | left | right | below | above | party (index : Nat) | unnamed
  deriving BEq, Repr

/-- Is the printed interface a NAME?  Only a name can key a stable slot in
the item-14 ladder; a pretty-printed compound (spaces) or a `clip`-
ellipsized one cannot. -/
def nameableInterface (interface : String) : Bool :=
  -- no leading `!`: inside `RandomSystems.CC` the scoped `i ! x` query
  -- notation owns the token, and a term may not START with it
  let t := lastComponent interface
  (t != "") && (t.any Char.isWhitespace == false) &&
    ((t.splitOn "…").length == 1)

/-- Classify an interface by its last name component: the four paper
interfaces to their paper places, any other name to a numbered party slot
(`geography` alone knows the spine order, so it assigns the real index —
this returns the placeholder `party 0`), and an unnameable one to
`unnamed`. -/
def classifyInterface (interface : String) : Flank :=
  let t := (lastComponent interface).toLower
  if ["a", "u", "alice", "sender", "snd"].contains t then .left
  else if ["b", "v", "bob", "receiver", "rcv"].contains t then .right
  else if ["e", "eve", "adv", "adversary"].contains t then .below
  else if ["f", "free"].contains t then .above
  else if nameableInterface interface then .party 0
  else .unnamed

/-! ### The positioned-primitive engine (§12, round 3)

Flexbox owned the layout and could not keep wires on box edges; now the
emitter owns the coordinate system.  Every diagram is one
`position: relative` container and every box, wire, and tag is an
absolutely-positioned child at coordinates COMPUTED in Lean from the
§12 grid constants — a wire endpoint lands on a box edge, a bus, or a
labeled boundary crossing by construction, and the gallery's geometry
audit re-checks the rendered result in the browser.  The grid is
orthogonal, so 2px divs cover every wire.  Styles stay React camelCase
Json objects (the #62 rule); the gallery serializer kebab-cases them. -/

private def resWF : Float := 120     -- resource box
private def resHF : Float := 44
private def pillWF : Float := 76     -- converter pill
private def pillHF : Float := 34
private def rowGapF : Float := 10    -- ∥ stack gap
private def flankGapF : Float := 8   -- flank rows gap
private def chainGapF : Float := 8   -- serial pill connector
private def busLeadF : Float := 12   -- bus → row lead
private def coreLeadF : Float := 30  -- tagged converter → core wire
private def stubLenF : Float := 30   -- bare-resource / boundary stub
private def parStubF : Float := 18   -- bare-∥ outward stub
private def padXF : Float := 12     -- dashed boundary padding
private def padYF : Float := 14
private def dropLenF : Float := 18   -- vertical wire to a below pill
private def dangleLenF : Float := 20 -- adversary wire below the box
private def diagMarginF : Float := 8
private def busGapF : Float := 10    -- pitch of the per-interface buses
private def portPitchF : Float := 14 -- pitch of a box's port ladder
private def colPitchF : Float := 92  -- pitch of the perpendicular columns
private def connPitchF : Float := 22 -- pitch of a connection's fork (§12 item 28)
private def connLeadF : Float := 34  -- extra inner lead: the fork carries labels
private def bendRF : Float := 6      -- `radius.bend` (§12 item 29): THE bend radius
private def trackStepF : Float := 10 -- pitch of the routing channel's tracks
/-- **The straight run every lead gets before it may turn** (§12 item 29).
The first track used to sit one `trackStepF` from the flank, and a bend eats
`bendRF` of that: a lead turned 4px out of its pill, which reads as a wire
glued to the box corner and made three leads into one ragged blob.  A lead's
first segment must be visibly a segment, so the first track sits `leadInF`
out — `leadInF - bendRF` of straight wire, the same for every lead. -/
private def leadInF : Float := 16

private def wireColor : String := "#555"

/-- A positioned primitive.  Coordinates are the OUTER top-left corner
for boxes and the centerline endpoints for wires.  `openEnds` marks
deliberately open wire ports (`"1"` = the first endpoint given, `"2"` the
second, `"12"` both) that the geometry audit must not flag — an
unconnected interface is semantics, not sloppiness.  `dotted` is §12
item 18's one other stroke: a FREE interface, accessed directly by the
distinguisher.  There is no third semantic stroke. -/
private inductive Prim
  | box (x y w h radius : Float) (color borderStyle : String)
      (double smallCaps : Bool) (label title cls : String)
  /-- `target` is the INTENDED landing of a lead's last segment: the index of
  the core row that owns the interface the wire names (`cc-row-<k>` on that
  row's own box).  It is emitted as `data-target` so the geometry audit can
  read the emitter's intent back and check the drawing against it — a branch
  landing on the wrong but perfectly legal box violates no measurement, which
  is why nothing caught the eq.-(1) shape.  `""` = no claim, no check. -/
  | hwire (x y len : Float) (openEnds : String) (dotted : Bool)
      (target : String := "")
  | vwire (x y len : Float) (openEnds : String) (dotted : Bool)
  /-- `fork` names the CONNECTION a branch label belongs to (its converter's
  D4 path), emitted as `data-fork` so the audit can check that one node's
  branches carry DISTINCT labels — `γ.first ≠ γ.second` always, so two equal
  labels always mean the drawing lost the distinction.  `""` = an ordinary
  tag, not a branch label. -/
  | tag (x y : Float) (anchorStart : Bool) (content title : String)
      (fork : String := "")
  /-- The fold marker (§12 item 12): a 1px grey rounded outline offset
  `+deckOffset` behind the element at `(x, y, w, h)` — pure line work,
  reads "several of these".  Chrome: exempt from frame-content. -/
  | deck (x y w h radius : Float)
  /-- A corner name on a dashed region (§12 item 12, Maurer11's
  convention): small caption-size text at the region's top-left.
  Chrome: exempt from frame-content. -/
  | corner (x y : Float) (content title color : String)
  /-- **A BEND** (§12 item 29): the quarter turn joining a horizontal wire
  to a vertical one at the constant radius `bendRF`.  `(x, y)` is the outer
  top-left of the `(r+1) × (r+1)` corner cell and `corner` names the ROUNDED
  corner — `"tr"` draws the top and right borders, and with the radius equal
  to the cell they collapse into exactly one quarter arc.  A bend is a
  wire's turn, never a joint: its two arc ends are the wire endpoints it
  splices, which is what the audit reads from `data-corner`. -/
  | bend (x y r : Float) (corner : String) (dotted : Bool)

private def flipOpen : String → String
  | "1" => "2"
  | "2" => "1"
  | s => s

/-- Horizontal wire between two x's at height `y`; normalizes direction,
`openEnds` naming the ARGUMENTS' endpoints (`"1"` = `x1`) either way. -/
private def hw (x1 x2 y : Float) (openEnds : String := "")
    (dotted : Bool := false) (target : String := "") : Prim :=
  if x1 ≤ x2 then .hwire x1 y (x2 - x1) openEnds dotted target
  else .hwire x2 y (x1 - x2) (flipOpen openEnds) dotted target

/-- Vertical wire between two y's at `x`. -/
private def vw (y1 y2 x : Float) (openEnds : String := "")
    (dotted : Bool := false) : Prim :=
  if y1 ≤ y2 then .vwire x y1 (y2 - y1) openEnds dotted
  else .vwire x y2 (y1 - y2) (flipOpen openEnds) dotted

/-- **The two-bend orthogonal route** (§12 item 29): `(x₁, y₁)` out
horizontally, one turn at the channel track `turnX`, one turn back, in at
`(x₂, y₂)`.  Exactly two bends, both at `bendRF`; a level route degenerates
to one straight wire and no bend at all.  A route too short to seat a radius
falls back to sharp corners rather than to a smaller radius — the radius is
a constant of the design system (§12 item 1's discipline: geometry is
semantic, so a bend must not encode "this wire was cramped"). -/
private def routeHVH (x1 y1 x2 y2 turnX : Float) (openEnds : String := "")
    (dotted : Bool := false) (target : String := "") : Array Prim :=
  if (y2 - y1).abs ≤ 0.25 then #[hw x1 x2 y1 openEnds dotted target] else
  let sx : Float := if turnX ≥ x1 then 1 else -1
  let sy : Float := if y2 ≥ y1 then 1 else -1
  let room := min ((y2 - y1).abs / 2) (min (turnX - x1).abs (x2 - turnX).abs)
  if room < bendRF then
    #[hw x1 turnX y1 (if openEnds.contains '1' then "1" else ""),
      vw y1 y2 turnX "" dotted,
      hw turnX x2 y2 (if openEnds.contains '2' then "2" else "") dotted target]
  else
    let r := bendRF
    -- the rounded corner is the one the arc bulges toward
    let c1 := if sx > 0 then (if sy > 0 then "tr" else "br")
              else (if sy > 0 then "tl" else "bl")
    let c2 := if sx > 0 then (if sy > 0 then "bl" else "tl")
              else (if sy > 0 then "br" else "tr")
    let cell := fun (cx cy : Float) (cnr : String) =>
      Prim.bend (if cnr == "tl" || cnr == "bl" then cx - 1 else cx - r)
        (if cnr == "tl" || cnr == "tr" then cy - 1 else cy - r) r cnr dotted
    #[hw x1 (turnX - sx * r) y1 (if openEnds.contains '1' then "1" else "") dotted,
      cell turnX y1 c1,
      vw (y1 + sy * r) (y2 - sy * r) turnX "" dotted,
      cell turnX y2 c2,
      hw (turnX + sx * r) x2 y2 (if openEnds.contains '2' then "2" else "") dotted
        target]

private def Prim.translate (dx dy : Float) : Prim → Prim
  | .box x y w h r c bs d sc l t cls => .box (x+dx) (y+dy) w h r c bs d sc l t cls
  | .hwire x y len o dt tg => .hwire (x+dx) (y+dy) len o dt tg
  | .vwire x y len o dt => .vwire (x+dx) (y+dy) len o dt
  | .tag x y a c t fk => .tag (x+dx) (y+dy) a c t fk
  | .deck x y w h r => .deck (x+dx) (y+dy) w h r
  | .corner x y c t col => .corner (x+dx) (y+dy) c t col
  | .bend x y r c dt => .bend (x+dx) (y+dy) r c dt

/-- The ratified `space.ui.deckOffset` token. -/
private def deckOffsetF : Float := 3

/-- Chrome primitives (deck outlines, corner names) dress a region; they
never count as its content — a marker must not resize a semantic
boundary (§12 item 12). -/
private def Prim.isChrome : Prim → Bool
  | .deck .. => true
  | .corner .. => true
  | _ => false

/-- Approximate bounds (tag text estimated at 6.2px/char), for
normalization and the boundary rectangle.

TYPE SIZE IS AN EMITTER TOKEN, and this estimate is why.  The three rendered
sizes are written as `var(--cc-font-box, 13px)`, `var(--cc-font-tag, 11px)`
and `var(--cc-font-corner, 10px)`, so a host (the D4 panel) may raise them to
the reader's own em — an interface tag frozen at 11px is unreadable at an
18px editor font.  But 6.2px/char is CALIBRATED AT 11px and the item-11b
pad-symmetry audit is computed from it, so the raise is bounded: box 14px,
tag 13px, corner 12px.  (The box cap is arithmetic, not taste: the 8-codepoint
converter budget measures 67px at 14px against a 72px inner pill width.)
Rendered type and this estimate must move together, which they cannot do if
the size lives in a stylesheet. -/
private def Prim.bounds : Prim → Float × Float × Float × Float
  | .box x y w h _ _ _ _ _ _ _ _ => (x, y, x + w, y + h)
  | .hwire x y len .. => (x, y - 1, x + len, y + 1)
  | .vwire x y len _ _ => (x - 1, y, x + 1, y + len)
  | .tag x y a c .. =>
      let w := c.length.toFloat * 6.2
      if a then (x, y - 6, x + w, y + 6)
      else (x - w/2, y - 12, x + w/2, y)
  | .deck x y w h _ => (x, y, x + w + deckOffsetF, y + h + deckOffsetF)
  | .corner x y c _ _ => (x, y, x + c.length.toFloat * 6.2, y + 13)
  | .bend x y r _ _ => (x, y, x + r + 1, y + r + 1)

private def primsBounds (prims : Array Prim) :
    Float × Float × Float × Float := Id.run do
  let mut minX : Float := 1e9
  let mut minY : Float := 1e9
  let mut maxX : Float := -1e9
  let mut maxY : Float := -1e9
  for p in prims do
    let (a, b, c, d) := p.bounds
    minX := min minX a; minY := min minY b
    maxX := max maxX c; maxY := max maxY d
  return (minX, minY, maxX, maxY)

/-- Bounds of the semantic content only — chrome excluded.  This is what
a dashed boundary wraps at exactly `(padXF, padYF)` per side (§12
item 11's frame-pad symmetry). -/
private def contentBounds (prims : Array Prim) :
    Float × Float × Float × Float :=
  primsBounds (prims.filter (fun p => !p.isChrome))

/-- Coordinates are half-pixel multiples by construction; print them
exactly (`23`, `23.5`), never as floating noise. -/
private def fmtF (x : Float) : String :=
  let n := (x * 2).round
  let neg := n < 0
  let m := (if neg then -n else n).toUInt64.toNat
  let core := if m % 2 == 0 then toString (m / 2) else s!"{m / 2}.5"
  if neg then s!"-{core}" else core

private def px (v : Float) : String := s!"{fmtF v}px"

/-- The dashed-boundary padding, as CSS pixels.  Exported so the gallery's
frame-pad symmetry audit (§12 item 11b: a boundary is its content union
inflated by exactly this much per side) reads the EMITTER's numbers and
cannot drift from them. -/
def framePad : String × String := (fmtF padXF, fmtF padYF)

/-- The CONNECTION FORK pitch, as CSS pixels: the spacing of the branches
where they meet their converter (§12 item 28).  Exported for the same reason
`framePad` is — the gallery's fork audit reads the EMITTER's number and
cannot drift from it. -/
def forkPitch : String := fmtF connPitchF

private def Prim.toHtml : Prim → Html
  | .box x y w h radius color borderStyle double smallCaps label title cls =>
      let style := Json.mkObj <|
        ([("position", "absolute"), ("left", px x), ("top", px y),
          ("width", px w), ("height", px h), ("boxSizing", "border-box"),
          ("border", s!"2px {borderStyle} {color}"),
          ("borderRadius", px radius), ("color", color),
          ("display", "flex"), ("alignItems", "center"),
          ("justifyContent", "center"), ("overflow", "hidden"),
          ("whiteSpace", "nowrap"),
          ("fontFamily", "'JetBrains Mono', ui-monospace, monospace"),
          ("fontSize", "var(--cc-font-box, 13px)")] : List (String × Json))
        ++ (if double then
              ([("outline", s!"1px {borderStyle} {color}"),
                ("outlineOffset", "-4px")] : List (String × Json)) else [])
        ++ (if smallCaps then
              ([("fontVariant", "small-caps")] : List (String × Json)) else [])
      Html.element "div"
        #[("style", style), ("title", title), ("class", cls)]
        (if label == "" then #[] else #[Html.text label])
  | .hwire x y len openEnds dotted target =>
      -- a dotted wire is a 2px top BORDER on a zero-height div: the
      -- rendered rect, hence every geometry-audit measurement, is
      -- identical to the solid form's
      let attrs : Array (String × Json) :=
        #[("style", Json.mkObj <|
            ([("position", "absolute"), ("left", px x), ("top", px (y - 1)),
              ("width", px len)] : List (String × Json)) ++
            (if dotted then
              ([("height", "0"),
                ("borderTop", s!"2px dotted {wireColor}")] : List (String × Json))
             else [("height", "2px"), ("background", wireColor)])),
          ("class", "cc-wire"), ("data-axis", "h")]
      let attrs :=
        if dotted then attrs.push ("data-stroke", "dotted") else attrs
      let attrs :=
        if target == "" then attrs else attrs.push ("data-target", target)
      Html.element "div"
        (if openEnds == "" then attrs else attrs.push ("data-open", openEnds))
        #[]
  | .vwire x y len openEnds dotted =>
      let attrs : Array (String × Json) :=
        #[("style", Json.mkObj <|
            ([("position", "absolute"), ("left", px (x - 1)), ("top", px y),
              ("height", px len)] : List (String × Json)) ++
            (if dotted then
              ([("width", "0"),
                ("borderLeft", s!"2px dotted {wireColor}")] : List (String × Json))
             else [("width", "2px"), ("background", wireColor)])),
          ("class", "cc-wire"), ("data-axis", "v")]
      let attrs :=
        if dotted then attrs.push ("data-stroke", "dotted") else attrs
      Html.element "div"
        (if openEnds == "" then attrs else attrs.push ("data-open", openEnds))
        #[]
  | .tag x y anchorStart content title fork =>
      let attrs : Array (String × Json) :=
        #[("style", Json.mkObj
            [("position", "absolute"), ("left", px x), ("top", px y),
             ("transform",
              if anchorStart then "translateY(-50%)"
              else "translate(-50%, -100%)"),
             ("fontFamily", "'JetBrains Mono', ui-monospace, monospace"),
             ("fontSize", "var(--cc-font-tag, 11px)"),
             ("color", wireColor), ("whiteSpace", "nowrap")]),
          ("class", "cc-tag"), ("title", title)]
      Html.element "div"
        (if fork == "" then attrs else attrs.push ("data-fork", fork))
        #[Html.text content]
  | .deck x y w h radius =>
      Html.element "div"
        #[("style", Json.mkObj
            [("position", "absolute"),
             ("left", px (x + deckOffsetF)), ("top", px (y + deckOffsetF)),
             ("width", px w), ("height", px h),
             ("boxSizing", "border-box"),
             ("border", "1px solid #888888"),
             ("borderRadius", px radius)]),
          ("class", "cc-deck")]
        #[]
  | .corner x y content title color =>
      Html.element "div"
        #[("style", Json.mkObj
            [("position", "absolute"), ("left", px x), ("top", px y),
             ("fontFamily", "'JetBrains Mono', ui-monospace, monospace"),
             ("fontSize", "var(--cc-font-corner, 10px)"), ("color", color),
             ("whiteSpace", "nowrap")]),
          ("class", "cc-corner"), ("title", title)]
        #[Html.text content]
  | .bend x y r cnr dotted =>
      let stroke := if dotted then "dotted" else "solid"
      let side := s!"2px {stroke} {wireColor}"
      let borders : List (String × Json) :=
        match cnr with
        | "tr" => [("borderTop", side), ("borderRight", side),
                   ("borderTopRightRadius", px (r + 1))]
        | "br" => [("borderBottom", side), ("borderRight", side),
                   ("borderBottomRightRadius", px (r + 1))]
        | "tl" => [("borderTop", side), ("borderLeft", side),
                   ("borderTopLeftRadius", px (r + 1))]
        | _ => [("borderBottom", side), ("borderLeft", side),
                ("borderBottomLeftRadius", px (r + 1))]
      Html.element "div"
        #[("style", Json.mkObj <|
            ([("position", "absolute"), ("left", px x), ("top", px y),
              ("width", px (r + 1)), ("height", px (r + 1)),
              ("boxSizing", "border-box")] : List (String × Json)) ++ borders),
          ("class", "cc-bend"), ("data-corner", cnr)]
        #[]

/-- A laid-out sub-picture: primitives in local coordinates with their
joint extent.  `portL`/`portR` are the y's of the side connection
points; `solid` says the sides are solid box edges (a wire may enter at
ANY height there), false for a constructed sub-picture whose only
connection points are its protruding stub tips. -/
private structure Pic where
  w : Float
  h : Float
  portL : Float
  portR : Float
  solid : Bool
  prims : Array Prim
  deriving Inhabited

/-- Normalize primitives so the joint bounding box starts at the origin
(minima floored to the half-pixel grid); ports given in
pre-normalization coordinates, defaulting to mid-height. -/
private def Pic.ofPrims (prims : Array Prim)
    (portL? portR? : Option Float := none) (solid : Bool := true) : Pic :=
  if prims.isEmpty then ⟨0, 0, 0, 0, solid, #[]⟩ else
    let (minX, minY, maxX, maxY) := primsBounds prims
    let fx := (minX * 2).floor / 2
    let fy := (minY * 2).floor / 2
    let h := maxY - fy
    ⟨maxX - fx, h,
     (portL?.map (· - fy)).getD (h / 2), (portR?.map (· - fy)).getD (h / 2),
     solid, prims.map (·.translate (-fx) (-fy))⟩

/-- One row of a `∥` stack: its horizontal edges, side-port heights, and
vertical extent. -/
private structure RowPort where
  leftX : Float
  rightX : Float
  portLY : Float
  portRY : Float
  centerY : Float
  height : Float
  solid : Bool
  /-- The row's BAND (§12 item 30): the strip it owns in the stack.  Every
  wire and pill that belongs to this row lives inside it, and the bands are
  disjoint, which is what makes the picture planar by construction. -/
  bandTop : Float := 0
  bandH : Float := 0
  deriving Inhabited

/-- **Stack components vertically into BANDS** (§12 item 30).  Row `r` owns
the closed strip `[bandTop, bandTop + bandH]`; the bands tile the stack and
are pairwise disjoint, which is the whole planarity argument — every wire,
pill and rung belonging to a row is confined to that row's band, so wires of
different rows cannot meet.  `bandMin` is what the flanks need for row `r`
(its converter cluster is taller than the box); the comp is centred in its
band and the bands are `rowGapF` apart.  `bandMin = []` is the plain stack. -/
private def stackRowsBands (comps : List Pic) (bandMin : List Float) :
    Pic × List RowPort := Id.run do
  let wMax := comps.foldl (fun a c => max a c.w) 0
  let mut prims : Array Prim := #[]
  let mut ports : List RowPort := []
  let mut y : Float := 0
  for k in [0:comps.length] do
    let c := comps[k]!
    let bh := max c.h (bandMin[k]?.getD 0)
    let x := (wMax - c.w) / 2
    let dy := y + (bh - c.h) / 2
    prims := prims ++ c.prims.map (·.translate x dy)
    ports := ports ++
      [⟨x, x + c.w, dy + c.portL, dy + c.portR, dy + c.h / 2, c.h, c.solid,
        y, bh⟩]
    y := y + bh + rowGapF
  let h := if comps.isEmpty then 0 else y - rowGapF
  return (⟨wMax, h, h / 2, h / 2, true, prims⟩, ports)

/-- The plain stack: every band is its own row. -/
private def stackRows (comps : List Pic) : Pic × List RowPort :=
  stackRowsBands comps []

/-- The rungs of a box's PORT LADDER: `n` connection points on one edge,
at offsets from the box centre that are symmetric by construction (§12
item 14 — a multi-party box has off-centre ports, so the machine-checked
port rule is the ladder's symmetry about the centre, not a single axis).
`n = 1` gives the centre, recovering the n = 2 geometry exactly.  The
pitch is floored to whole pixels so that `+d` and `−d` survive the
half-pixel emitter grid as an exact pair. -/
private def ladderOffset (span : Float) (n k : Nat) : Float :=
  if n ≤ 1 then 0 else
    let pitch := (min portPitchF ((span - 12) / (n - 1).toFloat)).floor
    (k.toFloat - (n - 1).toFloat / 2) * pitch

/-- **The stack BRACKET** — one side of a core whose rows the term does not
name (§12 item 30(c)).  It is the composite's own edge, not a wire: one
vertical at `busLeadF` from the stack, one spur to each row's axis, and the
entries land on it.  Used for the two cases where "which row?" has no
answer: a side with NO converters at all (the untouched interfaces of a
`∥`, which really are all the rows'), and a side whose interface set an
inner CONNECTION has re-indexed.  A single entry facing a single solid row
it already meets on axis takes a direct wire instead.  Returns the wires and
the x each entry terminates at. -/
private def sideWiring (isLeft : Bool) (sx sy stackW : Float)
    (ports : List RowPort) (entryYs : List Float) :
    Array Prim × List Float := Id.run do
  let edgeX := fun (p : RowPort) =>
    if isLeft then sx + p.leftX else sx + p.rightX
  let portY := fun (p : RowPort) =>
    if p.solid then sy + p.centerY
    else sy + (if isLeft then p.portLY else p.portRY)
  match ports, entryYs with
  | [p], [ey] =>
      -- a direct wire into a solid box must meet it ON AXIS (§12 item 11's
      -- wire-axis rule): entry at the box's vertical center, not merely
      -- within its edge; off-center entries take the bracket
      if decide ((ey - portY p).abs ≤ 0.25) then return (#[], [edgeX p])
      else pure ()
  | _, _ => pure ()
  let railX :=
    if isLeft then sx - busLeadF else sx + stackW + busLeadF
  let ys := ports.map portY ++ entryYs
  let top := ys.foldl min (ys.headD 0)
  let bot := ys.foldl max (ys.headD 0)
  let mut prims : Array Prim := #[vw top bot railX]
  for p in ports do
    prims := prims.push (hw railX (edgeX p) (portY p))
  return (prims, entryYs.map fun _ => railX)

/-! ### Row targeting (§12 item 30(a): the item-9a amendment)

`∥` is Jost's DISJOINT parallel composition (`par : … S I → … S J → … S (I ⊕ J)`),
so an interface of a stack is an interface of exactly ONE row and its
`Sum.inl`/`Sum.inr` prefix IS the path into the `∥` tree — the same path
`flattenParAt` walks.  A wire therefore knows the row it lands on, and item
9a's bus (a wire reaching every resource in the stack) asserts a reach the
term does not have. -/

/-- Peel the `Sum.inl`/`Sum.inr` prefix of a printed interface into
`flattenParAt`'s alphabet (`l`/`r`).  A `clip`-ellipsized name carries no
prefix we may trust, and answers `none`. -/
private partial def sumStepsGo (t : String) (acc : String) : String :=
  let t := t.trimAscii.toString
  let t := (if t.startsWith "(" then (t.drop 1).toString else t).trimAscii.toString
  if t.startsWith "Sum.inl" then sumStepsGo (t.drop 7).toString (acc.push 'l')
  else if t.startsWith "Sum.inr" then sumStepsGo (t.drop 7).toString (acc.push 'r')
  else acc

/-- The core row an interface names, when it names one: the row whose
`∥`-path is a prefix of the interface's own `Sum` path.  `none` is the
honest answer — a stack whose rows the term does not separate, an
ellipsized name, or an interface set an inner connection re-indexed. -/
private def targetRow (rowSteps : List String) (interface : String) :
    Option Nat :=
  if (interface.splitOn "…").length > 1 then none else
    let steps := sumStepsGo interface ""
    let hits := rowSteps.filter (fun r => steps.startsWith r)
    if hits.length == 1 then rowSteps.findIdx? (fun r => steps.startsWith r)
    else none

/-! ### The routing channel (§12 item 29)

Between a flank's converters and the core sits a CHANNEL: a band of
vertical TRACKS, one per bending wire, each wire turning exactly twice.
The track ORDER is what makes the routing non-crossing rather than
accidentally non-crossing.  Order the wires by entry height, matched to
targets in the same order (which the band discipline supplies); wire `i`
must turn further from the flank than wire `j` exactly when `j`'s entry lies
strictly inside `i`'s vertical span — otherwise `i` would have to dive
across `j`'s lead.  That relation is a strict partial order on an
order-preserving matching (a two-cycle would need `tᵢ > eⱼ` and `tⱼ < eᵢ`
at once, i.e. `tᵢ > eⱼ > eᵢ > tⱼ > tᵢ`), so ANY linear extension works and
the longest-chain rank is one. -/

/-- One wire through the channel: out of a flank chain at `entry`, into a
core row at `target`. -/
private structure Lead where
  entry : Float
  target : Float
  deriving Inhabited

/-- The track rank of each lead: the length of the longest chain
`i ▹ j ▹ …` under "`j`'s entry lies strictly inside `i`'s span".  A larger
rank turns further from the flank; equal ranks are incomparable and may
take neighbouring tracks in any order. -/
private def trackRanks (leads : Array Lead) : Array Nat := Id.run do
  let n := leads.size
  let covers := fun (i j : Nat) =>
    let a := leads[i]!
    let b := leads[j]!
    i != j && decide (min a.entry a.target + 0.25 < b.entry) &&
      decide (b.entry < max a.entry a.target - 0.25)
  let mut rank : Array Nat := Array.replicate n 1
  for _ in [0:n] do
    for i in [0:n] do
      for j in [0:n] do
        if covers i j && rank[i]! ≤ rank[j]! then
          rank := rank.set! i (rank[j]! + 1)
  return rank

/-- Lay the channel: each bending lead gets its own track, tracks ordered by
`trackRanks` (ties by index), the first `trackStepF` from the flank edge.
Returns the track x of each lead and the channel's width. -/
private def channelTracks (leads : Array Lead) (isLeft : Bool)
    (flankX : Float) : Array Float × Float := Id.run do
  let ranks := trackRanks leads
  let bending := (Array.range leads.size).filter fun i =>
    decide ((leads[i]!.entry - leads[i]!.target).abs > 0.25)
  -- Ties are FREE (equal rank = incomparable, and any linear extension of the
  -- rank order is planar), so spend them on legibility: among equal ranks the
  -- SHALLOWEST jog turns first.  A shallow jog is the one whose corner has the
  -- least vertical room, and putting it on the near track keeps it clear of
  -- the deeper leads' corners instead of stacking all the turns together.
  let travel := fun (i : Nat) => (leads[i]!.entry - leads[i]!.target).abs
  let order := bending.qsort fun i j =>
    ranks[i]! < ranks[j]! ||
      (ranks[i]! == ranks[j]! &&
        (decide (travel i < travel j) ||
          (decide (travel i == travel j) && i < j)))
  let mut xs : Array Float := Array.replicate leads.size flankX
  for slot in [0:order.size] do
    let d := leadInF + slot.toFloat * trackStepF
    xs := xs.set! order[slot]! (if isLeft then flankX + d else flankX - d)
  return (xs, leadInF + order.size.toFloat * trackStepF)

/-! ### D4 node addressing: the path alphabet

A **path** names a node of the shape tree — `inner` down an attachment's
carrier, `left`/`right` into a `∥`.  D3 addressed by a `Nat` spine depth,
which cannot name either child of a `∥`; a path can.  The emitter stamps
every addressable box with its path in the `class` attribute
(`cc-at-<path>`, alongside the unchanged `cc-box`), which is how the D4
panel (`Jost/SurfacePanel.lean`) finds the box a click landed on and where
to anchor its menu.  The wire format is deliberately tiny — `R` for the
root then one letter per step — because it is read back by a *different*
module; `SurfacePanel.Path.encode` is its inverse and the two are pinned
against each other there.  A box with NO `cc-at-` class is not
addressable (a fold-collapsed view node, whose path would name the wrong
subterm; the panel therefore refuses view directives). -/

/-- The root of a path: the whole term. -/
def nodeRoot : String := "R"

/-- Down an attachment's carrier (`α •[i] R ↦ R`). -/
def nodeInner (path : String) : String := path ++ "i"

/-- Into the left component of a `∥`. -/
def nodeLeft (path : String) : String := path ++ "l"

/-- Into the right component of a `∥`. -/
def nodeRight (path : String) : String := path ++ "r"

/-- The `class` of a box: always `cc-box` (the geometry audit's selector,
untouched), plus the D4 address when the box stands for an addressable
node.  An unaddressable box carries no `cc-at-` class at all. -/
private def boxCls (path : String) : String :=
  if path == "" then "cc-box" else s!"cc-box cc-at-{path}"

/-- An attach node peeled off the outer spine: the converters that flank
(or, for the simulator, hang below) the constructed system in Fig. 1.
`folded` marks a fold-collapsed serial run (composed name, deck marker);
`path` is its D4 address (empty when it has none). -/
structure SpineNode where
  converter : String
  interface : String
  role : Option Names.Role
  decl : Option Name
  folded : Bool := false
  /-- The interfaces a CONNECTION reaches (`α ••[γ] R`), empty for `•[i]`.
  TERM structure (`γ.first`, `γ.second`); never read for a row or a flank. -/
  reach : List String := []
  /-- The same interfaces in the BASE resource's coordinates
  (`Diagram.descendInterface`), `""` where a branch reaches none.  THIS is
  what targeting, geography and branch labels read. -/
  reachAt : List String := []
  path : String := ""
  deriving Inhabited

/-- Is this node the blocking converter?  Then the interface is FILTERED
and the picture draws its effect, not a symbol (§12 item 15). -/
def SpineNode.blocked (node : SpineNode) : Bool := node.converter == blockGlyph

/-- Does this node stand for a CONNECTION — a converter reaching more than
one interface at once (§12 item 28)? -/
def SpineNode.connects (node : SpineNode) : Bool := node.reach.length > 1

/-- **A connection's converter SPANS its reach** (Jost Fig. 2.1's tall
π_ε^A): the pill grows by one fork pitch per extra branch, so every branch
meets its inner edge with the ordinary pill margin above and below.  An
ordinary attachment keeps the fixed grid height exactly (§12 item 1). -/
def SpineNode.pillH (node : SpineNode) : Float :=
  pillHF + ((max node.reach.length 1) - 1).toFloat * connPitchF

/-- The offset of branch `k` of a connection from its converter's centre:
the fork ladder, symmetric about the centre by construction (§12 item 11a),
at the emitter's own `connPitchF`. -/
def SpineNode.forkOffset (node : SpineNode) (k : Nat) : Float :=
  let n := max node.reach.length 1
  (k.toFloat - (n - 1).toFloat / 2) * connPitchF

/-- Peel the outer attach spine from the core it converts, stamping each
node with its path from `path` (the node at depth `k` sits at
`path ++ "i"^k`). -/
def peelFrom (path : String) : Shape → List SpineNode × Shape
  | .attach conv ifc inner role decl reach reachAt _ _ folded =>
      let (spine, core) := peelFrom (nodeInner path) inner
      (⟨conv, ifc, role, decl, folded, reach, reachAt, path⟩ :: spine, core)
  | s => ([], s)

/-- Peel the outer attach spine from the core it converts. -/
def peel : Shape → List SpineNode × Shape := peelFrom nodeRoot

/-- Re-nest a spine onto a core — `peel`'s inverse (view transforms edit
the spine as a list, then rebuild). -/
def nest (spine : List SpineNode) (core : Shape) : Shape :=
  spine.foldr
    (fun nd acc => .attach nd.converter nd.interface acc nd.role nd.decl
      nd.reach nd.reachAt (folded := nd.folded))
    core

/-- Flatten a `∥` tree into the Fig.-1 stack. -/
partial def flattenPar : Shape → List Shape
  | .par l r _ => flattenPar l ++ flattenPar r
  | s => [s]

/-- Flatten a `∥` tree into the Fig.-1 stack, each row carrying its D4
path (`left`/`right` steps, in tree order). -/
partial def flattenParAt (path : String) : Shape → List (Shape × String)
  | .par l r _ =>
      flattenParAt (nodeLeft path) l ++ flattenParAt (nodeRight path) r
  | s => [(s, path)]

/-- Alternate a list onto the two flanks: 1st, 3rd, … left; 2nd, 4th, …
right — the outermost converter takes the left edge, MaRuTa12 Fig. 1's
`enc`-left / `dec`-right reading of `dec^B enc^A (KEY‖AUT)`.  This is
the FALLBACK when geography cannot classify the spine. -/
private def alternate : List SpineNode → List SpineNode × List SpineNode
  | [] => ([], [])
  | node :: rest =>
      let (right, left) := alternate rest
      (node :: left, right)

/-- The §12 flank split of a spine (items 2 and 14). -/
structure Geography where
  left : List SpineNode
  right : List SpineNode
  above : List SpineNode
  below : List SpineNode
  /-- `"classified"` — item 2's A/B geography, the n = 2 case;
  `"indexed"` — item 14's numbered party ladder; `"fallback"` — an
  unnameable interface, the only genuine failure.  Reported on the panel
  as `data-geography`. -/
  mode : String
  deriving Inhabited

/-- Split the spine by §12 geography.  A simulator-role node and an
E-interface node go below, an F-interface node above.  The party nodes
take item 2's flanks when every one of them is recognisably A- or B-side
(the n = 2 specialization) and otherwise the item-14 LADDER: every party
on the party flank, in spine order, one numbered slot each — an
unrecognised interface takes a slot, it never degrades the spine.  Only an
unnameable interface falls back to alternation. -/
def geography (spine : List SpineNode) : Geography :=
  let place := fun (nd : SpineNode) =>
    if nd.role == some .simulator then Flank.below
    else
      -- **A CONNECTION is placed by the interfaces it REACHES**, not by γ's
      -- own printed name (Jost Fig. 2.1: π_ε^A sits on A's flank and π_ε^B on
      -- B's, because that is where their feet are).  γ's name is not an
      -- interface and classifies to nothing but a numbered slot, which is why
      -- the eq.-(1) shape used to stack both connections on one flank.  Only
      -- when every branch agrees and agrees on a PAPER side: a γ with one foot
      -- on A and one on B belongs to neither and keeps its slot.
      match nd.reachAt with
      | [] => classifyInterface nd.interface
      | first :: rest =>
          let c := classifyInterface first
          if first != "" && (c == .left || c == .right) &&
              rest.all (fun s => s != "" && classifyInterface s == c) then c
          else classifyInterface nd.interface
  let above := spine.filter fun nd => place nd == .above
  let below := spine.filter fun nd => place nd == .below
  let parties := spine.filter fun nd =>
    place nd != .above && place nd != .below
  if parties.any (fun nd => place nd == .unnamed) then
    let (l, r) := alternate parties
    ⟨l, r, above, below, "fallback"⟩
  else if parties.all (fun nd => place nd == .left || place nd == .right) then
    ⟨parties.filter (fun nd => place nd == .left),
     parties.filter (fun nd => place nd == .right), above, below, "classified"⟩
  else
    ⟨parties, [], above, below, "indexed"⟩

/-- The worst geography met anywhere in a diagram: the panel reports the
weakest claim it can honestly make. -/
def worstMode (modes : List String) : String :=
  if modes.contains "fallback" then "fallback"
  else if modes.contains "indexed" then "indexed"
  else "classified"

/-! ### The boxes -/

/-- **§12 item 13: shape codes the KIND**, colour only reinforces it.  A
resource is a rectangle, a converter a rounded box (Jost Fig. 2.1 caption
p. 27; PorRen22 Fig. 4 caption p. 9) — and a SIMULATOR IS A CONVERTER
(PorRen22 §II.D.c p. 10), so it takes the rounded shape too and never an
ellipse; its dotted border is its non-colour twin, as small-caps is the
game's and the double outline the constructed system's.  Returns the
corner radius and the border style. -/
private def kindShape (role : Option Names.Role) : Float × String :=
  if role == some .simulator then (resHF / 2, "dotted")
  else if role == some .converter then (resHF / 2, "solid")
  else (2, "solid")

/-- A resource box: fixed grid size, kind coded by shape (item 13), role
color duplicated by a non-color signal (double outline = constructed,
small-caps = game), full label in `title`, middle-ellipsis at the
resource budget. -/
private def leafPic (label : String) (role : Option Names.Role)
    (path : String := "") : Pic :=
  let (radius, border) := kindShape role
  ⟨resWF, resHF, resHF / 2, resHF / 2, true,
    #[.box 0 0 resWF resHF radius (roleColor role) border
        (role == some .constructed) (role == some .game)
        (middleEllipsis resourceBudget label) label (boxCls path)]⟩

/-- A fold-collapsed box (D1/D2): looks EXACTLY like a normal leaf plus
the deck outline — abstraction, not elision.  `full` (the title) says
what it abbreviates. -/
private def foldPic (label : String) (role : Option Names.Role)
    (full : String) (path : String := "") : Pic :=
  let (radius, border) := kindShape role
  ⟨resWF, resHF, resHF / 2, resHF / 2, true,
    #[.deck 0 0 resWF resHF radius,
      .box 0 0 resWF resHF radius (roleColor role) border
        (role == some .constructed) (role == some .game)
        (middleEllipsis resourceBudget label) full (boxCls path)]⟩

/-- The connection marker on a converter pill (§12 item 28): `cc-conn-<n>`
says this box is the converter of a connection reaching `n` interfaces, and
is what the gallery's FORK audit keys on.  A class, not a new attribute:
the audit already reads class lists. -/
private def connCls (nd : SpineNode) : String :=
  if nd.connects then s!" cc-conn-{nd.reach.length}" else ""

/-- A converter pill: the papers' smallest, ROUNDED object (the shape is
the converter's non-color signal; the simulator's is a dotted border).
A folded run is ONE pill under its composed name, deck outline behind.
A CONNECTION's pill SPANS its reach (`nd.pillH`) — Jost Fig. 2.1's tall
π_ε^A, whose right edge carries one wire per interface reached. -/
private def pillPrims (nd : SpineNode) (x y : Float) : Array Prim :=
  let role := nd.role.orElse fun _ => some .converter
  let border := (kindShape role).2
  let h := nd.pillH
  let title :=
    if nd.connects then
      s!"{nd.converter} @ {nd.interface} ⟨{String.intercalate ", " nd.reach}⟩"
    else s!"{nd.converter} @ {nd.interface}"
  (if nd.folded then #[.deck x y pillWF h (pillHF / 2)] else #[]) ++
  #[.box x y pillWF h (pillHF / 2) (roleColor role) border false false
      (middleEllipsis converterBudget nd.converter)
      title
      -- a fold-collapsed run stands for SEVERAL term nodes, so its path
      -- would name the wrong subterm: it is deliberately unaddressable
      (boxCls (if nd.folded then "" else nd.path) ++ connCls nd)]

/-- The serial chain of one interface's converters: pills joined by
short wire segments, outermost first in list order (Maurer11 Fig. 4's
`π₂ π₁ R` — same-interface order is the monoid and must be visible).
Pills of unequal height (a connection spans, an ordinary attachment does
not) are CENTERED on the chain's axis, so the joining segments stay on it. -/
private def chainPic (nodes : List SpineNode) : Pic := Id.run do
  let h := nodes.foldl (fun a nd => max a nd.pillH) pillHF
  let mut prims : Array Prim := #[]
  let mut x : Float := 0
  for nd in nodes do
    if decide (x > 0) then
      prims := prims.push (hw (x - chainGapF) x (h / 2))
    prims := prims ++ pillPrims nd x ((h - nd.pillH) / 2)
    x := x + pillWF + chainGapF
  return ⟨x - chainGapF, h, h / 2, h / 2, true, prims⟩

/-- Group a flank's spine nodes by interface, first-occurrence row
order, outermost-first inside each group.  Same-interface converters
compose serially — the monoid, whose order must stay visible (Maurer11
Fig. 4's `π₂ π₁ R` reading) — while distinct interfaces commute
(`attachAt_comm`) and get their own rows. -/
private def groupByInterface (nodes : List SpineNode) :
    List (String × List SpineNode) :=
  nodes.foldl (init := []) fun acc nd =>
    if acc.any (fun g => g.1 == nd.interface) then
      acc.map fun g =>
        if g.1 == nd.interface then (g.1, g.2 ++ [nd]) else g
    else acc ++ [(nd.interface, [nd])]

/-- One row of a flank: the interface tag, the chain of converter pills
drawn for it, and whether the interface is FILTERED (§12 item 15 — a
blocked interface's wire stops without exiting the boundary; absence of
output IS the filter's rendering, so `⊣` is never drawn as a box). -/
private structure FlankRow where
  tag : String
  chain : Pic
  blocked : Bool
  /-- The interfaces the row's CORE-FACING converter reaches (§12 item 28);
  empty for an ordinary attachment.  One entry per branch is what the row
  contributes to the side wiring. -/
  reach : List String := []
  /-- The same, in the BASE resource's coordinates (`SpineNode.reachAt`) —
  what a branch's TARGET and LABEL are read from.  Same length as `reach`
  whenever the descent succeeded, `[]` when it did not. -/
  reachAt : List String := []
  /-- The D4 path of the row's core-facing converter — the identity of the
  FORK its branch labels belong to. -/
  forkId : String := ""
  y : Float := 0
  /-- The core ROW each branch lands on (§12 item 30(a)): one entry per
  branch, `none` where the term does not say which row — then the whole
  flank falls back to the stack bracket. -/
  targets : List (Option Nat) := []
  deriving Inhabited

/-- A flank group's drawable row: the blocking nodes drop out of the
chain and become the row's `blocked` flag.  The row's REACH is the
INNERMOST node's — the spine arrives outermost-first and it is the innermost
converter that faces the core, so it is the one whose fork the core-side
wiring draws.  Each branch is resolved to the core row it names, unless
`resolvable` says an inner connection has re-indexed this interface set. -/
private def flankRow (reverse : Bool) (rowSteps : List String)
    (resolvable : String → Bool) (group : String × List SpineNode) :
    FlankRow :=
  let nodes := group.2.filter (fun nd => !nd.blocked)
  let reach := (nodes.getLast?.map (·.reach)).getD []
  let reachAt := (nodes.getLast?.map (·.reachAt)).getD []
  let forkId := (nodes.getLast?.map (·.path)).getD group.1
  let nodes := if reverse then nodes.reverse else nodes
  { tag := group.1
    chain :=
      if nodes.isEmpty then ⟨0, pillHF, pillHF / 2, pillHF / 2, true, #[]⟩
      else chainPic nodes
    blocked := group.2.any (·.blocked)
    reach := reach
    reachAt := reachAt
    forkId := forkId
    targets :=
      -- A CONNECTION's branches are targeted from `reachAt` — the descended,
      -- base-resource reading — and NOT through `resolvable`: the descent is
      -- exactly what `resolvable` used to refuse to do, so a node outside an
      -- inner connection is now readable rather than merely honest about
      -- being unreadable (§12 item 28's scope (i), closed).  An ordinary
      -- attachment still goes through `resolvable`: its own index is not
      -- descended, so an inner connection still re-indexes it.
      if reach.length > 1 then
        if reachAt.length == reach.length then
          reachAt.map fun s => if s == "" then none else targetRow rowSteps s
        else reach.map fun _ => none
      else if resolvable group.1 then [targetRow rowSteps group.1]
      else [none] }

/-- The core row a flank row anchors to: the first it reaches.  Its whole
converter cluster lives in that row's BAND (§12 item 30). -/
private def FlankRow.anchor (r : FlankRow) : Option Nat :=
  (r.targets.filterMap id).min?

/-- Does the whole flank know which rows it lands on?  One `none` and the
side draws the stack bracket instead (§12 item 30(c)) — mixed granularity
in one flank cannot be drawn planar, because a bracket spans every band a
resolved wire would have to cross. -/
private def flankResolved (rows : List FlankRow) : Bool :=
  !rows.isEmpty && rows.all fun r => r.targets.all Option.isSome

/-- Deeper-than-one nesting collapses to a compound box.  A subterm D2
recognizes as a registered display-named constant renders as that name's
SOLID box plus the deck (abstraction has a name; the title records
`NAME := structure`).  Otherwise: neutral gray dashed with the deck, and
— per the corner-label migration (§12 item 12) — the summary label sits
at the TOP-LEFT CORNER like every dashed region's name, never centered;
the full structure rides in the `title`. -/
private def compoundPic (path : String) (s : Shape) : Pic :=
  match s with
  | .attach _ _ _ _ _ _ _ (some (nm, role)) _ _ =>
      foldPic nm role s!"{nm} := {summary s}" path
  | s =>
      let label :=
        match s with
        | .attach conv ifc .. =>
            s!"{middleEllipsis converterBudget conv}^{middleEllipsis
              interfaceBudget (lastComponent ifc)}(…)"
        | s => middleEllipsis resourceBudget (summary s)
      ⟨resWF, resHF, resHF / 2, resHF / 2, true,
        #[.deck 0 0 resWF resHF 2,
          .box 0 0 resWF resHF 2 "#888888" "dashed" false false
            "" (summary s) (boxCls path),
          .corner 8 6 label (summary s) "#888888"]⟩

/-- **Stamp a core row's own box** with `cc-row-<k>` — the handle the geometry
audit's TARGET check reads back: a lead stamped `data-target="k"` must
terminate on this element.  Only a box that IS the row (a leaf, a
fold-collapsed or anonymous compound) can carry it; a row drawn as an
unfolded REGION is a dashed frame with no single box, and is left unmarked —
the emitter then stamps no target on the leads landing there and the check
stays silent rather than wrong.  Returns whether it found one. -/
private def markRowBox (k : Nat) (p : Pic) : Pic × Bool := Id.run do
  let mut out : Array Prim := #[]
  let mut hit := false
  for pr in p.prims do
    match pr with
    | .box x y w h r c bs d sc l t cls =>
        if !hit && decide (x.abs ≤ 0.5) && decide (y.abs ≤ 0.5) &&
            decide ((w - p.w).abs ≤ 0.5) && decide ((h - p.h).abs ≤ 0.5) &&
            cls.startsWith "cc-box" then
          out := out.push (.box x y w h r c bs d sc l t s!"{cls} cc-row-{k}")
          hit := true
        else out := out.push pr
    | _ => out := out.push pr
  return ({ p with prims := out }, hit)

/-- The budget of a branch label (§12 item 1).  A branch of a connection is
labelled by a QUALIFIED interface — Jost printed p. 27, "we address a party's
interfaces by referring to the corresponding atomic resource's name, e.g.,
interface A of AuthChan" — so `AUT.a`, not `a`.  That is a different kind of
label from a bare interface tag and gets its own budget; six codepoints would
ellipsize every qualified name there is. -/
def branchBudget : Nat := 12

/-- The budget of a CONNECTION's own crossing label.  The wire a connection
produces is tagged with γ's NAME (`gammaAB`), which is not an interface
letter: metering it at the 6-codepoint interface budget was a category error
and is what printed `gam…AB`.  Tags are never clipped in pixels — `.cc-tag`
sets no width and no overflow — so the ellipsis was entirely the budget's
doing. -/
def connectionBudget : Nat := 10

/-- One wire leaving a flank chain for the core. -/
private structure FlankEntry where
  /-- Which flank row (chain) it leaves. -/
  row : Nat
  /-- Its height at the chain's inner edge. -/
  y : Float
  /-- A CONNECTION branch's interface label (§12 item 28); `none` for a
  plain attachment, whose name appears at its boundary crossing instead. -/
  label : Option String
  /-- The core row it lands on, `none` when the term does not say. -/
  target : Option Nat
  deriving Inhabited

/-- Lay out a constructed term in datum coordinates (core vertical
center at `y = 0`), then normalize.  Flank chains sit right/left-aligned
toward the core, one row per interface (§12 item 14: one converter box
per party, STACKED vertically, feeding the parallel resource stack —
BBM18 Fig. 4), each in the BAND of the core row it lands on (item 30);
the leads cross the channel as two-bend routes on their own tracks
(item 29), or, where the term does not name a row, land on the stack
BRACKET (item 30(c)); the perpendicular flanks hang one COLUMN per
interface below (E and the simulators) and above (Jost's free F, drawn
dotted per item 18); the dashed boundary wraps the content; interfaces
protrude through it as tagged crossings — except a FILTERED one, whose
wire stops inside without exiting (item 15).  Returns the pic and the
geography modes of this box and any nested ones. -/
private def layoutConstructed
    (layoutShape : String → Nat → Shape → Pic × List String)
    (path : String) (s : Shape) : Pic × List String := Id.run do
  let (spine, core) := peelFrom path s
  let geo := geography spine
  let corePath := spine.foldl (fun p _ => nodeInner p) path
  let coreRows := flattenParAt corePath core
  let rowSteps := coreRows.map fun (_, p) => (p.drop corePath.length).toString
  let nRows := coreRows.length
  let comps := coreRows.map (fun (c, p) => layoutShape p 1 c)
  let flags := comps.foldl (fun a c => a ++ c.2) ([] : List String)
  -- each row's own box gets `cc-row-<k>`, so a lead can name the box it is
  -- supposed to land on and the audit can check that it does
  let marks := (List.range nRows).map fun k => markRowBox k (comps[k]!).1
  let rowPics := marks.map (·.1)
  let rowMark := fun (t : Option Nat) =>
    match t with
    | some r => if (marks[r]?.map (·.2)).getD false then toString r else ""
    | none => ""
  -- the display name of each core row, for the branch labels below
  let rowNames := coreRows.map fun (c, _) =>
    match c with
    | .leaf l .. => l
    | .foldBox l _ _ => l
    | .region l _ _ => l
    | c => summary c
  -- An inner CONNECTION re-indexes the interface set (`attachAlong` lands in
  -- `rest ⊕ Unit`), so a node OUTSIDE one cannot be read against the core's
  -- rows: §12 item 28's honest scope (i), now decided rather than deferred.
  let indexOf := fun (p : SpineNode → Bool) => Id.run do
    let mut hit : Option Nat := none
    let mut i : Nat := 0
    for nd in spine do
      if p nd then hit := some i
      i := i + 1
    return hit
  let lastConn := indexOf (·.connects)
  let resolvable := fun (ifc : String) =>
    match lastConn, indexOf (·.interface == ifc) with
    | none, _ => true
    | some c, some d => d ≥ c
    | some _, none => false
  let mkRows := fun (rev : Bool) (nodes : List SpineNode) =>
    (groupByInterface nodes).map (flankRow rev rowSteps resolvable)
  let leftRes := flankResolved (mkRows false geo.left)
  let rightRes := flankResolved (mkRows true geo.right)
  -- §12 item 30(b): cross-interface order on a flank is FREE
  -- (`attachAt_comm` — item 9 already says so), so spend that freedom on
  -- planarity: order the rows by the core row they land on.
  let byTarget := fun (rs : List FlankRow) =>
    rs.mergeSort fun a b => (a.anchor.getD nRows) ≤ (b.anchor.getD nRows)
  let leftRows0 := if leftRes then byTarget (mkRows false geo.left)
    else mkRows false geo.left
  let rightRows0 := if rightRes then byTarget (mkRows true geo.right)
    else mkRows true geo.right
  -- The distinct core rows a flank row lands on.  An ordinary attachment
  -- names one; a CONNECTION's fork may SPAN several — Jost Fig. 2.1's π_ε^A
  -- reaches `Key` and `AuthChan` at once, and a band discipline that seats
  -- the whole cluster in ONE row's band cannot draw that.
  let spanOf := fun (x : FlankRow) =>
    (x.targets.filterMap id).foldl
      (fun acc t => if acc.contains t then acc else acc ++ [t]) []
  -- BANDS (§12 item 30): row `r`'s band must seat every converter cluster
  -- that lands on it, so the pills of one row can never reach into another
  -- row's wires.  A cluster that SPANS `m` rows books an `m`-th share of
  -- each — the bands it spans then total at least its height, gaps on top.
  let clusterH := fun (rs : List FlankRow) (r : Nat) =>
    let c := rs.filter fun x => (spanOf x).contains r
    if c.isEmpty then (0 : Float)
    else c.foldl (fun a x =>
        a + x.chain.h / (max (spanOf x).length 1).toFloat) 0 +
      (c.length - 1).toFloat * flankGapF
  let bandMin := (List.range nRows).map fun r =>
    max (if leftRes then clusterH leftRows0 r else 0)
      (if rightRes then clusterH rightRows0 r else 0)
  let (stackPic, ports) := stackRowsBands rowPics bandMin
  let coreTop := -(stackPic.h / 2)
  -- Placement: a resolved flank puts each cluster in its row's band; an
  -- unresolved one keeps the centred column it always had.  Row heights are
  -- NOT uniform — a connection's pill spans its fork (§12 item 28).
  let colH := fun (rows : List FlankRow) =>
    if rows.isEmpty then (0 : Float) else
      rows.foldl (fun a r => a + r.chain.h) 0 +
        (rows.length - 1).toFloat * flankGapF
  let stackAt := fun (rows : List FlankRow) => Id.run do
    let mut out : List FlankRow := []
    let mut y := -(colH rows / 2)
    for r in rows do
      out := out ++ [{ r with y := y }]
      y := y + r.chain.h + flankGapF
    return out
  -- The height a flank row WANTS its axis at: the mean of the axes of the
  -- rows it lands on.  For a single target that is the row's own axis, i.e.
  -- exactly the band-centred placement this replaces; for a fork spanning
  -- two rows it is the midpoint between them, which is what makes the two
  -- branches leave the pill symmetrically (Fig. 2.1's two level wires).
  let rowAxis := fun (t : Nat) => coreTop + (ports[t]!).centerY
  let desiredOf := fun (x : FlankRow) =>
    let ts := spanOf x
    if ts.isEmpty then coreTop + stackPic.h / 2
    else (ts.foldl (fun a t => a + rowAxis t) 0) / ts.length.toFloat
  let placeBands := fun (rs : List FlankRow) => Id.run do
    let mut out : List FlankRow := []
    for r in [0:nRows] do
      let c := rs.filter fun x => x.anchor == some r
      if c.isEmpty then continue
      let h := c.foldl (fun a x => a + x.chain.h) 0 +
        (c.length - 1).toFloat * flankGapF
      let mid := (c.foldl (fun a x => a + desiredOf x) 0) / c.length.toFloat
      let mut y := mid - h / 2
      for x in c do
        out := out ++ [{ x with y := y }]
        y := y + x.chain.h + flankGapF
    return out
  let leftRows := if leftRes then placeBands leftRows0 else stackAt leftRows0
  let rightRows := if rightRes then placeBands rightRows0 else stackAt rightRows0
  let leftW := leftRows.foldl (fun a r => max a r.chain.w) 0
  -- **The core-facing entries of a flank** (§12 item 28).  An ordinary row
  -- contributes ONE entry at its axis; a CONNECTION row contributes one per
  -- interface it reaches, at the fork ladder about that axis — Jost
  -- Fig. 2.1's π_ε^A, whose inner edge carries one wire per reach.
  let entriesOf := fun (rows : List FlankRow) => Id.run do
    let mut out : Array FlankEntry := #[]
    for k in [0:rows.length] do
      let r := rows[k]!
      let cy := r.y + r.chain.portL
      let n := r.targets.length
      if n ≤ 1 then out := out.push ⟨k, cy, none, r.targets.headD none⟩
      else
        for j in [0:n] do
          out := out.push
            ⟨k, cy + (j.toFloat - (n - 1).toFloat / 2) * connPitchF,
              -- the branch's own name is the BASE interface it reaches
              (match r.reachAt[j]? with
               | some s => if s == "" then r.reach[j]? else some s
               | none => r.reach[j]?),
              r.targets[j]!⟩
    return out
  let leftEntries := if leftRows.isEmpty then #[] else entriesOf leftRows
  let rightEntries := if rightRows.isEmpty then #[] else entriesOf rightRows
  -- The LEADS: the y a resolved entry must reach on its row's edge.  Rungs
  -- are handed out per row in entry order, so a row's port ladder is
  -- monotone in the entries' heights (§12 item 11a: still symmetric about
  -- the row centre, since `ladderOffset` is).
  let leadsOf := fun (isLeft : Bool) (entries : Array FlankEntry) => Id.run do
    let mut offs : Array (Array Float) := Array.replicate nRows #[]
    for e in entries do
      if let some t := e.target then
        offs := offs.set! t ((offs[t]!).push (e.y - (coreTop + (ports[t]!).centerY)))
    -- A row whose entries ALREADY form a symmetric ladder inside its edge
    -- keeps them as its rungs: the wires are then straight and a connection's
    -- fork reads exactly as Jost Fig. 2.1 draws it, two level wires off one
    -- tall pill.  Symmetric is item 11(a)'s own test, so this cannot weaken it.
    let matched := fun (t : Nat) =>
      let os := offs[t]!
      let lim := ((ports[t]!).height - 12) / 2
      os.size > 1 && os.all (fun d => decide (d.abs ≤ lim)) &&
        os.all fun d => os.any fun x => decide ((d + x).abs ≤ 0.5)
    let mut seen : Array Nat := Array.replicate nRows 0
    let mut out : Array Lead := #[]
    for e in entries do
      let t := e.target.getD 0
      let p := ports[t]!
      let k := seen[t]!
      seen := seen.set! t (k + 1)
      out := out.push ⟨e.y,
        if !p.solid then coreTop + (if isLeft then p.portLY else p.portRY)
        else if matched t then e.y
        else coreTop + p.centerY + ladderOffset p.height (offs[t]!).size k⟩
    return out
  let leftLeads := if leftRes then leadsOf true leftEntries else #[]
  let rightLeads := if rightRes then leadsOf false rightEntries else #[]
  -- the channel is as wide as its tracks; a flank carrying a CONNECTION
  -- needs a longer inner lead still, because each branch of the fork carries
  -- the name of the interface it reaches (§12 item 28)
  let channelW := fun (leads : Array Lead) =>
    leadInF + (leads.filter fun l =>
      decide ((l.entry - l.target).abs > 0.25)).size.toFloat * trackStepF
  let leadOf := fun (rows : List FlankRow) (leads : Array Lead) =>
    (if rows.any (fun r => r.reach.length > 1) then connLeadF else 0) +
      max coreLeadF (channelW leads)
  let coreSX := if leftRows.isEmpty then 0 else leftW + leadOf leftRows leftLeads
  let rightColX := coreSX + stackPic.w +
    (if rightRows.isEmpty then 0 else leadOf rightRows rightLeads)
  let mut prims : Array Prim := stackPic.prims.map (·.translate coreSX coreTop)
  let (busL, endsL) :=
    if leftRes then (#[], leftEntries.toList.map fun _ => leftW)
    else sideWiring true coreSX coreTop stackPic.w ports
      (if leftEntries.isEmpty then [0] else (leftEntries.map (·.y)).toList)
  let (busR, endsR) :=
    if rightRes then (#[], rightEntries.toList.map fun _ => rightColX)
    else sideWiring false coreSX coreTop stackPic.w ports
      (if rightEntries.isEmpty then [0] else (rightEntries.map (·.y)).toList)
  prims := prims ++ busL ++ busR
  -- inner leads are UNTAGGED: an interface tag appears exactly once per
  -- diagram, at its outermost visible point — the boundary crossing
  -- (§12 item 4, exact: labels at crossings, boxes near-empty).  The
  -- OUTER tip of each row is where the crossing (or, when filtered, the
  -- dead stub) starts.  A CONNECTION's branches are the one exception, and
  -- not a loosening of the rule: the interfaces γ reaches are CONSUMED by
  -- the converter and never cross the boundary, so the branch IS their
  -- outermost visible point (§12 item 28).
  let mut leftTips : List Float := []
  let mut rightTips : List Float := []
  let firstEntry := fun (entries : Array FlankEntry) (k : Nat) =>
    (entries.findIdx? (fun e => e.row == k)).getD 0
  let (leftTracks, _) := channelTracks leftLeads true leftW
  let (rightTracks, _) := channelTracks rightLeads false rightColX
  -- **A branch's label** (§12 item 28, Jost printed p. 27): "When considering
  -- a composed resource, such as [AuthChan, Key], then we address a party's
  -- interfaces by referring to the corresponding atomic resource's name,
  -- e.g., interface A of AuthChan."  So a branch of a fork is labelled by the
  -- interface QUALIFIED by the row it lands on — which is exactly the
  -- information the bare last component drops, and why the eq.-(1) shape drew
  -- `u` twice.  Two qualifications, in Jost's own order of preference: the
  -- atomic resource's NAME, and, when that name does not address (two rows
  -- drawn under the same one — `toyR ∥ toyR`), its POSITION.  A resource that
  -- is not composed addresses nothing, so a one-row core keeps the bare
  -- letter: the qualification is Jost's for composed resources only.
  let rowKey := fun (r : Nat) =>
    let nm := (rowNames[r]?).getD (toString (r + 1))
    if (rowNames.filter (· == nm)).length == 1 then nm else toString (r + 1)
  let branchTag := fun (reached : String) (t : Option Nat) =>
    match (if nRows ≤ 1 then none else t) with
    | some r =>
        (s!"{rowKey r}.{lastComponent reached}",
         s!"interface {lastComponent reached} of {rowKey r} ({reached})")
    | none => (lastComponent reached, reached)
  for j in [0:leftEntries.size] do
    let e := leftEntries[j]!
    let innerX := coreSX + (ports[e.target.getD 0]!).leftX
    let mut tagX := (leftW + (if leftRes then innerX else endsL[j]!)) / 2
    let mut tagY := e.y
    if leftRes then
      let l := leftLeads[j]!
      prims := prims ++ routeHVH leftW l.entry innerX l.target leftTracks[j]!
        (target := rowMark e.target)
      -- the label rides the segment that ARRIVES, not the one that leaves:
      -- at the entry height it floats off its own wire and next to another's
      tagX := (leftTracks[j]! + innerX) / 2
      tagY := l.target
    else if (leftRows[e.row]!).chain.w > 0 then
      -- the item-30(c) BRACKET path.  The stamp is carried here too, and
      -- deliberately: a branch whose interface DOES name a row and which is
      -- nevertheless drawn onto a rail that serves every row is precisely the
      -- eq.-(1) defect, and it must stay visible to the audit rather than
      -- disappear because the emitter declined to make a claim.
      prims := prims.push (hw leftW endsL[j]! e.y (target := rowMark e.target))
    if let some reached := e.label then
      let (text, title) := branchTag reached e.target
      prims := prims.push
        (.tag tagX tagY false (middleEllipsis branchBudget text) title
          (leftRows[e.row]!).forkId)
  for j in [0:rightEntries.size] do
    let e := rightEntries[j]!
    let innerX := coreSX + (ports[e.target.getD 0]!).rightX
    let mut tagX := (rightColX + (if rightRes then innerX else endsR[j]!)) / 2
    let mut tagY := e.y
    if rightRes then
      let l := rightLeads[j]!
      prims := prims ++ routeHVH rightColX l.entry innerX l.target rightTracks[j]!
        (target := rowMark e.target)
      tagX := (rightTracks[j]! + innerX) / 2
      tagY := l.target
    else if (rightRows[e.row]!).chain.w > 0 then
      prims := prims.push
        (hw endsR[j]! rightColX e.y (target := rowMark e.target))
    if let some reached := e.label then
      let (text, title) := branchTag reached e.target
      prims := prims.push
        (.tag tagX tagY false (middleEllipsis branchBudget text) title
          (rightRows[e.row]!).forkId)
  for k in [0:leftRows.length] do
    let r := leftRows[k]!
    if r.chain.w > 0 then
      prims := prims ++ r.chain.prims.map (·.translate (leftW - r.chain.w) r.y)
      leftTips := leftTips ++ [leftW - r.chain.w]
    else leftTips := leftTips ++
      [if leftRes then leftW else endsL[firstEntry leftEntries k]!]
  for k in [0:rightRows.length] do
    let r := rightRows[k]!
    if r.chain.w > 0 then
      prims := prims ++ r.chain.prims.map (·.translate rightColX r.y)
      rightTips := rightTips ++ [rightColX + r.chain.w]
    else rightTips := rightTips ++
      [if rightRes then rightColX else endsR[firstEntry rightEntries k]!]
  -- the perpendicular flanks: ONE COLUMN PER INTERFACE, side by side.
  -- Distinct interfaces are distinct wires, so a simulator never spans
  -- parties (§12 item 16); same-interface converters chain IN SERIES
  -- along the wire.  Each column leaves the core on its own rung of the
  -- cap ladder and jogs out to its column axis.
  let coreCX := coreSX + stackPic.w / 2
  let perpFlank := fun (groups : List (String × List SpineNode))
      (dir : Float) (dotted : Bool) => Id.run do
    let m := groups.length
    -- the cap ladder must fit the ROW the wires actually touch (rows are
    -- centred in the stack, so only the span differs)
    let touched := if dir > 0 then ports.getLast? else ports.head?
    let capSpan := (touched.map fun p => p.rightX - p.leftX).getD stackPic.w
    let mut ps : Array Prim := #[]
    let mut exits : List (Float × Float × Bool × String) := []
    for k in [0:m] do
      let g := groups[k]!
      let capX := coreCX + ladderOffset capSpan m k
      let colX := coreCX + (k.toFloat - (m - 1).toFloat / 2) * colPitchF
      let nodes := g.2.filter (fun nd => !nd.blocked)
      let dead := g.2.any (·.blocked) && nodes.isEmpty
      let y0 := if dir > 0 then coreTop + stackPic.h else coreTop
      -- the jog to the column axis is STAGGERED (§12 item 29): the outermost
      -- column turns first, so an inner column's drop can never cross an
      -- outer column's jog.  At m ≤ 2 every rank is 0 and nothing moves.
      let jogRank := (min k (m - 1 - k)).toFloat
      let mut y := y0 + dir * (dropLenF + jogRank * trackStepF)
      ps := ps.push (vw y0 y capX (if dead && m == 1 then "2" else "") dotted)
      if m > 1 then
        if capX != colX then ps := ps.push (hw capX colX y "" dotted)
        let y2 := y + dir * dropLenF
        ps := ps.push (vw y y2 colX (if dead then "2" else "") dotted)
        y := y2
      let ordered := if dir > 0 then nodes else nodes.reverse
      for j in [0:ordered.length] do
        if j > 0 then
          let yn := y + dir * chainGapF
          ps := ps.push (vw y yn colX "" dotted)
          y := yn
        let ph := ordered[j]!.pillH
        ps := ps ++ pillPrims ordered[j]! (colX - pillWF / 2)
          (if dir > 0 then y else y - ph)
        y := y + dir * ph
      -- a filtered column carries its label at the dead tip, INSIDE the
      -- boundary it never crosses (§12 item 15)
      if dead then
        ps := ps.push (.tag (colX + 5) ((y0 + y) / 2) true
          (middleEllipsis interfaceBudget (lastComponent g.1)) g.1)
      exits := exits ++ [(colX, y, dead, g.1)]
    return (ps, exits)
  let (belowPrims, belowExits) :=
    perpFlank (groupByInterface geo.below) 1 false
  let (abovePrims, aboveExits) :=
    perpFlank (groupByInterface geo.above) (-1) true
  prims := prims ++ belowPrims ++ abovePrims
  -- A FILTERED flank interface stops WITHOUT EXITING (§12 item 15), so
  -- its stub is drawn as CONTENT: the boundary then sits `padXF` beyond
  -- the dead tip and that padding IS the visible gap.  (Drawn after the
  -- boundary it would poke through — the frame-pad audit cannot see it,
  -- because content outside a frame is not that frame's content.)
  -- A row's own crossing label.  A CONNECTION's outer wire is tagged with
  -- γ's NAME, not with an interface letter, so it is metered at the
  -- connection budget (§12 item 1 keeps a budget per KIND of label — metering
  -- a γ-name at the 6-codepoint interface budget is what printed `gam…AB`).
  let crossText := fun (row : FlankRow) =>
    middleEllipsis
      (if row.reach.length > 1 then connectionBudget else interfaceBudget)
      (lastComponent row.tag)
  let stubTagAt := fun (x y : Float) (row : FlankRow) =>
    Prim.tag x (y - 3) false (crossText row) row.tag
  -- …and at a BOUNDARY crossing it is placed so its far edge clears the
  -- frame: centred on the stub when it fits there, pushed outward otherwise,
  -- so a long name never lies across the dashed line it labels.
  let stubTagOut := fun (isLeft : Bool) (edge x y : Float) (row : FlankRow) =>
    let half := (crossText row).length.toFloat * 6.2 / 2
    stubTagAt
      (if isLeft then min x (edge - 4 - half) else max x (edge + 4 + half)) y row
  for k in [0:leftRows.length] do
    let r := leftRows[k]!
    if r.blocked then
      let ey := r.y + r.chain.portL
      prims := prims.push (hw (leftTips[k]! - stubLenF) leftTips[k]! ey "1")
      prims := prims.push (stubTagAt (leftTips[k]! - stubLenF / 2) ey r)
  for k in [0:rightRows.length] do
    let r := rightRows[k]!
    if r.blocked then
      let ey := r.y + r.chain.portL
      prims := prims.push (hw rightTips[k]! (rightTips[k]! + stubLenF) ey "2")
      prims := prims.push (stubTagAt (rightTips[k]! + stubLenF / 2) ey r)
  -- the dashed boundary, UNDER the content so titles and crossings win;
  -- chrome (deck overhangs) never resizes it (§12 items 11-12)
  let (bx0, by0, bx1, by1) := contentBounds prims
  let rx0 := bx0 - padXF
  let ry0 := by0 - padYF
  let rx1 := bx1 + padXF
  let ry1 := by1 + padYF
  prims := #[Prim.box rx0 ry0 (rx1 - rx0) (ry1 - ry0) 4 "#888888" "dashed"
    false false "" (summary s) "cc-boundary"] ++ prims
  -- protruding party interfaces (tagged crossings; untagged when empty).
  -- A FILTERED interface takes no crossing: its wire already stopped.
  -- a row no spine node names keeps its own interfaces: it crosses the
  -- boundary at its axis, which is inside its BAND and therefore clear of
  -- every pill and every track (§12 item 30 — this stub is exactly what the
  -- band discipline buys, and it is why dropping item 9a's bus loses no row)
  let untouched := fun (isLeft : Bool) (entries : Array FlankEntry) =>
    (List.range nRows).filter fun r =>
      !entries.any (fun e => e.target == some r) &&
        (ports[r]!).solid && (if isLeft then true else true)
  if leftRows.isEmpty then
    prims := prims.push (hw (rx0 - stubLenF) endsL[0]! 0 "1")
  else
    for k in [0:leftRows.length] do
      let r := leftRows[k]!
      if !r.blocked then
        let ey := r.y + r.chain.portL
        prims := prims.push (hw (rx0 - stubLenF) leftTips[k]! ey "1")
        prims := prims.push (stubTagOut true rx0 (rx0 - stubLenF / 2) ey r)
    if leftRes then
      for r in untouched true leftEntries do
        prims := prims.push (hw (rx0 - stubLenF)
          (coreSX + (ports[r]!).leftX) (coreTop + (ports[r]!).centerY) "1")
  if rightRows.isEmpty then
    prims := prims.push (hw endsR[0]! (rx1 + stubLenF) 0 "2")
  else
    for k in [0:rightRows.length] do
      let r := rightRows[k]!
      if !r.blocked then
        let ey := r.y + r.chain.portL
        prims := prims.push (hw rightTips[k]! (rx1 + stubLenF) ey "2")
        prims := prims.push (stubTagOut false rx1 (rx1 + stubLenF / 2) ey r)
    if rightRes then
      for r in untouched false rightEntries do
        prims := prims.push (hw (coreSX + (ports[r]!).rightX)
          (rx1 + stubLenF) (coreTop + (ports[r]!).centerY) "2")
  -- the dangling perpendicular wires (Maurer11 Fig. 3), one per column,
  -- each carrying its OWN interface label; a filtered column has none
  for (colX, y, dead, tag) in belowExits do
    if !dead then
      prims := prims.push (vw y (ry1 + dangleLenF) colX "2")
      prims := prims.push (.tag (colX + 5) (ry1 + dangleLenF / 2) true
        (middleEllipsis interfaceBudget (lastComponent tag)) tag)
  for (colX, y, dead, tag) in aboveExits do
    if !dead then
      prims := prims.push (vw y (ry0 - dangleLenF) colX "2" true)
      prims := prims.push (.tag (colX + 5) (ry0 - dangleLenF / 2) true
        (middleEllipsis interfaceBudget (lastComponent tag)) tag)
  -- the side connection ports a parent stack may wire to: the first
  -- crossing's height (the untagged stub sits at the datum)
  let portOf := fun (rows : List FlankRow) =>
    match rows with
    | [] => (0 : Float)
    | r :: _ => r.y + r.chain.portL
  return (Pic.ofPrims prims (some (portOf leftRows)) (some (portOf rightRows))
    (solid := false), flags ++ [geo.mode])

/-- An unfold-expanded named region (D1d): the inner structure laid out
inside a dashed frame in the region's role color, the name at the
top-left corner (Maurer11's convention), side stubs crossing the frame.
A stack/leaf interior gets its own row wiring (like a bare `∥`); a
constructed interior arrives with boundary and stubs of its own and is
simply framed. -/
private partial def regionPic
    (layoutShape : String → Nat → Shape → Pic × List String)
    (path : String) (label : String) (role : Option Names.Role)
    (inner : Shape) : Pic × List String := Id.run do
  let color := roleColor role
  let frame := fun (content : Array Prim) (extra : Array Prim)
      (pL pR : Float) (flags : List String) => Id.run do
    let (bx0, by0, bx1, by1) := contentBounds content
    let (rx0, ry0, rx1, ry1) :=
      (bx0 - padXF, by0 - padYF, bx1 + padXF, by1 + padYF)
    let prims :=
      #[Prim.box rx0 ry0 (rx1 - rx0) (ry1 - ry0) 4 color "dashed"
          false false "" label "cc-boundary",
        Prim.corner (rx0 + 8) (ry0 + 6) label label color] ++
      content ++ extra
    return (Pic.ofPrims prims (some pL) (some pR) (solid := false), flags)
  match inner with
  | .attach .. =>
      -- a construction: full layout (its own boundary + crossings), framed
      let (ip, flags) := layoutShape path 0 inner
      frame ip.prims #[] ip.portL ip.portR flags
  | s =>
      -- a stack (or single box): rows, side wiring, stubs through the frame
      let comps := (flattenParAt path s).map (fun (c, p) => layoutShape p 1 c)
      let flags := comps.foldl (fun a c => a ++ c.2) ([] : List String)
      let (stackPic, ports) := stackRows (comps.map (·.1))
      let midY := stackPic.h / 2
      let (busL, xL) := sideWiring true 0 0 stackPic.w ports [midY]
      let (busR, xR) := sideWiring false 0 0 stackPic.w ports [midY]
      let content := stackPic.prims ++ busL ++ busR
      let (bx0, _, bx1, _) := contentBounds content
      let stubs :=
        #[hw (bx0 - padXF - stubLenF) xL[0]! midY "1",
          hw xR[0]! (bx1 + padXF + stubLenF) midY "2"]
      frame content stubs midY midY flags

/-- Recursive shape layout: leaves are boxes, one dashed nesting level
renders fully, a construction encountered deeper collapses to a compound
box; folded boxes and unfolded regions render at any depth (they are the
user's view state); a `∥` under `flattenPar` never reaches the `par` arm
(defensive stack without wires). -/
private partial def layoutShape : String → Nat → Shape → Pic × List String
  | path, _, .leaf label role _ _ => (leafPic label role path, [])
  | _, _, .foldBox label role original =>
      -- a fold-collapsed stack stands for several term nodes: unaddressable
      (foldPic label role s!"{label} = {summary original}", [])
  | path, _, .region label role inner =>
      regionPic layoutShape path label role inner
  | path, depth, .par l r e? =>
      let comps := (flattenParAt path (.par l r e?)).map
        (fun (c, p) => layoutShape p depth c)
      ((stackRows (comps.map (·.1))).1,
       comps.foldl (fun a c => a ++ c.2) [])
  | path, depth, s =>
      if depth ≥ 1 then (compoundPic path s, [])
      else layoutConstructed layoutShape path s

/-- Wrap a normalized pic in the `position: relative` container that
owns the coordinate system. -/
private def picHtml (pic : Pic) (flags : List String) : Html :=
  let attrs : Array (String × Json) :=
    #[("style", Json.mkObj
        [("position", "relative"),
         ("width", px (pic.w + 2 * diagMarginF)),
         ("height", px (pic.h + 2 * diagMarginF)),
         ("flex", "none"), ("margin", "4px")]),
      ("class", "cc-diagram")]
  let attrs :=
    if flags.isEmpty then attrs
    else attrs.push ("data-geography", worstMode flags)
  Html.element "div" attrs
    (pic.prims.map fun p => (p.translate diagMarginF diagMarginF).toHtml)

/-- The §12 layout, round 3: one positioned-coordinate container per
diagram.  A bare resource gets untagged interface stubs (no boundary is
crossed, so no label); a bare `∥` reads as ONE resource — per-row leads
into side buses with outward stubs; a converted term is
`layoutConstructed`.  Every wire endpoint lands on a box edge, a bus,
or a boundary crossing by construction. -/
partial def html (s : Shape) : Html :=
  match s with
  | .leaf label role _ _ =>
      let p := leafPic label role nodeRoot
      let y := p.h / 2
      picHtml (Pic.ofPrims (p.prims ++
        #[hw (-stubLenF) 0 y "1", hw p.w (p.w + stubLenF) y "2"])) []
  | .foldBox label role original =>
      let p := foldPic label role s!"{label} = {summary original}"
      let y := resHF / 2
      picHtml (Pic.ofPrims (p.prims ++
        #[hw (-stubLenF) 0 y "1", hw resWF (resWF + stubLenF) y "2"])) []
  | .region label role inner =>
      let (pic, flags) := regionPic layoutShape nodeRoot label role inner
      picHtml pic flags
  | .par .. => Id.run do
      let comps := (flattenParAt nodeRoot s).map
        (fun (c, p) => layoutShape p 0 c)
      let flags := comps.foldl (fun a c => a ++ c.2) ([] : List String)
      let (stackPic, ports) := stackRows (comps.map (·.1))
      let midY := stackPic.h / 2
      let (busL, xL) := sideWiring true 0 0 stackPic.w ports [midY]
      let (busR, xR) := sideWiring false 0 0 stackPic.w ports [midY]
      let prims := stackPic.prims ++ busL ++ busR ++
        #[hw (xL[0]! - parStubF) xL[0]! midY "1",
          hw xR[0]! (xR[0]! + parStubF) midY "2"]
      return picHtml (Pic.ofPrims prims) flags
  | s =>
      let (pic, flags) := layoutShape nodeRoot 0 s
      picHtml pic flags

/-- Fig.-3-style equation pair: two diagrams with the relation glyph
between (§12 item 6).

The pair WRAPS where it does not fit.  That is not a breach of "orientation
is semantic": the `≡` axis carries a RELATION between two systems, not
interface geography, so stacking the two sides preserves everything the
figure means — whereas rotating either diagram would move A, B, E and F. -/
def pairHtml (left : Html) (relation : String) (right : Html) : Html :=
  Html.element "div"
    #[("style", Json.mkObj
        [("display", "flex"), ("flexDirection", "row"),
         ("flexWrap", "wrap"), ("alignItems", "center"),
         ("justifyContent", "center"), ("maxWidth", "100%"),
         ("rowGap", "8px"), ("columnGap", "16px")])]
    #[left,
      Html.element "div"
        #[("style", Json.mkObj
            [("fontSize", "20px"),
             ("fontFamily", "'JetBrains Mono', ui-monospace, monospace"),
             ("flex", "none")])]
        #[Html.text relation],
      right]

/-! ### Named-subterm recognition (D2)

A folded or collapsed subterm that is definitionally a registered
`cc_display` constant takes that constant's name and role — the folded
diagram reads like the paper (`NET`, not an elision). -/

/-- Every declaration carrying `cc_display`, imported and local: the
recognition candidate pool (small — display names are curated). -/
private def displayCandidates (env : Environment) : Array (Name × String) :=
  Id.run do
  let mut out := (Names.displayAttr.ext.getState env).2.toList.toArray
  for i in [0:env.header.moduleData.size] do
    out := out ++ Names.displayAttr.ext.getModuleEntries env i
  return out

/-- Recognition is a convenience, never a cost centre: every candidate
comparison runs under its OWN heartbeat budget, and an overrun counts as
"no match" — a diagram must never be the reason an elaboration is slow. -/
private def recognitionHeartbeats : Nat := 400

/-- Is `e` definitionally a registered display-named constant (other than
itself)?  Type-gated first (reducible — this rejects almost every
candidate for free), then a heartbeat-bounded guarded `isDefEq`; any
failure or overrun counts as no. -/
def recognize? (e : Expr) : MetaM (Option (String × Option Names.Role)) := do
  let env ← getEnv
  let ty ← inferType e
  for (n, disp) in displayCandidates env do
    if e.isConstOf n then continue
    let matched ←
      try
        if !env.contains n then pure false else
        withCurrHeartbeats <|
          withTheReader Core.Context
            ({ · with maxHeartbeats := recognitionHeartbeats * 1000 }) do
          let c ← mkConstWithFreshMVarLevels n
          let cTy ← inferType c
          if !(← withReducible (isDefEqGuarded cTy ty)) then pure false
          else isDefEqGuarded c e
      catch _ => pure false
    if matched then return some (disp, Names.role? env n)
  return none

/-- Annotate the attach nodes that sit under a `∥` — exactly the ones the
layout can collapse to a compound box — with D2 recognition. -/
partial def annotateKnown (s : Shape) (underPar : Bool := false) :
    MetaM Shape := do
  match s with
  | .attach c i inner r d g ga k e? f =>
      let inner' ← annotateKnown inner false
      let k' ← match k, e?, underPar with
        | none, some e, true => recognize? e
        | k, _, _ => pure k
      return .attach c i inner' r d g ga k' e? f
  | .par l r e? =>
      return .par (← annotateKnown l true) (← annotateKnown r true) e?
  | .region lb ro inner =>
      return .region lb ro (← annotateKnown inner underPar)
  | s => return s

/-! ### View directives (D1): declarative fold/unfold -/

/-- A parsed view directive: `unfold N` δ-unfolds the named leaf into a
region; `fold c [as "S"]` collapses `c`'s same-interface serial runs on
the outer spine; `fold A ∥ B [as "S"]` collapses the matching stack into
a named box. -/
inductive ViewDir where
  | unfoldName (name : String)
  | foldConv (name : String) (as? : Option String)
  | foldStack (names : List String) (as? : Option String)

/-- Fold every maximal same-interface serial run of converters named
`name` on the outer spine into ONE node with the composed name
(`enc∘enc∘enc` — the pill ellipsizes it to `enc∘…enc` at the converter
budget; the receipt keeps it whole). -/
def foldConvRun (name : String) (as? : Option String) (s : Shape) :
    Shape := Id.run do
  let (spine, core) := peel s
  if !spine.any (·.converter == name) then return s
  let mut out : List SpineNode := []
  let mut done : List String := []
  for nd in spine do
    if nd.converter == name then
      if done.contains nd.interface then continue
      done := done ++ [nd.interface]
      let run := spine.filter fun m =>
        m.converter == name && m.interface == nd.interface
      if run.length == 1 then
        out := out ++ [{ nd with converter := as?.getD nd.converter, folded := as?.isSome }]
      else
        let composed := String.intercalate "∘" (run.map (·.converter))
        out := out ++ [{ nd with converter := as?.getD composed, folded := true, decl := none }]
    else out := out ++ [nd]
  return nest out core

/-- The leaf labels of a `∥` subtree, when every row is a leaf. -/
private def stackLabels (s : Shape) : Option (List String) :=
  (flattenPar s).mapM fun
    | .leaf label _ _ _ => some label
    | _ => none

/-- Fold the first `∥` node whose rows are exactly the named leaves into
a box.  D2 recognition runs either way: `as` overrides only the NAME, so
a recognized stack keeps its role colour under the user's alias (the role
describes the subterm, which `as` does not change).  Unrecognized and
unaliased, the box falls back to the `∥`-joined labels. -/
partial def foldStackAt (names : List String) (as? : Option String)
    (s : Shape) : MetaM Shape := do
  match s with
  | .par l r e? =>
      if stackLabels (.par l r e?) == some names then
        let rec? ← match e? with
          | some e => recognize? e
          | none => pure none
        let (nm, role) := rec?.getD (String.intercalate " ∥ " names, none)
        return .foldBox (as?.getD nm) role (.par l r e?)
      else
        return .par (← foldStackAt names as? l) (← foldStackAt names as? r) e?
  | .attach c i inner r d g ga k e? f =>
      return .attach c i (← foldStackAt names as? inner) r d g ga k e? f
  | .region lb ro inner =>
      return .region lb ro (← foldStackAt names as? inner)
  | s => return s

/-- Elaborated term → view-adjusted shape: `unfold`s feed `ofExpr`, folds
transform the tree, D2 annotation runs last. -/
def shapeWithDirs (e : Expr) (dirs : List ViewDir) : MetaM Shape := do
  let unfolds := dirs.filterMap fun
    | .unfoldName n => some n
    | _ => none
  let mut s ← ofExpr e unfolds
  for d in dirs do
    match d with
    | .foldConv n as? => s := foldConvRun n as? s
    | .foldStack ns as? => s ← foldStackAt ns as? s
    | .unfoldName _ => pure ()
  annotateKnown s

end Diagram

/-! ### The view-directive grammar

`#cc_diagram t with [fold …, unfold …]`.  Reservation-free: `fold`,
`unfold` and `as` are matched as NON-reserved words (`&"fold "`), so
importers keep all three as ordinary identifiers — the receipts at the
bottom of this file use them as `Nat`s.

The clause is introduced by `with` (already a core Lean token, so it
reserves nothing new) and not by a bare bracket: `#cc_diagram t [fold α]`
cannot mean the view clause, because `t [fold α]` is already a legal term
— an application of `t` to the list literal `[fold α]`, `fold` being an
ordinary identifier.  The term parser wins that race, so the bare form
would either need `fold` reserved (banned) or `t` clamped to `term:max`
(a surface regression: `#cc_diagram α •[i] R` would stop parsing).  `with`
is a token no term can continue into, so the split is unambiguous.

`behavior := both` is what makes the non-reserved words reachable AT ALL:
a `&"fold "` alternative is indexed in the category under the *token*
`fold`, while the input is lexed as an *identifier* (that is the whole
point of not reserving it).  `both` makes the category try the token
index for a leading identifier too. -/

declare_syntax_cat ccViewDir (behavior := both)

syntax (name := ccFoldDir)
  &"fold " ident (" ∥ " ident)* (&" as " str)? : ccViewDir
syntax (name := ccUnfoldDir) &"unfold " ident : ccViewDir

/-- Parse one view directive from its raw syntax. -/
def Diagram.parseViewDir (stx : Syntax) : CommandElabM Diagram.ViewDir := do
  if stx.isOfKind ``ccFoldDir then
    let first := stx[1].getId.toString
    let rest := stx[2].getArgs.map (fun t => t[1].getId.toString)
    let as? := if stx[3].isNone then none else stx[3][1].isStrLit?
    if rest.isEmpty then
      return .foldConv first as?
    else
      return .foldStack (first :: rest.toList) as?
  else if stx.isOfKind ``ccUnfoldDir then
    return .unfoldName stx[1].getId.toString
  else
    throwError "unknown view directive{indentD stx}"

/-- `#cc_diagram t`: log the ASCII composition diagram of `t` and show the
Fig.-2.1 HTML panel in the infoview.  Structure comes from the elaborated
term (head constants `∥` / `attach`); a plain resource renders as one box
under its own name.

The optional view clause `with [dir, …]` (D1) adjusts the projection —
never the term: `fold enc` collapses `enc`'s same-interface serial runs
to one deck-marked pill; `fold KEY ∥ AUT as "NET"` collapses the matching
stack to a named box (without `as`, D2 recognition supplies the name of a
definitionally-equal display-named constant); `unfold SEC` δ-unfolds the
named leaf into a corner-labelled dashed region.  Folded nodes print as
`▸`, regions as `◈`, in the receipt. -/
syntax (name := ccDiagramCmd) "#cc_diagram " term
  (" with " "[" ccViewDir,* "]")? : command

@[command_elab ccDiagramCmd] def elabCcDiagram : CommandElab := fun stx => do
  let t : TSyntax `term := ⟨stx[1]⟩
  let dirs ←
    if stx[2].isNone then pure []
    else stx[2][2].getSepArgs.toList.mapM Diagram.parseViewDir
  let shape ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    Diagram.shapeWithDirs (← instantiateMVars e) dirs
  logInfo (Diagram.ascii shape)
  let ht := Diagram.html shape
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← rpcEncode ht) }) stx

/-- The two shapes and the relation glyph of a (possibly ∀-bound)
equality or `≈[ε]` statement — shared by `#cc_diagram thm` and the
gallery generator.  View directives apply to BOTH sides: a fold is a
statement about the vocabulary, and an identity drawn with one side
folded and the other not would be a lie. -/
def Diagram.ofStatement? (type : Expr) (dirs : List Diagram.ViewDir := []) :
    MetaM (Option (Diagram.Shape × String × Diagram.Shape)) :=
  forallTelescope type fun _ body => do
    let args := body.getAppArgs
    match body.getAppFn with
    | .const n _ =>
        if n = ``Eq ∧ args.size ≥ 3 then
          return some (← Diagram.shapeWithDirs args[args.size - 2]! dirs, "≡",
            ← Diagram.shapeWithDirs args[args.size - 1]! dirs)
        else if n = ``RandomSystems.CC.ResourceSystem.close ∧ args.size ≥ 3 then
          let eps :=
            (toString (← ppExpr args[args.size - 3]!)).trimAscii.toString
          return some (← Diagram.shapeWithDirs args[args.size - 2]! dirs,
            s!"≈[{eps}]", ← Diagram.shapeWithDirs args[args.size - 1]! dirs)
        else return none
    | _ => return none

/-- `#cc_diagram thm Name`: render an equality or `≈[ε]` theorem as the
papers' figure pair — both sides drawn, the relation glyph between
(Maurer11 Fig. 3 top/bottom; §12 item 6).  The ASCII receipt stacks the
two structure trees around the glyph.  `thm` is a non-reserved word.  The
same `with [dir, …]` view clause applies, to BOTH sides at once. -/
syntax (name := ccDiagramThmCmd) (priority := high)
  "#cc_diagram " &"thm " ident (" with " "[" ccViewDir,* "]")? : command

@[command_elab ccDiagramThmCmd] def elabCcDiagramThm : CommandElab :=
    fun stx => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  let dirs ←
    if stx[3].isNone then pure []
    else stx[3][2].getSepArgs.toList.mapM Diagram.parseViewDir
  let (l, rel, r) ← liftTermElabM do
    let info ← getConstInfo declName
    match ← Diagram.ofStatement? info.type dirs with
    | some sides => pure sides
    | none => throwError
        "#cc_diagram thm expects an equality or ≈[ε] statement, got{indentExpr info.type}"
  logInfo s!"{Diagram.ascii l}\n{rel}\n{Diagram.ascii r}"
  let ht := Diagram.pairHtml (Diagram.html l) rel (Diagram.html r)
  liftCoreM <| Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return json% { html: $(← rpcEncode ht) }) stx

/-! ## Receipts -/

namespace WidgetTests

open BridgeDemo

/-- The counter of the bridge demo, as a *computable* realization (the
resource wrapper is noncomputable; the presentation is not — which is the
point of `#simulate`). -/
def simCounter : ctr.Realization where
  State := Nat
  init := 0
  step n query :=
    match query with
    | ⟨.user, .ping⟩ => some (n + 1, ())
    | ⟨.audit, .read⟩ => some (n, n)

instance : ∀ i, Repr (ctr.Out i) := fun i =>
  match i with
  | .user => (inferInstance : Repr Unit)
  | .audit => (inferInstance : Repr Nat)

/-- A one-shot variant: the second ping leaves the domain — the trace shows
the blocking `⊥` and stops. -/
def simOneShot : ctr.Realization where
  State := Bool
  init := false
  step used query :=
    match query with
    | ⟨.user, .ping⟩ => if used then none else some (true, ())
    | ⟨.audit, .read⟩ => some (used, (if used then 1 else 0 : Nat))

/-- info: .user ! .ping ↦ ()
.user ! .ping ↦ ()
.audit ! .read ↦ 2 -/
#guard_msgs in
#simulate simCounter on
  [(.user ! .ping : ctr.Query), (.user ! .ping : ctr.Query),
    (.audit ! .read : ctr.Query)]

/-- info: .user ! .ping ↦ ()
.user ! .ping ↦ ⊥  (outside the domain — simulation blocked) -/
#guard_msgs in
#simulate simOneShot on
  [(.user ! .ping : ctr.Query), (.user ! .ping : ctr.Query),
    (.audit ! .read : ctr.Query)]

/-- info: □ counterA -/
#guard_msgs in
#cc_diagram counterA

/-- info: ∥
  □ counterA
  □ counterA -/
#guard_msgs in
#cc_diagram twoCounters

/-- A minimal attach-shaped term for the diagram: an identity converter at
the counter's `user` interface (source service = target service). -/
noncomputable def attached :=
  ResourceAt.attach (S := ctr.services) (layout := ctr.selfLayout)
    CtrIface.user (Converter.ofMaps id id) rfl counterA

/-- info: ◠ Converter.ofMaps id id @ CtrIface.user
  □ counterA -/
#guard_msgs in
#cc_diagram attached

/-! ### Display names in goals and diagrams (the channel calculus) -/

open Channels

-- A channel displays as its glyph in goal/check output (guillemeted —
-- the identifier-lexer boundary; diagram labels below are clean).
/-- info: «•—→» : Resource (channelInterfaces Bool) -/
#guard_msgs in
#check authenticatedChannel Bool

-- Parallel channels diagram under their clean glyphs.
/-- info: ∥
  □ •—→
  □ •—→ -/
#guard_msgs in
#cc_diagram (authenticatedChannel Bool ∥ authenticatedChannel Bool)

-- The shared key's glyph.
/-- info: □ •══• -/
#guard_msgs in
#cc_diagram (sharedKey Bool)

-- A constructed/ideal resource gets the ◆ sigil (red in the HTML panel,
-- per Maurer11's palette).
@[cc_display "SEC", cc_role constructed]
noncomputable def secDemo : Resource ctr := counterA

/-- info: ◆ SEC -/
#guard_msgs in
#cc_diagram secDemo

-- D1: `ofExpr` stops at a display-named head (the name IS the paper
-- object); an `unfold` directive overrides that for THAT leaf, which
-- becomes a corner-labelled dashed region with its content inside.
/-- info: ◈ SEC
  □ counterA -/
#guard_msgs in
#cc_diagram secDemo with [unfold SEC]

/-! ### The bundled carrier and the algebra in diagrams (parts 4–5) -/

section CarrierDiagrams

open CarrierDemo AlgebraDemo
open scoped Converter ResourceSystem

-- The eq.-(1) shape: converters flanking a parallel composition
-- (`decB ••[γ^B] encA ••[γ^A] (toyR ∥ toyR)`) — in the HTML panel this is
-- the dashed Fig.-1 box, the toys stacked, and each converter FORKED onto
-- the two interfaces its connection reaches (§12 item 28, Jost Fig. 2.1's
-- π_ε^A).  The receipt records that reach in `⟨…⟩`: it is term structure
-- (`γ.first`, `γ.second`), so the structure twin owes it a line.  The merge
-- underneath is still never drawn, because the author never writes it.
/-- info: ◠ decB @ gammaV ⟨Sum.inl Comp.key, Sum.inl Comp.aut⟩
  ◠ encA @ gammaU ⟨Sum.inl Party.u, Sum.inr Party.u⟩
    ∥
      □ toyR
      □ toyR -/
#guard_msgs in
#cc_diagram CarrierDemo.constructedShape

-- Blocking draws as the `⊣` converter at its interface.
/-- info: ◠ ⊣ @ Party3.e
  □ toy3 -/
#guard_msgs in
#cc_diagram (⊣[Party3.e] toy3)

-- A `Σ`-word acting by `•`: the interface is read off the scalar's type;
-- an embedded single converter is labelled by the converter itself.
/-- info: ◠ mask @ Party.u
  □ toyR -/
#guard_msgs in
#cc_diagram (Converter.word mask Party.u • toyR)

-- The React path of the positioned renderer, live in the infoview
-- (the gallery serializes this very tree for the browser audit):
#html Diagram.html (Diagram.Shape.leaf "toyR" (some .assumed) none)

/-! ### `#cc_diagram thm`: equation pairs (§12 item 6) -/

-- The grammar-vs-twin identity as a figure pair.
/-- info: □ Counter
≡
□ twin -/
#guard_msgs in
#cc_diagram thm GrammarTests.counter_eq_twin

/-- Exact closeness, for the `≈[ε]` face of the pair renderer. -/
theorem toyClose : toyR ≈[(0 : ℝ)] toyR :=
  (ResourceSystem.close_zero_iff _ _).mpr rfl

/-- info: □ toyR
≈[0]
□ toyR -/
#guard_msgs in
#cc_diagram thm toyClose

/-! ### The fixed grid never stretches (§12 item 1) -/

-- The label policy is a render-layer concern: the ASCII receipt keeps the
-- full (clip-38) label, the HTML box ellipsizes at its budget.
/-- info: middle-ellipsis: TheAbs…Width -/
#guard_msgs in
#eval IO.println
  s!"middle-ellipsis: {Diagram.middleEllipsis Diagram.resourceBudget
    "TheAbsurdlyLongResourceNameThatUsedToStretchTheEntireDiagramWidth"}"

-- Geography (§12 items 2 and 14): the four PAPER interfaces to their
-- paper places — A left, B right, E below, Jost's free F above — and any
-- other NAME to a numbered party slot (`geography` fixes the index from
-- the spine order).  Only a printed form that is not a name at all
-- (`partyOf 0`, or a `clip`-ellipsized expression) is `unnamed`, and that
-- alone is the fallback.
/-- info: [RandomSystems.CC.Diagram.Flank.left,
 RandomSystems.CC.Diagram.Flank.right,
 RandomSystems.CC.Diagram.Flank.below,
 RandomSystems.CC.Diagram.Flank.above,
 RandomSystems.CC.Diagram.Flank.party 0,
 RandomSystems.CC.Diagram.Flank.unnamed,
 RandomSystems.CC.Diagram.Flank.unnamed] -/
#guard_msgs in
#eval [Diagram.classifyInterface "Party.u", Diagram.classifyInterface "Party.v",
  Diagram.classifyInterface "Party3.e", Diagram.classifyInterface "Iface.F",
  Diagram.classifyInterface "CtrIface.user",
  Diagram.classifyInterface "Iface.partyOf 0",
  Diagram.classifyInterface "Iface.someVeryLongInterfaceExpressi…tail"]

end CarrierDiagrams

/-! ### `on`, `fold`, `unfold`, `as` are not reserved

The `#simulate` and view-clause grammars match their words with
`&"…"` (non-reserved), so importers (and this very file) keep all four as
plain identifiers. -/

def on : Nat := 1
def fold : Nat := 2
def unfold : Nat := 3
def as : Nat := 4

example : on + fold + unfold + as = 10 := rfl

end WidgetTests

end RandomSystems.CC
