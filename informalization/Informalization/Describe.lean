/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Explanation
import Informalization.FTL

/-!
# `Describe` — the proof-describer framework (DESIGN §7)

A symbolic (GOFAI) describer that turns a typed `ProofTree` into an `FTL.FStep`
tree. It operates over an **abstract** `ProofTree` ADT, *not* over live Lean
`InfoTree`s: the `InfoTree → ProofTree` ingestion is a separate module (the
"re-parenting" seam of §7). Here the algebra over the already-built tree is fully
implemented.

A `Describer` is `ProofTree → Option FTL.FStep`: `none` means "inapplicable"
(mirroring `throwInapplicableDescriber`). A registry tries describers in priority
order, falling back to a **total** Tier-0 describer that always yields a
`Frame.fallback` carrier sentence — so every node yields *some* not-wrong step
(§7's totality guarantee).

Salience policy (DESIGN §8): a node is `.pivotal` when it splits or transforms the
goal (`constructor`, `refine`), else `.routine`. The renderer's expansion budget
shows pivotal steps first.

The **decompiler seam** (`decompile`) — real proof-term decompilation for the
`exact/apply/refine` family — is left as future work and returns `none` here.
-/

namespace Informalization.Describe

open Informalization

/-! ## The `ProofTree` ADT (DESIGN §7) -/

/-- The closed tactic set the describers recognize. `term` is term-mode; `other`
carries an unrecognized tactic name for the fallback path. -/
inductive TacticKind
  | intro | exact | apply | refine | constructor | term | other (name : String)
  deriving Repr, Inhabited, BEq

/-- A true, re-parented proof tree: side goals are already attached to their
parent as `children`. Each node records the tactic `kind`, its source text
(`syntaxStr`), the optional goal it ran against (`goalBefore`), the `args` it used
(lemma/hyp/var names), and its sub-steps. -/
structure ProofTree where
  kind : TacticKind
  syntaxStr : String
  goalBefore : Option GoalState := none
  args : Array String := #[]
  children : Array ProofTree := #[]
  deriving Inhabited

/-! ## Describers

A `Describer` is `ProofTree → Option FTL.FStep`; `none` ⇒ inapplicable. The
concrete describers below are deliberately simple and string-based: they read
`kind` and `args`, never inspecting Lean terms. -/

/-- The describer type: returns `some` when applicable, `none` to defer to the
next describer (mirrors `throwInapplicableDescriber`). -/
abbrev Describer := ProofTree → Option FTL.FStep

/-- Strip a leading tactic keyword so a fallback cites the lemma, not the tactic
("exact reduction_comp_left" → "reduction_comp_left"). -/
def citeOf (s : String) : String :=
  match s.splitOn " " with
  | kw :: rest =>
    if rest.isEmpty then s
    else if kw ∈ ["exact", "apply", "refine", "rw", "rewrite", "simp", "exact?", "calc"] then
      String.intercalate " " rest
    else s
  | [] => s

/-- The **fallback describer** (Tier 0): TOTAL — it always produces a
`Frame.fallback` carrier sentence from the node's source text (with any leading
tactic keyword stripped), so every node yields some (not-wrong) step. -/
def fallbackDescriber (t : ProofTree) : FTL.FStep :=
  { frame := .fallback (citeOf t.syntaxStr)
    salience := .routine
    goal := t.goalBefore }

/-- `intro x …` ⇒ "Fix x …" (`Frame.fix` over the introduced vars). Routine. -/
def introDescriber : Describer := fun t =>
  match t.kind with
  | .intro => some { frame := .fix t.args, salience := .routine, goal := t.goalBefore }
  | _      => none

/-- `exact h` ⇒ "Since h, we get <goal>." (`Frame.since`) when a hypothesis/lemma
name is supplied; inapplicable otherwise. Routine. -/
def exactDescriber : Describer := fun t =>
  match t.kind with
  | .exact =>
    match t.args[0]? with
    | some name =>
      let concl := match t.goalBefore with | some g => g.goal | none => "the goal"
      some { frame := .since #[name] concl, salience := .routine, goal := t.goalBefore }
    | none => none
  | _ => none

/-- `constructor` ⇒ "It suffices to show <goal>." (`Frame.itSuffices`): it splits a
goal into sub-goals, so it is **pivotal**. -/
def constructorDescriber : Describer := fun t =>
  match t.kind with
  | .constructor =>
    let goal := match t.goalBefore with | some g => g.goal | none => "the components"
    some { frame := .itSuffices goal, salience := .pivotal, goal := t.goalBefore }
  | _ => none

/-- `apply lem` ⇒ "By lem applied to …, we get <goal>." (`Frame.byApplied`).
Routine (a straight backward application, not a goal split). -/
def applyDescriber : Describer := fun t =>
  match t.kind with
  | .apply =>
    let lemma_ := t.args[0]?.getD t.syntaxStr
    let arg := t.args[1]?.getD ""
    let concl := match t.goalBefore with | some g => g.goal | none => "the goal"
    some { frame := .byApplied lemma_ arg concl, salience := .routine, goal := t.goalBefore }
  | _ => none

/-- `refine e` ⇒ "By e applied to …, we get <goal>." (`Frame.byApplied`). Refine
restructures the goal into holes, so it is **pivotal**. -/
def refineDescriber : Describer := fun t =>
  match t.kind with
  | .refine =>
    let lemma_ := t.args[0]?.getD t.syntaxStr
    let arg := t.args[1]?.getD ""
    let concl := match t.goalBefore with | some g => g.goal | none => "the goal"
    some { frame := .byApplied lemma_ arg concl, salience := .pivotal, goal := t.goalBefore }
  | _ => none

/-! ## Registry + dispatch -/

/-- The describer registry, in priority order. The first describer returning
`some` wins; `describe` appends the total `fallbackDescriber` behind them. -/
def registry : Array Describer :=
  #[ introDescriber
   , constructorDescriber
   , refineDescriber
   , applyDescriber
   , exactDescriber ]

/-- Describe one node: the first describer in `registry` that returns `some`,
else the total `fallbackDescriber`. The node's `goalBefore` is attached as the
produced step's `goal` (every concrete describer already does this; we re-attach
for safety so dispatch is the single source of truth). -/
def describe (t : ProofTree) : FTL.FStep :=
  let step := match registry.findSome? (fun d => d t) with
    | some s => s
    | none   => fallbackDescriber t
  { step with goal := t.goalBefore }

/-- Recursively describe a whole tree: describe the node, then describe each child
and hang them off the produced step's `children`. `partial` because the recursion
is nested inside `Array.map` over `children` (the data is finite; partiality here
is a checker convenience, matching `FTL.realizeStep`'s accepted convention). -/
partial def describeTree (t : ProofTree) : FTL.FStep :=
  let here := describe t
  -- A goal-SPLITTING step (constructor/refine/apply with sub-goals) must reduce
  -- to its sub-goals — "it suffices to show A and B" — NOT restate the current
  -- goal as its conclusion (which reads circularly). Build the sub-goal list
  -- from the children's own goals.
  let splits := t.kind == .constructor || t.kind == .refine || t.kind == .apply
  let subgoals := t.children.filterMap (fun c => c.goalBefore.map (·.goal))
  let here2 :=
    if splits && subgoals.size ≥ 1 then
      { here with frame := .itSuffices (String.intercalate " \\text{ and } " subgoals.toList) }
    else here
  { here2 with children := t.children.map describeTree }

/-! ## Decompiler seam (DESIGN §7)

Real proof-term decompilation (the `exact/apply/refine` family — turning a `Term`
into a sequence of synthesized tactic steps) is future work. The seam is typed and
total; it always declines. -/

/-- Seam: real proof-term decompilation is future work. Always returns `none`. -/
def decompile (_termSyntax : String) : Option (Array String) := none

end Informalization.Describe

/-! ## Tests -/

section DescribeTests
open Informalization
open Informalization.Describe

private def introNode : ProofTree :=
  { kind := .intro, syntaxStr := "intro x y", args := #["x", "y"]
    goalBefore := some { hyps := #[], goal := "P x" } }

-- An `intro` node describes to a `Frame.fix` step.
#guard (match describe introNode with
  | { frame := .fix vs, .. } => vs == #["x", "y"]
  | _ => false)

-- A `constructor` node is pivotal (it splits the goal).
private def ctorNode : ProofTree :=
  { kind := .constructor, syntaxStr := "constructor"
    goalBefore := some { hyps := #[], goal := "A ∧ B" } }
#guard (match describe ctorNode with
  | { frame := .itSuffices _, salience := .pivotal, .. } => true
  | _ => false)

-- An unknown tactic falls back to the Tier-0 carrier sentence.
private def unknownNode : ProofTree :=
  { kind := .other "omega", syntaxStr := "omega" }
#guard (match describe unknownNode with
  | { frame := .fallback s, .. } => s == "omega"
  | _ => false)

-- `exact h` produces a `Frame.since` citing the hypothesis.
private def exactNode : ProofTree :=
  { kind := .exact, syntaxStr := "exact h", args := #["h"]
    goalBefore := some { hyps := #[], goal := "P x" } }
#guard (match describe exactNode with
  | { frame := .since facts _, .. } => facts == #["h"]
  | _ => false)

-- `describeTree` on a 2-level tree produces nested children.
private def twoLevel : ProofTree :=
  { kind := .constructor, syntaxStr := "constructor"
    goalBefore := some { hyps := #[], goal := "A ∧ B" }
    children := #[ introNode, exactNode ] }
#guard (describeTree twoLevel).children.size == 2

-- The describer attaches the node's goal state to the produced step.
#guard (match (describe introNode).goal with
  | some g => g.goal == "P x"
  | none   => false)

-- The decompiler seam declines.
#guard (decompile "fun x => f x").isNone

end DescribeTests
