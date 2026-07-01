/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Explanation
import Informalization.Grammar
import Informalization.Ontology

/-!
# `FTL` — the Formal Theory Language layer (DESIGN §3)

A typed, **emit-only** Formal Theory Language (ForTheL stance, §3.1) plus a total
realizer to `Explanation`. This is *not* a parser: nothing in the Lean → prose
direction needs to parse. We provide

* the statement ADT (`FStatement`) — mirroring ForTheL statement forms
  (Let / For-all / iff / implies / atom);
* the proof-step ADT (`FStep` over `Frame`) — mirroring the Verbose/cnl-rs proof
  frames shared with §6.4 (Since / By / We conclude / It suffices / Assume / Fix);
* a total, pure **realizer** `FStatement/FStep/FDocument → Explanation`.

Per §3.1 the realizer does *not* reinvent article/plural/merge logic: surface
realization of introductions goes through the grammar engine
(`Grammar.realizeIntros` — GF-RGL feature realization + Reiter–Dale aggregation).
Each realized piece reports the fidelity `Tier` it achieved (DESIGN §3.3):
structured FTL frames are `Tier.structured`, the carrier sentence is
`Tier.fallback`.

`realizeStep` recurses over `FStep.children : Array FStep` (a `⊕`-expandable
sub-proof). The nested `Array` recursion is written with `partial def` — the
project's accepted convention for total realizers (the data is finite; partiality
here is a checker convenience, not a semantic gap).
-/

namespace Informalization.FTL

open Informalization
open Informalization.Grammar

/-! ## Statement FTL (DESIGN §3.1) -/

/-- A formal-theory statement, mirroring ForTheL statement forms. `atom` is a bare
typeset proposition carrying optional provenance (the `Expr` it was rendered from,
§3.2). -/
inductive FStatement where
  /-- "Let X, … be a …" — surface-realized through the grammar engine. -/
  | lets (intros : List Grammar.Intro)
  /-- "For all …, <body>." -/
  | forAll (intros : List Grammar.Intro) (body : FStatement)
  /-- "<lhs> if and only if <rhs>." -/
  | iff (lhs rhs : FStatement)
  /-- "if <lhs> then <rhs>." -/
  | implies (lhs rhs : FStatement)
  /-- A bare proposition, typeset as math, with optional provenance. -/
  | atom (latex : String) (prov : Option Prov := none)
  deriving Inhabited

/-! ## Proof FTL (DESIGN §3.1, §6.4) -/

/-- How load-bearing a proof step is, driving the renderer's expansion budget
(DESIGN §8). -/
inductive Salience
  | pivotal
  | routine
  deriving DecidableEq, Repr, Inhabited

/-- The reasoning moves of a proof step (the cnl-rs/Verbose frames shared with
§6.4). Strings are LaTeX fragments. -/
inductive Frame where
  /-- "Since <facts>, we get <concl>." -/
  | since (facts : Array String) (concl : String)
  /-- "By <lemma> applied to <arg>, we get <concl>." -/
  | byApplied (lemma_ arg concl : String)
  /-- "We conclude <concl> by <facts>." -/
  | weConclude (concl : String) (facts : Array String)
  /-- "It suffices to show <goal>." -/
  | itSuffices (goal : String)
  /-- "Assume <h>." -/
  | assume (h : String)
  /-- "Fix <vars>." -/
  | fix (vars : Array String)
  /-- "Let <vars> be elements of <ty>." — a typed introduction of variables. -/
  | letElems (vars : Array String) (ty : String)
  /-- **Verbatim author prose**: a sequence of segments, each `(isMath, s)` — `s`
  is rendered as inline math when `isMath`, else as plain text. This is the
  free-form escape hatch for reproducing source text exactly (e.g. CR18's own
  sentence shapes), outside the controlled frame vocabulary. Tier `natural`. -/
  | prose (parts : Array (Bool × String))
  /-- Tier-0 carrier sentence: a verbatim LaTeX fallback. -/
  | fallback (latex : String)
  deriving Inhabited

/-- The fidelity tier a frame realizes (DESIGN §3.3). The structured frames are
`Tier.structured`; the carrier sentence is `Tier.fallback`. (Noun-lexicon-driven
`Tier.natural` frames are a future addition; none here reach it yet.) -/
def Frame.tier : Frame → Tier
  | .since _ _      => .structured
  | .byApplied _ _ _ => .structured
  | .weConclude _ _  => .structured
  | .itSuffices _    => .structured
  | .assume _        => .structured
  | .fix _           => .structured
  | .letElems _ _    => .structured
  | .prose _         => .natural
  | .fallback _      => .fallback

/-- One proof step: a reasoning `frame`, its `salience`, an optional `goal` state
to surface on hover, and a sub-proof (`children`) for `⊕` expansion. -/
structure FStep where
  frame : Frame
  salience : Salience := .routine
  goal : Option GoalState := none
  children : Array FStep := #[]
  deriving Inhabited

/-! ## Document -/

/-- A formal-theory document: a `title`, the theorem `statement`, and the proof as
an array of top-level steps. -/
structure FDocument where
  title : String
  statement : FStatement
  proof : Array FStep
  deriving Inhabited

/-! ## Realizers (total, pure)

All realizers emit inert `Explanation` data. Introductions are surface-realized by
the grammar engine; we never reimplement article/plural/merge logic here. -/

/-- Realize a statement into an `Explanation`. Introductions go through
`Grammar.realizeIntros` (GF-RGL + Reiter–Dale); `atom` becomes a provenance-carrying
math leaf. -/
def realizeStatement : FStatement → Explanation
  | .lets intros => .text (Grammar.realizeIntros intros)
  | .forAll intros body =>
      .concat #[
        .text ("For all " ++ Grammar.realizeIntros intros ++ ", "),
        realizeStatement body ]
  | .iff lhs rhs =>
      .concat #[ realizeStatement lhs, .text " if and only if ", realizeStatement rhs ]
  -- A theorem in "Let …  Then …" form (introductions, then the conclusion).
  | .implies (.lets intros) rhs =>
      .concat #[ .text (Grammar.realizeIntros intros ++ " Then "),
                 realizeStatement rhs, .text "." ]
  | .implies lhs rhs =>
      .concat #[ .text "if ", realizeStatement lhs, .text " then ", realizeStatement rhs ]
  | .atom latex prov => .math latex prov

/-- Realize one proof `Frame` into a sentence (a `concat` of text/math leaves), per
the phrasebook of §6.4. Fact lists are joined with `Grammar.joinAnd`. -/
def realizeFrame : Frame → Explanation
  | .since facts concl =>
      -- "Since <facts>, <proposition>." — no "we get"; the math is asserted as
      -- a clause, not handed over as a bare object.
      .concat #[
        .text ("Since " ++ Grammar.joinAnd facts.toList ++ ", "),
        .math concl,
        .text "." ]
  | .byApplied lemma_ arg concl =>
      let appliedTo : Array Explanation :=
        if arg.isEmpty then #[] else #[.text " applied to ", .math arg]
      .concat ((#[(.text "By " : Explanation), .math lemma_] ++ appliedTo)
        ++ #[.text ", ", .math concl, .text "."])
  | .weConclude concl facts =>
      .concat #[
        .text "We conclude ", .math concl,
        .text (" by " ++ Grammar.joinAnd facts.toList ++ ".") ]
  | .itSuffices goal =>
      .concat #[ .text "It suffices to show ", .math goal, .text "." ]
  | .assume h =>
      .concat #[ .text "Assume ", .math h, .text "." ]
  | .fix vars =>
      .concat #[ .text ("Fix " ++ Grammar.joinAnd vars.toList ++ ".") ]
  | .letElems vars ty =>
      .concat #[ .text ("Let " ++ Grammar.joinAnd vars.toList ++ " be elements of "),
                 .math ty, .text "." ]
  | .prose parts =>
      .concat (parts.map (fun p => if p.1 then Explanation.math p.2 else Explanation.text p.2))
  | .fallback s =>
      -- a citation we couldn't decompile: render as TEXT (never typeset tactic
      -- syntax as math), woven into a sentence.
      .concat #[ .text "By ", .text s, .text ", the goal follows." ]

/-- A one-line gist of a frame, used as the collapsed summary when a step has an
expandable sub-proof. -/
def Frame.gist : Frame → String
  | .since _ concl       => "Since …, " ++ concl
  | .byApplied l _ concl => "By " ++ l ++ ", " ++ concl
  | .weConclude concl _  => "We conclude " ++ concl
  | .itSuffices goal     => "It suffices: " ++ goal
  | .assume h            => "Assume " ++ h
  | .fix vars            => "Fix " ++ String.intercalate ", " vars.toList
  | .letElems vars _     => "Let " ++ String.intercalate ", " vars.toList ++ " be given"
  | .prose parts         => String.intercalate "" (parts.toList.filterMap (fun p => if p.1 then none else some p.2))
  | .fallback latex      => latex

/-- Realize a proof step. The frame sentence is rendered, the goal state (if any)
attached as a hover `tooltip`, and a nonempty sub-proof wrapped in a `detail` node
(collapsed gist + `⊕`; expanded = indented realized children). The `detail`'s
`salient` flag tracks the step's salience so the expansion budget can show pivotal
subtrees first (DESIGN §8). `partial` for the nested `Array FStep` recursion. -/
partial def realizeStep (step : FStep) : Explanation :=
  let sentence := realizeFrame step.frame
  -- attach the goal state on hover, if present
  let anchored :=
    match step.goal with
    | some g => Explanation.tooltip sentence (Explanation.goalState g)
    | none   => sentence
  if step.children.isEmpty then
    anchored
  else
    -- The sentence stays visible; the `detail` carries only the ⊕ toggle and the
    -- indented sub-proof. Each sub-step is its own block so they don't run together.
    let kids := step.children.map (fun c => Explanation.paragraph #[realizeStep c])
    let expanded := Explanation.indent (Explanation.concat kids)
    Explanation.concat #[
      anchored,
      Explanation.text " ",
      Explanation.detail (Explanation.text "") expanded (salient := step.salience == .pivotal) ]

/-- Realize a whole document: the statement as one paragraph, then the proof as a
"Proof. …" paragraph of realized steps. (The `title` is handled by the JSON
wrapper, DESIGN §4G.) -/
def realizeDocument (doc : FDocument) : Explanation :=
  let stmtPara := Explanation.paragraph #[ realizeStatement doc.statement ]
  -- the "Theorem." / "Proof." labels are added by the renderer's CSS so they can
  -- be styled; each top-level proof step is its own block so they read as a list.
  let stepParas := doc.proof.map (fun s => Explanation.paragraph #[ realizeStep s ])
  -- QED marker (Kyle's habit: every proof signs off)
  let qed := Explanation.paragraph #[ Explanation.text "∎" ]
  Explanation.concat (#[stmtPara] ++ stepParas ++ #[qed])

end Informalization.FTL

/-! ## Tests -/

section FTLTests
open Informalization
open Informalization.FTL

private def tyIntro (n : String) : Grammar.Intro :=
  { name := n, nounSingular := "type", nounPlural := "types" }

-- A `lets` of three same-shape intros realizes (via the grammar engine) to the
-- merged, Oxford-comma sentence.
/-- info: "Let α, β and γ be types." -/
#guard_msgs in
#eval match realizeStatement (.lets [tyIntro "α", tyIntro "β", tyIntro "γ"]) with
  | .text s => s
  | _ => "<not text>"

-- A `since` frame realizes to a concat sentence (text "Since …, we get " + math + ".").
#guard (realizeFrame (.since #["h₁", "h₂"] "P x")).size == 4

-- Frame tiers: structured frames vs the carrier sentence.
#guard (Frame.since #[] "x").tier == Tier.structured
#guard (Frame.fallback "t").tier == Tier.fallback

-- A leaf step (no children) realizes to its bare frame sentence (a `concat`),
-- not a `detail`.
private def leafStep : FStep := { frame := .assume "x = y" }
#guard (match realizeStep leafStep with | .detail _ _ _ => false | _ => true)

-- A step WITH children stays a visible sentence followed by a `detail` node
-- (the ⊕ toggle + indented sub-proof), marked salient when pivotal.
private def parentStep : FStep :=
  { frame := .itSuffices "P x"
    salience := .pivotal
    children := #[ { frame := .assume "h" }, { frame := .since #["h"] "P x" } ] }
#guard (match realizeStep parentStep with
  | .concat xs => match xs.back? with
                  | some (.detail _ _ salient) => salient
                  | _ => false
  | _ => false)

-- A goal-state on a step is attached as a hover tooltip.
private def goalStep : FStep :=
  { frame := .fix #["x"]
    goal := some { hyps := #[], goal := "P x" } }
#guard (match realizeStep goalStep with | .tooltip _ _ => true | _ => false)

-- A whole document realizes to a concat of one statement block + one block per
-- proof step (so steps read as a list, not a run-on paragraph).
private def demoDoc : FDocument :=
  { title := "demo"
    statement := .lets [tyIntro "α"]
    proof := #[ leafStep, parentStep ] }
-- one statement block + one block per step + a QED block
#guard (match realizeDocument demoDoc with
        | .concat xs => xs.size == 2 + demoDoc.proof.size | _ => false)

end FTLTests
