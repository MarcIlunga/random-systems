/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization

/-! Describer-path demo (Describe → FTL → Grammar → Serialize): a clean,
self-contained statement — *reducibility is transitive* — run through the
tactic-describers. All notation in words; the two hypotheses live in the hover
goal-state, and the single step cites transitivity (no circular "it suffices",
no leaked Lean). -/

open Informalization

private def hyp (n t : String) (c : Bool := false) : Hyp := ⟨n, t, c⟩
private def gstate (hs : Array Hyp) (g : String) : GoalState := ⟨hs, g⟩

private def problem (n : String) : Grammar.Intro :=
  { name := n, nounSingular := "problem", nounPlural := "problems" }

-- Hypotheses first, conclusion last: not circular, unambiguous scoping.
private def statement : FTL.FStatement :=
  .implies (.lets [problem "p", problem "q", problem "r"])
    (.atom "\\text{the reduction of } q \\text{ to } r \\text{ and the reduction of } r \\text{ to } p \\text{ compose to a reduction of } q \\text{ to } p")

-- One clean step: cite transitivity; the two hypotheses sit in the goal-state.
private def proofTree : Describe.ProofTree :=
  { kind := .apply, syntaxStr := "composition", args := #["composing the reduction of q to r with the reduction of r to p"],
    goalBefore := some (gstate
      #[ hyp "q reduces to r" "", hyp "r reduces to p" "" ]
      "q \\text{ reduces to } p") }

private def doc : FTL.FDocument :=
  { title := "Reducibility is transitive", statement,
    proof := #[Describe.describeTree proofTree] }

#eval do
  let expl := FTL.realizeDocument doc
  let json := Lean.Json.mkObj [("title", Lean.Json.str doc.title), ("body", expl.toJson)]
  IO.println json.pretty
