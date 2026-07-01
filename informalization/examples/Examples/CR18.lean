/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization

/-! Informalization of a REAL, already-proven CR18 theorem:
`RandomSystems.CR18.CausalApply.winProb_apply` — CR18 §4.7.2 (4.9)/(4.10),
proven sorry-free in random-systems/RandomSystems/CR18/ReductionByConverter.lean.
The proof mirrors that Lean proof and threads line-to-line: expand the goal's LHS,
push the game pushforward back along c, expand the RHS the same way, reduce to a
per-winner identity, and close by the reduction equality (4.9). -/

open Informalization

private def hyp (n t : String) (c : Bool := false) : Hyp := ⟨n, t, c⟩
private def gstate (hs : Array Hyp) (g : String) : GoalState := ⟨hs, g⟩

private def converter : Grammar.Intro :=
  { name := "c", nounSingular := "converter", nounPlural := "converters" }
private def winnerDist : Grammar.Intro :=
  { name := "W", nounSingular := "distribution over winning conditions",
    nounPlural := "distributions over winning conditions" }
private def gameDist : Grammar.Intro :=
  { name := "G", nounSingular := "distribution over games",
    nounPlural := "distributions over games" }

private def statement : FTL.FStatement :=
  .implies (.lets [converter, winnerDist, gameDist])
    (.atom "\\omega(W, c \\cdot G) = \\omega(W^c, G)")

private def topGoal : GoalState :=
  gstate #[ hyp "c" "\\text{a converter}",
            hyp "W" "\\text{a distribution over winning conditions}",
            hyp "G" "\\text{a distribution over games}" ]
    "\\omega(W, c \\cdot G) = \\omega(W^c, G)"

private def proof : Array FTL.FStep := #[
  -- 1. expand the LHS by definition (⟦w g⟧ = 1 when winner w beats game g)
  { frame := .since #["by definition the winning probability is a weighted sum, with ⟦w g⟧ = 1 exactly when the winning condition w beats game g"]
      "\\omega(W, c \\cdot G) = \\sum_w W(w) \\sum_g (c \\cdot G)(g)\\,⟦w\\,g⟧",
    salience := .pivotal, goal := some topGoal },
  -- 2. push the game pushforward c·G back along c (the inner per-w rewrite)
  { frame := .since #["the pushforward c·G pulls the game-sum back along c"]
      "\\sum_g (c \\cdot G)(g)\\,⟦w\\,g⟧ = \\sum_g G(g)\\,⟦w\\,(c\\,g)⟧",
    salience := .routine,
    goal := some (gstate #[hyp "w" "\\text{a winning condition}" true]
      "\\sum_g (c \\cdot G)(g)\\,⟦w\\,g⟧ = \\sum_g G(g)\\,⟦w\\,(c\\,g)⟧"),
    children := #[
      { frame := .since #["the summand vanishes when a weight is zero"] "0 \\cdot x = 0" },
      { frame := .since #["the summand is additive in the weight"]
          "(a + b) \\cdot x = a \\cdot x + b \\cdot x" } ] },
  -- 3. expand the RHS: the reduced winner Wᶜ pushes forward the same way
  { frame := .since #["the reduced winner W^c pushes forward along c in the same way"]
      "\\omega(W^c, G) = \\sum_w W(w) \\sum_g G(g)\\,⟦(w \\circ c)\\,g⟧",
    salience := .routine },
  -- 4. so both sides agree iff, for each w, the two inner sums agree
  { frame := .itSuffices
      "\\sum_g G(g)\\,⟦w\\,(c\\,g)⟧ = \\sum_g G(g)\\,⟦(w \\circ c)\\,g⟧ \\text{ for each } w",
    salience := .routine },
  -- 5. close by the reduction equality (4.9), which is definitional
  { frame := .weConclude "\\omega(W, c \\cdot G) = \\omega(W^c, G)"
      #["the reduction equality (w∘c) g = w (c g), which holds by definition of the reduction ρ^c (CR18 4.9)"],
    salience := .pivotal } ]

private def doc : FTL.FDocument :=
  { title := "CR18 §4.7.2 — Reduction by a converter", statement, proof }

#eval do
  let expl := FTL.realizeDocument doc
  let json := Lean.Json.mkObj [("title", Lean.Json.str doc.title), ("body", expl.toJson)]
  IO.println json.pretty
