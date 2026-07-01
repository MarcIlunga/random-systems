/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization

/-! Verbatim-faithful informalization of **CR18 Lemma 4.5** (Composition of
Reductions), Maurer, *Cryptography Foundations*, §4.4.8. The two "Composing both
sides …" sentences are reproduced in CR18's own words via the verbatim `prose`
frame; the closing sentence uses the systematic `weConclude` frame ("We conclude
… by combining the two inequalities", CR18: "Combining the two inequalities
yields …"). No invented terminology. -/

open Informalization

private def hyp (n t : String) (c : Bool := false) : Hyp := ⟨n, t, c⟩
private def gstate (hs : Array Hyp) (g : String) : GoalState := ⟨hs, g⟩

private def prob (n : String) : Grammar.Intro :=
  { name := n, nounSingular := "problem", nounPlural := "problems" }
private def red (n : String) : Grammar.Intro :=
  -- CR18: ρ is the solver-transformation (the *inequality* is the reduction), so
  -- naming ρ a "reduction" would be a terminology drift. ρ : Σ_p → Σ_q.
  { name := n, nounSingular := "solver-transformation", nounPlural := "solver-transformations" }
private def lerf (n : String) : Grammar.Intro :=
  { name := n, nounSingular := "function", nounPlural := "functions",
    adjectives := ["≤-respecting"] }

private def statement : FTL.FStatement :=
  .implies (.lets [prob "p", prob "q", prob "r", red "ρ", red "ρ'", lerf "τ", lerf "τ'"])
    (.atom "\\tau p \\le q \\rho \\,\\wedge\\, \\tau' q \\le r \\rho' \\;\\Rightarrow\\; \\tau' \\tau p \\le r \\rho' \\rho")

private def proof : Array FTL.FStep := #[
  -- CR18 sentence 1 (verbatim wording), with the goal-state as context on hover.
  { frame := .prose #[
      (false, "Composing both sides of "), (true, "\\tau p \\le q \\rho"),
      (false, " with the ≤-respecting function "), (true, "\\tau'"),
      (false, " on the left side results in "), (true, "\\tau' \\tau p \\le \\tau' q \\rho"),
      (false, ", since "), (true, "\\tau'"), (false, " is ≤-respecting.") ],
    salience := .pivotal,
    goal := some (gstate #[ hyp "τ p ≤ q ρ" "", hyp "τ' is ≤-respecting" "" ]
      "\\tau' \\tau p \\le \\tau' q \\rho") },
  -- CR18 sentence 2 (verbatim wording).
  { frame := .prose #[
      (false, "Composing both sides of "), (true, "\\tau' q \\le r \\rho'"),
      (false, " with "), (true, "\\rho"),
      (false, " on the right side results in "), (true, "\\tau' q \\rho \\le r \\rho' \\rho"),
      (false, ".") ],
    salience := .pivotal,
    goal := some (gstate #[ hyp "τ' q ≤ r ρ'" "" ] "\\tau' q \\rho \\le r \\rho' \\rho") },
  -- CR18 sentence 3, via the systematic frame (≈ "Combining … yields …").
  { frame := .weConclude "\\tau' \\tau p \\le r \\rho' \\rho" #["combining the two inequalities"],
    salience := .pivotal } ]

private def doc : FTL.FDocument :=
  { title := "CR18 Lemma 4.5 — Composition of reductions", statement, proof }

#eval do
  let expl := FTL.realizeDocument doc
  let json := Lean.Json.mkObj [("title", Lean.Json.str doc.title), ("body", expl.toJson)]
  IO.println json.pretty
