/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Explanation

/-!
# `Explanation → Verso slide markup`

The bridge that makes **Verso the host for our informalization text** (DESIGN:
presentation layer). Pure `String` emission — no Verso/`import Lean` dependency,
so it stays in the `v4.29.0` core. The slide project (`slides/`, on Verso's
toolchain) pastes / includes the emitted markup inside a `:::frame`.

Node → Verso mapping (the VersoSlides genre):
* `text`        → escaped prose
* `math`        → inline math `` $`…` ``
* `displayMath` → display math `` $$`…` ``
* `paragraph`   → blank-line-separated block
* `indent`      → a nested `:::frame … :::` (proof sub-block)
* `detail`      → summary, then the expansion in a `:::fragment` (reveal on click
                  — Verso's presentation analogue of show-hidden-detail)
* `clickable`   → label, then reveal in a `:::fragment`
* `tooltip`     → the anchor, then the goal-state in a `:::fragment` (proof state
                  summoned on demand)
* `goalState`   → a framed block listing hypotheses and the goal after `⊢`
-/

namespace Informalization

/-- Escape the few Verso-significant characters in literal prose. -/
def escapeVerso (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '*'  => "\\*"
      | '_'  => "\\_"
      | '`'  => "\\`"
      | '$'  => "\\$"
      | '['  => "\\["
      | ']'  => "\\]"
      | other => other.toString)

/-- Render a goal-state as a small framed block (hypotheses, then `⊢ goal`). -/
def GoalState.toVerso (g : GoalState) : String :=
  let hyps := g.hyps.foldl (init := "") fun acc h =>
    acc ++ "* " ++ escapeVerso h.name ++
      (if h.type.trim.isEmpty then "" else " : $`" ++ h.type ++ "`") ++ "\n"
  ":::frame\n" ++ hyps ++ "\n$`\\vdash` $`" ++ g.goal ++ "`\n:::\n"

/-- Emit an `Explanation` as VersoSlides markup. `partial` for the nested
`Array Explanation` recursion (finite data). -/
partial def Explanation.toVerso : Explanation → String
  | .text s            => escapeVerso s
  | .math l _          => "$`" ++ l ++ "`"
  | .displayMath l _   => "\n$$`" ++ l ++ "`\n"
  | .concat xs         => xs.foldl (fun acc x => acc ++ x.toVerso) ""
  | .paragraph xs      => (xs.foldl (fun acc x => acc ++ x.toVerso) "") ++ "\n\n"
  | .indent b          => b.toVerso
  | .detail s e _      => s.toVerso ++ infExpander e
  | .clickable a b     => a.toVerso ++ infExpander b
  | .tooltip a (.goalState g) => a.toVerso ++ infExpander (.goalState g)
  | .tooltip a h       => a.toVerso ++ infExpander h
  | .goalState g       => GoalState.toVerso g
where
  /-- In-place ⊕ expander: a clickable `⊕` that unfolds a hidden block (the
  standalone renderer's show-hidden-detail). Wired by the deck's toggle JS. -/
  infExpander (e : Explanation) : String :=
    " {class \"inf-toggle\"}[⊕]\n\n:::class \"inf-hidden\"\n" ++ e.toVerso ++ "\n:::\n"

/-- Wrap emitted markup as a full one-slide VersoSlides document fragment with a
heading (for splicing into a deck). -/
def Explanation.toVersoSlide (title : String) (e : Explanation) : String :=
  "# " ++ title ++ "\n\n" ++ e.toVerso

end Informalization

section VersoEmitTests
open Informalization

-- inline math + text emit as Verso markup
#guard (Explanation.concat #[.text "Since ", .math "g", .text " is injective, ", .math "f\\,a = f\\,b", .text "."]).toVerso
        == "Since $`g` is injective, $`f\\,a = f\\,b`."
-- a detail becomes an in-place ⊕ expander (clickable, unfolds in place)
#guard (Explanation.detail (.text "summary") (.text "hidden")).toVerso
        == "summary {class \"inf-toggle\"}[⊕]\n\n:::class \"inf-hidden\"\nhidden\n:::\n"
-- escaping protects Verso-significant characters
#guard escapeVerso "a*b_c" == "a\\*b\\_c"

end VersoEmitTests
