/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfaceWidgets
import RandomSystems.Jost.SurfaceGrammar

/-!
# The authoring surface, part 7: `#cc_latex` — the paper-equation exporter

`#cc_latex t` emits the LaTeX of a composition term or statement, the way
the papers typeset it; `#cc_latex thm Name` renders a (possibly ∀-bound)
equality or closeness theorem's statement.  The walk is the SAME
head-constant analysis as `#cc_diagram` (`Diagram.ofExpr`) — one shape,
two projections — so the diagram and the equation can never disagree
about structure.

The dictionary:

* a named object emits its `@[cc_latex "…"]` form, falling back to
  `\mathsf{<display name>}`;
* attachment `α •[i] R` (and a `Converters`-word acting by `•`) is the
  superscript `\mathsf{α}^{i}`, interfaces shortened to their last name
  component (`Party.u` is `u` on paper);
* `∥` is `\|`, flat across associations;
* `⊣[i]` is `\dashv^{i}`;
* `≈[ε]` is `\approx_{ε}` (`\varepsilon` when the radius is a variable
  so named);
* `=` is `\equiv` — deliberately: Maurer's `≡` (identical behavior) IS
  this library's `=` on the behavioral carrier (`close_zero_iff`), so the
  paper glyph for our equality is `\equiv`.

Parenthesization only where the papers demand it: an attachment
parenthesizes a `∥` operand (Maurer11's `dec^B enc^A (KEY \| AUT)`);
attachment chains juxtapose with thin space; `∥` chains stay flat.

Roles can color the equation as in Maurer11 eqs. (1)–(2):
`#cc_latex (color := true) t` wraps each named object in
`\textcolor[HTML]{…}` using the diagram palette.  Default off — papers
print mostly black.

Limitations (deliberate): a `Protocol • R` application renders as its
pretty-printed leaf (protocols bundle several interfaces — no single
superscript is honest); a display-glyph without a declared `cc_latex`
falls back to `\mathsf{...}` of the glyph itself, so declare `cc_latex`
alongside glyph `cc_display` names; converter-parallel `(ψ‖φ)` is not
rendered because part 5 deliberately does not deliver the operation.
-/

namespace RandomSystems.CC

open Lean Elab Command Meta

namespace Latex

/-- LaTeX-escape a plain label destined for `\mathsf`. -/
def escape (s : String) : String :=
  s.foldl (fun acc c =>
    match c with
    | '_' => acc ++ "\\_"
    | '#' => acc ++ "\\#"
    | '%' => acc ++ "\\%"
    | '&' => acc ++ "\\&"
    | ' ' => acc ++ "\\ "
    | c => acc.push c) ""

/-- Interfaces print as their last name component: `Party.u` is `u`. -/
def interfaceTex (s : String) : String :=
  escape ((s.splitOn ".").getLast?.getD s)

/-- The role's palette color as a `\textcolor[HTML]{…}` wrapper, when the
color flag is on. -/
def colorize (useColor : Bool) (role : Option Names.Role) (tex : String) :
    String :=
  if useColor then
    let hex := (Diagram.roleColor role).drop 1
    s!"\\textcolor[HTML]\{{hex}}\{{tex}}"
  else tex

/-- The LaTeX of a named object: its declared `cc_latex` form, else
`\mathsf{<display label>}`. -/
def nameTex (env : Environment) (label : String) (decl : Option Name) :
    String :=
  match decl.bind (Names.latexName? env) with
  | some tex => tex
  | none => s!"\\mathsf\{{escape label}}"

/-- Render a composition shape — the very shape `#cc_diagram` draws — as
the paper equation term. -/
partial def ofShape (env : Environment) (useColor : Bool) :
    Diagram.Shape → String
  | .leaf label role decl _ => colorize useColor role (nameTex env label decl)
  | .par l r _ => s!"{ofShape env useColor l} \\| {ofShape env useColor r}"
  | .attach conv ifc inner role decl _ _ _ _ _ =>
      let convTex :=
        if conv = "⊣" then "\\dashv"
        else colorize useColor (role.orElse fun _ => some .converter)
          (nameTex env conv decl)
      let innerTex := ofShape env useColor inner
      let wrapped :=
        match inner with
        | .par .. => s!"({innerTex})"
        | _ => innerTex
      s!"{convTex}^\{{interfaceTex ifc}}\\,{wrapped}"
  -- view state (D1): a folded box is its name; an unfolded region is its
  -- content — LaTeX shows what the view shows
  | .foldBox label role _ => colorize useColor role (nameTex env label none)
  | .region _ _ inner => ofShape env useColor inner

/-- Render an elaborated term: an equality (`\equiv`), an `≈[ε]`
closeness, or a resource composition. -/
partial def ofExpr (useColor : Bool) (e : Expr) : MetaM String := do
  let env ← getEnv
  let args := e.getAppArgs
  let asShape (e : Expr) : MetaM String :=
    return ofShape env useColor (← Diagram.ofExpr e)
  match e.getAppFn with
  | .const n _ =>
      if n = ``Eq ∧ args.size ≥ 3 then
        let l ← ofExpr useColor args[args.size - 2]!
        let r ← ofExpr useColor args[args.size - 1]!
        return s!"{l} \\;\\equiv\\; {r}"
      else if n = ``RandomSystems.CC.ResourceSystem.close ∧ args.size ≥ 3 then
        let eps := (toString (← ppExpr args[args.size - 3]!)).trimAscii.toString
        let epsTex :=
          if eps = "ε" ∨ eps = "epsilon" then "\\varepsilon" else escape eps
        let l ← ofExpr useColor args[args.size - 2]!
        let r ← ofExpr useColor args[args.size - 1]!
        return s!"{l} \\;\\approx_\{{epsTex}}\\; {r}"
      else
        asShape e
  | _ => asShape e

end Latex

/-- `#cc_latex t`: emit the paper-equation LaTeX of a composition term or
statement (see the module docstring for the dictionary).
`#cc_latex (color := true) t` colors named objects by role, Maurer11
eqs. (1)–(2) style.  `color` is a non-reserved word. -/
syntax (name := ccLatexCmd)
  "#cc_latex " (atomic("(" &"color" " := ") term ") ")? term : command

/-- `#cc_latex thm Name`: render the statement of a (possibly ∀-bound)
equality or closeness theorem — the marquee use is an identity printed as
`LHS \equiv RHS`.  `thm` is a non-reserved word. -/
syntax (name := ccLatexThmCmd) (priority := high)
  "#cc_latex " &"thm " ident : command

/- Raw child-index dispatch, not quotation patterns: quotations misparse
soft (`&"…"`) keywords — the same finding that de-reserved the grammar. -/

@[command_elab ccLatexCmd] def elabCcLatex : CommandElab := fun stx => do
  let optGroup := stx[1]
  let useColor :=
    if optGroup.getNumArgs == 0 then false
    else ((optGroup[3].reprint.getD "").trimAscii.toString) == "true"
  let t : TSyntax `term := ⟨stx[2]⟩
  let tex ← liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    Latex.ofExpr useColor (← instantiateMVars e)
  logInfo tex

@[command_elab ccLatexThmCmd] def elabCcLatexThm : CommandElab := fun stx => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[2]
  let tex ← liftTermElabM do
    let info ← getConstInfo declName
    forallTelescope info.type fun _ body =>
      Latex.ofExpr false body
  logInfo tex

/-! ## Receipts -/

namespace LatexTests

open Channels CarrierDemo AlgebraDemo
open scoped Converter ResourceSystem

-- A single glyph resource: the declared `cc_latex` form, verbatim.
/-- info: {\bullet}\!=\!\!=\!{\bullet} -/
#guard_msgs in
#cc_latex (sharedKey Bool)

-- `∥` as `\|`, flat.
/-- info: {\bullet}\!\longrightarrow \| {\bullet}\!\longrightarrow -/
#guard_msgs in
#cc_latex (authenticatedChannel Bool ∥ authenticatedChannel Bool)

-- The eq.-(1) shape: superscript attachments, parenthesized `∥` core —
-- Maurer11's `dec^B enc^A (KEY \| AUT)` pattern on the carrier demo.  The
-- superscript is the CONNECTION each converter is attached along, which is
-- Jost's own `π^γ R` (printed p. 18) rather than a single interface letter.
/-- info: \mathsf{decB}^{gammaV}\,\mathsf{encA}^{gammaU}\,(\mathsf{toyR} \| \mathsf{toyR}) -/
#guard_msgs in
#cc_latex CarrierDemo.constructedShape

-- Blocking is `\dashv` with the interface superscript.
/-- info: \dashv^{e}\,\mathsf{toy3} -/
#guard_msgs in
#cc_latex (⊣[Party3.e] toy3)

-- Closeness as `\approx` with the radius subscript.
/-- info: \mathsf{toyR} \;\approx_{0}\; \mathsf{toyR} -/
#guard_msgs in
#cc_latex (toyR ≈[(0 : ℝ)] toyR)

-- Role colors behind the flag: assumed = Maurer blue.
/-- info: \textcolor[HTML]{2563c4}{{\bullet}\!=\!\!=\!{\bullet}} -/
#guard_msgs in
#cc_latex (color := true) (sharedKey Bool)

-- The marquee: an equality THEOREM rendered as the paper identity —
-- Maurer's `≡` IS this library's `=`.
/-- info: \mathsf{Counter} \;\equiv\; \mathsf{twin} -/
#guard_msgs in
#cc_latex thm GrammarTests.counter_eq_twin

end LatexTests

end RandomSystems.CC
