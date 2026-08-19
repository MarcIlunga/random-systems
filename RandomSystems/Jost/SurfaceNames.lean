/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Display names: the papers' typography, attached to declarations

The Maurer school names its objects visually: resources by symbols
(`—→` insecure, `•—→` authenticated, `•══•` shared key — MaRuTa12 §1.3:
"denoted either by special symbols or by upper case boldface letters"),
converters by sans names (`otp-enc`, `sim`), specifications calligraphic,
and Maurer11's equations color the terms by role.  Lean identifiers cannot
carry hyphens, arrows, or fonts — so presentation is declared, not
encoded: three attributes attach a display string, a LaTeX form, and a
role to any declaration.  The consumers are the delaborators (goals), the
diagram/simulation widgets, and the `#cc_latex` exporter; the grammar
emits these attributes from its optional `display …/latex …/role …`
clauses.

This module is deliberately just the CONTRACT: attributes + getters.
-/

namespace RandomSystems.CC.Names

open Lean

/-- Maurer11's role palette (eqs. (1)–(2)): assumed resources blue,
constructed/ideal red, converters green, the simulator teal; games from
the small-caps game names of JosMau20. -/
inductive Role
  | assumed | constructed | converter | simulator | game
  deriving BEq, Repr, Inhabited, DecidableEq

def Role.ofName? : Name → Option Role
  | `assumed => some .assumed
  | `constructed => some .constructed
  | `converter => some .converter
  | `simulator => some .simulator
  | `game => some .game
  | _ => none

syntax (name := cc_display) "cc_display " str : attr
syntax (name := cc_latex) "cc_latex " str : attr
syntax (name := cc_role) "cc_role " ident : attr

initialize displayAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `cc_display
    descr := "paper display name (arbitrary string, glyphs welcome)"
    getParam := fun _ stx =>
      match stx with
      | `(attr| cc_display $s:str) => pure s.getString
      | _ => throwError "cc_display expects a string literal" }

initialize latexAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `cc_latex
    descr := "LaTeX form for #cc_latex export"
    getParam := fun _ stx =>
      match stx with
      | `(attr| cc_latex $s:str) => pure s.getString
      | _ => throwError "cc_latex expects a string literal" }

initialize roleAttr : ParametricAttribute Role ←
  registerParametricAttribute {
    name := `cc_role
    descr := "role for typography: assumed | constructed | converter | simulator | game"
    getParam := fun _ stx =>
      match stx with
      | `(attr| cc_role $r:ident) =>
          match Role.ofName? r.getId with
          | some role => pure role
          | none => throwError
              "cc_role expects one of: assumed, constructed, converter, simulator, game"
      | _ => throwError "cc_role expects an identifier" }

/-- The declared display name, if any. -/
def displayName? (env : Environment) (declName : Name) : Option String :=
  displayAttr.getParam? env declName

/-- The declared LaTeX form, if any. -/
def latexName? (env : Environment) (declName : Name) : Option String :=
  latexAttr.getParam? env declName

/-- The declared role, if any. -/
def role? (env : Environment) (declName : Name) : Option Role :=
  roleAttr.getParam? env declName

/-- Display name with the paper-natural fallback: the declaration's last
name component. -/
def displayOf (env : Environment) (declName : Name) : String :=
  (displayName? env declName).getD
    (match declName with
      | .str _ s => s
      | n => n.toString)

end RandomSystems.CC.Names
