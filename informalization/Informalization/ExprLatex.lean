/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# `ExprLatex` — a real, total `Expr → LaTeX` pretty-printer (DESIGN §4(E))

A genuine recursive `exprToLatex` over the **closed core-Lean fragment** the
worked example needs: application, `∀`/`→`, `fun`, projections, named constants
(via a notation table), bound/free variables, literals, and sorts. It is *total*:
every node yields *some* LaTeX; unknown constants fall back to a fully
LaTeX-escaped `toString` (still provenance-valid — DESIGN §3.2). No mathlib, no
metaprogramming beyond plain `Expr` recursion.

The precedence-driven parenthesization (so that `(1+2)+3` and `1+(2+3)` typeset
correctly, and a binary operator only wraps a sub-term when its precedence
demands it) is **mirrored from `kmill/LeanTeX`** (the talk's `Expr→LaTeX` box;
Apache-2.0). We adopt the *idea* — a parent-precedence parameter threaded through
the recursion with a `paren`-when-`childPrec < parentPrec` rule — not the code,
which targets toolchain v4.18 and pulls its own dependencies (see
`design/REUSE_SURVEY.md` §2). Toolchain here is v4.29.0.

Security note (DESIGN §9): a malicious/odd Lean module controls every name and
literal that reaches this printer. So **all** name- and literal-derived text is
passed through `escapeLatex` before it is emitted, so nothing user-controlled can
break out of the math context (e.g. inject `\href` or unbalanced braces). This is
the Lean-side half of the "inert output" trust boundary.
-/

namespace Informalization

open Lean

/-- LaTeX-escape a raw string: every TeX-special character is replaced by its
escaped form. This is a security control (DESIGN §9): names and literals come
from an untrusted Lean module, so they must never reach the renderer able to
issue TeX commands or unbalance the surrounding math group. Total. -/
def escapeLatex (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    acc ++ (match c with
      | '\\' => "\\textbackslash{}"
      | '{'  => "\\{"
      | '}'  => "\\}"
      | '_'  => "\\_"
      | '^'  => "\\^{}"
      | '#'  => "\\#"
      | '%'  => "\\%"
      | '&'  => "\\&"
      | '$'  => "\\$"
      | '~'  => "\\textasciitilde{}"
      | _    => c.toString)

/-- The notation table: known constant names → their LaTeX rendering. Mirrors
Miller's hand-crafted `@[english_param]` registry — it grows on demand and is
purely advisory. Names not in the table fall back to an escaped `toString`. -/
def notationTable : Lean.Name → Option String
  | ``Eq                 => some "="
  | ``Iff                => some "\\iff"
  | ``And                => some "\\wedge"
  | ``Or                 => some "\\vee"
  | ``Not                => some "\\neg"
  | ``Function.comp      => some "\\circ"
  | ``Function.Injective => some "\\mathrm{injective}"
  | ``Nat                => some "\\mathbb{N}"
  | ``HAdd.hAdd          => some "+"
  | ``Add.add            => some "+"
  | ``HMul.hMul          => some "\\cdot"
  | ``Mul.mul            => some "\\cdot"
  | _                    => none

/-- Is `n` a binary operator we render infix? Returns its LaTeX symbol if so. -/
def binOp (n : Lean.Name) : Option String :=
  match n with
  | ``Eq | ``Iff | ``And | ``Or
  | ``HAdd.hAdd | ``Add.add | ``HMul.hMul | ``Mul.mul => notationTable n
  | _ => none

/-- Parenthesization precedences (mirrored from LeanTeX's precedence model).
Higher binds tighter. A child is wrapped in `\left(…\right)` exactly when its
own precedence is **strictly below** the precedence its parent demands. -/
def precOf (n : Lean.Name) : Nat :=
  match n with
  | ``Iff               => 20
  | ``Or                => 30
  | ``And               => 40
  | ``Eq                => 50
  | ``HAdd.hAdd | ``Add.add => 65
  | ``HMul.hMul | ``Mul.mul => 70
  | _                   => 75

/-- The precedence floor for function application / juxtaposition (`f\,a`). -/
def appPrec : Nat := 80

/-- Wrap `s` in LaTeX parentheses iff the rendered child's precedence
`child` is below the context's required precedence `ctx`. -/
def parenIf (ctx child : Nat) (s : String) : String :=
  if child < ctx then "\\left(" ++ s ++ "\\right)" else s

/-- Render a sort/type universe to LaTeX. -/
def sortToLatex (lvl : Level) : String :=
  if lvl.isZero then "\\mathrm{Prop}"
  else if lvl == Level.succ Level.zero then "\\mathrm{Type}"
  else "\\mathrm{Sort}"

/-- Render a literal to LaTeX (already safe: nat literals are digits; string
literals are escaped and quoted). -/
def litToLatex : Literal → String
  | .natVal n => toString n
  | .strVal s => "\\texttt{\"" ++ escapeLatex s ++ "\"}"

/-- A bound variable falls back to a fresh placeholder when its de Bruijn index
escapes the threaded binder stack (should not happen for closed terms, but keeps
the function total). -/
def bvarName (binders : List String) (i : Nat) : String :=
  match binders[i]? with
  | some nm => nm
  | none    => "x_{" ++ toString i ++ "}"

/-- Core renderer. `binders` is the de Bruijn name stack (innermost first);
`ctx` is the precedence the surrounding context requires. Total, structural. -/
partial def exprToLatexAux (binders : List String) (ctx : Nat) (e : Expr) : String :=
  match e with
  | .bvar i        => escapeLatex (bvarName binders i)
  | .fvar fid      => escapeLatex (toString fid.name)
  | .mvar mid      => escapeLatex (toString mid.name)
  | .sort lvl      => sortToLatex lvl
  | .lit l         => litToLatex l
  | .const n _     =>
      match notationTable n with
      | some s => s
      | none   => escapeLatex n.toString
  | .mdata _ inner => exprToLatexAux binders ctx inner
  | .proj _ idx s  =>
      -- `s.idx` — projection; render the structure then a dotted field index.
      let str := exprToLatexAux binders appPrec s
      parenIf ctx appPrec (str ++ ".\\mathrm{" ++ toString idx ++ "}")
  | .letE nm _ val body _ =>
      -- Render a `let` as a substitution-style binding.
      let nmStr := escapeLatex nm.toString
      let valStr := exprToLatexAux binders 0 val
      let bodyStr := exprToLatexAux (nm.toString :: binders) ctx body
      "\\text{let } " ++ nmStr ++ " := " ++ valStr ++ " \\text{ in } " ++ bodyStr
  | .forallE nm ty body _ =>
      if body.hasLooseBVar 0 then
        -- Dependent ∀: "\forall x, body".
        let nmStr := escapeLatex nm.toString
        let bodyStr := exprToLatexAux (nm.toString :: binders) 0 body
        parenIf ctx 10 ("\\forall " ++ nmStr ++ ",\\, " ++ bodyStr)
      else
        -- Non-dependent: an arrow "A \to B" (push a dummy binder for indices).
        let tyStr := exprToLatexAux binders 16 ty
        let bodyStr := exprToLatexAux ("_" :: binders) 15 body
        parenIf ctx 15 (tyStr ++ " \\to " ++ bodyStr)
  | .lam nm _ body _ =>
      let nmStr := escapeLatex nm.toString
      let bodyStr := exprToLatexAux (nm.toString :: binders) 0 body
      parenIf ctx 10 ("\\lambda " ++ nmStr ++ ",\\, " ++ bodyStr)
  | .app .. =>
      -- Peel the spine: head + explicit-ish argument list.
      let fn := e.getAppFn
      let args := e.getAppArgs
      match fn with
      | .const n _ =>
          -- Binary operator? Use the last two arguments as operands (the rest
          -- are implicit type/instance args we drop for display).
          match binOp n with
          | some sym =>
              if args.size ≥ 2 then
                let a := args[args.size - 2]!
                let b := args[args.size - 1]!
                let p := precOf n
                let aStr := exprToLatexAux binders p a
                let bStr := exprToLatexAux binders (p + 1) b
                parenIf ctx p (aStr ++ " " ++ sym ++ " " ++ bStr)
              else
                -- Under-applied operator: render as a plain const.
                escapeLatex n.toString
          | none =>
              -- `Function.comp` has 3 implicit type args, then `g f`; anything
              -- beyond is application: `(comp g f) a` = `(g ∘ f) a`.
              if n == ``Function.comp ∧ args.size ≥ 5 then
                let g := args[3]!
                let f := args[4]!
                let p := precOf ``Function.comp
                let gStr := exprToLatexAux binders p g
                let fStr := exprToLatexAux binders (p + 1) f
                let core := gStr ++ " \\circ " ++ fStr
                let extras := args.extract 5 args.size
                if extras.isEmpty then
                  parenIf ctx p core
                else
                  let argStr := extras.foldl (init := "") fun acc a =>
                    acc ++ "\\, " ++ exprToLatexAux binders (appPrec + 1) a
                  parenIf ctx appPrec ("(" ++ core ++ ")" ++ argStr)
              else
                renderJuxt binders ctx fn args
      | _ => renderJuxt binders ctx fn args
where
  /-- Function juxtaposition `f\,a\,b\,…` at application precedence. -/
  renderJuxt (binders : List String) (ctx : Nat) (fn : Expr) (args : Array Expr) : String :=
    let fnStr := exprToLatexAux binders appPrec fn
    let argStr := args.foldl (init := "") fun acc a =>
      acc ++ "\\, " ++ exprToLatexAux binders (appPrec + 1) a
    parenIf ctx appPrec (fnStr ++ argStr)

/-- Total, pure `Expr → LaTeX` over the closed core fragment. -/
def exprToLatex (e : Expr) : String :=
  exprToLatexAux [] 0 e

/-! ## Tests (hand-built `Expr`s) -/

section Tests

open Lean (mkApp2)

-- `Nat = Nat` → "\mathbb{N} = \mathbb{N}".
#guard exprToLatex
    (mkApp2 (.const ``Eq [.zero]) (.const ``Nat []) (.const ``Nat []))
  = "\\mathbb{N} = \\mathbb{N}"

-- A literal `3` → "3".
#guard exprToLatex (.lit (.natVal 3)) = "3"

-- `Prop` sort → "\mathrm{Prop}".
#guard exprToLatex (.sort .zero) = "\\mathrm{Prop}"

-- Non-dependent `∀ (_ : Nat), Nat` → arrow "\mathbb{N} \to \mathbb{N}".
#guard exprToLatex
    (.forallE `x (.const ``Nat []) (.const ``Nat []) .default)
  = "\\mathbb{N} \\to \\mathbb{N}"

-- A `λ x, x` over bvar 0 → "\lambda x,\, x".
#guard exprToLatex (.lam `x (.const ``Nat []) (.bvar 0) .default)
  = "\\lambda x,\\, x"

-- An unknown constant's name is LaTeX-escaped (underscore is escaped).
#guard exprToLatex (.const `Foo_bar []) = "Foo\\_bar"

-- `And P Q` for opaque consts → infix "\wedge".
#guard exprToLatex (mkApp2 (.const ``And []) (.const `P []) (.const `Q []))
  = "P \\wedge Q"

end Tests

end Informalization
