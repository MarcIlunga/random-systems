/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.SurfacePar
import RandomSystems.Jost.SurfaceNames

/-!
# The authoring surface, part 4: goal displays in surface vocabulary

The vocabulary rule (`Jost/Surface.lean`, §10.11) keeps kernel names out of
surface *statements*; this module keeps them out of surface *goal states*.
Mid-proof, `whnf`/`unfold` can expose the kernel spellings of surface
notions — `DependentRandomSystem (SignatureUniverse.ofInterfaces …) …` for
`Resource F`, `ofProb (Machine.lawOf …)` for `sampleInit …` — and the
reader should not have to translate back.  Delaborators re-sugar:

* `DependentRandomSystem`-types at an interface declaration → `Resource F`
  (both the `F.sig`/`F.bnd` spelling and the fully unfolded
  `ofInterfaces (F.In) (F.Out)` spelling), and at a service layout →
  `ResourceAt S layout`;
* `DependentRandomSystem.ofProb (Machine.lawOf fam seed h)` →
  `Resource.sampleInit fam seed` (the normalization proof is elided from
  the display, like an instance argument);
* `DependentRandomSystem.ofProb ⟨Finsupp.single m.toDDS 1, _⟩` →
  `Resource.ofRealization m`;
* address-tagged queries `⟨i, x⟩` whose Σ-motive is an interface-alphabet
  family → `i ! x`, with the matching *input* notation `i ! x` (a macro,
  deliberately not a `notation`, so no global auto-unexpander is installed
  for arbitrary sigma pairs — display is owned by the type-gated
  delaborator below).

Master toggle: `set_option cc.surfaceDisplay false` (importing modules; a
Lean rule keeps a module's own registered option unusable in-module) or
the standard `set_option pp.notation false` restore the raw kernel forms —
kernel debugging must be able to see what is really there.

Mechanism notes (why delaborators, not unexpanders): an
`app_unexpander` fires only on the syntax the default delaborator already
produced and cannot inspect types or subterm shapes; the shapes above are
*type-* and *argument-shape-dependent* (a sigma pair is a query only
because of its motive; `ofProb` re-sugars differently by its argument), so
they need genuine `@[app_delab]` delaborators over the `Expr`.  All
delaborators `failure` out to the default printer when a pattern or the
toggle does not match, so nothing outside the gated shapes changes.
-/

open Lean Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Delaborator.SubExpr

register_option cc.surfaceDisplay : Bool := {
  defValue := true
  descr := "render CC kernel forms in surface vocabulary \
    (Resource, ResourceAt, sampleInit, ofRealization, i ! x); \
    set to false to see raw kernel terms"
}

namespace RandomSystems.CC

/-- Input notation for address-tagged queries: `i ! x` is the query `x` at
interface `i`.  A macro rather than a `notation`, so Lean installs no
global unexpander for arbitrary `Sigma.mk` displays; the display side is
the type-gated delaborator in this module. -/
scoped syntax:67 (name := queryBang) term:68 " !" ppHardSpace term:67 : term

scoped macro_rules (kind := queryBang)
  | `($i ! $x) => `(Sigma.mk $i $x)

namespace SurfaceDelab

/-- The toggle, read inside a delaborator.  Read by raw name (a Lean rule
forbids evaluating a module's own `register_option` initializer, so the
generated `Lean.Option` constant is only usable by importers); also gated
on the standard `pp.notation`, so `set_option pp.notation false` — the
usual "show me the raw terms" switch — disables the surface display too. -/
private def surfaceDisplayOn : DelabM Bool := do
  let opts ← getOptions
  let ppNotation ← getPPOption Lean.getPPNotation
  return opts.get `cc.surfaceDisplay true && ppNotation

/-- `DependentRandomSystem`-shaped types re-sugar to `Resource F` /
`ResourceAt S layout` when the signature/boundary arguments carry an
interface declaration or a service layout. -/
@[app_delab RandomSystems.CR18.TypedResource.DependentRandomSystem]
def delabResourceType : Delab := do
  unless (← surfaceDisplayOn) do failure
  let e ← getExpr
  guard <| e.isAppOfArity
    ``RandomSystems.CR18.TypedResource.DependentRandomSystem 5
  let U := e.getArg! 1
  let b := e.getArg! 4
  if U.isAppOfArity ``Interfaces.sig 1 && b.isAppOfArity ``Interfaces.bnd 1
      && U.appArg! == b.appArg! then
    -- spelling `DependentRandomSystem F.sig F.bnd`
    let F ← withNaryArg 1 <| withNaryArg 0 delab
    `($(mkIdent `Resource) $F)
  else if U.isAppOfArity
        ``RandomSystems.CR18.TypedResource.SignatureUniverse.ofInterfaces 3
      && b.isAppOfArity
        ``RandomSystems.CR18.TypedResource.Boundary.ofInterfaces 3 then
    -- fully unfolded spelling `… (ofInterfaces F.In F.Out) (ofInterfaces F.In F.Out)`
    let inU := U.getArg! 1
    let outU := U.getArg! 2
    if inU.isAppOfArity ``Interfaces.In 1 && outU.isAppOfArity ``Interfaces.Out 1
        && outU.appArg! == inU.appArg!
        && b.getArg! 1 == inU && b.getArg! 2 == outU then
      let F ← withNaryArg 1 <| withNaryArg 1 <| withNaryArg 0 delab
      `($(mkIdent `Resource) $F)
    else
      failure
  else if U.isAppOfArity ``Services.sig 1 then
    -- spelling `DependentRandomSystem S.sig layout`
    let S ← withNaryArg 1 <| withNaryArg 0 delab
    let layout ← withNaryArg 4 delab
    `($(mkIdent `ResourceAt) $S $layout)
  else if U.isAppOfArity
      ``RandomSystems.CR18.TypedResource.SignatureUniverse.mk 3 then
    -- unfolded `Services.sig`: the structure literal over one `S`
    let code := U.getArg! 0
    if code.isAppOfArity ``Services.Service 1
        && (U.getArg! 1).isAppOfArity ``Services.In 1
        && (U.getArg! 1).appArg! == code.appArg!
        && (U.getArg! 2).isAppOfArity ``Services.Out 1
        && (U.getArg! 2).appArg! == code.appArg! then
      let S ← withNaryArg 1 <| withNaryArg 0 <| withNaryArg 0 delab
      let layout ← withNaryArg 4 delab
      `($(mkIdent `ResourceAt) $S $layout)
    else
      failure
  else
    failure

/-- `ofProb` of a sampled family re-sugars to `sampleInit` (normalization
proof elided); `ofProb` of a point law at a realization re-sugars to
`ofRealization`. -/
@[app_delab RandomSystems.CR18.TypedResource.DependentRandomSystem.ofProb]
def delabOfProb : Delab := do
  unless (← surfaceDisplayOn) do failure
  let e ← getExpr
  guard <| e.isAppOfArity
    ``RandomSystems.CR18.TypedResource.DependentRandomSystem.ofProb 6
  let sys := e.getArg! 5
  if sys.isAppOfArity ``RandomSystems.CR18.TypedResource.Machine.lawOf 7 then
    let fam ← withNaryArg 5 <| withNaryArg 4 delab
    let seed ← withNaryArg 5 <| withNaryArg 5 delab
    `($(mkIdent `Resource.sampleInit) $fam $seed)
  else if sys.isAppOfArity ``Subtype.mk 4 then
    let val := sys.getArg! 2
    if val.isAppOfArity ``Finsupp.single 5
        && (val.getArg! 3).isAppOfArity
          ``RandomSystems.CR18.TypedResource.Machine.toDDS 4 then
      let m ← withNaryArg 5 <| withNaryArg 2 <| withNaryArg 3 <|
        withNaryArg 3 delab
      `($(mkIdent `Resource.ofRealization) $m)
    else
      failure
  else
    failure

/-- Query *types* at an interface declaration re-sugar to `F.Query`: the
`Sigma` over an interface-alphabet motive whose signature/boundary both
come from one `F`. -/
@[app_delab Sigma]
def delabQueryType : Delab := do
  unless (← surfaceDisplayOn) do failure
  let e ← getExpr
  guard <| e.isAppOfArity ``Sigma 2
  let motive := e.getArg! 1
  let .lam _ _ body _ := motive | failure
  guard <| body.isAppOfArity
    ``RandomSystems.CR18.TypedResource.SignatureUniverse.input 2
  let U := body.getArg! 0
  guard <| U.isAppOfArity ``Interfaces.sig 1
  let boundaryApp := body.getArg! 1
  guard <| boundaryApp.isApp
  let bnd := boundaryApp.appFn!
  guard <| bnd.isAppOfArity ``Interfaces.bnd 1 && bnd.appArg! == U.appArg!
  let F ← withNaryArg 1 <| withBindingBody `interface <|
    withNaryArg 0 <| withNaryArg 0 delab
  `($(mkIdent `Interfaces.Query) $F)

/-! ### Declared display names (`@[cc_display "…"]`, `SurfaceNames.lean`)

A declaration carrying a `cc_display` string renders AS that string —
glyphs welcome (`•—→`, `•══•`): the papers name resources by symbols
(MaRuTa12 §1.3), and presentation is declared, not encoded in
identifiers.  Arguments are elided from the display (the papers write
`—→`, not `—→ M`); toggle off to recover the full term. -/

/-- A display string as term syntax.  Rendered as an identifier, so glyph
names print guillemeted (`«•—→»`) — the honest boundary of Lean's
identifier lexer, and still round-trippable input.  (A raw `Syntax.atom`
prints the bare string but crashes the formatter; the clean glyph without
guillemets is the `#cc_latex` exporter's job.) -/
private def displayStx (s : String) : Term :=
  mkIdent (Name.mkSimple s)

/-- Applications headed by a display-named declaration render as the
declared string. -/
@[delab app]
def delabDisplayNamedApp : Delab := do
  unless (← surfaceDisplayOn) do failure
  let e ← getExpr
  let .const n _ := e.getAppFn | failure
  let some disp := Names.displayName? (← getEnv) n | failure
  return displayStx disp

/-- Bare display-named constants render as the declared string. -/
@[delab const]
def delabDisplayNamedConst : Delab := do
  unless (← surfaceDisplayOn) do failure
  let .const n _ := (← getExpr) | failure
  let some disp := Names.displayName? (← getEnv) n | failure
  return displayStx disp

/-- Address-tagged queries display as `i ! x`.  Gated on the sigma's
motive being an interface-alphabet family, so ordinary `Sigma.mk` pairs
are untouched. -/
@[app_delab Sigma.mk]
def delabQueryMk : Delab := do
  unless (← surfaceDisplayOn) do failure
  let e ← getExpr
  guard <| e.isAppOfArity ``Sigma.mk 4
  let ty ← Meta.whnfR (← Meta.inferType e)
  guard <| ty.isAppOfArity ``Sigma 2
  let motive := ty.getArg! 1
  let .lam _ _ body _ := motive | failure
  let head := body.getAppFn
  let isAlphabet :=
    head.isConstOf ``RandomSystems.CR18.TypedResource.SignatureUniverse.input
      || head.isConstOf ``Interfaces.In
      || head.isConstOf ``Services.In
      || head.isConstOf ``SumService.inputs
  guard isAlphabet
  let i ← withNaryArg 2 delab
  let x ← withNaryArg 3 delab
  `($i ! $x)

end SurfaceDelab

/-! ## Receipts -/

namespace SurfaceDelabTests

open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource

inductive DIface | a | b
  deriving DecidableEq

inductive AIn | ping
inductive BIn | read

def demo : Interfaces where
  Iface := DIface
  In := fun | .a => AIn | .b => BIn
  Out := fun | .a => Unit | .b => Nat

def box : demo.Realization where
  State := Nat
  init := 0
  step n query :=
    match query with
    | ⟨.a, .ping⟩ => some (n + 1, ())
    | ⟨.b, .read⟩ => some (n, n)

noncomputable def res : Resource demo := Resource.ofRealization box

noncomputable def fam : Bool → demo.Realization := fun _ => box

-- The kernel spelling re-sugars.  (`id res` forces the inferred ascription
-- type into the message; bare `res` would print its STORED type, where the
-- `Resource` abbrev survives and no delaboration is needed.)
/-- info: id res : Resource demo -/
#guard_msgs in
#check (id res : DependentRandomSystem demo.sig demo.bnd)

-- The standard raw-terms switch restores the kernel form.  (The module.s own
-- `set_option cc.surfaceDisplay false` behaves identically for importers,
-- verified externally; a Lean rule keeps a module.s own registered option
-- unusable in-module.)
set_option pp.notation false in
/-- info: id res : DependentRandomSystem demo.sig demo.bnd -/
#guard_msgs in
#check (id res : DependentRandomSystem demo.sig demo.bnd)

-- A kernel-spelled sampled law re-sugars to `sampleInit`.
/-- info: Resource.sampleInit fam (Dist.uniform Bool) : Resource demo -/
#guard_msgs in
#check (DependentRandomSystem.ofProb
  (Machine.lawOf fam (Dist.uniform Bool) Dist.uniform_isProbDist))

-- A query literal displays as `i ! x`.
/-- info: DIface.a !AIn.ping : Interfaces.Query demo -/
#guard_msgs in
#check (⟨DIface.a, AIn.ping⟩ : demo.Query)

/-- The input notation round-trips with the anonymous-constructor form. -/
example : (DIface.a ! AIn.ping : demo.Query) = ⟨DIface.a, AIn.ping⟩ := rfl

-- Ordinary sigma pairs are untouched by the query display.
/-- info: ⟨1, 2⟩ : (_ : ℕ) × ℕ -/
#guard_msgs in
#check (⟨1, 2⟩ : Σ _ : Nat, Nat)

-- A declared display name renders as its string — glyphs welcome
-- (MaRuTa12 §1.3 names channels by symbols).  Applications elide their
-- arguments under the display name (the papers write `—→`, never `—→ M`).
-- (`#check` on a BARE constant takes a special signature path that skips
-- term delaboration, so the receipts are application-shaped.)
@[cc_display "•—→", cc_role assumed]
noncomputable def authDemo : Resource demo := res

@[cc_display "—→"]
noncomputable def insecureDemo (_M : Type) : Resource demo := res

/-- info: «—→» : Resource demo -/
#guard_msgs in
#check insecureDemo Bool

/-- info: id «•—→» : Resource demo -/
#guard_msgs in
#check (id authDemo : Resource demo)

-- The raw-terms switch recovers the identifiers.
set_option pp.notation false in
/-- info: insecureDemo Bool : Resource demo -/
#guard_msgs in
#check insecureDemo Bool

end SurfaceDelabTests

end RandomSystems.CC
