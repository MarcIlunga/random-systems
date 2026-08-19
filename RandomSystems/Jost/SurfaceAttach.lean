/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Jost.Surface
import RandomSystems.StepRealization
import RandomSystems.Jost.SurfaceLint

/-!
# The authoring surface, part 2: converters and attachment

A construction moves an interface between *services* — the authenticated
channel's interface `A` accepts ciphertexts in the assumed world and
plaintexts in the constructed world.  The author therefore declares, once
per development, the `Services` the construction ranges over (named
input/output alphabet pairs); a converter *transforms* the service at one
interface; attachment performs the transformation on a resource, leaving
every other interface untouched.

* `Services` — the alphabet pairs of one development (the kernel's
  signature codes, surfaced with a name that says what they are: what an
  interface *provides*).
* `Converter S source target` — Def 2.2.2's converter between two
  services, authored by `Converter.ofRounds`: a step function seeing the
  whole outer history and the open round's inner answers, issuing one
  inner call per step until the round's call budget is spent, then
  answering.  The causality/finiteness judgment is discharged once,
  inside the constructor (`isDDC_ofHistoryStep`).
* `Resource.attach` — converter application `π R` at one interface, on
  resources (the behavioral quotient), inheriting congruence and
  1-Lipschitz non-expansion from the kernel (`TypedAction.lean`).

Statements mention only surface names; the kernel vocabulary stays in
bodies (rule of `Jost/Surface.lean`).
-/

namespace RandomSystems.CC

open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource
open RandomSystems.CR18.PFunConverter

/-- The services of one development: for each service name, the input and
output alphabet an interface providing it carries.  (Kernel: the signature
universe's codes.)  A single-world declaration (`Interfaces`) is the
special case with one service per interface. -/
@[cc_surface]
structure Services : Type 1 where
  Service : Type
  [deceq : DecidableEq Service]
  In : Service → Type
  Out : Service → Type

attribute [instance] Services.deceq

namespace Services

variable (S : Services)

/-- The kernel signature universe of this development.  (Implementation;
never appears in a surface statement.) -/
abbrev sig : SignatureUniverse := ⟨S.Service, S.In, S.Out⟩

instance : DecidableEq (S.sig).Code := S.deceq

/-- An assignment of services to interfaces — which service each interface
of a resource provides.  (Kernel: a boundary.) -/
@[cc_surface]
abbrev Layout (I : Type) := I → S.Service

end Services

/-- The resource at a service layout: behaviors at that boundary, exactly
as in `Jost/Surface.lean` but allowing several services per development. -/
@[cc_surface]
abbrev ResourceAt (S : Services) {I : Type} [DecidableEq I]
    (layout : S.Layout I) :=
  DependentRandomSystem S.sig layout

/-- **Def 2.2.2's converter** between two services: upon an input at the
outside (target-service) interface it makes finitely many inside
(source-service) calls, then answers.  Authored via `ofRounds`. -/
@[cc_surface]
abbrev Converter (S : Services) (source target : S.Service) :=
  DeterministicConverter S.sig source target

namespace Converter

variable {S : Services} {source target : S.Service}

/-- Author a converter by rounds (Def 2.2.2 made structural, on the
kernel's own stateful carrier): `step` sees the whole outer history and
the open round's inner answers so far; it issues the round's next inner
call until the round's `calls` budget is spent, then answers at the
outside interface.  `discipline` says exactly that (`calls us` inner calls
in the round at outer history `us`), and `bound` is the finite global
budget — together they discharge Def 2.2.2's causality/finiteness
judgment once, here. -/
@[cc_surface]
noncomputable def ofRounds
    (step : (history : List (S.In target)) → history ≠ [] →
      List (S.Out source) → S.In source ⊕ S.Out target)
    (calls : List (S.In target) → ℕ)
    (discipline : ∀ (history : List (S.In target)) (nonempty : history ≠ [])
      (answers : List (S.Out source)),
      (∃ query, step history nonempty answers = Sum.inl query) ↔
        answers.length < calls history)
    (bound : ∃ budget, ∀ history, calls history ≤ budget) :
    Converter S source target :=
  DeterministicConverter.ofHistory
    (ProtocolFn.ofHistoryStep step calls)
    (ProtocolFn.isDDC_ofHistoryStep step calls discipline bound)

/-- The memoryless special case: one outer input becomes one inner query,
one inner answer becomes the outer answer. -/
@[cc_surface]
noncomputable def ofMaps (query : S.In target → S.In source)
    (answer : S.Out source → S.Out target) : Converter S source target :=
  DeterministicConverter.ofFunctions query answer

end Converter

namespace ResourceAt

variable {S : Services} {I : Type} [DecidableEq I] {layout : S.Layout I}

/-- Converter application at one interface, **layout-indexed**: the
interface's service changes from `source` to `target`; every other
interface is untouched.  Well-defined on behaviors, congruent and
1-Lipschitz, by the kernel's quotient theory.

**Demoted** (Maurer standard): the result type moves the layout by
`Function.update`, which Maurer11 fn. 9 forbids the reader to see —
attachment yields "again a resource with the same interface set".  Surface
successor: `Converter.attachAt` (`α •[i] R`, total, on the bundled
carrier — `Jost/SurfaceCarrier.lean`); this layout-indexed form remains
the kernel step under it (`Converter.attachAt_of_provides`). -/
@[cc_surface_demoted]
noncomputable def attach {source target : S.Service}
    (interface : I) (converter : Converter S source target)
    (provides : layout interface = source)
    (resource : ResourceAt S layout) :
    ResourceAt S (Function.update layout interface target) :=
  DependentRandomSystem.attach interface converter provides resource

/-- Attachment does not expand behavioral distance (converter
non-expansion, Thm 2.2.11's engine at this layer).

**Demoted** (Maurer standard): states the raw metric projection; the
papers write `≈_ε`.  Surface successor: `ResourceSystem.close_attachAt`
(Maurer11 eq. (4), in `≈[ε]` — `Jost/SurfaceCarrier.lean`). -/
@[cc_surface_demoted]
theorem edist_attach_le {source target : S.Service}
    (interface : I) (converter : Converter S source target)
    (provides : layout interface = source)
    (left right : ResourceAt S layout) :
    edist (attach interface converter provides left)
        (attach interface converter provides right) ≤ edist left right :=
  DependentRandomSystem.edist_attach_le interface converter provides left right

/-- Transport helper: `ofProb` respects heterogeneous equality of
normalized laws over propositionally equal boundaries.  (Kernel-shaped;
migration candidate for `TypedAction.lean` beside
`Prob.heq_of_boundary_eq_of_val_heq`.) -/
theorem heq_ofProb_of_boundary_eq {boundaryL boundaryR : Boundary S.sig I}
    (boundaries : boundaryL = boundaryR)
    {left : DependentPDS.Prob S.sig boundaryL}
    {right : DependentPDS.Prob S.sig boundaryR}
    (values : HEq left right) :
    HEq (DependentRandomSystem.ofProb left)
      (DependentRandomSystem.ofProb right) := by
  subst boundaries
  exact heq_of_eq (congrArg DependentRandomSystem.ofProb (eq_of_heq values))

/-- Composition-order independence at the layout-indexed layer: converters
attached at *distinct* interfaces commute.  The two composites live at the
two orders of updating the layout — propositionally the same layout — so
the identity is heterogeneous; commuting the layout updates is the only
transport involved.  Lifted from the kernel's law-level interchange through
the quotient.

**Demoted** (Maurer standard): Prop. 2.2.3 / Maurer11 Def. 1 (i) is a
plain equality, not an `HEq` across transported layouts.  Surface
successor: `Converter.attachAt_comm` (bare `=` on the bundled carrier —
`Jost/SurfaceCarrier.lean`); this `HEq` form remains the kernel engine it
is proved from. -/
@[cc_surface_demoted]
theorem attach_comm
    {source₁ target₁ source₂ target₂ : S.Service}
    {interface₁ interface₂ : I} (different : interface₁ ≠ interface₂)
    (converter₁ : Converter S source₁ target₁)
    (converter₂ : Converter S source₂ target₂)
    (provides₁ : layout interface₁ = source₁)
    (provides₂ : layout interface₂ = source₂)
    (resource : ResourceAt S layout) :
    HEq
      (attach interface₁ converter₁
        (by simpa [replaceBoundary, different] using provides₁)
        (attach interface₂ converter₂ provides₂ resource))
      (attach interface₂ converter₂
        (by
          have reverse : interface₂ ≠ interface₁ := Ne.symm different
          simpa [replaceBoundary, reverse] using provides₂)
        (attach interface₁ converter₁ provides₁ resource)) := by
  induction resource using Quotient.inductionOn with
  | _ prob =>
      exact heq_ofProb_of_boundary_eq
        (replace_boundary_comm layout different target₁ target₂)
        (DependentPDS.Prob.attach_comm different converter₁ converter₂
          provides₁ provides₂ prob)

end ResourceAt

end RandomSystems.CC
