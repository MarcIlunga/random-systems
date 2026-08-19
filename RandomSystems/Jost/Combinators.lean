/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ResourceMachine

/-!
# Package combinators: parallel composition and converter attachment

The two composition operations of Jost's system algebra (§2.2.2), at the
package (`Machine`) level:

* `Machine.par` — Fig. 2.1's `[R, S]`: the two packages side by side, product
  state, queries routed by the interface address.  The composite's signature
  universe is the tagged sum (`SignatureUniverse.par`).
* `Converter.attach` — converter application `π R`.  A converter is itself a
  package whose step, instead of answering directly, runs a *program* over
  the inner interfaces (`Prog` — the formal residue of the pseudocode `call`
  keyword) and then answers at the queried outer interface.

**Status (2026-08-04 second-round audit): demoted to an authoring device.**
The composition *algebra* of the surface is the kernel's — attachment via
`TypedAttachment`/`TypedAction` (`Jost/SurfaceAttach.lean`, incl. the
Prop-2.2.3 interchange), parallel via `TypedTensor`
(`Jost/SurfacePar.lean`, Jost's `[R, S]` at DISJOINT interface sets — the
same operation this file's `Machine.par` builds, so the two now agree in
shape as well as in name).  These combinators remain only as
convenient constructors of machine *families* (`Jost/Systems.lean`); a
family is data, so no coherence with the kernel operations is owed by any
surface statement.  An agreement receipt (machine-level attach/par vs the
kernel's, after denotation) would be owed only by a statement equating a
combinator-built composite with a kernel-attached one; none exists, and
the item stays on the bridge ledger.
-/

namespace RandomSystems.CR18.TypedResource

universe c i u v s t w

/-! ## Parallel composition -/

/-- Tagged sum of two signature universes: a code for each side, alphabets
inherited componentwise. -/
def SignatureUniverse.par (U₁ U₂ : SignatureUniverse.{c, u, v}) :
    SignatureUniverse.{c, u, v} where
  Code := U₁.Code ⊕ U₂.Code
  input := Sum.elim U₁.input U₂.input
  output := Sum.elim U₁.output U₂.output

/-- Boundary of a parallel composite: each side keeps its own codes. -/
def Boundary.par {I₁ I₂ : Type i} {U₁ U₂ : SignatureUniverse.{c, u, v}}
    (sigma₁ : Boundary U₁ I₁) (sigma₂ : Boundary U₂ I₂) :
    Boundary (U₁.par U₂) (I₁ ⊕ I₂) :=
  Sum.map sigma₁ sigma₂

/-- Fig. 2.1's `[R, S]`: product state, the address routes the query to the
owning package, the other package's state is untouched. -/
def Machine.par {I₁ I₂ : Type i} {U₁ U₂ : SignatureUniverse.{c, u, v}}
    {sigma₁ : Boundary U₁ I₁} {sigma₂ : Boundary U₂ I₂}
    (m₁ : Machine U₁ sigma₁) (m₂ : Machine U₂ sigma₂) :
    Machine (U₁.par U₂) (sigma₁.par sigma₂) where
  State := m₁.State × m₂.State
  init := (m₁.init, m₂.init)
  step state query :=
    match query with
    | ⟨.inl interface, input⟩ =>
        (m₁.step state.1 ⟨interface, input⟩).map fun next =>
          ((next.1, state.2), next.2)
    | ⟨.inr interface, input⟩ =>
        (m₂.step state.2 ⟨interface, input⟩).map fun next =>
          ((state.1, next.1), next.2)

/-! ## Programs over the inner interfaces (the `call` keyword) -/

/-- A finite program over the queries of `(U, sigma)`: either answer now, or
issue one inner query and continue on its (fibre-typed) answer.  This is the
formal object behind each pseudocode block `call y ← (kwd, x) at interface I
of R; …`. -/
inductive Prog {I : Type i} (U : SignatureUniverse.{c, u, v})
    (sigma : Boundary U I) (α : Type w) where
  | ret (value : α)
  | call (query : Query U sigma) (rest : AnswerAt query → Prog U sigma α)

/-- Run a program against a package, threading the package's state.  `none`
as soon as an inner call leaves the package's domain (blocking divergence
propagates outward, DESIGN §10.8). -/
def Machine.runProg {I : Type i} {U : SignatureUniverse.{c, u, v}}
    {sigma : Boundary U I} (m : Machine U sigma) {α : Type w} :
    m.State → Prog U sigma α → Option (m.State × α)
  | state, .ret value => some (state, value)
  | state, .call query rest =>
      (m.step state query).bind fun next => m.runProg next.1 (rest next.2)

@[simp]
theorem Machine.runProg_ret {I : Type i} {U : SignatureUniverse.{c, u, v}}
    {sigma : Boundary U I} (m : Machine U sigma) {α : Type w}
    (state : m.State) (value : α) :
    m.runProg state (.ret value) = some (state, value) :=
  rfl

@[simp]
theorem Machine.runProg_call {I : Type i} {U : SignatureUniverse.{c, u, v}}
    {sigma : Boundary U I} (m : Machine U sigma) {α : Type w}
    (state : m.State) (query : Query U sigma)
    (rest : AnswerAt query → Prog U sigma α) :
    m.runProg state (.call query rest) =
      (m.step state query).bind fun next => m.runProg next.1 (rest next.2) :=
  rfl

/-! ## Converters -/

/-- A converter package between an outer boundary `(V, tau)` and an inner
boundary `(U, sigma)`: converter state, and per outer query a program over
the inner queries computing the new converter state and the answer in the
outer query's fibre.  Converters never block by themselves — blocking can
only arrive from the attached resource, through `runProg`. -/
structure Converter {J : Type i} {I : Type i} (V : SignatureUniverse.{c, u, v})
    (tau : Boundary V J) (U : SignatureUniverse.{c, u, v})
    (sigma : Boundary U I) : Type (max (i + 1) c u v (t + 1)) where
  State : Type t
  init : State
  step : State → (query : Query V tau) → Prog U sigma (State × AnswerAt query)

/-- Converter application `π R`: the composite package at the outer boundary.
Each outer query runs the converter's program against the resource, threading
both states. -/
def Converter.attach {J : Type i} {I : Type i}
    {V : SignatureUniverse.{c, u, v}} {tau : Boundary V J}
    {U : SignatureUniverse.{c, u, v}} {sigma : Boundary U I}
    (pi : Converter V tau U sigma) (m : Machine U sigma) : Machine V tau where
  State := pi.State × m.State
  init := (pi.init, m.init)
  step state query :=
    (m.runProg state.2 (pi.step state.1 query)).map fun result =>
      ((result.2.1, result.1), result.2.2)

@[simp]
theorem Converter.attach_step {J : Type i} {I : Type i}
    {V : SignatureUniverse.{c, u, v}} {tau : Boundary V J}
    {U : SignatureUniverse.{c, u, v}} {sigma : Boundary U I}
    (pi : Converter V tau U sigma) (m : Machine U sigma)
    (state : pi.State × m.State) (query : Query V tau) :
    (pi.attach m).step state query =
      (m.runProg state.2 (pi.step state.1 query)).map fun result =>
        ((result.2.1, result.1), result.2.2) :=
  rfl

end RandomSystems.CR18.TypedResource
