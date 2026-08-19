/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedAction
import RandomSystems.TypedFramingMetric
import RandomSystems.Jost.LawCoupling
import RandomSystems.Jost.SurfaceLint

/-!
# The authoring surface: thesis vocabulary over the contextual quotient

Jost Def 2.2.1 in the words the thesis uses.  An author declares the
per-interface alphabets (`Interfaces` — the typed reading of Fig. 2.2's
interface blocks), writes state machines, and obtains **resources**:

* `Resource F` — the thesis's resource proper.  **Plain `=` on `Resource F`
  is behavioral identity**: the carrier is the contextual quotient
  (`TypedAction.lean`), so no representation detail — Finsupp encoding,
  seed choice, lazy-vs-eager sampling, state layout — is observable
  through it, and no separate `≈` is needed.
* `Resource.ofState` — a Fig. 2.2 box with no `Initialization` sampling:
  a state, its initialization, one step per query.
* `Resource.sampleInit` — the `x ←$ X` Initialization block: a seed-indexed
  family of realizations under a seed law (Def 2.2.1's "random variable
  over deterministic systems", verbatim).

The proof devices arrive with the constructors, restated at the resource:

* `ofState_congr_of_bisim` — state refactors are invisible;
* `sampleInit_congr` / `sampleInit_eq_of_coupling` — "couple on the seed,
  compare answers along the transcript" produces *resource equality*.

Vocabulary rule, enforced here and owed by every later surface module: the
kernel's names (`SignatureUniverse`, codes, `Boundary`, `Dependent*`) may
appear in definition *bodies*, never in a surface *statement* (§10.11:
statements read as algebra).  `Realization` — the repository's own word
for a state-machine presentation (`StepRealization.lean`) — is the only
name the author meets for the pseudocode object itself.

Nothing here is new mathematics: the quotient, its metric, congruence and
attachment theory are `TypedAction.lean`'s; the coupling principles are
`Jost/LawCoupling.lean`'s.  This module only removes the kernel vocabulary
from the author's field of view — the kernel keeps codes for multi-world
signatures, which no single-world author needs.
-/

namespace RandomSystems.CC

open RandomSystems (Dist)
open RandomSystems.CR18.TypedResource

/-- Def 2.2.1's interface data, typed as Fig. 2.2 uses it: a set of
interfaces, and for each one its input and output alphabet.  (Parties are a
grouping of interfaces; at this surface each interface is an access point.) -/
@[cc_surface]
structure Interfaces : Type 1 where
  Iface : Type
  [deceq : DecidableEq Iface]
  In : Iface → Type
  Out : Iface → Type

attribute [instance] Interfaces.deceq

namespace Interfaces

variable (F : Interfaces)

/-- The kernel signature of a single-world interface declaration.
(Implementation; never appears in a surface statement.) -/
abbrev sig : SignatureUniverse := SignatureUniverse.ofInterfaces F.In F.Out

/-- The kernel boundary: each interface carries its own signature.
(Implementation; never appears in a surface statement.) -/
abbrev bnd : Boundary F.sig F.Iface := Boundary.ofInterfaces F.In F.Out

/-- A stateful realization of a resource — the rectangular box of
Figs. 2.1/2.2: persistent state, initialization, one step per query.
"Realization" is the repository's word for a state-machine presentation of
a behavior (`StepRealization.lean`); the resource itself is obtained
through the constructors below, and two realizations related by a
bisimulation present the same resource. -/
@[cc_surface]
abbrev Realization : Type 1 := InterfaceMachine F.In F.Out

/-- An address-tagged query: an interface together with an input at it. -/
@[cc_surface]
abbrev Query := RandomSystems.CR18.TypedResource.Query F.sig F.bnd

/-- A deterministic **system** over an interface declaration: what a
realization presents when the state is hidden — answers along every finite
transcript.  (The carrier is the kernel's deterministic-system type;
body-only, per §10.11.) -/
@[cc_surface]
abbrev System := DependentDDS F.sig F.bnd

instance : DecidableEq F.sig.Code := F.deceq

end Interfaces

/-- **The system a realization presents**: the denotation map, pseudocode
box ↦ deterministic system.  Two realizations present the same system
exactly when their answers agree along every transcript; the coupling
congruences below phrase their fibre conditions through this map. -/
@[cc_surface]
abbrev presents {F : Interfaces} (realization : F.Realization) : F.System :=
  realization.toDDS

/-- **The resource** (Def 2.2.1) at an interface declaration: behaviors,
not presentations — normalized laws over deterministic systems, quotiented
by every finite deterministic observation context.  Equality is behavioral,
which is the thesis's own identity for resources. -/
@[cc_surface]
abbrev Resource (F : Interfaces) :=
  DependentRandomSystem F.sig F.bnd

namespace Resource

variable {F : Interfaces}

/-- A deterministic realization, as a resource. -/
@[cc_surface]
noncomputable def ofRealization (realization : F.Realization) : Resource F :=
  DependentRandomSystem.ofProb
    ⟨Finsupp.single realization.toDDS 1, Dist.isProbDist_single _⟩

/-- A Fig. 2.2 box with no `Initialization` sampling, written directly:
a state type, its initial value, one step per query.  `none` marks the
history as outside the domain (blocking); a recoverable rejection is an
ordinary answer value. -/
@[cc_surface]
noncomputable def ofState {State : Type} (init : State)
    (step : State → (query : F.Query) → Option (State × AnswerAt query)) :
    Resource F :=
  ofRealization ⟨State, init, step⟩

/-- Fig. 2.2's `Initialization x ←$ X` block: a seed-indexed family of
realizations under a seed law denotes a resource — Def 2.2.1's random
variable over deterministic systems, verbatim. -/
@[cc_surface]
noncomputable def sampleInit {Omega : Type*} (family : Omega → F.Realization)
    (seed : Dist Omega)
    (normalized : seed.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _) : Resource F :=
  DependentRandomSystem.ofProb (Machine.lawOf family seed normalized)

/-- State refactors are invisible at the resource: a bisimulation with
equal answers identifies the presented resources.  (The realization is the
*description*; the resource is its behavior.) -/
@[cc_surface]
theorem ofRealization_congr_of_bisim {left right : F.Realization}
    (rel : left.State → right.State → Prop)
    (init : rel left.init right.init)
    (step : ∀ {state₁ : left.State} {state₂ : right.State},
      rel state₁ state₂ → ∀ query : F.Query,
        (left.step state₁ query).map Prod.snd =
            (right.step state₂ query).map Prod.snd ∧
          ∀ next₁ next₂, left.step state₁ query = some next₁ →
            right.step state₂ query = some next₂ → rel next₁.1 next₂.1) :
    ofRealization left = ofRealization right := by
  have denote_eq := Machine.toDDS_eq_of_bisim rel init step
  unfold ofRealization
  exact congrArg DependentRandomSystem.ofProb (Subtype.ext
    (show Finsupp.single left.toDDS (1 : ℝ) = Finsupp.single right.toDDS 1 by
      rw [denote_eq]))

/-- Two `Initialization` blocks over one seed law present the same resource
as soon as the sampled realizations present the same system at every seed
in the support — the identity-coupling case. -/
@[cc_surface]
theorem sampleInit_congr {Omega : Type*}
    {family₁ family₂ : Omega → F.Realization} {seed : Dist Omega}
    (normalized : seed.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _)
    (fibres : ∀ omega ∈ seed.support,
      presents (family₁ omega) = presents (family₂ omega)) :
    sampleInit family₁ seed normalized = sampleInit family₂ seed normalized :=
  congrArg DependentRandomSystem.ofProb
    (Machine.lawOf_congr normalized fibres)

/-- "Couple on the seed, compare answers along the transcript": a coupling
of the two seed laws whose coupled realizations present the same system on
the joint support identifies the two resources. -/
@[cc_surface_bridge]
theorem sampleInit_eq_of_coupling {Omega₁ Omega₂ : Type*}
    {family₁ : Omega₁ → F.Realization} {family₂ : Omega₂ → F.Realization}
    {seed₁ : Dist Omega₁} {seed₂ : Dist Omega₂}
    (normalized₁ : seed₁.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _)
    (normalized₂ : seed₂.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _)
    (joint : Dist (Omega₁ × Omega₂))
    (marginal_fst : Dist.fTransform Prod.fst joint = seed₁)
    (marginal_snd : Dist.fTransform Prod.snd joint = seed₂)
    (fibres : ∀ pair ∈ joint.support,
      presents (family₁ pair.1) = presents (family₂ pair.2)) :
    sampleInit family₁ seed₁ normalized₁ =
      sampleInit family₂ seed₂ normalized₂ :=
  congrArg DependentRandomSystem.ofProb
    (Machine.lawOf_eq_of_coupling normalized₁ normalized₂ joint
      marginal_fst marginal_snd fibres)

/-- Eliminate a pushforward-support quantifier with the substitution
pre-applied: to know `P` on the support of `f⋆μ` it suffices to know
`P ∘ f` on the support of `μ`.  (Dist-level helper; migration candidate
for `Dist.lean` beside `mem_support_fTransform`.) -/
theorem _root_.RandomSystems.Dist.forall_support_fTransform
    {A B : Type*} {f : A → B} {μ : RandomSystems.Dist A} {P : B → Prop}
    (pointwise : ∀ a ∈ μ.support, P (f a)) :
    ∀ b ∈ (RandomSystems.Dist.fTransform f μ).support, P b := by
  intro b member
  obtain ⟨a, mem, image⟩ := RandomSystems.Dist.mem_support_fTransform f μ member
  exact image ▸ pointwise a mem

/-- The workhorse special case of the coupling bridge: **transport the first
seed onto the second along a map**.  The joint is the graph pushforward, the
first marginal is definitional, and the fibre condition arrives with the
substitution pre-applied — consumers never touch the joint's support.
(The coin: `transport := not`; OTP's pairing: `transport := (m₀ ^^ ·)`.) -/
@[cc_surface_bridge]
theorem sampleInit_eq_of_pushforward_coupling {Omega₁ Omega₂ : Type*}
    {family₁ : Omega₁ → F.Realization} {family₂ : Omega₂ → F.Realization}
    {seed₁ : Dist Omega₁} {seed₂ : Dist Omega₂}
    (normalized₁ : seed₁.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _)
    (normalized₂ : seed₂.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _)
    (transport : Omega₁ → Omega₂)
    (transports : Dist.fTransform transport seed₁ = seed₂)
    (fibres : ∀ omega ∈ seed₁.support,
      presents (family₁ omega) = presents (family₂ (transport omega))) :
    sampleInit family₁ seed₁ normalized₁ =
      sampleInit family₂ seed₂ normalized₂ := by
  refine sampleInit_eq_of_coupling normalized₁ normalized₂
    (Dist.fTransform (fun omega => (omega, transport omega)) seed₁) ?_ ?_ ?_
  · rw [Dist.fTransform_comp]
    exact Dist.fTransform_id seed₁
  · rw [Dist.fTransform_comp]
    exact transports
  · exact Dist.forall_support_fTransform fibres

/-! ### Bridges — the one sanctioned appearance of kernel names

Resources ARE behaviors, so surface equality must be provable from — and
refutable by — behavioral facts.  These bridges are where the kernel's
equivalence notions enter a surface statement; by the vocabulary rule they
appear here and nowhere else. -/

/-- Two `Initialization` blocks present the same resource **iff** no finite
deterministic observation context separates their laws — Def 2.2.1's
identity of resources, cashed as an iff on the presentations. -/
@[cc_surface_bridge]
theorem sampleInit_eq_iff {Omega₁ Omega₂ : Type*}
    {family₁ : Omega₁ → F.Realization} {family₂ : Omega₂ → F.Realization}
    {seed₁ : Dist Omega₁} {seed₂ : Dist Omega₂}
    (normalized₁ : seed₁.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _)
    (normalized₂ : seed₂.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _) :
    sampleInit family₁ seed₁ normalized₁ =
        sampleInit family₂ seed₂ normalized₂ ↔
      DependentPDS.ContextuallyEquivalent
        (Machine.lawOf family₁ seed₁ normalized₁).val
        (Machine.lawOf family₂ seed₂ normalized₂).val :=
  ⟨fun h =>
      @Quotient.exact _ (DependentPDS.Prob.contextualSetoid F.sig F.bnd) _ _ h,
    fun h =>
      @Quotient.sound _ (DependentPDS.Prob.contextualSetoid F.sig F.bnd) _ _ h⟩

/-- The flat entry point (full abstraction's equivalence face): if every
strict test accepts the two flattened laws with equal mass, the resources
are equal.  This is the route for identities that are *not* law
equalities — e.g. the one-time pad, where the real and ideal laws differ
as distributions over deterministic systems yet present one behavior. -/
@[cc_surface_bridge]
theorem sampleInit_eq_of_flatten_equivalent {Omega₁ Omega₂ : Type*}
    {family₁ : Omega₁ → F.Realization} {family₂ : Omega₂ → F.Realization}
    {seed₁ : Dist Omega₁} {seed₂ : Dist Omega₂}
    (normalized₁ : seed₁.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _)
    (normalized₂ : seed₂.isProbDist := by
      first
        | exact RandomSystems.Dist.uniform_isProbDist
        | exact RandomSystems.Dist.isProbDist_single _)
    (equivalent : RandomSystems.CR18.StrictContext.Equivalent
      (DependentPDS.flatten (Machine.lawOf family₁ seed₁ normalized₁).val)
      (DependentPDS.flatten (Machine.lawOf family₂ seed₂ normalized₂).val)) :
    sampleInit family₁ seed₁ normalized₁ =
      sampleInit family₂ seed₂ normalized₂ :=
  DependentRandomSystem.ofProb_eq_of_flatten_equivalent _ _ equivalent

end Resource

end RandomSystems.CC
