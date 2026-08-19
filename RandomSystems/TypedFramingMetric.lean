/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedAction
import RandomSystems.TypedFraming

/-!
# Metric full abstraction for arbitrary-interface typed resources

Every finite typed experiment can be compiled to one strict test on the
flattened global boundary. The compiler uses the all-interface frame from
`TypedFraming`, so it supports the complete deterministic converter class:
arbitrary history-sensitive `ProtocolFn`s certified by `IsDDC`.

Consequently, typed contextual distance is exactly strict distinguishing
distance after flattening. No finiteness assumption on the interface type,
converter subclass, or application-specific hypothesis is introduced here.
-/

namespace RandomSystems.CR18.TypedResource

open PFunConverter
open RandomSystems (Dist)
open scoped Classical ENNReal

noncomputable section

universe c i u v

variable {I : Type i} {U : SignatureUniverse.{c, u, v}}
variable [DecidableEq I] [DecidableEq U.Code]

namespace DependentPDS

/-- Deterministic framing coherence lifts pointwise to finite-support laws. -/
theorem flatten_attach_eq_apply_law_framed
    {boundary : Boundary U I} {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentPDS U boundary) :
    DependentPDS.flatten
        (DependentPDS.attach interface converter sourceMatches system) =
      StrictContext.applyLaw
        (TypedFraming.framedConverter
          interface boundary converter sourceMatches).val
        (DependentPDS.flatten system) := by
  unfold DependentPDS.flatten DependentPDS.attach StrictContext.applyLaw
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  apply congrArg (fun function => Dist.fTransform function system)
  funext deterministic
  exact DependentDDS.flatten_attach_eq_apply_framed
    interface boundary converter sourceMatches deterministic

end DependentPDS

namespace Experiment

/-- Compile a finite boundary-indexed typed experiment to one strict test on
the flattened source boundary. -/
def toFlattenTest :
    {boundary : Boundary U I} → Experiment I U boundary →
      StrictContext.Test (Query U boundary) (FlatAnswer U boundary)
  | _, .test observer => observer
  | boundary, .attach interface converter sourceMatches next =>
      TypedFraming.frameTest interface boundary converter sourceMatches
        (toFlattenTest next)

/-- Compiling a typed experiment preserves its accepting mass exactly. -/
theorem accept_mass_eq_to_flatten_test :
    ∀ {boundary : Boundary U I}
      (experiment : Experiment I U boundary)
      (system : DependentPDS U boundary),
      experiment.acceptMass system =
        StrictContext.acceptMass (toFlattenTest experiment)
          (DependentPDS.flatten system)
  | _, .test observer, system => rfl
  | _, .attach interface converter sourceMatches next, system => by
      have induction := accept_mass_eq_to_flatten_test next
        (DependentPDS.attach interface converter sourceMatches system)
      rw [DependentPDS.flatten_attach_eq_apply_law_framed
        interface converter sourceMatches system] at induction
      have absorbed := StrictContext.accept_mass_apply
        (toFlattenTest next)
        (TypedFraming.framedConverter
          interface _ converter sourceMatches)
        (DependentPDS.flatten system)
      rw [absorbed] at induction
      simpa only [Experiment.acceptMass, toFlattenTest,
        TypedFraming.frameTest] using induction

end Experiment

namespace DependentPDS

/-- Typed contextual distance is at most strict distance after flattening. -/
theorem contextual_edist_le_max_edist_flatten
    {boundary : Boundary U I}
    (left right : DependentPDS U boundary) :
    contextualEDist left right ≤
      StrictContext.maxEDist (flatten left) (flatten right) := by
  unfold contextualEDist
  refine iSup_le fun experiment => ?_
  rw [Experiment.accept_mass_eq_to_flatten_test experiment left,
    Experiment.accept_mass_eq_to_flatten_test experiment right]
  exact le_iSup
    (fun test => edist
      (StrictContext.acceptMass test (flatten left))
      (StrictContext.acceptMass test (flatten right)))
    (Experiment.toFlattenTest experiment)

/-- Every strict flattened test is already a terminal typed experiment. -/
theorem max_edist_flatten_le_contextual_edist
    {boundary : Boundary U I}
    (left right : DependentPDS U boundary) :
    StrictContext.maxEDist (flatten left) (flatten right) ≤
      contextualEDist left right := by
  unfold StrictContext.maxEDist
  refine iSup_le fun test => ?_
  exact le_iSup
    (fun experiment : Experiment I U boundary =>
      edist (experiment.acceptMass left) (experiment.acceptMass right))
    (.test test)

/-- Full abstraction: the native typed contextual metric is exactly strict
distinguishing distance on the flattened global law. -/
theorem contextual_edist_eq_max_edist_flatten
    {boundary : Boundary U I}
    (left right : DependentPDS U boundary) :
    contextualEDist left right =
      StrictContext.maxEDist (flatten left) (flatten right) :=
  le_antisymm
    (contextual_edist_le_max_edist_flatten left right)
    (max_edist_flatten_le_contextual_edist left right)

end DependentPDS

/-- **Strict-flattened equivalence upcast**: if two normalized dependent
laws have strictly equivalent flattened laws, their contextual classes are
equal.  This is the direct quotient lift of the experiment compiler;
callers should not repeat that plumbing. -/
theorem DependentRandomSystem.ofProb_eq_of_flatten_equivalent
    {boundary : Boundary U I}
    (left right : DependentPDS.Prob U boundary)
    (equivalent :
      StrictContext.Equivalent
        (DependentPDS.flatten left.val)
        (DependentPDS.flatten right.val)) :
    DependentRandomSystem.ofProb left =
      DependentRandomSystem.ofProb right := by
  apply Quotient.sound
  apply (DependentPDS.Prob.contextual_setoid_rel_iff left right).mpr
  intro experiment
  rw [Experiment.accept_mass_eq_to_flatten_test,
    Experiment.accept_mass_eq_to_flatten_test]
  exact equivalent experiment.toFlattenTest

/-! ## The identity converter is idle, all the way up to the total action

`DependentDDS.attach_ofFunctions_id_heq` (`TypedFraming.lean`) says a
memoryless *bijection* converter with identity maps changes nothing
deterministically.  Pushing that through the eager-randomness pushforward
(`Dist.fTransform`), the normalization subtype and the contextual quotient
gives the statement the algebra actually wants: on the **heterogeneous
carrier**, where attachment is total and the boundary is bundled, the
identity converter's action is the identity function
(`Primitive.act_ofFunctions_id`) — a plain equation with no transport
visible, because the mismatch branch and the boundary update are both
discharged inside. -/

section IdentityConverter

/-- A law-level pushforward along a boundary-changing step that is
heterogeneously the identity is heterogeneously the identity. -/
theorem DependentPDS.heq_fTransform_of_boundary_eq
    {left right : Boundary U I} (boundaries : left = right)
    (step : DependentDDS U left → DependentDDS U right)
    (pointwise : ∀ system, HEq (step system) system)
    (law : DependentPDS U left) :
    HEq (Dist.fTransform step law) law := by
  subst boundaries
  have identity : step = id := funext fun system => eq_of_heq (pointwise system)
  rw [identity]
  exact heq_of_eq (Dist.fTransform_id law)

/-- The identity converter is idle on finite-support laws. -/
theorem DependentPDS.attach_ofFunctions_id_heq {boundary : Boundary U I}
    (interface : I) (law : DependentPDS U boundary) :
    HEq (DependentPDS.attach interface
        (DeterministicConverter.ofFunctions
          (id : U.input (boundary interface) → U.input (boundary interface))
          (id : U.output (boundary interface) → U.output (boundary interface)))
        rfl law) law :=
  DependentPDS.heq_fTransform_of_boundary_eq
    (replace_boundary_self boundary interface).symm _
    (fun system =>
      DependentDDS.attach_ofFunctions_id_heq interface boundary system) law

/-- The identity converter is idle on normalized laws. -/
theorem DependentPDS.Prob.attach_ofFunctions_id_heq {boundary : Boundary U I}
    (interface : I) (law : DependentPDS.Prob U boundary) :
    HEq (law.attach interface
        (DeterministicConverter.ofFunctions
          (id : U.input (boundary interface) → U.input (boundary interface))
          (id : U.output (boundary interface) → U.output (boundary interface)))
        rfl) law :=
  DependentPDS.Prob.heq_of_boundary_eq_of_val_heq
    (replace_boundary_self boundary interface)
    (DependentPDS.attach_ofFunctions_id_heq interface law.val)

/-- The identity converter is idle on the contextual quotient. -/
theorem DependentRandomSystem.attach_ofFunctions_id_heq
    {boundary : Boundary U I} (interface : I)
    (resource : DependentRandomSystem U boundary) :
    HEq (DependentRandomSystem.attach interface
        (DeterministicConverter.ofFunctions
          (id : U.input (boundary interface) → U.input (boundary interface))
          (id : U.output (boundary interface) → U.output (boundary interface)))
        rfl resource) resource := by
  induction resource using Quotient.inductionOn with
  | _ law =>
      exact DependentRandomSystem.of_prob_heq_of_boundary_eq
        (replace_boundary_self boundary interface)
        (DependentPDS.Prob.attach_ofFunctions_id_heq interface law)

/-- Resources at propositionally equal boundaries are equal on the
heterogeneous carrier as soon as their systems agree heterogeneously. -/
theorem Resource.mk_eq_mk_of_heq {left right : Boundary U I}
    (boundaries : left = right)
    {leftSystem : DependentRandomSystem U left}
    {rightSystem : DependentRandomSystem U right}
    (systems : HEq leftSystem rightSystem) :
    Resource.mk left leftSystem = Resource.mk right rightSystem := by
  subst boundaries
  rw [eq_of_heq systems]

/-- **The identity converter is idle** (total form, Maurer11 Def. 1's
carrier): the primitive whose local program is the memoryless identity
acts as the identity on every resource.  No side condition: on a
nonmatching interface the action is already the identity, and on a
matching one the boundary update installs the code the interface already
advertises. -/
theorem Primitive.act_ofFunctions_id {interface : I} (code : U.Code)
    (resource : Resource I U) :
    (Primitive.ofFunctions code code
        (id : U.input code → U.input code)
        (id : U.output code → U.output code) :
      Primitive I U interface).act resource = resource := by
  rcases resource with ⟨boundary, system⟩
  by_cases advertises : boundary interface = code
  · subst advertises
    rw [Primitive.act_of_matches _ boundary rfl system]
    exact Resource.mk_eq_mk_of_heq (replace_boundary_self boundary interface)
      (DependentRandomSystem.attach_ofFunctions_id_heq interface system)
  · exact Primitive.act_of_not_matches _ boundary advertises system

end IdentityConverter

end

end RandomSystems.CR18.TypedResource
