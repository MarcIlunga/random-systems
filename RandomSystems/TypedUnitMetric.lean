/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StepRealization
import RandomSystems.TypedUnitCoherence
import RandomSystems.TypedAction

/-!
# One-interface full abstraction for typed random systems

This module relates the dependent typed experiment metric to the established
fixed-alphabet strict metric when the interface type is `Unit`.  It is not a
CBC-specific bridge: every finite typed experiment, including an arbitrary
chain of stateful `IsDDC` attachments, is compiled into one strict test on the
underlying one-interface resource.

The small `singleView` chart removes the unique interface tag.  Its inverse
direction, `unitChartProtocolAt`, restores that tag with a simple converter.
The central receipt `Experiment.acceptMass_eq_toUnitTestAt` says that context
compilation preserves acceptance mass exactly.  Consequently the full typed
contextual distance is bounded by the strict distance of the local view.

No `Emulable`, rollback-compatibility, memorylessness, or CBC hypothesis is
used.  The result relies only on the selected deterministic converter class:
an arbitrary `ProtocolFn` satisfying `IsDDC`.
-/

namespace RandomSystems.CR18.TypedResource

open PFunConverter
open RandomSystems (Dist)
open scoped Classical ENNReal

noncomputable section

universe c u v

variable {U : SignatureUniverse.{c, u, v}}

/-! ## The one-interface chart -/

/-- Remove the unique interface tag from a dependent query. -/
def untagUnitQuery {boundary : Boundary U Unit} :
    Query U boundary → U.input (boundary ())
  | ⟨(), input⟩ => input

/-- Restore the unique interface tag on a local proper answer. -/
def tagUnitAnswer {boundary : Boundary U Unit} :
    U.output (boundary ()) → FlatAnswer U boundary :=
  fun output => ⟨(), output⟩

/-- The elementary converter that presents a local one-interface resource as
its dependent flattened resource. -/
def unitChartProtocolAt (boundary : Boundary U Unit) :
    ProtocolFn
      (Query U boundary) (FlatAnswer U boundary)
      (U.input (boundary ())) (U.output (boundary ())) :=
  simpleFn untagUnitQuery tagUnitAnswer

/-- `unitChartProtocolAt` is an admissible deterministic converter. -/
def unitChartAt (boundary : Boundary U Unit) :
    {alpha : ProtocolFn
      (Query U boundary) (FlatAnswer U boundary)
      (U.input (boundary ())) (U.output (boundary ())) // IsDDC alpha} := by
  refine ⟨unitChartProtocolAt boundary, ?_⟩
  unfold unitChartProtocolAt
  exact isDDC_simpleFn _ _

/-- Restore the unique interface tag on a local query. -/
def tagUnitQueryAt (boundary : Boundary U Unit)
    (input : U.input (boundary ())) : Query U boundary :=
  ⟨(), input⟩

/-- Remove the unique interface tag from a dependent proper answer. -/
def untagUnitAnswerAt {boundary : Boundary U Unit} :
    FlatAnswer U boundary → U.output (boundary ())
  | ⟨(), output⟩ => output

/-- The inverse elementary chart, from the dependent flattened alphabet back
to the unique local interface. -/
def reverseUnitChartProtocolAt (boundary : Boundary U Unit) :
    ProtocolFn (U.input (boundary ())) (U.output (boundary ()))
      (Query U boundary) (FlatAnswer U boundary) :=
  simpleFn (tagUnitQueryAt boundary) untagUnitAnswerAt

/-- The inverse one-interface chart is an admissible deterministic
converter. -/
def reverseUnitChartAt (boundary : Boundary U Unit) :
    {alpha : ProtocolFn (U.input (boundary ())) (U.output (boundary ()))
      (Query U boundary) (FlatAnswer U boundary) // IsDDC alpha} :=
  ⟨reverseUnitChartProtocolAt boundary,
    isDDC_simpleFn (tagUnitQueryAt boundary) untagUnitAnswerAt⟩

/-- Erase the unique interface tag from a dependent deterministic resource. -/
def DependentDDS.singleView {boundary : Boundary U Unit}
    (system : DependentDDS U boundary) :
    PFunDDS.DDS (U.input (boundary ())) (U.output (boundary ())) :=
  ⟨(fun history =>
      (⟨history.map (fun input =>
          (⟨(), input⟩ : Query U boundary)) ∈ system.domain,
        fun member => system.output
          (history.map fun input => (⟨(), input⟩ : Query U boundary))
          (by
            intro empty
            have historyEmpty : history = [] := List.map_eq_nil_iff.mp empty
            subst history
            exact system.empty_not_mem member) member⟩ :
        Part (U.output (boundary ())))),
    ⟨by
      intro member
      exact system.empty_not_mem member,
     by
      intro left right isPrefix nonempty member
      exact system.prefix_closed (isPrefix.map _) (by simpa) member⟩⟩

/-- Flattening a one-interface dependent resource is exactly application of
the elementary tag-restoring chart to its local view. -/
theorem flatten_eq_apply_unitChartAt {boundary : Boundary U Unit}
    (system : DependentDDS U boundary) :
    system.flatten =
      apply (unitChartProtocolAt boundary) system.singleView := by
  unfold unitChartProtocolAt
  rw [ProtocolFn.apply_simpleFn_eq_simple_apply]
  apply Subtype.ext
  funext history
  rw [DDC.simple_apply]
  have tag_untag (typedHistory : List (Query U boundary)) :
      (typedHistory.map untagUnitQuery).map
        (fun input => (⟨(), input⟩ : Query U boundary)) =
        typedHistory := by
    induction typedHistory with
    | nil => rfl
    | cons query tail induction =>
        rcases query with ⟨interface, input⟩
        cases interface
        simp [untagUnitQuery, induction]
  have history_roundtrip := tag_untag history
  generalize localEquation :
    history.map untagUnitQuery = localHistory at history_roundtrip ⊢
  conv_lhs => rw [← history_roundtrip]
  cases localHistory with
  | nil =>
      apply Part.ext
      intro output
      simp [DependentDDS.flatten, DependentDDS.singleView,
        system.empty_not_mem]
  | cons head tail =>
      apply Part.ext
      rintro ⟨interface, output⟩
      cases interface
      simp [DependentDDS.flatten, DependentDDS.singleView,
        tagUnitAnswer]

/-- Applying the inverse chart to a flattened one-interface resource recovers
its local view exactly. -/
theorem apply_reverseUnitChartAt_flatten
    {boundary : Boundary U Unit} (system : DependentDDS U boundary) :
    apply (reverseUnitChartProtocolAt boundary) system.flatten =
      system.singleView := by
  unfold reverseUnitChartProtocolAt
  rw [ProtocolFn.apply_simpleFn_eq_simple_apply]
  apply Subtype.ext
  funext history
  rw [DDC.simple_apply]
  apply Part.ext'
  · rfl
  · intro left right
    rfl

/-- Probability-law local view at an arbitrary `Unit` boundary. -/
def DependentPDS.singleView {boundary : Boundary U Unit}
    (system : DependentPDS U boundary) :
    PFunPDS (U.input (boundary ())) (U.output (boundary ())) :=
  Dist.fTransform DependentDDS.singleView system

/-- The deterministic chart equation transported to finite-support laws. -/
theorem DependentPDS.flatten_eq_applyLaw_unitChartAt
    {boundary : Boundary U Unit} (system : DependentPDS U boundary) :
    DependentPDS.flatten system =
      StrictContext.applyLaw (unitChartProtocolAt boundary)
        system.singleView := by
  unfold DependentPDS.flatten DependentPDS.singleView StrictContext.applyLaw
  rw [Dist.fTransform_comp]
  apply congrArg (fun function => Dist.fTransform function system)
  funext deterministic
  exact flatten_eq_apply_unitChartAt deterministic

/-- Law-level inverse chart equation. -/
theorem DependentPDS.applyLaw_reverseUnitChartAt_flatten
    {boundary : Boundary U Unit} (system : DependentPDS U boundary) :
    StrictContext.applyLaw (reverseUnitChartProtocolAt boundary)
        (DependentPDS.flatten system) = system.singleView := by
  unfold StrictContext.applyLaw DependentPDS.flatten DependentPDS.singleView
  rw [Dist.fTransform_comp]
  apply congrArg (fun function => Dist.fTransform function system)
  funext deterministic
  exact apply_reverseUnitChartAt_flatten deterministic

/-- Lift a local strict test to an observer on the flattened dependent
alphabet. -/
def localTestAsUnitObserver {boundary : Boundary U Unit}
    (test : StrictContext.Test
      (U.input (boundary ())) (U.output (boundary ()))) :
    StrictContext.Test (Query U boundary) (FlatAnswer U boundary) :=
  StrictContext.absorb test (reverseUnitChartAt boundary)

/-- Lifting a local strict test through the inverse chart preserves its
acceptance mass. -/
theorem acceptMass_localTestAsUnitObserver
    {boundary : Boundary U Unit}
    (test : StrictContext.Test
      (U.input (boundary ())) (U.output (boundary ())))
    (system : DependentPDS U boundary) :
    StrictContext.acceptMass (localTestAsUnitObserver test)
        (DependentPDS.flatten system) =
      StrictContext.acceptMass test system.singleView := by
  calc
    _ = StrictContext.acceptMass test
          (StrictContext.applyLaw (reverseUnitChartProtocolAt boundary)
            (DependentPDS.flatten system)) :=
      (StrictContext.accept_mass_apply test (reverseUnitChartAt boundary)
        (DependentPDS.flatten system)).symm
    _ = _ := congrArg (StrictContext.acceptMass test)
      (DependentPDS.applyLaw_reverseUnitChartAt_flatten system)

@[simp]
theorem DependentPDS.singleView_weight {boundary : Boundary U Unit}
    (system : DependentPDS U boundary) :
    system.singleView.weight = system.weight :=
  Dist.weight_fTransform _ _

/-- The tag-erasing chart is faithful: it is `flatten` composed with an
invertible relabelling, and `flatten` is injective. -/
theorem DependentDDS.singleView_injective {boundary : Boundary U Unit} :
    Function.Injective
      (DependentDDS.singleView (U := U) (boundary := boundary)) := by
  intro left right same
  apply DependentDDS.flatten_injective
  rw [flatten_eq_apply_unitChartAt, flatten_eq_apply_unitChartAt, same]

/-- Over the signed carrier `isProbDist` bundles `NonNeg`, so the weight
equation no longer settles this on its own; faithfulness of the chart does
(`Dist.isProbDist_fTransform_of_injective`), which keeps the statement
unconditional for every caller. -/
theorem DependentPDS.singleView_is_probability_distribution_iff
    {boundary : Boundary U Unit} (system : DependentPDS U boundary) :
    system.singleView.isProbDist ↔ system.isProbDist :=
  Dist.isProbDist_fTransform_of_injective DependentDDS.singleView_injective
    system

/-! ## Attachment and experiment compilation -/

section Attachment

variable [DecidableEq U.Code]

/-- One-interface local view commutes with arbitrary typed attachment. -/
theorem DependentDDS.singleView_attach
    {boundary : Boundary U Unit} {target : U.Code}
    (converter : DeterministicConverter U (boundary ()) target)
    (system : DependentDDS U boundary) :
    (system.attach () converter rfl).singleView =
      apply converter.protocol system.singleView := by
  let code := boundary ()
  have boundaryEquation : boundary = (fun _ : Unit => code) := by
    funext interface
    cases interface
    rfl
  cases boundaryEquation
  exact DependentDDS.unitView_attachUnit converter system

/-- Law-level one-interface local view commutes with arbitrary typed
attachment. -/
theorem DependentPDS.singleView_attach
    {boundary : Boundary U Unit} {target : U.Code}
    (converter : DeterministicConverter U (boundary ()) target)
    (system : DependentPDS U boundary) :
    (DependentPDS.attach () converter rfl system).singleView =
      StrictContext.applyLaw converter.protocol system.singleView := by
  unfold DependentPDS.attach DependentPDS.singleView StrictContext.applyLaw
  rw [Dist.fTransform_comp, Dist.fTransform_comp]
  apply congrArg (fun function => Dist.fTransform function system)
  funext deterministic
  exact deterministic.singleView_attach converter

/-- One-interface local view commutes with attachment when applicability is
supplied by an explicit boundary equality.  This is the transport-stable form
used by heterogeneous AC actions; `singleView_attach` is its literal-`rfl`
special case. -/
theorem DependentPDS.singleView_attach_of_matches
    {boundary : Boundary U Unit} {source target : U.Code}
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary () = source)
    (system : DependentPDS U boundary) :
    (DependentPDS.attach () converter sourceMatches system).singleView =
      StrictContext.applyLaw
        (sourceMatches.symm ▸ converter).protocol system.singleView := by
  cases sourceMatches
  exact DependentPDS.singleView_attach converter system

/-- Compile every finite typed one-interface experiment to one strict test on
the local resource alphabet. -/
def Experiment.toUnitTestAt :
    {boundary : Boundary U Unit} → Experiment Unit U boundary →
    StrictContext.Test (U.input (boundary ())) (U.output (boundary ()))
  | boundary, .test observer =>
      StrictContext.absorb observer (unitChartAt boundary)
  | boundary, .attach () converter sourceMatches next =>
      sourceMatches.symm ▸
        StrictContext.absorb
          (by
            simpa [replaceBoundary] using Experiment.toUnitTestAt next)
          ⟨converter.protocol, converter.isDDC⟩

/-- Compiling a one-interface typed experiment preserves its accepting event
exactly, for every displayed PDS law. -/
theorem Experiment.acceptMass_eq_toUnitTestAt :
    ∀ {boundary : Boundary U Unit}
      (experiment : Experiment Unit U boundary)
      (system : DependentPDS U boundary),
      experiment.acceptMass system =
        StrictContext.acceptMass experiment.toUnitTestAt system.singleView
  | boundary, .test observer, system => by
      change StrictContext.acceptMass observer (DependentPDS.flatten system) =
        StrictContext.acceptMass
          (StrictContext.absorb observer (unitChartAt boundary))
          system.singleView
      rw [DependentPDS.flatten_eq_applyLaw_unitChartAt]
      exact StrictContext.accept_mass_apply observer
        (unitChartAt boundary) system.singleView
  | boundary, .attach () converter sourceMatches next, system => by
      have sourceEquation : boundary () = _ := sourceMatches
      subst sourceEquation
      have proofEquation : sourceMatches = rfl := Subsingleton.elim _ _
      subst proofEquation
      have induction := Experiment.acceptMass_eq_toUnitTestAt next
        (DependentPDS.attach () converter rfl system)
      rw [DependentPDS.singleView_attach] at induction
      let nextTest : StrictContext.Test (U.input _) (U.output _) := by
        simpa [replaceBoundary] using Experiment.toUnitTestAt next
      have induction' :
          next.acceptMass (DependentPDS.attach () converter rfl system) =
            StrictContext.acceptMass nextTest
              (StrictContext.applyLaw converter.protocol system.singleView) := by
        simpa [nextTest, replaceBoundary] using induction
      have absorbed :
          StrictContext.acceptMass nextTest
              (StrictContext.applyLaw converter.protocol system.singleView) =
            StrictContext.acceptMass
              (StrictContext.absorb nextTest
                ⟨converter.protocol, converter.isDDC⟩)
              system.singleView :=
        StrictContext.accept_mass_apply nextTest
          ⟨converter.protocol, converter.isDDC⟩ system.singleView
      rw [absorbed] at induction'
      simpa only [Experiment.acceptMass, Experiment.toUnitTestAt, nextTest]
        using induction'

/-- Equality of one-interface local views already gives equality in the
typed contextual quotient. -/
theorem DependentRandomSystem.of_prob_eq_of_single_view_eq
    {boundary : Boundary U Unit}
    (left right : DependentPDS.Prob U boundary)
    (viewsEqual : left.val.singleView = right.val.singleView) :
    DependentRandomSystem.ofProb left =
      DependentRandomSystem.ofProb right := by
  apply Quotient.sound
  apply (DependentPDS.Prob.contextual_setoid_rel_iff left right).mpr
  intro experiment
  rw [Experiment.acceptMass_eq_toUnitTestAt,
    Experiment.acceptMass_eq_toUnitTestAt, viewsEqual]

/-- Transport-stable version of
`DependentRandomSystem.of_prob_eq_of_single_view_eq` across propositionally
equal one-interface boundaries. -/
theorem DependentRandomSystem.of_prob_heq_of_boundary_eq_of_single_view_heq
    {leftBoundary rightBoundary : Boundary U Unit}
    (boundaryEqual : leftBoundary = rightBoundary)
    (left : DependentPDS.Prob U leftBoundary)
    (right : DependentPDS.Prob U rightBoundary)
    (viewsEqual : HEq left.val.singleView right.val.singleView) :
    HEq (DependentRandomSystem.ofProb left)
      (DependentRandomSystem.ofProb right) := by
  subst rightBoundary
  apply heq_of_eq
  apply DependentRandomSystem.of_prob_eq_of_single_view_eq
  exact eq_of_heq viewsEqual

/-- Every typed one-interface context is represented by a strict local test.
This is the direction needed to transport fixed-alphabet distance bounds into
the selected typed AC metric. -/
theorem DependentPDS.contextualEDist_le_maxEDist_singleView
    {boundary : Boundary U Unit}
    (left right : DependentPDS U boundary) :
    DependentPDS.contextualEDist left right ≤
      StrictContext.maxEDist left.singleView right.singleView := by
  unfold DependentPDS.contextualEDist
  refine iSup_le fun experiment => ?_
  rw [experiment.acceptMass_eq_toUnitTestAt left,
    experiment.acceptMass_eq_toUnitTestAt right]
  exact le_iSup
    (fun test => edist
      (StrictContext.acceptMass test left.singleView)
      (StrictContext.acceptMass test right.singleView))
    experiment.toUnitTestAt

/-- Every local strict test is also represented by a typed one-interface
experiment. -/
theorem DependentPDS.maxEDist_singleView_le_contextualEDist
    {boundary : Boundary U Unit}
    (left right : DependentPDS U boundary) :
    StrictContext.maxEDist left.singleView right.singleView ≤
      DependentPDS.contextualEDist left right := by
  unfold StrictContext.maxEDist
  refine iSup_le fun test => ?_
  rw [← acceptMass_localTestAsUnitObserver test left,
    ← acceptMass_localTestAsUnitObserver test right]
  exact le_iSup
    (fun experiment : Experiment Unit U boundary =>
      edist (experiment.acceptMass left) (experiment.acceptMass right))
    (.test (localTestAsUnitObserver test))

/-- Metric full abstraction for one-interface typed resources: the complete
typed experiment metric is exactly the established strict metric on the
local fixed-alphabet view. -/
theorem DependentPDS.contextualEDist_eq_maxEDist_singleView
    {boundary : Boundary U Unit}
    (left right : DependentPDS U boundary) :
    DependentPDS.contextualEDist left right =
      StrictContext.maxEDist left.singleView right.singleView :=
  le_antisymm
    (DependentPDS.contextualEDist_le_maxEDist_singleView left right)
    (DependentPDS.maxEDist_singleView_le_contextualEDist left right)

end Attachment

end

end RandomSystems.CR18.TypedResource
