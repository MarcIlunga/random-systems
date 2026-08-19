/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StrictContext
import RandomSystems.TypedAttachment
import RandomSystems.SemanticRegistry

/-!
# Strict contextual action for typed random systems

This is the behavioral and metric layer of the selected deterministic
RS-to-AC instance.  The operational layer in `TypedAttachment` accepts every
stateful typed `ProtocolFn` satisfying `IsDDC`.  Here observational contexts
are generated independently from:

* a terminal strict deterministic test of the current dependent boundary;
* attachment of any deterministic typed converter, followed by another
  context.

This definition makes closure under converters structural.  It replaces the
old observable-`s⊥` quotient and its `Emulable`/`FrameCompatible`
certificates.  `Part.none` is blocking divergence.  A rejection that permits
continuation must be an ordinary value in the dependent output alphabet.
-/

namespace RandomSystems.CR18

namespace TypedResource

open PFunConverter
open RandomSystems (Dist)
open scoped Classical ENNReal

noncomputable section

universe c i u v

/-! ## Probability-law attachment -/

namespace DependentPDS

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I] [DecidableEq U.Code]

/-- Boundary-independent implementation chart for native dependent laws. -/
def embed {boundary : Boundary U I} (system : DependentPDS U boundary) :
    Dist (PFunDDS.Resource I (AmbientInput U) (AmbientOutput U)) :=
  Dist.fTransform DependentDDS.embed system

theorem embed_injective {boundary : Boundary U I} :
    Function.Injective
      (embed : DependentPDS U boundary →
        Dist (PFunDDS.Resource I (AmbientInput U) (AmbientOutput U))) := by
  intro left right same
  ext deterministic
  change Dist.fTransform DependentDDS.embed left =
    Dist.fTransform DependentDDS.embed right at same
  have point := congrArg
    (fun distribution => distribution deterministic.embed) same
  dsimp only at point
  rw [Dist.fTransform_injective_apply left DependentDDS.embed
      DependentDDS.embed_injective deterministic,
    Dist.fTransform_injective_apply right DependentDDS.embed
      DependentDDS.embed_injective deterministic] at point
  exact_mod_cast point

@[simp]
theorem embed_transport {left right : Boundary U I}
    (same : left = right) (system : DependentPDS U left) :
    embed (cast (congrArg (fun boundary => DependentPDS U boundary) same)
      system) = embed system := by
  cases same
  rfl

theorem heq_of_boundary_eq_of_embed_eq
    {leftBoundary rightBoundary : Boundary U I}
    {left : DependentPDS U leftBoundary}
    {right : DependentPDS U rightBoundary}
    (boundaryEqual : leftBoundary = rightBoundary)
    (embedEqual : embed left = embed right) : HEq left right := by
  subst rightBoundary
  exact heq_of_eq (embed_injective embedEqual)

/-- Push a native finite-support law through deterministic typed attachment. -/
def attach {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentPDS U boundary) :
    DependentPDS U (replaceBoundary boundary interface target) :=
  Dist.fTransform
    (fun deterministic =>
      deterministic.attach interface converter sourceMatches)
    system

@[simp]
theorem attach_weight {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentPDS U boundary) :
    (attach interface converter sourceMatches system).weight = system.weight :=
  Dist.weight_fTransform _ _

/-- Over the signed carrier `isProbDist` bundles `NonNeg` with the weight
equation, so the weight equation alone no longer settles normalization: the
reflecting direction needs the source law to be honest (a pushforward can
merge cancelling signed masses into a non-negative image).  The hypothesis is
free at the only call site, which already holds `isProbDist`. -/
theorem attach_is_probability_distribution_iff {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : DependentPDS U boundary) (nonneg : system.NonNeg) :
    (attach interface converter sourceMatches system).isProbDist ↔
      system.isProbDist :=
  Dist.isProbDist_fTransform _ nonneg

/-- Attachment on a normalized native law. -/
def Prob.attach {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : Prob U boundary) :
    Prob U (replaceBoundary boundary interface target) :=
  ⟨DependentPDS.attach interface converter sourceMatches system.val,
    (attach_is_probability_distribution_iff
      interface converter sourceMatches system.val
      system.property.nonNeg).2 system.property⟩

@[simp]
theorem prob_attach_coe {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    {boundary : Boundary U I} (sourceMatches : boundary interface = source)
    (system : Prob U boundary) :
    (system.attach interface converter sourceMatches).val =
      DependentPDS.attach interface converter sourceMatches system.val :=
  rfl

/-- Distinct native attachments commute as boundary-independent ambient laws. -/
theorem embed_attach_comm
    {source₁ target₁ source₂ target₂ : U.Code}
    {interface₁ interface₂ : I} (different : interface₁ ≠ interface₂)
    (converter₁ : DeterministicConverter U source₁ target₁)
    (converter₂ : DeterministicConverter U source₂ target₂)
    {boundary : Boundary U I}
    (matches₁ : boundary interface₁ = source₁)
    (matches₂ : boundary interface₂ = source₂)
    (system : DependentPDS U boundary) :
    embed
      (attach interface₁ converter₁
        (by simpa [replaceBoundary, different] using matches₁)
        (attach interface₂ converter₂ matches₂ system)) =
    embed
      (attach interface₂ converter₂
        (by
          have reverse : interface₂ ≠ interface₁ := Ne.symm different
          simpa [replaceBoundary, reverse] using matches₂)
        (attach interface₁ converter₁ matches₁ system)) := by
  unfold embed attach
  rw [Dist.fTransform_comp, Dist.fTransform_comp,
    Dist.fTransform_comp, Dist.fTransform_comp]
  exact congrArg (fun function => Dist.fTransform function system)
    (funext fun deterministic =>
      deterministic.embed_attach_comm different converter₁ converter₂
        matches₁ matches₂)

/-- Probability-law typed interchange, with the transport induced by
commuting the two boundary updates. -/
theorem attach_comm
    {source₁ target₁ source₂ target₂ : U.Code}
    {interface₁ interface₂ : I} (different : interface₁ ≠ interface₂)
    (converter₁ : DeterministicConverter U source₁ target₁)
    (converter₂ : DeterministicConverter U source₂ target₂)
    {boundary : Boundary U I}
    (matches₁ : boundary interface₁ = source₁)
    (matches₂ : boundary interface₂ = source₂)
    (system : DependentPDS U boundary) :
    let left :=
      attach interface₁ converter₁
        (by simpa [replaceBoundary, different] using matches₁)
        (attach interface₂ converter₂ matches₂ system)
    let right :=
      attach interface₂ converter₂
        (by
          have reverse : interface₂ ≠ interface₁ := Ne.symm different
          simpa [replaceBoundary, reverse] using matches₂)
        (attach interface₁ converter₁ matches₁ system)
    HEq left right := by
  dsimp only
  apply heq_of_boundary_eq_of_embed_eq
    (replace_boundary_comm boundary different target₁ target₂)
  exact embed_attach_comm different converter₁ converter₂
    matches₁ matches₂ system

theorem Prob.heq_of_boundary_eq_of_val_heq
    {leftBoundary rightBoundary : Boundary U I}
    (boundaryEqual : leftBoundary = rightBoundary)
    {left : Prob U leftBoundary} {right : Prob U rightBoundary}
    (valuesEqual : HEq left.val right.val) : HEq left right := by
  subst rightBoundary
  exact heq_of_eq (Subtype.ext (eq_of_heq valuesEqual))

theorem Prob.attach_comm
    {source₁ target₁ source₂ target₂ : U.Code}
    {interface₁ interface₂ : I} (different : interface₁ ≠ interface₂)
    (converter₁ : DeterministicConverter U source₁ target₁)
    (converter₂ : DeterministicConverter U source₂ target₂)
    {boundary : Boundary U I}
    (matches₁ : boundary interface₁ = source₁)
    (matches₂ : boundary interface₂ = source₂)
    (system : Prob U boundary) :
    HEq
      ((system.attach interface₂ converter₂ matches₂).attach
        interface₁ converter₁
          (by simpa [replaceBoundary, different] using matches₁))
      ((system.attach interface₁ converter₁ matches₁).attach
        interface₂ converter₂
          (by
            have reverse : interface₂ ≠ interface₁ := Ne.symm different
            simpa [replaceBoundary, reverse] using matches₂)) := by
  apply Prob.heq_of_boundary_eq_of_val_heq
    (replace_boundary_comm boundary different target₁ target₂)
  exact DependentPDS.attach_comm different converter₁ converter₂
    matches₁ matches₂ system.val

end DependentPDS

/-! ## Boundary-indexed contextual experiments -/

/-- A finite deterministic observation context at a dependent boundary.
`attach` faces a source-boundary resource, attaches its converter, and then
continues with an experiment at the target boundary. -/
inductive Experiment (I : Type i) (U : SignatureUniverse.{c, u, v})
    [DecidableEq I] :
    Boundary U I → Type (max (max c i) (max u v)) where
  | test {boundary : Boundary U I}
      (observer : StrictContext.Test
        (Query U boundary) (FlatAnswer U boundary)) :
      Experiment I U boundary
  | attach {boundary : Boundary U I} {source target : U.Code}
      (interface : I) (converter : DeterministicConverter U source target)
      (sourceMatches : boundary interface = source)
      (next : Experiment I U
        (replaceBoundary boundary interface target)) :
      Experiment I U boundary

namespace Experiment

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I] [DecidableEq U.Code]

/-- Evaluate a finite context against a native PDS law.  Real-valued,
following `StrictContext.acceptMass` over the signed `Dist` carrier: an
experiment's accepting mass is a `Dist.mass`, and honesty of the law is a
separate hypothesis rather than a property of the carrier. -/
def acceptMass {boundary : Boundary U I} :
    Experiment I U boundary → DependentPDS U boundary → ℝ
  | .test observer, system =>
      StrictContext.acceptMass observer (DependentPDS.flatten system)
  | .attach interface converter sourceMatches next, system =>
      acceptMass next
        (DependentPDS.attach interface converter sourceMatches system)

end Experiment

namespace DependentPDS

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I] [DecidableEq U.Code]
variable {boundary : Boundary U I}

/-- Equality under every finite deterministic typed context. -/
def ContextuallyEquivalent
    (left right : DependentPDS U boundary) : Prop :=
  ∀ experiment : Experiment I U boundary,
    experiment.acceptMass left = experiment.acceptMass right

theorem contextually_equivalent_refl (system : DependentPDS U boundary) :
    ContextuallyEquivalent system system :=
  fun _ => rfl

theorem contextually_equivalent_symm {left right : DependentPDS U boundary}
    (equivalent : ContextuallyEquivalent left right) :
    ContextuallyEquivalent right left :=
  fun experiment => (equivalent experiment).symm

theorem contextually_equivalent_trans
    {left middle right : DependentPDS U boundary}
    (left_middle : ContextuallyEquivalent left middle)
    (middle_right : ContextuallyEquivalent middle right) :
    ContextuallyEquivalent left right :=
  fun experiment => (left_middle experiment).trans (middle_right experiment)

/-- Contextual equivalence is closed under every deterministic typed
attachment by construction. -/
theorem contextually_equivalent_attach {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    {left right : DependentPDS U boundary}
    (equivalent : ContextuallyEquivalent left right) :
    ContextuallyEquivalent
      (attach interface converter sourceMatches left)
      (attach interface converter sourceMatches right) := by
  intro experiment
  exact equivalent
    (.attach interface converter sourceMatches experiment)

/-- Contextual extended distance on native dependent laws. -/
def contextualEDist (left right : DependentPDS U boundary) : ENNReal :=
  ⨆ experiment : Experiment I U boundary,
    edist (experiment.acceptMass left) (experiment.acceptMass right)

theorem contextual_edist_self (system : DependentPDS U boundary) :
    contextualEDist system system = 0 := by
  simp [contextualEDist]

theorem contextual_edist_comm (left right : DependentPDS U boundary) :
    contextualEDist left right = contextualEDist right left := by
  simp only [contextualEDist, edist_comm]

theorem contextual_edist_triangle
    (left middle right : DependentPDS U boundary) :
    contextualEDist left right ≤
      contextualEDist left middle + contextualEDist middle right := by
  unfold contextualEDist
  refine iSup_le fun experiment => ?_
  exact (edist_triangle (experiment.acceptMass left)
      (experiment.acceptMass middle) (experiment.acceptMass right)).trans
    (add_le_add
      (le_iSup (fun current : Experiment I U boundary =>
        edist (current.acceptMass left) (current.acceptMass middle)) experiment)
      (le_iSup (fun current : Experiment I U boundary =>
        edist (current.acceptMass middle) (current.acceptMass right)) experiment))

theorem contextual_edist_eq_of_equivalent
    {left left' right right' : DependentPDS U boundary}
    (leftEquivalent : ContextuallyEquivalent left left')
    (rightEquivalent : ContextuallyEquivalent right right') :
    contextualEDist left right = contextualEDist left' right' := by
  unfold contextualEDist
  apply iSup_congr
  intro experiment
  rw [leftEquivalent experiment, rightEquivalent experiment]

theorem contextual_edist_attach_le {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (left right : DependentPDS U boundary) :
    contextualEDist (attach interface converter sourceMatches left)
        (attach interface converter sourceMatches right) ≤
      contextualEDist left right := by
  unfold contextualEDist
  refine iSup_le fun experiment => ?_
  exact le_iSup
    (fun current : Experiment I U boundary =>
      edist (current.acceptMass left) (current.acceptMass right))
    (.attach interface converter sourceMatches experiment)

theorem contextual_edist_eq_zero_iff
    (left right : DependentPDS U boundary) :
    contextualEDist left right = 0 ↔ ContextuallyEquivalent left right := by
  constructor
  · intro zero experiment
    have bounded :
        edist (experiment.acceptMass left) (experiment.acceptMass right) ≤
          contextualEDist left right :=
      le_iSup (fun current : Experiment I U boundary =>
        edist (current.acceptMass left) (current.acceptMass right)) experiment
    rw [zero] at bounded
    exact edist_eq_zero.mp (bot_unique bounded)
  · intro equivalent
    apply le_antisymm
    · unfold contextualEDist
      refine iSup_le fun experiment => ?_
      rw [equivalent experiment, edist_self]
    · exact bot_le

/-- The strict contextual setoid on normalized native laws. -/
abbrev Prob.contextualSetoid {I : Type i} (U : SignatureUniverse)
    [DecidableEq I] [DecidableEq U.Code]
    (boundary : Boundary U I) : Setoid (Prob U boundary) where
  r left right := ContextuallyEquivalent left.val right.val
  iseqv := ⟨
    fun system => contextually_equivalent_refl system.val,
    fun equivalent => contextually_equivalent_symm equivalent,
    fun left_middle middle_right =>
      contextually_equivalent_trans left_middle middle_right⟩

theorem Prob.contextual_setoid_rel_iff
    (left right : Prob U boundary) :
    (@Setoid.r _ (Prob.contextualSetoid U boundary)) left right ↔
      ContextuallyEquivalent left.val right.val :=
  by
    simp only [Setoid.r]

end DependentPDS

/-! ## Contextual behavior fibres and heterogeneous carrier -/

/-- The mathematical typed resource at one boundary: normalized native PDS
presentations quotiented by every finite deterministic typed context. -/
def DependentRandomSystem {I : Type i} (U : SignatureUniverse)
    [DecidableEq I] [DecidableEq U.Code] (boundary : Boundary U I) : Type _ :=
  Quotient (DependentPDS.Prob.contextualSetoid U boundary)

namespace DependentRandomSystem

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I] [DecidableEq U.Code]
variable {boundary : Boundary U I}

def ofProb (system : DependentPDS.Prob U boundary) :
    DependentRandomSystem U boundary :=
  Quotient.mk (DependentPDS.Prob.contextualSetoid U boundary) system

def contextualEDist
    (left right : DependentRandomSystem U boundary) : ENNReal :=
  Quotient.liftOn₂ left right
    (fun left right => DependentPDS.contextualEDist left.val right.val)
    (fun left right left' right' leftEquivalent rightEquivalent => by
      have leftEquivalent' :
          DependentPDS.ContextuallyEquivalent left.val left'.val := by
        exact (DependentPDS.Prob.contextual_setoid_rel_iff
          left left').mp leftEquivalent
      have rightEquivalent' :
          DependentPDS.ContextuallyEquivalent right.val right'.val := by
        exact (DependentPDS.Prob.contextual_setoid_rel_iff
          right right').mp rightEquivalent
      exact DependentPDS.contextual_edist_eq_of_equivalent
        leftEquivalent' rightEquivalent')

instance instPseudoEMetricSpace :
    PseudoEMetricSpace (DependentRandomSystem U boundary) where
  edist := contextualEDist
  edist_self system := Quotient.inductionOn system fun representative =>
    DependentPDS.contextual_edist_self representative.val
  edist_comm left right := Quotient.inductionOn₂ left right fun left right =>
    DependentPDS.contextual_edist_comm left.val right.val
  edist_triangle left middle right :=
    Quotient.inductionOn₃ left middle right fun left middle right =>
      DependentPDS.contextual_edist_triangle left.val middle.val right.val

@[simp]
theorem edist_of_prob (left right : DependentPDS.Prob U boundary) :
    edist (ofProb left) (ofProb right) =
      DependentPDS.contextualEDist left.val right.val :=
  rfl

/-- At a fixed dependent boundary, zero contextual distance is exactly
equality of the contextual quotient. -/
theorem edist_eq_zero_iff_eq
    (left right : DependentRandomSystem U boundary) :
    edist left right = 0 ↔ left = right := by
  constructor
  · intro zero
    induction left using Quotient.inductionOn with
    | _ left =>
        induction right using Quotient.inductionOn with
        | _ right =>
            apply Quotient.sound
            exact (DependentPDS.contextual_edist_eq_zero_iff
              left.val right.val).mp zero
  · rintro rfl
    exact edist_self _

def attach {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (resource : DependentRandomSystem U boundary) :
    DependentRandomSystem U
      (replaceBoundary boundary interface target) :=
  Quotient.liftOn resource
    (fun system => ofProb
      (system.attach interface converter sourceMatches))
    (fun left right equivalent => by
      apply Quotient.sound
      have equivalent' :
          DependentPDS.ContextuallyEquivalent left.val right.val := by
        exact (DependentPDS.Prob.contextual_setoid_rel_iff
          left right).mp equivalent
      apply (DependentPDS.Prob.contextual_setoid_rel_iff _ _).mpr
      exact DependentPDS.contextually_equivalent_attach
        interface converter sourceMatches equivalent')

@[simp]
theorem attach_of_prob {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentPDS.Prob U boundary) :
    attach interface converter sourceMatches (ofProb system) =
      ofProb (system.attach interface converter sourceMatches) :=
  rfl

theorem edist_attach_le {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (left right : DependentRandomSystem U boundary) :
    edist (attach interface converter sourceMatches left)
        (attach interface converter sourceMatches right) ≤ edist left right := by
  induction left using Quotient.inductionOn with
  | _ left =>
      induction right using Quotient.inductionOn with
      | _ right =>
          exact DependentPDS.contextual_edist_attach_le
            interface converter sourceMatches left.val right.val

theorem attach_lipschitz_with_one {source target : U.Code}
    (interface : I) (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source) :
    LipschitzWith 1
      (attach interface converter sourceMatches) :=
  LipschitzWith.of_edist_le
    (edist_attach_le interface converter sourceMatches)

theorem of_prob_heq_of_boundary_eq
    {leftBoundary rightBoundary : Boundary U I}
    (boundaryEqual : leftBoundary = rightBoundary)
    {left : DependentPDS.Prob U leftBoundary}
    {right : DependentPDS.Prob U rightBoundary}
    (representativesEqual : HEq left right) :
    HEq (ofProb left) (ofProb right) := by
  subst rightBoundary
  exact heq_of_eq (congrArg ofProb (eq_of_heq representativesEqual))

end DependentRandomSystem

/-- Heterogeneous contextual resources over every dependent boundary. -/
structure Resource (I : Type i) (U : SignatureUniverse)
    [DecidableEq I] [DecidableEq U.Code] where
  boundary : Boundary U I
  system : DependentRandomSystem U boundary

namespace Resource

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I] [DecidableEq U.Code]

/-- Package a finite-support law at a known boundary as a heterogeneous
resource.  Every construction site previously spelled `⟨boundary, ofProb S⟩` by
hand — 60+ occurrences across ten `RandomSystemsCC` modules — even though the
boundary is already determined by the law's own type.  The coercion recovers it
from `DependentPDS.Prob U boundary` instead of asking the caller to repeat it. -/
instance instCoeTCProbResource {boundary : Boundary U I} :
    CoeTC (DependentPDS.Prob U boundary) (Resource I U) where
  coe system := ⟨boundary, DependentRandomSystem.ofProb system⟩

@[simp]
theorem coe_prob_boundary {boundary : Boundary U I}
    (system : DependentPDS.Prob U boundary) :
    (system : Resource I U).boundary = boundary := rfl

@[simp]
theorem coe_prob_system {boundary : Boundary U I}
    (system : DependentPDS.Prob U boundary) :
    (system : Resource I U).system = DependentRandomSystem.ofProb system := rfl

def boundaryEdist (left right : Resource I U) : ENNReal :=
  match left, right with
  | ⟨leftBoundary, leftSystem⟩, ⟨rightBoundary, rightSystem⟩ =>
      if same : leftBoundary = rightBoundary then
        edist (same ▸ leftSystem) rightSystem
      else
        ⊤

@[simp]
theorem boundary_edist_same (boundary : Boundary U I)
    (left right : DependentRandomSystem U boundary) :
    boundaryEdist (Resource.mk boundary left) (Resource.mk boundary right) =
      edist left right := by
  simp [boundaryEdist]

theorem boundary_edist_ne {leftBoundary rightBoundary : Boundary U I}
    (different : leftBoundary ≠ rightBoundary)
    (left : DependentRandomSystem U leftBoundary)
    (right : DependentRandomSystem U rightBoundary) :
    boundaryEdist (Resource.mk leftBoundary left)
      (Resource.mk rightBoundary right) = ⊤ := by
  simp [boundaryEdist, different]

instance instPseudoEMetricSpace : PseudoEMetricSpace (Resource I U) where
  edist := boundaryEdist
  edist_self := by
    rintro ⟨boundary, system⟩
    simp [boundaryEdist]
  edist_comm := by
    rintro ⟨leftBoundary, leftSystem⟩ ⟨rightBoundary, rightSystem⟩
    by_cases same : leftBoundary = rightBoundary
    · subst rightBoundary
      simp [boundaryEdist, edist_comm]
    · have reverse : rightBoundary ≠ leftBoundary := Ne.symm same
      simp [boundaryEdist, same, reverse]
  edist_triangle := by
    rintro ⟨leftBoundary, leftSystem⟩
      ⟨middleBoundary, middleSystem⟩
      ⟨rightBoundary, rightSystem⟩
    by_cases leftMiddle : leftBoundary = middleBoundary
    · subst middleBoundary
      by_cases leftRight : leftBoundary = rightBoundary
      · subst rightBoundary
        simpa [boundaryEdist] using
          edist_triangle leftSystem middleSystem rightSystem
      · simp [boundaryEdist, leftRight]
    · by_cases middleRight : middleBoundary = rightBoundary
      · subst rightBoundary
        simp [boundaryEdist, leftMiddle]
      · by_cases leftRight : leftBoundary = rightBoundary
        · subst rightBoundary
          simp [boundaryEdist, leftMiddle, middleRight]
        · simp [boundaryEdist, leftMiddle, middleRight, leftRight]

@[simp]
theorem edist_same (boundary : Boundary U I)
    (left right : DependentRandomSystem U boundary) :
    edist (Resource.mk boundary left) (Resource.mk boundary right) =
      edist left right :=
  boundary_edist_same boundary left right

theorem edist_ne {leftBoundary rightBoundary : Boundary U I}
    (different : leftBoundary ≠ rightBoundary)
    (left : DependentRandomSystem U leftBoundary)
    (right : DependentRandomSystem U rightBoundary) :
    edist (Resource.mk leftBoundary left)
      (Resource.mk rightBoundary right) = ⊤ :=
  boundary_edist_ne different left right

/-- Across the heterogeneous carrier, zero distance also coincides with
equality: unequal boundaries are at infinite distance and each fibre is the
separated contextual quotient. -/
theorem edist_eq_zero_iff_eq (left right : Resource I U) :
    edist left right = 0 ↔ left = right := by
  constructor
  · intro zero
    rcases left with ⟨leftBoundary, leftSystem⟩
    rcases right with ⟨rightBoundary, rightSystem⟩
    by_cases same : leftBoundary = rightBoundary
    · subst rightBoundary
      rw [edist_same] at zero
      have systemsEqual :=
        (DependentRandomSystem.edist_eq_zero_iff_eq
          leftSystem rightSystem).mp zero
      subst rightSystem
      rfl
    · rw [edist_ne same] at zero
      simp at zero
  · rintro rfl
    exact edist_self _

end Resource

/-! ## Total deterministic primitives -/

@[rs_rule "rs.typed.primitive" rs_primitive random_systems]
structure Primitive (I : Type i) (U : SignatureUniverse)
    [DecidableEq I] [DecidableEq U.Code] (interface : I) where
  source : U.Code
  target : U.Code
  converter : DeterministicConverter U source target

namespace Primitive

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I] [DecidableEq U.Code]

/-- An arbitrary history-sensitive local program as a total AC-facing
primitive.  Applicability is carried by its source code; no global boundary
vector is baked into the primitive. -/
def ofHistory {interface : I} (source target : U.Code)
    (protocol : ProtocolFn
      (U.input target) (U.output target)
      (U.input source) (U.output source))
    (isDDC : IsDDC protocol) : Primitive I U interface where
  source := source
  target := target
  converter := DeterministicConverter.ofHistory protocol isDDC

/-- Ergonomic one-query local program. -/
def ofFunctions {interface : I} (source target : U.Code)
    (query : U.input target → U.input source)
    (answer : U.output source → U.output target) :
    Primitive I U interface where
  source := source
  target := target
  converter := DeterministicConverter.ofFunctions query answer

@[rs_rule "rs.typed.primitive_action" rs_typed_resource random_systems]
def act {interface : I} (primitive : Primitive I U interface) :
    Resource I U → Resource I U
  | ⟨boundary, system⟩ =>
      if sourceMatches : boundary interface = primitive.source then
        ⟨replaceBoundary boundary interface primitive.target,
          DependentRandomSystem.attach interface primitive.converter
            sourceMatches system⟩
      else
        ⟨boundary, system⟩

theorem act_of_matches {interface : I}
    (primitive : Primitive I U interface)
    (boundary : Boundary U I)
    (sourceMatches : boundary interface = primitive.source)
    (system : DependentRandomSystem U boundary) :
    primitive.act ⟨boundary, system⟩ =
      ⟨replaceBoundary boundary interface primitive.target,
        DependentRandomSystem.attach interface primitive.converter
          sourceMatches system⟩ := by
  simp [act, sourceMatches]

theorem act_of_not_matches {interface : I}
    (primitive : Primitive I U interface)
    (boundary : Boundary U I)
    (sourceMismatch : boundary interface ≠ primitive.source)
    (system : DependentRandomSystem U boundary) :
    primitive.act ⟨boundary, system⟩ = ⟨boundary, system⟩ := by
  simp [act, sourceMismatch]

@[rs_rule "rs.typed.primitive_nonexpanding" distance_bound random_systems]
theorem edist_act_le {interface : I}
    (primitive : Primitive I U interface)
    (left right : Resource I U) :
    edist (primitive.act left) (primitive.act right) ≤ edist left right := by
  rcases left with ⟨leftBoundary, leftSystem⟩
  rcases right with ⟨rightBoundary, rightSystem⟩
  by_cases same : leftBoundary = rightBoundary
  · subst rightBoundary
    by_cases sourceMatches : leftBoundary interface = primitive.source
    · rw [act_of_matches primitive leftBoundary sourceMatches leftSystem,
        act_of_matches primitive leftBoundary sourceMatches rightSystem,
        Resource.edist_same, Resource.edist_same]
      exact DependentRandomSystem.edist_attach_le
        interface primitive.converter sourceMatches leftSystem rightSystem
    · rw [act_of_not_matches primitive leftBoundary sourceMatches leftSystem,
        act_of_not_matches primitive leftBoundary sourceMatches rightSystem]
  · rw [Resource.edist_ne same]
    exact le_top

theorem act_lipschitz_with_one {interface : I}
    (primitive : Primitive I U interface) :
    LipschitzWith 1 primitive.act :=
  LipschitzWith.of_edist_le primitive.edist_act_le

theorem act_comm {interface₁ interface₂ : I}
    (different : interface₁ ≠ interface₂)
    (primitive₁ : Primitive I U interface₁)
    (primitive₂ : Primitive I U interface₂)
    (resource : Resource I U) :
    primitive₁.act (primitive₂.act resource) =
      primitive₂.act (primitive₁.act resource) := by
  rcases resource with ⟨boundary, system⟩
  by_cases matches₁ : boundary interface₁ = primitive₁.source
  · by_cases matches₂ : boundary interface₂ = primitive₂.source
    · induction system using Quotient.inductionOn with
      | _ system =>
          rw [act_of_matches primitive₂ boundary matches₂,
            act_of_matches primitive₁
              (replaceBoundary boundary interface₂ primitive₂.target)
              (by simpa [replaceBoundary, different] using matches₁),
            act_of_matches primitive₁ boundary matches₁,
            act_of_matches primitive₂
              (replaceBoundary boundary interface₁ primitive₁.target)
              (by
                have reverse : interface₂ ≠ interface₁ := Ne.symm different
                simpa [replaceBoundary, reverse] using matches₂)]
          rw [Resource.mk.injEq]
          refine ⟨replace_boundary_comm boundary different
            primitive₁.target primitive₂.target, ?_⟩
          apply DependentRandomSystem.of_prob_heq_of_boundary_eq
            (replace_boundary_comm boundary different
              primitive₁.target primitive₂.target)
          exact DependentPDS.Prob.attach_comm different
            primitive₁.converter primitive₂.converter
            matches₁ matches₂ system
    · rw [act_of_not_matches primitive₂ boundary matches₂,
        act_of_matches primitive₁ boundary matches₁]
      have after₁Mismatch :
          replaceBoundary boundary interface₁ primitive₁.target interface₂ ≠
            primitive₂.source := by
        simpa [replaceBoundary, Ne.symm different] using matches₂
      rw [act_of_not_matches primitive₂
        (replaceBoundary boundary interface₁ primitive₁.target)
        after₁Mismatch]
  · by_cases matches₂ : boundary interface₂ = primitive₂.source
    · rw [act_of_matches primitive₂ boundary matches₂]
      have after₂Mismatch :
          replaceBoundary boundary interface₂ primitive₂.target interface₁ ≠
            primitive₁.source := by
        simpa [replaceBoundary, different] using matches₁
      rw [act_of_not_matches primitive₁
          (replaceBoundary boundary interface₂ primitive₂.target)
          after₂Mismatch,
        act_of_not_matches primitive₁ boundary matches₁,
        act_of_matches primitive₂ boundary matches₂]
    · rw [act_of_not_matches primitive₂ boundary matches₂]
      rw [act_of_not_matches primitive₁ boundary matches₁]
      rw [act_of_not_matches primitive₂ boundary matches₂]

end Primitive

end

end TypedResource

end RandomSystems.CR18
