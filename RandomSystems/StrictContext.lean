/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ComposeRealization
import RandomSystems.PDS
import RandomSystems.SemanticRegistry

/-!
# Strict contextual behavior for partial random systems

This is the completion-free observational seam used by the deterministic
RS-to-AC instance.  A test is an arbitrary stateful `IsDDC` protocol that is
triggered once and either returns a Boolean verdict or remains undefined.
`Part.none` is divergence and has no continuation.  A committed rejection is
therefore represented in the resource's ordinary answer alphabet, not by
deleting an input and replaying from an earlier history.

The central theorem is structural context absorption: testing `alpha S` is
literally testing `S` with the serial composite of the test and `alpha`.
Consequently every deterministic `IsDDC` converter respects contextual
equivalence and is one-Lipschitz.  No `Emulable` hypothesis occurs.
-/

namespace RandomSystems.CR18.StrictContext

open RandomSystems (Dist)
open RandomSystems.CR18.PFunConverter
open scoped Classical ENNReal

noncomputable section

universe a b u v w z

variable {U : Type u} {V : Type v} {X : Type w} {Y : Type z}
variable {W : Type a} {Z : Type b}

/-- A finite strict deterministic observation context. -/
abbrev Test (X : Type u) (Y : Type v) :=
  {test : ProtocolFn Unit Bool X Y // IsDDC test}

/-- The partial verdict of a strict test on one deterministic resource. -/
def observe (test : Test X Y) (system : PFunDDS.DDS X Y) : Part Bool :=
  applyRaw test.val system [Unit.unit]

/-- Acceptance mass of a possibly diverging test against a PDS law. -/
def acceptMass (test : Test X Y) (system : PFunPDS X Y) : ℝ :=
  system.mass fun deterministic => true ∈ observe test deterministic

/-- Apply a deterministic protocol to every deterministic resource sample. -/
def applyLaw (converter : ProtocolFn U V X Y) (system : PFunPDS X Y) :
    PFunPDS U V :=
  Dist.fTransform (PFunConverter.apply converter) system

@[simp]
theorem apply_law_weight (converter : ProtocolFn U V X Y)
    (system : PFunPDS X Y) :
    (applyLaw converter system).weight = system.weight :=
  Dist.weight_fTransform _ _

theorem apply_law_is_probability_distribution_iff
    (converter : ProtocolFn U V X Y) {system : PFunPDS X Y}
    (hsystem : system.NonNeg) :
    (applyLaw converter system).isProbDist ↔ system.isProbDist :=
  Dist.isProbDist_fTransform _ hsystem

/-- Applying the identity restriction converter to a law is exactly the
corresponding prefix-closed domain restriction. -/
theorem apply_law_restrictionFn
    (P : List X → Prop) [DecidablePred P] (hP : PrefixClosed P)
    (system : PFunPDS X Y) :
    applyLaw (restrictionFn P) system = PFunPDS.filterDom P hP system := by
  unfold applyLaw PFunPDS.filterDom
  apply congrArg (fun function => Dist.fTransform function system)
  funext deterministic
  exact apply_restrictionFn P hP deterministic

/-- The transcript-level query counter, lifted pointwise to probability
laws, is exactly the canonical `[q]` restriction. -/
theorem apply_law_queryLimitFn (q : Nat) (system : PFunPDS X Y) :
    applyLaw (queryLimitFn q) system = PFunPDS.filterQueries q system := by
  unfold applyLaw PFunPDS.filterQueries
  apply congrArg (fun function => Dist.fTransform function system)
  funext deterministic
  exact apply_queryLimitFn q deterministic

/-- Serial protocol application is literal pushforward composition.  The
outer `AnswersInY` clause is exactly the hypothesis of the underlying causal
interaction-associativity theorem. -/
theorem apply_law_comp
    (outer : ProtocolFn W Z U V) (inner : ProtocolFn U V X Y)
    (system : PFunPDS X Y) (outerAnswers : AnswersInY outer) :
    applyLaw (comp outer inner) system =
      applyLaw outer (applyLaw inner system) := by
  unfold applyLaw
  rw [Dist.fTransform_comp]
  congr 1
  funext deterministic
  exact apply_comp outer inner deterministic outerAnswers

/-- Compile an arbitrary deterministic converter into a strict test. -/
def absorb (test : Test U V)
    (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha}) : Test X Y :=
  ⟨comp test.val converter.val,
    serial_composition_is_ddc test.property converter.property⟩

/-- Exact deterministic context absorption. -/
theorem observe_absorb (test : Test U V)
    (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha})
    (system : PFunDDS.DDS X Y) :
    observe test (PFunConverter.apply converter.val system) =
      observe (absorb test converter) system := by
  unfold observe absorb
  have action := apply_comp test.val converter.val system test.property.1
  exact congrArg
    (fun result : PFunDDS.DDS Unit Bool => result.val [Unit.unit])
    action.symm

/-- Distribution-level context absorption. -/
theorem accept_mass_apply (test : Test U V)
    (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha})
    (system : PFunPDS X Y) :
    acceptMass test (applyLaw converter.val system) =
      acceptMass (absorb test converter) system := by
  unfold acceptMass applyLaw
  rw [Dist.mass_fTransform]
  apply Dist.mass_congr
  intro deterministic
  rw [observe_absorb]

/-- Equality under every finite strict deterministic observation. -/
def Equivalent (left right : PFunPDS X Y) : Prop :=
  ∀ test : Test X Y, acceptMass test left = acceptMass test right

theorem equivalent_refl (system : PFunPDS X Y) : Equivalent system system :=
  fun _ => rfl

theorem equivalent_symm {left right : PFunPDS X Y}
    (equivalent : Equivalent left right) : Equivalent right left :=
  fun test => (equivalent test).symm

theorem equivalent_trans {left middle right : PFunPDS X Y}
    (left_middle : Equivalent left middle)
    (middle_right : Equivalent middle right) : Equivalent left right :=
  fun test => (left_middle test).trans (middle_right test)

/-- Every deterministic stateful `IsDDC` converter preserves strict
contextual equivalence. -/
theorem equivalent_apply
    (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha})
    {left right : PFunPDS X Y} (equivalent : Equivalent left right) :
    Equivalent (applyLaw converter.val left) (applyLaw converter.val right) := by
  intro test
  rw [accept_mass_apply, accept_mass_apply]
  exact equivalent (absorb test converter)

/-- Strict contextual extended distance on displayed PDS laws. -/
def maxEDist (left right : PFunPDS X Y) : ENNReal :=
  ⨆ test : Test X Y, edist (acceptMass test left) (acceptMass test right)

theorem max_edist_self (system : PFunPDS X Y) : maxEDist system system = 0 := by
  simp [maxEDist]

theorem max_edist_comm (left right : PFunPDS X Y) :
    maxEDist left right = maxEDist right left := by
  simp only [maxEDist, edist_comm]

theorem max_edist_triangle (left middle right : PFunPDS X Y) :
    maxEDist left right ≤ maxEDist left middle + maxEDist middle right := by
  unfold maxEDist
  refine iSup_le fun test => ?_
  exact (edist_triangle (acceptMass test left) (acceptMass test middle)
      (acceptMass test right)).trans
    (add_le_add
      (le_iSup (fun current : Test X Y =>
        edist (acceptMass current left) (acceptMass current middle)) test)
      (le_iSup (fun current : Test X Y =>
        edist (acceptMass current middle) (acceptMass current right)) test))

theorem max_edist_eq_of_equivalent
    {left left' right right' : PFunPDS X Y}
    (left_equivalent : Equivalent left left')
    (right_equivalent : Equivalent right right') :
    maxEDist left right = maxEDist left' right' := by
  unfold maxEDist
  apply iSup_congr
  intro test
  rw [left_equivalent test, right_equivalent test]

theorem max_edist_apply_le
    (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha})
    (left right : PFunPDS X Y) :
    maxEDist (applyLaw converter.val left) (applyLaw converter.val right) ≤
      maxEDist left right := by
  unfold maxEDist
  refine iSup_le fun test => ?_
  rw [accept_mass_apply, accept_mass_apply]
  exact le_iSup
    (fun current : Test X Y =>
      edist (acceptMass current left) (acceptMass current right))
    (absorb test converter)

/-- The contextual relation is exactly the zero kernel of strict distance. -/
theorem max_edist_eq_zero_iff (left right : PFunPDS X Y) :
    maxEDist left right = 0 ↔ Equivalent left right := by
  constructor
  · intro zero test
    have bounded :
        edist (acceptMass test left) (acceptMass test right) ≤
          maxEDist left right :=
      le_iSup (fun current : Test X Y =>
        edist (acceptMass current left) (acceptMass current right)) test
    rw [zero] at bounded
    exact edist_eq_zero.mp (bot_unique bounded)
  · intro equivalent
    apply le_antisymm
    · unfold maxEDist
      refine iSup_le fun test => ?_
      rw [equivalent test, edist_self]
    · exact bot_le

/-- The setoid on normalized PDS presentations. -/
def equivalentSetoid (X : Type u) (Y : Type v) :
    Setoid (PFunPDS.Prob X Y) where
  r left right := Equivalent left.val right.val
  iseqv := ⟨
    fun system => equivalent_refl system.val,
    fun equivalent => equivalent_symm equivalent,
    fun left_middle middle_right =>
      equivalent_trans left_middle middle_right⟩

/-- The mathematical strict behavior type of a normalized partial random
system.  PDS is a presentation; equality is finite contextual observation. -/
def System (X : Type u) (Y : Type v) : Type (max u v) :=
  Quotient (equivalentSetoid X Y)

namespace System

/-- Insert a normalized PDS presentation into strict behavior. -/
def ofProb (system : PFunPDS.Prob X Y) : System X Y :=
  Quotient.mk (equivalentSetoid X Y) system

/-- Strict contextual distance descends to behavior classes. -/
def contextualEDist (left right : System X Y) : ENNReal :=
  Quotient.liftOn₂ left right
    (fun left right => maxEDist left.val right.val)
    (fun _ _ _ _ left_equivalent right_equivalent =>
      max_edist_eq_of_equivalent left_equivalent right_equivalent)

noncomputable instance instPseudoEMetricSpace :
    PseudoEMetricSpace (System X Y) where
  edist := contextualEDist
  edist_self system := Quotient.inductionOn system fun representative =>
    max_edist_self representative.val
  edist_comm left right := Quotient.inductionOn₂ left right fun left right =>
    max_edist_comm left.val right.val
  edist_triangle left middle right :=
    Quotient.inductionOn₃ left middle right fun left middle right =>
      max_edist_triangle left.val middle.val right.val

@[simp]
theorem edist_of_prob (left right : PFunPDS.Prob X Y) :
    edist (ofProb left) (ofProb right) = maxEDist left.val right.val :=
  rfl

/-- The strict quotient has no residual zero-distance identifications:
contextual equivalence was already absorbed into carrier equality. -/
theorem edist_eq_zero_iff_eq (left right : System X Y) :
    edist left right = 0 ↔ left = right := by
  constructor
  · intro zero
    induction left using Quotient.inductionOn with
    | _ left =>
        induction right using Quotient.inductionOn with
        | _ right =>
            apply Quotient.sound
            exact (max_edist_eq_zero_iff left.val right.val).mp zero
  · rintro rfl
    exact edist_self _

/-- Apply every deterministic stateful `IsDDC` converter to strict behavior. -/
def apply (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha}) :
    System X Y → System U V :=
  fun resource => Quotient.liftOn resource
    (fun system => ofProb ⟨applyLaw converter.val system.val,
      (apply_law_is_probability_distribution_iff
        converter.val system.property.nonNeg).2 system.property⟩)
    (fun _ _ equivalent => Quotient.sound
      (equivalent_apply converter equivalent))

@[simp]
theorem apply_of_prob
    (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha})
    (system : PFunPDS.Prob X Y) :
    apply converter (ofProb system) =
      ofProb ⟨applyLaw converter.val system.val,
        (apply_law_is_probability_distribution_iff
          converter.val system.property.nonNeg).2 system.property⟩ :=
  rfl

theorem edist_apply_le
    (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha})
    (left right : System X Y) :
    edist (apply converter left) (apply converter right) ≤ edist left right := by
  induction left using Quotient.inductionOn with
  | _ left =>
      induction right using Quotient.inductionOn with
      | _ right =>
          exact max_edist_apply_le converter left.val right.val

theorem lipschitz_apply
    (converter : {alpha : ProtocolFn U V X Y // IsDDC alpha}) :
    LipschitzWith 1 (apply converter : System X Y → System U V) :=
  LipschitzWith.of_edist_le (edist_apply_le converter)

/-- Same-interface serial coherence on strict behavior. -/
theorem apply_serial
    (outer : {alpha : ProtocolFn W Z U V // IsDDC alpha})
    (inner : {beta : ProtocolFn U V X Y // IsDDC beta})
    (resource : System X Y) :
    apply
        ⟨comp outer.val inner.val,
          serial_composition_is_ddc outer.property inner.property⟩ resource =
      apply outer (apply inner resource) := by
  induction resource using Quotient.inductionOn with
  | _ representative =>
      apply Quotient.sound
      change Equivalent
        (applyLaw (comp outer.val inner.val) representative.val)
        (applyLaw outer.val (applyLaw inner.val representative.val))
      rw [apply_law_comp outer.val inner.val representative.val
        outer.property.1]
      exact equivalent_refl _

end System

end

end RandomSystems.CR18.StrictContext
