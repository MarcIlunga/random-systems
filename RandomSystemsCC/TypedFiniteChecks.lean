/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedFinite
import RandomSystems.EmulateRealization
import CC.MPC

/-!
# Completion gates for the deterministic typed RS → AC instance

These are hostile, generic compile-time receipts rather than an application.
In particular `probeFn` is a deterministic DDC that is formally not
`Emulable`; admitting it into `Gamma` prevents the former transactional
restriction from returning unnoticed.
-/

namespace RandomSystemsCC.TypedFiniteChecks

noncomputable section

open AbstractCrypto
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto

/-! ## A genuinely dependent two-interface signature universe -/

inductive Code
  | bit
  | rich
  | committed
  deriving DecidableEq

abbrev testUniverse : SignatureUniverse where
  Code := Code
  input
    | .bit => Bool
    | .rich => Fin 3
    | .committed => Unit
  output
    | .bit => Bool
    | .rich => Option Bool
    | .committed => Option Bool

instance : DecidableEq testUniverse.Code := by
  change DecidableEq Code
  infer_instance

abbrev Interface := Fin 2

def bitBoundary : Boundary testUniverse Interface := fun _ => .bit

/-! ## Exact current-AC contract -/

def model : Model where
  Interface := Interface
  signatures := testUniverse
  finiteInterface := inferInstance
  interfaceDecidableEq := inferInstance
  codeDecidableEq := inferInstance

/-- No algebraic or metric assumptions occur in the downstream context: the
configured RS model installed them globally. -/
example : ∀ interface, Monoid (model.Gamma interface) :=
  fun _ => inferInstance

example : MulAction model.Protocol model.Phi :=
  inferInstance

example : PseudoEMetricSpace model.Phi :=
  inferInstance

example : IsNonexpandingSMul model.Protocol model.Phi :=
  inferInstance

/-! ## Ordinary functions and dependent signature change -/

def changeAtZero : Primitive Interface testUniverse (0 : Interface) :=
  Primitive.ofFunctions .bit .rich
    (fun index => index = 0)
    some

theorem change_at_zero_has_advertised_boundary
    (system : DependentRandomSystem testUniverse bitBoundary) :
    changeAtZero.act ⟨bitBoundary, system⟩ =
      ⟨replaceBoundary bitBoundary 0 .rich,
        DependentRandomSystem.attach 0 changeAtZero.converter rfl system⟩ :=
  Primitive.act_of_matches changeAtZero bitBoundary rfl system

/-! ## Arbitrary state, divergence, and the old probe/reset boundary -/

def queryLimitAtZero : Primitive Interface testUniverse (0 : Interface) :=
  Primitive.ofHistory .bit .bit (queryLimitFn 3) (isDDC_queryLimitFn 3)

def probeIsDDC : IsDDC probeFn :=
  ⟨answersInY_probeFn, 2, answersWithin_probeFn⟩

def probeAtZero : Primitive Interface testUniverse (0 : Interface) :=
  Primitive.ofHistory .bit .bit probeFn probeIsDDC

/-- The converter excluded by the old observable-completion seam is a
generator of the selected instance. -/
noncomputable def probeInGamma :
    Gamma Interface testUniverse (0 : Interface) :=
  Gamma.ofPrimitive probeAtZero

example : ¬ Emulable probeFn := not_emulable_probeFn

theorem probe_diverges_after_successful_inner_answer :
    probeFn ([true], [some false]) = Part.none := by
  simp [probeFn]

/-! ## Committed rejection is data, not rollback -/

/-- `none` here is a proper value of the resource output type `Option Bool`.
The partiality of the DDS remains the outer `Part`; hence the next history is
still defined. -/
def committedThenReply : PFunDDS.DDS Unit (Option Bool) :=
  PFunDDS.historyEvaluator fun history _ =>
    if history.length = 1 then none else some true

theorem committed_rejection_is_a_proper_first_answer :
    (none : Option Bool) ∈ committedThenReply.1 [Unit.unit] := by
  simp [committedThenReply, PFunDDS.historyEvaluator]

theorem continuation_after_committed_rejection_is_defined :
    (some true : Option Bool) ∈
      committedThenReply.1 [Unit.unit, Unit.unit] := by
  simp [committedThenReply, PFunDDS.historyEvaluator]

/-! ## Serial and distinct-interface laws -/

def flipAtZero : Primitive Interface testUniverse (0 : Interface) :=
  Primitive.ofFunctions .bit .bit id not

def idAtZero : Primitive Interface testUniverse (0 : Interface) :=
  Primitive.ofFunctions .bit .bit id id

def idAtOne : Primitive Interface testUniverse (1 : Interface) :=
  Primitive.ofFunctions .bit .bit id id

theorem ordinary_serial_is_ac_multiplication
    (resource : Phi Interface testUniverse) :
    ((Pi.mulSingle 0 (Gamma.ofPrimitive flipAtZero) :
          Protocol Interface testUniverse) *
        Pi.mulSingle 0 (Gamma.ofPrimitive idAtZero)) • resource =
      flipAtZero.act (idAtZero.act resource) :=
  primitive_mul_smul flipAtZero idAtZero resource

theorem distinct_interfaces_commute (resource : Phi Interface testUniverse) :
    changeAtZero.act (idAtOne.act resource) =
      idAtOne.act (changeAtZero.act resource) :=
  Primitive.act_comm (by decide) changeAtZero idAtOne resource

/-! ## AC construction notation -/

theorem generic_constructs_receipt (resource : Phi Interface testUniverse) :
    ({resource} : Set (Phi Interface testUniverse))
      —[Pi.mulSingle 0 (Gamma.ofPrimitive changeAtZero)]→
    ({changeAtZero.act resource} : Set (Phi Interface testUniverse)) :=
  primitive_constructs changeAtZero resource

/-- The same configured carrier is consumed directly by ordinary CC; no
additional algebraic or metric instance is installed here. -/
theorem generic_cc_receipt (resource : Phi Interface testUniverse) :
    CC.SecurelyConstructs (I := Interface)
      (∅ : Set Interface)
      (⊤ : Submonoid (Protocol Interface testUniverse))
      1 1 0 resource resource :=
  CC.SecurelyConstructs.refl (I := Interface) ∅ ⊤ 1 resource

/-- The exact indexed carrier is also a direct `CC.MPC` instance.  This is a
generic hierarchy receipt, not an application-specific security claim. -/
theorem generic_mpc_receipt (protocol : Protocol Interface testUniverse)
    (resource : Phi Interface testUniverse) :
    ConstructsForAll (I := Interface) protocol
      (fun _ => ({resource} : Set (Phi Interface testUniverse)))
      (fun dishonest =>
        ({patternAttach dishonestᶜ protocol • resource} :
          Set (Phi Interface testUniverse))) := by
  classical
  intro dishonest
  exact constructs_singleton_iff.mpr rfl

/-! ## Well-placedness: the word-level dropout is rejected

A converter word carries a type, and `outCode` computes it.  Before this
receipt existed, a word whose factors did not line up silently dropped the
mismatched factor and still produced a *provable* construction theorem whose
protocol label named a converter that never fired — substantive, and wrong.
-/

open ConverterTerm

/-- `changeAtZero : bit → rich` runs first, so the `bit`-sourced `flipAtZero`
placed after it can never fire.  The word is therefore **not** well placed. -/
theorem dropout_word_outCode_eq_none :
    (mul (prim flipAtZero) (prim changeAtZero)).outCode (bitBoundary 0) = none := by
  simp [ConverterTerm.outCode, bitBoundary, flipAtZero, changeAtZero,
    Primitive.ofFunctions]

theorem dropout_word_is_not_well_placed :
    ¬ (mul (prim flipAtZero) (prim changeAtZero)).WellPlaced (bitBoundary 0) := by
  simp [ConverterTerm.WellPlaced, dropout_word_outCode_eq_none]

/-- The dropout made visible: the ill-placed word acts as its right factor
alone, so `flipAtZero` contributes nothing while still appearing in the
protocol label.  This is the claim `WellPlaced` now blocks. -/
theorem dropout_word_acts_as_right_factor_only
    (resource : Phi Interface testUniverse) :
    (eval (mul (prim flipAtZero) (prim changeAtZero))).val resource =
      (eval (prim changeAtZero)).val resource := by
  show flipAtZero.act (changeAtZero.act resource) = changeAtZero.act resource
  rcases resource with ⟨boundary, system⟩
  by_cases matches0 : boundary 0 = Code.bit
  · rw [Primitive.act_of_matches changeAtZero boundary matches0]
    exact Primitive.act_of_not_matches flipAtZero _
      (by rw [replace_boundary_same]; decide) _
  · rw [Primitive.act_of_not_matches changeAtZero boundary matches0,
      Primitive.act_of_not_matches flipAtZero boundary matches0]

/-- A single primitive at the wrong code is rejected too. -/
theorem mismatched_primitive_is_not_well_placed :
    ¬ (prim flipAtZero).WellPlaced Code.rich := by
  simp [ConverterTerm.WellPlaced, ConverterTerm.outCode, flipAtZero,
    Primitive.ofFunctions]

/-- The positive case: a word whose factors line up **is** well placed, and the
receipt then says it moves the boundary exactly as its type advertises. -/
theorem aligned_word_is_well_placed :
    (mul (prim flipAtZero) (prim idAtZero)).WellPlaced (bitBoundary 0) := by
  simp [ConverterTerm.WellPlaced, ConverterTerm.outCode, bitBoundary,
    flipAtZero, idAtZero, Primitive.ofFunctions]

/-- The receipt in use: `changeAtZero` is well placed at `bit` and lands the
boundary at `rich`, exactly as its type says. -/
theorem well_placed_word_moves_boundary_as_typed
    (system : DependentRandomSystem testUniverse bitBoundary) :
    ((eval (prim changeAtZero)).val ⟨bitBoundary, system⟩).boundary =
      replaceBoundary bitBoundary 0 Code.rich :=
  ConverterTerm.boundary_eval_of_outCode _ ⟨bitBoundary, system⟩
    (by simp [ConverterTerm.outCode, bitBoundary, changeAtZero,
      Primitive.ofFunctions])

end

end RandomSystemsCC.TypedFiniteChecks
