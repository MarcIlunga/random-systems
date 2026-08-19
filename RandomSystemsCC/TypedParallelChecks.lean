/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedParallel
import RandomSystems.StrictContextTotal

/-!
# Acceptance test: `π • (A ∥ B)` is expressible on the `Phi` carrier

Before `RandomSystemsCC.TypedParallel`, the canonical CC statement
`AUT ∥ KEY ⟶ SEC` could not even be *written* on the carrier that holds
every CC endpoint of this estate: `Par` existed only on the strict
`ResourceLift` carrier, which carries no `CC.SecurelyConstructs` judgment.
This module is the worked receipt that the gap is closed, on a concrete
`⊕`-closed universe with two parties:

* `demoAut ∥ demoKey` — a genuine parallel resource on `Phi`;
* `actedComposite` — a **serial** protocol applied to it, the exact shape
  `π • (A ∥ B)`, with `acted_composite_boundary` the kernel-checked
  receipt that the action moves the parallel boundary as its type says;
* `par_resource_in_cc_judgment` — a `CC.SecurelyConstructs` judgment whose
  resources are parallel composites, kernel-checked (the reflexive one);
* the final `example` — the statement shape `AUT ∥ KEY ⟶ SEC` itself,
  with a nontrivial serial protocol and a distinct ideal resource,
  elaborating as a well-formed `Prop`;
* `constant_resources_distinct` / `par_remembers_components` — the
  non-vacuity receipts: a one-query strict test behaviorally separates
  the two components, and `∥` remembers them (`Resource.par_ne_left`,
  i.e. uniqueness of the parallel decomposition).

**What this module does *not* establish.**  No security theorem: the
`SecurelyConstructs` judgment proved here is the reflexive one, and the
final `example` only *elaborates* the target statement, it does not prove
it.  No protocol-side parallel: `Par (Protocol I U)`/`SMulParClass` are
deliberately absent (the parallel action is not non-expanding — STATUS
§11.5).  And no claim that the extraction protocol *equals* the left
component after action — the attach/parallel interchange is future work;
only the boundary receipt is proved about `actedComposite`.
-/

namespace RandomSystemsCC.TypedParallelChecks

noncomputable section

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open scoped AbstractCrypto PFunDDS

/-! ## A `⊕`-closed two-party demo universe -/

/-- Free binary sums over one `Bool` signature. -/
inductive DemoCode : Type
  | base
  | sum (left right : DemoCode)
  deriving DecidableEq

/-- `Bool` at the base; tagged sums at a sum code. -/
def demoAlphabet : DemoCode → Type
  | .base => Bool
  | .sum left right => demoAlphabet left ⊕ demoAlphabet right

/-- The demo universe: codes are free sums, both alphabets are
`demoAlphabet`. -/
def DemoU : SignatureUniverse :=
  ⟨DemoCode, demoAlphabet, demoAlphabet⟩

instance : DecidableEq DemoU.Code :=
  inferInstanceAs (DecidableEq DemoCode)

instance : HasSumCode DemoU where
  sumCode := .sum
  inputEquiv _ _ := Equiv.refl _
  outputEquiv _ _ := Equiv.refl _
  sumCode_inj h := by
    injection h with h₁ h₂
    exact ⟨h₁, h₂⟩

/-- Two parties, so `∥` visibly means "each party holds both resources",
not "twice as many parties". -/
abbrev Interface := Fin 2

/-- Both parties see the base signature. -/
def baseBoundary : Boundary DemoU Interface := fun _ => .base

/-! ## Concrete resources on the `Phi` carrier -/

/-- The total dependent system answering `answer` at every interface. -/
def constantSystem (answer : Bool) : DependentDDS DemoU baseBoundary where
  domain := {history | history ≠ []}
  empty_not_mem := fun absurd => absurd rfl
  prefix_closed := fun _ nonempty _ => nonempty
  output := fun _ _ _ => answer

private theorem single_constant_is_prob_dist (answer : Bool) :
    Dist.isProbDist
      (Finsupp.single (constantSystem answer) (1 : NNReal) :
        DependentPDS DemoU baseBoundary) := by
  show Dist.weight (Finsupp.single (constantSystem answer) (1 : NNReal)) = 1
  rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]

/-- The point-mass law on one constant system. -/
def constantLaw (answer : Bool) : DependentPDS.Prob DemoU baseBoundary :=
  ⟨Finsupp.single (constantSystem answer) 1,
    single_constant_is_prob_dist answer⟩

/-- The constant oracle as an element of the `Phi` carrier. -/
def constantResource (answer : Bool) : Phi Interface DemoU :=
  ⟨baseBoundary, DependentRandomSystem.ofProb (constantLaw answer)⟩

/-- The `AUT` stand-in. -/
abbrev demoAut : Phi Interface DemoU := constantResource true

/-- The `KEY` stand-in. -/
abbrev demoKey : Phi Interface DemoU := constantResource false

/-! ## The composite `A ∥ B` and the serial action `π • (A ∥ B)` -/

/-- **The parallel forms on the `Phi` carrier.** -/
example : Phi Interface DemoU := demoAut ∥ demoKey

/-- The parallel boundary is the sum boundary, definitionally. -/
theorem par_demo_boundary :
    (demoAut ∥ demoKey).boundary = sumBoundary baseBoundary baseBoundary :=
  rfl

/-- The serial extraction converter at Alice's interface: between the sum
code and the base, forwarding a base query into the left slot and reading
either slot's answer back.  A *serial* protocol — exactly what the target
statement needs; no protocol-side `∥` is involved. -/
def extractAtZero : Primitive Interface DemoU 0 :=
  Primitive.ofFunctions (.sum .base .base) .base Sum.inl (Sum.elim id id)

/-- **The acceptance expression**: a serial protocol applied to a genuine
parallel resource, `π • (A ∥ B)`, on the carrier where the CC judgments
live.  This term could not previously be formed. -/
def actedComposite : Phi Interface DemoU :=
  (Pi.mulSingle 0 (Gamma.ofPrimitive extractAtZero) :
      Protocol Interface DemoU) •
    (demoAut ∥ demoKey)

/-- The well-placedness receipt on the composite: the serial protocol is
accepted at the parallel boundary and moves Alice's interface from the sum
code to the base, exactly as its type says. -/
theorem acted_composite_boundary :
    actedComposite.boundary =
      replaceBoundary (sumBoundary baseBoundary baseBoundary) 0
        DemoCode.base := by
  refine boundary_mul_single_smul_of_outCode
    (Gamma.ofPrimitive extractAtZero) (demoAut ∥ demoKey) ?_
  rw [Gamma.outCode_ofPrimitive]
  rfl

/-! ## The CC judgment surface -/

/-- **A `CC.SecurelyConstructs` judgment over parallel composites,
kernel-checked** — the reflexive one, so it carries no security content;
its value is that the judgment now *accepts* parallel resources at all. -/
theorem par_resource_in_cc_judgment :
    CC.SecurelyConstructs (I := Interface)
      (∅ : Set Interface)
      (⊤ : Submonoid (Protocol Interface DemoU))
      1 1 0 (demoAut ∥ demoKey) (demoAut ∥ demoKey) :=
  CC.SecurelyConstructs.refl ∅ ⊤ 1 (demoAut ∥ demoKey)

/-- **The target statement shape, `AUT ∥ KEY ⟶ SEC`, is expressible**: a
dishonest interface set, a simulator monoid, a nontrivial *serial*
protocol, an error budget, the parallel real resource, and an ideal
resource, assembled into the canonical CC judgment.  This `example` only
elaborates — proving such a statement for a real construction is the
follow-up work this axis unblocks. -/
example (budget : ENNReal) (secure : Phi Interface DemoU) : Prop :=
  CC.SecurelyConstructs ({1} : Set Interface)
    (⊤ : Submonoid (Protocol Interface DemoU))
    (Pi.mulSingle 0 (Gamma.ofPrimitive extractAtZero)) 1 budget
    (demoAut ∥ demoKey) secure

/-! ## Non-vacuity: the components are behaviorally distinct, and `∥`
remembers them

Port of the `ChoiceSettingsExample` one-query probe to the demo universe:
without it, `demoAut ∥ demoKey` could secretly be `demoKey ∥ demoKey` and
every receipt above would be about a degenerate composite. -/

/-- The probed global query: Alice's interface, input `true`. -/
def probeQuery : Query DemoU baseBoundary := ⟨0, true⟩

/-- One-query environment: probe, then stop. -/
def probeEnvironment :
    PFunDDS.DDE (Query DemoU baseBoundary) (FlatAnswer DemoU baseBoundary)
  | [] => some probeQuery
  | _ :: _ => none

/-- Accept exactly the one-round transcript whose answer bit is `true`. -/
def probeAccept :
    List (Query DemoU baseBoundary ×
      Option (FlatAnswer DemoU baseBoundary)) → Bool
  | [(_, some answer)] => answer.2
  | _ => false

/-- The one-query bit reader as a CR18 distinguisher. -/
def probeDistinguisher :
    PFunDDS.DDD (Query DemoU baseBoundary)
      (FlatAnswer DemoU baseBoundary) :=
  PFunDDS.DDD.ofDDE probeEnvironment 1 probeAccept

/-- The reader as a strict test. -/
def probeTest :
    StrictContext.Test (Query DemoU baseBoundary)
      (FlatAnswer DemoU baseBoundary) :=
  StrictContextTotal.testOfTruncDDD 2 probeDistinguisher

private theorem constant_system_total (answer : Bool) :
    ∀ inputs : List (Query DemoU baseBoundary), inputs ≠ [] →
      inputs ∈ PFunDDS.dom (DependentDDS.flatten (constantSystem answer)) :=
  fun _ nonempty => nonempty

private theorem transcript_flatten_constant_one (answer : Bool) :
    PFunDDS.transcript (DependentDDS.flatten (constantSystem answer))
        probeEnvironment 1 =
      [(probeQuery, some ⟨0, answer⟩)] := by
  have fires : probeEnvironment
      ((PFunDDS.transcript (DependentDDS.flatten (constantSystem answer))
        probeEnvironment 0)↓ᵧ) = some probeQuery := rfl
  rw [transcript_succ_fire fires]
  have output_probe : PFunDDS.output
      ((DependentDDS.flatten (constantSystem answer))⊥)
      (((PFunDDS.transcript (DependentDDS.flatten (constantSystem answer))
          probeEnvironment 0)↓ₓ) ++ [probeQuery])
      (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
      some ⟨0, answer⟩ :=
    PFunDDS.output_fullyDefined_append_of_mem
      (DependentDDS.flatten (constantSystem answer)) [] probeQuery
      (Or.inr rfl)
      (constant_system_total answer [probeQuery] (by simp))
  rw [output_probe]
  rfl

private theorem true_mem_observe_probe_iff (answer : Bool) :
    true ∈ StrictContext.observe probeTest
        (DependentDDS.flatten (constantSystem answer)) ↔
      answer = true := by
  have toVerdict : true ∈ StrictContext.observe probeTest
        (DependentDDS.flatten (constantSystem answer)) ↔
      PFunDDS.verdict (PFunDDS.truncDDD 2 probeDistinguisher)
        (DependentDDS.flatten (constantSystem answer)) :=
    StrictContextTotal.true_mem_observe_testOfTruncDDD_iff_verdict_of_total
      2 probeDistinguisher _ (constant_system_total answer)
  have dropTrunc : PFunDDS.verdict (PFunDDS.truncDDD 2 probeDistinguisher)
        (DependentDDS.flatten (constantSystem answer)) ↔
      PFunDDS.verdict probeDistinguisher
        (DependentDDS.flatten (constantSystem answer)) :=
    StrictContextTotal.verdict_truncDDD_succ_ofDDE_iff
      probeEnvironment 1 probeAccept _
  have readTranscript : PFunDDS.verdict probeDistinguisher
        (DependentDDS.flatten (constantSystem answer)) ↔
      probeAccept
          (PFunDDS.transcript (DependentDDS.flatten (constantSystem answer))
            probeEnvironment 1) = true :=
    verdict_ofDDE_iff probeEnvironment 1 probeAccept _
  rw [toVerdict, dropTrunc, readTranscript, transcript_flatten_constant_one]
  cases answer <;> exact Iff.rfl

private theorem mass_single_one_of_mem {A : Type*} {point : A}
    {event : A → Prop} (member : event point) :
    Dist.mass (Finsupp.single point (1 : NNReal)) event = 1 := by
  classical
  unfold Dist.mass
  rw [Finsupp.sum_single_index
      (h := fun a weight => if event a then weight else 0) (ite_self 0),
    if_pos member]

private theorem mass_single_one_of_not_mem {A : Type*} {point : A}
    {event : A → Prop} (nonMember : ¬ event point) :
    Dist.mass (Finsupp.single point (1 : NNReal)) event = 0 := by
  classical
  unfold Dist.mass
  rw [Finsupp.sum_single_index
      (h := fun a weight => if event a then weight else 0) (ite_self 0),
    if_neg nonMember]

private theorem accept_mass_probe_constant (answer : Bool) :
    StrictContext.acceptMass probeTest
        (DependentPDS.flatten
          (Finsupp.single (constantSystem answer) 1)) =
      if answer then 1 else 0 := by
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  by_cases accepted : answer = true
  · rw [if_pos accepted]
    exact mass_single_one_of_mem
      ((true_mem_observe_probe_iff answer).mpr accepted)
  · rw [if_neg accepted]
    exact mass_single_one_of_not_mem (fun observed =>
      accepted ((true_mem_observe_probe_iff answer).mp observed))

/-- **The components are behaviorally distinct**: the one-query strict
test separates the constant-`true` and constant-`false` oracles as points
of the quotiented `Phi` carrier. -/
theorem constant_resources_distinct :
    constantResource true ≠ constantResource false := by
  intro same
  have systems :
      DependentRandomSystem.ofProb (constantLaw true) =
        DependentRandomSystem.ofProb (constantLaw false) := by
    injection same
  have equivalent :
      DependentPDS.ContextuallyEquivalent
        (constantLaw true).val (constantLaw false).val :=
    (DependentPDS.Prob.contextual_setoid_rel_iff _ _).mp
      (Quotient.exact systems)
  have masses := equivalent (.test probeTest)
  rw [show (Experiment.test probeTest).acceptMass (constantLaw true).val =
        StrictContext.acceptMass probeTest
          (DependentPDS.flatten (constantLaw true).val) from rfl,
    show (Experiment.test probeTest).acceptMass (constantLaw false).val =
        StrictContext.acceptMass probeTest
          (DependentPDS.flatten (constantLaw false).val) from rfl,
    show (constantLaw true).val = Finsupp.single (constantSystem true) 1
      from rfl,
    show (constantLaw false).val = Finsupp.single (constantSystem false) 1
      from rfl,
    accept_mass_probe_constant, accept_mass_probe_constant] at masses
  simp at masses

/-- **Non-vacuity of `Par (Phi I U)`**: parallel composition remembers its
components — the uniqueness of the parallel decomposition at work on
behaviorally (not just boundary-) distinct components. -/
theorem par_remembers_components :
    demoAut ∥ demoKey ≠ demoKey ∥ demoKey :=
  Resource.par_ne_left constant_resources_distinct

end

end RandomSystemsCC.TypedParallelChecks
