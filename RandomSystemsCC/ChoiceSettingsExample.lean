/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.LiftingExample
import RandomSystems.StrictContextTotal
import RandomSystems.TypedFraming
import AbstractCrypto.ChoiceSettings

/-!
# MauRen11 Theorem 2 reached from the concrete typed RS carrier

`AbstractCrypto.ChoiceSettings` proves MauRen11 §7.4, Theorem 2
(`filteredAbstraction_of_local_simulators`) on the selected
`Monoid`/`MulAction` contract.  This module is the reachability regression:
the concrete carrier `RandomSystemsCC.TypedFinite` discharges Theorem 2's
local-simulation premise for a genuine, if minimal, construction, so the
choice-domain/CFR conclusion `R_φ ⊑^π S_ψ` is now available on real
random-systems resources.

The construction: the real resource `R` is offered behind the
output-negating filter `φ = flip` of `RandomSystemsCC.LiftingExample`; the
ideal resource is `S = flip • R` with no filter (`ψ = 1`) and identity
honest-abstraction map (`π = 1`).  The premise's dishonest case is the one
genuine behavioral fact — the simulator `σ = flip` rebuilds raw access to
`R` from `S` because **double output negation is behaviorally invisible**:
`flip • flip • R = R` for *every* resource, proved at the flattened-trace
level through the typed simple-attachment coherence receipt and the
memoryless converter action laws (no admission, no quotient axiom).

Non-vacuity, in the sense of `STATUS.md` §11.2 rule 6: the filtered
specification's settings are inhabited; the filter genuinely acts
(`flip • constantResource false = constantResource true`); and the real and
ideal resources of the concrete receipt are *provably distinct* — a
one-query strict test separates them, so the abstraction is not secretly
reflexivity.
-/

namespace RandomSystemsCC.ChoiceSettingsExample

noncomputable section

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open RandomSystemsCC.LiftingExample (bitSig)
open scoped PFunDDS

/-- `RandomSystemsCC.LiftingExample`'s output-negating converter, this
module's filter and simulator.  (A namespace-local abbreviation, so that the
bare name `flip` is unambiguous against `_root_.flip`.) -/
abbrev flip : Primitive Unit bitSig () := RandomSystemsCC.LiftingExample.flip

/-! ## The negation filter, as a protocol tuple -/

/-- The output-negation filter `φ` (and, in the premise's dishonest case,
the simulator `σ`): `RandomSystemsCC.LiftingExample`'s `flip` converter
installed at the single interface. -/
def flipFilter : Protocol Unit bitSig :=
  fun _ => Gamma.ofPrimitive flip

/-- On the one-interface carrier the tuple `flipFilter` acts exactly as the
bare converter `flip`. -/
theorem flipFilter_smul (R : Phi Unit bitSig) :
    flipFilter • R = flip • R :=
  mul_single_smul () (Gamma.ofPrimitive flip) R

/-! ## The behavioral core: double output negation is invisible -/

/-- The typed simple-attachment coherence receipt, instantiated once at
`flip`: on the one-code signature every boundary is definitionally the same,
so the boundary-wide simple converter is the identity on queries and answer
negation on answers. -/
private theorem flatten_attach_flip {b : Boundary bitSig Unit}
    (d : DependentDDS bitSig b) :
    (d.attach () flip.converter rfl).flatten =
      PFunConverter.apply
        (PFunConverter.simpleFn (fun query => query)
          (fun answer : FlatAnswer bitSig b =>
            (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)))
        d.flatten :=
  DependentDDS.flatten_attach_ofFunctions () b
    (id : bitSig.input () → bitSig.input ()) (fun answer => !answer) rfl
    (fun query => query)
    (fun answer : FlatAnswer bitSig b =>
      (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b))
    (by rintro ⟨i, v⟩ same; rfl)
    (by rintro ⟨i, v⟩ different; exact absurd rfl different)
    (by rintro ⟨i, v⟩ same; rfl)
    (by rintro ⟨i, v⟩ different; exact absurd rfl different)
    d

/-- Attaching the negation converter twice restores every deterministic
dependent system on the nose: flatten both attachments to memoryless simple
converters, compose them, and cancel `!!` pointwise. -/
theorem attach_flip_attach_flip {b : Boundary bitSig Unit}
    (d : DependentDDS bitSig b) :
    (d.attach () flip.converter rfl).attach () flip.converter rfl = d := by
  apply DependentDDS.flatten_injective (sigma := b)
  have inner := flatten_attach_flip d
  have outer := flatten_attach_flip (b := b) (d.attach () flip.converter rfl)
  calc ((d.attach () flip.converter rfl).attach () flip.converter rfl).flatten
      = PFunConverter.apply
          (PFunConverter.simpleFn (fun query => query)
            (fun answer : FlatAnswer bitSig b =>
              (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)))
          ((d.attach () flip.converter rfl).flatten) := outer
    _ = PFunConverter.apply
          (PFunConverter.simpleFn (fun query => query)
            (fun answer : FlatAnswer bitSig b =>
              (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)))
          (PFunConverter.apply
            (PFunConverter.simpleFn (fun query => query)
              (fun answer : FlatAnswer bitSig b =>
                (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)))
            d.flatten) :=
        -- `congrArg`, not `rw`: `inner`'s left side spells the converter as
        -- `ofFunctions`, the goal spells it `flip.converter` (defeq).
        congrArg
          (PFunConverter.apply
            (PFunConverter.simpleFn (fun query => query)
              (fun answer : FlatAnswer bitSig b =>
                (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)))) inner
    _ = DDC.apply
          (DDC.simple (fun query => query)
            (fun answer : FlatAnswer bitSig b =>
              (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)))
          (DDC.apply
            (DDC.simple (fun query => query)
              (fun answer : FlatAnswer bitSig b =>
                (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)))
            d.flatten) := by
          rw [ProtocolFn.apply_simpleFn_eq_simple_apply,
            ProtocolFn.apply_simpleFn_eq_simple_apply]
    _ = DDC.apply
          (DDC.simple
            ((fun query => query) ∘ (fun query => query))
            ((fun answer : FlatAnswer bitSig b =>
                (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)) ∘
              (fun answer : FlatAnswer bitSig b =>
                (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b))))
          d.flatten :=
        DDC.simple_simple_apply _ _ _ _ d.flatten
    _ = DDC.apply (DDC.simple id id) d.flatten := by
        have cancel :
            ((fun answer : FlatAnswer bitSig b =>
                (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b)) ∘
              (fun answer : FlatAnswer bitSig b =>
                (⟨answer.1, !answer.2⟩ : FlatAnswer bitSig b))) =
              (id : FlatAnswer bitSig b → FlatAnswer bitSig b) := by
          funext answer
          show (⟨answer.1, !!answer.2⟩ : FlatAnswer bitSig b) = answer
          rw [Bool.not_not]
        rw [cancel]
        rfl
    _ = d.flatten := DDC.simple_id_id_apply d.flatten

/-- The involution on normalized native laws. -/
theorem prob_attach_flip_attach_flip {b : Boundary bitSig Unit}
    (p : DependentPDS.Prob bitSig b) :
    (p.attach () flip.converter rfl).attach () flip.converter rfl = p := by
  apply Subtype.ext
  show DependentPDS.attach () flip.converter rfl
      (DependentPDS.attach () flip.converter rfl p.val) = p.val
  unfold DependentPDS.attach
  rw [Dist.fTransform_comp]
  have collapse :
      ((fun d : DependentDDS bitSig b => d.attach () flip.converter rfl) ∘
        (fun d : DependentDDS bitSig b => d.attach () flip.converter rfl)) =
        id := by
    funext d
    exact attach_flip_attach_flip d
  -- `exact`, not `rw`: the two composed attachments carry syntactically
  -- different (defeq) boundary indices, which keyed rewriting refuses.
  exact (congrArg (fun f => Dist.fTransform f p.val) collapse).trans
    (Dist.fTransform_id p.val)

/-- **Double negation is invisible on the AC resource carrier**: the `flip`
converter is a behavioral involution on every resource.  This is the genuine
random-systems fact behind the Theorem 2 premise's dishonest case. -/
theorem flip_flip_smul (R : Phi Unit bitSig) :
    flip • (flip • R) = R := by
  obtain ⟨b, sys⟩ := R
  rw [primitive_smul_eq_act, primitive_smul_eq_act,
    Primitive.act_of_matches flip b rfl sys,
    Primitive.act_of_matches flip _ rfl _]
  induction sys using Quotient.inductionOn with
  | _ p =>
    show Resource.mk b
        (DependentRandomSystem.attach () flip.converter rfl
          (DependentRandomSystem.attach () flip.converter rfl
            (DependentRandomSystem.ofProb p))) =
      Resource.mk b (DependentRandomSystem.ofProb p)
    rw [DependentRandomSystem.attach_of_prob,
      DependentRandomSystem.attach_of_prob]
    exact congrArg (Resource.mk b)
      (congrArg DependentRandomSystem.ofProb (prob_attach_flip_attach_flip p))

/-! ## Theorem 2's premise, discharged -/

private theorem patternAttach_unit_of_mem {P : Set Unit} (h : () ∈ P)
    (f : Protocol Unit bitSig) : patternAttach P f = f := by
  funext j
  exact patternAttach_apply_of_mem f h

private theorem patternAttach_unit_of_notMem {P : Set Unit} (h : () ∉ P)
    (f : Protocol Unit bitSig) : patternAttach P f = 1 := by
  funext j
  exact patternAttach_apply_of_notMem f h

/-- MauRen11 §7.4's local ongoing-simulation premise, for every resource and
every honesty pattern at once: at an honest interface the filtered real
resource is the ideal resource by construction, and at a dishonest interface
the simulator `flip` rebuilds raw access to `R` from `S = flip • R` because
double negation is behaviorally invisible. -/
theorem flip_local_simulation (R : Phi Unit bitSig) (P : Set Unit) :
    patternAttach P (1 : Protocol Unit bitSig) •
        patternAttach P flipFilter • R =
      patternAttach Pᶜ flipFilter •
        patternAttach P (1 : Protocol Unit bitSig) • (flip • R) := by
  rw [patternAttach_one, one_smul, one_smul]
  by_cases h : () ∈ P
  · rw [patternAttach_unit_of_mem h,
      patternAttach_unit_of_notMem (Set.notMem_compl_iff.mpr h),
      one_smul]
    exact flipFilter_smul R
  · rw [patternAttach_unit_of_notMem h,
      patternAttach_unit_of_mem (Set.mem_compl h),
      one_smul, flipFilter_smul]
    exact (flip_flip_smul R).symm

/-! ## The receipt: Theorem 2 at the typed carrier -/

/-- **MauRen11 Theorem 2, reached from the concrete typed RS carrier**: the
real resource `R` filtered by output negation is `π`-abstracted (π = 1) by
the negated resource `flip • R` with no ideal filter — the full
choice-domain/CFR conclusion `R_φ ⊑^π S_ψ` of
`AbstractCrypto.ChoiceSettings`, with actual choice domains, completeness,
and the converter-induced graph inclusion, over genuine dependent
random-systems resources. -/
theorem flip_filtered_abstraction (R : Phi Unit bitSig) :
    FilteredAbstraction flipFilter 1 1 R (flip • R) :=
  filteredAbstraction_of_local_simulators (σ := flipFilter)
    (flip_local_simulation R)

/-- The bridge to Definition 11's function form also lands. -/
theorem flip_exists_abstraction (R : Phi Unit bitSig) :
    ∃ ab : (i : Unit) → Gamma Unit bitSig i → Gamma Unit bitSig i,
      ChoiceSpec.Abstraction (filteredSpec R flipFilter)
        (filteredSpec (flip • R) 1) ab :=
  (flip_filtered_abstraction R).exists_abstraction

/-- The filtered specification is inhabited: the full-domain setting on the
real resource is a member. -/
example (R : Phi Unit bitSig) :
    (⟨R, fun _ => Set.univ⟩ :
        ChoiceSetting (Gamma Unit bitSig) (Phi Unit bitSig)) ∈
      (filteredSpec R flipFilter).settings :=
  ⟨rfl, fun _ => Set.subset_univ _⟩

/-! ## Non-vacuity: the filter genuinely acts, on provably distinct resources

The receipt would be worthless if `flip` acted as the identity on the
quotient — the abstraction would then be reflexivity in disguise.  The
witness pair below rules that out: `flip` maps the constant-`false` oracle
to the constant-`true` oracle, and a one-query strict test separates the
two. -/

/-- The single-interface all-`bit` boundary. -/
def unitBoundary : Boundary bitSig Unit := fun _ => ()

/-- The total system answering `answer` on every history. -/
def constantSystem (answer : Bool) : DependentDDS bitSig unitBoundary where
  domain := {history | history ≠ []}
  empty_not_mem := fun absurd => absurd rfl
  prefix_closed := fun _ nonempty _ => nonempty
  output := fun _ _ _ => answer

private theorem single_constant_is_prob_dist (answer : Bool) :
    Dist.isProbDist
      (Finsupp.single (constantSystem answer) (1 : NNReal) :
        DependentPDS bitSig unitBoundary) := by
  show Dist.weight (Finsupp.single (constantSystem answer) (1 : NNReal)) = 1
  rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]

/-- The point-mass law on one constant system. -/
def constantLaw (answer : Bool) : DependentPDS.Prob bitSig unitBoundary :=
  ⟨Finsupp.single (constantSystem answer) 1,
    single_constant_is_prob_dist answer⟩

/-- The constant oracle as an element of the AC carrier. -/
def constantResource (answer : Bool) : Phi Unit bitSig :=
  ⟨unitBoundary, DependentRandomSystem.ofProb (constantLaw answer)⟩

/-- Attaching `flip` to the constant system negates its answer. -/
theorem attach_flip_constant (answer : Bool) :
    (constantSystem answer).attach () flip.converter rfl =
      constantSystem (!answer) := by
  apply DependentDDS.flatten_injective (sigma := unitBoundary)
  refine (flatten_attach_flip (constantSystem answer)).trans ?_
  rw [ProtocolFn.apply_simpleFn_eq_simple_apply]
  apply Subtype.ext
  funext history
  rw [DDC.simple_apply]
  have mapSelf : history.map (fun query => query) = history := List.map_id' _
  rw [mapSelf]
  apply Part.ext'
  · exact Iff.rfl
  · intro leftMember rightMember
    rfl

/-- `flip` maps the constant-`false` oracle to the constant-`true` oracle:
the filter genuinely acts. -/
theorem flip_constant_resource (answer : Bool) :
    flip • constantResource answer = constantResource (!answer) := by
  refine (Primitive.act_of_matches flip unitBoundary rfl
      (DependentRandomSystem.ofProb (constantLaw answer))).trans ?_
  show Resource.mk unitBoundary
      (DependentRandomSystem.attach () flip.converter rfl
        (DependentRandomSystem.ofProb (constantLaw answer))) =
    Resource.mk unitBoundary
      (DependentRandomSystem.ofProb (constantLaw (!answer)))
  rw [DependentRandomSystem.attach_of_prob]
  refine congrArg (Resource.mk unitBoundary)
    (congrArg DependentRandomSystem.ofProb ?_)
  apply Subtype.ext
  show DependentPDS.attach () flip.converter rfl
      (Finsupp.single (constantSystem answer) 1) =
    Finsupp.single (constantSystem (!answer)) 1
  unfold DependentPDS.attach
  show Finsupp.mapDomain _ (Finsupp.single (constantSystem answer) 1) = _
  rw [Finsupp.mapDomain_single, attach_flip_constant]
  rfl

/-! ### The one-query separating test -/

/-- The probed global query: the single interface, input `true`. -/
def probeQuery : Query bitSig unitBoundary := ⟨(), true⟩

/-- One-query environment: probe, then stop. -/
def probeEnvironment :
    PFunDDS.DDE (Query bitSig unitBoundary) (FlatAnswer bitSig unitBoundary)
  | [] => some probeQuery
  | _ :: _ => none

/-- Accept exactly the one-round transcript whose answer bit is `true`. -/
def probeAccept :
    List (Query bitSig unitBoundary ×
      Option (FlatAnswer bitSig unitBoundary)) → Bool
  | [(_, some answer)] => answer.2
  | _ => false

/-- The one-query bit reader as a CR18 distinguisher. -/
def probeDistinguisher :
    PFunDDS.DDD (Query bitSig unitBoundary)
      (FlatAnswer bitSig unitBoundary) :=
  PFunDDS.DDD.ofDDE probeEnvironment 1 probeAccept

/-- The reader as a strict test. -/
def probeTest :
    StrictContext.Test (Query bitSig unitBoundary)
      (FlatAnswer bitSig unitBoundary) :=
  StrictContextTotal.testOfTruncDDD 2 probeDistinguisher

private theorem constant_system_total (answer : Bool) :
    ∀ inputs : List (Query bitSig unitBoundary), inputs ≠ [] →
      inputs ∈ PFunDDS.dom (DependentDDS.flatten (constantSystem answer)) :=
  fun _ nonempty => nonempty

private theorem transcript_flatten_constant_one (answer : Bool) :
    PFunDDS.transcript (DependentDDS.flatten (constantSystem answer))
        probeEnvironment 1 =
      [(probeQuery, some ⟨(), answer⟩)] := by
  have fires : probeEnvironment
      ((PFunDDS.transcript (DependentDDS.flatten (constantSystem answer))
        probeEnvironment 0)↓ᵧ) = some probeQuery := rfl
  rw [transcript_succ_fire fires]
  have output_probe : PFunDDS.output
      ((DependentDDS.flatten (constantSystem answer))⊥)
      (((PFunDDS.transcript (DependentDDS.flatten (constantSystem answer))
          probeEnvironment 0)↓ₓ) ++ [probeQuery])
      (by simp [PFunDDS.fullyDefined, PFunDDS.dom]) =
      some ⟨(), answer⟩ :=
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

/-- Event mass of a point mass at a member point (see
`RandomSystemsCC.TypedDistinguisherChecks.mass_single_one_of_mem` for why
this is stated branchwise). -/
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

/-- **The witness pair is genuinely distinct**: the one-query strict test
separates the constant-`true` and constant-`false` oracles, so the receipt's
real and ideal resources are different points of the quotiented carrier and
the abstraction below is not reflexivity in disguise. -/
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

/-- The Theorem 2 receipt at the concrete witness pair: real and ideal are
the two constant oracles — provably distinct resources — and the negation
filter carries one to the other. -/
theorem constant_filtered_abstraction :
    FilteredAbstraction flipFilter 1 1
      (constantResource false) (constantResource true) := by
  have ideal : flip • constantResource false = constantResource true :=
    flip_constant_resource false
  rw [← ideal]
  exact flip_filtered_abstraction (constantResource false)

end

end RandomSystemsCC.ChoiceSettingsExample
