/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.TypedDistinguisher
import RandomSystemsCC.TypedFiniteChecks

/-!
# Non-vacuity gates for the strict-observation distinguisher class

An empty or degenerate test set would make `edistD ≡ 0` and every theorem
over it true and worthless.  These receipts exhibit, on the concrete
two-interface Boolean carrier of `TypedFiniteChecks`, a resource pair and a
single admitted test separating them with class distance exactly `1` — for
the full class **and** for its `q = 2` budgeted subclass, using one and the
same one-query truncated CR18 reader.

The witness resources are the two constant total systems (always answer
`false` / always answer `true`); the witness test probes interface `0` once
and accepts the returned bit.  Because the systems are total, the acceptance
mass is computed through the totality bridge
(`true_mem_observe_testOfTruncDDD_iff_verdict_of_total`) and one transcript
step — no bespoke drive analysis.
-/

namespace RandomSystemsCC.TypedDistinguisherChecks

noncomputable section

open AbstractCrypto
open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.TypedResource
open RandomSystemsCC.TypedFinite
open RandomSystemsCC.TypedFiniteChecks
open RandomSystemsCC.TypedDistinguisher
open scoped ENNReal PFunDDS

/-! ## The witness resources: two constant total systems -/

/-- The total dependent resource answering `answer` at every interface on
every history. -/
def constantSystem (answer : Bool) :
    DependentDDS testUniverse bitBoundary where
  domain := {history | history ≠ []}
  empty_not_mem := fun absurd => absurd rfl
  prefix_closed := fun _ nonempty _ => nonempty
  output := fun _ _ _ => answer

theorem constant_system_total (answer : Bool) :
    ∀ inputs : List (Query testUniverse bitBoundary), inputs ≠ [] →
      inputs ∈ PFunDDS.dom (DependentDDS.flatten (constantSystem answer)) :=
  fun _ nonempty => nonempty

theorem single_constant_is_prob_dist (answer : Bool) :
    Dist.isProbDist
      (Finsupp.single (constantSystem answer) (1 : NNReal) :
        DependentPDS testUniverse bitBoundary) := by
  show Dist.weight (Finsupp.single (constantSystem answer) (1 : NNReal)) = 1
  rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_single_index rfl]

/-- The point-mass normalized law on one constant system. -/
def constantLaw (answer : Bool) :
    DependentPDS.Prob testUniverse bitBoundary :=
  ⟨Finsupp.single (constantSystem answer) 1,
    single_constant_is_prob_dist answer⟩

/-- The witness resource pair, as elements of the AC carrier. -/
def witnessResource (answer : Bool) : Phi Interface testUniverse :=
  ⟨bitBoundary, DependentRandomSystem.ofProb (constantLaw answer)⟩

/-! ## The witness test: a one-query truncated CR18 reader -/

/-- The probed global query: interface `0`, input `true`. -/
def probeQuery : Query testUniverse bitBoundary := ⟨0, true⟩

/-- One-query environment: probe, then stop. -/
def probeEnvironment :
    PFunDDS.DDE (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary)
  | [] => some probeQuery
  | _ :: _ => none

/-- Accept exactly the one-round transcript whose proper answer bit is
`true`. -/
def probeAccept :
    List (Query testUniverse bitBoundary ×
      Option (FlatAnswer testUniverse bitBoundary)) → Bool
  | [(_, some answer)] => answer.2
  | _ => false

/-- The one-query bit reader as a CR18 distinguisher. -/
def probeDistinguisher :
    PFunDDS.DDD (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary) :=
  PFunDDS.DDD.ofDDE probeEnvironment 1 probeAccept

/-- The reader truncated at budget `2`, as a strict test — an admitted
member of both the full and the budgeted class. -/
def probeTest :
    StrictContext.Test (Query testUniverse bitBoundary)
      (FlatAnswer testUniverse bitBoundary) :=
  StrictContextTotal.testOfTruncDDD 2 probeDistinguisher

/-! ## Evaluating the test on the witness pair -/

theorem transcript_flatten_constant_one (answer : Bool) :
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

theorem true_mem_observe_probe_iff (answer : Bool) :
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

/-- Event mass of a point mass, on the branch where the point is in the event.
Stated as the two branches rather than one indicator: `Dist.mass` bakes in the
classical instance of `Dist.lean`, so an `if` in the *statement* would demand a
`DecidablePred` the caller cannot supply for an `observe` predicate — and
supplying one would not be the instance inside `mass` anyway (DESIGN §4 item
1).  Every consumer splits on the branch regardless. -/
theorem mass_single_one_of_mem {A : Type*} {point : A} {event : A → Prop}
    (member : event point) :
    Dist.mass (Finsupp.single point (1 : NNReal)) event = 1 := by
  classical
  unfold Dist.mass
  rw [Finsupp.sum_single_index (h := fun a weight => if event a then weight else 0)
      (ite_self 0), if_pos member]

/-- Event mass of a point mass, on the branch where the point is outside the
event.  See `mass_single_one_of_mem` for why this is two lemmas. -/
theorem mass_single_one_of_not_mem {A : Type*} {point : A} {event : A → Prop}
    (nonMember : ¬ event point) :
    Dist.mass (Finsupp.single point (1 : NNReal)) event = 0 := by
  classical
  unfold Dist.mass
  rw [Finsupp.sum_single_index (h := fun a weight => if event a then weight else 0)
      (ite_self 0), if_neg nonMember]

theorem accept_mass_probe_constant (answer : Bool) :
    StrictContext.acceptMass probeTest
        (DependentPDS.flatten (Finsupp.single (constantSystem answer) 1)) =
      if answer then 1 else 0 := by
  unfold StrictContext.acceptMass DependentPDS.flatten
  rw [Dist.mass_fTransform]
  by_cases accepted : answer = true
  -- `exact`, not `rw`: `rw` elaborates its argument first, so the membership
  -- proof `true ∈ observe …` would fix `point := true` instead of reading the
  -- point off the goal's `Finsupp.single`.
  · rw [if_pos accepted]
    exact mass_single_one_of_mem
      ((true_mem_observe_probe_iff answer).mpr accepted)
  · rw [if_neg accepted]
    exact mass_single_one_of_not_mem (fun observed =>
      accepted ((true_mem_observe_probe_iff answer).mp observed))

/-- The witness test on the heterogeneous carrier. -/
def witnessTest : Phi Interface testUniverse → ℝ≥0∞ :=
  boundaryTest bitBoundary probeTest

theorem witness_test_mem_bounded_tests :
    witnessTest ∈ boundedTests Interface testUniverse 2 :=
  boundary_test_mem_bounded_tests bitBoundary 2 probeDistinguisher

theorem witness_test_mem_strict_tests :
    witnessTest ∈ strictTests Interface testUniverse :=
  bounded_tests_subset_strict_tests 2 witness_test_mem_bounded_tests

theorem witness_test_value (answer : Bool) :
    witnessTest (witnessResource answer) = if answer then 1 else 0 := by
  show boundaryTest bitBoundary probeTest
      ⟨bitBoundary, DependentRandomSystem.ofProb (constantLaw answer)⟩ = _
  rw [boundary_test_same, strict_mass_of_prob]
  show ((StrictContext.acceptMass probeTest
      (DependentPDS.flatten (Finsupp.single (constantSystem answer) 1)) :
        NNReal) : ℝ≥0∞) = _
  rw [accept_mass_probe_constant]
  cases answer <;> simp

/-! ## The separation receipts -/

theorem witness_adv_eq_one :
    DistinguisherClass.adv witnessTest
      (witnessResource true) (witnessResource false) = 1 := by
  unfold DistinguisherClass.adv
  rw [witness_test_value true, witness_test_value false]
  simp

/-- **Non-vacuity of the full class**: the class distance of the witness
pair is exactly `1`, the maximum any distinguisher class can attain. -/
theorem strict_test_class_edistD_witness_eq_one :
    (strictTestClass Interface testUniverse).edistD
      (witnessResource true) (witnessResource false) = 1 := by
  refine le_antisymm
    ((strictTestClass Interface testUniverse).edistD_le_one _ _) ?_
  calc
    (1 : ℝ≥0∞) = DistinguisherClass.adv witnessTest
        (witnessResource true) (witnessResource false) :=
      witness_adv_eq_one.symm
    _ ≤ (strictTestClass Interface testUniverse).edistD
        (witnessResource true) (witnessResource false) :=
      (strictTestClass Interface testUniverse).adv_le_edistD
        witness_test_mem_strict_tests _ _

/-- **The gate itself**: `edistD` is not identically zero. -/
theorem strict_test_class_edistD_witness_ne_zero :
    (strictTestClass Interface testUniverse).edistD
        (witnessResource true) (witnessResource false) ≠ 0 := by
  rw [strict_test_class_edistD_witness_eq_one]
  exact one_ne_zero

/-- **Non-vacuity of the `q = 2` budgeted subclass**, by the same one-query
witness: a single query already separates the constant systems. -/
theorem bounded_strict_test_class_edistD_witness_eq_one :
    (boundedStrictTestClass Interface testUniverse 2).edistD
      (witnessResource true) (witnessResource false) = 1 := by
  refine le_antisymm
    ((boundedStrictTestClass Interface testUniverse 2).edistD_le_one _ _) ?_
  calc
    (1 : ℝ≥0∞) = DistinguisherClass.adv witnessTest
        (witnessResource true) (witnessResource false) :=
      witness_adv_eq_one.symm
    _ ≤ (boundedStrictTestClass Interface testUniverse 2).edistD
        (witnessResource true) (witnessResource false) :=
      (boundedStrictTestClass Interface testUniverse 2).adv_le_edistD
        witness_test_mem_bounded_tests _ _

/-- The exact hypothesis shape consumed by
`RandomSystemsCC.Frost.Instantiation.frost_instantiated` is discharged by
the concrete class. -/
example :
    ∀ left right : Phi Interface testUniverse,
      (strictTestClass Interface testUniverse).edistD left right ≤
        edist left right :=
  fun left right => strict_test_class_edistD_le_edist left right

/-- The witness receipt is consistent with the sound direction: the
installed metric also separates the witness pair. -/
example :
    (1 : ℝ≥0∞) ≤ edist (witnessResource true) (witnessResource false) :=
  strict_test_class_edistD_witness_eq_one ▸
    strict_test_class_edistD_le_edist
      (witnessResource true) (witnessResource false)

end

end RandomSystemsCC.TypedDistinguisherChecks
