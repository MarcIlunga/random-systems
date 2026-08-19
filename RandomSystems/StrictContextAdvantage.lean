/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CompatibleMetric
import RandomSystems.StrictContext

/-!
# Strict observations are bounded by CR18 distinguishing advantage

The selected typed AC metric ultimately tests resources with partial,
one-shot deterministic observers.  CR18's `maxAdvantage` instead ranges over
final-verdict distinguishers.  This module supplies the comparison at the
fixed-signature observation seam.

A partial strict observer is completed by returning verdict `false` exactly
where its normalized protocol is undefined.  This changes no accepting run,
but makes the protocol productive.  The existing CR18 emulation theorem can
therefore absorb it into a distinguisher of the original system.

This module is pure random-systems content (it imports nothing from the
bridge or the abstract package); it lives under `RandomSystems/` so both the
RS core and the RS-CC bridge can consume it without a boundary crossing.
-/

namespace RandomSystems.CR18.StrictContextAdvantage

open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.StrictContext
open scoped Classical ENNReal

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-- Complete a terminal strict observer by rejecting wherever its normalized
protocol is undefined.  Normalization ensures that off-tree junk is never
made operational. -/
def rejectOnDivergence (test : Test X Y) : ProtocolFn Unit Bool X Y :=
  fun pair =>
    if defined : (normalize test.val pair).Dom then
      Part.some ((normalize test.val pair).get defined)
    else
      Part.some (Sum.inr false)

theorem query_mem_rejectOnDivergence_iff (test : Test X Y)
    (pair : List Unit × List (Option Y)) (query : X) :
    Sum.inl query ∈ rejectOnDivergence test pair ↔
      Sum.inl query ∈ test.val pair ∧ Reach test.val pair := by
  unfold rejectOnDivergence
  split_ifs with defined
  · rw [Part.mem_some_iff]
    constructor
    · intro equal
      have member : Sum.inl query ∈ normalize test.val pair := by
        rw [equal]
        exact Part.get_mem defined
      exact (mem_normalize_iff test.val pair _).mp member
    · intro member
      exact (Part.get_eq_of_mem
        ((mem_normalize_iff test.val pair _).mpr member) defined).symm
  · constructor
    · intro impossible
      simp at impossible
    · rintro ⟨member, reachable⟩
      exfalso
      apply defined
      exact Part.dom_iff_mem.mpr
        ⟨Sum.inl query,
          (mem_normalize_iff test.val pair _).mpr ⟨member, reachable⟩⟩

theorem true_mem_rejectOnDivergence_iff (test : Test X Y)
    (pair : List Unit × List (Option Y)) :
    Sum.inr true ∈ rejectOnDivergence test pair ↔
      Sum.inr true ∈ test.val pair ∧ Reach test.val pair := by
  unfold rejectOnDivergence
  split_ifs with defined
  · rw [Part.mem_some_iff]
    constructor
    · intro equal
      have member : Sum.inr true ∈ normalize test.val pair := by
        rw [equal]
        exact Part.get_mem defined
      exact (mem_normalize_iff test.val pair _).mp member
    · intro member
      exact (Part.get_eq_of_mem
        ((mem_normalize_iff test.val pair _).mpr member) defined).symm
  · constructor
    · intro impossible
      simp at impossible
    · rintro ⟨member, reachable⟩
      exfalso
      apply defined
      exact Part.dom_iff_mem.mpr
        ⟨Sum.inr true,
          (mem_normalize_iff test.val pair _).mpr ⟨member, reachable⟩⟩

theorem rejectOnDivergence_defined (test : Test X Y)
    (pair : List Unit × List (Option Y)) :
    (rejectOnDivergence test pair).Dom := by
  unfold rejectOnDivergence
  split_ifs with defined
  · exact Part.dom_iff_mem.mpr
      ⟨(normalize test.val pair).get defined, Part.mem_some _⟩
  · exact Part.dom_iff_mem.mpr ⟨Sum.inr false, Part.mem_some _⟩

private theorem answersWithin_bound_positive
    {protocol : ProtocolFn Unit Bool X Y} {bound : Nat}
    (answersWithin : AnswersWithin protocol bound) : 0 < bound := by
  by_contra notPositive
  have boundZero : bound = 0 := Nat.eq_zero_of_not_pos notPositive
  subst bound
  have impossible := answersWithin ([()], []) (Reach.first ()) [] le_rfl
  apply impossible
  intro index indexLess
  simp at indexLess

theorem rejectOnDivergence_answersWithin (test : Test X Y) {bound : Nat}
    (answersWithin : AnswersWithin test.val bound) :
    AnswersWithin (rejectOnDivergence test) bound := by
  intro pair _reachable extension longEnough allQueries
  have boundPositive := answersWithin_bound_positive answersWithin
  have extensionPositive : 0 < extension.length :=
    lt_of_lt_of_le boundPositive longEnough
  obtain ⟨firstQuery, firstQueryMember⟩ :=
    allQueries 0 extensionPositive
  have firstLocal :=
    (query_mem_rejectOnDivergence_iff test pair firstQuery).mp
      (by simpa using firstQueryMember)
  apply answersWithin pair firstLocal.2 extension longEnough
  intro index indexLess
  obtain ⟨query, queryMember⟩ := allQueries index indexLess
  exact ⟨query,
    (query_mem_rejectOnDivergence_iff test
      (pair.1, pair.2 ++ extension.take index) query).mp queryMember |>.1⟩

/-- The rejecting completion is productive and hence belongs to the CR18
emulable converter class. -/
theorem rejectOnDivergence_emulable (test : Test X Y) :
    Emulable (rejectOnDivergence test) := by
  obtain ⟨bound, answersWithin⟩ := test.property.2
  exact emulable_of_answersWithin_of_dom
    (rejectOnDivergence test)
    (rejectOnDivergence_answersWithin test answersWithin)
    (fun pair _ => rejectOnDivergence_defined test pair)

private theorem drive_true_iff (test : Test X Y)
    (system : PFunDDS.DDS X Y) :
    ∀ {fuel : Nat} {outerInputs : List Unit} {innerInputs : List X}
      {innerAnswers : List (Option Y)} {finalInputs : List X}
      {finalAnswers : List (Option Y)},
      Reach test.val (outerInputs, innerAnswers) →
      ((true, finalInputs, finalAnswers) ∈
          drive test.val system fuel outerInputs innerInputs innerAnswers ↔
        (true, finalInputs, finalAnswers) ∈
          drive (rejectOnDivergence test) system fuel
            outerInputs innerInputs innerAnswers) := by
  intro fuel outerInputs innerInputs innerAnswers finalInputs finalAnswers
    reachable
  induction fuel generalizing outerInputs innerInputs innerAnswers with
  | zero =>
      simp [drive]
  | succ remaining induction =>
      simp only [drive, Part.mem_bind_iff]
      constructor
      · rintro ⟨move, moveMember, resultMember⟩
        cases move with
        | inl query =>
            refine ⟨Sum.inl query,
              (query_mem_rejectOnDivergence_iff test
                (outerInputs, innerAnswers) query).2
                ⟨moveMember, reachable⟩, ?_⟩
            exact (induction
              (Reach.answer reachable moveMember
                (PFunDDS.output (PFunDDS.fullyDefined system)
                  (innerInputs ++ [query])
                  (by rw [PFunDDS.dom_fullyDefined]; simp)))).1 resultMember
        | inr verdict =>
            simp only [Part.mem_some_iff] at resultMember ⊢
            obtain ⟨rfl, rfl, rfl⟩ := resultMember
            exact ⟨Sum.inr true,
              (true_mem_rejectOnDivergence_iff test
                (outerInputs, finalAnswers)).2 ⟨moveMember, reachable⟩,
              Part.mem_some _⟩
      · rintro ⟨move, moveMember, resultMember⟩
        cases move with
        | inl query =>
            have localMove := (query_mem_rejectOnDivergence_iff test
              (outerInputs, innerAnswers) query).1 moveMember
            refine ⟨Sum.inl query, localMove.1, ?_⟩
            exact (induction
              (Reach.answer reachable localMove.1
                (PFunDDS.output (PFunDDS.fullyDefined system)
                  (innerInputs ++ [query])
                  (by rw [PFunDDS.dom_fullyDefined]; simp)))).2 resultMember
        | inr verdict =>
            simp only [Part.mem_some_iff] at resultMember
            obtain ⟨rfl, rfl, rfl⟩ := resultMember
            exact ⟨Sum.inr true,
              ((true_mem_rejectOnDivergence_iff test
                (outerInputs, finalAnswers)).1 moveMember).1,
              Part.mem_some _⟩

private theorem true_mem_applyRawAt_singleton_iff
    (protocol : ProtocolFn Unit Bool X Y)
    (system : PFunDDS.DDS X Y) (fuel : Nat) :
    true ∈ applyRawAt protocol system fuel [()] ↔
      ∃ finalInputs finalAnswers,
        (true, finalInputs, finalAnswers) ∈
          drive protocol system fuel [()] [] [] := by
  rw [mem_applyRawAt_iff]
  constructor
  · rintro ⟨result, resultMember, lastTrue⟩
    simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at resultMember
    obtain ⟨driven, drivenMember, tail, tailMember, resultEquation⟩ :=
      resultMember
    simp only [Part.mem_some_iff] at tailMember
    subst tail
    obtain ⟨rfl, rfl, rfl⟩ := resultEquation
    simp only [List.getLast?_singleton, Option.some.injEq] at lastTrue
    rcases driven with ⟨verdict, finalInputs, finalAnswers⟩
    dsimp only at lastTrue
    subst verdict
    exact ⟨finalInputs, finalAnswers, drivenMember⟩
  · rintro ⟨finalInputs, finalAnswers, drivenMember⟩
    refine ⟨([true], finalInputs, finalAnswers), ?_, by simp⟩
    simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
    exact ⟨(true, finalInputs, finalAnswers), drivenMember,
      ([], finalInputs, finalAnswers), Part.mem_some _, rfl⟩

/-- Completing divergence with rejection preserves the accepting event on
every deterministic system. -/
theorem true_mem_observe_rejectOnDivergence_iff
    (test : Test X Y) (system : PFunDDS.DDS X Y) :
    true ∈ observe test system ↔
      true ∈ applyRaw (rejectOnDivergence test) system [()] := by
  unfold observe
  rw [mem_applyRaw, mem_applyRaw]
  constructor
  · rintro ⟨fuel, accepting⟩
    refine ⟨fuel, ?_⟩
    rw [true_mem_applyRawAt_singleton_iff] at accepting ⊢
    obtain ⟨finalInputs, finalAnswers, accepting⟩ := accepting
    exact ⟨finalInputs, finalAnswers,
      (drive_true_iff test system (Reach.first ())).1 accepting⟩
  · rintro ⟨fuel, accepting⟩
    refine ⟨fuel, ?_⟩
    rw [true_mem_applyRawAt_singleton_iff] at accepting ⊢
    obtain ⟨finalInputs, finalAnswers, accepting⟩ := accepting
    exact ⟨finalInputs, finalAnswers,
      (drive_true_iff test system (Reach.first ())).2 accepting⟩

/-! ## Reading the completed strict verdict through a CR18 distinguisher -/

/-- The one-query environment used to read a Boolean-valued system. -/
def readTrueEnvironment : PFunDDS.DDE Unit Bool
  | [] => some ()
  | _ :: _ => none

/-- Accept exactly the one-round transcript whose proper answer is `true`. -/
def readTrueTranscript : List (Unit × Option Bool) → Bool
  | [((), some true)] => true
  | _ => false

/-- A canonical CR18 distinguisher that makes one query and returns the
Boolean answer, treating rejection as `false`. -/
noncomputable def readTrueDistinguisher : PFunDDS.DDD Unit Bool :=
  PFunDDS.DDD.ofDDE readTrueEnvironment 1 readTrueTranscript

private theorem output_fullyDefined_singleton_eq_some_iff
    {A B : Type*} (system : PFunDDS.DDS A B) (query : A) (answer : B) :
    PFunDDS.output (PFunDDS.fullyDefined system) [query]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some answer ↔
      answer ∈ system.val [query] := by
  constructor
  · intro outputEquation
    obtain ⟨member, answerEquation⟩ :=
      PFunDDS.mem_of_output_fullyDefined_append_eq_some
        system [] query (Or.inr rfl) outputEquation
    rw [← answerEquation]
    exact Part.get_mem member
  · intro answerMember
    have member : [query] ∈ PFunDDS.dom system :=
      Part.dom_iff_mem.mpr ⟨answer, answerMember⟩
    calc
      PFunDDS.output (PFunDDS.fullyDefined system) [query] _ =
          some (PFunDDS.output system [query] member) := by
            simpa using PFunDDS.output_fullyDefined_append_of_mem
              system [] query (Or.inr rfl) member
      _ = some answer :=
        congrArg some (Part.mem_unique (Part.get_mem member) answerMember)

/-- The canonical reader accepts exactly when the Boolean-valued system
returns `true` on its unique query. -/
theorem verdict_readTrueDistinguisher_iff
    (system : PFunDDS.DDS Unit Bool) :
    PFunDDS.verdict readTrueDistinguisher system ↔
      true ∈ system.val [()] := by
  unfold readTrueDistinguisher
  rw [verdict_ofDDE_iff]
  change
    (readTrueTranscript
        [((), PFunDDS.output (PFunDDS.fullyDefined system) [()]
          (by rw [PFunDDS.dom_fullyDefined]; simp))] = true ↔
      true ∈ system.val [()])
  rw [show readTrueTranscript
      [((), PFunDDS.output (PFunDDS.fullyDefined system) [()]
        (by rw [PFunDDS.dom_fullyDefined]; simp))] = true ↔
      PFunDDS.output (PFunDDS.fullyDefined system) [()]
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some true by
    generalize PFunDDS.output (PFunDDS.fullyDefined system) [()]
      (by rw [PFunDDS.dom_fullyDefined]; simp) = output
    cases output with
    | none => simp [readTrueTranscript]
    | some answer => cases answer <;> simp [readTrueTranscript]]
  exact output_fullyDefined_singleton_eq_some_iff system () true

/-- Point mass on the canonical one-query Boolean reader. -/
noncomputable def readTrueDistribution :
    RandomSystems.Dist (PFunDDS.DDD Unit Bool) :=
  Finsupp.single readTrueDistinguisher 1

theorem readTrueDistribution_isProbDist :
    readTrueDistribution.isProbDist :=
  Dist.isProbDist_single readTrueDistinguisher

/-- Strict acceptance is literally the verdict probability of the canonical
reader after applying the rejecting completion. -/
theorem acceptMass_eq_verdictProb_apply_completion
    (test : Test X Y) (system : PFunPDS X Y) :
    acceptMass test system =
      verdictProb readTrueDistribution
        (PFunPDS.apply (rejectOnDivergence test) system) := by
  unfold readTrueDistribution
  rw [verdictProb_single]
  unfold acceptMass PFunPDS.apply
  rw [Dist.mass_fTransform]
  apply Dist.mass_congr
  intro deterministic
  rw [verdict_readTrueDistinguisher_iff,
    true_mem_observe_rejectOnDivergence_iff]
  rfl

/-- Every strict accepting-probability gap is bounded by CR18's optimal
distinguishing advantage.  The hypotheses are normalization, not finiteness
of either alphabet. -/
theorem edist_acceptMass_le_maxAdvantage
    (test : Test X Y) (left right : PFunPDS X Y)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist) :
    edist (acceptMass test left) (acceptMass test right) ≤
      ENNReal.ofReal Δ(left, right) := by
  let completedLeft := PFunPDS.apply (rejectOnDivergence test) left
  let completedRight := PFunPDS.apply (rejectOnDivergence test) right
  have completedLeftProb : completedLeft.isProbDist :=
    (PFunPDS.isProbDist_apply_iff _ leftProb.nonNeg).2 leftProb
  have completedRightProb : completedRight.isProbDist :=
    (PFunPDS.isProbDist_apply_iff _ rightProb.nonNeg).2 rightProb
  have forward :
      (acceptMass test right : ℝ) -
          (acceptMass test left : ℝ) ≤ Δ(left, right) := by
    calc
      (acceptMass test right : ℝ) -
            (acceptMass test left : ℝ) =
          advantage readTrueDistribution completedLeft completedRight := by
            unfold advantage completedLeft completedRight
            rw [acceptMass_eq_verdictProb_apply_completion,
              acceptMass_eq_verdictProb_apply_completion]
      _ ≤ Δ(completedLeft, completedRight) :=
        advantage_le_maxAdvantage readTrueDistribution _ _
          readTrueDistribution_isProbDist
      _ ≤ Δ(left, right) :=
        maxAdvantage_apply_le (rejectOnDivergence test)
          leftProb.nonNeg rightProb.nonNeg
          (rejectOnDivergence_emulable test)
  have backward :
      (acceptMass test left : ℝ) -
          (acceptMass test right : ℝ) ≤ Δ(left, right) := by
    calc
      (acceptMass test left : ℝ) -
            (acceptMass test right : ℝ) =
          advantage readTrueDistribution completedRight completedLeft := by
            unfold advantage completedLeft completedRight
            rw [acceptMass_eq_verdictProb_apply_completion,
              acceptMass_eq_verdictProb_apply_completion]
      _ ≤ Δ(completedRight, completedLeft) :=
        advantage_le_maxAdvantage readTrueDistribution _ _
          readTrueDistribution_isProbDist
      _ ≤ Δ(right, left) :=
        maxAdvantage_apply_le (rejectOnDivergence test)
          rightProb.nonNeg leftProb.nonNeg
          (rejectOnDivergence_emulable test)
      _ = Δ(left, right) := (maxAdvantage_comm leftProb rightProb).symm
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  exact abs_le.mpr ⟨by linarith, backward⟩

/-- The entire strict contextual metric is bounded by CR18 distinguishing
advantage on normalized laws. -/
theorem maxEDist_le_maxAdvantage
    (left right : PFunPDS X Y)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist) :
    maxEDist left right ≤ ENNReal.ofReal Δ(left, right) := by
  unfold maxEDist
  exact iSup_le fun test =>
    edist_acceptMass_le_maxAdvantage test left right leftProb rightProb

/-- CR18-to-strict equivalence bridge: on normalized laws, CR18 transcript
equivalence implies strict contextual equivalence.  Each strict test is
completed by rejection and read through the maximal-advantage comparison at
zero, so no caller has to repeat that plumbing.  (The converse is the
subject of `StrictContextTotal` / `StrictContextSharedDomain`: it needs the
source hypotheses, while this direction is unconditional.) -/
theorem strict_equivalent_of_equivalent
    (left right : PFunPDS X Y)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist)
    (equivalent : RandomSystems.CR18.Equivalent left right) :
    StrictContext.Equivalent left right := by
  intro test
  apply edist_eq_zero.mp
  apply bot_unique
  have bound :=
    edist_acceptMass_le_maxAdvantage test left right leftProb rightProb
  have maxZero : maxAdvantage left right = 0 := by
    rw [← adv_eq_maxAdvantage_swap rightProb.nonNeg leftProb.nonNeg]
    exact adv_eq_zero_of_equivalent
      (fun environment queries => (equivalent environment queries).symm)
  rw [maxZero] at bound
  simpa using bound

end

end RandomSystems.CR18.StrictContextAdvantage
