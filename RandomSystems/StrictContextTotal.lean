/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.StrictContextAdvantage

/-!
# Strict contextual distance and CR18 advantage on total resources

Every strict accepting gap is bounded by CR18 maximal distinguishing
advantage on normalized laws.  This module proves the converse for total
resources by compiling the finite transcript witness for CR18 advantage into
a bounded strict test.  Hence the two metrics agree exactly on normalized
total laws.

The proof exposes the weaker run-level condition actually required:
`ProperInteraction d s` says that the interaction of distinguisher `d`
with deterministic resource `s` never receives CR18's completion symbol.
Totality is one sufficient source-aligned way to establish it.  Bare
common-domain partiality is not silently promoted to this condition —
`StrictContextSharedDomain` earns it by rejection pruning instead.
-/
namespace RandomSystems.CR18.StrictContextTotal

open RandomSystems (Dist)
open RandomSystems.CR18
open RandomSystems.CR18.PFunConverter
open RandomSystems.CR18.StrictContext
open scoped Classical ENNReal PFunDDS

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

/-- A CR18 distinguisher, regarded as a one-shot strict protocol.  The
strict protocol agrees with the DDD on proper answer histories and blocks
after the CR18 completion symbol. -/
def protocolOfDDD (d : PFunDDS.DDD X Y) : ProtocolFn Unit Bool X Y :=
  fun pair =>
    if pair.1 = [()] ∧ none ∉ pair.2 then Part.some (d.val pair.2)
    else Part.none

@[simp]
theorem mem_protocolOfDDD_iff (d : PFunDDS.DDD X Y)
    (pair : List Unit × List (Option Y)) (move : X ⊕ Bool) :
    move ∈ protocolOfDDD d pair ↔
      pair.1 = [()] ∧ none ∉ pair.2 ∧ d.val pair.2 = move := by
  unfold protocolOfDDD
  split_ifs with h
  · constructor
    · intro hm
      exact ⟨h.1, h.2, (Part.mem_some_iff.mp hm).symm⟩
    · rintro ⟨_, _, equality⟩
      exact Part.mem_some_iff.mpr equality.symm
  · constructor
    · intro hm
      simp at hm
    · rintro ⟨outer, proper, _⟩
      exact (h ⟨outer, proper⟩).elim

theorem protocolOfDDD_answersInY (d : PFunDDS.DDD X Y) :
    AnswersInY (protocolOfDDD d) := by
  intro pair _reachable containsNone defined
  rw [Part.dom_iff_mem] at defined
  obtain ⟨move, moveMember⟩ := defined
  have proper := (mem_protocolOfDDD_iff d pair move).mp moveMember |>.2.1
  exact proper containsNone

theorem protocolOfTruncDDD_answersWithin (q : Nat) (d : PFunDDS.DDD X Y) :
    AnswersWithin (protocolOfDDD (PFunDDS.truncDDD q d)) (q + 1) := by
  intro pair _reachable extension longEnough allQueries
  obtain ⟨query, queryMember⟩ := allQueries q (by omega)
  have queryShape :=
    (mem_protocolOfDDD_iff (PFunDDS.truncDDD q d)
      (pair.1, pair.2 ++ extension.take q) (Sum.inl query)).mp queryMember
  have historyLong : q ≤ (pair.2 ++ extension.take q).length := by
    simp only [List.length_append, List.length_take]
    omega
  rw [PFunDDS.truncDDD_val_of_ge historyLong] at queryShape
  rcases value : d.val ((pair.2 ++ extension.take q).take q) with x | bit <;>
    rw [value] at queryShape <;> simp at queryShape

def testOfTruncDDD (q : Nat) (d : PFunDDS.DDD X Y) : Test X Y :=
  ⟨protocolOfDDD (PFunDDS.truncDDD q d),
    protocolOfDDD_answersInY _, q + 1,
    protocolOfTruncDDD_answersWithin q d⟩

theorem transcriptOutputs_proper_of_total
    (system : PFunDDS.DDS X Y)
    (total : ∀ inputs : List X, inputs ≠ [] → inputs ∈ PFunDDS.dom system)
    (environment : PFunDDS.DDE X Y) : ∀ fuel : Nat,
    none ∉ (PFunDDS.transcript system environment fuel)↓ᵧ := by
  intro fuel
  induction fuel with
  | zero => simp [PFunDDS.transcript]
  | succ fuel induction =>
      rcases move : environment
          ((PFunDDS.transcript system environment fuel)↓ᵧ) with _ | query
      · rw [transcript_succ_stall move]
        exact induction
      · have prefixAccepted :
            (PFunDDS.transcript system environment fuel)↓ₓ ∈
                PFunDDS.dom system ∨
              (PFunDDS.transcript system environment fuel)↓ₓ = [] := by
          by_cases empty :
              (PFunDDS.transcript system environment fuel)↓ₓ = []
          · exact Or.inr empty
          · exact Or.inl (total _ empty)
        have nextAccepted :
            (PFunDDS.transcript system environment fuel)↓ₓ ++ [query] ∈
              PFunDDS.dom system := total _ (by simp)
        have outputSome := PFunDDS.output_fullyDefined_append_of_mem
          system (PFunDDS.transcript system environment fuel)↓ₓ query
          prefixAccepted nextAccepted
        rw [transcript_succ_fire move, transcriptOutputs_append, outputSome]
        simpa using induction

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

theorem true_mem_observe_iff_exists_drive
    (test : Test X Y) (system : PFunDDS.DDS X Y) :
    true ∈ observe test system ↔
      ∃ fuel finalInputs finalAnswers,
        (true, finalInputs, finalAnswers) ∈
          drive test.val system fuel [()] [] [] := by
  unfold observe
  rw [mem_applyRaw]
  constructor
  · rintro ⟨fuel, member⟩
    rw [true_mem_applyRawAt_singleton_iff] at member
    obtain ⟨finalInputs, finalAnswers, member⟩ := member
    exact ⟨fuel, finalInputs, finalAnswers, member⟩
  · rintro ⟨fuel, finalInputs, finalAnswers, member⟩
    exact ⟨fuel,
      true_mem_applyRawAt_singleton_iff _ _ _ |>.2
        ⟨finalInputs, finalAnswers, member⟩⟩

theorem drive_lift_transcript
    (d : PFunDDS.DDD X Y) (system : PFunDDS.DDS X Y)
    {transcriptPrefix : List (X × Option Y)}
    (isTranscript :
      PFunDDS.Transcript system (PFunDDS.ddToDDE d) transcriptPrefix)
    (proper : none ∉ transcriptPrefix↓ᵧ)
    {fuel : Nat} {result : Bool × List X × List (Option Y)}
    (continuation : result ∈
      drive (protocolOfDDD d) system fuel [()]
        transcriptPrefix↓ₓ transcriptPrefix↓ᵧ) :
    result ∈ drive (protocolOfDDD d) system
      (fuel + transcriptPrefix.length) [()] [] [] := by
  induction isTranscript generalizing fuel with
  | nil => simpa
  | snoc =>
      rename_i t isPrefix query queryMove induction
      have properPrefix : none ∉ t↓ᵧ := by
        intro noneMember
        apply proper
        rw [transcriptOutputs_append]
        exact List.mem_append_left _ noneMember
      have dQueries : d.val t↓ᵧ = Sum.inl query :=
        PFunDDS.ddToDDE_eq_some_iff.mp queryMove
      have protocolQueries :
          Sum.inl query ∈ protocolOfDDD d ([()], t↓ᵧ) :=
        (mem_protocolOfDDD_iff d _ _).2 ⟨rfl, properPrefix, dQueries⟩
      have oneStep : result ∈
          drive (protocolOfDDD d) system (fuel + 1) [()]
            t↓ₓ t↓ᵧ := by
        apply drive_mem_query (protocolOfDDD d) system protocolQueries
        simpa only [transcriptInputs_append, transcriptOutputs_append]
          using continuation
      have lifted := induction properPrefix oneStep
      simpa only [List.length_append, List.length_singleton, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using lifted

/-- The interaction never exposes CR18's completion symbol.  This is the
exact run-level compatibility condition needed to read a DDD as a strict
test; totality is one sufficient way to establish it. -/
def ProperInteraction (d : PFunDDS.DDD X Y)
    (system : PFunDDS.DDS X Y) : Prop :=
  ∀ fuel : Nat,
    none ∉ (PFunDDS.transcript system (PFunDDS.ddToDDE d) fuel)↓ᵧ

theorem properInteraction_of_total
    (d : PFunDDS.DDD X Y) (system : PFunDDS.DDS X Y)
    (total : ∀ inputs : List X, inputs ≠ [] → inputs ∈ PFunDDS.dom system) :
    ProperInteraction d system :=
  transcriptOutputs_proper_of_total system total (PFunDDS.ddToDDE d)

theorem verdict_truncDDD_imp_true_mem_observe_of_proper
    (q : Nat) (d : PFunDDS.DDD X Y) (system : PFunDDS.DDS X Y)
    (properInteraction :
      ProperInteraction (PFunDDS.truncDDD q d) system)
    (accepts : PFunDDS.verdict (PFunDDS.truncDDD q d) system) :
    true ∈ observe (testOfTruncDDD q d) system := by
  obtain ⟨witness, accepts⟩ := accepts
  let bounded := PFunDDS.truncDDD q d
  let transcriptPrefix :=
    PFunDDS.transcript system (PFunDDS.ddToDDE bounded) witness
  have isTranscript :
      PFunDDS.Transcript system (PFunDDS.ddToDDE bounded) transcriptPrefix :=
    (PFunDDS.transcript_mem_iff _ _ _).2 ⟨witness, rfl⟩
  have proper : none ∉ transcriptPrefix↓ᵧ :=
    properInteraction witness
  have finalMove :
      Sum.inr true ∈ protocolOfDDD bounded ([()], transcriptPrefix↓ᵧ) := by
    apply (mem_protocolOfDDD_iff bounded _ _).2
    exact ⟨rfl, proper, accepts⟩
  have terminal :
      (true, transcriptPrefix↓ₓ, transcriptPrefix↓ᵧ) ∈
        drive (protocolOfDDD bounded) system 1 [()]
          transcriptPrefix↓ₓ transcriptPrefix↓ᵧ :=
    drive_mem_answer (protocolOfDDD bounded) system finalMove 0
  have complete := drive_lift_transcript bounded system
    isTranscript proper terminal
  apply (true_mem_observe_iff_exists_drive (testOfTruncDDD q d) system).2
  exact ⟨1 + transcriptPrefix.length, transcriptPrefix↓ₓ,
    transcriptPrefix↓ᵧ, complete⟩

theorem verdict_truncDDD_imp_true_mem_observe_of_total
    (q : Nat) (d : PFunDDS.DDD X Y) (system : PFunDDS.DDS X Y)
    (total : ∀ inputs : List X, inputs ≠ [] → inputs ∈ PFunDDS.dom system)
    (accepts : PFunDDS.verdict (PFunDDS.truncDDD q d) system) :
    true ∈ observe (testOfTruncDDD q d) system :=
  verdict_truncDDD_imp_true_mem_observe_of_proper q d system
    (properInteraction_of_total _ system total) accepts

theorem drive_true_implies_verdict_from_transcript
    (d : PFunDDS.DDD X Y) (system : PFunDDS.DDS X Y)
    {transcriptPrefix : List (X × Option Y)}
    (isTranscript :
      PFunDDS.Transcript system (PFunDDS.ddToDDE d) transcriptPrefix) :
    ∀ {fuel : Nat} {finalInputs : List X}
      {finalAnswers : List (Option Y)},
      (true, finalInputs, finalAnswers) ∈
          drive (protocolOfDDD d) system fuel [()]
            transcriptPrefix↓ₓ transcriptPrefix↓ᵧ →
        PFunDDS.verdict d system := by
  intro fuel
  induction fuel generalizing transcriptPrefix with
  | zero =>
      intro finalInputs finalAnswers member
      simp [drive] at member
  | succ remaining induction =>
      intro finalInputs finalAnswers member
      rcases drive_succ_elim member with
        ⟨query, queryMember, continuation⟩ |
        ⟨verdict, verdictMember, resultEquation⟩
      · have queryShape :=
          (mem_protocolOfDDD_iff d ([()], transcriptPrefix↓ᵧ)
            (Sum.inl query)).1 queryMember
        have environmentQueries :
            PFunDDS.ddToDDE d transcriptPrefix↓ᵧ = some query :=
          PFunDDS.ddToDDE_eq_some_iff.mpr queryShape.2.2
        have nextTranscript :=
          PFunDDS.Transcript.snoc isTranscript environmentQueries
        apply induction nextTranscript
        simpa only [transcriptInputs_append, transcriptOutputs_append]
          using continuation
      · obtain ⟨rfl, rfl, rfl⟩ := resultEquation
        have verdictShape :=
          (mem_protocolOfDDD_iff d ([()], transcriptPrefix↓ᵧ)
            (Sum.inr true)).1 verdictMember
        obtain ⟨witness, witnessEquation⟩ :=
          (PFunDDS.transcript_mem_iff _ _ _).1 isTranscript
        exact ⟨witness, by rw [witnessEquation]; exact verdictShape.2.2⟩

theorem true_mem_observe_testOfTruncDDD_imp_verdict
    (q : Nat) (d : PFunDDS.DDD X Y) (system : PFunDDS.DDS X Y)
    (accepts : true ∈ observe (testOfTruncDDD q d) system) :
    PFunDDS.verdict (PFunDDS.truncDDD q d) system := by
  obtain ⟨fuel, finalInputs, finalAnswers, run⟩ :=
    (true_mem_observe_iff_exists_drive (testOfTruncDDD q d) system).1 accepts
  exact drive_true_implies_verdict_from_transcript
    (PFunDDS.truncDDD q d) system PFunDDS.Transcript.nil run

theorem true_mem_observe_testOfTruncDDD_iff_verdict_of_total
    (q : Nat) (d : PFunDDS.DDD X Y) (system : PFunDDS.DDS X Y)
    (total : ∀ inputs : List X, inputs ≠ [] → inputs ∈ PFunDDS.dom system) :
    true ∈ observe (testOfTruncDDD q d) system ↔
      PFunDDS.verdict (PFunDDS.truncDDD q d) system :=
  ⟨true_mem_observe_testOfTruncDDD_imp_verdict q d system,
    verdict_truncDDD_imp_true_mem_observe_of_total q d system total⟩

theorem true_mem_observe_testOfTruncDDD_iff_verdict_of_proper
    (q : Nat) (d : PFunDDS.DDD X Y) (system : PFunDDS.DDS X Y)
    (properInteraction :
      ProperInteraction (PFunDDS.truncDDD q d) system) :
    true ∈ observe (testOfTruncDDD q d) system ↔
      PFunDDS.verdict (PFunDDS.truncDDD q d) system :=
  ⟨true_mem_observe_testOfTruncDDD_imp_verdict q d system,
    verdict_truncDDD_imp_true_mem_observe_of_proper
      q d system properInteraction⟩

theorem ddToDDE_ofDDE_stall_at
    (environment : PFunDDS.DDE X Y) (queryBound : Nat)
    (accept : List (X × Option Y) → Bool) (system : PFunDDS.DDS X Y) :
    PFunDDS.ddToDDE (PFunDDS.DDD.ofDDE environment queryBound accept)
        ((PFunDDS.transcript system
          (PFunDDS.ddToDDE
            (PFunDDS.DDD.ofDDE environment queryBound accept))
          queryBound)↓ᵧ) = none := by
  rw [transcript_ofDDE environment queryBound accept system le_rfl,
    ddToDDE_ofDDE]
  rcases lt_or_ge
      (PFunDDS.transcript system environment queryBound).length
      queryBound with shorter | longEnough
  · rw [if_pos (by rwa [transcriptOutputs_length]),
      replay_transcript_outputs]
    exact PFunDDS.transcript_stall_of_length_lt shorter
  · rw [if_neg (by rw [transcriptOutputs_length]; omega)]

theorem verdict_truncDDD_succ_ofDDE_iff
    (environment : PFunDDS.DDE X Y) (queryBound : Nat)
    (accept : List (X × Option Y) → Bool) (system : PFunDDS.DDS X Y) :
    PFunDDS.verdict
        (PFunDDS.truncDDD (queryBound + 1)
          (PFunDDS.DDD.ofDDE environment queryBound accept)) system ↔
      PFunDDS.verdict
        (PFunDDS.DDD.ofDDE environment queryBound accept) system := by
  constructor
  · exact PFunDDS.verdict_of_verdict_truncDDD
  · intro verdict
    have verdictAtBound :=
      (PFunDDS.Cache.verdict_iff_at_stall
        (PFunDDS.DDD.ofDDE environment queryBound accept) system queryBound
        (ddToDDE_ofDDE_stall_at environment queryBound accept system)).1 verdict
    exact PFunDDS.verdict_truncDDD_of_lt (by omega) verdictAtBound

/-- Mass only reads the support, so predicates that agree there have equal
mass.  Public because the shared-domain module needs the same support-local
congruence for its per-atom verdict transfer. -/
theorem mass_congr_support
    {A : Type*} (distribution : RandomSystems.Dist A)
    {predicate predicate' : A → Prop}
    (same : ∀ value ∈ distribution.support,
      predicate value ↔ predicate' value) :
    distribution.mass predicate = distribution.mass predicate' := by
  classical
  unfold Dist.mass Finsupp.sum
  refine Finset.sum_congr rfl fun value member => ?_
  have equivalent := same value (by simpa using member)
  dsimp only
  by_cases holds : predicate value
  · rw [if_pos holds, if_pos (equivalent.mp holds)]
  · rw [if_neg holds, if_neg (mt equivalent.mpr holds)]

theorem acceptMass_testOfDDE_eq_transcriptMass_of_proper
    (environment : PFunDDS.DDE X Y) (queryBound : Nat)
    (accept : List (X × Option Y) → Bool) (system : PFunPDS X Y)
    (proper : ∀ deterministic ∈ system.support,
      ProperInteraction
        (PFunDDS.truncDDD (queryBound + 1)
          (PFunDDS.DDD.ofDDE environment queryBound accept)) deterministic) :
    acceptMass
        (testOfTruncDDD (queryBound + 1)
          (PFunDDS.DDD.ofDDE environment queryBound accept)) system =
      (transcriptDist system environment queryBound).mass
        (fun transcript => accept transcript = true) := by
  rw [← verdictProb_ofDDE, verdictProb_single]
  unfold acceptMass
  apply mass_congr_support system
  intro deterministic inSupport
  exact
    (true_mem_observe_testOfTruncDDD_iff_verdict_of_proper
      (queryBound + 1)
      (PFunDDS.DDD.ofDDE environment queryBound accept) deterministic
      (proper deterministic inSupport)).trans
      (verdict_truncDDD_succ_ofDDE_iff
        environment queryBound accept deterministic)

theorem acceptMass_testOfDDE_eq_transcriptMass_of_total
    (environment : PFunDDS.DDE X Y) (queryBound : Nat)
    (accept : List (X × Option Y) → Bool) (system : PFunPDS X Y)
    (total : CondEquiv.TotalOnNonempty system) :
    acceptMass
        (testOfTruncDDD (queryBound + 1)
          (PFunDDS.DDD.ofDDE environment queryBound accept)) system =
      (transcriptDist system environment queryBound).mass
        (fun transcript => accept transcript = true) := by
  apply acceptMass_testOfDDE_eq_transcriptMass_of_proper
  intro deterministic inSupport
  exact properInteraction_of_total _ deterministic
    (total deterministic inSupport)

theorem ofReal_delta_transcriptDist_le_maxEDist_of_total
    (left right : PFunPDS X Y)
    (leftnn : left.NonNeg)
    (leftTotal : CondEquiv.TotalOnNonempty left)
    (rightTotal : CondEquiv.TotalOnNonempty right)
    (environment : PFunDDS.DDE X Y) (queryBound : Nat) :
    ENNReal.ofReal
        (RandomSystems.CR18.δ
          (transcriptDist right environment queryBound)
          (transcriptDist left environment queryBound) : Real) ≤
      maxEDist left right := by
  classical
  let accept : List (X × Option Y) → Bool := fun transcript =>
    decide
      ((transcriptDist left environment queryBound) transcript <
        (transcriptDist right environment queryBound) transcript)
  let test := testOfTruncDDD (queryBound + 1)
    (PFunDDS.DDD.ofDDE environment queryBound accept)
  have leftAcceptance :=
    acceptMass_testOfDDE_eq_transcriptMass_of_total
      environment queryBound accept left leftTotal
  have rightAcceptance :=
    acceptMass_testOfDDE_eq_transcriptMass_of_total
      environment queryBound accept right rightTotal
  have acceptPredicate : (fun transcript => accept transcript = true) =
      fun transcript =>
        (transcriptDist left environment queryBound) transcript <
          (transcriptDist right environment queryBound) transcript := by
    funext transcript
    simp only [accept, decide_eq_true_eq]
  rw [acceptPredicate] at leftAcceptance rightAcceptance
  rw [RandomSystems.CR18.δ_eq_mass_sub_mass _
      (transcriptDist_nonNeg leftnn environment queryBound),
    ← rightAcceptance, ← leftAcceptance]
  calc
    ENNReal.ofReal
          ((acceptMass test right : Real) -
            (acceptMass test left : Real)) ≤
        ENNReal.ofReal
          (abs ((acceptMass test right : Real) -
            (acceptMass test left : Real))) :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ = edist (acceptMass test right) (acceptMass test left) := by
      rw [edist_dist, Real.dist_eq]
    _ = edist (acceptMass test left) (acceptMass test right) :=
      edist_comm _ _
    _ ≤ maxEDist left right :=
      le_iSup
        (fun current : Test X Y =>
          edist (acceptMass current left) (acceptMass current right)) test

theorem ofReal_maxAdvantage_le_maxEDist_of_total
    (left right : PFunPDS X Y)
    (leftnn : left.NonNeg) (rightnn : right.NonNeg)
    (leftTotal : CondEquiv.TotalOnNonempty left)
    (rightTotal : CondEquiv.TotalOnNonempty right) :
    ENNReal.ofReal Δ(left, right) ≤ maxEDist left right := by
  obtain ⟨environment, queryBound, attainment⟩ :=
    exists_adv_eq_δ_transcriptDist right leftnn
  rw [← adv_eq_maxAdvantage_swap rightnn leftnn, attainment]
  exact ofReal_delta_transcriptDist_le_maxEDist_of_total
    left right leftnn leftTotal rightTotal environment queryBound

theorem maxEDist_eq_ofReal_maxAdvantage_of_total
    (left right : PFunPDS X Y)
    (leftProb : left.isProbDist) (rightProb : right.isProbDist)
    (leftTotal : CondEquiv.TotalOnNonempty left)
    (rightTotal : CondEquiv.TotalOnNonempty right) :
    maxEDist left right = ENNReal.ofReal Δ(left, right) := by
  apply le_antisymm
  · exact StrictContextAdvantage.maxEDist_le_maxAdvantage
      left right leftProb rightProb
  · exact ofReal_maxAdvantage_le_maxEDist_of_total
      left right leftProb.nonNeg rightProb.nonNeg leftTotal rightTotal

/-! A pointwise guardrail: without proper interaction, the reverse
simulation is false.  CR18 can query the empty DDS, observe `none`, and then
accept; a strict test must become silent at that `none`. -/

def oneQueryEnvironment : PFunDDS.DDE Unit Unit
  | [] => some ()
  | _ :: _ => none

def alwaysAcceptTranscript (_ : List (Unit × Option Unit)) : Bool := true

noncomputable def acceptAfterRejectedQuery : PFunDDS.DDD Unit Unit :=
  PFunDDS.DDD.ofDDE oneQueryEnvironment 1 alwaysAcceptTranscript

theorem acceptAfterRejectedQuery_verdict_empty :
    PFunDDS.verdict
      (PFunDDS.truncDDD 2 acceptAfterRejectedQuery)
      (PFunDDS.DDS.empty : PFunDDS.DDS Unit Unit) := by
  apply (verdict_truncDDD_succ_ofDDE_iff
    oneQueryEnvironment 1 alwaysAcceptTranscript _).2
  exact (verdict_ofDDE_iff _ _ _ _).2 rfl

theorem acceptAfterRejectedQuery_not_strictly_accepted :
    ¬ true ∈ observe (testOfTruncDDD 2 acceptAfterRejectedQuery)
      (PFunDDS.DDS.empty : PFunDDS.DDS Unit Unit) := by
  intro accepted
  obtain ⟨fuel, finalInputs, finalAnswers, run⟩ :=
    (true_mem_observe_iff_exists_drive
      (testOfTruncDDD 2 acceptAfterRejectedQuery)
      (PFunDDS.DDS.empty : PFunDDS.DDS Unit Unit)).1 accepted
  cases fuel with
  | zero => simp [drive] at run
  | succ remaining =>
      rcases drive_succ_elim run with
        ⟨query, queryMember, continuation⟩ |
        ⟨verdict, verdictMember, resultEquation⟩
      · have queryShape :=
          (mem_protocolOfDDD_iff
            (PFunDDS.truncDDD 2 acceptAfterRejectedQuery)
            ([()], []) (Sum.inl query)).1 queryMember
        have queryIsUnit : query = () := Subsingleton.elim _ _
        subst query
        have outputIsNone :
            PFunDDS.output
                (PFunDDS.fullyDefined
                  (PFunDDS.DDS.empty : PFunDDS.DDS Unit Unit)) [()]
                (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
          apply output_fullyDefined_eq_none_iff.mpr
          exact not_mem_dom_empty [()]
        simp only [List.nil_append] at continuation
        rw [outputIsNone] at continuation
        cases remaining with
        | zero => simp [drive] at continuation
        | succ rest =>
            simp only [drive, Part.mem_bind_iff] at continuation
            obtain ⟨move, moveMember, _⟩ := continuation
            have shape :=
              (mem_protocolOfDDD_iff
                (PFunDDS.truncDDD 2 acceptAfterRejectedQuery)
                ([()], [none]) move).1 moveMember
            exact shape.2.1 (by simp)
      · have verdictShape :=
          (mem_protocolOfDDD_iff
            (PFunDDS.truncDDD 2 acceptAfterRejectedQuery)
            ([()], []) (Sum.inr verdict)).1 verdictMember
        rw [PFunDDS.truncDDD_val_of_lt (by simp),
          acceptAfterRejectedQuery, PFunDDS.DDD.ofDDE] at verdictShape
        simp [oneQueryEnvironment, replay] at verdictShape

end

end RandomSystems.CR18.StrictContextTotal
