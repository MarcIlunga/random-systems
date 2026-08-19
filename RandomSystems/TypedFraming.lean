/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedAttachment
import RandomSystems.StrictContext
import RandomSystems.StepRealization
import RandomSystems.StrictRelabel

/-!
# All-interface framing for arbitrary deterministic typed converters

This module turns a signature-changing converter at one interface into a
strict converter on the complete dependent resource boundary. Queries at the
selected interface run the original history-sensitive protocol; queries at
all other interfaces are passed through while preserving the converter's
local history.

The public mathematical surface is intentionally small:

* `TypedFraming.framedConverter` is the boundary-wide strict converter;
* `TypedFraming.frameTest` pulls a strict observation through one attachment;
* `DependentDDS.flatten_attach_eq_apply_framed` proves that native typed
  attachment is exactly strict application after flattening.

The operational replay, fuel synchronization, ambient encoding, and
bisimulation machinery is private to `TypedFraming.Internal`.

This dependent, signature-changing framing is a project generalization. Its
implementation crosses through the ambient chart underlying the CR18
Definition 3.13-style attachment, but it is not asserted to be a verbatim CR18
theorem. Explicit recoverable rejection remains an ordinary typed answer.
Completion-level `none` is blocking: `AnswersInY` prevents a successful run
from resuming after it, which is precisely the strict AC-facing semantics used
by the coherence theorem.
-/

namespace RandomSystems.CR18.TypedResource

open PFunConverter

noncomputable section

universe c i u v w

namespace TypedFraming

namespace Internal

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I]
variable {source target : U.Code}
variable (interface : I) (boundary : Boundary U I)

/-- The advertised boundary after installing the local converter. -/
abbrev TargetBoundary : Boundary U I :=
  replaceBoundary boundary interface target

/-- Transport a query at a nonselected interface back to the source boundary. -/
def passQuery
    (query : Query U (TargetBoundary interface boundary (target := target)))
    (different : query.1 ≠ interface) : Query U boundary :=
  ⟨query.1,
    Eq.mp
      (congrArg U.input
        (replace_boundary_ne boundary different target))
      query.2⟩

/-- Transport a proper answer at a nonselected interface to the target boundary. -/
def passAnswer
    (answer : FlatAnswer U boundary)
    (different : answer.1 ≠ interface) :
    FlatAnswer U (TargetBoundary interface boundary (target := target)) :=
  ⟨answer.1,
    Eq.mp
      (congrArg U.output
        (replace_boundary_ne boundary different target).symm)
      answer.2⟩

/-- Decode the selected component of a target-boundary query. -/
def localInput
    (query : Query U (TargetBoundary interface boundary (target := target)))
    (same : query.1 = interface) : U.input target := by
  rcases query with ⟨queryInterface, value⟩
  dsimp only at same
  subst queryInterface
  simpa [TargetBoundary] using value

/-- Decode the selected component of a source-boundary proper answer. -/
def localAnswer
    (sourceMatches : boundary interface = source)
    (answer : FlatAnswer U boundary)
    (same : answer.1 = interface) : U.output source := by
  rcases answer with ⟨answerInterface, value⟩
  dsimp only at same
  subst answerInterface
  exact Eq.mp (congrArg U.output sourceMatches) value

/-- Re-encode a selected local inner query in the global source boundary. -/
def globalQuery (sourceMatches : boundary interface = source)
    (query : U.input source) : Query U boundary :=
  ⟨interface,
    Eq.mp (congrArg U.input sourceMatches.symm) query⟩

/-- Re-encode a selected local outside answer in the target boundary. -/
def globalAnswer (answer : U.output target) :
    FlatAnswer U (TargetBoundary interface boundary (target := target)) :=
  ⟨interface, by simpa [TargetBoundary] using answer⟩

/-- Re-encode a selected proper inner answer in the global source boundary. -/
def globalInnerAnswer (sourceMatches : boundary interface = source)
    (answer : U.output source) : FlatAnswer U boundary :=
  ⟨interface,
    Eq.mp (congrArg U.output sourceMatches.symm) answer⟩

omit [DecidableEq I] in

@[simp] theorem local_answer_global_inner_answer
    (sourceMatches : boundary interface = source)
    (answer : U.output source) :
    localAnswer interface boundary sourceMatches
        (globalInnerAnswer interface boundary sourceMatches answer) rfl =
      answer := by
  subst source
  rfl

omit [DecidableEq I] in

@[simp] theorem global_inner_answer_fst
    (sourceMatches : boundary interface = source)
    (answer : U.output source) :
    (globalInnerAnswer interface boundary sourceMatches answer).1 = interface :=
  rfl

omit [DecidableEq I] in

@[simp] theorem global_inner_answer_local_answer
    (sourceMatches : boundary interface = source)
    (answer : FlatAnswer U boundary) (same : answer.1 = interface) :
    globalInnerAnswer interface boundary sourceMatches
        (localAnswer interface boundary sourceMatches answer same) = answer := by
  rcases answer with ⟨answerInterface, value⟩
  change answerInterface = interface at same
  subst answerInterface
  simp [globalInnerAnswer, localAnswer]

omit [DecidableEq I] in

theorem local_answer_congr
    (sourceMatches : boundary interface = source)
    (left right : FlatAnswer U boundary)
    (leftSame : left.1 = interface) (rightSame : right.1 = interface)
    (equation : left = right) :
    localAnswer interface boundary sourceMatches left leftSame =
      localAnswer interface boundary sourceMatches right rightSame := by
  subst right
  rfl

/-- The phase of the all-interface frame.  The local protocol histories live
in `FrameState`, so they persist while unrelated interfaces pass through. -/
inductive Phase where
  | local
  | passPending
      (query : Query U (TargetBoundary interface boundary (target := target)))
      (different : query.1 ≠ interface)
  | passReturned
      (answer : FlatAnswer U
        (TargetBoundary interface boundary (target := target)))

/-- Replay state sufficient to evaluate the framed protocol. -/
structure FrameState where
  localInputs : List (U.input target)
  localAnswers : List (Option (U.output source))
  phase : Phase interface boundary (target := target)

/-- Start a new global round while retaining the local converter's cumulative
history. -/
def openRound
    (state : FrameState interface boundary (source := source) (target := target))
    (query : Query U (TargetBoundary interface boundary (target := target))) :
    FrameState interface boundary (source := source) (target := target) :=
  if same : query.1 = interface then
    { localInputs := state.localInputs ++ [localInput interface boundary query same]
      localAnswers := state.localAnswers
      phase := .local }
  else
    { state with phase := .passPending query same }

/-- Initial state after the first outside query. -/
def firstState
    (query : Query U (TargetBoundary interface boundary (target := target))) :
    FrameState interface boundary (source := source) (target := target) :=
  openRound interface boundary
    { localInputs := [], localAnswers := [], phase := .local } query

/-- The move prescribed by one replay state. -/
def stateMove
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target)) :
    Part
      (Query U boundary ⊕
        FlatAnswer U
          (TargetBoundary interface boundary (target := target))) :=
  match state.phase with
  | .local =>
      (converter.protocol (state.localInputs, state.localAnswers)).map
        (Sum.map
          (globalQuery interface boundary sourceMatches)
          (globalAnswer interface boundary))
  | .passPending query different =>
      Part.some (Sum.inl (passQuery interface boundary query different))
  | .passReturned answer => Part.some (Sum.inr answer)

/-- Consume one proper global resource answer.  Tag mismatch is blocking:
it is not projected away. -/
def consumeAnswer
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target))
    (answer : FlatAnswer U boundary) :
    Part (FrameState interface boundary (source := source) (target := target)) :=
  match state.phase with
  | .local =>
      if same : answer.1 = interface then
        Part.some
          { state with
            localAnswers := state.localAnswers ++
              [some (localAnswer interface boundary sourceMatches answer same)] }
      else Part.none
  | .passPending query _different =>
      if sameTag : answer.1 = query.1 then
        Part.some
          { state with
            phase := .passReturned
              (passAnswer interface boundary answer
                (sameTag.trans_ne _different)) }
      else Part.none
  | .passReturned _ => Part.none

/-- Fuel-free version of `replayAux`, used to expose append equations. -/
def replayCore
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target))
    (outside :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary))) :
    Part (FrameState interface boundary (source := source) (target := target)) :=
  match outside, answers with
  | [], [] => Part.some state
  | outside, answers =>
      (stateMove interface boundary converter sourceMatches state).bind fun move =>
        match move with
        | Sum.inl _query =>
            match answers with
            | some answer :: rest =>
                (consumeAnswer interface boundary sourceMatches state answer).bind
                  fun next => replayCore converter sourceMatches next outside rest
            | _ => Part.none
        | Sum.inr _answer =>
            match outside with
            | query :: rest =>
                replayCore converter sourceMatches
                  (openRound interface boundary state query) rest answers
            | [] => Part.none
termination_by outside.length + answers.length
decreasing_by all_goals simp_wf

/-- Fuel-free canonical replay of a global pair. -/
def replay (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (pair :
      List (Query U (TargetBoundary interface boundary (target := target))) ×
        List (Option (FlatAnswer U boundary))) :
    Part (FrameState interface boundary (source := source) (target := target)) :=
  match pair.1 with
  | [] => Part.none
  | first :: rest =>
      replayCore interface boundary converter sourceMatches
        (firstState interface boundary first) rest pair.2

theorem replay_core_answers_ne_none
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target))
    (outside :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    {result : FrameState interface boundary (source := source) (target := target)}
    (member : result ∈ replayCore interface boundary converter sourceMatches
      state outside answers) :
    none ∉ answers := by
  generalize measureEquation : outside.length + answers.length = measure
  induction measure using Nat.strong_induction_on generalizing
      state outside answers result with
  | h measure induction =>
      rw [replayCore.eq_def] at member
      cases outside with
      | nil =>
          cases answers with
          | nil => simp
          | cons optional rest =>
              simp only [List.length_nil, zero_add, List.length_cons] at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                (Part.mem_bind_iff.mp member)
              rcases move with query | answer
              · cases optional with
                | none => simp at tailMember
                | some proper =>
                    rw [Part.mem_bind_iff] at tailMember
                    obtain ⟨next, _nextMember, replayMember⟩ := tailMember
                    have smaller : rest.length < measure := by omega
                    simpa using induction rest.length smaller
                      (state := next) (outside := []) (answers := rest)
                      (result := result) replayMember (by simp)
              · simp at tailMember
      | cons nextOutside restOutside =>
          cases answers with
          | nil => simp
          | cons optional restAnswers =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                (Part.mem_bind_iff.mp member)
              rcases move with query | answer
              · cases optional with
                | none => simp at tailMember
                | some proper =>
                    rw [Part.mem_bind_iff] at tailMember
                    obtain ⟨next, _nextMember, replayMember⟩ := tailMember
                    have smaller :
                        (nextOutside :: restOutside).length + restAnswers.length <
                          measure := by
                      have measureValue :
                          measure = restOutside.length + 1 +
                            (restAnswers.length + 1) := measureEquation.symm
                      rw [measureValue]
                      simp only [List.length_cons]
                      omega
                    simpa using induction
                      ((nextOutside :: restOutside).length + restAnswers.length)
                      smaller (state := next)
                      (outside := nextOutside :: restOutside)
                      (answers := restAnswers) (result := result)
                      replayMember rfl
              · have smaller :
                  restOutside.length + (optional :: restAnswers).length <
                    measure := by
                  have measureValue :
                      measure = restOutside.length + 1 +
                        (restAnswers.length + 1) := measureEquation.symm
                  rw [measureValue]
                  simp only [List.length_cons]
                  omega
                exact induction
                    (restOutside.length + (optional :: restAnswers).length)
                    smaller
                    (state := openRound interface boundary state nextOutside)
                    (outside := restOutside)
                    (answers := optional :: restAnswers) (result := result)
                    tailMember rfl

theorem replay_answers_ne_none
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (pair :
      List (Query U (TargetBoundary interface boundary (target := target))) ×
        List (Option (FlatAnswer U boundary)))
    {state : FrameState interface boundary (source := source) (target := target)}
    (member : state ∈ replay interface boundary converter sourceMatches pair) :
    none ∉ pair.2 := by
  rcases pair with ⟨outside, answers⟩
  cases outside with
  | nil => simp [replay] at member
  | cons first rest =>
      exact replay_core_answers_ne_none interface boundary converter sourceMatches
        (firstState interface boundary first) rest answers member

/-- Canonical fuel-free rendering of the all-interface frame. -/
def framedProtocol
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source) :
    ProtocolFn
      (Query U (TargetBoundary interface boundary (target := target)))
      (FlatAnswer U (TargetBoundary interface boundary (target := target)))
      (Query U boundary) (FlatAnswer U boundary) :=
  fun pair =>
    (replay interface boundary converter sourceMatches pair).bind
      (stateMove interface boundary converter sourceMatches)

theorem framed_answers_in_y
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source) :
    AnswersInY (framedProtocol interface boundary converter sourceMatches) := by
  intro pair _reachable contains defined
  obtain ⟨move, moveMember⟩ := Part.dom_iff_mem.mp defined
  rw [framedProtocol, Part.mem_bind_iff] at moveMember
  obtain ⟨state, replayMember, _stateMoveMember⟩ := moveMember
  exact (replay_answers_ne_none interface boundary converter sourceMatches
    pair replayMember) contains

/-- A local history is idle either before its first selected-interface round,
or immediately after a local outside answer. -/
def LocalIdle (converter : DeterministicConverter U source target)
    (inputs : List (U.input target))
    (answers : List (Option (U.output source))) : Prop :=
  (inputs = [] ∧ answers = []) ∨
    ∃ answer, Reach converter.protocol (inputs, answers) ∧
      Sum.inr answer ∈ converter.protocol (inputs, answers)

/-- Reachability invariant carried by replay states. -/
def StateCoherent (converter : DeterministicConverter U source target)
    (state : FrameState interface boundary (source := source) (target := target)) :
    Prop :=
  match state.phase with
  | .local => Reach converter.protocol (state.localInputs, state.localAnswers)
  | .passPending _ _ | .passReturned _ =>
      LocalIdle converter state.localInputs state.localAnswers

theorem first_state_coherent
    (converter : DeterministicConverter U source target)
    (query : Query U (TargetBoundary interface boundary (target := target))) :
    StateCoherent interface boundary converter
      (firstState interface boundary query) := by
  unfold firstState openRound
  by_cases same : query.1 = interface
  · simp only [same, dite_true]
    exact Reach.first (localInput interface boundary query same)
  · simp only [same, dite_false]
    exact Or.inl ⟨rfl, rfl⟩

theorem coherent_consume_answer
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target))
    (coherent : StateCoherent interface boundary converter state)
    {query : Query U boundary}
    (queryMember : Sum.inl query ∈
      stateMove interface boundary converter sourceMatches state)
    (answer : FlatAnswer U boundary)
    {next : FrameState interface boundary (source := source) (target := target)}
    (nextMember : next ∈
      consumeAnswer interface boundary sourceMatches state answer) :
    StateCoherent interface boundary converter next := by
  rcases state with ⟨localInputs, localAnswers, phase⟩
  cases phase with
  | «local» =>
      simp only [stateMove, Part.mem_map_iff] at queryMember
      obtain ⟨localMove, localMember, moveEquation⟩ := queryMember
      rcases localMove with localQuery | localOutput
      · simp only [Sum.map_inl, Sum.inl.injEq] at moveEquation
        unfold consumeAnswer at nextMember
        by_cases same : answer.1 = interface
        · simp only [same, dite_true, Part.mem_some_iff] at nextMember
          subst next
          exact Reach.answer coherent localMember
            (some (localAnswer interface boundary sourceMatches answer same))
        · simp [same] at nextMember
      · simp at moveEquation
  | passPending pending different =>
      unfold consumeAnswer at nextMember
      by_cases sameTag : answer.1 = pending.1
      · simp only [sameTag, dite_true, Part.mem_some_iff] at nextMember
        subst next
        exact coherent
      · simp [sameTag] at nextMember
  | passReturned returned =>
      simp [stateMove] at queryMember

theorem coherent_open_round
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target))
    (coherent : StateCoherent interface boundary converter state)
    {answer : FlatAnswer U
      (TargetBoundary interface boundary (target := target))}
    (answerMember : Sum.inr answer ∈
      stateMove interface boundary converter sourceMatches state)
    (query : Query U (TargetBoundary interface boundary (target := target))) :
    StateCoherent interface boundary converter
      (openRound interface boundary state query) := by
  rcases state with ⟨localInputs, localAnswers, phase⟩
  cases phase with
  | «local» =>
      simp only [stateMove, Part.mem_map_iff] at answerMember
      obtain ⟨localMove, localMember, moveEquation⟩ := answerMember
      rcases localMove with localQuery | localOutput
      · simp at moveEquation
      · simp only [Sum.map_inr, Sum.inr.injEq] at moveEquation
        unfold openRound
        by_cases same : query.1 = interface
        · simp only [same, dite_true]
          exact Reach.next coherent localMember
            (localInput interface boundary query same)
        · simp only [same, dite_false]
          exact Or.inr ⟨localOutput, coherent, localMember⟩
  | passPending pending different =>
      simp [stateMove] at answerMember
  | passReturned returned =>
      unfold openRound
      by_cases same : query.1 = interface
      · simp only [same, dite_true]
        rcases coherent with empty | completed
        · rcases empty with ⟨rfl, rfl⟩
          exact Reach.first (localInput interface boundary query same)
        · obtain ⟨localOutput, reachable, outputMember⟩ := completed
          exact Reach.next reachable outputMember
            (localInput interface boundary query same)
      · simp only [same, dite_false]
        exact coherent

theorem replay_core_coherent
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target))
    (outside :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    {result : FrameState interface boundary (source := source) (target := target)}
    (coherent : StateCoherent interface boundary converter state)
    (member : result ∈ replayCore interface boundary converter sourceMatches
      state outside answers) :
    StateCoherent interface boundary converter result := by
  generalize measureEquation : outside.length + answers.length = measure
  induction measure using Nat.strong_induction_on generalizing
      state outside answers result with
  | h measure induction =>
      rw [replayCore.eq_def] at member
      cases outside with
      | nil =>
          cases answers with
          | nil =>
              simp only [Part.mem_some_iff] at member
              subst result
              exact coherent
          | cons optional rest =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · cases optional with
                | none => simp at tailMember
                | some proper =>
                    rw [Part.mem_bind_iff] at tailMember
                    obtain ⟨next, nextMember, replayMember⟩ := tailMember
                    have nextCoherent := coherent_consume_answer
                      interface boundary converter sourceMatches state coherent
                      moveMember proper nextMember
                    have smaller : rest.length < measure := by omega
                    exact induction rest.length smaller
                      (state := next) (outside := []) (answers := rest)
                      (result := result) nextCoherent replayMember (by simp)
              · simp at tailMember
      | cons nextOutside restOutside =>
          cases answers with
          | nil =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · simp at tailMember
              ·
                change result ∈ replayCore interface boundary converter
                  sourceMatches (openRound interface boundary state nextOutside)
                  restOutside [] at tailMember
                have nextCoherent := coherent_open_round
                  interface boundary converter sourceMatches state coherent
                  moveMember nextOutside
                have smaller : restOutside.length < measure := by omega
                exact induction restOutside.length smaller
                  (state := openRound interface boundary state nextOutside)
                  (outside := restOutside) (answers := []) (result := result)
                  nextCoherent tailMember (by simp)
          | cons optional restAnswers =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · cases optional with
                | none => simp at tailMember
                | some proper =>
                    rw [Part.mem_bind_iff] at tailMember
                    obtain ⟨next, nextMember, replayMember⟩ := tailMember
                    have nextCoherent := coherent_consume_answer
                      interface boundary converter sourceMatches state coherent
                      moveMember proper nextMember
                    have smaller :
                        (nextOutside :: restOutside).length + restAnswers.length <
                          measure := by
                      have measureValue :
                          measure = restOutside.length + 1 +
                            (restAnswers.length + 1) := measureEquation.symm
                      rw [measureValue]
                      simp only [List.length_cons]
                      omega
                    exact induction
                      ((nextOutside :: restOutside).length + restAnswers.length)
                      smaller (state := next)
                      (outside := nextOutside :: restOutside)
                      (answers := restAnswers) (result := result)
                      nextCoherent replayMember rfl
              ·
                change result ∈ replayCore interface boundary converter
                  sourceMatches (openRound interface boundary state nextOutside)
                  restOutside (optional :: restAnswers) at tailMember
                have nextCoherent := coherent_open_round
                  interface boundary converter sourceMatches state coherent
                  moveMember nextOutside
                have smaller :
                    restOutside.length + (optional :: restAnswers).length <
                      measure := by
                  have measureValue :
                      measure = restOutside.length + 1 +
                        (restAnswers.length + 1) := measureEquation.symm
                  rw [measureValue]
                  simp only [List.length_cons]
                  omega
                exact induction
                  (restOutside.length + (optional :: restAnswers).length)
                  smaller
                  (state := openRound interface boundary state nextOutside)
                  (outside := restOutside)
                  (answers := optional :: restAnswers) (result := result)
                  nextCoherent tailMember rfl

theorem replay_coherent
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (pair :
      List (Query U (TargetBoundary interface boundary (target := target))) ×
        List (Option (FlatAnswer U boundary)))
    {state : FrameState interface boundary (source := source) (target := target)}
    (member : state ∈ replay interface boundary converter sourceMatches pair) :
    StateCoherent interface boundary converter state := by
  rcases pair with ⟨outside, answers⟩
  cases outside with
  | nil => simp [replay] at member
  | cons first rest =>
      exact replay_core_coherent interface boundary converter sourceMatches
        (firstState interface boundary first) rest answers
        (first_state_coherent interface boundary converter first) member

/-- Successful replay is compositional under appending further inner answers.
This is the query-streak bridge: after the original pair has replayed to
`result`, extensions continue from exactly that state with no outer inputs. -/
theorem replay_core_append_answers_of_mem
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target))
    (outside :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers extension : List (Option (FlatAnswer U boundary)))
    {result : FrameState interface boundary (source := source) (target := target)}
    (member : result ∈ replayCore interface boundary converter sourceMatches
      state outside answers) :
    replayCore interface boundary converter sourceMatches state outside
        (answers ++ extension) =
      replayCore interface boundary converter sourceMatches result [] extension := by
  generalize measureEquation : outside.length + answers.length = measure
  induction measure using Nat.strong_induction_on generalizing
      state outside answers result with
  | h measure induction =>
      rw [replayCore.eq_def] at member
      cases outside with
      | nil =>
          cases answers with
          | nil =>
              simp only [Part.mem_some_iff] at member
              subst result
              rfl
          | cons optional rest =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · cases optional with
                | none => simp at tailMember
                | some proper =>
                    rw [Part.mem_bind_iff] at tailMember
                    obtain ⟨next, nextMember, replayMember⟩ := tailMember
                    have smaller : rest.length < measure := by omega
                    have recursive := induction rest.length smaller
                      (state := next) (outside := []) (answers := rest)
                      (result := result) replayMember (by simp)
                    rw [List.cons_append, replayCore.eq_def,
                      Part.eq_some_iff.mpr moveMember]
                    simp only [Part.bind_some]
                    rw [Part.eq_some_iff.mpr nextMember, Part.bind_some]
                    exact recursive
              · simp at tailMember
      | cons nextOutside restOutside =>
          cases answers with
          | nil =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · simp at tailMember
              ·
                change result ∈ replayCore interface boundary converter
                  sourceMatches (openRound interface boundary state nextOutside)
                  restOutside [] at tailMember
                have smaller : restOutside.length < measure := by omega
                have recursive := induction restOutside.length smaller
                  (state := openRound interface boundary state nextOutside)
                  (outside := restOutside) (answers := []) (result := result)
                  tailMember (by simp)
                rw [List.nil_append, replayCore.eq_def,
                  Part.eq_some_iff.mpr moveMember]
                simp only [Part.bind_some]
                exact recursive
          | cons optional restAnswers =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · cases optional with
                | none => simp at tailMember
                | some proper =>
                    rw [Part.mem_bind_iff] at tailMember
                    obtain ⟨next, nextMember, replayMember⟩ := tailMember
                    have smaller :
                        (nextOutside :: restOutside).length + restAnswers.length <
                          measure := by
                      have measureValue :
                          measure = restOutside.length + 1 +
                            (restAnswers.length + 1) := measureEquation.symm
                      rw [measureValue]
                      simp only [List.length_cons]
                      omega
                    have recursive := induction
                      ((nextOutside :: restOutside).length + restAnswers.length)
                      smaller (state := next)
                      (outside := nextOutside :: restOutside)
                      (answers := restAnswers) (result := result)
                      replayMember rfl
                    rw [List.cons_append, replayCore.eq_def,
                      Part.eq_some_iff.mpr moveMember]
                    simp only [Part.bind_some]
                    rw [Part.eq_some_iff.mpr nextMember, Part.bind_some]
                    exact recursive
              ·
                change result ∈ replayCore interface boundary converter
                  sourceMatches (openRound interface boundary state nextOutside)
                  restOutside (optional :: restAnswers) at tailMember
                have smaller :
                    restOutside.length + (optional :: restAnswers).length <
                      measure := by
                  have measureValue :
                      measure = restOutside.length + 1 +
                        (restAnswers.length + 1) := measureEquation.symm
                  rw [measureValue]
                  simp only [List.length_cons]
                  omega
                have recursive := induction
                  (restOutside.length + (optional :: restAnswers).length)
                  smaller
                  (state := openRound interface boundary state nextOutside)
                  (outside := restOutside)
                  (answers := optional :: restAnswers) (result := result)
                  tailMember rfl
                rw [List.cons_append, replayCore.eq_def,
                  Part.eq_some_iff.mpr moveMember]
                simp only [Part.bind_some]
                exact recursive

theorem replay_append_answers_of_mem
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (pair :
      List (Query U (TargetBoundary interface boundary (target := target))) ×
        List (Option (FlatAnswer U boundary)))
    (extension : List (Option (FlatAnswer U boundary)))
    {state : FrameState interface boundary (source := source) (target := target)}
    (member : state ∈ replay interface boundary converter sourceMatches pair) :
    replay interface boundary converter sourceMatches
        (pair.1, pair.2 ++ extension) =
      replayCore interface boundary converter sourceMatches state [] extension := by
  rcases pair with ⟨outside, answers⟩
  cases outside with
  | nil => simp [replay] at member
  | cons first rest =>
      exact replay_core_append_answers_of_mem interface boundary converter
        sourceMatches (firstState interface boundary first) rest answers extension
        member

/-- Decode a proper answer at the selected interface for the local protocol. -/
def decodeSelectedAnswer
    (sourceMatches : boundary interface = source) :
    Option (FlatAnswer U boundary) → Option (Option (U.output source))
  | none => none
  | some answer =>
      if same : answer.1 = interface then
        some (some (localAnswer interface boundary sourceMatches answer same))
      else none

/-- Decode a complete same-interface answer extension. -/
def decodeSelectedAnswers
    (sourceMatches : boundary interface = source) :
    List (Option (FlatAnswer U boundary)) →
      Option (List (Option (U.output source)))
  | [] => some []
  | answer :: rest =>
      (decodeSelectedAnswer interface boundary sourceMatches answer).bind
        fun decoded =>
          (decodeSelectedAnswers sourceMatches rest).map (List.cons decoded)

theorem decode_selected_answers_length
    (sourceMatches : boundary interface = source)
    {answers : List (Option (FlatAnswer U boundary))}
    {decoded : List (Option (U.output source))}
    (equation : decodeSelectedAnswers interface boundary sourceMatches answers =
      some decoded) :
    decoded.length = answers.length := by
  induction answers generalizing decoded with
  | nil =>
      simp [decodeSelectedAnswers] at equation
      subst decoded
      rfl
  | cons answer rest induction =>
      simp only [decodeSelectedAnswers] at equation
      cases oneEquation :
          decodeSelectedAnswer interface boundary sourceMatches answer with
      | none => simp [oneEquation] at equation
      | some one =>
          cases restEquation :
              decodeSelectedAnswers interface boundary sourceMatches rest with
          | none => simp [oneEquation, restEquation] at equation
          | some tail =>
              simp [oneEquation, restEquation] at equation
              subst decoded
              simp [induction restEquation]

theorem decode_selected_answers_take
    (sourceMatches : boundary interface = source)
    {answers : List (Option (FlatAnswer U boundary))}
    {decoded : List (Option (U.output source))}
    (equation : decodeSelectedAnswers interface boundary sourceMatches answers =
      some decoded) (count : Nat) :
    decodeSelectedAnswers interface boundary sourceMatches (answers.take count) =
      some (decoded.take count) := by
  induction answers generalizing decoded count with
  | nil =>
      simp [decodeSelectedAnswers] at equation
      subst decoded
      simp [decodeSelectedAnswers]
  | cons answer rest induction =>
      cases count with
      | zero => simp [decodeSelectedAnswers]
      | succ count =>
          simp only [decodeSelectedAnswers] at equation
          cases oneEquation :
              decodeSelectedAnswer interface boundary sourceMatches answer with
          | none => simp [oneEquation] at equation
          | some one =>
              cases restEquation :
                  decodeSelectedAnswers interface boundary sourceMatches rest with
              | none => simp [oneEquation, restEquation] at equation
              | some tail =>
                  simp [oneEquation, restEquation] at equation
                  subst decoded
                  simp only [List.take_succ_cons, decodeSelectedAnswers,
                    oneEquation, Option.bind_some]
                  rw [induction restEquation count]
                  rfl

/-- Replaying only answer extensions from a local phase is exactly local
answer decoding; the local input history is unchanged. -/
theorem replay_core_local_of_mem
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (extension : List (Option (FlatAnswer U boundary)))
    {result : FrameState interface boundary (source := source) (target := target)}
    (member : result ∈ replayCore interface boundary converter sourceMatches
      { localInputs := localInputs
        localAnswers := localAnswers
        phase := .local }
      [] extension) :
    ∃ decoded,
      decodeSelectedAnswers interface boundary sourceMatches extension =
        some decoded ∧
      result =
        { localInputs := localInputs
          localAnswers := localAnswers ++ decoded
          phase := .local } := by
  induction extension generalizing localAnswers result with
  | nil =>
      rw [replayCore.eq_def] at member
      simp only [Part.mem_some_iff] at member
      subst result
      exact ⟨[], rfl, by simp⟩
  | cons optional rest induction =>
      rw [replayCore.eq_def] at member
      obtain ⟨move, moveMember, tailMember⟩ := Part.mem_bind_iff.mp member
      rcases move with query | answer
      · cases optional with
        | none => simp at tailMember
        | some proper =>
            rw [Part.mem_bind_iff] at tailMember
            obtain ⟨next, nextMember, replayMember⟩ := tailMember
            unfold consumeAnswer at nextMember
            by_cases same : proper.1 = interface
            · simp only [same, dite_true, Part.mem_some_iff] at nextMember
              subst next
              obtain ⟨decoded, decodeEquation, resultEquation⟩ :=
                induction (localAnswers := localAnswers ++
                  [some (localAnswer interface boundary sourceMatches proper same)])
                  replayMember
              refine ⟨some (localAnswer interface boundary sourceMatches proper same) ::
                  decoded, ?_, ?_⟩
              · simp [decodeSelectedAnswers, decodeSelectedAnswer, same,
                  decodeEquation]
              · rw [resultEquation]
                congr 1
                simp [List.append_assoc]
            · simp [same] at nextMember
      · simp at tailMember

/-- A query move from a local frame state is exactly a local converter query. -/
theorem local_query_of_state_move
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    {query : Query U boundary}
    (member : Sum.inl query ∈ stateMove interface boundary converter
      sourceMatches
      { localInputs := localInputs
        localAnswers := localAnswers
        phase := .local }) :
    ∃ localQuery,
      Sum.inl localQuery ∈ converter.protocol (localInputs, localAnswers) := by
  simp only [stateMove, Part.mem_map_iff] at member
  obtain ⟨move, moveMember, equation⟩ := member
  rcases move with localQuery | localAnswer
  · exact ⟨localQuery, moveMember⟩
  · simp at equation

theorem mem_framed_protocol_iff
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (pair :
      List (Query U (TargetBoundary interface boundary (target := target))) ×
        List (Option (FlatAnswer U boundary)))
    (move : Query U boundary ⊕
      FlatAnswer U (TargetBoundary interface boundary (target := target))) :
    move ∈ framedProtocol interface boundary converter sourceMatches pair ↔
      ∃ state,
        state ∈ replay interface boundary converter sourceMatches pair ∧
        move ∈ stateMove interface boundary converter sourceMatches state := by
  simp [framedProtocol, Part.mem_bind_iff]

theorem pass_pending_after_one_not_query
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : pending.1 ≠ interface)
    (answer : Option (FlatAnswer U boundary)) :
    ¬ ∃ result,
      result ∈ replayCore interface boundary converter sourceMatches
        { localInputs := localInputs
          localAnswers := localAnswers
          phase := .passPending pending different }
        [] [answer] ∧
      ∃ query, Sum.inl query ∈
        stateMove interface boundary converter sourceMatches result := by
  rintro ⟨result, replayMember, query, queryMember⟩
  rw [replayCore.eq_def] at replayMember
  simp only [stateMove, Part.bind_some] at replayMember
  cases answer with
  | none => simp at replayMember
  | some proper =>
      rw [Part.mem_bind_iff] at replayMember
      obtain ⟨next, nextMember, tailMember⟩ := replayMember
      unfold consumeAnswer at nextMember
      by_cases sameTag : proper.1 = pending.1
      · simp only [sameTag, dite_true, Part.mem_some_iff] at nextMember
        subst next
        rw [replayCore.eq_def] at tailMember
        simp only [Part.mem_some_iff] at tailMember
        subst result
        simp [stateMove] at queryMember
      · simp [sameTag] at nextMember

/-- The local finite-query bound lifts to the all-interface frame.  The two
extra slots cover the one-query pass-through branch and make the zero-bound
edge case harmless. -/
theorem framed_answers_within
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    {bound : Nat}
    (localBound : AnswersWithin converter.protocol bound) :
    AnswersWithin
      (framedProtocol interface boundary converter sourceMatches)
      (bound + 2) := by
  intro pair _reachable extension lengthLower allQueries
  have extensionPositive : 0 < extension.length := by omega
  obtain ⟨firstQuery, firstQueryMember⟩ :=
    allQueries 0 extensionPositive
  have firstQueryMember' : Sum.inl firstQuery ∈
      framedProtocol interface boundary converter sourceMatches pair := by
    simpa using firstQueryMember
  obtain ⟨state, replayMember, stateQueryMember⟩ :=
    (mem_framed_protocol_iff interface boundary converter sourceMatches
      pair (Sum.inl firstQuery)).mp firstQueryMember'
  have coherent := replay_coherent interface boundary converter sourceMatches
    pair replayMember
  rcases state with ⟨localInputs, localAnswers, phase⟩
  cases phase with
  | «local» =>
      change Reach converter.protocol (localInputs, localAnswers) at coherent
      have boundIndex : bound < extension.length := by omega
      obtain ⟨boundQuery, boundQueryMember⟩ :=
        allQueries bound boundIndex
      obtain ⟨boundState, boundReplayMember, boundStateQueryMember⟩ :=
        (mem_framed_protocol_iff interface boundary converter sourceMatches
          (pair.1, pair.2 ++ extension.take bound)
          (Sum.inl boundQuery)).mp boundQueryMember
      have appendEquation := replay_append_answers_of_mem interface boundary
        converter sourceMatches pair (extension.take bound) replayMember
      rw [appendEquation] at boundReplayMember
      obtain ⟨decoded, decodeEquation, boundStateEquation⟩ :=
        replay_core_local_of_mem interface boundary converter sourceMatches
          localInputs localAnswers (extension.take bound) boundReplayMember
      have decodedLength : decoded.length = bound := by
        calc
          decoded.length = (extension.take bound).length :=
            decode_selected_answers_length interface boundary sourceMatches
              decodeEquation
          _ = bound := by
            rw [List.length_take, min_eq_left (Nat.le_of_lt boundIndex)]
      apply localBound (localInputs, localAnswers) coherent decoded
      · omega
      · intro index indexLess
        have indexBound : index < bound := by omega
        have indexExtension : index < extension.length := by omega
        obtain ⟨globalQuery, globalQueryMember⟩ :=
          allQueries index indexExtension
        obtain ⟨indexState, indexReplayMember, indexStateQueryMember⟩ :=
          (mem_framed_protocol_iff interface boundary converter sourceMatches
            (pair.1, pair.2 ++ extension.take index)
            (Sum.inl globalQuery)).mp globalQueryMember
        have indexAppendEquation := replay_append_answers_of_mem
          interface boundary converter sourceMatches pair
          (extension.take index) replayMember
        rw [indexAppendEquation] at indexReplayMember
        obtain ⟨indexDecoded, indexDecodeEquation, indexStateEquation⟩ :=
          replay_core_local_of_mem interface boundary converter sourceMatches
            localInputs localAnswers (extension.take index) indexReplayMember
        have expectedDecode :
            decodeSelectedAnswers interface boundary sourceMatches
                (extension.take index) =
              some (decoded.take index) := by
          have taken := decode_selected_answers_take interface boundary
            sourceMatches decodeEquation index
          simpa [List.take_take, min_eq_left (Nat.le_of_lt indexBound)] using
            taken
        have decodedEquation : indexDecoded = decoded.take index := by
          exact Option.some.inj (indexDecodeEquation.symm.trans expectedDecode)
        subst indexDecoded
        rw [indexStateEquation] at indexStateQueryMember
        exact local_query_of_state_move interface boundary converter
          sourceMatches localInputs (localAnswers ++ decoded.take index)
          indexStateQueryMember
  | passPending pending different =>
      have secondIndex : 1 < extension.length := by omega
      obtain ⟨secondQuery, secondQueryMember⟩ := allQueries 1 secondIndex
      cases extension with
      | nil => simp at extensionPositive
      | cons firstAnswer rest =>
        have secondQueryMember' : Sum.inl secondQuery ∈
            framedProtocol interface boundary converter sourceMatches
              (pair.1, pair.2 ++ [firstAnswer]) := by
          simpa using secondQueryMember
        obtain ⟨secondState, secondReplayMember, secondStateQueryMember⟩ :=
          (mem_framed_protocol_iff interface boundary converter sourceMatches
            (pair.1, pair.2 ++ [firstAnswer])
            (Sum.inl secondQuery)).mp secondQueryMember'
        have appendEquation := replay_append_answers_of_mem interface boundary
          converter sourceMatches pair [firstAnswer] replayMember
        rw [appendEquation] at secondReplayMember
        exact pass_pending_after_one_not_query interface boundary converter
          sourceMatches localInputs localAnswers pending different firstAnswer
          ⟨secondState, secondReplayMember, secondQuery,
            secondStateQueryMember⟩
  | passReturned returned =>
      simp [stateMove] at stateQueryMember

/-- The arbitrary boundary-changing frame is itself a deterministic discrete
converter; no `Emulable`, memoryless, or one-query restriction is used. -/
theorem framed_is_ddc
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source) :
    IsDDC (framedProtocol interface boundary converter sourceMatches) := by
  obtain ⟨bound, localBound⟩ := converter.isDDC.2
  exact ⟨framed_answers_in_y interface boundary converter sourceMatches,
    bound + 2,
    framed_answers_within interface boundary converter sourceMatches localBound⟩

/-- The framed protocol packaged in the exact strict-context converter type. -/
def framedConverter
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source) :
    { protocol : ProtocolFn
        (Query U (TargetBoundary interface boundary (target := target)))
        (FlatAnswer U (TargetBoundary interface boundary (target := target)))
        (Query U boundary) (FlatAnswer U boundary) // IsDDC protocol } :=
  ⟨framedProtocol interface boundary converter sourceMatches,
    framed_is_ddc interface boundary converter sourceMatches⟩

/-- Pull a strict target-boundary test through one typed attachment. -/
def frameTest
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (test : StrictContext.Test
      (Query U (TargetBoundary interface boundary (target := target)))
      (FlatAnswer U (TargetBoundary interface boundary (target := target)))) :
    StrictContext.Test (Query U boundary) (FlatAnswer U boundary) :=
  StrictContext.absorb test
    (framedConverter interface boundary converter sourceMatches)

/-! The remaining implementation crosses the ambient uniform-alphabet chart.
Code equality is needed only from this point onward; the public frame above
therefore carries no phantom code-decidability hypothesis. -/

variable [DecidableEq U.Code]

/-! ## A continuation resource for one selected-interface round

This is deliberately generic.  It isolates the suffix of a shared-state
resource visible while a converter is running at one interface.  It is the
missing bridge between `General.attachResolve` (which stores the complete
global history) and ordinary serial `DDC.resolve` (which stores only the
queries made in the current round).
-/

namespace Anchored

universe p x y

attribute [local instance] Classical.propDecidable

variable {P : Type p} {X : Type x} {Y : Type y}

def tagAt (selected : P) (queries : List X) : List (P × X) :=
  queries.map fun query => (selected, query)

@[simp] theorem tag_at_nil (selected : P) :
    tagAt selected ([] : List X) = [] := rfl

@[simp] theorem tag_at_append (selected : P) (left right : List X) :
    tagAt selected (left ++ right) =
      tagAt selected left ++ tagAt selected right := by
  simp [tagAt]

@[simp] theorem tag_at_singleton (selected : P) (query : X) :
    tagAt selected [query] = [(selected, query)] := rfl

/-- The local continuation of `system` after `base`, restricted to queries at
`selected`.  The empty local history is intentionally outside the DDS domain,
even when `base` itself is live. -/
def continuation (selected : P) (system : PFunDDS.Resource P X Y)
    (base : List (P × X)) : PFunDDS.DDS X Y :=
  ⟨(fun queries =>
      (⟨queries ≠ [] ∧
          base ++ tagAt selected queries ∈ PFunDDS.dom system,
        fun member => PFunDDS.output system
          (base ++ tagAt selected queries) member.2⟩ : Part Y)),
    ⟨by simp,
     by
      intro left right hprefix nonempty member
      refine ⟨nonempty, PFunDDS.prefix_closed system ?_ ?_ member.2⟩
      · obtain ⟨suffix, rfl⟩ := hprefix
        simp [tagAt, List.map_append]
      · simp [nonempty, tagAt]⟩⟩

@[simp] theorem continuation_dom (selected : P)
    (system : PFunDDS.Resource P X Y) (base : List (P × X)) :
    PFunDDS.dom (continuation selected system base) =
      {queries | queries ≠ [] ∧
        base ++ tagAt selected queries ∈ PFunDDS.dom system} :=
  rfl

/-- The global history corresponding to a local attempted-query history. -/
def globalState (selected : P) (system : PFunDDS.Resource P X Y)
    (base : List (P × X)) (queries : List X) : List (P × X) :=
  base ++ tagAt selected
    (PFunDDS.keptPrefix (continuation selected system base) queries)

theorem global_state_live (selected : P)
    (system : PFunDDS.Resource P X Y) (base : List (P × X))
    (queries : List X) :
    globalState selected system base queries ∈ PFunDDS.dom system ∨
      globalState selected system base queries = base := by
  rcases PFunDDS.keptPrefix_mem_or
      (continuation selected system base) queries with keptLive | keptEmpty
  · left
    exact keptLive.2
  · right
    simp [globalState, keptEmpty]

theorem output_fully_defined_append_eq_none
    (system : PFunDDS.DDS X Y) (history : List X) (query : X)
    (historyLive : history ∈ PFunDDS.dom system ∨ history = [])
    (rejected : history ++ [query] ∉ PFunDDS.dom system) :
    PFunDDS.output (PFunDDS.fullyDefined system) (history ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
  rw [PFunDDS.output_fullyDefined]
  have drop : (history ++ [query]).dropLast = history := by simp
  have last : (history ++ [query]).getLast (by simp) = query := by simp
  rw [drop, last]
  change
    (if candidate : PFunDDS.keptPrefix system history ++ [query] ∈
        PFunDDS.dom system then
      some (PFunDDS.output system
        (PFunDDS.keptPrefix system history ++ [query]) candidate)
    else none) = none
  rw [PFunDDS.keptPrefix_eq_self_of_mem_or_empty system historyLive]
  exact dif_neg rejected

theorem output_fully_defined_append_of_kept_mem
    (system : PFunDDS.DDS X Y) (history : List X) (query : X)
    (accepted : PFunDDS.keptPrefix system history ++ [query] ∈
      PFunDDS.dom system) :
    PFunDDS.output (PFunDDS.fullyDefined system) (history ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      some (PFunDDS.output system
        (PFunDDS.keptPrefix system history ++ [query]) accepted) := by
  rw [PFunDDS.output_fullyDefined]
  have drop : (history ++ [query]).dropLast = history := by simp
  have last : (history ++ [query]).getLast (by simp) = query := by simp
  rw [drop, last]
  change
    (if candidate : PFunDDS.keptPrefix system history ++ [query] ∈
        PFunDDS.dom system then
      some (PFunDDS.output system
        (PFunDDS.keptPrefix system history ++ [query]) candidate)
    else none) =
      some (PFunDDS.output system
        (PFunDDS.keptPrefix system history ++ [query]) accepted)
  exact dif_pos accepted

theorem output_fully_defined_append_eq_none_of_kept_not_mem
    (system : PFunDDS.DDS X Y) (history : List X) (query : X)
    (rejected : PFunDDS.keptPrefix system history ++ [query] ∉
      PFunDDS.dom system) :
    PFunDDS.output (PFunDDS.fullyDefined system) (history ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
  rw [PFunDDS.output_fullyDefined]
  have drop : (history ++ [query]).dropLast = history := by simp
  have last : (history ++ [query]).getLast (by simp) = query := by simp
  rw [drop, last]
  change
    (if candidate : PFunDDS.keptPrefix system history ++ [query] ∈
        PFunDDS.dom system then
      some (PFunDDS.output system
        (PFunDDS.keptPrefix system history ++ [query]) candidate)
    else none) = none
  exact dif_neg rejected

theorem output_continuation_kept
    (selected : P) (system : PFunDDS.Resource P X Y)
    (base : List (P × X))
    (baseLive : base ∈ PFunDDS.dom system ∨ base = [])
    (queries : List X) (query : X) :
    PFunDDS.output
        (PFunDDS.fullyDefined (continuation selected system base))
        (queries ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      PFunDDS.output (PFunDDS.fullyDefined system)
        (globalState selected system base queries ++ [(selected, query)])
        (by rw [PFunDDS.dom_fullyDefined]; simp) := by
  let kept := PFunDDS.keptPrefix
    (continuation selected system base) queries
  have localKeptLive : kept ∈
      PFunDDS.dom (continuation selected system base) ∨ kept = [] :=
    PFunDDS.keptPrefix_mem_or (continuation selected system base) queries
  have globalKeptLive :
      globalState selected system base queries ∈ PFunDDS.dom system ∨
        globalState selected system base queries = [] := by
    rcases global_state_live selected system base queries with live | same
    · exact Or.inl live
    · rw [same]
      exact baseLive
  have candidates :
      (kept ++ [query] ∈ PFunDDS.dom
          (continuation selected system base)) ↔
        (globalState selected system base queries ++ [(selected, query)] ∈
          PFunDDS.dom system) := by
    simp [continuation, globalState, kept, tagAt, List.map_append]
  by_cases localCandidate : kept ++ [query] ∈
      PFunDDS.dom (continuation selected system base)
  · have globalCandidate := candidates.mp localCandidate
    rw [output_fully_defined_append_of_kept_mem
          (continuation selected system base) queries query localCandidate,
        PFunDDS.output_fullyDefined_append_of_mem system
          (globalState selected system base queries) (selected, query)
          globalKeptLive globalCandidate]
    congr 1
    exact PFunDDS.output_congr system
      (by simp [continuation, globalState, tagAt]) _ _
  · have globalNot :
        globalState selected system base queries ++ [(selected, query)] ∉
          PFunDDS.dom system := fun member =>
            localCandidate (candidates.mpr member)
    rw [output_fully_defined_append_eq_none_of_kept_not_mem
          (continuation selected system base) queries query localCandidate,
        output_fully_defined_append_eq_none system
          (globalState selected system base queries) (selected, query)
          globalKeptLive globalNot]

theorem kept_prefix_append_singleton (system : PFunDDS.DDS X Y)
    (history : List X) (query : X) :
    PFunDDS.keptPrefix system (history ++ [query]) =
      if PFunDDS.keptPrefix system history ++ [query] ∈
          PFunDDS.dom system then
        PFunDDS.keptPrefix system history ++ [query]
      else PFunDDS.keptPrefix system history := by
  simp [PFunDDS.keptPrefix, List.foldl_append]

def stateMap (selected : P) (system : PFunDDS.Resource P X Y)
    (base : List (P × X)) :
    (List (DDC.CIn X Y) × List X) →
      (List (DDC.CIn X Y) × List (P × X)) :=
  fun state =>
    (state.1, globalState selected system base state.2)

def outcomeMap (selected : P) (system : PFunDDS.Resource P X Y)
    (base : List (P × X)) :
    (Y × (List (DDC.CIn X Y) × List X)) ⊕
        (List (DDC.CIn X Y) × List X) →
      (Y × (List (DDC.CIn X Y) × List (P × X))) ⊕
        (List (DDC.CIn X Y) × List (P × X))
  | Sum.inl (answer, state) =>
      Sum.inl (answer, stateMap selected system base state)
  | Sum.inr state => Sum.inr (stateMap selected system base state)

theorem attach_step_eq_map (selected : P) (alpha : DDC X Y X Y)
    (system : PFunDDS.Resource P X Y) (base : List (P × X))
    (baseLive : base ∈ PFunDDS.dom system ∨ base = [])
    (state : List (DDC.CIn X Y) × List X) :
    PFunConverter.General.attachStep selected alpha system
        (stateMap selected system base state) =
      (DDC.connStep alpha (continuation selected system base) state).map
        (outcomeMap selected system base) := by
  unfold PFunConverter.General.attachStep DDC.connStep
  rw [Part.map_bind]
  change (alpha.val state.1).bind _ = (alpha.val state.1).bind _
  apply congrArg (Part.bind (alpha.val state.1))
  funext move
  rcases move with ⟨label, answer⟩ | ⟨label, query⟩ <;> cases label
  · simp
  · rfl
  ·
    have answerEquation := output_continuation_kept selected system base
      baseLive state.2 query
    simp only [stateMap]
    rw [answerEquation]
    simp only [Part.map_some, outcomeMap, stateMap]
    unfold globalState
    rw [kept_prefix_append_singleton]
    by_cases accepted :
        PFunDDS.keptPrefix (continuation selected system base) state.2 ++
            [query] ∈ PFunDDS.dom (continuation selected system base)
    · rw [if_pos accepted]
      have completionSome :
          PFunDDS.output
              (PFunDDS.fullyDefined (continuation selected system base))
              (state.2 ++ [query])
              (by rw [PFunDDS.dom_fullyDefined]; simp) =
            some (PFunDDS.output (continuation selected system base)
              (PFunDDS.keptPrefix (continuation selected system base) state.2 ++
                [query]) accepted) :=
        output_fully_defined_append_of_kept_mem
          (continuation selected system base) state.2 query accepted
      have globalCompletionSome :
          PFunDDS.output (PFunDDS.fullyDefined system)
              (base ++ tagAt selected
                (PFunDDS.keptPrefix (continuation selected system base) state.2) ++
                [(selected, query)])
              (by rw [PFunDDS.dom_fullyDefined]; simp) =
            some (PFunDDS.output (continuation selected system base)
              (PFunDDS.keptPrefix (continuation selected system base) state.2 ++
                [query]) accepted) := by
        exact answerEquation.symm.trans completionSome
      rw [globalCompletionSome]
      simp [tagAt, List.map_append]
    · rw [if_neg accepted]
      have completionNone :
          PFunDDS.output
              (PFunDDS.fullyDefined (continuation selected system base))
              (state.2 ++ [query])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none :=
        output_fully_defined_append_eq_none_of_kept_not_mem
          (continuation selected system base) state.2 query accepted
      have globalCompletionNone :
          PFunDDS.output (PFunDDS.fullyDefined system)
              (base ++ tagAt selected
                (PFunDDS.keptPrefix (continuation selected system base) state.2) ++
                [(selected, query)])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
        exact answerEquation.symm.trans completionNone
      rw [globalCompletionNone]
  · simp

def resultMap (selected : P) (system : PFunDDS.Resource P X Y)
    (base : List (P × X)) :
    Y × (List (DDC.CIn X Y) × List X) →
      Y × (List (DDC.CIn X Y) × List (P × X)) :=
  fun result => (result.1, stateMap selected system base result.2)

theorem resolve_forward (selected : P) (alpha : DDC X Y X Y)
    (system : PFunDDS.Resource P X Y) (base : List (P × X))
    (baseLive : base ∈ PFunDDS.dom system ∨ base = [])
    {state : List (DDC.CIn X Y) × List X}
    {result : Y × (List (DDC.CIn X Y) × List X)}
    (member : result ∈
      DDC.resolve alpha (continuation selected system base) state) :
    resultMap selected system base result ∈
      PFunConverter.General.attachResolve selected alpha system
        (stateMap selected system base state) := by
  let localStep := DDC.connStep alpha (continuation selected system base)
  let globalStep := PFunConverter.General.attachStep selected alpha system
  let relation :
      (List (DDC.CIn X Y) × List X) →
        (List (DDC.CIn X Y) × List (P × X)) → Prop :=
    fun raw global => global = stateMap selected system base raw
  let outputRelation :
      (Y × (List (DDC.CIn X Y) × List X)) →
        (Y × (List (DDC.CIn X Y) × List (P × X))) → Prop :=
    fun raw global => global = resultMap selected system base raw
  have stop : ∀ raw global, relation raw global → ∀ output,
      Sum.inl output ∈ localStep raw →
        ∃ globalOutput, Sum.inl globalOutput ∈ globalStep global ∧
          outputRelation output globalOutput := by
    intro raw global related output outputMember
    subst global
    refine ⟨resultMap selected system base output, ?_, rfl⟩
    change Sum.inl (resultMap selected system base output) ∈
      PFunConverter.General.attachStep selected alpha system
        (stateMap selected system base raw)
    rw [attach_step_eq_map selected alpha system base baseLive]
    exact (Part.mem_map_iff _).mpr
      ⟨Sum.inl output, outputMember, rfl⟩
  have step : ∀ raw global, relation raw global → ∀ next,
      Sum.inr next ∈ localStep raw →
        ∃ globalNext, Sum.inr globalNext ∈ globalStep global ∧
          relation next globalNext := by
    intro raw global related next nextMember
    subst global
    refine ⟨stateMap selected system base next, ?_, rfl⟩
    change Sum.inr (stateMap selected system base next) ∈
      PFunConverter.General.attachStep selected alpha system
        (stateMap selected system base raw)
    rw [attach_step_eq_map selected alpha system base baseLive]
    exact (Part.mem_map_iff _).mpr
      ⟨Sum.inr next, nextMember, rfl⟩
  obtain ⟨globalResult, globalMember, related⟩ :=
    PFun.fix_bisim stop step member
      (stateMap selected system base state) rfl
  simpa [outputRelation] using related ▸ globalMember

theorem resolve_backward (selected : P) (alpha : DDC X Y X Y)
    (system : PFunDDS.Resource P X Y) (base : List (P × X))
    (baseLive : base ∈ PFunDDS.dom system ∨ base = [])
    {state : List (DDC.CIn X Y) × List X}
    {globalResult : Y ×
      (List (DDC.CIn X Y) × List (P × X))}
    (member : globalResult ∈
      PFunConverter.General.attachResolve selected alpha system
        (stateMap selected system base state)) :
    ∃ result,
      result ∈ DDC.resolve alpha (continuation selected system base) state ∧
      globalResult = resultMap selected system base result := by
  let globalStep := PFunConverter.General.attachStep selected alpha system
  let localStep := DDC.connStep alpha (continuation selected system base)
  let relation :
      (List (DDC.CIn X Y) × List (P × X)) →
        (List (DDC.CIn X Y) × List X) → Prop :=
    fun global raw => global = stateMap selected system base raw
  let outputRelation :
      (Y × (List (DDC.CIn X Y) × List (P × X))) →
        (Y × (List (DDC.CIn X Y) × List X)) → Prop :=
    fun global raw => global = resultMap selected system base raw
  have stop : ∀ global raw, relation global raw → ∀ output,
      Sum.inl output ∈ globalStep global →
        ∃ localOutput, Sum.inl localOutput ∈ localStep raw ∧
          outputRelation output localOutput := by
    intro global raw related output outputMember
    subst global
    change Sum.inl output ∈
      PFunConverter.General.attachStep selected alpha system
        (stateMap selected system base raw) at outputMember
    rw [attach_step_eq_map selected alpha system base baseLive] at outputMember
    obtain ⟨candidate, candidateMember, candidateEquation⟩ :=
      (Part.mem_map_iff _).mp outputMember
    rcases candidate with localOutput | localNext
    · refine ⟨localOutput, candidateMember, ?_⟩
      simpa [outputRelation, outcomeMap, resultMap] using
        candidateEquation.symm
    · simp [outcomeMap] at candidateEquation
  have step : ∀ global raw, relation global raw → ∀ next,
      Sum.inr next ∈ globalStep global →
        ∃ localNext, Sum.inr localNext ∈ localStep raw ∧
          relation next localNext := by
    intro global raw related next nextMember
    subst global
    change Sum.inr next ∈
      PFunConverter.General.attachStep selected alpha system
        (stateMap selected system base raw) at nextMember
    rw [attach_step_eq_map selected alpha system base baseLive] at nextMember
    obtain ⟨candidate, candidateMember, candidateEquation⟩ :=
      (Part.mem_map_iff _).mp nextMember
    rcases candidate with localOutput | localNext
    · simp [outcomeMap] at candidateEquation
    · refine ⟨localNext, candidateMember, ?_⟩
      simpa [relation, outcomeMap] using candidateEquation.symm
  obtain ⟨result, resultMember, related⟩ :=
    PFun.fix_bisim stop step member state rfl
  exact ⟨result, resultMember, related⟩

theorem attach_resolve_eq_map (selected : P) (alpha : DDC X Y X Y)
    (system : PFunDDS.Resource P X Y) (base : List (P × X))
    (baseLive : base ∈ PFunDDS.dom system ∨ base = [])
    (state : List (DDC.CIn X Y) × List X) :
    PFunConverter.General.attachResolve selected alpha system
        (stateMap selected system base state) =
      (DDC.resolve alpha (continuation selected system base) state).map
        (resultMap selected system base) := by
  apply Part.ext
  intro globalResult
  constructor
  · intro member
    obtain ⟨result, resultMember, equation⟩ :=
      resolve_backward selected alpha system base baseLive member
    exact (Part.mem_map_iff _).mpr
      ⟨result, resultMember, equation.symm⟩
  · intro member
    obtain ⟨result, resultMember, equation⟩ :=
      (Part.mem_map_iff _).mp member
    rw [← equation]
    exact resolve_forward selected alpha system base baseLive resultMember

end Anchored

/-! ## Native/ambient coherence for a selected-interface continuation -/

namespace TypedContinuation

attribute [local instance] Classical.propDecidable

def queryPath
    (sourceMatches : boundary interface = source)
    (queries : List (U.input source)) : List (Query U boundary) :=
  queries.map (globalQuery interface boundary sourceMatches)

omit [DecidableEq I] [DecidableEq U.Code] in

@[simp] theorem query_path_nil
    (sourceMatches : boundary interface = source) :
    queryPath interface boundary sourceMatches [] = [] := rfl

omit [DecidableEq I] [DecidableEq U.Code] in

@[simp] theorem query_path_append
    (sourceMatches : boundary interface = source)
    (left right : List (U.input source)) :
    queryPath interface boundary sourceMatches (left ++ right) =
      queryPath interface boundary sourceMatches left ++
        queryPath interface boundary sourceMatches right := by
  simp [queryPath]

omit [DecidableEq I] [DecidableEq U.Code] in

@[simp] theorem query_path_singleton
    (sourceMatches : boundary interface = source)
    (query : U.input source) :
    queryPath interface boundary sourceMatches [query] =
      [globalQuery interface boundary sourceMatches query] := rfl

omit [DecidableEq I] [DecidableEq U.Code] in

theorem query_path_ne_nil
    (sourceMatches : boundary interface = source)
    {queries : List (U.input source)} (nonempty : queries ≠ []) :
    queryPath interface boundary sourceMatches queries ≠ [] := by
  simpa [queryPath] using nonempty

/-- Raw native continuation function. -/
def continuationRaw
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary)) :
    PFunDDS.Raw (U.input source) (U.output source) :=
  fun queries =>
    ⟨queries ≠ [] ∧
        base ++ queryPath interface boundary sourceMatches queries ∈
          PFunDDS.dom system.flatten,
      fun member =>
        let globalHistory :=
          base ++ queryPath interface boundary sourceMatches queries
        let globalAnswer := PFunDDS.output system.flatten globalHistory member.2
        have same : globalAnswer.1 = interface := by
          have faithful := system.flatten_tag_faithful globalHistory member.2
          have lastInterface :
              (globalHistory.getLast (by
                exact List.append_ne_nil_of_right_ne_nil _
                  (query_path_ne_nil interface boundary sourceMatches
                    member.1))).1 = interface := by
            unfold globalHistory
            rw [List.getLast_append_right
              (query_path_ne_nil interface boundary sourceMatches member.1)]
            simp [queryPath, globalQuery]
          exact faithful.trans lastInterface
        localAnswer interface boundary sourceMatches globalAnswer same⟩

/-- The native source-signature DDS visible during one selected-interface
round after a fixed global base history. -/
def continuation
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary)) :
    PFunDDS.DDS (U.input source) (U.output source) :=
  ⟨continuationRaw interface boundary sourceMatches system base,
    ⟨by simp [continuationRaw],
     by
      intro left right hprefix nonempty member
      change left ≠ [] ∧
        base ++ queryPath interface boundary sourceMatches left ∈
          PFunDDS.dom system.flatten
      change right ≠ [] ∧
        base ++ queryPath interface boundary sourceMatches right ∈
          PFunDDS.dom system.flatten at member
      refine ⟨nonempty, PFunDDS.prefix_closed system.flatten ?_ ?_ member.2⟩
      · obtain ⟨suffix, rfl⟩ := hprefix
        simp [queryPath, List.map_append]
      · apply List.append_ne_nil_of_right_ne_nil
        exact query_path_ne_nil interface boundary sourceMatches nonempty⟩⟩

omit [DecidableEq I] [DecidableEq U.Code] in
@[simp] theorem continuation_dom
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary)) :
    PFunDDS.dom
        (continuation interface boundary sourceMatches system base) =
      {queries | queries ≠ [] ∧
        base ++ queryPath interface boundary sourceMatches queries ∈
          PFunDDS.dom system.flatten} :=
  rfl

def encodeLocalInput (query : U.input source) : AmbientInput U :=
  ⟨source, query⟩

def encodeLocalOutput (answer : U.output source) : AmbientOutput U :=
  ⟨source, answer⟩

omit [DecidableEq I] [DecidableEq U.Code] in

@[simp] theorem encode_query_path
    (sourceMatches : boundary interface = source)
    (queries : List (U.input source)) :
    (queryPath interface boundary sourceMatches queries).map encodeQuery =
      Anchored.tagAt interface (queries.map encodeLocalInput) := by
  induction queries with
  | nil => rfl
  | cons query rest induction =>
      simp [queryPath, Anchored.tagAt, globalQuery, encodeQuery,
        encodeLocalInput, sourceMatches]

omit [DecidableEq I] [DecidableEq U.Code] in
theorem continuation_ambient_apply_encoded
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    (queries : List (U.input source)) :
    (Anchored.continuation interface system.embed
      (base.map encodeQuery)).1
        (queries.map encodeLocalInput) =
      ((continuation interface boundary sourceMatches system base).1
        queries).map encodeLocalOutput := by
  apply Part.ext'
  · change
      (queries.map encodeLocalInput ≠ [] ∧
        base.map encodeQuery ++
            Anchored.tagAt interface (queries.map encodeLocalInput) ∈
          PFunDDS.dom system.embed) ↔
      (queries ≠ [] ∧
        base ++ queryPath interface boundary sourceMatches queries ∈
          PFunDDS.dom system.flatten)
    rw [← encode_query_path interface boundary sourceMatches]
    rw [← List.map_append]
    have embedded := system.embed_apply_encoded
      (base ++ queryPath interface boundary sourceMatches queries)
    constructor
    · rintro ⟨nonempty, member⟩
      refine ⟨?_, ?_⟩
      · simpa using nonempty
      · change
          ((system.embed.1
            ((base ++ queryPath interface boundary sourceMatches queries).map
              encodeQuery)).Dom)
            at member
        rw [embedded] at member
        exact member
    · rintro ⟨nonempty, member⟩
      refine ⟨by simpa using nonempty, ?_⟩
      change
        ((system.embed.1
          ((base ++ queryPath interface boundary sourceMatches queries).map
            encodeQuery)).Dom)
      rw [embedded]
      exact member
  · intro ambientMember nativeMember
    have ambientData :
      queries.map encodeLocalInput ≠ [] ∧
      base.map encodeQuery ++
          Anchored.tagAt interface (queries.map encodeLocalInput) ∈
        PFunDDS.dom system.embed := by
      simpa [Anchored.continuation, PFunDDS.dom, PFunDDS.toPFun] using
        ambientMember
    have ambientMember' := ambientData.2
    change queries ≠ [] ∧
      base ++ queryPath interface boundary sourceMatches queries ∈
        PFunDDS.dom system.flatten at nativeMember
    have nativeNonempty : queries ≠ [] := nativeMember.1
    let globalHistory :=
      base ++ queryPath interface boundary sourceMatches queries
    have encodedEquation := system.embed_apply_encoded globalHistory
    have ambientHistoryEquation :
        base.map encodeQuery ++
            Anchored.tagAt interface (queries.map encodeLocalInput) =
          globalHistory.map encodeQuery := by
      simp [globalHistory, encode_query_path interface boundary sourceMatches]
    let nativeAnswer :=
      PFunDDS.output system.flatten globalHistory nativeMember.2
    have nativeAnswerSame : nativeAnswer.1 = interface := by
      have faithful := system.flatten_tag_faithful globalHistory nativeMember.2
      have lastInterface :
          (globalHistory.getLast (by
            exact List.append_ne_nil_of_right_ne_nil _
              (query_path_ne_nil interface boundary sourceMatches
                nativeNonempty))).1 = interface := by
        unfold globalHistory
        rw [List.getLast_append_right
          (query_path_ne_nil interface boundary sourceMatches nativeNonempty)]
        simp [queryPath, globalQuery]
      exact faithful.trans lastInterface
    have nativeAnswerMember : nativeAnswer ∈
        system.flatten.1 globalHistory := by
      dsimp only [nativeAnswer, globalHistory]
      exact Part.get_mem _
    have ambientAnswerMember : encodeAnswer nativeAnswer ∈
        system.embed.1 (globalHistory.map encodeQuery) := by
      rw [encodedEquation]
      exact Part.mem_map _ nativeAnswerMember
    have ambientOutputEquation :
        PFunDDS.output system.embed
            (base.map encodeQuery ++
              Anchored.tagAt interface (queries.map encodeLocalInput))
            ambientMember' = encodeAnswer nativeAnswer := by
      have firstMember :
          PFunDDS.output system.embed
              (base.map encodeQuery ++
                Anchored.tagAt interface (queries.map encodeLocalInput))
              ambientMember' ∈
            system.embed.1
              (base.map encodeQuery ++
                Anchored.tagAt interface (queries.map encodeLocalInput)) :=
        Part.get_mem _
      have firstMemberEncoded :
          PFunDDS.output system.embed
              (base.map encodeQuery ++
                Anchored.tagAt interface (queries.map encodeLocalInput))
              ambientMember' ∈
            system.embed.1 (globalHistory.map encodeQuery) := by
        rw [← ambientHistoryEquation]
        exact firstMember
      exact Part.mem_unique firstMemberEncoded ambientAnswerMember
    change
      PFunDDS.output system.embed
          (base.map encodeQuery ++
            Anchored.tagAt interface (queries.map encodeLocalInput))
          ambientMember' =
        encodeLocalOutput
          (localAnswer interface boundary sourceMatches nativeAnswer
            nativeAnswerSame)
    rw [ambientOutputEquation]
    rcases nativeAnswer with ⟨answerInterface, answer⟩
    change answerInterface = interface at nativeAnswerSame
    subst answerInterface
    simp [encodeAnswer, encodeLocalOutput, localAnswer, sourceMatches]

omit [DecidableEq I] [DecidableEq U.Code] in
theorem continuation_ambient_dom_encoded_iff
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    (queries : List (U.input source)) :
    queries.map encodeLocalInput ∈
        PFunDDS.dom
          (Anchored.continuation interface system.embed
            (base.map encodeQuery)) ↔
      queries ∈ PFunDDS.dom
        (continuation interface boundary sourceMatches system base) := by
  change
    ((Anchored.continuation interface system.embed
      (base.map encodeQuery)).1 (queries.map encodeLocalInput)).Dom ↔
    ((continuation interface boundary sourceMatches system base).1
      queries).Dom
  rw [continuation_ambient_apply_encoded interface boundary sourceMatches]
  rfl

omit [DecidableEq I] [DecidableEq U.Code] in
theorem kept_prefix_ambient_encoded
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    (queries : List (U.input source)) :
    PFunDDS.keptPrefix
        (Anchored.continuation interface system.embed
          (base.map encodeQuery))
        (queries.map encodeLocalInput) =
      (PFunDDS.keptPrefix
        (continuation interface boundary sourceMatches system base)
        queries).map encodeLocalInput := by
  induction queries using List.reverseRecOn with
  | nil => rfl
  | append_singleton queries query induction =>
      rw [List.map_append, List.map_singleton,
        Anchored.kept_prefix_append_singleton,
        Anchored.kept_prefix_append_singleton, induction]
      have domainEquation := continuation_ambient_dom_encoded_iff
        interface boundary sourceMatches system base
        (PFunDDS.keptPrefix
          (continuation interface boundary sourceMatches system base)
          queries ++ [query])
      simp only [List.map_append, List.map_singleton] at domainEquation
      by_cases member :
          PFunDDS.keptPrefix
              (continuation interface boundary sourceMatches system base)
              queries ++ [query] ∈
            PFunDDS.dom
              (continuation interface boundary sourceMatches system base)
      · rw [if_pos member, if_pos (domainEquation.mpr member),
          List.map_append, List.map_singleton]
      · rw [if_neg member, if_neg (fun encodedMember =>
          member (domainEquation.mp encodedMember))]

omit [DecidableEq I] [DecidableEq U.Code] in
theorem continuation_ambient_output_encoded
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    (queries : List (U.input source))
    (member : queries ∈ PFunDDS.dom
      (continuation interface boundary sourceMatches system base)) :
    PFunDDS.output
        (Anchored.continuation interface system.embed
          (base.map encodeQuery))
        (queries.map encodeLocalInput)
        ((continuation_ambient_dom_encoded_iff interface boundary
          sourceMatches system base queries).mpr member) =
      encodeLocalOutput
        (PFunDDS.output
          (continuation interface boundary sourceMatches system base)
          queries member) := by
  apply Part.mem_unique
    (Part.get_mem
      ((continuation_ambient_dom_encoded_iff interface boundary
        sourceMatches system base queries).mpr member))
  rw [continuation_ambient_apply_encoded interface boundary sourceMatches]
  exact Part.mem_map _ (Part.get_mem member)

omit [DecidableEq I] [DecidableEq U.Code] in
theorem continuation_ambient_output_fully_defined_encoded
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    (queries : List (U.input source)) (query : U.input source) :
    PFunDDS.output
        (PFunDDS.fullyDefined
          (Anchored.continuation interface system.embed
            (base.map encodeQuery)))
        ((queries ++ [query]).map encodeLocalInput)
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      (PFunDDS.output
        (PFunDDS.fullyDefined
          (continuation interface boundary sourceMatches system base))
        (queries ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp)).map
          encodeLocalOutput := by
  simp only [List.map_append, List.map_singleton]
  let candidate :=
    PFunDDS.keptPrefix
      (continuation interface boundary sourceMatches system base) queries ++
        [query]
  have ambientCandidateEquation :
      PFunDDS.keptPrefix
          (Anchored.continuation interface system.embed
            (base.map encodeQuery))
          (queries.map encodeLocalInput) ++ [encodeLocalInput query] =
        candidate.map encodeLocalInput := by
    rw [kept_prefix_ambient_encoded interface boundary sourceMatches]
    simp [candidate]
  have domainEquation := continuation_ambient_dom_encoded_iff
    interface boundary sourceMatches system base candidate
  by_cases member : candidate ∈ PFunDDS.dom
      (continuation interface boundary sourceMatches system base)
  · have encodedMember := domainEquation.mpr member
    have ambientMember :
        PFunDDS.keptPrefix
            (Anchored.continuation interface system.embed
              (base.map encodeQuery))
            (queries.map encodeLocalInput) ++ [encodeLocalInput query] ∈
          PFunDDS.dom
            (Anchored.continuation interface system.embed
              (base.map encodeQuery)) := by
      rw [ambientCandidateEquation]
      exact encodedMember
    rw [PFunConverter.output_fullyDefined_append_keptPrefix_of_mem
        (Anchored.continuation interface system.embed
          (base.map encodeQuery))
        (queries.map encodeLocalInput) (encodeLocalInput query) ambientMember,
      PFunConverter.output_fullyDefined_append_keptPrefix_of_mem
        (continuation interface boundary sourceMatches system base)
        queries query member,
      Option.map_some]
    congr 1
    calc
      PFunDDS.output
          (Anchored.continuation interface system.embed
            (base.map encodeQuery))
          (PFunDDS.keptPrefix
              (Anchored.continuation interface system.embed
                (base.map encodeQuery))
              (queries.map encodeLocalInput) ++ [encodeLocalInput query])
          ambientMember =
        PFunDDS.output
          (Anchored.continuation interface system.embed
            (base.map encodeQuery))
          (candidate.map encodeLocalInput) encodedMember :=
            PFunDDS.output_congr _ ambientCandidateEquation _ _
      _ = encodeLocalOutput
          (PFunDDS.output
            (continuation interface boundary sourceMatches system base)
            candidate member) :=
        continuation_ambient_output_encoded interface boundary sourceMatches
          system base candidate member
  · have encodedNotMember : candidate.map encodeLocalInput ∉
        PFunDDS.dom
          (Anchored.continuation interface system.embed
            (base.map encodeQuery)) :=
      fun encodedMember => member (domainEquation.mp encodedMember)
    have ambientNotMember :
        PFunDDS.keptPrefix
            (Anchored.continuation interface system.embed
              (base.map encodeQuery))
            (queries.map encodeLocalInput) ++ [encodeLocalInput query] ∉
          PFunDDS.dom
            (Anchored.continuation interface system.embed
              (base.map encodeQuery)) := by
      rw [ambientCandidateEquation]
      exact encodedNotMember
    have ambientNone :
        PFunDDS.output
            (PFunDDS.fullyDefined
              (Anchored.continuation interface system.embed
                (base.map encodeQuery)))
            (queries.map encodeLocalInput ++ [encodeLocalInput query])
            (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
      exact Anchored.output_fully_defined_append_eq_none_of_kept_not_mem
        (Anchored.continuation interface system.embed
          (base.map encodeQuery))
        (queries.map encodeLocalInput) (encodeLocalInput query)
        ambientNotMember
    have nativeNone :
        PFunDDS.output
            (PFunDDS.fullyDefined
              (continuation interface boundary sourceMatches system base))
            (queries ++ [query])
            (by rw [PFunDDS.dom_fullyDefined]; simp) = none := by
      exact Anchored.output_fully_defined_append_eq_none_of_kept_not_mem
        (continuation interface boundary sourceMatches system base)
        queries query member
    rw [ambientNone, nativeNone, Option.map_none]

omit [DecidableEq I] [DecidableEq U.Code] in
/-- On a live local prefix, the native continuation's completed answer is
exactly the selected-tag answer returned by the flattened global resource. -/
theorem flatten_output_eq_continuation_output
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    (baseLive : base ∈ PFunDDS.dom system.flatten ∨ base = [])
    (queries : List (U.input source)) (query : U.input source)
    (queriesLive : queries ∈ PFunDDS.dom
        (continuation interface boundary sourceMatches system base) ∨
      queries = []) :
    PFunDDS.output (PFunDDS.fullyDefined system.flatten)
        (base ++ queryPath interface boundary sourceMatches queries ++
          [globalQuery interface boundary sourceMatches query])
        (by rw [PFunDDS.dom_fullyDefined]; simp) =
      (PFunDDS.output
        (PFunDDS.fullyDefined
          (continuation interface boundary sourceMatches system base))
        (queries ++ [query])
        (by rw [PFunDDS.dom_fullyDefined]; simp)).map
          (globalInnerAnswer interface boundary sourceMatches) := by
  let localSystem :=
    continuation interface boundary sourceMatches system base
  have kept : PFunDDS.keptPrefix localSystem queries = queries :=
    PFunDDS.keptPrefix_eq_self_of_mem_or_empty localSystem queriesLive
  have historyEquation :
      base ++ queryPath interface boundary sourceMatches queries ++
          [globalQuery interface boundary sourceMatches query] =
        base ++ queryPath interface boundary sourceMatches (queries ++ [query]) := by
    simp [TypedContinuation.queryPath, List.map_append]
  have candidates :
      queries ++ [query] ∈ PFunDDS.dom localSystem ↔
        base ++ queryPath interface boundary sourceMatches (queries ++ [query]) ∈
          PFunDDS.dom system.flatten := by
    change
      ((queries ++ [query]) ≠ [] ∧
        base ++ queryPath interface boundary sourceMatches
          (queries ++ [query]) ∈ PFunDDS.dom system.flatten) ↔ _
    simp
  by_cases accepted : queries ++ [query] ∈ PFunDDS.dom localSystem
  · have globalAccepted := candidates.mp accepted
    have globalPrefixLive :
        base ++ queryPath interface boundary sourceMatches queries ∈
            PFunDDS.dom system.flatten ∨
          base ++ queryPath interface boundary sourceMatches queries = [] := by
      rcases queriesLive with live | empty
      · exact Or.inl live.2
      · subst queries
        simpa using baseLive
    have globalAccepted' :
        (base ++ queryPath interface boundary sourceMatches queries) ++
            [globalQuery interface boundary sourceMatches query] ∈
          PFunDDS.dom system.flatten := by
      rw [historyEquation]
      exact globalAccepted
    have globalSome :=
      PFunDDS.output_fullyDefined_append_of_mem system.flatten
        (base ++ queryPath interface boundary sourceMatches queries)
        (globalQuery interface boundary sourceMatches query)
        globalPrefixLive globalAccepted'
    have localSome :=
      PFunDDS.output_fullyDefined_append_of_mem localSystem queries query
        queriesLive accepted
    let global :=
      PFunDDS.output system.flatten
        ((base ++ queryPath interface boundary sourceMatches queries) ++
          [globalQuery interface boundary sourceMatches query])
        globalAccepted'
    have globalSame : global.1 = interface := by
      have faithful := system.flatten_tag_faithful
        ((base ++ queryPath interface boundary sourceMatches queries) ++
          [globalQuery interface boundary sourceMatches query])
        globalAccepted'
      have lastInterface :
          (((base ++ queryPath interface boundary sourceMatches queries) ++
            [globalQuery interface boundary sourceMatches query]).getLast
              (by simp)).1 = interface := by
        simp [globalQuery]
      exact faithful.trans lastInterface
    have localEquation :
        PFunDDS.output localSystem (queries ++ [query]) accepted =
          localAnswer interface boundary sourceMatches global globalSame := by
      have firstSame :
          (PFunDDS.output system.flatten
            (base ++ queryPath interface boundary sourceMatches
              (queries ++ [query])) accepted.2).1 = interface := by
        have outputEquation := PFunDDS.output_congr system.flatten
          historyEquation.symm accepted.2 globalAccepted'
        rw [outputEquation]
        exact globalSame
      change
        localAnswer interface boundary sourceMatches
            (PFunDDS.output system.flatten
              (base ++ queryPath interface boundary sourceMatches
                (queries ++ [query])) accepted.2) firstSame =
          localAnswer interface boundary sourceMatches global globalSame
      have outputEquation := PFunDDS.output_congr system.flatten
        historyEquation.symm accepted.2 globalAccepted'
      dsimp only [global]
      exact local_answer_congr interface boundary sourceMatches _ _
        firstSame globalSame outputEquation
    have valueEquation :
        PFunDDS.output system.flatten
            ((base ++ queryPath interface boundary sourceMatches queries) ++
              [globalQuery interface boundary sourceMatches query])
            globalAccepted' =
          globalInnerAnswer interface boundary sourceMatches
            (PFunDDS.output localSystem (queries ++ [query]) accepted) := by
      change global = _
      rw [localEquation]
      exact (global_inner_answer_local_answer interface boundary sourceMatches
        global globalSame).symm
    calc
      _ = some (PFunDDS.output system.flatten
          ((base ++ queryPath interface boundary sourceMatches queries) ++
            [globalQuery interface boundary sourceMatches query])
          globalAccepted') := globalSome
      _ = some (globalInnerAnswer interface boundary sourceMatches
          (PFunDDS.output localSystem (queries ++ [query]) accepted)) :=
        congrArg some valueEquation
      _ = (some (PFunDDS.output localSystem (queries ++ [query]) accepted)).map
          (globalInnerAnswer interface boundary sourceMatches) := rfl
      _ = _ := congrArg
        (Option.map (globalInnerAnswer interface boundary sourceMatches))
        localSome.symm
  · have globalRejected :
        base ++ queryPath interface boundary sourceMatches (queries ++ [query]) ∉
          PFunDDS.dom system.flatten :=
      fun member => accepted (candidates.mpr member)
    have globalPrefixLive :
        base ++ queryPath interface boundary sourceMatches queries ∈
            PFunDDS.dom system.flatten ∨
          base ++ queryPath interface boundary sourceMatches queries = [] := by
      rcases queriesLive with live | empty
      · left
        exact live.2
      · subst queries
        simp only [query_path_nil, List.append_nil]
        exact baseLive
    have globalRejected' :
        (base ++ queryPath interface boundary sourceMatches queries) ++
            [globalQuery interface boundary sourceMatches query] ∉
          PFunDDS.dom system.flatten := by
      rw [historyEquation]
      exact globalRejected
    have globalNone :=
      Anchored.output_fully_defined_append_eq_none system.flatten
        (base ++ queryPath interface boundary sourceMatches queries)
        (globalQuery interface boundary sourceMatches query)
        globalPrefixLive globalRejected'
    have localNone := Anchored.output_fully_defined_append_eq_none
      localSystem queries query queriesLive accepted
    rw [globalNone, localNone, Option.map_none]

def encodeLocalOptionalOutput :
    Option (U.output source) → Option (AmbientOutput U) :=
  Option.map encodeLocalOutput

def encodeLocalDriveResult :
    (U.output target × List (U.input source) ×
        List (Option (U.output source))) →
      (AmbientOutput U × List (AmbientInput U) ×
        List (Option (AmbientOutput U))) :=
  fun result =>
    (⟨target, result.1⟩,
      result.2.1.map encodeLocalInput,
      result.2.2.map encodeLocalOptionalOutput)

omit [DecidableEq I] in
theorem drive_embedded_continuation_encoded
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary)) :
    ∀ (fuel : Nat) (outsideInputs : List (U.input target))
      (innerInputs : List (U.input source))
      (innerAnswers : List (Option (U.output source))),
      PFunConverter.drive converter.embeddedProtocol
          (Anchored.continuation interface system.embed
            (base.map encodeQuery)) fuel
          (outsideInputs.map fun value =>
            (⟨target, value⟩ : AmbientInput U))
          (innerInputs.map encodeLocalInput)
          (innerAnswers.map encodeLocalOptionalOutput) =
        (PFunConverter.drive converter.protocol
          (continuation interface boundary sourceMatches system base)
          fuel outsideInputs innerInputs innerAnswers).map
            encodeLocalDriveResult := by
  intro fuel
  induction fuel with
  | zero =>
      intro outsideInputs innerInputs innerAnswers
      simp [PFunConverter.drive]
  | succ remaining induction =>
      intro outsideInputs innerInputs innerAnswers
      simp only [PFunConverter.drive]
      have protocolEquation :
          converter.embeddedProtocol
              (outsideInputs.map fun value =>
                  (⟨target, value⟩ : AmbientInput U),
                innerAnswers.map encodeLocalOptionalOutput) =
            (converter.protocol (outsideInputs, innerAnswers)).map
              (encodeMove source target) := by
        simpa [encodeLocalOptionalOutput, encodeLocalOutput] using
          converter.embedded_protocol_apply_encoded
            outsideInputs innerAnswers
      rw [protocolEquation]
      rw [Part.bind_map, Part.map_bind]
      apply congrArg
      funext move
      cases move with
      | inl query =>
          simp only [encodeMove]
          have outputEquation :=
            continuation_ambient_output_fully_defined_encoded
              interface boundary sourceMatches system base innerInputs query
          simp only [List.map_append, List.map_singleton] at outputEquation
          have outputEquation' :
              PFunDDS.output
                  (PFunDDS.fullyDefined
                    (Anchored.continuation interface system.embed
                      (base.map encodeQuery)))
                  (innerInputs.map encodeLocalInput ++
                    [(⟨source, query⟩ : AmbientInput U)])
                  (by rw [PFunDDS.dom_fullyDefined]; simp) =
                (PFunDDS.output
                  (PFunDDS.fullyDefined
                    (continuation interface boundary sourceMatches
                      system base))
                  (innerInputs ++ [query])
                  (by rw [PFunDDS.dom_fullyDefined]; simp)).map
                    encodeLocalOutput := by
            simpa [encodeLocalInput] using outputEquation
          rw [outputEquation']
          simpa only [encodeLocalOptionalOutput, Option.map_map,
            Function.comp_def, encodeLocalOutput,
            List.map_append, List.map_singleton] using
              induction (outsideInputs := outsideInputs)
                (innerInputs := innerInputs ++ [query])
                (innerAnswers := innerAnswers ++
                  [PFunDDS.output
                    (PFunDDS.fullyDefined
                      (continuation interface boundary sourceMatches
                        system base))
                    (innerInputs ++ [query])
                    (by rw [PFunDDS.dom_fullyDefined]; simp)])
      | inr answer =>
          simp [encodeMove, encodeLocalDriveResult]

end TypedContinuation

/-! ## Closing one round and opening the next -/

namespace OuterReplay

omit [DecidableEq U.Code] in
theorem replay_core_append_outside_of_mem
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (state : FrameState interface boundary (source := source) (target := target))
    (outside :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    {result : FrameState interface boundary (source := source) (target := target)}
    (member : result ∈ replayCore interface boundary converter sourceMatches
      state outside answers)
    {outsideAnswer : FlatAnswer U
      (TargetBoundary interface boundary (target := target))}
    (answerMember : Sum.inr outsideAnswer ∈
      stateMove interface boundary converter sourceMatches result)
    (nextQuery :
      Query U (TargetBoundary interface boundary (target := target))) :
    replayCore interface boundary converter sourceMatches state
        (outside ++ [nextQuery]) answers =
      Part.some (openRound interface boundary result nextQuery) := by
  generalize measureEquation : outside.length + answers.length = measure
  induction measure using Nat.strong_induction_on generalizing
      state outside answers result with
  | h measure induction =>
      rw [replayCore.eq_def] at member
      cases outside with
      | nil =>
          cases answers with
          | nil =>
              simp only [Part.mem_some_iff] at member
              subst result
              rw [List.nil_append, replayCore.eq_def,
                Part.eq_some_iff.mpr answerMember]
              simp [replayCore]
          | cons optional rest =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · cases optional with
                | none => simp at tailMember
                | some proper =>
                    rw [Part.mem_bind_iff] at tailMember
                    obtain ⟨next, nextMember, replayMember⟩ := tailMember
                    have smaller : rest.length < measure := by omega
                    have recursive := induction rest.length smaller
                      (state := next) (outside := []) (answers := rest)
                      (result := result) replayMember answerMember
                      (by simp)
                    rw [List.nil_append, replayCore.eq_def,
                      Part.eq_some_iff.mpr moveMember]
                    simp only [Part.bind_some]
                    rw [Part.eq_some_iff.mpr nextMember, Part.bind_some]
                    exact recursive
              · simp at tailMember
      | cons nextOutside restOutside =>
          cases answers with
          | nil =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · simp at tailMember
              ·
                change result ∈ replayCore interface boundary converter
                  sourceMatches (openRound interface boundary state nextOutside)
                  restOutside [] at tailMember
                have smaller : restOutside.length < measure := by omega
                have recursive := induction restOutside.length smaller
                  (state := openRound interface boundary state nextOutside)
                  (outside := restOutside) (answers := []) (result := result)
                  tailMember answerMember (by simp)
                rw [List.cons_append, replayCore.eq_def,
                  Part.eq_some_iff.mpr moveMember]
                simp only [Part.bind_some]
                exact recursive
          | cons optional restAnswers =>
              simp at measureEquation
              obtain ⟨move, moveMember, tailMember⟩ :=
                Part.mem_bind_iff.mp member
              rcases move with query | answer
              · cases optional with
                | none => simp at tailMember
                | some proper =>
                    rw [Part.mem_bind_iff] at tailMember
                    obtain ⟨next, nextMember, replayMember⟩ := tailMember
                    have smaller :
                        (nextOutside :: restOutside).length +
                            restAnswers.length < measure := by
                      have measureValue :
                          measure = restOutside.length + 1 +
                            (restAnswers.length + 1) := measureEquation.symm
                      rw [measureValue]
                      simp only [List.length_cons]
                      omega
                    have recursive := induction
                      ((nextOutside :: restOutside).length +
                        restAnswers.length) smaller
                      (state := next)
                      (outside := nextOutside :: restOutside)
                      (answers := restAnswers) (result := result)
                      replayMember answerMember rfl
                    rw [List.cons_append, replayCore.eq_def,
                      Part.eq_some_iff.mpr moveMember]
                    simp only [Part.bind_some]
                    rw [Part.eq_some_iff.mpr nextMember, Part.bind_some]
                    exact recursive
              ·
                change result ∈ replayCore interface boundary converter
                  sourceMatches (openRound interface boundary state nextOutside)
                  restOutside (optional :: restAnswers) at tailMember
                have smaller :
                    restOutside.length + (optional :: restAnswers).length <
                      measure := by
                  have measureValue :
                      measure = restOutside.length + 1 +
                        (restAnswers.length + 1) := measureEquation.symm
                  rw [measureValue]
                  simp only [List.length_cons]
                  omega
                have recursive := induction
                  (restOutside.length + (optional :: restAnswers).length)
                  smaller
                  (state := openRound interface boundary state nextOutside)
                  (outside := restOutside)
                  (answers := optional :: restAnswers) (result := result)
                  tailMember answerMember rfl
                rw [List.cons_append, replayCore.eq_def,
                  Part.eq_some_iff.mpr moveMember]
                simp only [Part.bind_some]
                exact recursive

omit [DecidableEq U.Code] in
theorem replay_append_outside_of_mem
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (pair :
      List (Query U (TargetBoundary interface boundary (target := target))) ×
        List (Option (FlatAnswer U boundary)))
    {state : FrameState interface boundary (source := source) (target := target)}
    (member : state ∈ replay interface boundary converter sourceMatches pair)
    {outsideAnswer : FlatAnswer U
      (TargetBoundary interface boundary (target := target))}
    (answerMember : Sum.inr outsideAnswer ∈
      stateMove interface boundary converter sourceMatches state)
    (nextQuery :
      Query U (TargetBoundary interface boundary (target := target))) :
    replay interface boundary converter sourceMatches
        (pair.1 ++ [nextQuery], pair.2) =
      Part.some (openRound interface boundary state nextQuery) := by
  rcases pair with ⟨outside, answers⟩
  cases outside with
  | nil => simp [replay] at member
  | cons first rest =>
      exact replay_core_append_outside_of_mem interface boundary converter
        sourceMatches (firstState interface boundary first) rest answers member
        answerMember nextQuery

omit [DecidableEq U.Code] in
theorem replay_append_selected_some
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (member :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .local } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches (outside, answers))
    {query : U.input source}
    (queryMember : Sum.inl query ∈
      converter.protocol (localInputs, localAnswers))
    (answer : U.output source) :
    replay interface boundary converter sourceMatches
        (outside, answers ++
          [some (globalInnerAnswer interface boundary sourceMatches answer)]) =
      Part.some
        ({ localInputs := localInputs
           localAnswers := localAnswers ++ [some answer]
           phase := .local } :
          FrameState interface boundary (source := source) (target := target)) := by
  rw [replay_append_answers_of_mem interface boundary converter sourceMatches
    (outside, answers) _ member]
  rw [replayCore.eq_def]
  simp only [stateMove]
  rw [Part.eq_some_iff.mpr queryMember]
  simp [consumeAnswer, replayCore]

omit [DecidableEq U.Code] in
theorem replay_append_selected_none
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (member :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .local } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches (outside, answers))
    {query : U.input source}
    (queryMember : Sum.inl query ∈
      converter.protocol (localInputs, localAnswers)) :
    replay interface boundary converter sourceMatches
        (outside, answers ++ [none]) = Part.none := by
  rw [replay_append_answers_of_mem interface boundary converter sourceMatches
    (outside, answers) _ member]
  rw [replayCore.eq_def]
  simp only [stateMove]
  rw [Part.eq_some_iff.mpr queryMember]
  simp

omit [DecidableEq U.Code] in
theorem replay_append_pass_some
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : pending.1 ≠ interface)
    (member :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .passPending pending different } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches (outside, answers))
    (answer : FlatAnswer U boundary) (sameTag : answer.1 = pending.1) :
    replay interface boundary converter sourceMatches
        (outside, answers ++ [some answer]) =
      Part.some
        ({ localInputs := localInputs
           localAnswers := localAnswers
           phase := .passReturned
             (passAnswer interface boundary answer
               (sameTag.trans_ne different)) } :
          FrameState interface boundary (source := source) (target := target)) := by
  rw [replay_append_answers_of_mem interface boundary converter sourceMatches
    (outside, answers) _ member]
  rw [replayCore.eq_def]
  simp [stateMove, consumeAnswer, sameTag, replayCore]

omit [DecidableEq U.Code] in
theorem replay_append_pass_none
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : pending.1 ≠ interface)
    (member :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .passPending pending different } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches (outside, answers)) :
    replay interface boundary converter sourceMatches
        (outside, answers ++ [none]) = Part.none := by
  rw [replay_append_answers_of_mem interface boundary converter sourceMatches
    (outside, answers) _ member]
  rw [replayCore.eq_def]
  simp [stateMove]

end OuterReplay

/-! ## One pass-through round -/

namespace PassRound

def ResultRelated
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : pending.1 ≠ interface)
    (base : List (Query U boundary))
    (globalAnswers : List (Option (FlatAnswer U boundary)))
    (globalResult :
      FlatAnswer U (TargetBoundary interface boundary (target := target)) ×
        List (Query U boundary) × List (Option (FlatAnswer U boundary)))
    (answer : FlatAnswer U boundary) : Prop :=
  ∃ sameTag : answer.1 = pending.1,
    globalResult =
      (passAnswer interface boundary answer (sameTag.trans_ne different),
        base ++ [passQuery interface boundary pending different],
        globalAnswers ++ [some answer]) ∧
    ({ localInputs := localInputs
       localAnswers := localAnswers
       phase := .passReturned
         (passAnswer interface boundary answer (sameTag.trans_ne different)) } :
      FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalResult.2.2)

omit [DecidableEq U.Code] in
theorem framed_protocol_eq_pending
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : pending.1 ≠ interface)
    (member :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .passPending pending different } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches (outside, answers)) :
    framedProtocol interface boundary converter sourceMatches
        (outside, answers) =
      Part.some (Sum.inl (passQuery interface boundary pending different)) := by
  unfold framedProtocol
  rw [Part.eq_some_iff.mpr member, Part.bind_some]
  rfl

omit [DecidableEq U.Code] in
theorem framed_protocol_eq_returned
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (answer : FlatAnswer U
      (TargetBoundary interface boundary (target := target)))
    (member :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .passReturned answer } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches (outside, answers)) :
    framedProtocol interface boundary converter sourceMatches
        (outside, answers) = Part.some (Sum.inr answer) := by
  unfold framedProtocol
  rw [Part.eq_some_iff.mpr member, Part.bind_some]
  rfl

omit [DecidableEq U.Code] in
theorem drive_forward
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    (base : List (Query U boundary))
    (baseLive : base ∈ PFunDDS.dom system.flatten ∨ base = [])
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (globalAnswers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : pending.1 ≠ interface)
    (replayMember :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .passPending pending different } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalAnswers))
    {fuel : Nat}
    {globalResult :
      FlatAnswer U
          (TargetBoundary interface boundary (target := target)) ×
        List (Query U boundary) ×
          List (Option (FlatAnswer U boundary))}
    (driveMember : globalResult ∈
      PFunConverter.drive
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten fuel outside base globalAnswers) :
    ∃ answer : FlatAnswer U boundary,
      answer ∈ system.flatten.1
        (base ++ [passQuery interface boundary pending different]) ∧
      ResultRelated interface boundary converter sourceMatches outside
        localInputs localAnswers pending different base globalAnswers
        globalResult answer := by
  cases fuel with
  | zero => simp [PFunConverter.drive] at driveMember
  | succ remaining =>
      simp only [PFunConverter.drive] at driveMember
      rw [framed_protocol_eq_pending interface boundary converter sourceMatches
        outside globalAnswers localInputs localAnswers pending different
        replayMember] at driveMember
      simp only [Part.bind_some] at driveMember
      let completion :=
        PFunDDS.output (PFunDDS.fullyDefined system.flatten)
          (base ++ [passQuery interface boundary pending different])
          (by rw [PFunDDS.dom_fullyDefined]; simp)
      change globalResult ∈
        PFunConverter.drive
          (framedProtocol interface boundary converter sourceMatches)
          system.flatten remaining outside
          (base ++ [passQuery interface boundary pending different])
          (globalAnswers ++ [completion]) at driveMember
      cases completionEquation : completion with
      | none =>
          simp only [completionEquation] at driveMember
          have replayNone := OuterReplay.replay_append_pass_none
            interface boundary converter sourceMatches outside globalAnswers
            localInputs localAnswers pending different replayMember
          cases remaining with
          | zero => simp [PFunConverter.drive] at driveMember
          | succ next =>
              simp only [PFunConverter.drive] at driveMember
              have protocolNone :
                  framedProtocol interface boundary converter sourceMatches
                      (outside, globalAnswers ++ [none]) = Part.none := by
                unfold framedProtocol
                rw [replayNone]
                simp
              rw [protocolNone] at driveMember
              simp at driveMember
      | some answer =>
          have accepted :=
            PFunDDS.mem_of_output_fullyDefined_append_eq_some system.flatten
              base (passQuery interface boundary pending different) baseLive
              completionEquation
          obtain ⟨answerMember, answerEquation⟩ := accepted
          have sameTag : answer.1 = pending.1 := by
            have faithful := system.flatten_tag_faithful
              (base ++ [passQuery interface boundary pending different])
              answerMember
            have lastTag :
                ((base ++ [passQuery interface boundary pending different]).getLast
                  (by simp)).1 = pending.1 := by
              simp only [List.getLast_append_singleton]
              rfl
            have outputTag := faithful.trans lastTag
            rw [answerEquation] at outputTag
            exact outputTag
          have replaySome := OuterReplay.replay_append_pass_some
            interface boundary converter sourceMatches outside globalAnswers
            localInputs localAnswers pending different replayMember answer sameTag
          have returnedMember :
              ({ localInputs := localInputs
                 localAnswers := localAnswers
                 phase := .passReturned
                   (passAnswer interface boundary answer
                     (sameTag.trans_ne different)) } :
                FrameState interface boundary
                  (source := source) (target := target)) ∈
              replay interface boundary converter sourceMatches
                (outside, globalAnswers ++ [some answer]) := by
            rw [replaySome]
            exact Part.mem_some _
          simp only [completionEquation] at driveMember
          cases remaining with
          | zero => simp [PFunConverter.drive] at driveMember
          | succ next =>
              simp only [PFunConverter.drive] at driveMember
              rw [framed_protocol_eq_returned interface boundary converter
                sourceMatches outside (globalAnswers ++ [some answer])
                localInputs localAnswers
                (passAnswer interface boundary answer
                  (sameTag.trans_ne different)) returnedMember] at driveMember
              simp only [Part.bind_some, Part.mem_some_iff] at driveMember
              subst globalResult
              refine ⟨answer, ?_, sameTag, rfl, returnedMember⟩
              rw [← answerEquation]
              exact Part.get_mem answerMember

omit [DecidableEq U.Code] in
theorem drive_backward
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    (base : List (Query U boundary))
    (baseLive : base ∈ PFunDDS.dom system.flatten ∨ base = [])
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (globalAnswers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : pending.1 ≠ interface)
    (replayMember :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .passPending pending different } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalAnswers))
    (answer : FlatAnswer U boundary)
    (answerMember : answer ∈ system.flatten.1
      (base ++ [passQuery interface boundary pending different])) :
    ∃ globalResult,
      globalResult ∈
        PFunConverter.drive
          (framedProtocol interface boundary converter sourceMatches)
          system.flatten 2 outside base globalAnswers ∧
      ResultRelated interface boundary converter sourceMatches outside
        localInputs localAnswers pending different base globalAnswers
        globalResult answer := by
  have domainMember : base ++ [passQuery interface boundary pending different] ∈
      PFunDDS.dom system.flatten :=
    Part.dom_iff_mem.mpr ⟨answer, answerMember⟩
  have outputEquation :
      PFunDDS.output system.flatten
          (base ++ [passQuery interface boundary pending different])
          domainMember = answer :=
    Part.mem_unique (Part.get_mem domainMember) answerMember
  have completionEquation :
      PFunDDS.output (PFunDDS.fullyDefined system.flatten)
          (base ++ [passQuery interface boundary pending different])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = some answer :=
    (PFunDDS.output_fullyDefined_append_of_mem system.flatten base
      (passQuery interface boundary pending different) baseLive domainMember).trans
      (congrArg some outputEquation)
  have sameTag : answer.1 = pending.1 := by
    have faithful := system.flatten_tag_faithful
      (base ++ [passQuery interface boundary pending different]) domainMember
    have lastTag :
        ((base ++ [passQuery interface boundary pending different]).getLast
          (by simp)).1 = pending.1 := by
      simp only [List.getLast_append_singleton]
      rfl
    rw [outputEquation] at faithful
    exact faithful.trans lastTag
  have replaySome := OuterReplay.replay_append_pass_some
    interface boundary converter sourceMatches outside globalAnswers
    localInputs localAnswers pending different replayMember answer sameTag
  have returnedMember :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .passReturned
           (passAnswer interface boundary answer
             (sameTag.trans_ne different)) } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalAnswers ++ [some answer]) := by
    rw [replaySome]
    exact Part.mem_some _
  let globalResult :
      FlatAnswer U
          (TargetBoundary interface boundary (target := target)) ×
        List (Query U boundary) ×
          List (Option (FlatAnswer U boundary)) :=
    (passAnswer interface boundary answer (sameTag.trans_ne different),
      base ++ [passQuery interface boundary pending different],
      globalAnswers ++ [some answer])
  refine ⟨globalResult, ?_, ?_⟩
  · simp only [PFunConverter.drive]
    rw [framed_protocol_eq_pending interface boundary converter sourceMatches
      outside globalAnswers localInputs localAnswers pending different
      replayMember]
    simp only [Part.bind_some]
    rw [completionEquation]
    rw [framed_protocol_eq_returned interface boundary converter sourceMatches
      outside (globalAnswers ++ [some answer]) localInputs localAnswers
      (passAnswer interface boundary answer (sameTag.trans_ne different))
      returnedMember]
    simp [globalResult]
  · exact ⟨sameTag, rfl, returnedMember⟩

end PassRound

namespace DriveFacts

theorem result_output_mem
    {A B X Y : Type*} (protocol : ProtocolFn A B X Y)
    (system : PFunDDS.DDS X Y) :
    ∀ {fuel : Nat} {outside : List A} {inner : List X}
      {answers : List (Option Y)}
      {result : B × List X × List (Option Y)},
      result ∈ PFunConverter.drive protocol system fuel outside inner answers →
      Sum.inr result.1 ∈ protocol (outside, result.2.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro outside inner answers result member
      simp [PFunConverter.drive] at member
  | succ remaining induction =>
      intro outside inner answers result member
      simp only [PFunConverter.drive, Part.mem_bind_iff] at member
      obtain ⟨move, moveMember, tailMember⟩ := member
      rcases move with query | answer
      · exact induction tailMember
      · simp only [Part.mem_some_iff] at tailMember
        subst result
        exact moveMember

theorem result_inner_live
    {A B X Y : Type*}
    (protocol : ProtocolFn A B X Y) (system : PFunDDS.DDS X Y)
    (answersInY : AnswersInY protocol) :
    ∀ {fuel : Nat} {outside : List A} {inner : List X}
      {answers : List (Option Y)}
      {result : B × List X × List (Option Y)},
      Reach protocol (outside, answers) →
      (inner ∈ PFunDDS.dom system ∨ inner = []) →
      result ∈ PFunConverter.drive protocol system fuel outside inner answers →
      result.2.1 ∈ PFunDDS.dom system ∨ result.2.1 = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro outside inner answers result _ _ member
      simp [PFunConverter.drive] at member
  | succ remaining induction =>
      intro outside inner answers result reachable innerLive member
      simp only [PFunConverter.drive, Part.mem_bind_iff] at member
      obtain ⟨move, moveMember, tailMember⟩ := member
      rcases move with query | answer
      · let completion :=
          PFunDDS.output (PFunDDS.fullyDefined system) (inner ++ [query])
            (by rw [PFunDDS.dom_fullyDefined]; simp)
        change result ∈ PFunConverter.drive protocol system remaining outside
          (inner ++ [query]) (answers ++ [completion]) at tailMember
        cases completionEquation : completion with
        | none =>
            have nextReach := Reach.answer reachable moveMember none
            have undefined : ¬ (protocol (outside, answers ++ [none])).Dom :=
              answersInY _ nextReach (by simp)
            simp only [completionEquation] at tailMember
            cases remaining with
            | zero => simp [PFunConverter.drive] at tailMember
            | succ next =>
                simp only [PFunConverter.drive] at tailMember
                obtain ⟨nextMove, nextMoveMember, _⟩ :=
                  Part.mem_bind_iff.mp tailMember
                exact (undefined (Part.dom_iff_mem.mpr
                  ⟨nextMove, nextMoveMember⟩)).elim
        | some answerValue =>
            have accepted :=
              (PFunDDS.mem_of_output_fullyDefined_append_eq_some system inner
                query innerLive completionEquation).choose
            exact induction (Reach.answer reachable moveMember (some answerValue))
              (Or.inl accepted) (by
                simpa [completion, completionEquation] using tailMember)
      · simp only [Part.mem_some_iff] at tailMember
        subst result
        exact innerLive

end DriveFacts

/-! ## General attachment / framed-round bridge -/

namespace GeneralBridge

def encodeTargetInputs (inputs : List (U.input target)) :
    List (AmbientInput U) :=
  inputs.map fun input => (⟨target, input⟩ : AmbientInput U)

def encodeSourceAnswers (answers : List (Option (U.output source))) :
    List (Option (AmbientOutput U)) :=
  answers.map TypedContinuation.encodeLocalOptionalOutput

/-- Completed local converter history shared by the operational attachment
and the canonical all-interface frame. -/
def LocalReady
    (converter : DeterministicConverter U source target)
    (history : List (DDC.CIn (AmbientInput U) (AmbientOutput U)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source))) : Prop :=
  (history = [] ∧ localInputs = [] ∧ localAnswers = []) ∨
    (ParsesTo converter.embeddedProtocol history
        (encodeTargetInputs localInputs, encodeSourceAnswers localAnswers) ∧
      ∃ answer : AmbientOutput U,
        Sum.inr answer ∈ converter.embeddedProtocol
          (encodeTargetInputs localInputs, encodeSourceAnswers localAnswers))

theorem parses_open
    (converter : DeterministicConverter U source target)
    {history : List (DDC.CIn (AmbientInput U) (AmbientOutput U))}
    {localInputs : List (U.input target)}
    {localAnswers : List (Option (U.output source))}
    (ready : LocalReady converter history localInputs localAnswers)
    (query : U.input target) :
    ParsesTo converter.embeddedProtocol
      (history ++
        [Sum.inl (InLabel.outside,
          (⟨target, query⟩ : AmbientInput U))])
      (encodeTargetInputs (localInputs ++ [query]),
        encodeSourceAnswers localAnswers) := by
  rcases ready with ⟨rfl, rfl, rfl⟩ | ⟨parsed, answer, answerMember⟩
  · simpa [encodeTargetInputs, encodeSourceAnswers] using
      parsesTo_singleton converter.embeddedProtocol
        (⟨target, query⟩ : AmbientInput U)
  · have extended := parsesTo_snoc_out parsed answerMember
      (⟨target, query⟩ : AmbientInput U)
    simpa [encodeTargetInputs, encodeSourceAnswers, List.map_append] using
      extended

omit [DecidableEq I] [DecidableEq U.Code] in

theorem encoded_base_live
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    (baseLive : base ∈ PFunDDS.dom system.flatten ∨ base = []) :
    base.map encodeQuery ∈ PFunDDS.dom system.embed ∨
      base.map encodeQuery = [] := by
  rcases baseLive with live | empty
  · left
    change (system.embed.1 (base.map encodeQuery)).Dom
    rw [system.embed_apply_encoded base]
    exact live
  · right
    simp [empty]

omit [DecidableEq I] in
theorem native_drive_to_embedded
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    {fuel : Nat} {localInputs : List (U.input target)}
    {innerInputs : List (U.input source)}
    {localAnswers : List (Option (U.output source))}
    {result : U.output target × List (U.input source) ×
      List (Option (U.output source))}
    (member : result ∈ PFunConverter.drive converter.protocol
      (TypedContinuation.continuation interface boundary sourceMatches
        system base)
      fuel localInputs innerInputs localAnswers) :
    TypedContinuation.encodeLocalDriveResult result ∈
      PFunConverter.drive converter.embeddedProtocol
        (Anchored.continuation interface system.embed (base.map encodeQuery))
        fuel (encodeTargetInputs localInputs)
        (innerInputs.map TypedContinuation.encodeLocalInput)
        (encodeSourceAnswers localAnswers) := by
  change TypedContinuation.encodeLocalDriveResult result ∈
    PFunConverter.drive converter.embeddedProtocol
      (Anchored.continuation interface system.embed (base.map encodeQuery))
      fuel (localInputs.map fun value =>
        (⟨target, value⟩ : AmbientInput U))
      (innerInputs.map TypedContinuation.encodeLocalInput)
      (localAnswers.map TypedContinuation.encodeLocalOptionalOutput)
  rw [TypedContinuation.drive_embedded_continuation_encoded
    interface boundary converter sourceMatches system base fuel localInputs
      innerInputs localAnswers]
  exact Part.mem_map _ member

omit [DecidableEq I] in
theorem embedded_drive_to_native
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    {fuel : Nat} {localInputs : List (U.input target)}
    {innerInputs : List (U.input source)}
    {localAnswers : List (Option (U.output source))}
    {ambientResult : AmbientOutput U × List (AmbientInput U) ×
      List (Option (AmbientOutput U))}
    (member : ambientResult ∈
      PFunConverter.drive converter.embeddedProtocol
        (Anchored.continuation interface system.embed (base.map encodeQuery))
        fuel (encodeTargetInputs localInputs)
        (innerInputs.map TypedContinuation.encodeLocalInput)
        (encodeSourceAnswers localAnswers)) :
    ∃ result : U.output target × List (U.input source) ×
        List (Option (U.output source)),
      result ∈ PFunConverter.drive converter.protocol
        (TypedContinuation.continuation interface boundary sourceMatches
          system base)
        fuel localInputs innerInputs localAnswers ∧
      ambientResult = TypedContinuation.encodeLocalDriveResult result := by
  change ambientResult ∈
      PFunConverter.drive converter.embeddedProtocol
        (Anchored.continuation interface system.embed (base.map encodeQuery))
        fuel (localInputs.map fun value =>
          (⟨target, value⟩ : AmbientInput U))
        (innerInputs.map TypedContinuation.encodeLocalInput)
        (localAnswers.map TypedContinuation.encodeLocalOptionalOutput) at member
  rw [TypedContinuation.drive_embedded_continuation_encoded
    interface boundary converter sourceMatches system base fuel localInputs
      innerInputs localAnswers] at member
  obtain ⟨result, resultMember, equation⟩ :=
    (Part.mem_map_iff _).mp member
  exact ⟨result, resultMember, equation.symm⟩

omit [DecidableEq I] [DecidableEq U.Code] in
theorem encoded_global_state_eq
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) (base : List (Query U boundary))
    (innerInputs : List (U.input source))
    (innerLive : innerInputs ∈ PFunDDS.dom
        (TypedContinuation.continuation interface boundary sourceMatches
          system base) ∨ innerInputs = []) :
    Anchored.globalState interface system.embed (base.map encodeQuery)
        (innerInputs.map TypedContinuation.encodeLocalInput) =
      (base ++ TypedContinuation.queryPath interface boundary sourceMatches
        innerInputs).map encodeQuery := by
  unfold Anchored.globalState
  rw [TypedContinuation.kept_prefix_ambient_encoded interface boundary
    sourceMatches system base]
  rw [PFunDDS.keptPrefix_eq_self_of_mem_or_empty
    (TypedContinuation.continuation interface boundary sourceMatches
      system base) innerLive]
  simp [TypedContinuation.encode_query_path interface boundary sourceMatches,
    List.map_append]

end GeneralBridge

/-! ## One selected-interface round -/

namespace SelectedRound

def ResultRelated
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (localInputs : List (U.input target))
    (base : List (Query U boundary))
    (globalAnswers : List (Option (FlatAnswer U boundary)))
    (localAnswers : List (Option (U.output source)))
    (globalResult :
      FlatAnswer U (TargetBoundary interface boundary (target := target)) ×
        List (Query U boundary) ×
          List (Option (FlatAnswer U boundary)))
    (localResult :
      U.output target × List (U.input source) ×
        List (Option (U.output source))) : Prop :=
  globalResult.1 = globalAnswer interface boundary localResult.1 ∧
  globalResult.2.1 =
    base ++ TypedContinuation.queryPath interface boundary sourceMatches
      localResult.2.1 ∧
  ∃ extension : List (Option (U.output source)),
    localResult.2.2 = localAnswers ++ extension ∧
    globalResult.2.2 = globalAnswers ++
      extension.map
        (Option.map (globalInnerAnswer interface boundary sourceMatches)) ∧
    ({ localInputs := localInputs
       localAnswers := localResult.2.2
       phase := .local } :
      FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalResult.2.2)

omit [DecidableEq U.Code] in
theorem framed_protocol_eq_local_of_replay
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (member :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .local } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches (outside, answers)) :
    framedProtocol interface boundary converter sourceMatches
        (outside, answers) =
      (converter.protocol (localInputs, localAnswers)).map
        (Sum.map
          (globalQuery interface boundary sourceMatches)
          (globalAnswer interface boundary)) := by
  unfold framedProtocol
  rw [Part.eq_some_iff.mpr member, Part.bind_some]
  rfl

omit [DecidableEq U.Code] in
theorem drive_forward
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    (base : List (Query U boundary))
    (baseLive : base ∈ PFunDDS.dom system.flatten ∨ base = [])
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (globalAnswers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (localInner : List (U.input source))
    (localInnerLive : localInner ∈ PFunDDS.dom
        (TypedContinuation.continuation interface boundary sourceMatches
          system base) ∨ localInner = [])
    (replayMember :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .local } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalAnswers)) :
    ∀ {fuel : Nat}
      {globalResult :
        FlatAnswer U
            (TargetBoundary interface boundary (target := target)) ×
          List (Query U boundary) ×
            List (Option (FlatAnswer U boundary))},
      globalResult ∈
          PFunConverter.drive
            (framedProtocol interface boundary converter sourceMatches)
            system.flatten fuel outside
            (base ++ TypedContinuation.queryPath interface boundary
              sourceMatches localInner)
            globalAnswers →
        ∃ localResult,
          localResult ∈ PFunConverter.drive converter.protocol
            (TypedContinuation.continuation interface boundary sourceMatches
              system base)
            fuel localInputs localInner localAnswers ∧
          ResultRelated interface boundary converter sourceMatches outside
            localInputs base globalAnswers localAnswers globalResult
            localResult := by
  intro fuel
  induction fuel generalizing localInner localAnswers globalAnswers with
  | zero =>
      intro globalResult member
      simp [PFunConverter.drive] at member
  | succ remaining induction =>
      intro globalResult member
      simp only [PFunConverter.drive] at member
      rw [framed_protocol_eq_local_of_replay interface boundary converter
        sourceMatches outside globalAnswers localInputs localAnswers
        replayMember] at member
      rw [Part.bind_map] at member
      obtain ⟨localMove, localMoveMember, tailMember⟩ :=
        Part.mem_bind_iff.mp member
      rcases localMove with query | answer
      · simp only [Sum.map_inl] at tailMember
        have outputEquation :=
          TypedContinuation.flatten_output_eq_continuation_output
            interface boundary sourceMatches system base baseLive localInner
            query localInnerLive
        rw [outputEquation] at tailMember
        let localOutput :=
          PFunDDS.output
            (PFunDDS.fullyDefined
              (TypedContinuation.continuation interface boundary sourceMatches
                system base))
            (localInner ++ [query])
            (by rw [PFunDDS.dom_fullyDefined]; simp)
        change
          globalResult ∈
            PFunConverter.drive
              (framedProtocol interface boundary converter sourceMatches)
              system.flatten remaining outside
              ((base ++ TypedContinuation.queryPath interface boundary
                sourceMatches localInner) ++
                [globalQuery interface boundary sourceMatches query])
              (globalAnswers ++
                [localOutput.map
                  (globalInnerAnswer interface boundary sourceMatches)])
            at tailMember
        cases localOutputEquation : localOutput with
        | none =>
            simp only [localOutputEquation, Option.map_none] at tailMember
            have replayNone :=
              OuterReplay.replay_append_selected_none interface boundary
                converter sourceMatches outside globalAnswers localInputs
                localAnswers replayMember localMoveMember
            cases remaining with
            | zero => simp [PFunConverter.drive] at tailMember
            | succ next =>
                simp only [PFunConverter.drive] at tailMember
                have protocolNone :
                    framedProtocol interface boundary converter sourceMatches
                        (outside, globalAnswers ++ [none]) = Part.none := by
                  unfold framedProtocol
                  rw [replayNone]
                  simp
                rw [protocolNone] at tailMember
                simp at tailMember
        | some localAnswerValue =>
            have replaySome :=
              OuterReplay.replay_append_selected_some interface boundary
                converter sourceMatches outside globalAnswers localInputs
                localAnswers replayMember localMoveMember localAnswerValue
            have nextReplay :
                ({ localInputs := localInputs
                   localAnswers := localAnswers ++ [some localAnswerValue]
                   phase := .local } :
                  FrameState interface boundary
                    (source := source) (target := target)) ∈
                replay interface boundary converter sourceMatches
                  (outside, globalAnswers ++
                    [some (globalInnerAnswer interface boundary sourceMatches
                      localAnswerValue)]) := by
              rw [replaySome]
              exact Part.mem_some _
            have accepted :=
              PFunDDS.mem_of_output_fullyDefined_append_eq_some
                (TypedContinuation.continuation interface boundary
                  sourceMatches system base)
                localInner query localInnerLive localOutputEquation
            obtain ⟨nextLive, _answerEquation⟩ := accepted
            have tailMember' :
                globalResult ∈
                  PFunConverter.drive
                    (framedProtocol interface boundary converter sourceMatches)
                    system.flatten remaining outside
                    (base ++ TypedContinuation.queryPath interface boundary
                      sourceMatches (localInner ++ [query]))
                    (globalAnswers ++
                      [some (globalInnerAnswer interface boundary sourceMatches
                        localAnswerValue)]) := by
              simpa [TypedContinuation.query_path_append,
                localOutputEquation] using tailMember
            obtain ⟨localResult, localResultMember, related⟩ :=
              induction (localAnswers := localAnswers ++ [some localAnswerValue])
                (globalAnswers := globalAnswers ++
                  [some (globalInnerAnswer interface boundary sourceMatches
                    localAnswerValue)])
                (localInner := localInner ++ [query])
                (Or.inl nextLive) nextReplay tailMember'
            refine ⟨localResult, ?_, ?_⟩
            · exact PFunConverter.drive_mem_query converter.protocol
                (TypedContinuation.continuation interface boundary sourceMatches
                  system base)
                localMoveMember (by simpa [localOutput, localOutputEquation]
                  using localResultMember)
            · rcases related with ⟨outputEq, innerEq, extension,
                localAnswersEq, globalAnswersEq, finalReplay⟩
              refine ⟨outputEq, innerEq, some localAnswerValue :: extension,
                ?_, ?_, finalReplay⟩
              · simpa [List.append_assoc] using localAnswersEq
              · simpa [List.append_assoc] using globalAnswersEq
      · simp only [Sum.map_inr, Part.mem_some_iff] at tailMember
        subst globalResult
        refine ⟨(answer, localInner, localAnswers), ?_, ?_⟩
        · exact PFunConverter.drive_mem_answer converter.protocol
            (TypedContinuation.continuation interface boundary sourceMatches
              system base) localMoveMember remaining
        · exact ⟨rfl, rfl, [], by simp, by simp, replayMember⟩

omit [DecidableEq U.Code] in
theorem drive_backward
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    (base : List (Query U boundary))
    (baseLive : base ∈ PFunDDS.dom system.flatten ∨ base = [])
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (globalAnswers : List (Option (FlatAnswer U boundary)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (localInner : List (U.input source))
    (localInnerLive : localInner ∈ PFunDDS.dom
        (TypedContinuation.continuation interface boundary sourceMatches
          system base) ∨ localInner = [])
    (replayMember :
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .local } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalAnswers)) :
    ∀ {fuel : Nat}
      {localResult :
        U.output target × List (U.input source) ×
          List (Option (U.output source))},
      localResult ∈ PFunConverter.drive converter.protocol
          (TypedContinuation.continuation interface boundary sourceMatches
            system base)
          fuel localInputs localInner localAnswers →
        ∃ globalResult,
          globalResult ∈
            PFunConverter.drive
              (framedProtocol interface boundary converter sourceMatches)
              system.flatten fuel outside
              (base ++ TypedContinuation.queryPath interface boundary
                sourceMatches localInner)
              globalAnswers ∧
          ResultRelated interface boundary converter sourceMatches outside
            localInputs base globalAnswers localAnswers globalResult
            localResult := by
  intro fuel
  induction fuel generalizing localInner localAnswers globalAnswers with
  | zero =>
      intro localResult member
      simp [PFunConverter.drive] at member
  | succ remaining induction =>
      intro localResult member
      simp only [PFunConverter.drive, Part.mem_bind_iff] at member
      obtain ⟨localMove, localMoveMember, tailMember⟩ := member
      rcases localMove with query | answer
      · let localOutput :=
          PFunDDS.output
            (PFunDDS.fullyDefined
              (TypedContinuation.continuation interface boundary sourceMatches
                system base))
            (localInner ++ [query])
            (by rw [PFunDDS.dom_fullyDefined]; simp)
        change localResult ∈
          PFunConverter.drive converter.protocol
            (TypedContinuation.continuation interface boundary sourceMatches
              system base)
            remaining localInputs (localInner ++ [query])
              (localAnswers ++ [localOutput]) at tailMember
        cases localOutputEquation : localOutput with
        | none =>
            have currentReach :
                Reach converter.protocol (localInputs, localAnswers) := by
              have coherent := replay_coherent interface boundary converter
                sourceMatches (outside, globalAnswers) replayMember
              exact coherent
            have nextReach : Reach converter.protocol
                (localInputs, localAnswers ++ [none]) :=
              Reach.answer currentReach localMoveMember none
            have nextUndefined :
                ¬ (converter.protocol
                  (localInputs, localAnswers ++ [none])).Dom :=
              converter.isDDC.1 _ nextReach (by simp)
            simp only [localOutputEquation] at tailMember
            cases remaining with
            | zero => simp [PFunConverter.drive] at tailMember
            | succ next =>
                simp only [PFunConverter.drive] at tailMember
                obtain ⟨move, moveMember, _⟩ :=
                  Part.mem_bind_iff.mp tailMember
                exact (nextUndefined (Part.dom_iff_mem.mpr
                  ⟨move, moveMember⟩)).elim
        | some localAnswerValue =>
            have nextLive :=
              (PFunDDS.mem_of_output_fullyDefined_append_eq_some
                (TypedContinuation.continuation interface boundary
                  sourceMatches system base)
                localInner query localInnerLive localOutputEquation).choose
            have replaySome :=
              OuterReplay.replay_append_selected_some interface boundary
                converter sourceMatches outside globalAnswers localInputs
                localAnswers replayMember localMoveMember localAnswerValue
            have nextReplay :
                ({ localInputs := localInputs
                   localAnswers := localAnswers ++ [some localAnswerValue]
                   phase := .local } :
                  FrameState interface boundary
                    (source := source) (target := target)) ∈
                replay interface boundary converter sourceMatches
                  (outside, globalAnswers ++
                    [some (globalInnerAnswer interface boundary sourceMatches
                      localAnswerValue)]) := by
              rw [replaySome]
              exact Part.mem_some _
            have tailMember' :
                localResult ∈
                  PFunConverter.drive converter.protocol
                    (TypedContinuation.continuation interface boundary
                      sourceMatches system base)
                    remaining localInputs (localInner ++ [query])
                    (localAnswers ++ [some localAnswerValue]) := by
              simpa [localOutput, localOutputEquation] using tailMember
            obtain ⟨globalResult, globalResultMember, related⟩ :=
              induction
                (localAnswers := localAnswers ++ [some localAnswerValue])
                (globalAnswers := globalAnswers ++
                  [some (globalInnerAnswer interface boundary sourceMatches
                    localAnswerValue)])
                (localInner := localInner ++ [query])
                (Or.inl nextLive) nextReplay tailMember'
            refine ⟨globalResult, ?_, ?_⟩
            · simp only [PFunConverter.drive]
              rw [framed_protocol_eq_local_of_replay interface boundary
                converter sourceMatches outside globalAnswers localInputs
                localAnswers replayMember]
              rw [Part.bind_map]
              apply Part.mem_bind_iff.mpr
              refine ⟨Sum.inl query, localMoveMember, ?_⟩
              simp only [Sum.map_inl]
              have outputEquation :=
                TypedContinuation.flatten_output_eq_continuation_output
                  interface boundary sourceMatches system base baseLive
                  localInner query localInnerLive
              rw [outputEquation]
              simpa [TypedContinuation.query_path_append, localOutput,
                localOutputEquation] using globalResultMember
            · rcases related with ⟨outputEq, innerEq, extension,
                localAnswersEq, globalAnswersEq, finalReplay⟩
              refine ⟨outputEq, innerEq, some localAnswerValue :: extension,
                ?_, ?_, finalReplay⟩
              · simpa [List.append_assoc] using localAnswersEq
              · simpa [List.append_assoc] using globalAnswersEq
      · simp only [Part.mem_some_iff] at tailMember
        subst localResult
        let globalResult :
            FlatAnswer U
                (TargetBoundary interface boundary (target := target)) ×
              List (Query U boundary) ×
                List (Option (FlatAnswer U boundary)) :=
          (globalAnswer interface boundary answer,
            base ++ TypedContinuation.queryPath interface boundary
              sourceMatches localInner,
            globalAnswers)
        refine ⟨globalResult, ?_, ?_⟩
        · simp only [PFunConverter.drive]
          rw [framed_protocol_eq_local_of_replay interface boundary converter
            sourceMatches outside globalAnswers localInputs localAnswers
            replayMember]
          rw [Part.bind_map]
          exact Part.mem_bind_iff.mpr
            ⟨Sum.inr answer, localMoveMember, by simp [globalResult]⟩
        · exact ⟨rfl, rfl, [], by simp, by simp [globalResult], replayMember⟩

end SelectedRound

namespace SelectedEntry

def ResultRelated
    (converter : DeterministicConverter U source target)
    (roundInputs : List (U.input target))
    (generalResult : AmbientOutput U ×
      (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U)))
    (localResult : U.output target × List (U.input source) ×
      List (Option (U.output source)))
    (strictResult :
      FlatAnswer U (TargetBoundary interface boundary (target := target)) ×
        List (Query U boundary) × List (Option (FlatAnswer U boundary))) : Prop :=
  generalResult.1 = (⟨target, localResult.1⟩ : AmbientOutput U) ∧
  GeneralBridge.LocalReady converter generalResult.2.1 roundInputs
    localResult.2.2 ∧
  generalResult.2.2 = strictResult.2.1.map encodeQuery

theorem general_to_strict
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    (base : List (Query U boundary))
    (baseLive : base ∈ PFunDDS.dom system.flatten ∨ base = [])
    (converterHistory :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (ready : GeneralBridge.LocalReady converter converterHistory
      localInputs localAnswers)
    (query : U.input target)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (globalAnswers : List (Option (FlatAnswer U boundary)))
    (openedMember :
      ({ localInputs := localInputs ++ [query]
         localAnswers := localAnswers
         phase := .local } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalAnswers))
    {generalResult : AmbientOutput U ×
      (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U))}
    (generalMember : generalResult ∈
      PFunConverter.General.attachResolve interface converter.embeddedDDC
        system.embed
        (converterHistory ++
            [Sum.inl (InLabel.outside,
              (⟨target, query⟩ : AmbientInput U))],
          base.map encodeQuery)) :
    ∃ fuel localResult strictResult,
      localResult ∈ PFunConverter.drive converter.protocol
        (TypedContinuation.continuation interface boundary sourceMatches
          system base)
        fuel (localInputs ++ [query]) [] localAnswers ∧
      strictResult ∈ PFunConverter.drive
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten fuel outside base globalAnswers ∧
      SelectedRound.ResultRelated interface boundary converter sourceMatches
        outside (localInputs ++ [query]) base globalAnswers localAnswers
        strictResult localResult ∧
      ResultRelated interface boundary converter (localInputs ++ [query])
        generalResult localResult strictResult := by
  let openedHistory := converterHistory ++
    [Sum.inl (InLabel.outside,
      (⟨target, query⟩ : AmbientInput U))]
  have parsedOpen : ParsesTo converter.embeddedProtocol openedHistory
      (GeneralBridge.encodeTargetInputs (localInputs ++ [query]),
        GeneralBridge.encodeSourceAnswers localAnswers) := by
    exact GeneralBridge.parses_open converter ready query
  have encodedBaseLive :=
    GeneralBridge.encoded_base_live (U := U) (boundary := boundary)
      (system := system) (base := base) (baseLive := baseLive)
  have stateEquation :
      Anchored.stateMap interface system.embed (base.map encodeQuery)
          (openedHistory, []) = (openedHistory, base.map encodeQuery) := by
    simp [Anchored.stateMap, Anchored.globalState, Anchored.tagAt,
      PFunDDS.keptPrefix]
  have generalMember' := generalMember
  change generalResult ∈
    PFunConverter.General.attachResolve interface converter.embeddedDDC
      system.embed (openedHistory, base.map encodeQuery) at generalMember'
  rw [← stateEquation,
    Anchored.attach_resolve_eq_map interface converter.embeddedDDC system.embed
      (base.map encodeQuery) encodedBaseLive (openedHistory, [])] at generalMember'
  obtain ⟨ambientLocalResult, resolveMember, generalEquation⟩ :=
    (Part.mem_map_iff _).mp generalMember'
  obtain ⟨fuel, finalAmbientAnswers, ambientDriveMember, finalParsed,
      finalOutputMember⟩ :=
    PFunConverter.drive_of_resolve_toDDC converter.embeddedProtocol
      (Anchored.continuation interface system.embed (base.map encodeQuery))
      resolveMember
      (GeneralBridge.encodeTargetInputs (localInputs ++ [query]))
      (GeneralBridge.encodeSourceAnswers localAnswers) parsedOpen
  obtain ⟨localResult, localDriveMember, ambientResultEquation⟩ :=
    GeneralBridge.embedded_drive_to_native interface boundary converter
      sourceMatches system base (fuel := fuel)
      (localInputs := localInputs ++ [query]) (innerInputs := [])
      (localAnswers := localAnswers)
      (ambientResult :=
        (ambientLocalResult.1, ambientLocalResult.2.2,
          finalAmbientAnswers)) ambientDriveMember
  obtain ⟨strictResult, strictDriveMember, strictRelated⟩ :=
    SelectedRound.drive_backward interface boundary converter sourceMatches
      system base baseLive outside globalAnswers (localInputs ++ [query])
      localAnswers [] (Or.inr rfl) openedMember localDriveMember
  have strictDriveMember' : strictResult ∈ PFunConverter.drive
      (framedProtocol interface boundary converter sourceMatches)
      system.flatten fuel outside base globalAnswers := by
    simpa [TypedContinuation.query_path_nil] using strictDriveMember
  refine ⟨fuel, localResult, strictResult, localDriveMember,
    strictDriveMember', strictRelated, ?_⟩
  have ambientAnswerEquation :
      ambientLocalResult.1 =
        (⟨target, localResult.1⟩ : AmbientOutput U) := by
    exact congrArg Prod.fst ambientResultEquation
  have ambientInnerEquation :
      ambientLocalResult.2.2 =
        localResult.2.1.map TypedContinuation.encodeLocalInput := by
    exact congrArg (fun result => result.2.1) ambientResultEquation
  have ambientAnswersEquation :
      finalAmbientAnswers =
        GeneralBridge.encodeSourceAnswers localResult.2.2 := by
    have equation := congrArg (fun result => result.2.2) ambientResultEquation
    simpa [GeneralBridge.encodeSourceAnswers,
      TypedContinuation.encodeLocalDriveResult] using equation
  rw [ambientAnswersEquation] at finalParsed finalOutputMember
  have openedReach : Reach converter.protocol
      (localInputs ++ [query], localAnswers) := by
    have coherent := replay_coherent interface boundary converter sourceMatches
      (outside, globalAnswers) openedMember
    exact coherent
  have finalInnerLive := DriveFacts.result_inner_live converter.protocol
    (TypedContinuation.continuation interface boundary sourceMatches system base)
    converter.isDDC.1 openedReach (Or.inr rfl) localDriveMember
  have globalStateEquation := GeneralBridge.encoded_global_state_eq
    interface boundary sourceMatches system base localResult.2.1 finalInnerLive
  have strictInnerEquation := strictRelated.2.1
  rw [← generalEquation]
  refine ⟨ambientAnswerEquation, ?_, ?_⟩
  · exact Or.inr ⟨finalParsed, ambientLocalResult.1, finalOutputMember⟩
  · change
      Anchored.globalState interface system.embed (base.map encodeQuery)
          ambientLocalResult.2.2 = strictResult.2.1.map encodeQuery
    rw [ambientInnerEquation, globalStateEquation, strictInnerEquation]

theorem strict_to_general
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    (base : List (Query U boundary))
    (baseLive : base ∈ PFunDDS.dom system.flatten ∨ base = [])
    (converterHistory :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)))
    (localInputs : List (U.input target))
    (localAnswers : List (Option (U.output source)))
    (ready : GeneralBridge.LocalReady converter converterHistory
      localInputs localAnswers)
    (query : U.input target)
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (globalAnswers : List (Option (FlatAnswer U boundary)))
    (openedMember :
      ({ localInputs := localInputs ++ [query]
         localAnswers := localAnswers
         phase := .local } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside, globalAnswers))
    {fuel : Nat}
    {strictResult :
      FlatAnswer U (TargetBoundary interface boundary (target := target)) ×
        List (Query U boundary) × List (Option (FlatAnswer U boundary))}
    (strictMember : strictResult ∈ PFunConverter.drive
      (framedProtocol interface boundary converter sourceMatches)
      system.flatten fuel outside base globalAnswers) :
    ∃ localResult generalResult,
      localResult ∈ PFunConverter.drive converter.protocol
        (TypedContinuation.continuation interface boundary sourceMatches
          system base)
        fuel (localInputs ++ [query]) [] localAnswers ∧
      generalResult ∈
        PFunConverter.General.attachResolve interface converter.embeddedDDC
          system.embed
          (converterHistory ++
              [Sum.inl (InLabel.outside,
                (⟨target, query⟩ : AmbientInput U))],
            base.map encodeQuery) ∧
      SelectedRound.ResultRelated interface boundary converter sourceMatches
        outside (localInputs ++ [query]) base globalAnswers localAnswers
        strictResult localResult ∧
      ResultRelated interface boundary converter (localInputs ++ [query])
        generalResult localResult strictResult := by
  have strictMember' : strictResult ∈ PFunConverter.drive
      (framedProtocol interface boundary converter sourceMatches)
      system.flatten fuel outside
      (base ++ TypedContinuation.queryPath interface boundary sourceMatches [])
      globalAnswers := by
    simpa [TypedContinuation.query_path_nil] using strictMember
  obtain ⟨localResult, localDriveMember, strictRelated⟩ :=
    SelectedRound.drive_forward interface boundary converter sourceMatches
      system base baseLive outside globalAnswers (localInputs ++ [query])
      localAnswers [] (Or.inr rfl) openedMember strictMember'
  let openedHistory := converterHistory ++
    [Sum.inl (InLabel.outside,
      (⟨target, query⟩ : AmbientInput U))]
  have parsedOpen : ParsesTo converter.embeddedProtocol openedHistory
      (GeneralBridge.encodeTargetInputs (localInputs ++ [query]),
        GeneralBridge.encodeSourceAnswers localAnswers) :=
    GeneralBridge.parses_open converter ready query
  have ambientDriveMember := GeneralBridge.native_drive_to_embedded
    interface boundary converter sourceMatches system base localDriveMember
  obtain ⟨finalHistory, finalParsed, finalOutputMember, resolveMember⟩ :=
    PFunConverter.resolve_toDDC_of_drive converter.embeddedProtocol
      (Anchored.continuation interface system.embed (base.map encodeQuery))
      parsedOpen ambientDriveMember
  let ambientLocalResult : AmbientOutput U ×
      (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientInput U)) :=
    ((⟨target, localResult.1⟩ : AmbientOutput U),
      finalHistory,
      localResult.2.1.map TypedContinuation.encodeLocalInput)
  have resolveMember' : ambientLocalResult ∈
      converter.embeddedDDC.resolve
        (Anchored.continuation interface system.embed (base.map encodeQuery))
        (openedHistory, []) := by
    exact resolveMember
  let generalResult := Anchored.resultMap interface system.embed
    (base.map encodeQuery) ambientLocalResult
  have encodedBaseLive := GeneralBridge.encoded_base_live
    (U := U) (boundary := boundary) (system := system) (base := base)
    (baseLive := baseLive)
  have mappedMember : generalResult ∈
      (converter.embeddedDDC.resolve
        (Anchored.continuation interface system.embed (base.map encodeQuery))
        (openedHistory, [])).map
          (Anchored.resultMap interface system.embed (base.map encodeQuery)) :=
    Part.mem_map _ resolveMember'
  have stateEquation :
      Anchored.stateMap interface system.embed (base.map encodeQuery)
          (openedHistory, []) = (openedHistory, base.map encodeQuery) := by
    simp [Anchored.stateMap, Anchored.globalState, Anchored.tagAt,
      PFunDDS.keptPrefix]
  have generalMember : generalResult ∈
      PFunConverter.General.attachResolve interface converter.embeddedDDC
        system.embed (openedHistory, base.map encodeQuery) := by
    rw [← stateEquation]
    rw [Anchored.attach_resolve_eq_map interface converter.embeddedDDC
      system.embed (base.map encodeQuery) encodedBaseLive
      (openedHistory, [])]
    exact mappedMember
  have generalMember' : generalResult ∈
      PFunConverter.General.attachResolve interface converter.embeddedDDC
        system.embed
        (converterHistory ++
            [Sum.inl (InLabel.outside,
              (⟨target, query⟩ : AmbientInput U))],
          base.map encodeQuery) := by
    exact generalMember
  have openedReach : Reach converter.protocol
      (localInputs ++ [query], localAnswers) := by
    have coherent := replay_coherent interface boundary converter sourceMatches
      (outside, globalAnswers) openedMember
    exact coherent
  have finalInnerLive := DriveFacts.result_inner_live converter.protocol
    (TypedContinuation.continuation interface boundary sourceMatches system base)
    converter.isDDC.1 openedReach (Or.inr rfl) localDriveMember
  have globalStateEquation := GeneralBridge.encoded_global_state_eq
    interface boundary sourceMatches system base localResult.2.1 finalInnerLive
  have strictInnerEquation := strictRelated.2.1
  refine ⟨localResult, generalResult, localDriveMember, generalMember',
    strictRelated, ?_⟩
  refine ⟨rfl, ?_, ?_⟩
  · exact Or.inr ⟨finalParsed,
      (⟨target, localResult.1⟩ : AmbientOutput U), finalOutputMember⟩
  · change
      Anchored.globalState interface system.embed (base.map encodeQuery)
          (localResult.2.1.map TypedContinuation.encodeLocalInput) =
        strictResult.2.1.map encodeQuery
    rw [globalStateEquation, strictInnerEquation]

end SelectedEntry

namespace FramingEncoding

omit [DecidableEq U.Code] in

theorem encode_pass_query
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : pending.1 ≠ interface) :
    encodeQuery (passQuery interface boundary pending different) =
      encodeQuery pending := by
  rcases pending with ⟨pendingInterface, value⟩
  change pendingInterface ≠ interface at different
  simp [passQuery, encodeQuery, TargetBoundary,
    replace_boundary_ne boundary different target]

omit [DecidableEq U.Code] in

theorem encode_pass_answer
    (answer : FlatAnswer U boundary)
    (different : answer.1 ≠ interface) :
    encodeAnswer
        (passAnswer interface boundary (target := target) answer different) =
      encodeAnswer answer := by
  rcases answer with ⟨answerInterface, value⟩
  change answerInterface ≠ interface at different
  simp [passAnswer, encodeAnswer, TargetBoundary,
    replace_boundary_ne boundary different target]

omit [DecidableEq U.Code] in

theorem encode_global_answer (answer : U.output target) :
    encodeAnswer (globalAnswer interface boundary answer) =
      (⟨target, answer⟩ : AmbientOutput U) := by
  simp [globalAnswer, encodeAnswer, TargetBoundary]

omit [DecidableEq U.Code] in

theorem selected_payload
    (pending : Query U
      (TargetBoundary interface boundary (target := target)))
    (same : pending.1 = interface) :
    (encodeQuery pending).2 =
      (⟨target, localInput interface boundary pending same⟩ :
        AmbientInput U) := by
  rcases pending with ⟨pendingInterface, value⟩
  change pendingInterface = interface at same
  subst pendingInterface
  simp [encodeQuery, localInput, TargetBoundary]

end FramingEncoding

namespace OuterBridge

/-- Relation at an outer-round boundary.  The left disjunct is the unique
pre-query state; the right records a completed framed round. -/
def Cursor
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    (generalState :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U))
    (outside : List
      (Query U (TargetBoundary interface boundary (target := target))))
    (inner : List (Query U boundary))
    (answers : List (Option (FlatAnswer U boundary))) : Prop :=
  (generalState = ([], []) ∧ outside = [] ∧ inner = [] ∧ answers = []) ∨
    ∃ state : FrameState interface boundary
        (source := source) (target := target),
      GeneralBridge.LocalReady converter generalState.1
        state.localInputs state.localAnswers ∧
      generalState.2 = inner.map encodeQuery ∧
      (generalState.2 ∈ PFunDDS.dom system.embed ∨ generalState.2 = []) ∧
      state ∈ replay interface boundary converter sourceMatches
        (outside, answers) ∧
      ∃ answer, Sum.inr answer ∈
        stateMove interface boundary converter sourceMatches state

theorem native_base_live
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    {generalState :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U)}
    {outside : List
      (Query U (TargetBoundary interface boundary (target := target)))}
    {inner : List (Query U boundary)}
    {answers : List (Option (FlatAnswer U boundary))}
    (cursor : Cursor interface boundary converter sourceMatches system
      generalState outside inner answers) :
    inner ∈ PFunDDS.dom system.flatten ∨ inner = [] := by
  rcases cursor with ⟨_state, _outside, rfl, _answers⟩ |
      ⟨state, _ready, baseEquation, baseLive, _replay, _output⟩
  · exact Or.inr rfl
  · rw [baseEquation] at baseLive
    rcases baseLive with live | empty
    · left
      change (system.flatten.1 inner).Dom
      have encoded := system.embed_apply_encoded inner
      change (system.embed.1 (inner.map encodeQuery)).Dom at live
      rw [encoded] at live
      exact live
    · right
      simpa using (List.map_eq_nil_iff.mp empty)

theorem open_selected
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    {generalState :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U)}
    {outside : List
      (Query U (TargetBoundary interface boundary (target := target)))}
    {inner : List (Query U boundary)}
    {answers : List (Option (FlatAnswer U boundary))}
    (cursor : Cursor interface boundary converter sourceMatches system
      generalState outside inner answers)
    (query : Query U
      (TargetBoundary interface boundary (target := target)))
    (same : query.1 = interface) :
    ∃ localInputs localAnswers,
      GeneralBridge.LocalReady converter generalState.1
        localInputs localAnswers ∧
      ({ localInputs := localInputs ++
          [localInput interface boundary query same]
         localAnswers := localAnswers
         phase := .local } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside ++ [query], answers) := by
  rcases cursor with ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨state, ready, _baseEquation, _baseLive, replayMember,
        answer, answerMember⟩
  · refine ⟨[], [], Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
    simp [replay, firstState, openRound, same, replayCore]
  · refine ⟨state.localInputs, state.localAnswers, ready, ?_⟩
    have opened := OuterReplay.replay_append_outside_of_mem
      interface boundary converter sourceMatches (outside, answers)
      replayMember answerMember query
    rw [opened]
    simp [openRound, same]

theorem open_pass
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    {generalState :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U)}
    {outside : List
      (Query U (TargetBoundary interface boundary (target := target)))}
    {inner : List (Query U boundary)}
    {answers : List (Option (FlatAnswer U boundary))}
    (cursor : Cursor interface boundary converter sourceMatches system
      generalState outside inner answers)
    (query : Query U
      (TargetBoundary interface boundary (target := target)))
    (different : query.1 ≠ interface) :
    ∃ localInputs localAnswers,
      GeneralBridge.LocalReady converter generalState.1
        localInputs localAnswers ∧
      ({ localInputs := localInputs
         localAnswers := localAnswers
         phase := .passPending query different } :
        FrameState interface boundary (source := source) (target := target)) ∈
      replay interface boundary converter sourceMatches
        (outside ++ [query], answers) := by
  rcases cursor with ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨state, ready, _baseEquation, _baseLive, replayMember,
        answer, answerMember⟩
  · refine ⟨[], [], Or.inl ⟨rfl, rfl, rfl⟩, ?_⟩
    simp [replay, firstState, openRound, different, replayCore]
  · refine ⟨state.localInputs, state.localAnswers, ready, ?_⟩
    have opened := OuterReplay.replay_append_outside_of_mem
      interface boundary converter sourceMatches (outside, answers)
      replayMember answerMember query
    rw [opened]
    simp [openRound, different]

theorem encoded_inner
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    {generalState :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U)}
    {outside : List
      (Query U (TargetBoundary interface boundary (target := target)))}
    {inner : List (Query U boundary)}
    {answers : List (Option (FlatAnswer U boundary))}
    (cursor : Cursor interface boundary converter sourceMatches system
      generalState outside inner answers) :
    generalState.2 = inner.map encodeQuery := by
  rcases cursor with ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨_state, _ready, equation, _live, _replay, _output⟩
  · rfl
  · exact equation

/-- One ambient `General.attachEntryStep` is simulated by one strict framed
round.  The fuel is existential here; the outer fold takes maxima. -/
theorem entry_general_to_strict
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    {generalState :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U)}
    {outside : List
      (Query U (TargetBoundary interface boundary (target := target)))}
    {inner : List (Query U boundary)}
    {answers : List (Option (FlatAnswer U boundary))}
    (cursor : Cursor interface boundary converter sourceMatches system
      generalState outside inner answers)
    (query : Query U
      (TargetBoundary interface boundary (target := target)))
    {generalResult : AmbientOutput U ×
      (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U))}
    (generalMember : generalResult ∈
      PFunConverter.General.attachEntryStep interface converter.embeddedDDC
        system.embed generalState (encodeQuery query)) :
    ∃ fuel strictResult,
      strictResult ∈ PFunConverter.drive
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten fuel (outside ++ [query]) inner answers ∧
      generalResult.1 = encodeAnswer strictResult.1 ∧
      Cursor interface boundary converter sourceMatches system
        generalResult.2 (outside ++ [query]) strictResult.2.1
          strictResult.2.2 := by
  have baseLive := native_base_live interface boundary converter sourceMatches
    system cursor
  have baseEquation := encoded_inner interface boundary converter sourceMatches
    system cursor
  by_cases same : query.1 = interface
  · have encodedSame : (encodeQuery query).1 = interface := by
      simpa [encodeQuery] using same
    rw [PFunConverter.General.attachEntryStep, if_pos encodedSame] at generalMember
    rw [baseEquation] at generalMember
    rw [FramingEncoding.selected_payload interface boundary query same] at generalMember
    obtain ⟨localInputs, localAnswers, ready, openedMember⟩ :=
      open_selected interface boundary converter sourceMatches system cursor
        query same
    obtain ⟨fuel, localResult, strictResult, localDriveMember,
        strictDriveMember, strictRelated, entryRelated⟩ :=
      SelectedEntry.general_to_strict interface boundary converter
        sourceMatches system inner baseLive generalState.1 localInputs
        localAnswers ready (localInput interface boundary query same)
        (outside ++ [query]) answers openedMember generalMember
    rcases strictRelated with
      ⟨strictOutputEquation, strictInnerEquation, extension,
        localAnswersEquation, globalAnswersEquation, finalReplay⟩
    rcases entryRelated with
      ⟨generalOutputEquation, finalReady, generalBaseEquation⟩
    have openedReach : Reach converter.protocol
        (localInputs ++ [localInput interface boundary query same],
          localAnswers) := by
      exact replay_coherent interface boundary converter sourceMatches
        (outside ++ [query], answers) openedMember
    have finalLocalLive := DriveFacts.result_inner_live converter.protocol
      (TypedContinuation.continuation interface boundary sourceMatches
        system inner)
      converter.isDDC.1 openedReach (Or.inr rfl) localDriveMember
    have finalBaseLive :
        strictResult.2.1 ∈ PFunDDS.dom system.flatten ∨
          strictResult.2.1 = [] := by
      rw [strictInnerEquation]
      rcases finalLocalLive with live | empty
      · exact Or.inl live.2
      · rw [empty, TypedContinuation.query_path_nil, List.append_nil]
        exact baseLive
    have finalAmbientBaseLive :
        generalResult.2.2 ∈ PFunDDS.dom system.embed ∨
          generalResult.2.2 = [] := by
      rw [generalBaseEquation]
      exact GeneralBridge.encoded_base_live (U := U) (boundary := boundary)
        (system := system) (base := strictResult.2.1)
        (baseLive := finalBaseLive)
    let finalState : FrameState interface boundary
        (source := source) (target := target) :=
      { localInputs :=
          localInputs ++ [localInput interface boundary query same]
        localAnswers := localResult.2.2
        phase := .local }
    have localOutputMember := DriveFacts.result_output_mem converter.protocol
      (TypedContinuation.continuation interface boundary sourceMatches
        system inner)
      localDriveMember
    have finalMove : Sum.inr
        (globalAnswer interface boundary localResult.1) ∈
        stateMove interface boundary converter sourceMatches finalState := by
      simp only [finalState, stateMove, Part.mem_map_iff]
      exact ⟨Sum.inr localResult.1, localOutputMember, by simp⟩
    refine ⟨fuel, strictResult, strictDriveMember, ?_, Or.inr ?_⟩
    · calc
        generalResult.1 =
            (⟨target, localResult.1⟩ : AmbientOutput U) :=
          generalOutputEquation
        _ = encodeAnswer strictResult.1 := by
          rw [strictOutputEquation,
            FramingEncoding.encode_global_answer]
    · exact ⟨finalState, finalReady, generalBaseEquation,
        finalAmbientBaseLive,
        finalReplay, globalAnswer interface boundary localResult.1, finalMove⟩
  · have encodedDifferent : (encodeQuery query).1 ≠ interface := by
      simpa [encodeQuery] using same
    rw [PFunConverter.General.attachEntryStep, if_neg encodedDifferent,
      Part.mem_map_iff] at generalMember
    obtain ⟨ambientAnswer, ambientMember, rfl⟩ := generalMember
    obtain ⟨localInputs, localAnswers, ready, openedMember⟩ :=
      open_pass interface boundary converter sourceMatches system cursor query
        same
    have ambientMember' : ambientAnswer ∈ system.embed.1
        ((inner ++ [passQuery interface boundary query same]).map
          encodeQuery) := by
      rw [List.map_append, List.map_singleton,
        FramingEncoding.encode_pass_query interface boundary query same]
      rw [← baseEquation]
      exact ambientMember
    rw [system.embed_apply_encoded] at ambientMember'
    obtain ⟨answer, answerMember, encodedAnswerEquation⟩ :=
      (Part.mem_map_iff _).mp ambientMember'
    obtain ⟨strictResult, strictDriveMember, passRelated⟩ :=
      PassRound.drive_backward interface boundary converter sourceMatches
        system inner baseLive (outside ++ [query]) answers localInputs
        localAnswers query same openedMember answer answerMember
    rcases passRelated with
      ⟨sameTag, strictResultEquation, finalReplay⟩
    have finalBaseLive :
        strictResult.2.1 ∈ PFunDDS.dom system.flatten ∨
          strictResult.2.1 = [] := by
      rw [strictResultEquation]
      exact Or.inl (Part.dom_iff_mem.mpr ⟨answer, answerMember⟩)
    let returned := passAnswer interface boundary (target := target) answer
      (sameTag.trans_ne same)
    let finalState : FrameState interface boundary
        (source := source) (target := target) :=
      { localInputs := localInputs
        localAnswers := localAnswers
        phase := .passReturned returned }
    have finalMove : Sum.inr returned ∈
        stateMove interface boundary converter sourceMatches finalState := by
      simp [finalState, stateMove, returned]
    have strictOutputEquation : strictResult.1 = returned := by
      rw [strictResultEquation]
    have encodedStrictOutput : encodeAnswer strictResult.1 =
        encodeAnswer answer := by
      rw [strictOutputEquation]
      exact FramingEncoding.encode_pass_answer interface boundary answer
        (sameTag.trans_ne same)
    have finalGeneralBaseEquation :
        generalState.2 ++ [encodeQuery query] =
          strictResult.2.1.map encodeQuery := by
      rw [baseEquation, strictResultEquation, List.map_append,
        List.map_singleton,
        FramingEncoding.encode_pass_query interface boundary query same]
    have finalAmbientBaseLive :
        generalState.2 ++ [encodeQuery query] ∈
            PFunDDS.dom system.embed ∨
          generalState.2 ++ [encodeQuery query] = [] := by
      rw [finalGeneralBaseEquation]
      exact GeneralBridge.encoded_base_live (U := U) (boundary := boundary)
        (system := system) (base := strictResult.2.1)
        (baseLive := finalBaseLive)
    refine ⟨2, strictResult, strictDriveMember, ?_, Or.inr ?_⟩
    · exact encodedAnswerEquation.symm.trans encodedStrictOutput.symm
    · refine ⟨finalState, ready, finalGeneralBaseEquation,
        finalAmbientBaseLive, ?_, returned,
        finalMove⟩
      · simpa [finalState, returned] using finalReplay

/-- The full ambient outer driver is simulated by the strict framed driver.
Per-round fuels are synchronized by monotonicity at their maximum. -/
theorem drive_general_to_strict
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    ∀
      {generalState :
        List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
          List (AmbientQuery I U)}
      {outside : List
        (Query U (TargetBoundary interface boundary (target := target)))}
      {inner : List (Query U boundary)}
      {answers : List (Option (FlatAnswer U boundary))},
      Cursor interface boundary converter sourceMatches system
          generalState outside inner answers →
      ∀ (rest : List
        (Query U (TargetBoundary interface boundary (target := target))))
        {generalResult : List (AmbientOutput U) ×
          (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
            List (AmbientQuery I U))},
        generalResult ∈ PFunConverter.General.attachDrive interface
            converter.embeddedDDC system.embed generalState
              (rest.map encodeQuery) →
        ∃ fuel strictResult,
          strictResult ∈ PFunConverter.driveOuter
            (framedProtocol interface boundary converter sourceMatches)
            system.flatten fuel outside inner answers rest ∧
          generalResult.1 = strictResult.1.map encodeAnswer ∧
          Cursor interface boundary converter sourceMatches system
            generalResult.2 (outside ++ rest) strictResult.2.1
              strictResult.2.2 := by
  intro generalState outside inner answers cursor rest
  induction rest generalizing generalState outside inner answers with
  | nil =>
      intro generalResult generalMember
      simp only [List.map_nil, PFunConverter.General.attachDrive,
        Part.mem_some_iff] at generalMember
      subst generalResult
      refine ⟨0, ([], inner, answers), ?_, rfl, ?_⟩
      · simp [PFunConverter.driveOuter]
      · simpa using cursor
  | cons query tail induction =>
      intro generalResult generalMember
      simp only [List.map_cons, PFunConverter.General.attachDrive,
        Part.mem_bind_iff, Part.mem_map_iff] at generalMember
      obtain ⟨entryResult, entryMember, tailResult, tailMember, rfl⟩ :=
        generalMember
      obtain ⟨entryFuel, strictEntry, strictEntryMember,
          entryOutputEquation, nextCursor⟩ :=
        entry_general_to_strict interface boundary converter sourceMatches
          system cursor query entryMember
      obtain ⟨tailFuel, strictTail, strictTailMember, tailOutputEquation,
          finalCursor⟩ :=
        induction nextCursor tailMember
      have strictEntryAtMax := PFunConverter.drive_mono_le
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten (Nat.le_max_left entryFuel tailFuel) strictEntryMember
      have strictTailAtMax := PFunConverter.driveOuter_mono_le
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten (Nat.le_max_right entryFuel tailFuel) strictTailMember
      refine ⟨max entryFuel tailFuel,
        (strictEntry.1 :: strictTail.1, strictTail.2), ?_, ?_, ?_⟩
      · simp only [PFunConverter.driveOuter, Part.mem_bind_iff,
          Part.mem_map_iff]
        exact ⟨strictEntry, strictEntryAtMax, strictTail, strictTailAtMax,
          rfl⟩
      · simp [entryOutputEquation, tailOutputEquation]
      · simpa [List.append_assoc] using finalCursor

/-- One strict framed round is reflected by the ambient general attachment.
The additional tag equation records that the framed answer belongs to the
active outside interface; it is needed because `encodeAnswer` deliberately
forgets that interface. -/
theorem entry_strict_to_general
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    {generalState :
      List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
        List (AmbientQuery I U)}
    {outside : List
      (Query U (TargetBoundary interface boundary (target := target)))}
    {inner : List (Query U boundary)}
    {answers : List (Option (FlatAnswer U boundary))}
    (cursor : Cursor interface boundary converter sourceMatches system
      generalState outside inner answers)
    (query : Query U
      (TargetBoundary interface boundary (target := target)))
    {fuel : Nat}
    {strictResult :
      FlatAnswer U
          (TargetBoundary interface boundary (target := target)) ×
        List (Query U boundary) ×
          List (Option (FlatAnswer U boundary))}
    (strictMember : strictResult ∈ PFunConverter.drive
      (framedProtocol interface boundary converter sourceMatches)
      system.flatten fuel (outside ++ [query]) inner answers) :
    ∃ generalResult,
      generalResult ∈
        PFunConverter.General.attachEntryStep interface converter.embeddedDDC
          system.embed generalState (encodeQuery query) ∧
      generalResult.1 = encodeAnswer strictResult.1 ∧
      strictResult.1.1 = query.1 ∧
      Cursor interface boundary converter sourceMatches system
        generalResult.2 (outside ++ [query]) strictResult.2.1
          strictResult.2.2 := by
  have baseLive := native_base_live interface boundary converter sourceMatches
    system cursor
  have baseEquation := encoded_inner interface boundary converter sourceMatches
    system cursor
  by_cases same : query.1 = interface
  · have encodedSame : (encodeQuery query).1 = interface := by
      simpa [encodeQuery] using same
    obtain ⟨localInputs, localAnswers, ready, openedMember⟩ :=
      open_selected interface boundary converter sourceMatches system cursor
        query same
    obtain ⟨localResult, generalResult, localDriveMember, generalResolveMember,
        strictRelated, entryRelated⟩ :=
      SelectedEntry.strict_to_general interface boundary converter
        sourceMatches system inner baseLive generalState.1 localInputs
        localAnswers ready (localInput interface boundary query same)
        (outside ++ [query]) answers openedMember strictMember
    rcases strictRelated with
      ⟨strictOutputEquation, strictInnerEquation, extension,
        localAnswersEquation, globalAnswersEquation, finalReplay⟩
    rcases entryRelated with
      ⟨generalOutputEquation, finalReady, generalBaseEquation⟩
    have generalEntryMember : generalResult ∈
        PFunConverter.General.attachEntryStep interface converter.embeddedDDC
          system.embed generalState (encodeQuery query) := by
      rw [PFunConverter.General.attachEntryStep, if_pos encodedSame,
        baseEquation,
        FramingEncoding.selected_payload interface boundary query same]
      exact generalResolveMember
    have openedReach : Reach converter.protocol
        (localInputs ++ [localInput interface boundary query same],
          localAnswers) := by
      exact replay_coherent interface boundary converter sourceMatches
        (outside ++ [query], answers) openedMember
    have finalLocalLive := DriveFacts.result_inner_live converter.protocol
      (TypedContinuation.continuation interface boundary sourceMatches
        system inner)
      converter.isDDC.1 openedReach (Or.inr rfl) localDriveMember
    have finalBaseLive :
        strictResult.2.1 ∈ PFunDDS.dom system.flatten ∨
          strictResult.2.1 = [] := by
      rw [strictInnerEquation]
      rcases finalLocalLive with live | empty
      · exact Or.inl live.2
      · rw [empty, TypedContinuation.query_path_nil, List.append_nil]
        exact baseLive
    have finalAmbientBaseLive :
        generalResult.2.2 ∈ PFunDDS.dom system.embed ∨
          generalResult.2.2 = [] := by
      rw [generalBaseEquation]
      exact GeneralBridge.encoded_base_live (U := U) (boundary := boundary)
        (system := system) (base := strictResult.2.1)
        (baseLive := finalBaseLive)
    let finalState : FrameState interface boundary
        (source := source) (target := target) :=
      { localInputs :=
          localInputs ++ [localInput interface boundary query same]
        localAnswers := localResult.2.2
        phase := .local }
    have localOutputMember := DriveFacts.result_output_mem converter.protocol
      (TypedContinuation.continuation interface boundary sourceMatches
        system inner)
      localDriveMember
    have finalMove : Sum.inr
        (globalAnswer interface boundary localResult.1) ∈
        stateMove interface boundary converter sourceMatches finalState := by
      simp only [finalState, stateMove, Part.mem_map_iff]
      exact ⟨Sum.inr localResult.1, localOutputMember, by simp⟩
    refine ⟨generalResult, generalEntryMember, ?_, ?_, Or.inr ?_⟩
    · calc
        generalResult.1 =
            (⟨target, localResult.1⟩ : AmbientOutput U) :=
          generalOutputEquation
        _ = encodeAnswer strictResult.1 := by
          rw [strictOutputEquation,
            FramingEncoding.encode_global_answer]
    · rw [strictOutputEquation]
      exact same.symm
    · exact ⟨finalState, finalReady, generalBaseEquation,
        finalAmbientBaseLive, finalReplay,
        globalAnswer interface boundary localResult.1, finalMove⟩
  · have encodedDifferent : (encodeQuery query).1 ≠ interface := by
      simpa [encodeQuery] using same
    obtain ⟨localInputs, localAnswers, ready, openedMember⟩ :=
      open_pass interface boundary converter sourceMatches system cursor query
        same
    obtain ⟨answer, answerMember, passRelated⟩ :=
      PassRound.drive_forward interface boundary converter sourceMatches
        system inner baseLive (outside ++ [query]) answers localInputs
        localAnswers query same openedMember strictMember
    rcases passRelated with
      ⟨sameTag, strictResultEquation, finalReplay⟩
    have finalGeneralBaseEquation :
        generalState.2 ++ [encodeQuery query] =
          strictResult.2.1.map encodeQuery := by
      rw [baseEquation, strictResultEquation, List.map_append,
        List.map_singleton,
        FramingEncoding.encode_pass_query interface boundary query same]
    have ambientMember : encodeAnswer answer ∈ system.embed.1
        (generalState.2 ++ [encodeQuery query]) := by
      rw [finalGeneralBaseEquation, system.embed_apply_encoded]
      rw [strictResultEquation]
      exact Part.mem_map _ answerMember
    let returned := passAnswer interface boundary (target := target) answer
      (sameTag.trans_ne same)
    let generalResult : AmbientOutput U ×
        (List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
          List (AmbientQuery I U)) :=
      (encodeAnswer answer,
        generalState.1, generalState.2 ++ [encodeQuery query])
    have generalEntryMember : generalResult ∈
        PFunConverter.General.attachEntryStep interface converter.embeddedDDC
          system.embed generalState (encodeQuery query) := by
      rw [PFunConverter.General.attachEntryStep, if_neg encodedDifferent]
      exact Part.mem_map _ ambientMember
    have finalBaseLive :
        strictResult.2.1 ∈ PFunDDS.dom system.flatten ∨
          strictResult.2.1 = [] := by
      rw [strictResultEquation]
      exact Or.inl (Part.dom_iff_mem.mpr ⟨answer, answerMember⟩)
    have finalAmbientBaseLive :
        generalState.2 ++ [encodeQuery query] ∈
            PFunDDS.dom system.embed ∨
          generalState.2 ++ [encodeQuery query] = [] := by
      exact Or.inl (Part.dom_iff_mem.mpr ⟨encodeAnswer answer, ambientMember⟩)
    let finalState : FrameState interface boundary
        (source := source) (target := target) :=
      { localInputs := localInputs
        localAnswers := localAnswers
        phase := .passReturned returned }
    have finalMove : Sum.inr returned ∈
        stateMove interface boundary converter sourceMatches finalState := by
      simp [finalState, stateMove, returned]
    have strictOutputEquation : strictResult.1 = returned := by
      rw [strictResultEquation]
    have encodedStrictOutput : encodeAnswer strictResult.1 =
        encodeAnswer answer := by
      rw [strictOutputEquation]
      exact FramingEncoding.encode_pass_answer interface boundary answer
        (sameTag.trans_ne same)
    refine ⟨generalResult, generalEntryMember, ?_, ?_, Or.inr ?_⟩
    · exact encodedStrictOutput.symm
    · rw [strictResultEquation]
      exact sameTag
    · refine ⟨finalState, ready, ?_, finalAmbientBaseLive, ?_, returned,
        finalMove⟩
      · exact finalGeneralBaseEquation
      · simpa [finalState, returned] using finalReplay

/-- The strict outer fold is reflected by the ambient attachment fold.  In
addition to the encoded answers, the theorem retains the interface tag of
each strict answer, so no injectivity of the ambient output encoding is
assumed. -/
theorem drive_strict_to_general
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    ∀
      {generalState :
        List (DDC.CIn (AmbientInput U) (AmbientOutput U)) ×
          List (AmbientQuery I U)}
      {outside : List
        (Query U (TargetBoundary interface boundary (target := target)))}
      {inner : List (Query U boundary)}
      {answers : List (Option (FlatAnswer U boundary))},
      Cursor interface boundary converter sourceMatches system
          generalState outside inner answers →
      ∀ (rest : List
        (Query U (TargetBoundary interface boundary (target := target))))
        {fuel : Nat}
        {strictResult :
          List (FlatAnswer U
              (TargetBoundary interface boundary (target := target))) ×
            List (Query U boundary) ×
              List (Option (FlatAnswer U boundary))},
        strictResult ∈ PFunConverter.driveOuter
            (framedProtocol interface boundary converter sourceMatches)
            system.flatten fuel outside inner answers rest →
        ∃ generalResult,
          generalResult ∈ PFunConverter.General.attachDrive interface
              converter.embeddedDDC system.embed generalState
                (rest.map encodeQuery) ∧
          generalResult.1 = strictResult.1.map encodeAnswer ∧
          strictResult.1.map (fun answer => answer.1) =
            rest.map (fun query => query.1) ∧
          Cursor interface boundary converter sourceMatches system
            generalResult.2 (outside ++ rest) strictResult.2.1
              strictResult.2.2 := by
  intro generalState outside inner answers cursor rest
  induction rest generalizing generalState outside inner answers with
  | nil =>
      intro fuel strictResult strictMember
      simp only [PFunConverter.driveOuter, Part.mem_some_iff] at strictMember
      subst strictResult
      refine ⟨([], generalState), ?_, rfl, rfl, ?_⟩
      · simp [PFunConverter.General.attachDrive]
      · simpa using cursor
  | cons query tail induction =>
      intro fuel strictResult strictMember
      simp only [PFunConverter.driveOuter, Part.mem_bind_iff,
        Part.mem_map_iff] at strictMember
      obtain ⟨strictEntry, strictEntryMember, strictTail, strictTailMember,
          rfl⟩ := strictMember
      obtain ⟨generalEntry, generalEntryMember, entryOutputEquation,
          entryTagEquation, nextCursor⟩ :=
        entry_strict_to_general interface boundary converter sourceMatches
          system cursor query strictEntryMember
      obtain ⟨generalTail, generalTailMember, tailOutputEquation,
          tailTagEquation, finalCursor⟩ :=
        induction nextCursor strictTailMember
      refine ⟨(generalEntry.1 :: generalTail.1, generalTail.2), ?_, ?_, ?_,
        ?_⟩
      · simp only [List.map_cons, PFunConverter.General.attachDrive,
          Part.mem_bind_iff, Part.mem_map_iff]
        exact ⟨generalEntry, generalEntryMember, generalTail,
          generalTailMember, rfl⟩
      · simp [entryOutputEquation, tailOutputEquation]
      · simp [entryTagEquation, tailTagEquation]
      · simpa [List.append_assoc] using finalCursor

/-- On encoded target-boundary histories, the ambient attachment raw function
is exactly the ambient encoding of strict framed application. -/
theorem attach_raw_encoded_eq_map_apply_raw
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary)
    (history : List
      (Query U (TargetBoundary interface boundary (target := target)))) :
    PFunConverter.General.attachRaw interface converter.embeddedDDC
        system.embed (history.map encodeQuery) =
      (PFunConverter.applyRaw
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten history).map encodeAnswer := by
  apply Part.ext
  intro ambientAnswer
  constructor
  · intro ambientMember
    simp only [PFunConverter.General.attachRaw, Part.mem_bind_iff] at ambientMember
    obtain ⟨generalResult, generalDriveMember, generalOutputMember⟩ :=
      ambientMember
    have initialCursor : Cursor interface boundary converter sourceMatches
        system ([], []) [] [] [] :=
      Or.inl ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨fuel, strictResult, strictDriveMember, outputEquation,
        _finalCursor⟩ :=
      drive_general_to_strict interface boundary converter sourceMatches
        system initialCursor history generalDriveMember
    rw [outputEquation, List.getLast?_map] at generalOutputMember
    cases lastEquation : strictResult.1.getLast? with
    | none =>
        simp [lastEquation] at generalOutputMember
    | some answer =>
        have strictRawMember : answer ∈ PFunConverter.applyRaw
            (framedProtocol interface boundary converter sourceMatches)
            system.flatten history := by
          rw [PFunConverter.mem_applyRaw]
          refine ⟨fuel, ?_⟩
          rw [PFunConverter.mem_applyRawAt_iff]
          exact ⟨strictResult, strictDriveMember, lastEquation⟩
        refine (Part.mem_map_iff _).mpr
          ⟨answer, strictRawMember, ?_⟩
        have equation : ambientAnswer = encodeAnswer answer := by
          simpa [lastEquation] using generalOutputMember
        exact equation.symm
  · intro encodedMember
    obtain ⟨answer, strictRawMember, encodedEquation⟩ :=
      (Part.mem_map_iff _).mp encodedMember
    rw [PFunConverter.mem_applyRaw] at strictRawMember
    obtain ⟨fuel, strictRawAtMember⟩ := strictRawMember
    rw [PFunConverter.mem_applyRawAt_iff] at strictRawAtMember
    obtain ⟨strictResult, strictDriveMember, lastEquation⟩ :=
      strictRawAtMember
    have initialCursor : Cursor interface boundary converter sourceMatches
        system ([], []) [] [] [] :=
      Or.inl ⟨rfl, rfl, rfl, rfl⟩
    obtain ⟨generalResult, generalDriveMember, outputEquation,
        _tagEquation, _finalCursor⟩ :=
      drive_strict_to_general interface boundary converter sourceMatches
        system initialCursor history strictDriveMember
    simp only [PFunConverter.General.attachRaw, Part.mem_bind_iff]
    refine ⟨generalResult, generalDriveMember, ?_⟩
    rw [outputEquation, List.getLast?_map, lastEquation]
    simpa using encodedEquation.symm

/-- Strict framed application is tag-faithful: every proper answer is tagged
by the interface of the active outside query. -/
theorem framed_apply_tag_faithful
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    DependentDDS.TagFaithful
      (PFunConverter.apply
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten) := by
  intro history domainMember
  let answer := PFunDDS.output
    (PFunConverter.apply
      (framedProtocol interface boundary converter sourceMatches)
      system.flatten) history domainMember
  have answerMember : answer ∈ PFunConverter.applyRaw
      (framedProtocol interface boundary converter sourceMatches)
      system.flatten history := by
    exact Part.get_mem domainMember
  rw [PFunConverter.mem_applyRaw] at answerMember
  obtain ⟨fuel, rawAtMember⟩ := answerMember
  rw [PFunConverter.mem_applyRawAt_iff] at rawAtMember
  obtain ⟨strictResult, strictDriveMember, lastEquation⟩ := rawAtMember
  have initialCursor : Cursor interface boundary converter sourceMatches
      system ([], []) [] [] [] :=
    Or.inl ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨_generalResult, _generalDriveMember, _outputEquation,
      tagEquation, _finalCursor⟩ :=
    drive_strict_to_general interface boundary converter sourceMatches
      system initialCursor history strictDriveMember
  have historyNonempty : history ≠ [] := by
    intro empty
    subst history
    exact PFunDDS.empty_not_mem
      (PFunConverter.apply
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten) domainMember
  have lastTags := congrArg List.getLast? tagEquation
  rw [List.getLast?_map, lastEquation, List.getLast?_map,
    List.getLast?_eq_some_getLast historyNonempty] at lastTags
  simpa only [Option.map_some, Option.some.injEq] using lastTags

end OuterBridge

/-! ## The one-query frame as a boundary-wide simple converter

A `DeterministicConverter.ofFunctions` converter framed at one interface is,
*after application to a tag-faithful flat system*, exactly the boundary-wide
one-query simple converter that acts as the local maps at the selected
interface and passes every other interface through.  The statement is
deliberately resource-aware: as a raw trace equivalence it is false, because
the frame blocks wrong-tag answers that an unguarded global `simpleFn`
accepts.  Tag-faithfulness of the applied system is exactly what closes the
gap. -/

namespace SimpleFrame

/-- Positional agreement between the interface tag of every proper inner
answer and the tag of its outside query.  Every tag-faithful resource
completion supplies this invariant; an unguarded global `simpleFn` does not
demand it. -/
def TagAligned :
    List (Query U (TargetBoundary interface boundary (target := target))) →
      List (Option (FlatAnswer U boundary)) → Prop
  | _, [] => True
  | [], _ :: _ => False
  | query :: queries, answer :: answers =>
      (match answer with
        | none => True
        | some proper => proper.1 = query.1) ∧
      TagAligned queries answers

omit [DecidableEq U.Code] in
theorem tag_aligned_append
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (answer : Option (FlatAnswer U boundary))
    (lengthEquation : queries.length = answers.length + 1)
    (aligned :
      TagAligned interface boundary queries (answers ++ [answer])) :
    TagAligned interface boundary queries answers ∧
      match answer with
      | none => True
      | some proper =>
          proper.1 =
            (queries.getLast (List.ne_nil_of_length_pos (by omega))).1 := by
  induction queries generalizing answers with
  | nil => simp at lengthEquation
  | cons query queries induction =>
      cases answers with
      | nil =>
          have queriesEmpty : queries = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEquation
          subst queries
          constructor
          · trivial
          · cases answer with
            | none => trivial
            | some proper =>
                simpa [TagAligned] using aligned
      | cons first rest =>
          simp only [List.length_cons] at lengthEquation
          have tailLength : queries.length = rest.length + 1 := by omega
          simp only [List.cons_append, TagAligned] at aligned ⊢
          have recursive := induction rest tailLength aligned.2
          refine ⟨⟨aligned.1, recursive.1⟩, ?_⟩
          cases answer with
          | none => trivial
          | some proper =>
              have queriesNonempty : queries ≠ [] :=
                List.ne_nil_of_length_pos (by omega)
              simpa only [List.getLast_cons queriesNonempty] using recursive.2

omit [DecidableEq U.Code] in
theorem tag_aligned_append_of
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (answer : Option (FlatAnswer U boundary))
    (lengthEquation : queries.length = answers.length + 1)
    (aligned : TagAligned interface boundary queries answers)
    (lastTag :
      match answer with
      | none => True
      | some proper =>
          proper.1 =
            (queries.getLast (List.ne_nil_of_length_pos (by omega))).1) :
    TagAligned interface boundary queries (answers ++ [answer]) := by
  induction queries generalizing answers with
  | nil => simp at lengthEquation
  | cons query queries induction =>
      cases answers with
      | nil =>
          have queriesEmpty : queries = [] := by
            apply List.eq_nil_of_length_eq_zero
            simpa using lengthEquation
          subst queries
          simpa [TagAligned] using lastTag
      | cons first rest =>
          simp only [List.length_cons] at lengthEquation
          have tailLength : queries.length = rest.length + 1 := by omega
          simp only [List.cons_append, TagAligned] at aligned ⊢
          refine ⟨aligned.1, induction rest tailLength aligned.2 ?_⟩
          cases answer with
          | none => trivial
          | some proper =>
              have queriesNonempty : queries ≠ [] :=
                List.ne_nil_of_length_pos (by omega)
              simpa only [List.getLast_cons queriesNonempty] using lastTag

omit [DecidableEq U.Code] in
theorem tag_aligned_append_query
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (query : Query U (TargetBoundary interface boundary (target := target)))
    (lengthEquation : queries.length = answers.length) :
    TagAligned interface boundary (queries ++ [query]) answers ↔
      TagAligned interface boundary queries answers := by
  induction queries generalizing answers with
  | nil =>
      have answersEmpty : answers = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using lengthEquation.symm
      subst answers
      simp [TagAligned]
  | cons first rest induction =>
      cases answers with
      | nil => simp at lengthEquation
      | cons answer answers =>
          simp only [List.length_cons] at lengthEquation
          have tailLength : rest.length = answers.length := by omega
          simp only [List.cons_append, TagAligned,
            induction answers tailLength]

section

variable {queryMap : U.input target → U.input source}
variable {answerMap : U.output source → U.output target}
variable {sourceMatches : boundary interface = source}
variable {globalQueryMap :
  Query U (TargetBoundary interface boundary (target := target)) →
    Query U boundary}
variable {globalAnswerMap :
  FlatAnswer U boundary →
    FlatAnswer U (TargetBoundary interface boundary (target := target))}

omit [DecidableEq U.Code] in
theorem global_query_map_fst
    (queryLocal : ∀ query (same : query.1 = interface),
      globalQueryMap query =
        globalQuery interface boundary sourceMatches
          (queryMap (localInput interface boundary query same)))
    (queryPass : ∀ query (different : ¬query.1 = interface),
      globalQueryMap query = passQuery interface boundary query different)
    (query : Query U (TargetBoundary interface boundary (target := target))) :
    (globalQueryMap query).1 = query.1 := by
  by_cases same : query.1 = interface
  · rw [queryLocal query same]
    exact same.symm
  · rw [queryPass query same]
    rfl

omit [DecidableEq U.Code] in
theorem global_answer_map_fst
    (answerLocal : ∀ answer (same : answer.1 = interface),
      globalAnswerMap answer =
        globalAnswer interface boundary
          (answerMap (localAnswer interface boundary sourceMatches
            answer same)))
    (answerPass : ∀ answer (different : ¬answer.1 = interface),
      globalAnswerMap answer = passAnswer interface boundary answer different)
    (answer : FlatAnswer U boundary) :
    (globalAnswerMap answer).1 = answer.1 := by
  by_cases same : answer.1 = interface
  · rw [answerLocal answer same]
    exact same.symm
  · rw [answerPass answer same]
    rfl

omit [DecidableEq U.Code] in
/-- Pointwise agreement of the boundary-wide simple converter with the
canonical frame of its local one-query converter, on the simple converter's
trace tree restricted to tag-aligned answer histories. -/
theorem simple_eq_framed_of_reach
    (queryLocal : ∀ query (same : query.1 = interface),
      globalQueryMap query =
        globalQuery interface boundary sourceMatches
          (queryMap (localInput interface boundary query same)))
    (queryPass : ∀ query (different : ¬query.1 = interface),
      globalQueryMap query = passQuery interface boundary query different)
    (answerLocal : ∀ answer (same : answer.1 = interface),
      globalAnswerMap answer =
        globalAnswer interface boundary
          (answerMap (localAnswer interface boundary sourceMatches
            answer same)))
    (answerPass : ∀ answer (different : ¬answer.1 = interface),
      globalAnswerMap answer = passAnswer interface boundary answer different) :
    ∀ pair,
      Reach (simpleFn globalQueryMap globalAnswerMap) pair →
        TagAligned interface boundary pair.1 pair.2 →
        simpleFn globalQueryMap globalAnswerMap pair =
          framedProtocol interface boundary
            (DeterministicConverter.ofFunctions queryMap answerMap)
            sourceMatches pair := by
  intro pair reachable
  induction reachable with
  | first input =>
      intro _
      unfold framedProtocol
      have replayEquation :
          replay interface boundary
              (DeterministicConverter.ofFunctions queryMap answerMap)
              sourceMatches ([input], []) =
            Part.some (firstState interface boundary input) := by
        simp only [replay]
        rw [replayCore.eq_def]
      rw [replayEquation, Part.bind_some]
      have simpleEquation :
          simpleFn globalQueryMap globalAnswerMap ([input], []) =
            Part.some (Sum.inl (globalQueryMap input)) := by
        apply Part.eq_some_iff.mpr
        simpa using
          simpleFn_inl_mem globalQueryMap globalAnswerMap
            (us := [input]) (ys := []) (by simp)
      rw [simpleEquation]
      by_cases same : input.1 = interface
      · have stateEquation :
            (firstState interface boundary input :
              FrameState interface boundary (source := source)
                (target := target)) =
              { localInputs := [localInput interface boundary input same]
                localAnswers := []
                phase := .local } := by
          simp [firstState, openRound, same]
        rw [stateEquation]
        show Part.some (Sum.inl (globalQueryMap input)) =
          (simpleFn queryMap answerMap
              ([localInput interface boundary input same], [])).map
            (Sum.map (globalQuery interface boundary sourceMatches)
              (globalAnswer interface boundary))
        have localEquation :
            simpleFn queryMap answerMap
                ([localInput interface boundary input same], []) =
              Part.some (Sum.inl (queryMap
                (localInput interface boundary input same))) := by
          apply Part.eq_some_iff.mpr
          simpa using
            simpleFn_inl_mem queryMap answerMap
              (us := [localInput interface boundary input same]) (ys := [])
              (by simp)
        rw [localEquation, Part.map_some, Sum.map_inl,
          queryLocal input same]
      · have stateEquation :
            (firstState interface boundary input :
              FrameState interface boundary (source := source)
                (target := target)) =
              { localInputs := []
                localAnswers := []
                phase := .passPending input same } := by
          simp [firstState, openRound, same]
        rw [stateEquation]
        show Part.some (Sum.inl (globalQueryMap input)) =
          Part.some (Sum.inl (passQuery interface boundary input same))
        rw [queryPass input same]
  | answer reachable query answer induction =>
      rename_i queries answers innerQuery
      intro aligned
      have lengthEquation := simpleFn_inl_inv query
      have split := tag_aligned_append interface boundary _ _ _
        lengthEquation aligned
      have previousEquation := induction split.1
      have framedQuery :
          Sum.inl innerQuery ∈
            framedProtocol interface boundary
              (DeterministicConverter.ofFunctions queryMap answerMap)
              sourceMatches (queries, answers) := by
        have framedQuery := query
        rw [previousEquation] at framedQuery
        exact framedQuery
      obtain ⟨state, replayMember, moveMember⟩ :=
        (mem_framed_protocol_iff interface boundary
          (DeterministicConverter.ofFunctions queryMap answerMap)
          sourceMatches (queries, answers) _).mp framedQuery
      have canonicalMember :=
        simpleFn_inl_mem globalQueryMap globalAnswerMap
          (us := queries) (ys := answers) lengthEquation
      have innerQueryEquation :
          innerQuery =
            globalQueryMap
              (queries.getLast
                (List.ne_nil_of_length_pos (by omega))) :=
        Sum.inl.inj (Part.mem_unique query canonicalMember)
      rcases state with ⟨localInputs, localAnswers, phase⟩
      cases phase with
      | «local» =>
          simp only [stateMove, Part.mem_map_iff] at moveMember
          obtain ⟨localMove, localMember, moveEquation⟩ := moveMember
          cases localMove with
          | inl localQuery =>
              cases answer with
              | none =>
                  have replayNone :=
                    OuterReplay.replay_append_selected_none
                      interface boundary
                      (DeterministicConverter.ofFunctions queryMap answerMap)
                      sourceMatches queries answers
                      localInputs localAnswers replayMember localMember
                  unfold framedProtocol
                  rw [replayNone]
                  simp [simpleFn, lengthEquation]
              | some proper =>
                  simp only [Sum.map_inl, Sum.inl.injEq] at moveEquation
                  have properTag : proper.1 = interface := by
                    calc
                      proper.1 =
                          (queries.getLast
                            (List.ne_nil_of_length_pos (by omega))).1 :=
                        split.2
                      _ = (globalQueryMap
                            (queries.getLast
                              (List.ne_nil_of_length_pos (by omega)))).1 :=
                        (global_query_map_fst interface boundary queryLocal queryPass _).symm
                      _ = innerQuery.1 :=
                        congrArg Sigma.fst innerQueryEquation.symm
                      _ = interface := by
                        rw [← moveEquation]
                        rfl
                  let localProper :=
                    localAnswer interface boundary sourceMatches proper
                      properTag
                  have localLength := simpleFn_inl_inv localMember
                  have properEquation :
                      globalInnerAnswer interface boundary sourceMatches
                          localProper =
                        proper :=
                    global_inner_answer_local_answer interface boundary
                      sourceMatches proper properTag
                  have replaySomeRaw :=
                    OuterReplay.replay_append_selected_some
                      interface boundary
                      (DeterministicConverter.ofFunctions queryMap answerMap)
                      sourceMatches queries answers
                      localInputs localAnswers replayMember localMember
                      localProper
                  have replaySome :
                      replay interface boundary
                          (DeterministicConverter.ofFunctions queryMap
                            answerMap) sourceMatches
                          (queries, answers ++ [some proper]) =
                        Part.some
                          ({ localInputs := localInputs
                             localAnswers :=
                               localAnswers ++ [some localProper]
                             phase := Phase.local } :
                            FrameState interface boundary
                              (source := source) (target := target)) := by
                    rw [← properEquation]
                    exact replaySomeRaw
                  have newMember :
                      ({ localInputs := localInputs
                         localAnswers := localAnswers ++ [some localProper]
                         phase := Phase.local } :
                        FrameState interface boundary
                          (source := source) (target := target)) ∈
                        replay interface boundary
                          (DeterministicConverter.ofFunctions queryMap
                            answerMap) sourceMatches
                          (queries, answers ++ [some proper]) := by
                    rw [replaySome]
                    exact Part.mem_some _
                  have globalOut :
                      simpleFn globalQueryMap globalAnswerMap
                          (queries, answers ++ [some proper]) =
                        Part.some (Sum.inr (globalAnswerMap proper)) := by
                    apply Part.eq_some_iff.mpr
                    apply simpleFn_inr_mem
                    · simp [lengthEquation]
                    · simp
                    · simp
                  have localOut :
                      (DeterministicConverter.ofFunctions queryMap
                          answerMap).protocol
                          (localInputs, localAnswers ++ [some localProper]) =
                        Part.some (Sum.inr (answerMap localProper)) := by
                    apply Part.eq_some_iff.mpr
                    change
                      Sum.inr (answerMap localProper) ∈
                        simpleFn queryMap answerMap
                          (localInputs, localAnswers ++ [some localProper])
                    exact simpleFn_inr_mem queryMap answerMap
                      (h := by simpa using localLength) (h0 := by simp)
                      (y := localProper) (hy := by simp)
                  rw [globalOut]
                  rw [SelectedRound.framed_protocol_eq_local_of_replay
                    interface boundary
                    (DeterministicConverter.ofFunctions queryMap answerMap)
                    sourceMatches queries (answers ++ [some proper])
                    localInputs (localAnswers ++ [some localProper])
                    newMember]
                  rw [localOut, Part.map_some, Sum.map_inr]
                  rw [answerLocal proper properTag]
          | inr localAnswerValue =>
              simp at moveEquation
      | passPending pending different =>
          have moveEquation :
              innerQuery = passQuery interface boundary pending different := by
            simpa [stateMove] using moveMember
          cases answer with
          | none =>
              have replayNone :=
                OuterReplay.replay_append_pass_none interface boundary
                  (DeterministicConverter.ofFunctions queryMap answerMap)
                  sourceMatches queries answers localInputs localAnswers
                  pending different replayMember
              unfold framedProtocol
              rw [replayNone]
              simp [simpleFn, lengthEquation]
          | some proper =>
              have sameTag : proper.1 = pending.1 := by
                calc
                  proper.1 =
                      (queries.getLast
                        (List.ne_nil_of_length_pos (by omega))).1 :=
                    split.2
                  _ = (globalQueryMap
                        (queries.getLast
                          (List.ne_nil_of_length_pos (by omega)))).1 :=
                    (global_query_map_fst interface boundary queryLocal queryPass _).symm
                  _ = innerQuery.1 :=
                    congrArg Sigma.fst innerQueryEquation.symm
                  _ = pending.1 := by
                    rw [moveEquation]
                    rfl
              have replaySome :=
                OuterReplay.replay_append_pass_some interface boundary
                  (DeterministicConverter.ofFunctions queryMap answerMap)
                  sourceMatches queries answers localInputs localAnswers
                  pending different replayMember proper sameTag
              have returnedMember :
                  ({ localInputs := localInputs
                     localAnswers := localAnswers
                     phase := Phase.passReturned
                       (passAnswer interface boundary proper
                         (sameTag.trans_ne different)) } :
                    FrameState interface boundary
                      (source := source) (target := target)) ∈
                    replay interface boundary
                      (DeterministicConverter.ofFunctions queryMap answerMap)
                      sourceMatches (queries, answers ++ [some proper]) := by
                rw [replaySome]
                exact Part.mem_some _
              have globalOut :
                  simpleFn globalQueryMap globalAnswerMap
                      (queries, answers ++ [some proper]) =
                    Part.some (Sum.inr (globalAnswerMap proper)) := by
                apply Part.eq_some_iff.mpr
                apply simpleFn_inr_mem
                · simp [lengthEquation]
                · simp
                · simp
              rw [globalOut]
              rw [PassRound.framed_protocol_eq_returned interface boundary
                (DeterministicConverter.ofFunctions queryMap answerMap)
                sourceMatches queries (answers ++ [some proper])
                localInputs localAnswers
                (passAnswer interface boundary proper
                  (sameTag.trans_ne different))
                returnedMember]
              rw [answerPass proper (sameTag.trans_ne different)]
      | passReturned returned =>
          simp [stateMove] at moveMember
  | next reachable output input induction =>
      rename_i queries answers outerAnswer
      intro aligned
      obtain ⟨lengthEquation, answersPositive, lastAnswer,
          lastAnswerEquation, outerAnswerEquation⟩ :=
        simpleFn_inr_inv output
      have previousTags : TagAligned interface boundary queries answers :=
        (tag_aligned_append_query interface boundary queries answers input
          lengthEquation).mp aligned
      have previousEquation := induction previousTags
      have framedOutput :
          Sum.inr outerAnswer ∈
            framedProtocol interface boundary
              (DeterministicConverter.ofFunctions queryMap answerMap)
              sourceMatches (queries, answers) := by
        have framedOutput := output
        rw [previousEquation] at framedOutput
        exact framedOutput
      obtain ⟨state, replayMember, moveMember⟩ :=
        (mem_framed_protocol_iff interface boundary
          (DeterministicConverter.ofFunctions queryMap answerMap)
          sourceMatches (queries, answers) _).mp framedOutput
      have stateCoherent :=
        replay_coherent interface boundary
          (DeterministicConverter.ofFunctions queryMap answerMap)
          sourceMatches (queries, answers) replayMember
      have replayNext :=
        OuterReplay.replay_append_outside_of_mem interface boundary
          (DeterministicConverter.ofFunctions queryMap answerMap)
          sourceMatches (queries, answers) replayMember moveMember input
      have simpleNext :
          simpleFn globalQueryMap globalAnswerMap
              (queries ++ [input], answers) =
            Part.some (Sum.inl (globalQueryMap input)) := by
        apply Part.eq_some_iff.mpr
        simpa only [List.getLast_append_singleton] using
          simpleFn_inl_mem globalQueryMap globalAnswerMap
            (us := queries ++ [input]) (ys := answers)
            (by simp [lengthEquation])
      rcases state with ⟨localInputs, localAnswers, phase⟩
      have replayNext' :
          replay interface boundary
              (DeterministicConverter.ofFunctions queryMap answerMap)
              sourceMatches (queries ++ [input], answers) =
            Part.some
              (openRound interface boundary
                { localInputs := localInputs
                  localAnswers := localAnswers
                  phase := phase }
                input) := by
        simpa only using replayNext
      have localBalanced : localInputs.length = localAnswers.length := by
        cases phase with
        | «local» =>
            simp only [stateMove, Part.mem_map_iff] at moveMember
            obtain ⟨localMove, localMember, moveEquation⟩ := moveMember
            cases localMove with
            | inl localQuery =>
                simp at moveEquation
            | inr localAnswerValue =>
                exact (simpleFn_inr_inv localMember).1
        | passPending pending different =>
            simp [stateMove] at moveMember
        | passReturned returned =>
            change
              LocalIdle
                (DeterministicConverter.ofFunctions queryMap answerMap)
                localInputs localAnswers at stateCoherent
            rcases stateCoherent with empty | completed
            · rcases empty with ⟨rfl, rfl⟩
              rfl
            · obtain ⟨localAnswerValue, _, localMember⟩ := completed
              exact (simpleFn_inr_inv localMember).1
      rw [simpleNext]
      unfold framedProtocol
      rw [replayNext', Part.bind_some]
      by_cases same : input.1 = interface
      · have openEquation :
            openRound interface boundary
                ({ localInputs := localInputs
                   localAnswers := localAnswers
                   phase := phase } :
                  FrameState interface boundary
                    (source := source) (target := target))
                input =
              { localInputs :=
                  localInputs ++ [localInput interface boundary input same]
                localAnswers := localAnswers
                phase := .local } := by
          simp [openRound, same]
        rw [openEquation]
        show Part.some (Sum.inl (globalQueryMap input)) =
          (simpleFn queryMap answerMap
              (localInputs ++ [localInput interface boundary input same],
                localAnswers)).map
            (Sum.map (globalQuery interface boundary sourceMatches)
              (globalAnswer interface boundary))
        have localEquation :
            simpleFn queryMap answerMap
                (localInputs ++ [localInput interface boundary input same],
                  localAnswers) =
              Part.some (Sum.inl (queryMap
                (localInput interface boundary input same))) := by
          apply Part.eq_some_iff.mpr
          simpa only [List.getLast_append_singleton] using
            simpleFn_inl_mem queryMap answerMap
              (us := localInputs ++
                [localInput interface boundary input same])
              (ys := localAnswers)
              (by simp [localBalanced])
        rw [localEquation, Part.map_some, Sum.map_inl,
          queryLocal input same]
      · have openEquation :
            openRound interface boundary
                ({ localInputs := localInputs
                   localAnswers := localAnswers
                   phase := phase } :
                  FrameState interface boundary
                    (source := source) (target := target))
                input =
              { localInputs := localInputs
                localAnswers := localAnswers
                phase := .passPending input same } := by
          simp [openRound, same]
        rw [openEquation]
        show Part.some (Sum.inl (globalQueryMap input)) =
          Part.some (Sum.inl (passQuery interface boundary input same))
        rw [queryPass input same]

omit [DecidableEq U.Code] in
/-- The tag-alignment invariant survives one Def 3.3 resource completion of
a tag-faithful system. -/
theorem tag_aligned_append_completion
    (queryLocal : ∀ query (same : query.1 = interface),
      globalQueryMap query =
        globalQuery interface boundary sourceMatches
          (queryMap (localInput interface boundary query same)))
    (queryPass : ∀ query (different : ¬query.1 = interface),
      globalQueryMap query = passQuery interface boundary query different)
    (system : PFunDDS.DDS (Query U boundary) (FlatAnswer U boundary))
    (faithful : DependentDDS.TagFaithful system)
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (innerQueries : List (Query U boundary))
    (innerQuery : Query U boundary)
    (aligned : TagAligned interface boundary queries answers)
    (queryMember :
      Sum.inl innerQuery ∈
        simpleFn globalQueryMap globalAnswerMap (queries, answers)) :
    TagAligned interface boundary queries
      (answers ++ [
        PFunDDS.output (PFunDDS.fullyDefined system)
          (innerQueries ++ [innerQuery])
          (by rw [PFunDDS.dom_fullyDefined]; simp)]) := by
  have lengthEquation := simpleFn_inl_inv queryMember
  apply tag_aligned_append_of interface boundary queries answers _
    lengthEquation aligned
  have canonicalMember :=
    simpleFn_inl_mem globalQueryMap globalAnswerMap
      (us := queries) (ys := answers) lengthEquation
  have innerQueryEquation :
      innerQuery =
        globalQueryMap
          (queries.getLast (List.ne_nil_of_length_pos (by omega))) :=
    Sum.inl.inj (Part.mem_unique queryMember canonicalMember)
  generalize completionEquation :
    PFunDDS.output (PFunDDS.fullyDefined system)
      (innerQueries ++ [innerQuery])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = completion
  cases completion with
  | none => trivial
  | some proper =>
      rw [PFunDDS.output_fullyDefined] at completionEquation
      have drop : (innerQueries ++ [innerQuery]).dropLast = innerQueries := by
        simp
      have last :
          (innerQueries ++ [innerQuery]).getLast (by simp) = innerQuery := by
        simp
      rw [drop, last] at completionEquation
      dsimp only at completionEquation
      split at completionEquation
      · rename_i accepted
        show proper.1 =
          (queries.getLast (List.ne_nil_of_length_pos (by omega))).1
        have tagEquation : proper.1 = innerQuery.1 := by
          simp only [Option.some.injEq] at completionEquation
          subst proper
          simpa only [List.getLast_append_singleton] using
            faithful
              (PFunDDS.keptPrefix system innerQueries ++ [innerQuery])
              accepted
        rw [tagEquation, innerQueryEquation]
        exact global_query_map_fst interface boundary queryLocal queryPass _
      · simp at completionEquation

omit [DecidableEq U.Code] in
/-- **Typed simple-attachment coherence, applied form**: on a tag-faithful
flat system, applying the boundary-wide simple converter agrees with
applying the canonical frame of the local one-query converter. -/
theorem apply_simpleFn_eq_apply_framed
    (queryLocal : ∀ query (same : query.1 = interface),
      globalQueryMap query =
        globalQuery interface boundary sourceMatches
          (queryMap (localInput interface boundary query same)))
    (queryPass : ∀ query (different : ¬query.1 = interface),
      globalQueryMap query = passQuery interface boundary query different)
    (answerLocal : ∀ answer (same : answer.1 = interface),
      globalAnswerMap answer =
        globalAnswer interface boundary
          (answerMap (localAnswer interface boundary sourceMatches
            answer same)))
    (answerPass : ∀ answer (different : ¬answer.1 = interface),
      globalAnswerMap answer = passAnswer interface boundary answer different)
    (system : PFunDDS.DDS (Query U boundary) (FlatAnswer U boundary))
    (faithful : DependentDDS.TagFaithful system) :
    PFunConverter.apply (simpleFn globalQueryMap globalAnswerMap) system =
      PFunConverter.apply
        (framedProtocol interface boundary
          (DeterministicConverter.ofFunctions queryMap answerMap)
          sourceMatches) system := by
  apply PFunConverter.apply_eq_of_reachable_invariant _ _ system
    (fun queries answers => TagAligned interface boundary queries answers)
  · rintro queries answers query
      (⟨rfl, rfl⟩ | ⟨outerAnswer, reachable, answerMember, aligned⟩)
    · exact ⟨Reach.first query, trivial⟩
    · have lengthEquation := (simpleFn_inr_inv answerMember).1
      exact ⟨Reach.next reachable answerMember query,
        (tag_aligned_append_query interface boundary queries answers query
          lengthEquation).mpr aligned⟩
  · intro queries innerQueries answers innerQuery _reachable aligned
      queryMember
    exact tag_aligned_append_completion interface boundary
      queryLocal queryPass system faithful queries answers innerQueries
      innerQuery aligned queryMember
  · intro queries answers reachable aligned
    exact simple_eq_framed_of_reach interface boundary
      queryLocal queryPass answerLocal answerPass
      (queries, answers) reachable aligned

end

end SimpleFrame

/-! ## The bounded-step frame as a boundary-wide step converter

The multi-query analogue of `SimpleFrame`: a converter whose local protocol
is an outer-memoryless `ProtocolFn.ofStep` presentation, framed at one
interface and applied to a tag-faithful flat system, is exactly the
boundary-wide `ProtocolFn.ofStep` of any total global step that restricts to
the local step on selected rounds and to one pass-through resource call
elsewhere.  As with the one-query case, the raw trace equivalence is false —
the global step accepts wrong-tag answers the frame blocks — so the
statement is after application. -/

namespace StepFrame

omit [DecidableEq I] in
theorem mapM_id_map_option_map {A B : Type*} (f : A → B) :
    ∀ (l : List (Option A)),
      (l.map (Option.map f)).mapM (m := Option) id =
        (l.mapM (m := Option) id).map (List.map f) := by
  intro l
  induction l with
  | nil => rfl
  | cons head tail induction =>
      cases head with
      | none => simp [List.mapM_cons]
      | some value =>
          simp only [List.map_cons, List.mapM_cons, induction, id_eq]
          cases List.mapM (m := Option) id tail <;> simp

omit [DecidableEq I] in
theorem exists_map_some_of_map_option_map {A B : Type*} (f : A → B) :
    ∀ {l : List (Option A)} {ys : List B},
      ys.map some = l.map (Option.map f) →
      ∃ la : List A, l = la.map some ∧ ys = la.map f := by
  intro l
  induction l with
  | nil =>
      intro ys h
      cases ys with
      | nil => exact ⟨[], rfl, rfl⟩
      | cons y ytail => simp at h
  | cons head tail induction =>
      intro ys h
      cases ys with
      | nil => simp at h
      | cons y ytail =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hhead, htail⟩ := h
          cases head with
          | none => simp at hhead
          | some a =>
              obtain ⟨la, hl, hys⟩ := induction htail
              refine ⟨a :: la, by simp [hl], ?_⟩
              simp only [Option.map_some, Option.some.injEq] at hhead
              simp [hys, hhead]

omit [DecidableEq I] in
theorem mapM_id_append_none {A : Type*} (l : List (Option A)) :
    ((l ++ [none]).mapM (m := Option) id) = none := by
  induction l with
  | nil => rfl
  | cons head tail induction =>
      cases head <;> simp [List.mapM_cons, induction]

omit [DecidableEq I] in
theorem mapM_id_singleton_none {A : Type*} :
    (([none] : List (Option A)).mapM (m := Option) id) = none := by
  rfl

omit [DecidableEq I] [DecidableEq U.Code] in
/-- The interface tag delivered by one Def 3.3 completion of a tag-faithful
system is the tag of the completing query. -/
theorem output_fully_defined_append_tag
    (system : PFunDDS.DDS (Query U boundary) (FlatAnswer U boundary))
    (faithful : DependentDDS.TagFaithful system)
    (innerQueries : List (Query U boundary))
    (innerQuery : Query U boundary)
    {proper : FlatAnswer U boundary}
    (equation :
      PFunDDS.output (PFunDDS.fullyDefined system)
        (innerQueries ++ [innerQuery])
        (by rw [PFunDDS.dom_fullyDefined]; simp) = some proper) :
    proper.1 = innerQuery.1 := by
  rw [PFunDDS.output_fullyDefined] at equation
  have drop : (innerQueries ++ [innerQuery]).dropLast = innerQueries := by
    simp
  have last :
      (innerQueries ++ [innerQuery]).getLast (by simp) = innerQuery := by
    simp
  rw [drop, last] at equation
  dsimp only at equation
  split at equation
  · rename_i accepted
    simp only [Option.some.injEq] at equation
    subst proper
    simpa only [List.getLast_append_singleton] using
      faithful (PFunDDS.keptPrefix system innerQueries ++ [innerQuery])
        accepted
  · simp at equation

section

variable {localStep :
  U.input target → List (U.output source) → U.input source ⊕ U.output target}
variable {localCount : U.input target → ℕ}
variable {globalStep :
  Query U (TargetBoundary interface boundary (target := target)) →
    List (FlatAnswer U boundary) →
      Query U boundary ⊕
        FlatAnswer U (TargetBoundary interface boundary (target := target))}
variable {globalCount :
  Query U (TargetBoundary interface boundary (target := target)) → ℕ}
variable {sourceMatches : boundary interface = source}
variable {converter : DeterministicConverter U source target}

/-- Replay-state synchronization between the boundary-wide step history and
the frame: the current-round segments correspond through the selected-round
encoding, and pass rounds sit at their exact offsets. -/
def StepSync (sourceMatches : boundary interface = source)
    (localCount : U.input target → ℕ)
    (globalCount :
      Query U (TargetBoundary interface boundary (target := target)) → ℕ)
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (state : FrameState interface boundary
      (source := source) (target := target)) : Prop :=
  ∃ nonempty : queries ≠ [],
    match state.phase with
    | .local =>
        ∃ same : (queries.getLast nonempty).1 = interface,
          ∃ inputsNonempty : state.localInputs ≠ [],
            state.localInputs.getLast inputsNonempty =
              localInput interface boundary (queries.getLast nonempty)
                same ∧
            answers.drop ((queries.dropLast.map globalCount).sum) =
              (state.localAnswers.drop
                  ((state.localInputs.dropLast.map localCount).sum)).map
                (Option.map
                  (globalInnerAnswer interface boundary sourceMatches)) ∧
            (queries.dropLast.map globalCount).sum ≤ answers.length ∧
            answers.length ≤
              (queries.dropLast.map globalCount).sum +
                globalCount (queries.getLast nonempty) ∧
            (state.localInputs.dropLast.map localCount).sum ≤
              state.localAnswers.length
    | .passPending pending _ =>
        pending = queries.getLast nonempty ∧
        answers.length = (queries.dropLast.map globalCount).sum ∧
        state.localAnswers.length = (state.localInputs.map localCount).sum
    | .passReturned answer =>
        ∃ (proper : FlatAnswer U boundary)
          (sameTag : proper.1 = (queries.getLast nonempty).1)
          (different : ¬(queries.getLast nonempty).1 = interface),
          answers.drop ((queries.dropLast.map globalCount).sum) =
            [some proper] ∧
          answers.length = (queries.dropLast.map globalCount).sum + 1 ∧
          answer =
            passAnswer interface boundary proper
              (sameTag.trans_ne different) ∧
          state.localAnswers.length = (state.localInputs.map localCount).sum

/-- The drive invariant: either the pair replays to a synchronized frame
state, or both the frame and the global step converter are silent. -/
def StepInv (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (localCount : U.input target → ℕ)
    (globalStep :
      Query U (TargetBoundary interface boundary (target := target)) →
        List (FlatAnswer U boundary) →
          Query U boundary ⊕
            FlatAnswer U (TargetBoundary interface boundary
              (target := target)))
    (globalCount :
      Query U (TargetBoundary interface boundary (target := target)) → ℕ)
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary))) : Prop :=
  (∃ state,
      state ∈ replay interface boundary converter sourceMatches
        (queries, answers) ∧
      StepSync interface boundary sourceMatches localCount globalCount
        queries answers state) ∨
  (framedProtocol interface boundary converter sourceMatches
      (queries, answers) = Part.none ∧
    ProtocolFn.ofStep globalStep globalCount (queries, answers) = Part.none)

omit [DecidableEq U.Code] in
/-- Pointwise agreement of the boundary-wide step converter with the frame,
on invariant pairs. -/
theorem step_eq_framed_of_inv
    (protocolEquation :
      converter.protocol = ProtocolFn.ofStep localStep localCount)
    (selectedStep : ∀ query (same : query.1 = interface)
        (localAnswers : List (U.output source)),
      globalStep query
          (localAnswers.map
            (globalInnerAnswer interface boundary sourceMatches)) =
        Sum.map (globalQuery interface boundary sourceMatches)
          (globalAnswer interface boundary)
          (localStep (localInput interface boundary query same)
            localAnswers))
    (passStep : ∀ query (different : ¬query.1 = interface),
      globalStep query [] =
        Sum.inl (passQuery interface boundary query different))
    (passAnswerStep : ∀ query (different : ¬query.1 = interface)
        (answer : FlatAnswer U boundary) (sameTag : answer.1 = query.1),
      globalStep query [answer] =
        Sum.inr (passAnswer interface boundary answer
          (sameTag.trans_ne different)))
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (invariant : StepInv interface boundary converter sourceMatches
      localCount globalStep globalCount queries answers) :
    ProtocolFn.ofStep globalStep globalCount (queries, answers) =
      framedProtocol interface boundary converter sourceMatches
        (queries, answers) := by
  rcases invariant with ⟨state, replayMember, sync⟩ | ⟨framedNone, stepNone⟩
  · obtain ⟨nonempty, syncPhase⟩ := sync
    rcases state with ⟨localInputs, localAnswers, phase⟩
    cases phase with
    | «local» =>
        obtain ⟨same, inputsNonempty, lastEquation, segmentEquation,
          _offsetLe, _upperBound, _localOffsetLe⟩ := syncPhase
        rw [SelectedRound.framed_protocol_eq_local_of_replay interface
          boundary converter sourceMatches queries answers localInputs
          localAnswers replayMember]
        rw [protocolEquation]
        rw [ProtocolFn.ofStep_apply globalStep globalCount nonempty answers]
        rw [ProtocolFn.ofStep_apply localStep localCount inputsNonempty
          localAnswers]
        rw [segmentEquation, mapM_id_map_option_map]
        cases localSegment :
            (localAnswers.drop
              ((localInputs.dropLast.map localCount).sum)).mapM id with
        | none => simp
        | some localValues =>
            simp only [Option.map_some, Part.map_some]
            rw [lastEquation, selectedStep _ same localValues]
    | passPending pending different =>
        obtain ⟨pendingEquation, lengthEquation, _complete⟩ := syncPhase
        subst pendingEquation
        rw [PassRound.framed_protocol_eq_pending interface boundary
          converter sourceMatches queries answers localInputs localAnswers
          _ different replayMember]
        rw [ProtocolFn.ofStep_apply globalStep globalCount nonempty answers]
        rw [show answers.drop ((queries.dropLast.map globalCount).sum) = []
          from by rw [← lengthEquation]; exact List.drop_length]
        show Part.some (globalStep (queries.getLast nonempty) []) =
          Part.some (Sum.inl (passQuery interface boundary
            (queries.getLast nonempty) different))
        rw [passStep (queries.getLast nonempty) different]
    | passReturned answer =>
        obtain ⟨proper, sameTag, different, segmentEquation,
          _lengthEquation, answerEquation, _complete⟩ := syncPhase
        rw [PassRound.framed_protocol_eq_returned interface boundary
          converter sourceMatches queries answers localInputs localAnswers
          answer replayMember]
        rw [ProtocolFn.ofStep_apply globalStep globalCount nonempty answers]
        rw [segmentEquation]
        show Part.some (globalStep (queries.getLast nonempty) [proper]) =
          Part.some (Sum.inr answer)
        rw [passAnswerStep (queries.getLast nonempty) different proper
          sameTag]
        rw [answerEquation]
  · rw [stepNone, framedNone]

omit [DecidableEq U.Code] in
/-- The invariant survives one Def 3.3 completion of a tag-faithful
system. -/
theorem step_inv_completion
    (protocolEquation :
      converter.protocol = ProtocolFn.ofStep localStep localCount)
    (globalIssues : ∀ query answers,
      (∃ inner, globalStep query answers = Sum.inl inner) ↔
        answers.length < globalCount query)
    (selectedStep : ∀ query (same : query.1 = interface)
        (localAnswers : List (U.output source)),
      globalStep query
          (localAnswers.map
            (globalInnerAnswer interface boundary sourceMatches)) =
        Sum.map (globalQuery interface boundary sourceMatches)
          (globalAnswer interface boundary)
          (localStep (localInput interface boundary query same)
            localAnswers))
    (passStep : ∀ query (different : ¬query.1 = interface),
      globalStep query [] =
        Sum.inl (passQuery interface boundary query different))
    (passAnswerStep : ∀ query (different : ¬query.1 = interface)
        (answer : FlatAnswer U boundary) (sameTag : answer.1 = query.1),
      globalStep query [answer] =
        Sum.inr (passAnswer interface boundary answer
          (sameTag.trans_ne different)))
    (system : PFunDDS.DDS (Query U boundary) (FlatAnswer U boundary))
    (faithful : DependentDDS.TagFaithful system)
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (innerQueries : List (Query U boundary))
    (answers : List (Option (FlatAnswer U boundary)))
    (innerQuery : Query U boundary)
    (invariant : StepInv interface boundary converter sourceMatches
      localCount globalStep globalCount queries answers)
    (queryMember :
      Sum.inl innerQuery ∈
        ProtocolFn.ofStep globalStep globalCount (queries, answers)) :
    StepInv interface boundary converter sourceMatches localCount
      globalStep globalCount queries
      (answers ++ [
        PFunDDS.output (PFunDDS.fullyDefined system)
          (innerQueries ++ [innerQuery])
          (by rw [PFunDDS.dom_fullyDefined]; simp)]) := by
  rcases invariant with ⟨state, replayMember, sync⟩ | ⟨_, stepNone⟩
  case inr =>
    rw [stepNone] at queryMember
    exact absurd queryMember (Part.notMem_none _)
  obtain ⟨nonempty, syncPhase⟩ := sync
  obtain ⟨segmentValues, segmentEquation, moveEquation⟩ :=
    (ProtocolFn.mem_ofStep_iff globalStep globalCount nonempty answers _).mp
      queryMember
  rcases state with ⟨localInputs, localAnswers, phase⟩
  cases phase with
  | «local» =>
      obtain ⟨same, inputsNonempty, lastEquation, syncSegment, offsetLe,
        _upperBound, localOffsetLe⟩ := syncPhase
      dsimp only at inputsNonempty lastEquation syncSegment offsetLe localOffsetLe
      obtain ⟨localValues, localSegmentEquation, valuesEquation⟩ :=
        exists_map_some_of_map_option_map _
          (segmentEquation.symm.trans syncSegment)
      have rawMove := moveEquation
      rw [valuesEquation, selectedStep _ same localValues] at moveEquation
      cases localMove : localStep (localInput interface boundary
          (queries.getLast nonempty) same) localValues with
      | inr localOut =>
          rw [localMove] at moveEquation
          simp at moveEquation
      | inl localQuery =>
          rw [localMove] at moveEquation
          simp only [Sum.map_inl, Sum.inl.injEq] at moveEquation
          have localQueryMember :
              Sum.inl localQuery ∈
                converter.protocol (localInputs, localAnswers) := by
            rw [protocolEquation]
            refine (ProtocolFn.mem_ofStep_iff localStep localCount
              inputsNonempty localAnswers _).mpr
              ⟨localValues, localSegmentEquation, ?_⟩
            rw [lastEquation, localMove]
          generalize completionEquation :
            PFunDDS.output (PFunDDS.fullyDefined system)
              (innerQueries ++ [innerQuery])
              (by rw [PFunDDS.dom_fullyDefined]; simp) = completion
          cases completion with
          | none =>
              right
              constructor
              · have replayNone :=
                  OuterReplay.replay_append_selected_none interface boundary
                    converter sourceMatches queries answers localInputs
                    localAnswers replayMember localQueryMember
                unfold framedProtocol
                rw [replayNone]
                simp
              · rw [ProtocolFn.ofStep_apply globalStep globalCount nonempty
                  (answers ++ [none])]
                rw [List.drop_append_of_le_length offsetLe,
                  mapM_id_append_none]
          | some proper =>
              have properTag : proper.1 = interface := by
                have tagEquation :=
                  output_fully_defined_append_tag boundary system
                    faithful innerQueries innerQuery completionEquation
                rw [tagEquation, moveEquation]
                rfl
              have properEquation :
                  globalInnerAnswer interface boundary sourceMatches
                      (localAnswer interface boundary sourceMatches proper
                        properTag) =
                    proper :=
                global_inner_answer_local_answer interface boundary
                  sourceMatches proper properTag
              have replaySome :=
                OuterReplay.replay_append_selected_some interface boundary
                  converter sourceMatches queries answers localInputs
                  localAnswers replayMember localQueryMember
                  (localAnswer interface boundary sourceMatches proper
                    properTag)
              rw [properEquation] at replaySome
              left
              refine ⟨{ localInputs := localInputs
                        localAnswers := localAnswers ++
                          [some (localAnswer interface boundary sourceMatches
                            proper properTag)]
                        phase := .local }, ?_, ?_⟩
              · rw [replaySome]
                exact Part.mem_some _
              refine ⟨nonempty, same, inputsNonempty, ?_, ?_, ?_, ?_, ?_⟩
              · simpa using lastEquation
              · rw [List.drop_append_of_le_length offsetLe,
                  List.drop_append_of_le_length localOffsetLe,
                  List.map_append, syncSegment]
                congr 1
                simp only [List.map_cons, List.map_nil, Option.map_some]
                rw [properEquation]
              · simp only [List.length_append, List.length_singleton]
                omega
              · have segmentLength :
                    segmentValues.length <
                      globalCount (queries.getLast nonempty) :=
                  (globalIssues (queries.getLast nonempty)
                    segmentValues).mp ⟨innerQuery, rawMove.symm⟩
                have dropLength := congrArg List.length segmentEquation
                simp only [List.length_drop, List.length_map]
                  at dropLength
                simp only [List.length_append, List.length_singleton]
                omega
              · simp only [List.length_append, List.length_singleton]
                omega
  | passPending pending different =>
      obtain ⟨pendingEquation, lengthEquation, complete⟩ := syncPhase
      have segmentEmpty :
          answers.drop ((queries.dropLast.map globalCount).sum) = [] := by
        rw [← lengthEquation]
        exact List.drop_length
      have valuesEmpty : segmentValues = [] := by
        rw [segmentEmpty] at segmentEquation
        cases segmentValues with
        | nil => rfl
        | cons head tail => simp at segmentEquation
      have differentLast :
          ¬(queries.getLast nonempty).1 = interface := by
        rw [← pendingEquation]
        exact different
      rw [valuesEmpty, passStep (queries.getLast nonempty) differentLast]
        at moveEquation
      have innerQueryEquation :
          innerQuery =
            passQuery interface boundary (queries.getLast nonempty)
              differentLast :=
        Sum.inl.inj moveEquation
      generalize completionEquation :
        PFunDDS.output (PFunDDS.fullyDefined system)
          (innerQueries ++ [innerQuery])
          (by rw [PFunDDS.dom_fullyDefined]; simp) = completion
      cases completion with
      | none =>
          right
          constructor
          · have replayNone :=
              OuterReplay.replay_append_pass_none interface boundary
                converter sourceMatches queries answers localInputs
                localAnswers pending different replayMember
            unfold framedProtocol
            rw [replayNone]
            simp
          · rw [ProtocolFn.ofStep_apply globalStep globalCount nonempty
              (answers ++ [none])]
            rw [← lengthEquation, List.drop_left, mapM_id_singleton_none]
      | some proper =>
          have properTagLast :
              proper.1 = (queries.getLast nonempty).1 := by
            have tagEquation :=
              output_fully_defined_append_tag boundary system
                faithful innerQueries innerQuery completionEquation
            rw [tagEquation, innerQueryEquation]
            rfl
          have properTagPending : proper.1 = pending.1 := by
            rw [properTagLast, ← pendingEquation]
          have replaySome :=
            OuterReplay.replay_append_pass_some interface boundary
              converter sourceMatches queries answers localInputs
              localAnswers pending different replayMember proper
              properTagPending
          dsimp only at complete
          left
          refine ⟨{ localInputs := localInputs
                    localAnswers := localAnswers
                    phase := .passReturned
                      (passAnswer interface boundary proper
                        (properTagPending.trans_ne different)) }, ?_, ?_⟩
          · rw [replaySome]
            exact Part.mem_some _
          refine ⟨nonempty, proper, properTagLast, differentLast, ?_, ?_,
            ?_, complete⟩
          · rw [← lengthEquation, List.drop_left]
          · simp only [List.length_append, List.length_singleton]
            omega
          · rfl
  | passReturned answer =>
      obtain ⟨proper, sameTag, different, segmentEquation', _lengthEquation,
        _answerEquation, _complete⟩ := syncPhase
      have valuesEquation : segmentValues = [proper] := by
        rw [segmentEquation'] at segmentEquation
        cases segmentValues with
        | nil => simp at segmentEquation
        | cons head tail =>
            cases tail with
            | nil =>
                simp only [List.map_cons, List.map_nil, List.cons.injEq,
                  Option.some.injEq] at segmentEquation
                rw [segmentEquation.1]
            | cons second rest => simp at segmentEquation
      rw [valuesEquation,
        passAnswerStep (queries.getLast nonempty) different proper sameTag]
        at moveEquation
      simp at moveEquation

omit [DecidableEq U.Code] in
/-- The invariant survives opening a new outer round. -/
theorem step_inv_open
    (protocolEquation :
      converter.protocol = ProtocolFn.ofStep localStep localCount)
    (globalIssues : ∀ query answers,
      (∃ inner, globalStep query answers = Sum.inl inner) ↔
        answers.length < globalCount query)
    (selectedStep : ∀ query (same : query.1 = interface)
        (localAnswers : List (U.output source)),
      globalStep query
          (localAnswers.map
            (globalInnerAnswer interface boundary sourceMatches)) =
        Sum.map (globalQuery interface boundary sourceMatches)
          (globalAnswer interface boundary)
          (localStep (localInput interface boundary query same)
            localAnswers))
    (selectedCount : ∀ query (same : query.1 = interface),
      globalCount query =
        localCount (localInput interface boundary query same))
    (passStep : ∀ query (different : ¬query.1 = interface),
      globalStep query [] =
        Sum.inl (passQuery interface boundary query different))
    (passCount : ∀ query (_ : ¬query.1 = interface),
      globalCount query = 1)
    (queries :
      List (Query U (TargetBoundary interface boundary (target := target))))
    (answers : List (Option (FlatAnswer U boundary)))
    (query : Query U (TargetBoundary interface boundary (target := target)))
    (ready : (queries = [] ∧ answers = []) ∨
      ∃ outerAnswer,
        Reach (ProtocolFn.ofStep globalStep globalCount)
            (queries, answers) ∧
          Sum.inr outerAnswer ∈
            ProtocolFn.ofStep globalStep globalCount (queries, answers) ∧
          StepInv interface boundary converter sourceMatches localCount
            globalStep globalCount queries answers) :
    StepInv interface boundary converter sourceMatches localCount
      globalStep globalCount (queries ++ [query]) answers := by
  rcases ready with ⟨rfl, rfl⟩ |
    ⟨outerAnswer, _reachable, answerMember, invariant⟩
  · rw [List.nil_append]
    left
    have replayEquation :
        replay interface boundary converter sourceMatches ([query], []) =
          Part.some (firstState interface boundary query) := by
      simp only [replay]
      rw [replayCore.eq_def]
    by_cases same : query.1 = interface
    · have stateEquation :
          (firstState interface boundary query :
            FrameState interface boundary (source := source)
              (target := target)) =
            { localInputs := [localInput interface boundary query same]
              localAnswers := []
              phase := .local } := by
        simp [firstState, openRound, same]
      refine ⟨_, (by rw [replayEquation]; exact Part.mem_some _), ?_⟩
      rw [stateEquation]
      refine ⟨by simp, ?_⟩
      simp only [List.getLast_singleton, List.dropLast_singleton,
        List.map_nil, List.sum_nil, List.drop_zero]
      exact ⟨same, by simp, by simp, by simp, by simp, by simp, by simp⟩
    · have stateEquation :
          (firstState interface boundary query :
            FrameState interface boundary (source := source)
              (target := target)) =
            { localInputs := []
              localAnswers := []
              phase := .passPending query same } := by
        simp [firstState, openRound, same]
      refine ⟨_, (by rw [replayEquation]; exact Part.mem_some _), ?_⟩
      rw [stateEquation]
      exact ⟨by simp, by simp [List.getLast_singleton], by simp, by simp⟩
  · rcases invariant with ⟨state, replayMember, sync⟩ | ⟨_, stepNone⟩
    case inr =>
      rw [stepNone] at answerMember
      exact absurd answerMember (Part.notMem_none _)
    obtain ⟨nonempty, syncPhase⟩ := sync
    obtain ⟨segmentValues, segmentEquation, moveEquation⟩ :=
      (ProtocolFn.mem_ofStep_iff globalStep globalCount nonempty answers
        _).mp answerMember
    rcases state with ⟨localInputs, localAnswers, phase⟩
    cases phase with
    | «local» =>
        obtain ⟨same, inputsNonempty, lastEquation, syncSegment, offsetLe,
          upperBound, localOffsetLe⟩ := syncPhase
        dsimp only at inputsNonempty lastEquation syncSegment offsetLe upperBound localOffsetLe
        obtain ⟨localValues, localSegmentEquation, valuesEquation⟩ :=
          exists_map_some_of_map_option_map _
            (segmentEquation.symm.trans syncSegment)
        have rawMove := moveEquation
        rw [valuesEquation, selectedStep _ same localValues] at moveEquation
        cases localMove : localStep (localInput interface boundary
            (queries.getLast nonempty) same) localValues with
        | inl localQuery =>
            rw [localMove] at moveEquation
            simp at moveEquation
        | inr localOut =>
            rw [localMove] at moveEquation
            simp only [Sum.map_inr, Sum.inr.injEq] at moveEquation
            have stateMoveMember :
                Sum.inr (globalAnswer interface boundary localOut) ∈
                  stateMove interface boundary converter sourceMatches
                    { localInputs := localInputs
                      localAnswers := localAnswers
                      phase := .local } := by
              simp only [stateMove, Part.mem_map_iff]
              refine ⟨Sum.inr localOut, ?_, rfl⟩
              rw [protocolEquation]
              refine (ProtocolFn.mem_ofStep_iff localStep localCount
                inputsNonempty localAnswers _).mpr
                ⟨localValues, localSegmentEquation, ?_⟩
              rw [lastEquation, localMove]
            have replayNext :=
              OuterReplay.replay_append_outside_of_mem interface boundary
                converter sourceMatches (queries, answers) replayMember
                stateMoveMember query
            have segmentFull :
                ¬segmentValues.length <
                  globalCount (queries.getLast nonempty) :=
              ProtocolFn.not_lt_cnt_of_eq_inr globalIssues rawMove.symm
            have dropLength := congrArg List.length segmentEquation
            simp only [List.length_drop, List.length_map] at dropLength
            have answersLength :
                answers.length =
                  (queries.dropLast.map globalCount).sum +
                    globalCount (queries.getLast nonempty) := by
              omega
            have localValuesLength :
                localValues.length = segmentValues.length := by
              rw [valuesEquation]
              simp
            have localDropLength :=
              congrArg List.length localSegmentEquation
            simp only [List.length_drop, List.length_map]
              at localDropLength
            have localAnswersLength :
                localAnswers.length =
                  (localInputs.map localCount).sum := by
              rw [sum_map_dropLast_getLast localCount inputsNonempty,
                lastEquation, ← selectedCount _ same]
              omega
            have newOffset :
                (queries.map globalCount).sum = answers.length := by
              rw [sum_map_dropLast_getLast globalCount nonempty]
              omega
            left
            by_cases sameNew : query.1 = interface
            · have openEquation :
                  openRound interface boundary
                      ({ localInputs := localInputs
                         localAnswers := localAnswers
                         phase := .local } :
                        FrameState interface boundary (source := source)
                          (target := target)) query =
                    { localInputs := localInputs ++
                        [localInput interface boundary query sameNew]
                      localAnswers := localAnswers
                      phase := .local } := by
                simp [openRound, sameNew]
              refine ⟨_, (by rw [replayNext, openEquation]; exact Part.mem_some _), ?_⟩
              refine ⟨by simp, ?_⟩
              simp only [List.getLast_append_singleton,
                List.dropLast_concat]
              refine ⟨sameNew, by simp, (by simp), ?_, ?_, ?_, ?_⟩
              · rw [newOffset, List.drop_length, ← localAnswersLength,
                  List.drop_length]
                rfl
              · exact newOffset.le
              · rw [newOffset]
                omega
              · omega
            · have openEquation :
                  openRound interface boundary
                      ({ localInputs := localInputs
                         localAnswers := localAnswers
                         phase := .local } :
                        FrameState interface boundary (source := source)
                          (target := target)) query =
                    { localInputs := localInputs
                      localAnswers := localAnswers
                      phase := .passPending query sameNew } := by
                simp [openRound, sameNew]
              refine ⟨_, (by rw [replayNext, openEquation]; exact Part.mem_some _), ?_⟩
              refine ⟨by simp, by simp, ?_, localAnswersLength⟩
              rw [List.dropLast_concat]
              exact newOffset.symm
    | passPending pending different =>
        obtain ⟨pendingEquation, lengthEquation, _complete⟩ := syncPhase
        have segmentEmpty :
            answers.drop ((queries.dropLast.map globalCount).sum) = [] := by
          rw [← lengthEquation]
          exact List.drop_length
        have valuesEmpty : segmentValues = [] := by
          rw [segmentEmpty] at segmentEquation
          cases segmentValues with
          | nil => rfl
          | cons head tail => simp at segmentEquation
        have differentLast :
            ¬(queries.getLast nonempty).1 = interface := by
          rw [← pendingEquation]
          exact different
        rw [valuesEmpty,
          passStep (queries.getLast nonempty) differentLast]
          at moveEquation
        simp at moveEquation
    | passReturned answer =>
        obtain ⟨proper, sameTag, differentLast, segmentEquation',
          lengthEquation, answerEquation, complete⟩ := syncPhase
        dsimp only at answerEquation complete
        have stateMoveMember :
            Sum.inr answer ∈
              stateMove interface boundary converter sourceMatches
                { localInputs := localInputs
                  localAnswers := localAnswers
                  phase := .passReturned answer } := by
          simp [stateMove]
        have replayNext :=
          OuterReplay.replay_append_outside_of_mem interface boundary
            converter sourceMatches (queries, answers) replayMember
            stateMoveMember query
        have newOffset :
            (queries.map globalCount).sum = answers.length := by
          rw [sum_map_dropLast_getLast globalCount nonempty,
            passCount (queries.getLast nonempty) differentLast]
          omega
        left
        by_cases sameNew : query.1 = interface
        · have openEquation :
              openRound interface boundary
                  ({ localInputs := localInputs
                     localAnswers := localAnswers
                     phase := .passReturned answer } :
                    FrameState interface boundary (source := source)
                      (target := target)) query =
                { localInputs := localInputs ++
                    [localInput interface boundary query sameNew]
                  localAnswers := localAnswers
                  phase := .local } := by
            simp [openRound, sameNew]
          refine ⟨_, (by rw [replayNext, openEquation]; exact Part.mem_some _), ?_⟩
          refine ⟨by simp, ?_⟩
          simp only [List.getLast_append_singleton, List.dropLast_concat]
          refine ⟨sameNew, by simp, (by simp), ?_, ?_, ?_, ?_⟩
          · rw [newOffset, List.drop_length, ← complete, List.drop_length]
            rfl
          · exact newOffset.le
          · rw [newOffset]
            omega
          · omega
        · have openEquation :
              openRound interface boundary
                  ({ localInputs := localInputs
                     localAnswers := localAnswers
                     phase := .passReturned answer } :
                    FrameState interface boundary (source := source)
                      (target := target)) query =
                { localInputs := localInputs
                  localAnswers := localAnswers
                  phase := .passPending query sameNew } := by
            simp [openRound, sameNew]
          refine ⟨_, (by rw [replayNext, openEquation]; exact Part.mem_some _), ?_⟩
          refine ⟨by simp, by simp, ?_, complete⟩
          rw [List.dropLast_concat]
          exact newOffset.symm

omit [DecidableEq U.Code] in
/-- **Framed `ofStep` application coherence, applied form**: on a
tag-faithful flat system, applying the boundary-wide step converter agrees
with applying the canonical frame of the local step converter. -/
theorem apply_ofStep_eq_apply_framed
    (protocolEquation :
      converter.protocol = ProtocolFn.ofStep localStep localCount)
    (globalIssues : ∀ query answers,
      (∃ inner, globalStep query answers = Sum.inl inner) ↔
        answers.length < globalCount query)
    (selectedStep : ∀ query (same : query.1 = interface)
        (localAnswers : List (U.output source)),
      globalStep query
          (localAnswers.map
            (globalInnerAnswer interface boundary sourceMatches)) =
        Sum.map (globalQuery interface boundary sourceMatches)
          (globalAnswer interface boundary)
          (localStep (localInput interface boundary query same)
            localAnswers))
    (selectedCount : ∀ query (same : query.1 = interface),
      globalCount query =
        localCount (localInput interface boundary query same))
    (passStep : ∀ query (different : ¬query.1 = interface),
      globalStep query [] =
        Sum.inl (passQuery interface boundary query different))
    (passAnswerStep : ∀ query (different : ¬query.1 = interface)
        (answer : FlatAnswer U boundary) (sameTag : answer.1 = query.1),
      globalStep query [answer] =
        Sum.inr (passAnswer interface boundary answer
          (sameTag.trans_ne different)))
    (passCount : ∀ query (_ : ¬query.1 = interface),
      globalCount query = 1)
    (system : PFunDDS.DDS (Query U boundary) (FlatAnswer U boundary))
    (faithful : DependentDDS.TagFaithful system) :
    PFunConverter.apply (ProtocolFn.ofStep globalStep globalCount) system =
      PFunConverter.apply
        (framedProtocol interface boundary converter sourceMatches)
        system := by
  apply PFunConverter.apply_eq_of_reachable_invariant _ _ system
    (fun queries answers =>
      StepInv interface boundary converter sourceMatches localCount
        globalStep globalCount queries answers)
  · intro queries answers query ready
    constructor
    · rcases ready with ⟨rfl, rfl⟩ |
        ⟨outerAnswer, reachable, answerMember, _⟩
      · exact Reach.first query
      · exact Reach.next reachable answerMember query
    · exact step_inv_open interface boundary protocolEquation globalIssues
        selectedStep selectedCount passStep passCount
        queries answers query ready
  · intro queries innerQueries answers innerQuery _reachable invariant
      queryMember
    exact step_inv_completion interface boundary protocolEquation
      globalIssues selectedStep passStep passAnswerStep system faithful
      queries innerQueries answers innerQuery invariant queryMember
  · intro queries answers _reachable invariant
    exact step_eq_framed_of_inv interface boundary protocolEquation
      selectedStep passStep passAnswerStep queries answers invariant

end

end StepFrame

end Internal

export Internal (framedConverter frameTest)

end TypedFraming

open TypedFraming.Internal

variable {I : Type i} {U : SignatureUniverse}
variable [DecidableEq I] [DecidableEq U.Code]
variable {source target : U.Code}
variable (interface : I) (boundary : Boundary U I)

/-- Arbitrary stateful typed attachment is exactly strict application of the
canonical all-interface frame.  This is the deterministic coherence theorem
needed to compile every boundary-indexed AC experiment to one strict test. -/
theorem DependentDDS.flatten_attach_eq_apply_framed
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (system : DependentDDS U boundary) :
    (system.attach interface converter sourceMatches).flatten =
      PFunConverter.apply
        (framedConverter interface boundary converter sourceMatches).val
        system.flatten := by
  apply Subtype.ext
  funext history
  have encodedEquation :
      ((system.attach interface converter sourceMatches).flatten.1 history).map
          encodeAnswer =
        ((PFunConverter.apply
          (framedProtocol interface boundary converter sourceMatches)
          system.flatten).1 history).map encodeAnswer := by
    calc
      ((system.attach interface converter sourceMatches).flatten.1 history).map
          encodeAnswer =
        (system.attach interface converter sourceMatches).embed.1
          (history.map encodeQuery) :=
            (DependentDDS.embed_apply_encoded
              (system.attach interface converter sourceMatches) history).symm
      _ = PFunConverter.General.attachRaw interface converter.embeddedDDC
          system.embed (history.map encodeQuery) := by
            rw [DependentDDS.embed_attach]
            rfl
      _ = (PFunConverter.applyRaw
          (framedProtocol interface boundary converter sourceMatches)
          system.flatten history).map encodeAnswer :=
            OuterBridge.attach_raw_encoded_eq_map_apply_raw interface boundary
              converter sourceMatches system history
      _ = ((PFunConverter.apply
          (framedProtocol interface boundary converter sourceMatches)
          system.flatten).1 history).map encodeAnswer := rfl
  apply Part.ext'
  · have domainEquation := congrArg Part.Dom encodedEquation
    simpa using domainEquation
  · intro leftMember rightMember
    let leftAnswer := PFunDDS.output
      (system.attach interface converter sourceMatches).flatten history leftMember
    let rightAnswer := PFunDDS.output
      (PFunConverter.apply
        (framedProtocol interface boundary converter sourceMatches)
        system.flatten) history rightMember
    have tagEqual : leftAnswer.1 = rightAnswer.1 :=
      ((system.attach interface converter sourceMatches).flatten_tag_faithful
          history leftMember).trans
        (OuterBridge.framed_apply_tag_faithful interface boundary converter
          sourceMatches system history rightMember).symm
    have leftEncoded : encodeAnswer leftAnswer ∈
        ((system.attach interface converter sourceMatches).flatten.1
          history).map encodeAnswer :=
      Part.mem_map _ (Part.get_mem leftMember)
    have rightEncoded : encodeAnswer rightAnswer ∈
        ((PFunConverter.apply
          (framedProtocol interface boundary converter sourceMatches)
          system.flatten).1 history).map encodeAnswer :=
      Part.mem_map _ (Part.get_mem rightMember)
    have leftInRight : encodeAnswer leftAnswer ∈
        ((PFunConverter.apply
          (framedProtocol interface boundary converter sourceMatches)
          system.flatten).1 history).map encodeAnswer := by
      rw [← encodedEquation]
      exact leftEncoded
    have encodedEqual : encodeAnswer leftAnswer = encodeAnswer rightAnswer :=
      Part.mem_unique leftInRight rightEncoded
    change leftAnswer = rightAnswer
    rcases leftAnswer with ⟨leftTag, leftValue⟩
    rcases rightAnswer with ⟨rightTag, rightValue⟩
    dsimp only at tagEqual
    subst rightTag
    simp only [encodeAnswer] at encodedEqual
    have valueEqual : leftValue = rightValue :=
      eq_of_heq (Sigma.mk.inj encodedEqual).2
    subst rightValue
    rfl

omit [DecidableEq U.Code] in
/-- **Typed simple-attachment coherence** (resource-aware): after application
to a tag-faithful flat system, the canonical frame of a one-query
`DeterministicConverter.ofFunctions` converter is exactly the boundary-wide
simple converter whose query/answer maps act as the local maps at the
selected interface and pass every other interface through.  This is
deliberately *not* a raw trace equivalence: the frame rejects wrong-tag
answers that an unguarded global `simpleFn` accepts, and tag-faithful
application is what makes the two agree. -/
theorem TypedFraming.apply_framed_ofFunctions_eq_apply_simpleFn
    (queryMap : U.input target → U.input source)
    (answerMap : U.output source → U.output target)
    (sourceMatches : boundary interface = source)
    (globalQueryMap :
      Query U (TargetBoundary interface boundary (target := target)) →
        Query U boundary)
    (globalAnswerMap :
      FlatAnswer U boundary →
        FlatAnswer U (TargetBoundary interface boundary (target := target)))
    (queryLocal : ∀ query (same : query.1 = interface),
      globalQueryMap query =
        globalQuery interface boundary sourceMatches
          (queryMap (localInput interface boundary query same)))
    (queryPass : ∀ query (different : ¬query.1 = interface),
      globalQueryMap query = passQuery interface boundary query different)
    (answerLocal : ∀ answer (same : answer.1 = interface),
      globalAnswerMap answer =
        globalAnswer interface boundary
          (answerMap (localAnswer interface boundary sourceMatches
            answer same)))
    (answerPass : ∀ answer (different : ¬answer.1 = interface),
      globalAnswerMap answer = passAnswer interface boundary answer different)
    (system : PFunDDS.DDS (Query U boundary) (FlatAnswer U boundary))
    (faithful : DependentDDS.TagFaithful system) :
    PFunConverter.apply
        (framedConverter interface boundary
          (DeterministicConverter.ofFunctions queryMap answerMap)
          sourceMatches).val system =
      PFunConverter.apply
        (PFunConverter.simpleFn globalQueryMap globalAnswerMap) system :=
  (Internal.SimpleFrame.apply_simpleFn_eq_apply_framed interface boundary
    queryLocal queryPass answerLocal answerPass system faithful).symm

/-- **Typed simple-attachment coherence, dependent form**: attaching a
one-query `ofFunctions` converter and flattening is exactly protocol
application of the boundary-wide simple converter to the flattened
resource. -/
theorem DependentDDS.flatten_attach_ofFunctions
    (queryMap : U.input target → U.input source)
    (answerMap : U.output source → U.output target)
    (sourceMatches : boundary interface = source)
    (globalQueryMap :
      Query U (TargetBoundary interface boundary (target := target)) →
        Query U boundary)
    (globalAnswerMap :
      FlatAnswer U boundary →
        FlatAnswer U (TargetBoundary interface boundary (target := target)))
    (queryLocal : ∀ query (same : query.1 = interface),
      globalQueryMap query =
        globalQuery interface boundary sourceMatches
          (queryMap (localInput interface boundary query same)))
    (queryPass : ∀ query (different : ¬query.1 = interface),
      globalQueryMap query = passQuery interface boundary query different)
    (answerLocal : ∀ answer (same : answer.1 = interface),
      globalAnswerMap answer =
        globalAnswer interface boundary
          (answerMap (localAnswer interface boundary sourceMatches
            answer same)))
    (answerPass : ∀ answer (different : ¬answer.1 = interface),
      globalAnswerMap answer = passAnswer interface boundary answer different)
    (system : DependentDDS U boundary) :
    (system.attach interface
        (DeterministicConverter.ofFunctions queryMap answerMap)
        sourceMatches).flatten =
      PFunConverter.apply
        (PFunConverter.simpleFn globalQueryMap globalAnswerMap)
        system.flatten := by
  rw [DependentDDS.flatten_attach_eq_apply_framed]
  exact TypedFraming.apply_framed_ofFunctions_eq_apply_simpleFn interface
    boundary queryMap answerMap sourceMatches globalQueryMap globalAnswerMap
    queryLocal queryPass answerLocal answerPass system.flatten
    system.flatten_tag_faithful

omit [DecidableEq U.Code] in
/-- **Framed `ofStep` application coherence** (resource-aware): after
application to a tag-faithful flat system, the canonical frame of a
converter whose local protocol is an outer-memoryless `ProtocolFn.ofStep`
presentation is exactly the boundary-wide `ProtocolFn.ofStep` of any total
global step that restricts to the local step on selected rounds and makes
one pass-through resource call elsewhere.  As with the one-query receipt,
this is deliberately not a raw trace equivalence: the frame blocks
wrong-tag answers that the total global step accepts. -/
theorem TypedFraming.apply_framed_ofStep_eq_apply_ofStep
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (localStep :
      U.input target → List (U.output source) →
        U.input source ⊕ U.output target)
    (localCount : U.input target → ℕ)
    (protocolEquation :
      converter.protocol = PFunConverter.ProtocolFn.ofStep localStep
        localCount)
    (globalStep :
      Query U (TargetBoundary interface boundary (target := target)) →
        List (FlatAnswer U boundary) →
          Query U boundary ⊕
            FlatAnswer U (TargetBoundary interface boundary
              (target := target)))
    (globalCount :
      Query U (TargetBoundary interface boundary (target := target)) → ℕ)
    (globalIssues : ∀ query answers,
      (∃ inner, globalStep query answers = Sum.inl inner) ↔
        answers.length < globalCount query)
    (selectedStep : ∀ query (same : query.1 = interface)
        (localAnswers : List (U.output source)),
      globalStep query
          (localAnswers.map
            (globalInnerAnswer interface boundary sourceMatches)) =
        Sum.map (globalQuery interface boundary sourceMatches)
          (globalAnswer interface boundary)
          (localStep (localInput interface boundary query same)
            localAnswers))
    (selectedCount : ∀ query (same : query.1 = interface),
      globalCount query =
        localCount (localInput interface boundary query same))
    (passStep : ∀ query (different : ¬query.1 = interface),
      globalStep query [] =
        Sum.inl (passQuery interface boundary query different))
    (passAnswerStep : ∀ query (different : ¬query.1 = interface)
        (answer : FlatAnswer U boundary) (sameTag : answer.1 = query.1),
      globalStep query [answer] =
        Sum.inr (passAnswer interface boundary answer
          (sameTag.trans_ne different)))
    (passCount : ∀ query (_ : ¬query.1 = interface),
      globalCount query = 1)
    (system : PFunDDS.DDS (Query U boundary) (FlatAnswer U boundary))
    (faithful : DependentDDS.TagFaithful system) :
    PFunConverter.apply
        (framedConverter interface boundary converter sourceMatches).val
        system =
      PFunConverter.apply
        (PFunConverter.ProtocolFn.ofStep globalStep globalCount) system :=
  (Internal.StepFrame.apply_ofStep_eq_apply_framed interface boundary
    protocolEquation globalIssues selectedStep selectedCount passStep
    passAnswerStep passCount system faithful).symm

/-- **Framed `ofStep` application coherence, dependent form**: attaching a
bounded-step converter and flattening is exactly protocol application of
the boundary-wide step converter to the flattened resource. -/
theorem DependentDDS.flatten_attach_ofStep
    (converter : DeterministicConverter U source target)
    (sourceMatches : boundary interface = source)
    (localStep :
      U.input target → List (U.output source) →
        U.input source ⊕ U.output target)
    (localCount : U.input target → ℕ)
    (protocolEquation :
      converter.protocol = PFunConverter.ProtocolFn.ofStep localStep
        localCount)
    (globalStep :
      Query U (TargetBoundary interface boundary (target := target)) →
        List (FlatAnswer U boundary) →
          Query U boundary ⊕
            FlatAnswer U (TargetBoundary interface boundary
              (target := target)))
    (globalCount :
      Query U (TargetBoundary interface boundary (target := target)) → ℕ)
    (globalIssues : ∀ query answers,
      (∃ inner, globalStep query answers = Sum.inl inner) ↔
        answers.length < globalCount query)
    (selectedStep : ∀ query (same : query.1 = interface)
        (localAnswers : List (U.output source)),
      globalStep query
          (localAnswers.map
            (globalInnerAnswer interface boundary sourceMatches)) =
        Sum.map (globalQuery interface boundary sourceMatches)
          (globalAnswer interface boundary)
          (localStep (localInput interface boundary query same)
            localAnswers))
    (selectedCount : ∀ query (same : query.1 = interface),
      globalCount query =
        localCount (localInput interface boundary query same))
    (passStep : ∀ query (different : ¬query.1 = interface),
      globalStep query [] =
        Sum.inl (passQuery interface boundary query different))
    (passAnswerStep : ∀ query (different : ¬query.1 = interface)
        (answer : FlatAnswer U boundary) (sameTag : answer.1 = query.1),
      globalStep query [answer] =
        Sum.inr (passAnswer interface boundary answer
          (sameTag.trans_ne different)))
    (passCount : ∀ query (_ : ¬query.1 = interface),
      globalCount query = 1)
    (system : DependentDDS U boundary) :
    (system.attach interface converter sourceMatches).flatten =
      PFunConverter.apply
        (PFunConverter.ProtocolFn.ofStep globalStep globalCount)
        system.flatten := by
  rw [DependentDDS.flatten_attach_eq_apply_framed]
  exact TypedFraming.apply_framed_ofStep_eq_apply_ofStep interface boundary
    converter sourceMatches localStep localCount protocolEquation
    globalStep globalCount globalIssues selectedStep selectedCount passStep
    passAnswerStep passCount system.flatten system.flatten_tag_faithful

/-! ## A memoryless bijection converter IS a relabelling

`Converter.ofMaps` with *bijective* maps changes no behaviour, only the
names of the letters: after flattening, attaching it is exactly
`PFunDDS.DDS.relabel` along the boundary-wide alphabet equivalence that
acts at the selected interface and is the identity everywhere else
(`fibreEquiv`).  Everything the strict theory knows about relabelling —
that it is an isometry (`StrictContext.maxEDist_relabel`), that it
preserves and reflects equivalence (`equivalent_relabel_iff`) — therefore
applies verbatim to such an attachment.

The proof is assembly, not new transcript work:
`flatten_attach_ofFunctions` (the frame of a one-query converter is the
boundary-wide `simpleFn`) → `apply_simpleFn_eq_simple_apply` (that
protocol function is the paper-facing simple DDC) → `DDC.simple_apply`
(whose closed form `map d ∘ S ∘ map c` IS `DDS.relabel_raw`).

The identity case is the payoff: with `e = f = Equiv.refl` the relabelling
is the boundary transport itself, so attaching `ofFunctions id id` is the
resource, heterogeneously (`DependentDDS.attach_ofFunctions_id_heq`). -/

/-- The alphabet equivalence induced at one interface: `e` on the fibre of
`interface`, the identity cast on every other fibre.  Stated for an
arbitrary alphabet family so that one definition serves both the query
side (`U.input`) and the answer side (`U.output`). -/
def fibreCongr (alphabet : U.Code → Type w)
    (sourceMatches : boundary interface = source)
    (equivalence : alphabet source ≃ alphabet target) (other : I) :
    alphabet (boundary other) ≃
      alphabet (replaceBoundary boundary interface target other) :=
  if same : other = interface then
    (Equiv.cast (congrArg alphabet (by rw [same]; exact sourceMatches))).trans
      (equivalence.trans (Equiv.cast (congrArg alphabet
        (by rw [same, replace_boundary_same]))))
  else
    Equiv.cast (congrArg alphabet
      (replace_boundary_ne boundary same target).symm)

/-- **`fibreEquiv`**: the boundary-wide alphabet equivalence that acts as
`equivalence` at `interface` and as the identity elsewhere.  At
`alphabet := U.input` this is an equivalence `Query U boundary ≃ Query U
(TargetBoundary …)`; at `alphabet := U.output` one of the flat answer
alphabets. -/
def fibreEquiv (alphabet : U.Code → Type w)
    (sourceMatches : boundary interface = source)
    (equivalence : alphabet source ≃ alphabet target) :
    (Σ other, alphabet (boundary other)) ≃
      (Σ other, alphabet (replaceBoundary boundary interface target other)) :=
  Equiv.sigmaCongrRight
    (fibreCongr interface boundary alphabet sourceMatches equivalence)

omit [DecidableEq U.Code] in
/-- At the selected interface, the inverse fibre equivalence is exactly the
frame's own query re-encoding. -/
theorem fibre_equiv_symm_local
    (sourceMatches : boundary interface = source)
    (queryEquiv : U.input source ≃ U.input target)
    (query : Query U (TargetBoundary interface boundary (target := target)))
    (same : query.1 = interface) :
    (fibreEquiv interface boundary U.input sourceMatches queryEquiv).symm
        query =
      globalQuery interface boundary sourceMatches
        (⇑queryEquiv.symm (localInput interface boundary query same)) := by
  rcases query with ⟨other, value⟩
  change other = interface at same
  subst other
  show (⟨interface,
      (fibreCongr interface boundary U.input sourceMatches queryEquiv
        interface).symm value⟩ : Query U boundary) = _
  rw [fibreCongr, dif_pos rfl]
  rfl

omit [DecidableEq U.Code] in
/-- At every other interface, the inverse fibre equivalence is the frame's
pass-through. -/
theorem fibre_equiv_symm_pass
    (sourceMatches : boundary interface = source)
    (queryEquiv : U.input source ≃ U.input target)
    (query : Query U (TargetBoundary interface boundary (target := target)))
    (different : ¬query.1 = interface) :
    (fibreEquiv interface boundary U.input sourceMatches queryEquiv).symm
        query =
      passQuery interface boundary query different := by
  rcases query with ⟨other, value⟩
  change ¬other = interface at different
  show (⟨other,
      (fibreCongr interface boundary U.input sourceMatches queryEquiv
        other).symm value⟩ : Query U boundary) = _
  rw [fibreCongr, dif_neg different]
  rfl

omit [DecidableEq U.Code] in
/-- At the selected interface, the fibre equivalence is the frame's own
answer re-encoding. -/
theorem fibre_equiv_answer_local
    (sourceMatches : boundary interface = source)
    (answerEquiv : U.output source ≃ U.output target)
    (answer : FlatAnswer U boundary) (same : answer.1 = interface) :
    fibreEquiv interface boundary U.output sourceMatches answerEquiv answer =
      globalAnswer interface boundary
        (answerEquiv
          (localAnswer interface boundary sourceMatches answer same)) := by
  rcases answer with ⟨other, value⟩
  change other = interface at same
  subst other
  show (⟨interface,
      fibreCongr interface boundary U.output sourceMatches answerEquiv
        interface value⟩ :
      FlatAnswer U (TargetBoundary interface boundary (target := target))) = _
  rw [fibreCongr, dif_pos rfl]
  rfl

omit [DecidableEq U.Code] in
/-- At every other interface, the fibre equivalence is the frame's
pass-through. -/
theorem fibre_equiv_answer_pass
    (sourceMatches : boundary interface = source)
    (answerEquiv : U.output source ≃ U.output target)
    (answer : FlatAnswer U boundary) (different : ¬answer.1 = interface) :
    fibreEquiv interface boundary U.output sourceMatches answerEquiv answer =
      passAnswer interface boundary answer different := by
  rcases answer with ⟨other, value⟩
  change ¬other = interface at different
  show (⟨other,
      fibreCongr interface boundary U.output sourceMatches answerEquiv
        other value⟩ :
      FlatAnswer U (TargetBoundary interface boundary (target := target))) = _
  rw [fibreCongr, dif_neg different]
  rfl

/-- **A memoryless bijection converter is a relabelling** (dependent
form).  Attaching `ofFunctions ⇑e.symm ⇑f` for alphabet *equivalences*
`e`, `f` and flattening is exactly `PFunDDS.DDS.relabel` of the flattened
resource along the fibre equivalences — no transcript argument survives
the reduction, because a bijective memoryless converter renames letters
and does nothing else. -/
theorem DependentDDS.flatten_attach_ofMaps_eq_relabel
    (sourceMatches : boundary interface = source)
    (queryEquiv : U.input source ≃ U.input target)
    (answerEquiv : U.output source ≃ U.output target)
    (system : DependentDDS U boundary) :
    (system.attach interface
        (DeterministicConverter.ofFunctions ⇑queryEquiv.symm ⇑answerEquiv)
        sourceMatches).flatten =
      PFunDDS.DDS.relabel
        (fibreEquiv interface boundary U.input sourceMatches queryEquiv)
        (fibreEquiv interface boundary U.output sourceMatches answerEquiv)
        system.flatten := by
  rw [DependentDDS.flatten_attach_ofFunctions interface boundary
      (⇑queryEquiv.symm) (⇑answerEquiv) sourceMatches
      (⇑(fibreEquiv interface boundary U.input sourceMatches queryEquiv).symm)
      (⇑(fibreEquiv interface boundary U.output sourceMatches answerEquiv))
      (fibre_equiv_symm_local interface boundary sourceMatches queryEquiv)
      (fibre_equiv_symm_pass interface boundary sourceMatches queryEquiv)
      (fibre_equiv_answer_local interface boundary sourceMatches answerEquiv)
      (fibre_equiv_answer_pass interface boundary sourceMatches answerEquiv)
      system,
    PFunConverter.ProtocolFn.apply_simpleFn_eq_simple_apply]
  apply Subtype.ext
  funext history
  rw [PFunConverter.DDC.simple_apply]
  rfl

/-! ### The identity case: the boundary move is invisible -/

section Transport

omit [DecidableEq U.Code] in
/-- Transporting a boundary-indexed letter along an equality of boundaries
acts on the payload only. -/
theorem cast_sigma_of_boundary_eq {left right : Boundary U I}
    (boundaries : left = right) (alphabet : U.Code → Type w) (other : I)
    (value : alphabet (left other)) :
    cast (congrArg (fun assignment : Boundary U I =>
        Σ index, alphabet (assignment index)) boundaries)
        (⟨other, value⟩ : Σ index, alphabet (left index)) =
      ⟨other, cast (congrArg alphabet (congrFun boundaries other)) value⟩ := by
  subst boundaries
  rfl

omit [DecidableEq U.Code] in
/-- **The identity fibre equivalence is the boundary transport.**  With
`equivalence = Equiv.refl`, `fibreEquiv` is exactly the cast along
`replace_boundary_self`: renaming nothing renames nothing. -/
theorem fibre_equiv_refl (alphabet : U.Code → Type w)
    (boundaries : boundary =
      replaceBoundary boundary interface (boundary interface))
    (value : Σ other, alphabet (boundary other)) :
    fibreEquiv interface boundary alphabet
        (rfl : boundary interface = boundary interface)
        (Equiv.refl (alphabet (boundary interface))) value =
      cast (congrArg (fun assignment : Boundary U I =>
        Σ index, alphabet (assignment index)) boundaries) value := by
  rcases value with ⟨other, value⟩
  rw [cast_sigma_of_boundary_eq boundaries]
  show (⟨other, fibreCongr interface boundary alphabet rfl
      (Equiv.refl (alphabet (boundary interface))) other value⟩ :
      Σ index, alphabet
        (replaceBoundary boundary interface (boundary interface) index)) = _
  by_cases same : other = interface
  · subst same
    rw [fibreCongr, dif_pos rfl]
    rfl
  · rw [fibreCongr, dif_neg same]
    rfl

/-- Two resources at propositionally equal boundaries are heterogeneously
equal as soon as one flattens to the *transport* relabelling of the other.
The two boundaries are variables here, so the transport is discharged by
`subst` and `DependentDDS.flatten_injective` — no ambient chart. -/
theorem DependentDDS.heq_of_flatten_relabel_cast
    {left right : Boundary U I} (boundaries : left = right)
    {leftSystem : DependentDDS U right} {rightSystem : DependentDDS U left}
    {queryTransport : Query U left ≃ Query U right}
    {answerTransport : FlatAnswer U left ≃ FlatAnswer U right}
    (queryCast : ∀ query, queryTransport query =
      cast (congrArg (fun assignment : Boundary U I =>
        Σ index, U.input (assignment index)) boundaries) query)
    (answerCast : ∀ answer, answerTransport answer =
      cast (congrArg (fun assignment : Boundary U I =>
        Σ index, U.output (assignment index)) boundaries) answer)
    (flattened : leftSystem.flatten =
      PFunDDS.DDS.relabel queryTransport answerTransport
        rightSystem.flatten) :
    HEq leftSystem rightSystem := by
  subst boundaries
  have queryRefl : queryTransport = Equiv.refl (Query U left) :=
    Equiv.ext queryCast
  have answerRefl : answerTransport = Equiv.refl (FlatAnswer U left) :=
    Equiv.ext answerCast
  rw [queryRefl, answerRefl, PFunDDS.DDS.relabel_refl] at flattened
  exact heq_of_eq (DependentDDS.flatten_injective flattened)

/-- **The identity converter is idle** (deterministic form): attaching
`ofFunctions id id` at an interface returns the resource itself.  The
equality is heterogeneous only because the boundary update
`Function.update boundary interface (boundary interface)` is the identity
propositionally rather than definitionally. -/
theorem DependentDDS.attach_ofFunctions_id_heq
    (system : DependentDDS U boundary) :
    HEq (system.attach interface
        (DeterministicConverter.ofFunctions
          (id : U.input (boundary interface) → U.input (boundary interface))
          (id : U.output (boundary interface) → U.output (boundary interface)))
        rfl) system :=
  DependentDDS.heq_of_flatten_relabel_cast
    (replace_boundary_self boundary interface).symm
    (fibre_equiv_refl interface boundary U.input
      (replace_boundary_self boundary interface).symm)
    (fibre_equiv_refl interface boundary U.output
      (replace_boundary_self boundary interface).symm)
    (DependentDDS.flatten_attach_ofMaps_eq_relabel interface boundary rfl
      (Equiv.refl (U.input (boundary interface)))
      (Equiv.refl (U.output (boundary interface))) system)

end Transport

end

end RandomSystems.CR18.TypedResource
