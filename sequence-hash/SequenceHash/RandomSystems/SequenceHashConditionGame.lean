import RandomSystems.HistoryConditionC
import SequenceHash.RandomSystems.OccupiedLinkProfile
import SequenceHash.RandomSystems.SequenceHashJoinAdaptive
import SequenceHash.RandomSystems.SequenceHashRepresentative

/-!
# History-aware condition-C presentation of the SequenceHash simulator

The executable simulator is a total state machine.  This module places its
flattened denotation in the canonical `historyEvaluator` form consumed by the
stateful condition-C framework.  The equations are exact equalities of PDS
laws, not merely transcript equivalences.

The construction-specific monitor and the final join/link accounting are
built below this representation boundary.  Keeping the boundary public makes
it impossible for that accounting to silently replace the executable machine
by a hand-written answer process.
-/

noncomputable section

open RandomSystems
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

universe u

variable {C B X Tag : Type u}

/-- Every transition of the executable simulator returns an answer. -/
theorem simulatorMachine_stepTotal [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X) :
    Machine.StepTotal (simulatorMachine grammar iv coins) := by
  intro state query
  exact simulator_step_isSome grammar iv coins state query

/-- The flattened simulator denotation accepts every nonempty public query
history. -/
theorem simulatorFlatDDS_total [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X) :
    ∀ history : List (Query C B X), history ≠ [] →
      history ∈ PFunDDS.dom
        ((simulatorMachine grammar iv coins).toDDS.flatten) := by
  intro history nonempty
  change history ≠ [] ∧
    ((simulatorMachine grammar iv coins).run history).isSome
  exact ⟨nonempty,
    Machine.run_isSome_of_stepTotal _
      (simulatorMachine_stepTotal grammar iv coins) history⟩

/-- The answer computed by the actual simulator on a complete nonempty public
query history.  No transition classification is duplicated here: the value
is read directly from `Machine.toDDS.flatten`. -/
def simulatorHistoryOutput [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) (nonempty : history ≠ []) :
    Reply C B X :=
  PFunDDS.output ((simulatorMachine grammar iv coins).toDDS.flatten)
    history (simulatorFlatDDS_total grammar iv coins history nonempty)

/-- A deterministic simulator fibre is exactly its canonical history
evaluator. -/
theorem simulator_flatten_eq_historyEvaluator [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X) :
    (simulatorMachine grammar iv coins).toDDS.flatten =
      PFunDDS.historyEvaluator
        (simulatorHistoryOutput grammar iv coins) := by
  exact PFunDDS.eq_historyEvaluator_of_total _
    (simulatorFlatDDS_total grammar iv coins)

/-! ## The join bit as an executor-derived history event -/

/-- Final simulator state after a public query history.  Totality supplies the
`Option.get` proof; the state itself is computed by the executable machine. -/
def simulatorRunState [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) : State C B X Tag :=
  ((simulatorMachine grammar iv coins).run history).get
    (Machine.run_isSome_of_stepTotal _
      (simulatorMachine_stepTotal grammar iv coins) history)

/-- Running the simulator really returns `simulatorRunState`. -/
theorem simulator_run_eq_some_runState [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) :
    (simulatorMachine grammar iv coins).run history =
      some (simulatorRunState grammar iv coins history) := by
  exact (Option.some_get
    (Machine.run_isSome_of_stepTotal _
      (simulatorMachine_stepTotal grammar iv coins) history)).symm

/-- A fired join remains fired while the executable simulator processes any
suffix.  The proof splits the actual public interface at every step and calls
the native primitive/evaluation preservation theorems. -/
theorem simulator_runFrom_join_monotone [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (history : List (Query C B X))
    (fired : state.join = true) :
    (((simulatorMachine grammar iv coins).runFrom state history).get
        (Machine.runFrom_isSome_of_stepTotal _
          (simulatorMachine_stepTotal grammar iv coins) state history)).join =
      true := by
  induction history generalizing state with
  | nil => simpa [Machine.runFrom]
  | cons query rest inductionHypothesis =>
      rcases query with ⟨interface, input⟩
      cases interface with
      | prim =>
          simpa [Machine.runFrom, simulatorMachine, simulatorStep] using
            inductionHypothesis
              (primitiveStep grammar iv coins state input).1
              (primitiveStep_join_monotone grammar iv coins state input fired)
      | eval =>
          simpa [Machine.runFrom, simulatorMachine, simulatorStep] using
            inductionHypothesis
              (evalStep coins state input).1
              (evalStep_join_monotone coins state input fired)

/-- The simulator's own graph-join event is prefix-monotone as a predicate on
public query histories. -/
theorem simulatorRunState_join_prefix [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    {left right : List (Query C B X)} (isPrefix : left <+: right)
    (fired : (simulatorRunState grammar iv coins left).join = true) :
    (simulatorRunState grammar iv coins right).join = true := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  have leftRun := simulator_run_eq_some_runState grammar iv coins left
  have suffixFired := simulator_runFrom_join_monotone grammar iv coins
    (simulatorRunState grammar iv coins left) suffix fired
  have runAppend :
      (simulatorMachine grammar iv coins).run (left ++ suffix) =
        (simulatorMachine grammar iv coins).runFrom
          (simulatorRunState grammar iv coins left) suffix := by
    have leftRunFrom :
        (simulatorMachine grammar iv coins).runFrom
            (simulatorMachine grammar iv coins).init left =
          some (simulatorRunState grammar iv coins left) := by
      simpa [Machine.run] using leftRun
    unfold Machine.run
    rw [Machine.runFrom_append, leftRunFrom]
    rfl
  have finalStateEq :
      simulatorRunState grammar iv coins (left ++ suffix) =
        ((simulatorMachine grammar iv coins).runFrom
          (simulatorRunState grammar iv coins left) suffix).get
            (Machine.runFrom_isSome_of_stepTotal _
              (simulatorMachine_stepTotal grammar iv coins)
              (simulatorRunState grammar iv coins left) suffix) := by
    apply Option.some.inj
    rw [← simulator_run_eq_some_runState grammar iv coins (left ++ suffix)]
    exact runAppend.trans (Option.some_get _).symm
  rw [finalStateEq]
  exact suffixFired

/-- The executor's currently visible graph-join flag, viewed as a proposition
on a seed and public query history.  Hidden construction paths are added by
the audit monitor later; keeping this name explicit prevents the visible flag
from being mistaken for the final bad event. -/
def SimulatorVisibleJoin [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) : Prop :=
  (simulatorRunState grammar iv coins history).join = true

instance instDecidableSimulatorVisibleJoin [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) :
    Decidable (SimulatorVisibleJoin grammar iv coins history) := by
  unfold SimulatorVisibleJoin
  infer_instance

/-! ## Hidden construction-path audit

The smart simulator does not install compression points traversed only by a
construction query.  They nevertheless belong to the proof's collision graph.
The following audit recomputes those paths from the simulator's complete
compression tape and combines them with the live words held by the executor.
An assignment is `(semantic word, endpoint)`; reaching one endpoint by two
different words is precisely a graph join. -/

/-- Semantic word/end-point assignments along one MD path, including the
full nonempty word. -/
def mdPathAssignments (compression : Compression C B) :
    C → List B → List B → List (List B × C)
  | _state, [], _pathPrefix => []
  | state, block :: rest, pathPrefix =>
      let next := compression state block
      let word := pathPrefix ++ [block]
      (word, next) :: mdPathAssignments compression next rest word

@[simp]
theorem mdPathAssignments_nil (compression : Compression C B)
    (state : C) (pathPrefix : List B) :
    mdPathAssignments compression state [] pathPrefix = [] := by
  rfl

@[simp]
theorem mdPathAssignments_cons (compression : Compression C B)
    (state : C) (block : B) (rest pathPrefix : List B) :
    mdPathAssignments compression state (block :: rest) pathPrefix =
      let next := compression state block
      let word := pathPrefix ++ [block]
      (word, next) :: mdPathAssignments compression next rest word := by
  rfl

/-- Critical assignments created by a fresh construction input.  Every inner
endpoint is live; the terminal outer output is deliberately excluded. -/
def constructionAssignments (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) : List (List B × C) :=
  let inner := mdPathAssignments compression iv (grammar.innerWord input) []
  let embedded := mdIterate compression iv (grammar.innerWord input)
  let outer := mdPathAssignments compression iv
    (grammar.outerWord (grammar.tagOf input) embedded) []
  inner ++ outer.dropLast

/-- Hidden critical assignments contributed by construction-interface calls
in a public query history.  Repeated calls may duplicate identical pairs; the
join predicate compares semantic words, so those duplicates are harmless. -/
def hiddenAssignments (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) :
    List (Query C B X) → List (List B × C)
  | [] => []
  | ⟨.prim, _point⟩ :: rest =>
      hiddenAssignments grammar iv compression rest
  | ⟨.eval, input⟩ :: rest =>
      constructionAssignments grammar iv compression input ++
        hiddenAssignments grammar iv compression rest

theorem hiddenAssignments_append (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (left right : List (Query C B X)) :
    hiddenAssignments grammar iv compression (left ++ right) =
      hiddenAssignments grammar iv compression left ++
        hiddenAssignments grammar iv compression right := by
  induction left with
  | nil => rfl
  | cons query rest inductionHypothesis =>
      rcases query with ⟨interface, input⟩
      cases interface <;>
        simp [hiddenAssignments, inductionHypothesis, List.append_assoc]

/-- Live assignments currently materialized by the executable simulator. -/
def visibleAssignments [Fintype C]
    (state : State C B X Tag) : List (List B × C) :=
  (Finset.univ.toList.filterMap fun value =>
    (state.word value).map fun word => (word, value))

@[simp]
theorem mem_visibleAssignments_iff [Fintype C] [DecidableEq C]
    [DecidableEq B] (state : State C B X Tag) (word : List B) (value : C) :
    (word, value) ∈ visibleAssignments state ↔
      state.word value = some word := by
  simp [visibleAssignments]

/-- Complete semantic assignment list audited at a public history. -/
def auditedAssignments [Fintype C] [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) : List (List B × C) :=
  visibleAssignments (simulatorRunState grammar iv coins history) ++
    hiddenAssignments grammar iv (fun state block => coins.2 (state, block))
      history

/-- Two different semantic paths reach the same chaining value. -/
def AssignmentCollision [DecidableEq C] [DecidableEq B]
    (assignments : List (List B × C)) : Prop :=
  ∃ left ∈ assignments, ∃ right ∈ assignments,
    left.1 ≠ right.1 ∧ left.2 = right.2

/-- A loose root named at the primitive interface is in fact a hidden or live
construction state. -/
def AssignmentHitsLoose [DecidableEq C]
    (assignments : List (List B × C)) (loose : Finset C) : Prop :=
  ∃ assignment ∈ assignments, assignment.2 ∈ loose

/-- Full graph-join audit currently needed by the proof.  It includes the
executor's own flag, hidden/live semantic collisions (including a nonempty
word returning to the IV via the visible `([], IV)` assignment), and loose
root guesses. -/
def SimulatorJoinAudit [Fintype C] [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) : Prop :=
  SimulatorVisibleJoin grammar iv coins history ∨
    AssignmentCollision (auditedAssignments grammar iv coins history) ∨
    AssignmentHitsLoose (auditedAssignments grammar iv coins history)
      (simulatorRunState grammar iv coins history).loose

instance instDecidableAssignmentCollision [DecidableEq C] [DecidableEq B]
    (assignments : List (List B × C)) :
    Decidable (AssignmentCollision assignments) := by
  unfold AssignmentCollision
  infer_instance

instance instDecidableAssignmentHitsLoose [DecidableEq C]
    (assignments : List (List B × C)) (loose : Finset C) :
    Decidable (AssignmentHitsLoose assignments loose) := by
  unfold AssignmentHitsLoose
  infer_instance

instance instDecidableSimulatorJoinAudit [Fintype C] [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) :
    Decidable (SimulatorJoinAudit grammar iv coins history) := by
  unfold SimulatorJoinAudit
  infer_instance

/-! ## Prefix monotonicity of the complete audit

The framework already proves once and for all that any prefix-monotone
history predicate yields a monotone MBO.  The only construction-specific
obligation here is therefore to show that the executable simulator never
forgets a live word, a loose root, or a fired join. -/

/-- The pieces of simulator state used by the audit only grow. -/
structure StateExtends (before after : State C B X Tag) : Prop where
  word : ∀ value path,
    before.word value = some path → after.word value = some path
  loose : ∀ value, value ∈ before.loose → value ∈ after.loose
  join : before.join = true → after.join = true

theorem stateExtends_refl (state : State C B X Tag) :
    StateExtends state state := by
  exact ⟨fun _ _ h => h, fun _ h => h, fun h => h⟩

theorem StateExtends.trans {first second third : State C B X Tag}
    (left : StateExtends first second) (right : StateExtends second third) :
    StateExtends first third := by
  exact ⟨fun value path h => right.word value path (left.word value path h),
    fun value h => right.loose value (left.loose value h),
    fun h => right.join (left.join h)⟩

theorem stateExtends_installTable [DecidableEq C] [DecidableEq B]
    (state : State C B X Tag) (query : C × B) (answer : C) :
    StateExtends state (installTable state query answer) := by
  exact ⟨by simp [installTable], by simp [installTable], by simp [installTable]⟩

theorem stateExtends_recordEval [DecidableEq X]
    (state : State C B X Tag) (input : X) :
    StateExtends state (recordEval state input) := by
  exact ⟨by simp [recordEval], by simp [recordEval], by simp [recordEval]⟩

theorem stateExtends_recordLoose [DecidableEq C]
    (state : State C B X Tag) (root : C) :
    StateExtends state (recordLoose state root) := by
  refine ⟨by simp [recordLoose], ?_, by simp [recordLoose]⟩
  intro value member
  exact Finset.mem_insert_of_mem member

theorem stateExtends_recordPending [DecidableEq C] [DecidableEq Tag]
    (state : State C B X Tag) (tag : Tag) (embedded answer : C) :
    StateExtends state (recordPending state tag embedded answer) := by
  exact ⟨by simp [recordPending], by simp [recordPending],
    by simp [recordPending]⟩

theorem stateExtends_markJoin (state : State C B X Tag) :
    StateExtends state (markJoin state) := by
  exact ⟨by simp [markJoin], by simp [markJoin], by simp [markJoin]⟩

theorem stateExtends_installLive_of_word_none [DecidableEq C]
    (state : State C B X Tag) (value : C) (path : List B)
    (completed : Option X) (fresh : state.word value = none) :
    StateExtends state (installLive state value path completed) := by
  refine ⟨?_, by simp [installLive], by simp [installLive]⟩
  intro oldValue oldPath present
  by_cases equal : oldValue = value
  · subst oldValue
    rw [fresh] at present
    simp at present
  · simpa [installLive, equal] using present

/-- All four executor-generated propagation branches extend the audit state. -/
theorem stateExtends_propagate [DecidableEq C]
    (state : State C B X Tag) (iv value : C) (path : List B)
    (completed : Option X) :
    StateExtends state (propagate state iv value path completed) := by
  apply propagate_cases state iv value path completed
      (P := fun next => StateExtends state next)
  · intro _initial
    exact stateExtends_markJoin state
  · intro _previous _notInitial _live
    exact stateExtends_markJoin state
  · intro _notInitial _notLive _loose
    exact stateExtends_markJoin state
  · intro _notInitial notLive _notLoose
    exact stateExtends_installLive_of_word_none state value path completed notLive

theorem stateExtends_ordinaryPrimitiveStep [DecidableEq C] [DecidableEq B]
    (coins : Coins C B X) (state : State C B X Tag) (query : C × B) :
    StateExtends state (ordinaryPrimitiveStep coins state query).1 := by
  exact stateExtends_installTable state query (coins.2 query)

theorem stateExtends_loosePrimitiveStep [DecidableEq C] [DecidableEq B]
    (coins : Coins C B X) (state : State C B X Tag) (query : C × B) :
    StateExtends state (loosePrimitiveStep coins state query).1 := by
  exact (stateExtends_installTable state query (coins.2 query)).trans
    (stateExtends_recordLoose
      (installTable state query (coins.2 query)) query.1)

theorem stateExtends_livePrimitiveStep [DecidableEq C] [DecidableEq B]
    (iv : C) (coins : Coins C B X) (state : State C B X Tag)
    (query : C × B) (path : List B) (completed : Option X) :
    StateExtends state
      (livePrimitiveStep iv coins state query path completed).1 := by
  exact (stateExtends_installTable state query (coins.2 query)).trans
    (stateExtends_propagate
      (installTable state query (coins.2 query)) iv (coins.2 query)
        path completed)

theorem stateExtends_pendingPrimitiveStep [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (coins : Coins C B X) (state : State C B X Tag) (query : C × B)
    (tag : Tag) (embedded : C) :
    StateExtends state
      (pendingPrimitiveStep coins state query tag embedded).1 := by
  exact (stateExtends_installTable state query (coins.2 query)).trans
    (stateExtends_recordPending
      (installTable state query (coins.2 query)) tag embedded (coins.2 query))

theorem stateExtends_linkedPrimitiveStep [DecidableEq C] [DecidableEq B]
    (coins : Coins C B X) (state : State C B X Tag) (query : C × B)
    (input : X) :
    StateExtends state (linkedPrimitiveStep coins state query input).1 := by
  exact stateExtends_installTable state query (coins.1 input)

/-- Every primitive observation leaf generated from the executable parser
tree preserves all audit witnesses. -/
theorem stateExtends_primitiveStep [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : C × B) :
    StateExtends state (primitiveStep grammar iv coins state query).1 := by
  apply primitiveStep_cases grammar iv coins state query
      (P := fun result => StateExtends state result.1)
  · intro _answer _repeated
    exact stateExtends_refl state
  · intro _notRepeated _loose
    exact stateExtends_loosePrimitiveStep coins state query
  · intro path _notRepeated _live _parse
    exact stateExtends_livePrimitiveStep iv coins state query
      (path ++ [query.2]) none
  · intro path input _notRepeated _live _parse
    exact stateExtends_livePrimitiveStep iv coins state query
      (path ++ [query.2]) (some input)
  · intro path _notRepeated _live _parse
    exact stateExtends_livePrimitiveStep iv coins state query
      (path ++ [query.2]) none
  · intro _path tag embedded _notRepeated _live _parse _unknown
    exact stateExtends_pendingPrimitiveStep coins state query tag embedded
  · intro _path tag embedded _input _notRepeated _live _parse _known _wrong
    exact stateExtends_pendingPrimitiveStep coins state query tag embedded
  · intro _path _tag _embedded input _notRepeated _live _parse _known _right
    exact stateExtends_linkedPrimitiveStep coins state query input
  · intro _path _notRepeated _live _parse
    exact stateExtends_ordinaryPrimitiveStep coins state query

theorem stateExtends_evalStep [DecidableEq X]
    (coins : Coins C B X) (state : State C B X Tag) (input : X) :
    StateExtends state (evalStep coins state input).1 := by
  apply evalStep_cases coins state input
      (P := fun result => StateExtends state result.1)
  · intro _repeated
    exact stateExtends_refl state
  · intro _fresh
    exact stateExtends_recordEval state input

/-- The public interface split is also generated from the executable query
type, so both interfaces are covered without a default branch. -/
theorem stateExtends_simulatorStep [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : Query C B X) :
    StateExtends state
      ((simulatorStep grammar iv coins state query).get
        (simulator_step_isSome grammar iv coins state query)).1 := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | prim =>
      simpa only [simulatorStep, Option.get_some] using
        stateExtends_primitiveStep grammar iv coins state input
  | eval =>
      simpa only [simulatorStep, Option.get_some] using
        stateExtends_evalStep coins state input

theorem stateExtends_simulatorRunFrom [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (history : List (Query C B X)) :
    StateExtends state
      (((simulatorMachine grammar iv coins).runFrom state history).get
        (Machine.runFrom_isSome_of_stepTotal _
          (simulatorMachine_stepTotal grammar iv coins) state history)) := by
  induction history generalizing state with
  | nil =>
      simpa [Machine.runFrom] using stateExtends_refl state
  | cons query rest inductionHypothesis =>
      rcases query with ⟨interface, input⟩
      cases interface with
      | prim =>
          simpa [Machine.runFrom, simulatorMachine, simulatorStep] using
            (stateExtends_primitiveStep grammar iv coins state input).trans
              (inductionHypothesis
                (primitiveStep grammar iv coins state input).1)
      | eval =>
          simpa [Machine.runFrom, simulatorMachine, simulatorStep] using
            (stateExtends_evalStep coins state input).trans
              (inductionHypothesis (evalStep coins state input).1)

/-- The audit-relevant state at a public prefix extends to every longer public
history. -/
theorem stateExtends_simulatorRunState_prefix [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    {left right : List (Query C B X)} (isPrefix : left <+: right) :
    StateExtends (simulatorRunState grammar iv coins left)
      (simulatorRunState grammar iv coins right) := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  have leftRun := simulator_run_eq_some_runState grammar iv coins left
  have suffixExtends := stateExtends_simulatorRunFrom grammar iv coins
    (simulatorRunState grammar iv coins left) suffix
  have runAppend :
      (simulatorMachine grammar iv coins).run (left ++ suffix) =
        (simulatorMachine grammar iv coins).runFrom
          (simulatorRunState grammar iv coins left) suffix := by
    have leftRunFrom :
        (simulatorMachine grammar iv coins).runFrom
            (simulatorMachine grammar iv coins).init left =
          some (simulatorRunState grammar iv coins left) := by
      simpa [Machine.run] using leftRun
    unfold Machine.run
    rw [Machine.runFrom_append, leftRunFrom]
    rfl
  have finalStateEq :
      simulatorRunState grammar iv coins (left ++ suffix) =
        ((simulatorMachine grammar iv coins).runFrom
          (simulatorRunState grammar iv coins left) suffix).get
            (Machine.runFrom_isSome_of_stepTotal _
              (simulatorMachine_stepTotal grammar iv coins)
              (simulatorRunState grammar iv coins left) suffix) := by
    apply Option.some.inj
    rw [← simulator_run_eq_some_runState grammar iv coins (left ++ suffix)]
    exact runAppend.trans (Option.some_get _).symm
  rw [finalStateEq]
  exact suffixExtends

theorem mem_auditedAssignments_of_prefix [Fintype C] [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    {left right : List (Query C B X)} (isPrefix : left <+: right)
    {assignment : List B × C}
    (member : assignment ∈ auditedAssignments grammar iv coins left) :
    assignment ∈ auditedAssignments grammar iv coins right := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  have stateExtends := stateExtends_simulatorRunState_prefix grammar iv coins
    (List.prefix_append left suffix)
  rcases List.mem_append.mp member with visible | hidden
  · apply List.mem_append_left
    rw [mem_visibleAssignments_iff] at visible ⊢
    exact stateExtends.word assignment.2 assignment.1 visible
  · apply List.mem_append_right
    rw [hiddenAssignments_append]
    exact List.mem_append_left _ hidden

/-- The complete join/link audit is the sole SequenceHash-specific MBO
obligation.  The generic history-condition framework turns this theorem into
`MonotoneMBO` wherever the final proof instantiates its game. -/
theorem simulatorJoinAudit_prefix [Fintype C] [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    {left right : List (Query C B X)} (isPrefix : left <+: right)
    (fired : SimulatorJoinAudit grammar iv coins left) :
    SimulatorJoinAudit grammar iv coins right := by
  rcases fired with visible | collisionOrLoose
  · exact Or.inl
      (simulatorRunState_join_prefix grammar iv coins isPrefix visible)
  · rcases collisionOrLoose with collision | loose
    · right
      left
      rcases collision with ⟨first, firstMember, second, secondMember,
        different, equal⟩
      exact ⟨first,
        mem_auditedAssignments_of_prefix grammar iv coins isPrefix firstMember,
        second,
        mem_auditedAssignments_of_prefix grammar iv coins isPrefix secondMember,
        different, equal⟩
    · right
      right
      rcases loose with ⟨assignment, assignmentMember, looseMember⟩
      refine ⟨assignment,
        mem_auditedAssignments_of_prefix grammar iv coins isPrefix
          assignmentMember, ?_⟩
      exact (stateExtends_simulatorRunState_prefix grammar iv coins isPrefix).loose
        assignment.2 looseMember

/-- The ideal PDS is exactly the uniform seed law of the executable history
answer function. -/
theorem ideal_p_eq_historyEvaluator [Fintype C] [Fintype B] [Fintype X]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    (idealP grammar iv).val =
      Dist.fTransform
        (fun coins : Coins C B X =>
          PFunDDS.historyEvaluator
            (simulatorHistoryOutput grammar iv coins))
        (Dist.uniform (Coins C B X)) := by
  change
    Dist.fTransform DependentDDS.flatten
        (Dist.fTransform
          (fun coins : Coins C B X =>
            (simulatorMachine grammar iv coins).toDDS)
          (Dist.uniform (Coins C B X))) = _
  rw [Dist.fTransform_comp]
  apply Finsupp.mapDomain_congr
  intro coins _support
  exact simulator_flatten_eq_historyEvaluator grammar iv coins

/-- The correlated representative of the real system has the same exact
history-evaluator presentation; only its seed law differs from the ideal one. -/
theorem correlated_p_eq_historyEvaluator [Fintype C] [Fintype B]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    (correlatedP grammar iv).val =
      Dist.fTransform
        (fun compression : Compression C B =>
          PFunDDS.historyEvaluator
            (simulatorHistoryOutput grammar iv
              (correlatedCoins grammar iv compression)))
        (Dist.uniform (Compression C B)) := by
  change
    Dist.fTransform DependentDDS.flatten
        (Dist.fTransform
          (fun compression : Compression C B =>
            (simulatorMachine grammar iv
              (correlatedCoins grammar iv compression)).toDDS)
          (Dist.uniform (Compression C B))) = _
  rw [Dist.fTransform_comp]
  apply Finsupp.mapDomain_congr
  intro compression _support
  exact simulator_flatten_eq_historyEvaluator grammar iv
    (correlatedCoins grammar iv compression)

/-- The ordinary real construction inherits the history presentation through
the already-proved correlated-simulator bisimulation. -/
theorem real_p_eq_historyEvaluator [Fintype C] [Fintype B]
    [Nonempty C] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    (realP grammar iv).val =
      Dist.fTransform
        (fun compression : Compression C B =>
          PFunDDS.historyEvaluator
            (simulatorHistoryOutput grammar iv
              (correlatedCoins grammar iv compression)))
        (Dist.uniform (Compression C B)) := by
  rw [real_p_eq_correlated grammar iv]
  exact correlated_p_eq_historyEvaluator grammar iv

end MDSimulator
end RandomSystemsModel
end SequenceHash
