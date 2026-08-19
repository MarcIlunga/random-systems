import RandomSystems.Jost.LawCoupling
import SequenceHash.RandomSystems.SequenceHashGraphInvariant

/-!
# A common-machine representative for SequenceHash

The real and ideal systems can be represented by the same stateful simulator.
Only the law of its two complete tapes changes.  In the real representative
the construction tape is the two-pass MD evaluation of the compression tape;
in the ideal representative the two tapes are independent and uniform.

The deterministic equality with the ordinary real construction is proved by
a bisimulation.  Its primitive step is discharged by `primitiveStep_cases`,
so Lean generates one obligation for every native table/parser/link leaf.
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

/-- Correlate the construction tape with the compression tape by evaluating
the real two-pass MD construction. -/
def correlatedCoins (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) : Coins C B X :=
  (sequenceEval grammar iv compression,
    fun point => compression point.1 point.2)

/-- Every compression-table entry installed by the simulator agrees with the
underlying complete compression function. -/
def TableAgrees (compression : Compression C B)
    (state : State C B X Tag) : Prop :=
  ∀ point answer, state.table point = some answer →
    compression point.1 point.2 = answer

/-- The invariant relating the ordinary real machine to the simulator driven
by its correlated tapes. -/
def RepresentativeInvariant (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (state : State C B X Tag) : Prop :=
  GraphInvariant grammar state iv ∧ TableAgrees compression state

theorem initial_state_table_agrees [DecidableEq C]
    (compression : Compression C B) (iv : C) :
    TableAgrees compression (initialState (B := B) (X := X) (Tag := Tag) iv) := by
  intro point answer lookup
  simp [initialState] at lookup

theorem initial_state_representative_invariant [DecidableEq C]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) :
    RepresentativeInvariant grammar iv compression (initialState iv) :=
  ⟨initialState_graphInvariant grammar iv,
    initial_state_table_agrees compression iv⟩

/-- A certified partial-table path evaluates to the same endpoint under the
complete compression function. -/
theorem md_iterate_eq_of_follow_eq_some
    {compression : Compression C B} {table : C × B → Option C}
    (agrees : ∀ point answer, table point = some answer →
      compression point.1 point.2 = answer)
    (start : C) (blocks : List B) (endpoint : C)
    (path : follow table start blocks = some endpoint) :
    mdIterate compression start blocks = endpoint := by
  induction blocks generalizing start endpoint with
  | nil =>
      simpa using Option.some.inj path
  | cons block rest inductionHypothesis =>
      simp only [follow_cons] at path
      cases lookup : table (start, block) with
      | none => simp [lookup] at path
      | some next =>
          have tail : follow table next rest = some endpoint := by
            simpa [lookup] using path
          change mdIterate compression (compression start block) rest = endpoint
          rw [agrees (start, block) next lookup]
          exact inductionHypothesis next endpoint tail

theorem table_agrees_install_table [DecidableEq C] [DecidableEq B]
    {compression : Compression C B} {state : State C B X Tag}
    {query : C × B} {answer : C}
    (agrees : TableAgrees compression state)
    (answer_eq : compression query.1 query.2 = answer) :
    TableAgrees compression (installTable state query answer) := by
  intro point claimed lookup
  by_cases hit : point = query
  · subst point
    have claimed_eq : answer = claimed := by
      simpa [installTable] using lookup
    rw [← claimed_eq]
    exact answer_eq
  · have old : state.table point = some claimed := by
      simpa [installTable, hit] using lookup
    exact agrees point claimed old

theorem table_agrees_record_eval [DecidableEq X]
    {compression : Compression C B} {state : State C B X Tag} {input : X}
    (agrees : TableAgrees compression state) :
    TableAgrees compression (recordEval state input) := by
  simpa [TableAgrees, recordEval] using agrees

theorem table_agrees_record_loose [DecidableEq C]
    {compression : Compression C B} {state : State C B X Tag} {root : C}
    (agrees : TableAgrees compression state) :
    TableAgrees compression (recordLoose state root) := by
  simpa [TableAgrees, recordLoose] using agrees

theorem table_agrees_record_pending [DecidableEq C] [DecidableEq Tag]
    {compression : Compression C B} {state : State C B X Tag}
    {tag : Tag} {embedded answer : C}
    (agrees : TableAgrees compression state) :
    TableAgrees compression (recordPending state tag embedded answer) := by
  simpa [TableAgrees, recordPending] using agrees

theorem table_agrees_install_live [DecidableEq C]
    {compression : Compression C B} {state : State C B X Tag}
    {value : C} {word : List B} {completed : Option X}
    (agrees : TableAgrees compression state) :
    TableAgrees compression (installLive state value word completed) := by
  simpa [TableAgrees, installLive] using agrees

theorem table_agrees_mark_join
    {compression : Compression C B} {state : State C B X Tag}
    (agrees : TableAgrees compression state) :
    TableAgrees compression (markJoin state) := by
  simpa [TableAgrees, markJoin] using agrees

/-- Destination propagation changes graph indices but never the compression
table.  The four source branches remain explicit proof obligations. -/
theorem table_agrees_propagate [DecidableEq C]
    {compression : Compression C B} (state : State C B X Tag)
    (iv value : C) (word : List B) (completed : Option X)
    (agrees : TableAgrees compression state) :
    TableAgrees compression (propagate state iv value word completed) := by
  apply propagate_cases state iv value word completed
      (P := fun next => TableAgrees compression next)
  · intro _initial
    exact table_agrees_mark_join agrees
  · intro _previous _notInitial _word
    exact table_agrees_mark_join agrees
  · intro _notInitial _word _loose
    exact table_agrees_mark_join agrees
  · intro _notInitial _word _fresh
    exact table_agrees_install_live agrees

/-- On a linked terminal leaf, the correlated construction tape is exactly
the complete compression function's answer at the queried terminal point. -/
theorem correlated_coins_linked_answer_eq
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (state : State C B X Tag)
    (query : C × B) (path : List B) (tag : Tag) (embedded : C)
    (input : X)
    (invariant : RepresentativeInvariant grammar iv compression state)
    (source : state.word query.1 = some path)
    (parse : grammar.classifyWord (path ++ [query.2]) =
      .outerComplete tag embedded)
    (inner : state.inner embedded = some input)
    (tag_eq : grammar.tagOf input = tag) :
    (correlatedCoins grammar iv compression).1 input =
      compression query.1 query.2 := by
  have source_path : follow state.table iv path = some query.1 :=
    invariant.1.1 query.1 path source
  have source_value : mdIterate compression iv path = query.1 :=
    md_iterate_eq_of_follow_eq_some invariant.2 iv path query.1 source_path
  have inner_path := innerEndpoint_certified invariant.1 inner
  have inner_value :
      mdIterate compression iv (grammar.innerWord input) = embedded :=
    md_iterate_eq_of_follow_eq_some invariant.2 iv
      (grammar.innerWord input) embedded inner_path.2
  have outer_word :
      path ++ [query.2] =
        grammar.outerWord (grammar.tagOf input) embedded :=
    outerLinked_word_eq parse tag_eq
  simp only [correlatedCoins, sequenceEval]
  rw [inner_value, ← outer_word, mdIterate_append, source_value]
  rfl

/-- Every native primitive leaf of the correlated simulator returns the real
compression answer. -/
theorem primitive_step_correlated_answer_eq [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (state : State C B X Tag)
    (query : C × B)
    (invariant : RepresentativeInvariant grammar iv compression state) :
    (primitiveStep grammar iv (correlatedCoins grammar iv compression)
      state query).2 = compression query.1 query.2 := by
  -- Deliberately unfold the executor here.  Every `split` below is generated
  -- from a live `match`/`if` in `primitiveStep`; there is no intermediary case
  -- datatype or manually curated premise list in this correctness receipt.
  unfold primitiveStep
  split
  next answer tableLookup =>
    exact (invariant.2 query answer tableLookup).symm
  next _tableLookup =>
    split
    next _rootLookup => rfl
    next path rootLookup =>
      dsimp only
      split
      next _parse => rfl
      next _input _parse => rfl
      next _parse => rfl
      next tag embedded parse =>
        split
        next _innerLookup => rfl
        next input innerLookup =>
          split
          next tagEquality =>
            exact correlated_coins_linked_answer_eq grammar iv compression
              state query path tag embedded input invariant rootLookup parse
                innerLookup tagEquality
          next _tagInequality => rfl
      next _parse => rfl

/-- Every native primitive leaf also preserves agreement of the installed
table with the complete compression function. -/
theorem primitive_step_table_agrees [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (state : State C B X Tag)
    (query : C × B)
    (invariant : RepresentativeInvariant grammar iv compression state) :
    TableAgrees compression
      (primitiveStep grammar iv (correlatedCoins grammar iv compression)
        state query).1 := by
  let coins := correlatedCoins grammar iv compression
  have tape_eq : compression query.1 query.2 = coins.2 query := by
    rfl
  apply primitiveStep_cases grammar iv coins state query
      (P := fun result => TableAgrees compression result.1)
  · intro answer _lookup
    exact invariant.2
  · intro _table _word
    exact table_agrees_record_loose
      (table_agrees_install_table invariant.2 tape_eq)
  · intro path _table _word _parse
    exact table_agrees_propagate _ _ _ _ _
      (table_agrees_install_table invariant.2 tape_eq)
  · intro path input _table _word _parse
    exact table_agrees_propagate _ _ _ _ _
      (table_agrees_install_table invariant.2 tape_eq)
  · intro path _table _word _parse
    exact table_agrees_propagate _ _ _ _ _
      (table_agrees_install_table invariant.2 tape_eq)
  · intro path tag embedded _table _word _parse _inner
    exact table_agrees_record_pending
      (table_agrees_install_table invariant.2 tape_eq)
  · intro path tag embedded input _table _word _parse _inner _tag
    exact table_agrees_record_pending
      (table_agrees_install_table invariant.2 tape_eq)
  · intro path tag embedded input _table source parse inner tag_eq
    exact table_agrees_install_table invariant.2
      (correlated_coins_linked_answer_eq grammar iv compression state query
        path tag embedded input invariant source parse inner tag_eq).symm
  · intro path _table _word _parse
    exact table_agrees_install_table invariant.2 tape_eq

/-- One correlated simulator step has the same visible answer as the ordinary
real machine and preserves the representative invariant. -/
theorem simulator_step_correlated [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (state : State C B X Tag)
    (query : Query C B X)
    (invariant : RepresentativeInvariant grammar iv compression state) :
    ((simulatorMachine grammar iv
        (correlatedCoins grammar iv compression)).step state query).map Prod.snd =
        ((realMachine (sequenceEval grammar iv) compression).step () query).map
          Prod.snd ∧
      ∀ next_real next_simulator,
        (realMachine (sequenceEval grammar iv) compression).step () query =
          some next_real →
        (simulatorMachine grammar iv
          (correlatedCoins grammar iv compression)).step state query =
          some next_simulator →
        RepresentativeInvariant grammar iv compression next_simulator.1 := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | eval =>
      constructor
      · simp only [simulatorMachine, simulatorStep, realMachine,
          Option.map_some]
        apply congrArg some
        simp only [evalStep]
        split <;> rfl
      · intro next_real next_simulator _real_step simulator_step
        simp only [simulatorMachine, simulatorStep, Option.some.injEq] at simulator_step
        have next_eq : (evalStep (correlatedCoins grammar iv compression)
            state input).1 = next_simulator.1 := by
          exact congrArg (fun result => result.1) simulator_step
        rw [← next_eq]
        exact ⟨evalStep_graphInvariant grammar iv _ state input invariant.1,
          by
            apply evalStep_cases (correlatedCoins grammar iv compression)
              state input
              (P := fun result => TableAgrees compression result.1)
            · intro _seen
              exact invariant.2
            · intro _fresh
              exact table_agrees_record_eval invariant.2⟩
  | prim =>
      constructor
      · simp only [simulatorMachine, simulatorStep, realMachine,
          Option.map_some]
        exact congrArg some
          (primitive_step_correlated_answer_eq grammar iv compression state
            input invariant)
      · intro next_real next_simulator _real_step simulator_step
        simp only [simulatorMachine, simulatorStep, Option.some.injEq] at simulator_step
        have next_eq :
            (primitiveStep grammar iv
              (correlatedCoins grammar iv compression) state input).1 =
              next_simulator.1 := by
          exact congrArg (fun result => result.1) simulator_step
        rw [← next_eq]
        exact ⟨primitiveStep_graphInvariant grammar iv _ state input invariant.1,
          primitive_step_table_agrees grammar iv compression state input
            invariant⟩

/-- Fibrewise equality: the correlated simulator denotes exactly the real
SequenceHash-plus-compression resource. -/
theorem real_machine_to_dds_eq_correlated_simulator [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) :
    (realMachine (sequenceEval grammar iv) compression).toDDS =
      (simulatorMachine grammar iv
        (correlatedCoins grammar iv compression)).toDDS := by
  refine Machine.toDDS_eq_of_bisim
    (fun (_real : Unit) state =>
      RepresentativeInvariant grammar iv compression state)
    (initial_state_representative_invariant grammar iv compression) ?_
  intro real_state state invariant query
  rcases real_state with ⟨⟩
  obtain ⟨answers, successors⟩ :=
    simulator_step_correlated grammar iv compression state query invariant
  exact ⟨answers.symm, successors⟩

/-- The real law has a representative that samples one uniform compression
function and then runs the common simulator on its correlated tapes. -/
noncomputable def correlatedDependentP
    [Fintype C] [Fintype B] [Nonempty C]
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    DependentPDS.Prob
      (SignatureUniverse.ofInterfaces (Input C B X) (Output C))
      (Boundary.ofInterfaces (Input C B X) (Output C)) :=
  Machine.lawOf
    (fun compression => simulatorMachine grammar iv
      (correlatedCoins grammar iv compression))
    (Dist.uniform (Compression C B)) Dist.uniform_isProbDist

theorem real_dependent_p_eq_correlated [Fintype C] [Fintype B] [Nonempty C]
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    realDependentP grammar iv = correlatedDependentP grammar iv := by
  apply Machine.lawOf_congr Dist.uniform_isProbDist
  intro compression _support
  exact real_machine_to_dds_eq_correlated_simulator grammar iv compression

/-- Flattened fixed-alphabet version of the correlated real representative. -/
noncomputable def correlatedP
    [Fintype C] [Fintype B] [Nonempty C]
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    PFunPDS.Prob (Query C B X) (Reply C B X) :=
  (correlatedDependentP grammar iv).flatten

theorem real_p_eq_correlated [Fintype C] [Fintype B] [Nonempty C]
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    realP grammar iv = correlatedP grammar iv := by
  rw [realP, correlatedP, real_dependent_p_eq_correlated]

end MDSimulator
end RandomSystemsModel
end SequenceHash
