import RandomSystems.CoordinateSwap
import SequenceHash.RandomSystems.SequenceHashConditionGame

/-!
# Finite terminal traces for the SequenceHash simulator

The smart-simulator proof exchanges one ideal-oracle coordinate with the
terminal compression coordinate of each activated construction input.  This
file records those coordinates without storing the simulator's infinite
function-valued state.  Every list below is finite and is computed from the
same executable compression tape used by the simulator.
-/

noncomputable section

namespace SequenceHash
namespace RandomSystemsModel
namespace MDSimulator

open RandomSystems
open RandomSystems.CR18
open RandomSystems.CR18.TypedResource

universe u

variable {C B X Tag : Type u}

/-! ## Compression input traces -/

/-- Compression-table points visited by an MD word, in execution order. -/
def mdInputTrace (compression : Compression C B) :
    C → List B → List (C × B)
  | _state, [] => []
  | state, block :: rest =>
      (state, block) :: mdInputTrace compression (compression state block) rest

@[simp]
theorem mdInputTrace_nil (compression : Compression C B) (state : C) :
    mdInputTrace compression state [] = [] := by
  rfl

@[simp]
theorem mdInputTrace_cons (compression : Compression C B) (state : C)
    (block : B) (rest : List B) :
    mdInputTrace compression state (block :: rest) =
      (state, block) ::
        mdInputTrace compression (compression state block) rest := by
  rfl

@[simp]
theorem length_mdInputTrace (compression : Compression C B) (state : C)
    (blocks : List B) :
    (mdInputTrace compression state blocks).length = blocks.length := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      simp [mdInputTrace, inductionHypothesis]

/-- Agreement on the points selected by one execution preserves both its
answer and the complete selected-point trace. -/
theorem mdInputTrace_eq_of_eq_on_trace
    (left right : Compression C B) (state : C) (blocks : List B)
    (agree : ∀ point ∈ mdInputTrace left state blocks,
      right point.1 point.2 = left point.1 point.2) :
    mdInputTrace right state blocks = mdInputTrace left state blocks ∧
      mdIterate right state blocks = mdIterate left state blocks := by
  induction blocks generalizing state with
  | nil => exact ⟨rfl, rfl⟩
  | cons block rest inductionHypothesis =>
      have headAgree :
          right state block = left state block :=
        agree (state, block) (by simp [mdInputTrace])
      have tailAgree : ∀ point ∈
          mdInputTrace left (left state block) rest,
          right point.1 point.2 = left point.1 point.2 := by
        intro point member
        exact agree point (by simp [mdInputTrace, member])
      obtain ⟨traceEqual, iterateEqual⟩ :=
        inductionHypothesis (left state block) tailAgree
      constructor
      · simp only [mdInputTrace_cons, headAgree]
        exact congrArg (fun tail => (state, block) :: tail) traceEqual
      · change mdIterate right (right state block) rest =
          mdIterate left (left state block) rest
        rw [headAgree]
        exact iterateEqual

theorem mdIterate_eq_of_eq_on_inputTrace
    (left right : Compression C B) (state : C) (blocks : List B)
    (agree : ∀ point ∈ mdInputTrace left state blocks,
      right point.1 point.2 = left point.1 point.2) :
    mdIterate right state blocks = mdIterate left state blocks :=
  (mdInputTrace_eq_of_eq_on_trace left right state blocks agree).2

/-! ## Inner/outer construction traces -/

/-- The inner MD path of one construction input. -/
def innerInputTrace (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) : List (C × B) :=
  mdInputTrace compression iv (grammar.innerWord input)

/-- The outer MD path after computing the hidden inner endpoint. -/
def outerInputTrace (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) : List (C × B) :=
  let embedded := mdIterate compression iv (grammar.innerWord input)
  mdInputTrace compression iv
    (grammar.outerWord (grammar.tagOf input) embedded)

/-- All compression inputs used by one two-pass SequenceHash evaluation. -/
def sequenceInputTrace (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) : List (C × B) :=
  innerInputTrace grammar iv compression input ++
    outerInputTrace grammar iv compression input

theorem outerInputTrace_ne_nil (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) :
    outerInputTrace grammar iv compression input ≠ [] := by
  intro empty
  have lengths := congrArg List.length empty
  simp only [outerInputTrace, length_mdInputTrace, List.length_nil] at lengths
  exact grammar.outer_nonempty (grammar.tagOf input)
    (mdIterate compression iv (grammar.innerWord input))
    (List.eq_nil_of_length_eq_zero lengths)

/-- The final compression-table point of the outer path. -/
def terminalPoint (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) : C × B :=
  (outerInputTrace grammar iv compression input).getLast
    (outerInputTrace_ne_nil grammar iv compression input)

theorem terminalPoint_mem_outerInputTrace
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) :
    terminalPoint grammar iv compression input ∈
      outerInputTrace grammar iv compression input := by
  exact List.getLast_mem _

theorem terminalPoint_mem_sequenceInputTrace
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) :
    terminalPoint grammar iv compression input ∈
      sequenceInputTrace grammar iv compression input := by
  exact List.mem_append_right _
    (terminalPoint_mem_outerInputTrace grammar iv compression input)

/-- Every nonempty MD execution is its terminal-table answer. -/
theorem mdIterate_eq_apply_terminal
    (compression : Compression C B) (state : C) (blocks : List B)
    (nonempty : blocks ≠ []) :
    mdIterate compression state blocks =
      let point := (mdInputTrace compression state blocks).getLast
        (by
          intro traceEmpty
          apply nonempty
          apply List.eq_nil_of_length_eq_zero
          have lengths := congrArg List.length traceEmpty
          simpa [length_mdInputTrace] using lengths)
      compression point.1 point.2 := by
  induction blocks generalizing state with
  | nil => exact False.elim (nonempty rfl)
  | cons block rest inductionHypothesis =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          change mdIterate compression (compression state block)
              (next :: tail) = _
          simpa [mdInputTrace] using
            inductionHypothesis (compression state block) (by simp)

/-- The construction answer is the value stored at its terminal point. -/
theorem sequenceEval_eq_terminal_apply
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) :
    sequenceEval grammar iv compression input =
      compression (terminalPoint grammar iv compression input).1
        (terminalPoint grammar iv compression input).2 := by
  unfold sequenceEval terminalPoint outerInputTrace
  exact mdIterate_eq_apply_terminal compression iv
    (grammar.outerWord (grammar.tagOf input)
      (mdIterate compression iv (grammar.innerWord input)))
    (grammar.outer_nonempty _ _)

/-! ## Oracle-coordinate activations -/

/-- Primitive-interface part of the oracle-activation audit. -/
def activatedPrimitiveInput [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (state : State C B X Tag)
    (query : C × B) : Option X :=
  match state.table query with
  | some _answer => none
  | none =>
      match state.word query.1 with
      | none => none
      | some path =>
          match grammar.classifyWord (path ++ [query.2]) with
          | .innerPrefix => none
          | .innerComplete _input => none
          | .outerPrefix => none
          | .outerComplete tag embedded =>
              match state.inner embedded with
              | none => none
              | some input =>
                  if grammar.tagOf input = tag then some input else none
          | .invalid => none

/-- The ideal-oracle coordinate read by one public simulator step.  An
evaluation query always reads its input.  A primitive query reads an oracle
coordinate only at the fresh, correctly tagged linked-terminal leaf.  This
definition delegates to a separately typed primitive tree so dependent query
elimination cannot hide an interface case. -/
def activatedInput [DecidableEq C] [DecidableEq B] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (state : State C B X Tag) :
    Query C B X → Option X
  | ⟨.eval, input⟩ => some input
  | ⟨.prim, query⟩ => activatedPrimitiveInput grammar state query

@[simp]
theorem activatedInput_eval [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (state : State C B X Tag) (input : X) :
    activatedInput grammar state ⟨.eval, input⟩ = some input := by
  rfl

/-- Complete characterization of a primitive activation.  These are exactly
the hypotheses of the executor's `outerLinked` leaf. -/
theorem activatedInput_prim_eq_some_iff [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (state : State C B X Tag)
    (query : C × B) (input : X) :
    activatedInput grammar state ⟨.prim, query⟩ = some input ↔
      state.table query = none ∧
      ∃ path tag embedded,
        state.word query.1 = some path ∧
        grammar.classifyWord (path ++ [query.2]) =
          .outerComplete tag embedded ∧
        state.inner embedded = some input ∧
        grammar.tagOf input = tag := by
  simp only [activatedInput]
  unfold activatedPrimitiveInput
  split
  next answer tableLookup =>
    simp only [Option.some.injEq, reduceCtorEq, false_iff]
    intro impossible
    have contradiction : (some answer : Option C) = none :=
      tableLookup.symm.trans impossible.1
    cases contradiction
  next tableLookup =>
    split
    next wordLookup => simp [tableLookup, wordLookup]
    next path wordLookup =>
      split
      next parse => simp [tableLookup, wordLookup, parse]
      next parsedInput parse => simp [tableLookup, wordLookup, parse]
      next parse => simp [tableLookup, wordLookup, parse]
      next tag embedded parse =>
        split
        next innerLookup => simp [tableLookup, wordLookup, parse, innerLookup]
        next linkedInput innerLookup =>
          split
          next tagEqual =>
            simp only [Option.some.injEq]
            constructor
            · intro inputEqual
              subst linkedInput
              exact ⟨tableLookup, path, tag, embedded, wordLookup, parse,
                innerLookup, tagEqual⟩
            · rintro ⟨_, otherPath, otherTag, otherEmbedded,
                otherWord, otherParse, otherInner, otherTagEqual⟩
              have pathEqual : otherPath = path :=
                Option.some.inj (otherWord.symm.trans wordLookup)
              subst otherPath
              have parseEqual := otherParse.symm.trans parse
              cases parseEqual
              have inputEqual : input = linkedInput :=
                Option.some.inj (otherInner.symm.trans innerLookup)
              exact inputEqual.symm
          next tagDifferent =>
            simp only [Option.some.injEq, reduceCtorEq, false_iff]
            rintro ⟨_, otherPath, otherTag, otherEmbedded,
              otherWord, otherParse, otherInner, otherTagEqual⟩
            have pathEqual : otherPath = path :=
              Option.some.inj (otherWord.symm.trans wordLookup)
            subst otherPath
            have parseEqual := otherParse.symm.trans parse
            cases parseEqual
            have inputEqual : input = linkedInput :=
              Option.some.inj (otherInner.symm.trans innerLookup)
            apply tagDifferent
            rw [← inputEqual, otherTagEqual]
      next parse => simp [tableLookup, wordLookup, parse]

/-- One first activation, with its terminal point and any answer that had
already occupied that point. -/
structure Activation (C B X : Type u) where
  input : X
  terminal : C × B
  occupied : Option C
deriving DecidableEq, Fintype

/-- Finite observer state used only by the proof.  The simulator state itself
need not be finite because `word` contains unbounded lists. -/
structure ActivationState (C B X Tag : Type u) where
  simulator : State C B X Tag
  activated : Finset X
  log : List (Activation C B X)

/-- State component of one total simulator step. -/
def simulatorNextState [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : Query C B X) : State C B X Tag :=
  ((simulatorStep grammar iv coins state query).get
    (simulator_step_isSome grammar iv coins state query)).1

/-- Execute one public step and append a record exactly when it reads a
previously unactivated ideal-oracle coordinate. -/
def activationTransition [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B)
    (audit : ActivationState C B X Tag) (query : Query C B X) :
    ActivationState C B X Tag :=
  let candidate := activatedInput grammar audit.simulator query
  let nextState := simulatorNextState grammar iv
    (correlatedCoins grammar iv compression) audit.simulator query
  match candidate with
  | none => { audit with simulator := nextState }
  | some input =>
      if already : input ∈ audit.activated then
        { audit with simulator := nextState }
      else
        let terminal := terminalPoint grammar iv compression input
        { simulator := nextState
          activated := insert input audit.activated
          log := audit.log ++
            [{ input := input
               terminal := terminal
               occupied := audit.simulator.table terminal }] }

/-- The complete finite activation audit of a public query history. -/
def activationRun [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    ActivationState C B X Tag :=
  history.foldl (activationTransition grammar iv compression)
    { simulator := initialState iv, activated := ∅, log := [] }

/-- The list of free terminal swaps named by an activation audit. -/
def ActivationState.freePairs (audit : ActivationState C B X Tag) :
    List (X × (C × B)) :=
  audit.log.filterMap fun activation =>
    if activation.occupied.isNone then
      some (activation.input, activation.terminal)
    else
      none

/-- Occupied activations retained by the exact local common carrier. -/
def ActivationState.occupiedRecords (audit : ActivationState C B X Tag) :
    List (Activation C B X) :=
  audit.log.filter fun activation => activation.occupied.isSome

/-! ## Structural receipts for the activation audit -/

/-- The finite set and chronological log name exactly the same inputs, and
each input occurs in the log only once. -/
def ActivationState.WellFormed [DecidableEq X]
    (audit : ActivationState C B X Tag) : Prop :=
  audit.activated = (audit.log.map Activation.input).toFinset ∧
    (audit.log.map Activation.input).Nodup

theorem activationTransition_wellFormed [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (audit : ActivationState C B X Tag)
    (query : Query C B X) (wellFormed : audit.WellFormed) :
    (activationTransition grammar iv compression audit query).WellFormed := by
  cases candidate : activatedInput grammar audit.simulator query with
  | none =>
      simpa [activationTransition, candidate,
        ActivationState.WellFormed] using wellFormed
  | some input =>
      by_cases already : input ∈ audit.activated
      · simpa [activationTransition, candidate, already,
          ActivationState.WellFormed] using wellFormed
      · have notInLog : input ∉ audit.log.map Activation.input := by
          simpa [wellFormed.1] using already
        have appendedNodup :
            (audit.log.map Activation.input ++ [input]).Nodup := by
          simpa [List.concat_eq_append] using wellFormed.2.concat notInLog
        constructor
        · simp [activationTransition, candidate, already,
            ActivationState.WellFormed, wellFormed.1, notInLog]
        · simpa [activationTransition, candidate, already,
            ActivationState.WellFormed, notInLog] using appendedNodup

theorem activationRun_wellFormed [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    (activationRun grammar iv compression history).WellFormed := by
  unfold activationRun
  have initial :
      (ActivationState.WellFormed
        ({ simulator := initialState iv, activated := ∅, log := [] } :
          ActivationState C B X Tag)) := by
    simp [ActivationState.WellFormed]
  generalize
    ({ simulator := initialState iv, activated := ∅, log := [] } :
      ActivationState C B X Tag) = audit at initial ⊢
  induction history generalizing audit with
  | nil => simpa using initial
  | cons query rest inductionHypothesis =>
      simp only [List.foldl_cons]
      exact inductionHypothesis _
        (activationTransition_wellFormed grammar iv compression audit query
          initial)

theorem activationRun_log_inputs_nodup [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    ((activationRun grammar iv compression history).log.map
      Activation.input).Nodup :=
  (activationRun_wellFormed grammar iv compression history).2

/-- Every record stores the canonical terminal computed by the correlated
compression tape for its own input. -/
def ActivationState.TerminalsCorrect
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B)
    (audit : ActivationState C B X Tag) : Prop :=
  ∀ activation ∈ audit.log,
    activation.terminal =
      terminalPoint grammar iv compression activation.input

theorem activationTransition_terminalsCorrect [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (audit : ActivationState C B X Tag)
    (query : Query C B X) (correct : audit.TerminalsCorrect grammar iv compression) :
    (activationTransition grammar iv compression audit query).TerminalsCorrect
      grammar iv compression := by
  intro activation member
  cases candidate : activatedInput grammar audit.simulator query with
  | none =>
      exact correct activation (by
        simpa [activationTransition, candidate] using member)
  | some input =>
      by_cases already : input ∈ audit.activated
      · exact correct activation (by
          simpa [activationTransition, candidate, already] using member)
      · have memberCases : activation ∈ audit.log ∨
            activation =
              { input := input
                terminal := terminalPoint grammar iv compression input
                occupied := audit.simulator.table
                  (terminalPoint grammar iv compression input) } := by
          simpa [activationTransition, candidate, already] using member
        rcases memberCases with old | rfl
        · exact correct activation old
        · rfl

theorem activationRun_terminalsCorrect [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    (activationRun grammar iv compression history).TerminalsCorrect
      grammar iv compression := by
  unfold activationRun
  have initial :
      ActivationState.TerminalsCorrect grammar iv compression
        ({ simulator := initialState iv, activated := ∅, log := [] } :
          ActivationState C B X Tag) := by
    simp [ActivationState.TerminalsCorrect]
  generalize
    ({ simulator := initialState iv, activated := ∅, log := [] } :
      ActivationState C B X Tag) = audit at initial ⊢
  induction history generalizing audit with
  | nil => simpa using initial
  | cons query rest inductionHypothesis =>
      simp only [List.foldl_cons]
      exact inductionHypothesis _
        (activationTransition_terminalsCorrect grammar iv compression audit
          query initial)

theorem activation_terminal_eq_of_mem_run [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (activation : Activation C B X)
    (member : activation ∈
      (activationRun grammar iv compression history).log) :
    activation.terminal =
      terminalPoint grammar iv compression activation.input :=
  activationRun_terminalsCorrect grammar iv compression history activation member

/-- Filtering the activation log to free records preserves uniqueness of the
ideal-oracle coordinate. -/
theorem ActivationState.freePairs_fst_nodup [DecidableEq X]
    (audit : ActivationState C B X Tag)
    (nodup : (audit.log.map Activation.input).Nodup) :
    (audit.freePairs.map Prod.fst).Nodup := by
  have projectionSublist : ∀ log : List (Activation C B X),
      List.Sublist
        ((log.filterMap (fun activation =>
            if activation.occupied.isNone then
              some (activation.input, activation.terminal)
            else none)).map Prod.fst)
        (log.map Activation.input) := by
    intro log
    induction log with
    | nil => exact List.Sublist.refl []
    | cons activation rest inductionHypothesis =>
        cases occupied : activation.occupied with
        | none =>
            simpa [occupied] using
              List.Sublist.cons_cons activation.input inductionHypothesis
        | some value =>
            simpa [occupied] using
              List.sublist_cons_of_sublist activation.input inductionHypothesis
  exact nodup.sublist (by
    simpa [ActivationState.freePairs] using projectionSublist audit.log)

/-! ## Fixed-reveal terminal swaps -/

/-- Read an uncurried complete table as a compression function. -/
def compressionOfTable (table : C × B → C) : Compression C B :=
  fun state block => table (state, block)

/-- The correlated real coins carried by an augmented `(dummy, table)` seed.
The dummy table is deliberately ignored until an occupied-link carrier needs
it for exact thinning. -/
def correlatedAugmentedCoins (grammar : Grammar C B X Tag) (iv : C)
    (seed : Coins C B X) : Coins C B X :=
  correlatedCoins grammar iv (compressionOfTable seed.2)

/-- Exchange every free ideal-oracle coordinate with its revealed terminal
compression coordinate.  For a fixed reveal this is an honest permutation of
the complete product seed. -/
def ActivationState.swapCoins [DecidableEq C] [DecidableEq B]
    [DecidableEq X] (audit : ActivationState C B X Tag) :
    Equiv.Perm (Coins C B X) :=
  RandomSystems.coordinateSwaps audit.freePairs

theorem ActivationState.swapCoins_oracle_of_mem [DecidableEq C]
    [DecidableEq B] [DecidableEq X]
    (audit : ActivationState C B X Tag)
    (fstNodup : (audit.freePairs.map Prod.fst).Nodup)
    (sndNodup : (audit.freePairs.map Prod.snd).Nodup)
    (pair : X × (C × B)) (member : pair ∈ audit.freePairs)
    (seed : Coins C B X) :
    (audit.swapCoins seed).1 pair.1 = seed.2 pair.2 := by
  exact RandomSystems.coordinateSwaps_fst_apply_of_mem audit.freePairs
    fstNodup sndNodup pair member seed

theorem ActivationState.swapCoins_compression_of_mem [DecidableEq C]
    [DecidableEq B] [DecidableEq X]
    (audit : ActivationState C B X Tag)
    (fstNodup : (audit.freePairs.map Prod.fst).Nodup)
    (sndNodup : (audit.freePairs.map Prod.snd).Nodup)
    (pair : X × (C × B)) (member : pair ∈ audit.freePairs)
    (seed : Coins C B X) :
    (audit.swapCoins seed).2 pair.2 = seed.1 pair.1 := by
  exact RandomSystems.coordinateSwaps_snd_apply_of_mem audit.freePairs
    fstNodup sndNodup pair member seed

theorem ActivationState.swapCoins_oracle_of_not_mem [DecidableEq C]
    [DecidableEq B] [DecidableEq X]
    (audit : ActivationState C B X Tag) (input : X)
    (fresh : input ∉ audit.freePairs.map Prod.fst)
    (seed : Coins C B X) :
    (audit.swapCoins seed).1 input = seed.1 input := by
  exact RandomSystems.coordinateSwaps_fst_apply_of_not_mem
    audit.freePairs input seed fresh

theorem ActivationState.swapCoins_compression_of_not_mem [DecidableEq C]
    [DecidableEq B] [DecidableEq X]
    (audit : ActivationState C B X Tag) (point : C × B)
    (fresh : point ∉ audit.freePairs.map Prod.snd)
    (seed : Coins C B X) :
    (audit.swapCoins seed).2 point = seed.2 point := by
  exact RandomSystems.coordinateSwaps_snd_apply_of_not_mem
    audit.freePairs point seed fresh

/-- The exact retained branch at every previously occupied terminal. -/
def ActivationState.LinkConsistent
    (audit : ActivationState C B X Tag) (dummy : X → C) : Prop :=
  ∀ activation ∈ audit.log, ∀ answer,
    activation.occupied = some answer → dummy activation.input = answer

instance instDecidableLinkConsistent [DecidableEq C] [Fintype C]
    [DecidableEq X] [Fintype X]
    (audit : ActivationState C B X Tag) (dummy : X → C) :
    Decidable (audit.LinkConsistent dummy) := by
  unfold ActivationState.LinkConsistent
  infer_instance

/-- Minimal fixed-reveal safety needed for the multi-coordinate exchange.
The first projection is automatically unique by the activation audit; graph
safety supplies uniqueness of the terminal compression coordinates. -/
def ActivationState.TerminalsDistinct
    (audit : ActivationState C B X Tag) : Prop :=
  (audit.freePairs.map Prod.snd).Nodup

instance instDecidableTerminalsDistinct [DecidableEq C] [DecidableEq B]
    (audit : ActivationState C B X Tag) :
    Decidable audit.TerminalsDistinct := by
  unfold ActivationState.TerminalsDistinct
  infer_instance

/-! ## History-aware terminal classification

The chronological activation record alone is not enough to decide whether a
terminal coordinate may be exchanged.  A direct primitive query may touch the
terminal either before or after the first construction-oracle activation.  The
following predicate inspects every executable prefix and records exactly the
case in which such a query is fresh and does not take the correctly linked
leaf. -/

/-- Correlated simulator state immediately before position `index` of a public
history. -/
def correlatedStateBefore [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (index : Fin history.length) : State C B X Tag :=
  (history.take index.1).foldl
    (simulatorNextState grammar iv
      (correlatedCoins grammar iv compression)) (initialState iv)

/-- A terminal needs the occupied-link carrier precisely when some fresh
primitive observation of that point is not the correctly linked observation
for this activation.  The definition quantifies over the finite list of
actual public steps, so its decidability is computational. -/
def TerminalBlocked [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (activation : Activation C B X) : Prop :=
  ∃ index : Fin history.length,
    history.get index = ⟨.prim, activation.terminal⟩ ∧
    (correlatedStateBefore grammar iv compression history index).table
        activation.terminal = none ∧
    activatedInput grammar
        (correlatedStateBefore grammar iv compression history index)
        (history.get index) ≠ some activation.input

noncomputable instance instDecidableTerminalBlocked
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (activation : Activation C B X) :
    Decidable (TerminalBlocked grammar iv compression history activation) := by
  exact Classical.propDecidable _

/-- Terminal exchanges that are safe for the complete public history. -/
def smartFreePairs [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    List (X × (C × B)) :=
  (activationRun grammar iv compression history).log.filterMap fun activation =>
    if TerminalBlocked grammar iv compression history activation then
      none
    else
      some (activation.input, activation.terminal)

/-- Activations handled by the exact occupied-link common carrier. -/
def smartLinkRecords [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    List (Activation C B X) :=
  (activationRun grammar iv compression history).log.filter fun activation =>
    decide (TerminalBlocked grammar iv compression history activation)

/-- Exchange all history-safe construction coordinates with their real MD
terminal coordinates. -/
def smartSwapCoins [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    Equiv.Perm (Coins C B X) :=
  RandomSystems.coordinateSwaps
    (smartFreePairs grammar iv compression history)

/-- The retained occupied-link branch.  On every nonswappable activation the
dummy ideal-oracle coordinate equals the real construction answer. -/
def SmartLinkConsistent [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (dummy : X → C) : Prop :=
  ∀ activation ∈ (activationRun grammar iv compression history).log,
    TerminalBlocked grammar iv compression history activation →
      dummy activation.input =
        sequenceEval grammar iv compression activation.input

instance instDecidableSmartLinkConsistent [Fintype C] [Fintype B]
    [Fintype X] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (dummy : X → C) :
    Decidable (SmartLinkConsistent grammar iv compression history dummy) := by
  unfold SmartLinkConsistent
  infer_instance

/-- Graph safety needed by the simultaneous coordinate exchange: no two
swappable activations name the same compression coordinate. -/
def SmartTerminalsDistinct [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) : Prop :=
  ((smartFreePairs grammar iv compression history).map Prod.snd).Nodup

instance instDecidableSmartTerminalsDistinct [Fintype C] [Fintype B]
    [Fintype X] [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    Decidable (SmartTerminalsDistinct grammar iv compression history) := by
  unfold SmartTerminalsDistinct
  infer_instance

@[simp]
theorem mem_smartFreePairs_iff [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (pair : X × (C × B)) :
    pair ∈ smartFreePairs grammar iv compression history ↔
      ∃ activation ∈ (activationRun grammar iv compression history).log,
        ¬ TerminalBlocked grammar iv compression history activation ∧
        (activation.input, activation.terminal) = pair := by
  simp [smartFreePairs]

/-- Safe-pair inputs inherit the activation log's uniqueness. -/
theorem smartFreePairs_fst_nodup [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    ((smartFreePairs grammar iv compression history).map Prod.fst).Nodup := by
  have projectionSublist : ∀ log : List (Activation C B X),
      List.Sublist
        ((log.filterMap (fun activation =>
            if TerminalBlocked grammar iv compression history activation then
              none
            else some (activation.input, activation.terminal))).map Prod.fst)
        (log.map Activation.input) := by
    intro log
    induction log with
    | nil => exact List.Sublist.refl []
    | cons activation rest inductionHypothesis =>
        by_cases blocked :
            TerminalBlocked grammar iv compression history activation
        · simpa [blocked] using
            List.sublist_cons_of_sublist activation.input inductionHypothesis
        · simpa [blocked] using
            List.Sublist.cons_cons activation.input inductionHypothesis
  exact (activationRun_log_inputs_nodup grammar iv compression history).sublist
    (by
      simpa [smartFreePairs] using
        projectionSublist
          (activationRun grammar iv compression history).log)

/-- An activation log with unique input projection contains at most one
record for a given construction input. -/
theorem activation_eq_of_mem_of_input_eq [DecidableEq X]
    {log : List (Activation C B X)}
    (nodup : (log.map Activation.input).Nodup)
    {left right : Activation C B X}
    (leftMember : left ∈ log) (rightMember : right ∈ log)
    (inputEqual : left.input = right.input) :
    left = right := by
  induction log generalizing left right with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at nodup
      rcases nodup with ⟨headFresh, tailNodup⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftTail
      · rcases rightMember with rfl | rightTail
        · rfl
        · exfalso
          apply headFresh
          exact List.mem_map.mpr ⟨right, rightTail, inputEqual.symm⟩
      · rcases rightMember with rfl | rightTail
        · exfalso
          apply headFresh
          exact List.mem_map.mpr ⟨left, leftTail, inputEqual⟩
        · exact inductionHypothesis tailNodup leftTail rightTail inputEqual

/-- A blocked activation input cannot occur as the first projection of any
safe pair. -/
theorem input_not_mem_smartFreePairs_of_blocked [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (activation : Activation C B X)
    (member : activation ∈
      (activationRun grammar iv compression history).log)
    (blocked : TerminalBlocked grammar iv compression history activation) :
    activation.input ∉
      (smartFreePairs grammar iv compression history).map Prod.fst := by
  intro inputMember
  obtain ⟨pair, pairMember, pairInput⟩ := List.mem_map.mp inputMember
  obtain ⟨other, otherMember, otherSafe, pairEqual⟩ :=
    (mem_smartFreePairs_iff grammar iv compression history pair).mp pairMember
  have inputEqual : other.input = activation.input := by
    simpa [← pairInput] using congrArg Prod.fst pairEqual
  have logNodup := activationRun_log_inputs_nodup grammar iv compression history
  have activationEqual : other = activation := by
    exact activation_eq_of_mem_of_input_eq logNodup otherMember member
      inputEqual
  subst other
  exact otherSafe blocked

theorem smartSwapCoins_oracle_of_mem [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (sndNodup :
      ((smartFreePairs grammar iv compression history).map Prod.snd).Nodup)
    (pair : X × (C × B))
    (member : pair ∈ smartFreePairs grammar iv compression history)
    (seed : Coins C B X) :
    (smartSwapCoins grammar iv compression history seed).1 pair.1 =
      seed.2 pair.2 := by
  exact RandomSystems.coordinateSwaps_fst_apply_of_mem
    (smartFreePairs grammar iv compression history)
    (smartFreePairs_fst_nodup grammar iv compression history)
    sndNodup pair member seed

theorem smartSwapCoins_compression_of_not_mem [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (point : C × B)
    (fresh : point ∉
      (smartFreePairs grammar iv compression history).map Prod.snd)
    (seed : Coins C B X) :
    (smartSwapCoins grammar iv compression history seed).2 point =
      seed.2 point := by
  exact RandomSystems.coordinateSwaps_snd_apply_of_not_mem
    (smartFreePairs grammar iv compression history) point seed fresh

theorem smartSwapCoins_oracle_of_not_mem [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X))
    (input : X)
    (fresh : input ∉
      (smartFreePairs grammar iv compression history).map Prod.fst)
    (seed : Coins C B X) :
    (smartSwapCoins grammar iv compression history seed).1 input =
      seed.1 input := by
  exact RandomSystems.coordinateSwaps_fst_apply_of_not_mem
    (smartFreePairs grammar iv compression history) input seed fresh

/-! ## One-step replay under two complete tapes -/

/-- A primitive step depends on the compression coordinate exactly in the
eight non-linked fresh leaves and on the ideal-oracle coordinate exactly in
the linked leaf.  The proof is routed through the generated nine-premise
eliminator, so every executable parser branch is present. -/
theorem primitiveStep_eq_of_activated_agreement [DecidableEq C]
    [DecidableEq B] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) (state : State C B X Tag)
    (query : C × B)
    (compressionAgreement :
      state.table query = none →
        activatedPrimitiveInput grammar state query = none →
        left.2 query = right.2 query)
    (oracleAgreement : ∀ input,
      activatedPrimitiveInput grammar state query = some input →
        left.1 input = right.1 input) :
    primitiveStep grammar iv left state query =
      primitiveStep grammar iv right state query := by
  apply primitiveStep_cases grammar iv left state query
      (P := fun result =>
        result = primitiveStep grammar iv right state query)
  · intro answer tableLookup
    simp [primitiveStep, tableLookup]
  · intro tableLookup wordLookup
    have inactive :
        activatedPrimitiveInput grammar state query = none := by
      simp [activatedPrimitiveInput, tableLookup, wordLookup]
    have answerEqual := compressionAgreement tableLookup inactive
    simp [primitiveStep, tableLookup, wordLookup,
      loosePrimitiveStep, answerEqual]
  · intro path tableLookup wordLookup parse
    have inactive :
        activatedPrimitiveInput grammar state query = none := by
      simp [activatedPrimitiveInput, tableLookup, wordLookup, parse]
    have answerEqual := compressionAgreement tableLookup inactive
    simp [primitiveStep, tableLookup, wordLookup, parse,
      livePrimitiveStep, answerEqual]
  · intro path input tableLookup wordLookup parse
    have inactive :
        activatedPrimitiveInput grammar state query = none := by
      simp [activatedPrimitiveInput, tableLookup, wordLookup, parse]
    have answerEqual := compressionAgreement tableLookup inactive
    simp [primitiveStep, tableLookup, wordLookup, parse,
      livePrimitiveStep, answerEqual]
  · intro path tableLookup wordLookup parse
    have inactive :
        activatedPrimitiveInput grammar state query = none := by
      simp [activatedPrimitiveInput, tableLookup, wordLookup, parse]
    have answerEqual := compressionAgreement tableLookup inactive
    simp [primitiveStep, tableLookup, wordLookup, parse,
      livePrimitiveStep, answerEqual]
  · intro path tag embedded tableLookup wordLookup parse innerLookup
    have inactive :
        activatedPrimitiveInput grammar state query = none := by
      simp [activatedPrimitiveInput, tableLookup, wordLookup, parse,
        innerLookup]
    have answerEqual := compressionAgreement tableLookup inactive
    simp [primitiveStep, tableLookup, wordLookup, parse, innerLookup,
      pendingPrimitiveStep, answerEqual]
  · intro path tag embedded input tableLookup wordLookup parse innerLookup
      tagDifferent
    have inactive :
        activatedPrimitiveInput grammar state query = none := by
      simp [activatedPrimitiveInput, tableLookup, wordLookup, parse,
        innerLookup, tagDifferent]
    have answerEqual := compressionAgreement tableLookup inactive
    simp [primitiveStep, tableLookup, wordLookup, parse, innerLookup,
      tagDifferent, pendingPrimitiveStep, answerEqual]
  · intro path tag embedded input tableLookup wordLookup parse innerLookup
      tagEqual
    have active :
        activatedPrimitiveInput grammar state query = some input := by
      simp [activatedPrimitiveInput, tableLookup, wordLookup, parse,
        innerLookup, tagEqual]
    have answerEqual := oracleAgreement input active
    simp [primitiveStep, tableLookup, wordLookup, parse, innerLookup,
      tagEqual, linkedPrimitiveStep, answerEqual]
  · intro path tableLookup wordLookup parse
    have inactive :
        activatedPrimitiveInput grammar state query = none := by
      simp [activatedPrimitiveInput, tableLookup, wordLookup, parse]
    have answerEqual := compressionAgreement tableLookup inactive
    simp [primitiveStep, tableLookup, wordLookup, parse,
      ordinaryPrimitiveStep, answerEqual]

theorem evalStep_eq_of_oracle_agreement [DecidableEq X]
    (left right : Coins C B X) (state : State C B X Tag) (input : X)
    (answerEqual : left.1 input = right.1 input) :
    evalStep left state input = evalStep right state input := by
  unfold evalStep
  split <;> simp [answerEqual]

/-- Interface-level form of the one-step replay theorem. -/
theorem simulatorStep_eq_of_activated_agreement [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) (state : State C B X Tag)
    (query : Query C B X)
    (compressionAgreement : ∀ point,
      query = ⟨.prim, point⟩ → state.table point = none →
        activatedInput grammar state query = none →
        left.2 point = right.2 point)
    (oracleAgreement : ∀ input,
      activatedInput grammar state query = some input →
        left.1 input = right.1 input) :
    simulatorStep grammar iv left state query =
      simulatorStep grammar iv right state query := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | prim =>
      simp only [simulatorStep, Option.some.injEq]
      apply primitiveStep_eq_of_activated_agreement grammar iv left right
        state input
      · intro tableLookup inactive
        exact compressionAgreement input rfl tableLookup (by simpa using inactive)
      · intro activated active
        exact oracleAgreement activated (by simpa using active)
  | eval =>
      simp only [simulatorStep, Option.some.injEq]
      apply evalStep_eq_of_oracle_agreement
      exact oracleAgreement input (by simp [activatedInput])

/-! ## Replay along a complete public history -/

/-- Exact coin equalities needed by one public step from a fixed state. -/
def StepCoinsAgree [DecidableEq C] [DecidableEq B] [DecidableEq Tag]
  (grammar : Grammar C B X Tag) (left right : Coins C B X)
    (state : State C B X Tag) (query : Query C B X) : Prop :=
  (∀ point, query = ⟨.prim, point⟩ →
      state.table point = none →
      activatedInput grammar state query = none →
        left.2 point = right.2 point) ∧
    (∀ input, activatedInput grammar state query = some input →
      left.1 input = right.1 input)

/-- State reached by folding the total executable simulator. -/
def simulatorAdvance [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X) :
    State C B X Tag → List (Query C B X) → State C B X Tag :=
  List.foldl (simulatorNextState grammar iv coins)

@[simp]
theorem activationTransition_simulator [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (audit : ActivationState C B X Tag)
    (query : Query C B X) :
    (activationTransition grammar iv compression audit query).simulator =
      simulatorNextState grammar iv
        (correlatedCoins grammar iv compression) audit.simulator query := by
  simp only [activationTransition]
  split
  · rfl
  · split <;> rfl

/-- The observer and the executable correlated simulator carry exactly the
same state after every prefix. -/
theorem activationRun_simulator_eq_advance [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (history : List (Query C B X)) :
    (activationRun grammar iv compression history).simulator =
      simulatorAdvance grammar iv
        (correlatedCoins grammar iv compression) (initialState iv) history := by
  have foldEquality : ∀ (queries : List (Query C B X))
      (audit : ActivationState C B X Tag),
      (queries.foldl (activationTransition grammar iv compression) audit).simulator =
        queries.foldl
          (simulatorNextState grammar iv
            (correlatedCoins grammar iv compression)) audit.simulator := by
    intro queries
    induction queries with
    | nil => intro audit; rfl
    | cons query rest inductionHypothesis =>
        intro audit
        simp only [List.foldl_cons]
        rw [inductionHypothesis]
        rw [activationTransition_simulator]
  unfold activationRun simulatorAdvance
  exact foldEquality history _

theorem activationTransition_log_prefix [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (audit : ActivationState C B X Tag)
    (query : Query C B X) :
    audit.log <+:
      (activationTransition grammar iv compression audit query).log := by
  simp only [activationTransition]
  split
  · exact List.prefix_refl _
  · split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

theorem activationFold_log_prefix [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (audit : ActivationState C B X Tag)
    (history : List (Query C B X)) :
    audit.log <+:
      (history.foldl (activationTransition grammar iv compression) audit).log := by
  induction history generalizing audit with
  | nil => exact List.prefix_refl _
  | cons query rest inductionHypothesis =>
      exact (activationTransition_log_prefix grammar iv compression audit query).trans
        (inductionHypothesis
          (activationTransition grammar iv compression audit query))

/-- A currently activated oracle coordinate has a unique record immediately
after the step that observes it. -/
theorem exists_activationTransition_log_of_candidate [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (audit : ActivationState C B X Tag)
    (query : Query C B X) (input : X)
    (wellFormed : audit.WellFormed)
    (candidate : activatedInput grammar audit.simulator query = some input) :
    ∃ activation ∈
        (activationTransition grammar iv compression audit query).log,
      activation.input = input := by
  by_cases already : input ∈ audit.activated
  · have inputInMap : input ∈ audit.log.map Activation.input := by
      simpa [wellFormed.1] using already
    obtain ⟨activation, activationMember, activationInput⟩ :=
      List.mem_map.mp inputInMap
    refine ⟨activation, ?_, activationInput⟩
    simpa [activationTransition, candidate, already] using activationMember
  · let terminal := terminalPoint grammar iv compression input
    let activation : Activation C B X :=
      { input := input
        terminal := terminal
        occupied := audit.simulator.table terminal }
    refine ⟨activation, ?_, rfl⟩
    simp [activationTransition, candidate, already, activation, terminal]

/-- Any oracle coordinate read at one public step has its activation record in
the final audit of every history containing that step. -/
theorem exists_activationRun_log_of_active [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B)
    (front : List (Query C B X)) (query : Query C B X)
    (suffix : List (Query C B X)) (input : X)
    (active : activatedInput grammar
      (simulatorAdvance grammar iv
        (correlatedCoins grammar iv compression) (initialState iv) front)
      query = some input) :
    ∃ activation ∈
        (activationRun grammar iv compression
          (front ++ query :: suffix)).log,
      activation.input = input := by
  let before := activationRun grammar iv compression front
  have beforeWellFormed : before.WellFormed := by
    exact activationRun_wellFormed grammar iv compression front
  have activeBefore :
      activatedInput grammar before.simulator query = some input := by
    rw [activationRun_simulator_eq_advance]
    exact active
  obtain ⟨activation, currentMember, activationInput⟩ :=
    exists_activationTransition_log_of_candidate grammar iv compression
      before query input beforeWellFormed activeBefore
  refine ⟨activation, ?_, activationInput⟩
  have memberAfterSuffix : activation ∈
      (suffix.foldl (activationTransition grammar iv compression)
        (activationTransition grammar iv compression before query)).log :=
    (activationFold_log_prefix grammar iv compression
      (activationTransition grammar iv compression before query) suffix).mem
      currentMember
  simpa [activationRun, List.foldl_append, before] using memberAfterSuffix

/-- The step equalities required recursively along one concrete history.
The successor state is computed in the left execution; the replay theorem
below proves that the right execution reaches the same state. -/
def ReplaySafeFrom [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) :
    State C B X Tag → List (Query C B X) → Prop
  | _state, [] => True
  | state, query :: rest =>
      StepCoinsAgree grammar left right state query ∧
        ReplaySafeFrom grammar iv left right
          (simulatorNextState grammar iv left state query) rest

/-- Replay safety from the initial simulator state. -/
def ReplaySafe [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) (history : List (Query C B X)) : Prop :=
  ReplaySafeFrom grammar iv left right (initialState iv) history

/-- The central fixed-history exchange theorem.  Safe terminal coordinates
are exchanged; blocked coordinates are retained by the occupied-link
equality.  The resulting independent-tape execution replays the correlated
real execution at every public step. -/
theorem replaySafe_correlatedAugmented_smartSwap [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (seed : Coins C B X) (history : List (Query C B X))
    (terminalsDistinct : SmartTerminalsDistinct grammar iv
      (compressionOfTable seed.2) history)
    (linkConsistent : SmartLinkConsistent grammar iv
      (compressionOfTable seed.2) history seed.1) :
    ReplaySafe grammar iv
      (correlatedAugmentedCoins grammar iv seed)
      (smartSwapCoins grammar iv (compressionOfTable seed.2) history seed)
      history := by
  let compression : Compression C B := compressionOfTable seed.2
  let left : Coins C B X := correlatedCoins grammar iv compression
  let right : Coins C B X :=
    smartSwapCoins grammar iv compression history seed
  change ReplaySafeFrom grammar iv left right (initialState iv) history
  have replaySuffix : ∀ (front suffix : List (Query C B X)),
      front ++ suffix = history →
      ReplaySafeFrom grammar iv left right
        (simulatorAdvance grammar iv left (initialState iv) front) suffix := by
    intro front suffix decomposition
    induction suffix generalizing front with
    | nil => simp [ReplaySafeFrom]
    | cons query rest inductionHypothesis =>
        simp only [ReplaySafeFrom]
        constructor
        · constructor
          · intro point queryIsPrimitive tableFresh inactive
            have pointNotSafe : point ∉
                (smartFreePairs grammar iv compression history).map Prod.snd := by
              intro pointMember
              obtain ⟨pair, pairMember, pairPoint⟩ :=
                List.mem_map.mp pointMember
              obtain ⟨activation, activationMember, activationSafe,
                  activationPair⟩ :=
                (mem_smartFreePairs_iff grammar iv compression history pair).mp
                  pairMember
              have terminalEqual : activation.terminal = point := by
                calc
                  activation.terminal = pair.2 := by
                    simpa using congrArg Prod.snd activationPair
                  _ = point := pairPoint
              apply activationSafe
              have indexBound : front.length < history.length := by
                rw [← decomposition]
                simp
              let index : Fin history.length := ⟨front.length, indexBound⟩
              have queryAt : history.get index = query := by
                calc
                  history.get index =
                      (front ++ query :: rest).get
                        ⟨index.1, by simpa [← decomposition] using index.2⟩ :=
                    List.get_of_eq decomposition.symm index
                  _ = query := by simp [index]
              have stateAt :
                  correlatedStateBefore grammar iv compression history index =
                    simulatorAdvance grammar iv left (initialState iv) front := by
                have takeEqual : history.take front.length = front := by
                  calc
                    history.take front.length =
                        (front ++ query :: rest).take front.length :=
                      congrArg (List.take front.length) decomposition.symm
                    _ = front := by simp
                simp [correlatedStateBefore, simulatorAdvance, index, takeEqual,
                  left]
              refine ⟨index, ?_, ?_, ?_⟩
              · rw [queryAt, queryIsPrimitive, terminalEqual]
              · rw [stateAt, terminalEqual]
                exact tableFresh
              · rw [stateAt, queryAt]
                intro impossible
                rw [inactive] at impossible
                cases impossible
            change seed.2 point = right.2 point
            exact (smartSwapCoins_compression_of_not_mem grammar iv compression
              history point pointNotSafe seed).symm
          · intro input active
            obtain ⟨activation, activationMemberLocal, activationInput⟩ :=
              exists_activationRun_log_of_active grammar iv compression
                front query rest input active
            have activationMember : activation ∈
                (activationRun grammar iv compression history).log := by
              rw [← decomposition]
              exact activationMemberLocal
            by_cases blocked :
                TerminalBlocked grammar iv compression history activation
            · have inputNotSafe : activation.input ∉
                  (smartFreePairs grammar iv compression history).map Prod.fst :=
                input_not_mem_smartFreePairs_of_blocked grammar iv compression
                  history activation activationMember blocked
              have unchanged := smartSwapCoins_oracle_of_not_mem grammar iv
                compression history activation.input inputNotSafe seed
              have retained := linkConsistent activation activationMember blocked
              rw [← activationInput]
              change sequenceEval grammar iv compression activation.input =
                right.1 activation.input
              exact retained.symm.trans unchanged.symm
            · have pairMember :
                  (activation.input, activation.terminal) ∈
                    smartFreePairs grammar iv compression history := by
                exact (mem_smartFreePairs_iff grammar iv compression history
                  (activation.input, activation.terminal)).mpr
                    ⟨activation, activationMember, blocked, rfl⟩
              have exchanged := smartSwapCoins_oracle_of_mem grammar iv
                compression history terminalsDistinct
                (activation.input, activation.terminal) pairMember seed
              rw [← activationInput]
              change sequenceEval grammar iv compression activation.input =
                right.1 activation.input
              have terminalCorrect := activation_terminal_eq_of_mem_run
                grammar iv compression history activation activationMember
              calc
                sequenceEval grammar iv compression activation.input =
                    compression
                      (terminalPoint grammar iv compression
                        activation.input).1
                      (terminalPoint grammar iv compression
                        activation.input).2 :=
                  sequenceEval_eq_terminal_apply grammar iv compression
                    activation.input
                _ = compression activation.terminal.1
                      activation.terminal.2 := by rw [terminalCorrect]
                _ = seed.2 activation.terminal := rfl
                _ = right.1 activation.input := exchanged.symm
        · have tail := inductionHypothesis (front ++ [query]) (by
              simpa [List.append_assoc] using decomposition)
          simpa [simulatorAdvance, List.foldl_append] using tail
  simpa [ReplaySafe, simulatorAdvance] using replaySuffix [] history (by simp)

theorem replaySafeFrom_append [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) (state : State C B X Tag)
    (front suffix : List (Query C B X))
    (safe : ReplaySafeFrom grammar iv left right state (front ++ suffix)) :
    ReplaySafeFrom grammar iv left right state front ∧
      ReplaySafeFrom grammar iv left right
        (simulatorAdvance grammar iv left state front) suffix := by
  induction front generalizing state with
  | nil => simpa [ReplaySafeFrom, simulatorAdvance] using safe
  | cons query rest inductionHypothesis =>
      simp only [List.cons_append, ReplaySafeFrom] at safe
      obtain ⟨stepSafe, tailSafe⟩ := safe
      obtain ⟨frontSafe, suffixSafe⟩ := inductionHypothesis
        (simulatorNextState grammar iv left state query) tailSafe
      constructor
      · exact ⟨stepSafe, frontSafe⟩
      · simpa [simulatorAdvance] using suffixSafe

theorem replaySafeFrom_prefix [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) (state : State C B X Tag)
    {front history : List (Query C B X)} (isPrefix : front <+: history)
    (safe : ReplaySafeFrom grammar iv left right state history) :
    ReplaySafeFrom grammar iv left right state front := by
  obtain ⟨suffix, rfl⟩ := isPrefix
  exact (replaySafeFrom_append grammar iv left right state front suffix safe).1

/-- The machine fold is definitionally the total `simulatorAdvance`. -/
theorem simulator_runFrom_eq_some_advance [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (history : List (Query C B X)) :
    (simulatorMachine grammar iv coins).runFrom state history =
      some (simulatorAdvance grammar iv coins state history) := by
  induction history generalizing state with
  | nil => rfl
  | cons query rest inductionHypothesis =>
      rw [Machine.runFrom_cons]
      have stepSome :
          simulatorStep grammar iv coins state query =
            some ((simulatorStep grammar iv coins state query).get
              (simulator_step_isSome grammar iv coins state query)) :=
        Option.some_get
          (simulator_step_isSome grammar iv coins state query) |>.symm
      rw [show (simulatorMachine grammar iv coins).step state query =
          simulatorStep grammar iv coins state query by rfl, stepSome]
      change
        (simulatorMachine grammar iv coins).runFrom
            (simulatorNextState grammar iv coins state query) rest =
          some (simulatorAdvance grammar iv coins state (query :: rest))
      rw [inductionHypothesis]
      rfl

/-- A replay-safe history reaches the same state under both complete tapes. -/
theorem simulator_runFrom_eq_of_replaySafe [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) (state : State C B X Tag)
    (history : List (Query C B X))
    (safe : ReplaySafeFrom grammar iv left right state history) :
    (simulatorMachine grammar iv left).runFrom state history =
      (simulatorMachine grammar iv right).runFrom state history := by
  rw [simulator_runFrom_eq_some_advance grammar iv left state history]
  induction history generalizing state with
  | nil => rfl
  | cons query rest inductionHypothesis =>
      simp only [ReplaySafeFrom] at safe
      have stepEqual := simulatorStep_eq_of_activated_agreement
        grammar iv left right state query safe.1.1 safe.1.2
      cases leftTransition : simulatorStep grammar iv left state query with
      | none =>
          have defined :=
            simulator_step_isSome grammar iv left state query
          simp [leftTransition] at defined
      | some next =>
        have rightTransition :
            simulatorStep grammar iv right state query = some next := by
          rw [leftTransition] at stepEqual
          exact stepEqual.symm
        have leftNext :
            simulatorNextState grammar iv left state query = next.1 := by
          unfold simulatorNextState
          exact congrArg Prod.fst
            (Option.get_of_eq_some
              (simulator_step_isSome grammar iv left state query)
              leftTransition)
        have rightNext :
            simulatorNextState grammar iv right state query = next.1 := by
          unfold simulatorNextState
          exact congrArg Prod.fst
            (Option.get_of_eq_some
              (simulator_step_isSome grammar iv right state query)
              rightTransition)
        rw [Machine.runFrom_cons,
          show (simulatorMachine grammar iv right).step state query =
            simulatorStep grammar iv right state query by rfl,
          rightTransition]
        change
          some (simulatorAdvance grammar iv left
            (simulatorNextState grammar iv left state query) rest) =
          (simulatorMachine grammar iv right).runFrom next.1 rest
        rw [leftNext]
        have tailSafe :
            ReplaySafeFrom grammar iv left right next.1 rest := by
          simpa [leftNext] using safe.2
        exact inductionHypothesis next.1 tailSafe

/-- Replay safety identifies the complete state-and-answer transition at the
last query of every nonempty history. -/
theorem simulator_lastStep_eq_of_replaySafe [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) (history : List (Query C B X))
    (nonempty : history ≠ [])
    (safe : ReplaySafe grammar iv left right history) :
    (simulatorMachine grammar iv left).lastStep history nonempty =
      (simulatorMachine grammar iv right).lastStep history nonempty := by
  let front := history.dropLast
  let finalQuery := history.getLast nonempty
  have decomposed : front ++ [finalQuery] = history := by
    exact List.dropLast_append_getLast nonempty
  have safeDecomposed : ReplaySafeFrom grammar iv left right
      (initialState iv) (front ++ [finalQuery]) := by
    rw [decomposed]
    exact safe
  obtain ⟨frontSafe, finalSafe⟩ := replaySafeFrom_append grammar iv
    left right (initialState iv) front [finalQuery] safeDecomposed
  have finalAgreement : StepCoinsAgree grammar left right
      (simulatorAdvance grammar iv left (initialState iv) front)
      finalQuery := by
    simpa [ReplaySafeFrom] using finalSafe.1
  have finalStepEqual := simulatorStep_eq_of_activated_agreement
    grammar iv left right
      (simulatorAdvance grammar iv left (initialState iv) front)
      finalQuery finalAgreement.1 finalAgreement.2
  have leftFront :
      (simulatorMachine grammar iv left).runFrom (initialState iv) front =
        some (simulatorAdvance grammar iv left (initialState iv) front) :=
    simulator_runFrom_eq_some_advance grammar iv left (initialState iv) front
  have frontRunsEqual := simulator_runFrom_eq_of_replaySafe grammar iv
    left right (initialState iv) front frontSafe
  have rightFront :
      (simulatorMachine grammar iv right).runFrom (initialState iv) front =
        some (simulatorAdvance grammar iv left (initialState iv) front) :=
    frontRunsEqual.symm.trans leftFront
  unfold Machine.lastStep Machine.run
  change
    ((simulatorMachine grammar iv left).runFrom (initialState iv) front).bind
        (fun state => (simulatorMachine grammar iv left).step state finalQuery) =
      ((simulatorMachine grammar iv right).runFrom (initialState iv) front).bind
        (fun state => (simulatorMachine grammar iv right).step state finalQuery)
  rw [leftFront, rightFront]
  exact finalStepEqual

/-- Consequently every observable flattened answer on the replay-safe
history is identical. -/
theorem simulatorHistoryOutput_eq_of_replaySafe [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (left right : Coins C B X) (history : List (Query C B X))
    (nonempty : history ≠ [])
    (safe : ReplaySafe grammar iv left right history) :
    simulatorHistoryOutput grammar iv left history nonempty =
      simulatorHistoryOutput grammar iv right history nonempty := by
  have lastEqual := simulator_lastStep_eq_of_replaySafe grammar iv
    left right history nonempty safe
  have leftLastSome :
      ((simulatorMachine grammar iv left).lastStep history nonempty).isSome := by
    have runSome := Machine.run_isSome_of_stepTotal
      (simulatorMachine grammar iv left)
      (simulatorMachine_stepTotal grammar iv left) history
    rw [(simulatorMachine grammar iv left).run_eq_lastStep_map
      history nonempty] at runSome
    simpa using runSome
  have rightLastSome :
      ((simulatorMachine grammar iv right).lastStep history nonempty).isSome := by
    rw [← lastEqual]
    exact leftLastSome
  have resultEqual :
      ((simulatorMachine grammar iv left).lastStep history nonempty).get
          leftLastSome =
        ((simulatorMachine grammar iv right).lastStep history nonempty).get
          rightLastSome := by
    let leftResult :=
      ((simulatorMachine grammar iv left).lastStep history nonempty).get
        leftLastSome
    have leftTransition :
        (simulatorMachine grammar iv left).lastStep history nonempty =
          some leftResult :=
      Option.eq_some_of_isSome leftLastSome
    have rightTransition :
        (simulatorMachine grammar iv right).lastStep history nonempty =
          some leftResult :=
      lastEqual.symm.trans leftTransition
    exact (Option.get_of_eq_some leftLastSome leftTransition).trans
      (Option.get_of_eq_some rightLastSome rightTransition).symm
  unfold simulatorHistoryOutput PFunDDS.output DependentDDS.flatten
    Machine.toDDS
  simp only
  change
    (⟨(history.getLast nonempty).1,
      ((simulatorMachine grammar iv left).lastStep history nonempty).get
        leftLastSome |>.2⟩ : Reply C B X) =
    (⟨(history.getLast nonempty).1,
      ((simulatorMachine grammar iv right).lastStep history nonempty).get
        rightLastSome |>.2⟩ : Reply C B X)
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact congrArg Prod.snd resultEqual

/-- Observable fixed-history form of the terminal-exchange theorem. -/
theorem simulatorHistoryOutput_correlatedAugmented_eq_smartSwap
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (seed : Coins C B X) (history : List (Query C B X))
    (nonempty : history ≠ [])
    (terminalsDistinct : SmartTerminalsDistinct grammar iv
      (compressionOfTable seed.2) history)
    (linkConsistent : SmartLinkConsistent grammar iv
      (compressionOfTable seed.2) history seed.1) :
    simulatorHistoryOutput grammar iv
        (correlatedAugmentedCoins grammar iv seed) history nonempty =
      simulatorHistoryOutput grammar iv
        (smartSwapCoins grammar iv (compressionOfTable seed.2) history seed)
        history nonempty := by
  exact simulatorHistoryOutput_eq_of_replaySafe grammar iv _ _ history nonempty
    (replaySafe_correlatedAugmented_smartSwap grammar iv seed history
      terminalsDistinct linkConsistent)

end MDSimulator
end RandomSystemsModel
end SequenceHash
