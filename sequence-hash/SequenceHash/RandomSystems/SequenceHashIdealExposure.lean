import RandomSystems.CoordinateFunctional
import SequenceHash.RandomSystems.CachedDeferredSampling
import SequenceHash.RandomSystems.SequenceHashSmartCarrier

/-!
# Lazy compression exposure for the ideal SequenceHash simulator

This file refines one public ideal/simulator execution into compression-oracle
micro-steps.  Public steps that use only a repeated table entry or the ideal
oracle are performed silently.  Every genuine compression access—including
the hidden inner and outer computations attached to a first ideal-oracle
activation—is routed through one cache-aware oracle program.

The resulting state records the exact source coordinate of every critical
live value.  It is the bridge from the executable simulator to the generic
coordinate-functional graph bound; no probabilistic case split is encoded in
the simulator itself.
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

/-- Whether a critical state was returned at the public primitive interface
or was sampled only inside the passive construction audit. -/
inductive CriticalOrigin where
  | visible
  | hidden
deriving DecidableEq

/-- One fresh nonterminal compression assignment, with its semantic word when
the public parser already knows one and the exact microstep that produced its
value.  Public ordinary samples use the empty word as inert metadata: they are
still recorded because a later hidden path may reuse their cached value. -/
structure CriticalRecord (C B : Type u) where
  word : List B
  point : C × B
  value : C
  source : ℕ
  origin : CriticalOrigin
deriving DecidableEq

/-- One root first named by a loose public primitive query, together with the
microstep at which the query was answered.  The root itself is selected before
that step's raw compression answer is read. -/
structure LooseRootRecord (C : Type u) where
  value : C
  source : ℕ
deriving DecidableEq

/-- One first ideal-oracle activation after its hidden two-pass computation
has been exposed. -/
structure ExposedActivation (C B X : Type u) where
  input : X
  embedded : C
  terminal : C × B
  occupied : Option C
  realAnswer : C
deriving DecidableEq

/-- The next kind of compression micro-step.  `public` performs silent public
steps until an oracle access is required.  Inner outputs are all critical;
outer outputs are critical except for the final terminal output. -/
inductive ExposurePhase (C B X : Type u) where
  | idle
  | primitiveCall (point : C × B)
  | inner (input : X) (state : C) (pathPrefix : List B)
      (block : B) (rest : List B)
  | outer (input : X) (embedded state : C) (pathPrefix : List B)
      (block : B) (rest : List B)
  | done
deriving DecidableEq

/-- Complete finite control state of the exposure program.  `oracleTable`
contains hidden and public compression accesses, while `simulator.table`
contains only entries installed at the public primitive interface. -/
structure IdealExposureState (C B X Tag : Type u) where
  simulator : State C B X Tag
  transcript : List (Query C B X × Option (Reply C B X))
  remaining : ℕ
  clock : ℕ
  phase : ExposurePhase C B X
  oracleTable : C × B → Option C
  activated : Finset X
  auditQueue : List X
  critical : List (CriticalRecord C B)
  looseRoots : List (LooseRootRecord C)
  activations : List (ExposedActivation C B X)

/-- Initial exposure state for `rounds` public interaction rounds. -/
def initialIdealExposure [DecidableEq C] (iv : C) (rounds : ℕ) :
    IdealExposureState C B X Tag where
  simulator := initialState iv
  transcript := []
  remaining := rounds
  clock := 0
  phase := .idle
  oracleTable := fun _ => none
  activated := ∅
  auditQueue := []
  critical := []
  looseRoots := []
  activations := []

/-- Flatten one native answer at its active public interface. -/
def exposeReply (query : Query C B X) (answer : AnswerAt query) :
    Reply C B X :=
  ⟨query.1, answer⟩

/-- Total result of one executable simulator step. -/
def simulatorResult [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : Query C B X) :
    State C B X Tag × AnswerAt query :=
  (simulatorStep grammar iv coins state query).get
    (simulator_step_isSome grammar iv coins state query)

/-- A public step needs a compression-oracle answer exactly at a fresh
primitive point that is not a correctly linked outer terminal. -/
def publicCompressionPoint [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (state : State C B X Tag) :
    Query C B X → Option (C × B)
  | ⟨.eval, _input⟩ => none
  | ⟨.prim, point⟩ =>
      match state.table point with
      | some _answer => none
      | none =>
          match activatedPrimitiveInput grammar state point with
          | some _input => none
          | none => some point

/-- Semantic word produced by a fresh public compression call when that call
extends the live graph by a nonterminal state.  This repeats the executor's
native lookup/parser tree, so all parser constructors remain visible to Lean. -/
def publicCriticalWord [DecidableEq C] [DecidableEq B]
    (grammar : Grammar C B X Tag) (state : State C B X Tag)
    (point : C × B) : Option (List B) :=
  match state.table point with
  | some _answer => none
  | none =>
      match state.word point.1 with
      | none => none
      | some path =>
          let word := path ++ [point.2]
          match grammar.classifyWord word with
          | .innerPrefix => some word
          | .innerComplete _input => some word
          | .outerPrefix => some word
          | .outerComplete _tag _embedded => none
          | .invalid => none

/-- Root introduced by the executor's native loose-primitive branch. -/
def publicLooseRoot [DecidableEq C] [DecidableEq B]
    (state : State C B X Tag) (point : C × B) : Option C :=
  match state.table point with
  | some _answer => none
  | none =>
      match state.word point.1 with
      | some _path => none
      | none => some point.1

@[simp]
theorem publicCompressionPoint_eval [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (state : State C B X Tag) (input : X) :
    publicCompressionPoint grammar state ⟨.eval, input⟩ = none := by
  rfl

/-- Install every semantic compression access in the exposure cache. -/
def exposeOracleAnswer [DecidableEq C] [DecidableEq B]
    (state : IdealExposureState C B X Tag) (point : C × B) (answer : C) :
    IdealExposureState C B X Tag :=
  { state with
      oracleTable := Function.update state.oracleTable point (some answer) }

/-- Begin the nonempty hidden inner path at the public IV. -/
def beginInnerExposureAt
    (grammar : Grammar C B X Tag) (iv : C) (input : X)
    (state : IdealExposureState C B X Tag) :
    IdealExposureState C B X Tag :=
  match grammar.innerWord input with
  | [] => state
  | block :: rest =>
      { state with phase := .inner input iv [] block rest }

/-- Begin the nonempty hidden outer path once the inner endpoint is known. -/
def beginOuterExposure
    (grammar : Grammar C B X Tag) (iv embedded : C) (input : X)
    (state : IdealExposureState C B X Tag) :
    IdealExposureState C B X Tag :=
  match grammar.outerWord (grammar.tagOf input) embedded with
  | [] => state
  | block :: rest =>
      { state with phase := .outer input embedded iv [] block rest }

/-- Append a completed public step and, on a first ideal-oracle activation,
queue its hidden construction audit before the next public query. -/
def finishPublicStep [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (before : IdealExposureState C B X Tag)
    (query : Query C B X) (next : State C B X Tag × AnswerAt query) :
    IdealExposureState C B X Tag :=
  let base : IdealExposureState C B X Tag :=
    { before with
      simulator := next.1
      transcript := before.transcript ++ [(query, some (exposeReply query next.2))]
      remaining := before.remaining - 1
      phase := .idle }
  match activatedInput grammar before.simulator query with
  | none => base
  | some input =>
      if input ∈ before.activated then base
      else
        let activatedBase :=
          { base with activated := insert input before.activated }
        match query with
        | ⟨.prim, point⟩ =>
            { activatedBase with
              activations := activatedBase.activations ++
                [{ input := input
                   embedded := iv
                   terminal := point
                   occupied := before.simulator.table point
                   realAnswer := next.2 }] }
        | ⟨.eval, _queriedInput⟩ =>
            { activatedBase with
              auditQueue := activatedBase.auditQueue ++ [input] }

/-- Execute a public step that provably does not need the compression tape.
The dummy compression function is unreachable in this branch. -/
def silentPublicStep [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (state : IdealExposureState C B X Tag) (query : Query C B X) :
    IdealExposureState C B X Tag :=
  finishPublicStep grammar iv state query
    (simulatorResult grammar iv (dummy, fun _ => fallback)
      state.simulator query)

/-- Complete the hidden outer audit without sampling its terminal output.
In the ideal representative that output is exactly the already sampled
random-oracle value.  The terminal point and any earlier public occupant are
recorded for the occupied-link carrier, but terminal outputs never enter the
live-state tape. -/
def finishOuterExposure
    (dummy : X → C) (state : IdealExposureState C B X Tag)
    (input : X) (embedded chaining : C) (block : B) :
    IdealExposureState C B X Tag :=
  let point := (chaining, block)
  { state with
    phase := .idle
    activations := state.activations ++
      [{ input := input
         embedded := embedded
         terminal := point
         occupied := state.simulator.table point
         realAnswer := dummy input }] }

/-- Start the next deferred construction audit after the public interaction
has stopped.  Hidden paths cannot influence the ideal public transcript, so
postponing them is an exact representative change; it also fixes every loose
root before hidden critical states are sampled. -/
def beginNextAudit
    (grammar : Grammar C B X Tag) (iv : C)
    (state : IdealExposureState C B X Tag) :
    IdealExposureState C B X Tag :=
  match state.auditQueue with
  | [] => { state with phase := .done }
  | input :: rest =>
      beginInnerExposureAt grammar iv input
        { state with auditQueue := rest }

/-- Perform silent public progress.  The fuel is consumed only when a public
round is completed without reading the compression oracle. -/
def prepareIdealExposure [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X)) :
    ℕ → IdealExposureState C B X Tag → IdealExposureState C B X Tag
  | 0, state => state
  | fuel + 1, state =>
      match state.phase with
      | .done => state
      | .primitiveCall _point => state
      | .inner _input _chaining _pathPrefix _block _rest => state
      | .outer input embedded chaining _pathPrefix block rest =>
          match rest with
          | [] =>
              prepareIdealExposure grammar iv fallback dummy environment fuel
                (finishOuterExposure dummy state input embedded chaining block)
          | _nextBlock :: _tail => state
      | .idle =>
          match state.remaining with
          | 0 => beginNextAudit grammar iv state
          | _remaining + 1 =>
              match environment (PFunDDS.transcriptOutputs state.transcript) with
              | none =>
                  beginNextAudit grammar iv { state with remaining := 0 }
              | some query =>
                  match publicCompressionPoint grammar state.simulator query with
                  | some point => { state with phase := .primitiveCall point }
                  | none =>
                      prepareIdealExposure grammar iv fallback dummy environment
                        fuel
                        (silentPublicStep grammar iv fallback dummy state query)

/-- Normalize a control state to its next compression access or termination. -/
def normalizeIdealExposure [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) : IdealExposureState C B X Tag :=
  prepareIdealExposure grammar iv fallback dummy environment
    (state.remaining + 2) state

/-- Point requested by a normalized exposure phase; termination uses one
fixed padding point whose answer is ignored. -/
def idealExposurePoint [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) : C × B :=
  match (normalizeIdealExposure grammar iv fallbackC dummy environment state).phase with
  | .primitiveCall point => point
  | .inner _input chaining _pathPrefix block _rest => (chaining, block)
  | .outer _input _embedded chaining _pathPrefix block _rest => (chaining, block)
  | .idle => (fallbackC, fallbackB)
  | .done => (fallbackC, fallbackB)

/-- Advance one normalized compression phase.  The match is deliberately
exhaustive: every genuine public or hidden compression access is represented
by one of the three live constructors, while `idle` and `done` are padding
branches whose raw answer is ignored. -/
def idealExposureStep [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) (answer : C) :
    IdealExposureState C B X Tag :=
  let normalized :=
    normalizeIdealExposure grammar iv fallbackC dummy environment state
  match normalized.phase with
  | .idle => { normalized with clock := normalized.clock + 1 }
  | .done => { normalized with clock := normalized.clock + 1 }
  | .primitiveCall point =>
      let query : Query C B X := ⟨.prim, point⟩
      let exposed := exposeOracleAnswer normalized point answer
      let recordedSample :=
        match normalized.oracleTable point with
        | some _cached => exposed
        | none =>
            { exposed with
              critical := exposed.critical ++
                [{ word := (publicCriticalWord grammar normalized.simulator
                      point).getD [],
                   point := point, value := answer,
                   source := normalized.clock, origin := .visible }] }
      let recorded :=
        match publicLooseRoot normalized.simulator point with
        | none => recordedSample
        | some root =>
            { recordedSample with
              looseRoots := recordedSample.looseRoots ++
                [{ value := root, source := normalized.clock }] }
      { (finishPublicStep grammar iv recorded query
          (simulatorResult grammar iv (dummy, fun _ => answer)
            normalized.simulator query)) with
        clock := normalized.clock + 1 }
  | .inner input chaining pathPrefix block rest =>
      let point := (chaining, block)
      let word := pathPrefix ++ [block]
      let exposed := exposeOracleAnswer normalized point answer
      let recorded :=
        match normalized.oracleTable point with
        | some _cached => exposed
        | none =>
            { exposed with
              critical := exposed.critical ++
                [{ word := word, point := point, value := answer,
                   source := normalized.clock, origin := .hidden }] }
      match rest with
      | [] =>
          { (beginOuterExposure grammar iv answer input recorded) with
            clock := normalized.clock + 1 }
      | nextBlock :: tail =>
          { recorded with
            clock := normalized.clock + 1
            phase := .inner input answer word nextBlock tail }
  | .outer input embedded chaining pathPrefix block rest =>
      let point := (chaining, block)
      let word := pathPrefix ++ [block]
      let exposed := exposeOracleAnswer normalized point answer
      match rest with
      | [] =>
          { (finishOuterExposure dummy normalized input embedded chaining block) with
            clock := normalized.clock + 1 }
      | nextBlock :: tail =>
          let recorded : IdealExposureState C B X Tag :=
            match normalized.oracleTable point with
            | some _cached => exposed
            | none =>
                { exposed with
                  critical := exposed.critical ++
                    [{ word := word, point := point, value := answer,
                       source := normalized.clock, origin := .hidden }] }
          { recorded with
              clock := normalized.clock + 1
              phase := .outer input embedded answer word nextBlock tail }

/-- The complete ideal/simulator execution viewed as a cache-aware adaptive
compression program. -/
def idealExposureProgram [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X)) :
    CachedOracleProgram (C × B) C (IdealExposureState C B X Tag) where
  query := idealExposurePoint grammar iv fallbackC fallbackB dummy environment
  step := idealExposureStep grammar iv fallbackC dummy environment

/-! ## Sampling-clock invariants -/

@[simp]
theorem beginInnerExposureAt_clock
    (grammar : Grammar C B X Tag) (iv : C) (input : X)
    (state : IdealExposureState C B X Tag) :
    (beginInnerExposureAt grammar iv input state).clock = state.clock := by
  unfold beginInnerExposureAt
  split <;> rfl

@[simp]
theorem beginInnerExposureAt_critical
    (grammar : Grammar C B X Tag) (iv : C) (input : X)
    (state : IdealExposureState C B X Tag) :
    (beginInnerExposureAt grammar iv input state).critical = state.critical := by
  unfold beginInnerExposureAt
  split <;> rfl

@[simp]
theorem beginOuterExposure_critical
    (grammar : Grammar C B X Tag) (iv embedded : C) (input : X)
    (state : IdealExposureState C B X Tag) :
    (beginOuterExposure grammar iv embedded input state).critical =
      state.critical := by
  unfold beginOuterExposure
  split <;> rfl

@[simp]
theorem exposeOracleAnswer_critical [DecidableEq C] [DecidableEq B]
    (state : IdealExposureState C B X Tag) (point : C × B) (answer : C) :
    (exposeOracleAnswer state point answer).critical = state.critical := by
  rfl

@[simp]
theorem finishOuterExposure_critical
    (dummy : X → C) (state : IdealExposureState C B X Tag)
    (input : X) (embedded chaining : C) (block : B) :
    (finishOuterExposure dummy state input embedded chaining block).critical =
      state.critical := by
  rfl

@[simp]
theorem beginNextAudit_clock
    (grammar : Grammar C B X Tag) (iv : C)
    (state : IdealExposureState C B X Tag) :
    (beginNextAudit grammar iv state).clock = state.clock := by
  unfold beginNextAudit
  split
  · rfl
  · simp

@[simp]
theorem beginNextAudit_critical
    (grammar : Grammar C B X Tag) (iv : C)
    (state : IdealExposureState C B X Tag) :
    (beginNextAudit grammar iv state).critical = state.critical := by
  unfold beginNextAudit
  split
  · rfl
  · simp

@[simp]
theorem finishPublicStep_clock [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (state : IdealExposureState C B X Tag) (query : Query C B X)
    (next : State C B X Tag × AnswerAt query) :
    (finishPublicStep grammar iv state query next).clock = state.clock := by
  unfold finishPublicStep
  split
  next => rfl
  next input =>
    split
    next => rfl
    next =>
      rcases query with ⟨interface, payload⟩
      cases interface with
      | prim => rfl
      | eval => simp

@[simp]
theorem finishPublicStep_critical [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C)
    (state : IdealExposureState C B X Tag) (query : Query C B X)
    (next : State C B X Tag × AnswerAt query) :
    (finishPublicStep grammar iv state query next).critical =
      state.critical := by
  unfold finishPublicStep
  split
  next => rfl
  next input =>
    split
    next => rfl
    next =>
      rcases query with ⟨interface, payload⟩
      cases interface with
      | prim => rfl
      | eval => simp

@[simp]
theorem silentPublicStep_clock [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (state : IdealExposureState C B X Tag) (query : Query C B X) :
    (silentPublicStep grammar iv fallback dummy state query).clock =
      state.clock := by
  simp [silentPublicStep]

@[simp]
theorem silentPublicStep_critical [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (state : IdealExposureState C B X Tag) (query : Query C B X) :
    (silentPublicStep grammar iv fallback dummy state query).critical =
      state.critical := by
  simp [silentPublicStep]

/-- Silent normalization consumes no compression coordinate. -/
theorem prepareIdealExposure_clock [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X)) :
    ∀ fuel (state : IdealExposureState C B X Tag),
      (prepareIdealExposure grammar iv fallback dummy environment fuel state).clock =
        state.clock := by
  intro fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel inductionHypothesis =>
      intro state
      cases phase : state.phase with
      | idle =>
          cases remaining : state.remaining with
          | zero => simp [prepareIdealExposure, phase, remaining]
          | succ remaining =>
              cases issued :
                  environment (PFunDDS.transcriptOutputs state.transcript) with
              | none =>
                  simp [prepareIdealExposure, phase, remaining, issued]
              | some query =>
                  cases pointLookup :
                      publicCompressionPoint grammar state.simulator query with
                  | some point =>
                      simp [prepareIdealExposure, phase, remaining, issued,
                        pointLookup]
                  | none =>
                      simp only [prepareIdealExposure, phase, remaining,
                        issued, pointLookup]
                      rw [inductionHypothesis]
                      exact silentPublicStep_clock grammar iv fallback dummy
                        state query
      | primitiveCall point => simp [prepareIdealExposure, phase]
      | inner input chaining pathPrefix block rest =>
          simp [prepareIdealExposure, phase]
      | outer input embedded chaining pathPrefix block rest =>
          cases rest with
          | nil =>
              simp [prepareIdealExposure, phase, inductionHypothesis,
                finishOuterExposure]
          | cons nextBlock tail => simp [prepareIdealExposure, phase]
      | done => simp [prepareIdealExposure, phase]

/-- Silent normalization neither creates nor removes critical records. -/
theorem prepareIdealExposure_critical [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X)) :
    ∀ fuel (state : IdealExposureState C B X Tag),
      (prepareIdealExposure grammar iv fallback dummy environment fuel state).critical =
        state.critical := by
  intro fuel
  induction fuel with
  | zero => intro state; rfl
  | succ fuel inductionHypothesis =>
      intro state
      cases phase : state.phase with
      | idle =>
          cases remaining : state.remaining with
          | zero => simp [prepareIdealExposure, phase, remaining]
          | succ remaining =>
              cases issued :
                  environment (PFunDDS.transcriptOutputs state.transcript) with
              | none =>
                  simp [prepareIdealExposure, phase, remaining, issued]
              | some query =>
                  cases pointLookup :
                      publicCompressionPoint grammar state.simulator query with
                  | some point =>
                      simp [prepareIdealExposure, phase, remaining, issued,
                        pointLookup]
                  | none =>
                      simp only [prepareIdealExposure, phase, remaining,
                        issued, pointLookup]
                      rw [inductionHypothesis]
                      exact silentPublicStep_critical grammar iv fallback dummy
                        state query
      | primitiveCall point => simp [prepareIdealExposure, phase]
      | inner input chaining pathPrefix block rest =>
          simp [prepareIdealExposure, phase]
      | outer input embedded chaining pathPrefix block rest =>
          cases rest with
          | nil =>
              simp [prepareIdealExposure, phase, inductionHypothesis,
                finishOuterExposure]
          | cons nextBlock tail => simp [prepareIdealExposure, phase]
      | done => simp [prepareIdealExposure, phase]

@[simp]
theorem normalizeIdealExposure_clock [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) :
    (normalizeIdealExposure grammar iv fallback dummy environment state).clock =
      state.clock := by
  exact prepareIdealExposure_clock grammar iv fallback dummy environment _ state

@[simp]
theorem normalizeIdealExposure_critical [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) :
    (normalizeIdealExposure grammar iv fallback dummy environment state).critical =
      state.critical := by
  exact prepareIdealExposure_critical grammar iv fallback dummy environment _ state

/-- One raw compression coordinate is consumed by every program step,
including the post-termination padding steps. -/
@[simp]
theorem idealExposureStep_clock [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) (answer : C) :
    (idealExposureStep grammar iv fallback dummy environment state answer).clock =
      state.clock + 1 := by
  simp only [idealExposureStep]
  generalize normalizedEquality :
      normalizeIdealExposure grammar iv fallback dummy environment state =
        normalized
  have normalizedClock : normalized.clock = state.clock := by
    rw [← normalizedEquality]
    exact normalizeIdealExposure_clock grammar iv fallback dummy environment state
  cases phase : normalized.phase with
  | idle => simp [normalizedClock]
  | done => simp [normalizedClock]
  | primitiveCall point => simp [normalizedClock]
  | inner input chaining pathPrefix block rest =>
      cases rest <;>
        simp [beginOuterExposure, normalizedClock]
  | outer input embedded chaining pathPrefix block rest =>
      cases rest <;>
        simp [finishOuterExposure, normalizedClock]

/-- Whether the next normalized oracle answer creates a fresh nonterminal
compression assignment.  All public primitive samples are included: even an
ordinary output may later be reused by a hidden construction path.  Cached
accesses and final outer terminals are excluded. -/
def idealExposureCritical [DecidableEq C] [DecidableEq B]
    (grammar : Grammar C B X Tag) (state : IdealExposureState C B X Tag) :
    Bool :=
  match state.phase with
  | .primitiveCall point =>
      (state.oracleTable point).isNone
  | .inner _input chaining _pathPrefix block _rest =>
      (state.oracleTable (chaining, block)).isNone
  | .outer _input _embedded chaining _pathPrefix block rest =>
      !rest.isEmpty && (state.oracleTable (chaining, block)).isNone
  | .idle => false
  | .done => false

/-- One exposure step appends exactly one record precisely in a critical
phase. -/
theorem idealExposureStep_critical_length [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) (answer : C) :
    (idealExposureStep grammar iv fallback dummy environment state answer).critical.length =
      state.critical.length +
        if idealExposureCritical grammar
            (normalizeIdealExposure grammar iv fallback dummy environment state)
        then 1 else 0 := by
  simp only [idealExposureStep]
  generalize normalizedEquality :
      normalizeIdealExposure grammar iv fallback dummy environment state =
        normalized
  have normalizedCritical : normalized.critical = state.critical := by
    rw [← normalizedEquality]
    exact normalizeIdealExposure_critical grammar iv fallback dummy environment state
  cases phase : normalized.phase with
  | idle => simp [idealExposureCritical, phase, normalizedCritical]
  | done => simp [idealExposureCritical, phase, normalizedCritical]
  | primitiveCall point =>
      cases oracleLookup : normalized.oracleTable point <;>
        cases criticalWord :
            publicCriticalWord grammar normalized.simulator point <;>
        cases looseRoot : publicLooseRoot normalized.simulator point <;>
        simp [idealExposureCritical, phase, oracleLookup, criticalWord,
          looseRoot, normalizedCritical]
  | inner input chaining pathPrefix block rest =>
      cases oracleLookup : normalized.oracleTable (chaining, block) <;>
        cases rest <;>
        simp [idealExposureCritical, phase, oracleLookup,
          normalizedCritical]
  | outer input embedded chaining pathPrefix block rest =>
      cases oracleLookup : normalized.oracleTable (chaining, block) <;>
        cases rest <;>
        simp [idealExposureCritical, phase, oracleLookup,
          normalizedCritical]

/-- The number of critical records never exceeds the number of consumed raw
coordinates. -/
theorem idealExposureStep_critical_le_clock [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) (answer : C)
    (bounded : state.critical.length ≤ state.clock) :
    (idealExposureStep grammar iv fallback dummy environment state answer).critical.length ≤
      (idealExposureStep grammar iv fallback dummy environment state answer).clock := by
  rw [idealExposureStep_critical_length, idealExposureStep_clock]
  split <;> omega

theorem idealExposureStep_critical_length_mono [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallback : C) (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) (answer : C) :
    state.critical.length ≤
      (idealExposureStep grammar iv fallback dummy environment state answer).critical.length := by
  rw [idealExposureStep_critical_length]
  split <;> omega

/-- A cached exposure step cannot decrease the critical-record count. -/
theorem cachedIdealExposureStep_critical_length_mono [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (execution : CachedExecution (C × B) C
      (IdealExposureState C B X Tag)) (raw : C) :
    execution.control.critical.length ≤
      (cachedOracleStep
        (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
        execution raw).control.critical.length := by
  simp only [cachedOracleStep]
  split <;>
    exact idealExposureStep_critical_length_mono grammar iv fallbackC dummy
      environment execution.control _

/-- The state immediately after any indexed raw answer has no more critical
records than the state after the complete vector. -/
theorem cachedIdealExposure_critical_after_le [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) : ∀ {m : ℕ} (values : Fin (m + 1) → C)
      (index : Fin (m + 1)),
      let program :=
        idealExposureProgram grammar iv fallbackC fallbackB dummy environment
      let before := cachedOracleRun program (initialIdealExposure iv rounds)
        (finStrictPrefix values index)
      (cachedOracleStep program before (values index)).control.critical.length ≤
        (cachedOracleRun program (initialIdealExposure iv rounds) values).control.critical.length := by
  intro m
  induction m with
  | zero =>
      intro values index
      have indexLast : index = Fin.last 0 := by
        apply Fin.ext
        omega
      subst index
      simpa only [cachedOracleRun_snoc] using le_rfl
  | succ m inductionHypothesis =>
      intro values index
      rcases Fin.eq_castSucc_or_eq_last index with ⟨earlier, rfl⟩ | rfl
      · let program :=
          idealExposureProgram grammar iv fallbackC fallbackB dummy environment
        let initial : IdealExposureState C B X Tag :=
          initialIdealExposure iv rounds
        have earlierBound := inductionHypothesis (Fin.init values) earlier
        have finalStep := cachedIdealExposureStep_critical_length_mono
          grammar iv fallbackC fallbackB dummy environment
          (cachedOracleRun program initial (Fin.init values))
          (values (Fin.last (m + 1)))
        change
          (cachedOracleStep program
              (cachedOracleRun program initial
                (finStrictPrefix values earlier.castSucc))
              (values earlier.castSucc)).control.critical.length ≤
            (cachedOracleRun program initial values).control.critical.length
        have beforeEqual :
            finStrictPrefix values earlier.castSucc =
              finStrictPrefix (Fin.init values) earlier := by
          exact finStrictPrefix_castSucc values earlier
        rw [beforeEqual]
        calc
          _ ≤ (cachedOracleRun program initial
                (Fin.init values)).control.critical.length := earlierBound
          _ ≤ (cachedOracleStep program
                (cachedOracleRun program initial (Fin.init values))
                (values (Fin.last (m + 1)))).control.critical.length :=
            finalStep
          _ = (cachedOracleRun program initial values).control.critical.length := by
            rw [← cachedOracleRun_snoc]
            exact congrArg
              (fun vector =>
                (cachedOracleRun program initial vector).control.critical.length)
              (Fin.snoc_init_self values)
      · change
          (cachedOracleStep
              (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
              (cachedOracleRun
                (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
                (initialIdealExposure iv rounds) (Fin.init values))
              (values (Fin.last (m + 1)))).control.critical.length ≤
            (cachedOracleRun
              (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
              (initialIdealExposure iv rounds) values).control.critical.length
        simpa only [cachedOracleRun_snoc] using le_rfl

/-- Length-polymorphic form of `cachedIdealExposure_critical_after_le`. -/
theorem cachedIdealExposure_critical_after_le' [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) {m : ℕ} (values : Fin m → C) (index : Fin m) :
    let program :=
      idealExposureProgram grammar iv fallbackC fallbackB dummy environment
    let before := cachedOracleRun program (initialIdealExposure iv rounds)
      (finStrictPrefix values index)
    (cachedOracleStep program before (values index)).control.critical.length ≤
      (cachedOracleRun program (initialIdealExposure iv rounds) values).control.critical.length := by
  cases m with
  | zero => exact Fin.elim0 index
  | succ m =>
      exact cachedIdealExposure_critical_after_le grammar iv fallbackC
        fallbackB dummy environment rounds values index

/-- Whenever the earlier prefix is critical, its critical rank is strictly
smaller than the rank at every later raw coordinate. -/
theorem cachedIdealExposure_critical_rank_lt [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) {m : ℕ} (values : Fin m → C)
    (earlier later : Fin m) (before : earlier.1 < later.1)
    (earlierCritical :
      idealExposureCritical grammar
        (normalizeIdealExposure grammar iv fallbackC dummy environment
          (cachedOracleRun
            (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
            (initialIdealExposure iv rounds)
            (finStrictPrefix values earlier)).control) = true) :
    (cachedOracleRun
      (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
      (initialIdealExposure iv rounds)
      (finStrictPrefix values earlier)).control.critical.length <
    (cachedOracleRun
      (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
      (initialIdealExposure iv rounds)
      (finStrictPrefix values later)).control.critical.length := by
  let program :=
    idealExposureProgram grammar iv fallbackC fallbackB dummy environment
  let initial : IdealExposureState C B X Tag := initialIdealExposure iv rounds
  let earlierExecution := cachedOracleRun program initial
    (finStrictPrefix values earlier)
  let laterValues := finStrictPrefix values later
  let earlierInside : Fin later.1 := ⟨earlier.1, before⟩
  have prefixEqual :
      finStrictPrefix laterValues earlierInside =
        finStrictPrefix values earlier := by
    funext index
    rfl
  have valueEqual : laterValues earlierInside = values earlier := by
    rfl
  have afterLe := cachedIdealExposure_critical_after_le' grammar iv fallbackC
    fallbackB dummy environment rounds laterValues earlierInside
  change
    (cachedOracleStep program
      (cachedOracleRun program initial
        (finStrictPrefix laterValues earlierInside))
      (laterValues earlierInside)).control.critical.length ≤
        (cachedOracleRun program initial laterValues).control.critical.length at afterLe
  rw [prefixEqual, valueEqual] at afterLe
  have stepIncrease :
      (cachedOracleStep program earlierExecution
        (values earlier)).control.critical.length =
          earlierExecution.control.critical.length + 1 := by
    simp only [cachedOracleStep]
    split <;>
      change (idealExposureStep grammar iv fallbackC dummy environment
          earlierExecution.control _).critical.length = _ <;>
      rw [idealExposureStep_critical_length, earlierCritical] <;>
      rfl
  change earlierExecution.control.critical.length <
    (cachedOracleRun program initial laterValues).control.critical.length
  change
    (cachedOracleStep program earlierExecution
      (values earlier)).control.critical.length ≤
        (cachedOracleRun program initial laterValues).control.critical.length at afterLe
  omega

/-! ## A critical-rank random tape -/

/-- Disjoint coordinates for critical live states, ordinary first
compression accesses, and repeated-access padding. -/
inductive ExposureTapeCoordinate (budget : ℕ) where
  | critical (rank : Fin (budget + 1))
  | ordinary (time : Fin (budget + 1))
  | padding (time : Fin (budget + 1))
deriving DecidableEq, Fintype

/-- Relabel the raw cached-execution tape.  Every fresh critical access uses
its microstep clock; ordinary accesses and repeats use the same clock in
disjoint summands.  Indexing critical values by time (rather than by their
list rank) makes a loose root at time `i` visibly independent of every later
critical coordinate `j`. -/
def idealExposureTapeSchedule [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds budget : ℕ) : AdaptiveSchedule (ExposureTapeCoordinate budget) C where
  next := fun {m} values =>
    let program :=
      idealExposureProgram grammar iv fallbackC fallbackB dummy environment
    let execution := cachedOracleRun program
      (initialIdealExposure iv rounds) values
    let point := program.query execution.control
    match execution.cache point with
    | some _answer =>
        .padding (Fin.ofNat (budget + 1) execution.control.clock)
    | none =>
        if idealExposureCritical grammar
            (normalizeIdealExposure grammar iv fallbackC dummy environment
              execution.control) then
          .critical
            (Fin.ofNat (budget + 1) execution.control.clock)
        else
          .ordinary (Fin.ofNat (budget + 1) execution.control.clock)

@[simp]
theorem idealExposureTapeSchedule_point [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds budget : ℕ) {m : ℕ} (values : Fin m → C)
    (index : Fin m) :
    adaptivePointAt
        (idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
          environment rounds budget) values index =
      let program :=
        idealExposureProgram grammar iv fallbackC fallbackB dummy environment
      let execution := cachedOracleRun program (initialIdealExposure iv rounds)
        (finStrictPrefix values index)
      let point := program.query execution.control
      match execution.cache point with
      | some _answer =>
          .padding (Fin.ofNat (budget + 1) execution.control.clock)
      | none =>
            if idealExposureCritical grammar
                (normalizeIdealExposure grammar iv fallbackC dummy environment
                  execution.control) then
              .critical
              (Fin.ofNat (budget + 1) execution.control.clock)
          else
            .ordinary (Fin.ofNat (budget + 1) execution.control.clock) := by
  rfl

/-- After `m` cached microsteps, the exposure clock is exactly `m`. -/
@[simp]
theorem cachedIdealExposure_clock [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) {m : ℕ} (values : Fin m → C) :
    (cachedOracleRun
      (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
      (initialIdealExposure iv rounds) values).control.clock = m := by
  induction m with
  | zero => rfl
  | succ m inductionHypothesis =>
      rw [show values = Fin.snoc (Fin.init values) (values (Fin.last m)) by
        exact (Fin.snoc_init_self values).symm]
      rw [cachedOracleRun_snoc]
      let previous := cachedOracleRun
        (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
        (initialIdealExposure iv rounds) (Fin.init values)
      have previousClock : previous.control.clock = m :=
        inductionHypothesis (Fin.init values)
      change (cachedOracleStep
        (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
        previous (values (Fin.last m))).control.clock = m + 1
      cases lookup : previous.cache
          ((idealExposureProgram grammar iv fallbackC fallbackB dummy environment).query
            previous.control) with
      | none =>
          simp only [cachedOracleStep, lookup]
          change (idealExposureStep grammar iv fallbackC dummy environment
            previous.control (values (Fin.last m))).clock = m + 1
          rw [idealExposureStep_clock, previousClock]
      | some cached =>
          simp only [cachedOracleStep, lookup]
          change (idealExposureStep grammar iv fallbackC dummy environment
            previous.control cached).clock = m + 1
          rw [idealExposureStep_clock, previousClock]

/-- The final critical-record count is bounded by the raw-tape budget. -/
theorem cachedIdealExposure_critical_length_le [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds : ℕ) {m : ℕ} (values : Fin m → C) :
    (cachedOracleRun
      (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
      (initialIdealExposure iv rounds) values).control.critical.length ≤ m := by
  induction m with
  | zero => simp [cachedOracleRun, initialCachedExecution,
      initialIdealExposure]
  | succ m inductionHypothesis =>
      rw [show values = Fin.snoc (Fin.init values) (values (Fin.last m)) by
        exact (Fin.snoc_init_self values).symm]
      rw [cachedOracleRun_snoc]
      let previous := cachedOracleRun
        (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
        (initialIdealExposure iv rounds) (Fin.init values)
      have previousBound : previous.control.critical.length ≤
          previous.control.clock := by
        rw [cachedIdealExposure_clock]
        exact inductionHypothesis (Fin.init values)
      have close (sample : C) :
          (idealExposureStep grammar iv fallbackC dummy environment
            previous.control sample).critical.length ≤ m + 1 := by
        apply le_trans
          (idealExposureStep_critical_le_clock grammar iv fallbackC dummy
            environment previous.control sample previousBound)
        rw [idealExposureStep_clock, cachedIdealExposure_clock]
      change (cachedOracleStep
        (idealExposureProgram grammar iv fallbackC fallbackB dummy environment)
        previous (values (Fin.last m))).control.critical.length ≤ m + 1
      cases lookup : previous.cache
          ((idealExposureProgram grammar iv fallbackC fallbackB dummy environment).query
            previous.control) with
      | none =>
          simpa only [cachedOracleStep, lookup] using
            close (values (Fin.last m))
      | some cached =>
          simpa only [cachedOracleStep, lookup] using close cached

theorem finOfNat_eq_of_lt {modulus left right : ℕ} [NeZero modulus]
    (leftBound : left < modulus) (rightBound : right < modulus)
    (equal : Fin.ofNat modulus left = Fin.ofNat modulus right) :
    left = right := by
  have valuesEqual := congrArg Fin.val equal
  simpa [Fin.ofNat, Nat.mod_eq_of_lt leftBound,
    Nat.mod_eq_of_lt rightBound] using valuesEqual

/-- The critical-rank relabeling is pointwise fresh.  Critical coordinates
are separated by the strict rank theorem; ordinary and padding coordinates
carry their distinct microstep clocks. -/
theorem idealExposureTapeSchedule_fresh [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds budget : ℕ) (values : Fin budget → C) :
    FreshAt
      (idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
        environment rounds budget) values := by
  intro left right pointEqual
  by_contra indexDifferent
  have valueDifferent : left.1 ≠ right.1 := by
    intro equal
    exact indexDifferent (Fin.ext equal)
  have noCollision : ∀ {earlier later : Fin budget},
      earlier.1 < later.1 →
      adaptivePointAt
          (idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
            environment rounds budget) values earlier ≠
        adaptivePointAt
          (idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
            environment rounds budget) values later := by
    intro earlier later earlierBefore collision
    let program :=
      idealExposureProgram grammar iv fallbackC fallbackB dummy environment
    let initial : IdealExposureState C B X Tag := initialIdealExposure iv rounds
    let earlierExecution := cachedOracleRun program initial
      (finStrictPrefix values earlier)
    let laterExecution := cachedOracleRun program initial
      (finStrictPrefix values later)
    let earlierPoint := program.query earlierExecution.control
    let laterPoint := program.query laterExecution.control
    have earlierClock : earlierExecution.control.clock = earlier.1 := by
      exact cachedIdealExposure_clock grammar iv fallbackC fallbackB dummy
        environment rounds (finStrictPrefix values earlier)
    have laterClock : laterExecution.control.clock = later.1 := by
      exact cachedIdealExposure_clock grammar iv fallbackC fallbackB dummy
        environment rounds (finStrictPrefix values later)
    have earlierClockBound : earlierExecution.control.clock < budget + 1 := by
      rw [earlierClock]
      omega
    have laterClockBound : laterExecution.control.clock < budget + 1 := by
      rw [laterClock]
      omega
    rw [idealExposureTapeSchedule_point,
      idealExposureTapeSchedule_point] at collision
    change
      (match earlierExecution.cache earlierPoint with
        | some _answer =>
            ExposureTapeCoordinate.padding
              (Fin.ofNat (budget + 1) earlierExecution.control.clock)
        | none =>
            if idealExposureCritical grammar
                (normalizeIdealExposure grammar iv fallbackC dummy environment
                  earlierExecution.control) then
              ExposureTapeCoordinate.critical
                (Fin.ofNat (budget + 1)
                  earlierExecution.control.clock)
            else
              ExposureTapeCoordinate.ordinary
                (Fin.ofNat (budget + 1) earlierExecution.control.clock)) =
      (match laterExecution.cache laterPoint with
        | some _answer =>
            ExposureTapeCoordinate.padding
              (Fin.ofNat (budget + 1) laterExecution.control.clock)
        | none =>
            if idealExposureCritical grammar
                (normalizeIdealExposure grammar iv fallbackC dummy environment
                  laterExecution.control) then
              ExposureTapeCoordinate.critical
                (Fin.ofNat (budget + 1)
                  laterExecution.control.clock)
            else
              ExposureTapeCoordinate.ordinary
                (Fin.ofNat (budget + 1) laterExecution.control.clock)) at collision
    cases earlierCache : earlierExecution.cache earlierPoint with
    | some earlierAnswer =>
        cases laterCache : laterExecution.cache laterPoint with
        | some laterAnswer =>
            rw [earlierCache, laterCache] at collision
            have timeEqual := ExposureTapeCoordinate.padding.inj collision
            have clockEqual := finOfNat_eq_of_lt earlierClockBound
              laterClockBound timeEqual
            omega
        | none =>
            cases laterCritical : idealExposureCritical grammar
                (normalizeIdealExposure grammar iv fallbackC dummy environment
                  laterExecution.control) <;>
              simp [earlierCache, laterCache, laterCritical] at collision
    | none =>
        cases laterCache : laterExecution.cache laterPoint with
        | some laterAnswer =>
            cases earlierCritical : idealExposureCritical grammar
                (normalizeIdealExposure grammar iv fallbackC dummy environment
                  earlierExecution.control) <;>
              simp [earlierCache, laterCache, earlierCritical] at collision
        | none =>
            cases earlierCritical : idealExposureCritical grammar
                (normalizeIdealExposure grammar iv fallbackC dummy environment
                  earlierExecution.control) with
            | false =>
                cases laterCritical : idealExposureCritical grammar
                    (normalizeIdealExposure grammar iv fallbackC dummy environment
                      laterExecution.control) with
                | false =>
                    rw [earlierCache, laterCache, earlierCritical,
                      laterCritical] at collision
                    have timeEqual := ExposureTapeCoordinate.ordinary.inj collision
                    have clockEqual := finOfNat_eq_of_lt earlierClockBound
                      laterClockBound timeEqual
                    omega
                | true =>
                    simp [earlierCache, laterCache, earlierCritical,
                      laterCritical] at collision
            | true =>
                cases laterCritical : idealExposureCritical grammar
                    (normalizeIdealExposure grammar iv fallbackC dummy environment
                      laterExecution.control) with
                | false =>
                    simp [earlierCache, laterCache, earlierCritical,
                      laterCritical] at collision
                | true =>
                    rw [earlierCache, laterCache, earlierCritical,
                      laterCritical] at collision
                    have timeEqual :=
                      ExposureTapeCoordinate.critical.inj collision
                    have clockEqual := finOfNat_eq_of_lt earlierClockBound
                      laterClockBound timeEqual
                    omega
  rcases Nat.lt_or_gt_of_ne valueDifferent with earlierBefore | laterBefore
  · exact noCollision earlierBefore pointEqual
  · exact noCollision laterBefore pointEqual.symm

/-- Changing the critical tape coordinate labeled by time `j` cannot affect
any raw answer strictly before time `j`.  The schedule can select a critical
coordinate only with its current clock, while ordinary and padding accesses
live in disjoint constructors. -/
theorem adaptiveRun_eq_before_critical_time [DecidableEq C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds budget : ℕ)
    (left right : ExposureTapeCoordinate budget → C)
    (time : Fin budget)
    (agree : ∀ coordinate,
      coordinate ≠ ExposureTapeCoordinate.critical time.castSucc →
        left coordinate = right coordinate) :
    ∀ m (before : m ≤ time.1),
      adaptiveRun
          (idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
            environment rounds budget) left m =
        adaptiveRun
          (idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
            environment rounds budget) right m := by
  intro m before
  induction m with
  | zero => rfl
  | succ m inductionHypothesis =>
      have strict : m < time.1 := by omega
      have previous := inductionHypothesis (by omega)
      rw [adaptiveRun_succ, adaptiveRun_succ, previous]
      congr 1
      apply agree
      let values := adaptiveRun
        (idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
          environment rounds budget) right m
      let program :=
        idealExposureProgram grammar iv fallbackC fallbackB dummy environment
      let execution := cachedOracleRun program
        (initialIdealExposure iv rounds) values
      let point := program.query execution.control
      have clock : execution.control.clock = m := by
        exact cachedIdealExposure_clock grammar iv fallbackC fallbackB dummy
          environment rounds values
      change
        (match execution.cache point with
          | some _answer =>
              ExposureTapeCoordinate.padding
                (Fin.ofNat (budget + 1) execution.control.clock)
          | none =>
              if idealExposureCritical grammar
                  (normalizeIdealExposure grammar iv fallbackC dummy environment
                    execution.control) then
                ExposureTapeCoordinate.critical
                  (Fin.ofNat (budget + 1) execution.control.clock)
              else
                ExposureTapeCoordinate.ordinary
                  (Fin.ofNat (budget + 1) execution.control.clock)) ≠
          ExposureTapeCoordinate.critical time.castSucc
      cases cacheLookup : execution.cache point with
      | some answer => simp [cacheLookup]
      | none =>
          cases critical : idealExposureCritical grammar
              (normalizeIdealExposure grammar iv fallbackC dummy environment
                execution.control) with
          | false => simp [cacheLookup, critical]
          | true =>
              simp only [cacheLookup, critical, Bool.true_eq, if_true]
              intro equal
              have indexEqual := ExposureTapeCoordinate.critical.inj equal
              have clockBound : execution.control.clock < budget + 1 := by
                rw [clock]
                exact Nat.lt_trans strict
                  (Nat.lt_trans time.2 (Nat.lt_succ_self budget))
              have naturalEqual := congrArg Fin.val indexEqual
              simp only [Fin.val_ofNat] at naturalEqual
              rw [Nat.mod_eq_of_lt clockBound, clock] at naturalEqual
              change m = time.1 at naturalEqual
              omega

/-- Final exposure control state produced by the critical-rank tape. -/
def idealExposureTapeRun [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds budget : ℕ)
    (tape : ExposureTapeCoordinate budget → C) :
    IdealExposureState C B X Tag :=
  let program :=
    idealExposureProgram grammar iv fallbackC fallbackB dummy environment
  let values := adaptiveRun
    (idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
      environment rounds budget) tape budget
  (cachedOracleRun program (initialIdealExposure iv rounds) values).control

/-- A uniform compression function and the relabeled critical-rank tape give
exactly the same law of final exposure states. -/
theorem eagerIdealExposure_uniform_eq_tape_uniform
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype B] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds budget : ℕ) :
    Dist.fTransform
        (fun compression : C × B → C =>
          eagerOracleRun
            (idealExposureProgram grammar iv fallbackC fallbackB dummy
              environment)
            compression (initialIdealExposure iv rounds) budget)
        (Dist.uniform (C × B → C)) =
      Dist.fTransform
        (idealExposureTapeRun grammar iv fallbackC fallbackB dummy environment
          rounds budget)
        (Dist.uniform (ExposureTapeCoordinate budget → C)) := by
  classical
  let program :=
    idealExposureProgram grammar iv fallbackC fallbackB dummy environment
  let initial : IdealExposureState C B X Tag := initialIdealExposure iv rounds
  let schedule := idealExposureTapeSchedule grammar iv fallbackC fallbackB
    dummy environment rounds budget
  let lazyObserve : (Fin budget → C) → IdealExposureState C B X Tag :=
    fun values => (cachedOracleRun program initial values).control
  have eagerCached := eagerOracleRun_uniform_eq_cachedOracleRun_uniform
    program initial budget
  have rawUniform :
      Dist.fTransform (fun tape => adaptiveRun schedule tape budget)
          (Dist.uniform (ExposureTapeCoordinate budget → C)) =
        Dist.uniform (Fin budget → C) :=
    adaptiveRun_uniform_eq_uniform_of_fresh schedule budget
      (idealExposureTapeSchedule_fresh grammar iv fallbackC fallbackB dummy
        environment rounds budget)
  change Dist.fTransform
      (fun compression : C × B → C =>
        eagerOracleRun program compression initial budget)
      (Dist.uniform (C × B → C)) = _
  calc
    _ = Dist.fTransform lazyObserve (Dist.uniform (Fin budget → C)) :=
      eagerCached
    _ = Dist.fTransform lazyObserve
          (Dist.fTransform (fun tape => adaptiveRun schedule tape budget)
            (Dist.uniform (ExposureTapeCoordinate budget → C))) := by
      rw [rawUniform]
    _ = Dist.fTransform
          (idealExposureTapeRun grammar iv fallbackC fallbackB dummy environment
            rounds budget)
          (Dist.uniform (ExposureTapeCoordinate budget → C)) := by
      rw [Dist.fTransform_comp]
      rfl

/-! ## The IV and live/live part of the graph bound -/

/-- Critical coordinates embedded in the relabeled exposure tape. -/
def criticalTapeEmbedding (budget : ℕ) :
    Fin budget ↪ ExposureTapeCoordinate budget where
  toFun := fun index => .critical index.castSucc
  inj' := by
    intro left right equal
    apply Fin.ext
    exact congrArg (fun index : Fin (budget + 1) => index.val)
      (ExposureTapeCoordinate.critical.inj equal)

/-- Restriction of a complete exposure tape to its critical coordinates. -/
def criticalTape (budget : ℕ) (tape : ExposureTapeCoordinate budget → C) :
    Fin budget → C :=
  fun index => tape (criticalTapeEmbedding budget index)

/-- The critical restriction of a uniform exposure tape is exactly a uniform
vector. -/
theorem criticalTape_uniform [Fintype C] [DecidableEq C] [Nonempty C]
    (budget : ℕ) :
    Dist.fTransform (criticalTape (C := C) budget)
        (Dist.uniform (ExposureTapeCoordinate budget → C)) =
      Dist.uniform (Fin budget → C) := by
  exact RandomSystems.CR18.uniform_restrict (criticalTapeEmbedding budget)

/-- The uniform critical tape hits IV or repeats a prior critical value with
the exact paper union-bound numerator. -/
theorem uniform_criticalTape_coreJoin_mass_le
    [Fintype C] [DecidableEq C] [Nonempty C]
    (iv : C) (budget : ℕ) :
    (Dist.uniform (ExposureTapeCoordinate budget → C)).mass
        (fun tape =>
          StaticJoin iv ∅ budget (criticalTape budget tape)) ≤
      ((Nat.choose (budget + 1) 2 : ℕ) : ℝ) /
        (Fintype.card C : ℝ) := by
  have massEquality :
      (Dist.uniform (ExposureTapeCoordinate budget → C)).mass
          (fun tape => StaticJoin iv ∅ budget (criticalTape budget tape)) =
        (Dist.uniform (Fin budget → C)).mass
          (StaticJoin iv ∅ budget) := by
    rw [← criticalTape_uniform (C := C) budget, Dist.mass_fTransform]
  rw [massEquality]
  simpa using uniform_staticJoin_mass_le_budget iv ∅ budget 0 (by simp)

/-! ## Loose-root/live joins -/

/-- Exposure control immediately before raw microstep `time`, reconstructed
from a complete relabelled tape. -/
def idealExposureTapePrefixState [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds budget : ℕ)
    (tape : ExposureTapeCoordinate budget → C) (time : Fin budget) :
    IdealExposureState C B X Tag :=
  let schedule :=
    idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
      environment rounds budget
  let program :=
    idealExposureProgram grammar iv fallbackC fallbackB dummy environment
  let values := adaptiveRun schedule tape budget
  (cachedOracleRun program (initialIdealExposure iv rounds)
    (finStrictPrefix values time)).control

/-- Loose roots fixed before the next raw answer is read.  At a fresh loose
primitive call the root is already determined by the query, even though the
executor appends its record only while completing that same step. -/
def looseRootsBeforeNextAnswer [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (state : IdealExposureState C B X Tag) : List (LooseRootRecord C) :=
  let normalized :=
    normalizeIdealExposure grammar iv fallbackC dummy environment state
  match normalized.phase with
  | .primitiveCall point =>
      match publicLooseRoot normalized.simulator point with
      | none => normalized.looseRoots
      | some root => normalized.looseRoots ++
          [{ value := root, source := normalized.clock }]
  | .idle | .inner .. | .outer .. | .done => normalized.looseRoots

/-- The witness `(rootIndex, time)` says that a root already present before
`time` equals the fresh critical coordinate labelled by `time`.  The family
deliberately includes unused root slots and unused critical times; this makes
the probability estimate independent of the adaptive execution shape. -/
def looseRootBeforeCriticalFamily [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds q budget : ℕ) :
    CoordinateFunctionalFamily
      (ExposureTapeCoordinate budget) C (Fin q × Fin budget) where
  coordinate witness := .critical witness.2.castSucc
  event witness tape :=
    ∃ root : LooseRootRecord C,
      (looseRootsBeforeNextAnswer grammar iv fallbackC dummy environment
          (idealExposureTapePrefixState grammar iv fallbackC fallbackB dummy
            environment rounds budget tape witness.2))[witness.1.1]? = some root ∧
        tape (.critical witness.2.castSucc) = root.value
  functional := by
    intro witness left right agree leftEvent rightEvent
    rcases leftEvent with ⟨leftRoot, leftLookup, leftValue⟩
    rcases rightEvent with ⟨rightRoot, rightLookup, rightValue⟩
    let schedule :=
      idealExposureTapeSchedule grammar iv fallbackC fallbackB dummy
        environment rounds budget
    let program :=
      idealExposureProgram grammar iv fallbackC fallbackB dummy environment
    have runPrefixEqual :
        adaptiveRun schedule left witness.2.1 =
          adaptiveRun schedule right witness.2.1 :=
      adaptiveRun_eq_before_critical_time grammar iv fallbackC fallbackB dummy
        environment rounds budget left right witness.2 agree
        witness.2.1 (le_refl _)
    have rawPrefixEqual :
        finStrictPrefix (adaptiveRun schedule left budget) witness.2 =
          finStrictPrefix (adaptiveRun schedule right budget) witness.2 := by
      rw [finStrictPrefix_adaptiveRun, finStrictPrefix_adaptiveRun]
      exact runPrefixEqual
    have stateEqual :
        idealExposureTapePrefixState grammar iv fallbackC fallbackB dummy
            environment rounds budget left witness.2 =
          idealExposureTapePrefixState grammar iv fallbackC fallbackB dummy
            environment rounds budget right witness.2 := by
      exact congrArg
        (fun values =>
          (cachedOracleRun program (initialIdealExposure iv rounds)
            values).control)
        rawPrefixEqual
    have rootEqual : leftRoot = rightRoot := by
      apply Option.some.inj
      calc
        some leftRoot =
            (looseRootsBeforeNextAnswer grammar iv fallbackC dummy environment
              (idealExposureTapePrefixState grammar iv fallbackC fallbackB dummy
                environment rounds budget left witness.2))[witness.1.1]? :=
          leftLookup.symm
        _ = (looseRootsBeforeNextAnswer grammar iv fallbackC dummy environment
              (idealExposureTapePrefixState grammar iv fallbackC fallbackB dummy
                environment rounds budget right witness.2))[witness.1.1]? := by
          rw [stateEqual]
        _ = some rightRoot := rightLookup
    change left (.critical witness.2.castSucc) =
      right (.critical witness.2.castSucc)
    calc
      left (.critical witness.2.castSucc) = leftRoot.value := leftValue
      _ = rightRoot.value := congrArg LooseRootRecord.value rootEqual
      _ = right (.critical witness.2.castSucc) := rightValue.symm

/-- A uniform exposure tape contains a loose-root/live join before its live
coordinate with mass at most `q * budget / |C|`. -/
theorem uniform_looseRootBeforeCritical_mass_le
    [Fintype C] [DecidableEq C] [Nonempty C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds q budget : ℕ) :
    (Dist.uniform (ExposureTapeCoordinate budget → C)).mass
        (looseRootBeforeCriticalFamily grammar iv fallbackC fallbackB dummy
          environment rounds q budget).Bad ≤
      (((q * budget : ℕ) : ℝ) / (Fintype.card C : ℝ)) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    (looseRootBeforeCriticalFamily grammar iv fallbackC fallbackB dummy
      environment rounds q budget).uniform_bad_mass_le

/-- The two graph failures controlled directly by independent critical
coordinates: a critical value hits IV/another critical value, or it hits a
loose root that was already fixed. -/
def EarlyExposureJoin [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds q budget : ℕ)
    (tape : ExposureTapeCoordinate budget → C) : Prop :=
  StaticJoin iv ∅ budget (criticalTape budget tape) ∨
    (looseRootBeforeCriticalFamily grammar iv fallbackC fallbackB dummy
      environment rounds q budget).Bad tape

/-- Exact finite union-bound numerator for the IV/live, live/live, and
earlier-root/live joins. -/
theorem uniform_earlyExposureJoin_mass_le
    [Fintype C] [DecidableEq C] [Nonempty C]
    [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv fallbackC : C) (fallbackB : B)
    (dummy : X → C)
    (environment : PFunDDS.DDE (Query C B X) (Reply C B X))
    (rounds q budget : ℕ) :
    (Dist.uniform (ExposureTapeCoordinate budget → C)).mass
        (EarlyExposureJoin grammar iv fallbackC fallbackB dummy environment
          rounds q budget) ≤
      ((((Nat.choose (budget + 1) 2) + q * budget : ℕ) : ℝ) /
        (Fintype.card C : ℝ)) := by
  let tapeDist := Dist.uniform (ExposureTapeCoordinate budget → C)
  calc
    tapeDist.mass
        (EarlyExposureJoin grammar iv fallbackC fallbackB dummy environment
          rounds q budget) ≤
      tapeDist.mass
          (fun tape => StaticJoin iv ∅ budget (criticalTape budget tape)) +
        tapeDist.mass
          (looseRootBeforeCriticalFamily grammar iv fallbackC fallbackB dummy
            environment rounds q budget).Bad :=
      Dist.mass_or_le Dist.uniform_nonNeg _ _
    _ ≤ ((Nat.choose (budget + 1) 2 : ℕ) : ℝ) /
          (Fintype.card C : ℝ) +
        (((q * budget : ℕ) : ℝ) / (Fintype.card C : ℝ)) :=
      add_le_add (uniform_criticalTape_coreJoin_mass_le iv budget)
        (uniform_looseRootBeforeCritical_mass_le grammar iv fallbackC
          fallbackB dummy environment rounds q budget)
    _ = ((((Nat.choose (budget + 1) 2) + q * budget : ℕ) : ℝ) /
          (Fintype.card C : ℝ)) := by
      push_cast
      ring

end MDSimulator
end RandomSystemsModel
end SequenceHash
