import SequenceHash.RandomSystems.SequenceHashSimulator

/-!
# Compression-graph path invariant for the SequenceHash simulator

This module proves the first substantive invariant through the simulator's
native case tree.  If `state.word value = some blocks`, then the installed
compression table really contains a path labeled by `blocks` from the public
IV to `value`.  The proof is independent of the byte-level grammar.

The key preservation theorem applies `primitiveStep_cases`; Lean therefore
creates a separate obligation for every table/root/parser/link observation.
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

/-- Follow a block word through a partial compression table. -/
def follow (table : C × B → Option C) : C → List B → Option C
  | start, [] => some start
  | start, block :: rest =>
      (table (start, block)).bind fun next => follow table next rest

@[simp]
theorem follow_nil (table : C × B → Option C) (start : C) :
    follow table start [] = some start := by
  rfl

@[simp]
theorem follow_cons (table : C × B → Option C) (start : C)
    (block : B) (rest : List B) :
    follow table start (block :: rest) =
      (table (start, block)).bind fun next => follow table next rest := by
  rfl

/-- Partial path following composes over concatenation. -/
theorem follow_append (table : C × B → Option C) (start : C)
    (left right : List B) :
    follow table start (left ++ right) =
      (follow table start left).bind fun middle => follow table middle right := by
  induction left generalizing start with
  | nil => rfl
  | cons block rest ih =>
      simp only [List.cons_append, follow_cons]
      cases table (start, block) with
      | none => rfl
      | some next => simpa using ih next

/-- Every semantic word index is backed by an installed table path. -/
def TableConsistent (state : State C B X Tag) (iv : C) : Prop :=
  ∀ value word, state.word value = some word →
    follow state.table iv word = some value

/-- The initial state contains exactly the empty path at IV. -/
theorem initialState_tableConsistent [DecidableEq C] (iv : C) :
    TableConsistent (initialState (B := B) (X := X) (Tag := Tag) iv) iv := by
  intro value word hword
  by_cases hvalue : value = iv
  · subst value
    simp [initialState] at hword
    subst word
    rfl
  · simp [initialState, hvalue] at hword

/-- Filling a previously undefined table point cannot change any path that was
already completely defined. -/
theorem follow_update_of_eq_some [DecidableEq C] [DecidableEq B]
    (table : C × B → Option C) (query : C × B) (answer : C)
    (fresh : table query = none) {start value : C} (blocks : List B)
    (defined : follow table start blocks = some value) :
    follow (Function.update table query (some answer)) start blocks =
      some value := by
  induction blocks generalizing start with
  | nil => exact defined
  | cons block rest ih =>
      rw [follow_cons] at defined ⊢
      cases hlookup : table (start, block) with
      | none => simp [hlookup] at defined
      | some next =>
          have hpoint : (start, block) ≠ query := by
            intro heq
            rw [heq, fresh] at hlookup
            simp at hlookup
          rw [Function.update_of_ne hpoint, hlookup]
          apply ih
          simpa [hlookup] using defined

/-- The newly filled edge extends any already certified source path. -/
theorem follow_install_edge [DecidableEq C] [DecidableEq B]
    (table : C × B → Option C) (iv : C) (query : C × B)
    (answer : C) (path : List B) (fresh : table query = none)
    (source : follow table iv path = some query.1) :
    follow (Function.update table query (some answer)) iv
      (path ++ [query.2]) = some answer := by
  rw [follow_append]
  rw [follow_update_of_eq_some table query answer fresh path source]
  simp [follow, Function.update_self]

/-- Installing a fresh table entry preserves every previously indexed path. -/
theorem tableConsistent_installTable [DecidableEq C] [DecidableEq B]
    {state : State C B X Tag} {iv : C} {query : C × B} {answer : C}
    (consistent : TableConsistent state iv)
    (fresh : state.table query = none) :
    TableConsistent (installTable state query answer) iv := by
  intro value word hword
  have oldWord : state.word value = some word := by
    simpa [installTable] using hword
  have oldPath := consistent value word oldWord
  simpa [installTable] using
    follow_update_of_eq_some state.table query answer fresh word oldPath

/-- Installing a new semantic word at a fresh destination preserves the old
index and certifies the new entry from its supplied path equation. -/
theorem tableConsistent_installLive [DecidableEq C]
    {state : State C B X Tag} {iv value : C} {word : List B}
    {completed : Option X}
    (consistent : TableConsistent state iv)
    (path : follow state.table iv word = some value) :
    TableConsistent (installLive state value word completed) iv := by
  intro other otherWord hword
  by_cases hvalue : other = value
  · subst other
    simp [installLive] at hword
    subst otherWord
    exact path
  · have oldWord : state.word other = some otherWord := by
      simpa [installLive, hvalue] using hword
    exact consistent other otherWord oldWord

/-- Setting the failure bit changes no table path. -/
theorem tableConsistent_markJoin {state : State C B X Tag} {iv : C}
    (consistent : TableConsistent state iv) :
    TableConsistent (markJoin state) iv := by
  simpa [TableConsistent, markJoin] using consistent

/-- Propagation preserves path consistency in all four native destination
branches.  Only the fresh branch installs a word. -/
theorem tableConsistent_propagate [DecidableEq C]
    {state : State C B X Tag} {iv value : C} {word : List B}
    {completed : Option X}
    (consistent : TableConsistent state iv)
    (path : follow state.table iv word = some value) :
    TableConsistent (propagate state iv value word completed) iv := by
  apply propagate_cases state iv value word completed
      (P := fun next => TableConsistent next iv)
  · intro _hiv
    exact tableConsistent_markJoin consistent
  · intro _previous _hne _hword
    exact tableConsistent_markJoin consistent
  · intro _hne _hword _hloose
    exact tableConsistent_markJoin consistent
  · intro _hne _hword _hfresh
    exact tableConsistent_installLive consistent path

/-! ## Preservation by each primitive action -/

theorem tableConsistent_ordinaryPrimitiveStep [DecidableEq C] [DecidableEq B]
    {state : State C B X Tag} {iv : C} {coins : Coins C B X}
    {query : C × B} (consistent : TableConsistent state iv)
    (fresh : state.table query = none) :
    TableConsistent (ordinaryPrimitiveStep coins state query).1 iv := by
  simpa [ordinaryPrimitiveStep] using
    tableConsistent_installTable consistent fresh
      (answer := coins.2 query)

theorem tableConsistent_loosePrimitiveStep [DecidableEq C] [DecidableEq B]
    {state : State C B X Tag} {iv : C} {coins : Coins C B X}
    {query : C × B} (consistent : TableConsistent state iv)
    (fresh : state.table query = none) :
    TableConsistent (loosePrimitiveStep coins state query).1 iv := by
  have installed := tableConsistent_installTable consistent fresh
      (answer := coins.2 query)
  simpa [loosePrimitiveStep, recordLoose] using installed

theorem tableConsistent_pendingPrimitiveStep [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    {state : State C B X Tag} {iv : C} {coins : Coins C B X}
    {query : C × B} {tag : Tag} {embedded : C}
    (consistent : TableConsistent state iv)
    (fresh : state.table query = none) :
    TableConsistent
      (pendingPrimitiveStep coins state query tag embedded).1 iv := by
  have installed := tableConsistent_installTable consistent fresh
      (answer := coins.2 query)
  simpa [pendingPrimitiveStep, recordPending] using installed

theorem tableConsistent_linkedPrimitiveStep [DecidableEq C] [DecidableEq B]
    {state : State C B X Tag} {iv : C} {coins : Coins C B X}
    {query : C × B} {input : X}
    (consistent : TableConsistent state iv)
    (fresh : state.table query = none) :
    TableConsistent (linkedPrimitiveStep coins state query input).1 iv := by
  simpa [linkedPrimitiveStep] using
    tableConsistent_installTable consistent fresh
      (answer := coins.1 input)

/-- Extending a certified live source by one newly installed edge, then
running the four-way destination classifier, preserves the path invariant. -/
theorem tableConsistent_livePrimitiveStep [DecidableEq C] [DecidableEq B]
    {state : State C B X Tag} {iv : C} {coins : Coins C B X}
    {query : C × B} {path : List B} {completed : Option X}
    (consistent : TableConsistent state iv)
    (fresh : state.table query = none)
    (sourceWord : state.word query.1 = some path) :
    TableConsistent
      (livePrimitiveStep iv coins state query (path ++ [query.2]) completed).1
      iv := by
  have sourcePath : follow state.table iv path = some query.1 :=
    consistent query.1 path sourceWord
  have installed :
      TableConsistent (installTable state query (coins.2 query)) iv :=
    tableConsistent_installTable consistent fresh
  have extended :
      follow (installTable state query (coins.2 query)).table iv
        (path ++ [query.2]) = some (coins.2 query) := by
    simpa [installTable] using
      follow_install_edge state.table iv query (coins.2 query) path fresh
        sourcePath
  simpa [livePrimitiveStep] using
    tableConsistent_propagate installed extended

/-! ## Generated preservation theorem -/

/-- Every native primitive leaf preserves the certified-path invariant.  This
is the graph proof's exhaustiveness receipt: all nine premises generated by
`primitiveStep_cases` are solved explicitly. -/
theorem primitiveStep_tableConsistent [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : C × B)
    (consistent : TableConsistent state iv) :
    TableConsistent (primitiveStep grammar iv coins state query).1 iv := by
  apply primitiveStep_cases grammar iv coins state query
      (P := fun result => TableConsistent result.1 iv)
  · intro _answer _htable
    exact consistent
  · intro htable _hword
    exact tableConsistent_loosePrimitiveStep consistent htable
  · intro path htable hword _hparse
    exact tableConsistent_livePrimitiveStep consistent htable hword
  · intro path input htable hword _hparse
    exact tableConsistent_livePrimitiveStep consistent htable hword
  · intro path htable hword _hparse
    exact tableConsistent_livePrimitiveStep consistent htable hword
  · intro path tag embedded htable _hword _hparse _hinner
    exact tableConsistent_pendingPrimitiveStep consistent htable
  · intro path tag embedded input htable _hword _hparse _hinner _htag
    exact tableConsistent_pendingPrimitiveStep consistent htable
  · intro path tag embedded input htable _hword _hparse _hinner _htag
    exact tableConsistent_linkedPrimitiveStep consistent htable
  · intro path htable _hword _hparse
    exact tableConsistent_ordinaryPrimitiveStep consistent htable

/-- Construction queries do not alter the compression graph. -/
theorem evalStep_tableConsistent [DecidableEq X]
    (coins : Coins C B X) (state : State C B X Tag) (iv : C) (input : X)
    (consistent : TableConsistent state iv) :
    TableConsistent (evalStep coins state input).1 iv := by
  apply evalStep_cases coins state input
      (P := fun result => TableConsistent result.1 iv)
  · intro _hseen
    exact consistent
  · intro _hfresh
    simpa [TableConsistent, recordEval] using consistent

/-! ## Typed inner-endpoint invariant -/

/-- Every completed-inner index points to the exact grammar word for the
recorded construction input. -/
def InnerConsistent (grammar : Grammar C B X Tag) (state : State C B X Tag) :
    Prop :=
  ∀ value input, state.inner value = some input →
    state.word value = some (grammar.innerWord input)

theorem initialState_innerConsistent [DecidableEq C]
    (grammar : Grammar C B X Tag) (iv : C) :
    InnerConsistent grammar (initialState iv) := by
  intro value input hinner
  simp [initialState] at hinner

theorem inner_none_of_word_none
    {grammar : Grammar C B X Tag} {state : State C B X Tag} {value : C}
    (consistent : InnerConsistent grammar state)
    (wordNone : state.word value = none) :
    state.inner value = none := by
  cases hinner : state.inner value with
  | none => rfl
  | some input =>
      have wordSome := consistent value input hinner
      rw [wordNone] at wordSome
      contradiction

theorem innerConsistent_installLive_none [DecidableEq C]
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    {value : C} {word : List B}
    (consistent : InnerConsistent grammar state)
    (innerNone : state.inner value = none) :
    InnerConsistent grammar (installLive state value word none) := by
  intro other input hinner
  by_cases hvalue : other = value
  · subst other
    simp [installLive, innerNone] at hinner
  · have oldInner : state.inner other = some input := by
      simpa [installLive, hvalue] using hinner
    have oldWord := consistent other input oldInner
    simpa [installLive, hvalue] using oldWord

theorem innerConsistent_installLive_some [DecidableEq C]
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    {value : C} {word : List B} {input : X}
    (consistent : InnerConsistent grammar state)
    (wordEq : word = grammar.innerWord input) :
    InnerConsistent grammar (installLive state value word (some input)) := by
  intro other claimed hinner
  by_cases hvalue : other = value
  · subst other
    simp [installLive] at hinner
    subst claimed
    simp [installLive, wordEq]
  · have oldInner : state.inner other = some claimed := by
      simpa [installLive, hvalue] using hinner
    have oldWord := consistent other claimed oldInner
    simpa [installLive, hvalue] using oldWord

theorem innerConsistent_markJoin
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    (consistent : InnerConsistent grammar state) :
    InnerConsistent grammar (markJoin state) := by
  simpa [InnerConsistent, markJoin] using consistent

/-- A live prefix propagation (`completed = none`) preserves the typed-inner
index.  Freshness of the destination word implies freshness of its inner slot. -/
theorem innerConsistent_propagate_none [DecidableEq C]
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    {iv value : C} {word : List B}
    (consistent : InnerConsistent grammar state) :
    InnerConsistent grammar (propagate state iv value word none) := by
  apply propagate_cases state iv value word none
      (P := fun next => InnerConsistent grammar next)
  · intro _hiv
    exact innerConsistent_markJoin consistent
  · intro _previous _hne _hword
    exact innerConsistent_markJoin consistent
  · intro _hne _hword _hloose
    exact innerConsistent_markJoin consistent
  · intro _hne hword _hfresh
    exact innerConsistent_installLive_none consistent
      (inner_none_of_word_none consistent hword)

/-- A completed inner propagation installs the exact decoded inner word. -/
theorem innerConsistent_propagate_some [DecidableEq C]
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    {iv value : C} {word : List B} {input : X}
    (consistent : InnerConsistent grammar state)
    (wordEq : word = grammar.innerWord input) :
    InnerConsistent grammar (propagate state iv value word (some input)) := by
  apply propagate_cases state iv value word (some input)
      (P := fun next => InnerConsistent grammar next)
  · intro _hiv
    exact innerConsistent_markJoin consistent
  · intro _previous _hne _hword
    exact innerConsistent_markJoin consistent
  · intro _hne _hword _hloose
    exact innerConsistent_markJoin consistent
  · intro _hne _hword _hfresh
    exact innerConsistent_installLive_some consistent wordEq

theorem innerConsistent_installTable [DecidableEq C] [DecidableEq B]
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    {query : C × B} {answer : C}
    (consistent : InnerConsistent grammar state) :
    InnerConsistent grammar (installTable state query answer) := by
  simpa [InnerConsistent, installTable] using consistent

theorem innerConsistent_livePrimitiveStep_none [DecidableEq C] [DecidableEq B]
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    {iv : C} {coins : Coins C B X} {query : C × B} {word : List B}
    (consistent : InnerConsistent grammar state) :
    InnerConsistent grammar
      (livePrimitiveStep iv coins state query word none).1 := by
  have installed :
      InnerConsistent grammar (installTable state query (coins.2 query)) :=
    innerConsistent_installTable consistent
  simpa [livePrimitiveStep] using innerConsistent_propagate_none installed

theorem innerConsistent_livePrimitiveStep_some [DecidableEq C] [DecidableEq B]
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    {iv : C} {coins : Coins C B X} {query : C × B} {word : List B}
    {input : X}
    (consistent : InnerConsistent grammar state)
    (wordEq : word = grammar.innerWord input) :
    InnerConsistent grammar
      (livePrimitiveStep iv coins state query word (some input)).1 := by
  have installed :
      InnerConsistent grammar (installTable state query (coins.2 query)) :=
    innerConsistent_installTable consistent
  simpa [livePrimitiveStep] using
    innerConsistent_propagate_some installed wordEq

/-- Every native primitive leaf preserves the typed inner index.  The
`innerComplete` leaf is the only one that uses parser soundness. -/
theorem primitiveStep_innerConsistent [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : C × B)
    (consistent : InnerConsistent grammar state) :
    InnerConsistent grammar (primitiveStep grammar iv coins state query).1 := by
  apply primitiveStep_cases grammar iv coins state query
      (P := fun result => InnerConsistent grammar result.1)
  · intro _answer _htable
    exact consistent
  · intro _htable _hword
    simpa [loosePrimitiveStep, recordLoose, installTable,
      InnerConsistent] using consistent
  · intro path _htable _hword _hparse
    exact innerConsistent_livePrimitiveStep_none consistent
  · intro path input _htable _hword hparse
    exact innerConsistent_livePrimitiveStep_some consistent
      (grammar.inner_complete_sound _ _ hparse)
  · intro path _htable _hword _hparse
    exact innerConsistent_livePrimitiveStep_none consistent
  · intro path tag embedded _htable _hword _hparse _hinner
    simpa [pendingPrimitiveStep, recordPending, installTable,
      InnerConsistent] using consistent
  · intro path tag embedded input _htable _hword _hparse _hinner _htag
    simpa [pendingPrimitiveStep, recordPending, installTable,
      InnerConsistent] using consistent
  · intro path tag embedded input _htable _hword _hparse _hinner _htag
    simpa [linkedPrimitiveStep, installTable, InnerConsistent] using consistent
  · intro path _htable _hword _hparse
    simpa [ordinaryPrimitiveStep, installTable, InnerConsistent] using consistent

theorem evalStep_innerConsistent [DecidableEq X]
    (grammar : Grammar C B X Tag) (coins : Coins C B X)
    (state : State C B X Tag) (input : X)
    (consistent : InnerConsistent grammar state) :
    InnerConsistent grammar (evalStep coins state input).1 := by
  apply evalStep_cases coins state input
      (P := fun result => InnerConsistent grammar result.1)
  · intro _hseen
    exact consistent
  · intro _hfresh
    simpa [recordEval, InnerConsistent] using consistent

/-- The certified live graph consists of real table paths and correctly typed
completed-inner endpoints. -/
def GraphInvariant (grammar : Grammar C B X Tag) (state : State C B X Tag)
    (iv : C) : Prop :=
  TableConsistent state iv ∧ InnerConsistent grammar state

theorem initialState_graphInvariant [DecidableEq C]
    (grammar : Grammar C B X Tag) (iv : C) :
    GraphInvariant grammar (initialState iv) iv :=
  ⟨initialState_tableConsistent iv, initialState_innerConsistent grammar iv⟩

theorem primitiveStep_graphInvariant [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : C × B)
    (invariant : GraphInvariant grammar state iv) :
    GraphInvariant grammar (primitiveStep grammar iv coins state query).1 iv :=
  ⟨primitiveStep_tableConsistent grammar iv coins state query invariant.1,
    primitiveStep_innerConsistent grammar iv coins state query invariant.2⟩

theorem evalStep_graphInvariant [DecidableEq X]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (input : X)
    (invariant : GraphInvariant grammar state iv) :
    GraphInvariant grammar (evalStep coins state input).1 iv :=
  ⟨evalStep_tableConsistent coins state iv input invariant.1,
    evalStep_innerConsistent grammar coins state input invariant.2⟩

theorem simulatorStep_graphInvariant [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : Query C B X)
    {next : State C B X Tag} {answer : AnswerAt query}
    (invariant : GraphInvariant grammar state iv)
    (step : simulatorStep grammar iv coins state query = some (next, answer)) :
    GraphInvariant grammar next iv := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | prim =>
      simp only [simulatorStep, Option.some.injEq] at step
      have nextEq : (primitiveStep grammar iv coins state input).1 = next :=
        congrArg Prod.fst step
      rw [← nextEq]
      exact primitiveStep_graphInvariant grammar iv coins state input invariant
  | eval =>
      simp only [simulatorStep, Option.some.injEq] at step
      have nextEq : (evalStep coins state input).1 = next :=
        congrArg Prod.fst step
      rw [← nextEq]
      exact evalStep_graphInvariant grammar iv coins state input invariant

/-- Main graph receipt: every state reachable after an arbitrary adaptive
history satisfies both certified-path and typed-inner invariants. -/
theorem simulatorRunFrom_graphInvariant [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) (state next : State C B X Tag)
    (invariant : GraphInvariant grammar state iv)
    (run : (simulatorMachine grammar iv coins).runFrom state history =
      some next) :
    GraphInvariant grammar next iv := by
  induction history generalizing state next with
  | nil =>
      have nextEq : state = next := Option.some.inj run
      rwa [← nextEq]
  | cons query rest ih =>
      rw [Machine.runFrom_cons] at run
      generalize hmove : (simulatorMachine grammar iv coins).step state query =
        move at run
      cases move with
      | none => simp at run
      | some moved =>
          simp only [Option.bind_some] at run
          change simulatorStep grammar iv coins state query = some moved at hmove
          have nextInvariant : GraphInvariant grammar moved.1 iv :=
            simulatorStep_graphInvariant grammar iv coins state query invariant
              hmove
          exact ih moved.1 next nextInvariant run

theorem simulatorRun_graphInvariant [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) (next : State C B X Tag)
    (run : (simulatorMachine grammar iv coins).run history = some next) :
    GraphInvariant grammar next iv := by
  exact simulatorRunFrom_graphInvariant grammar iv coins history
    (initialState iv) next (initialState_graphInvariant grammar iv) run

/-! ## Linked-terminal consequences -/

/-- A recorded inner endpoint has both its exact grammar word and a certified
table path from IV. -/
theorem innerEndpoint_certified
    {grammar : Grammar C B X Tag} {state : State C B X Tag} {iv embedded : C}
    {input : X} (invariant : GraphInvariant grammar state iv)
    (inner : state.inner embedded = some input) :
    state.word embedded = some (grammar.innerWord input) ∧
      follow state.table iv (grammar.innerWord input) = some embedded := by
  have word := invariant.2 embedded input inner
  exact ⟨word, invariant.1 embedded (grammar.innerWord input) word⟩

/-- Parser soundness turns the linked branch's local parse result into the
exact outer word obligated by the construction input. -/
theorem outerLinked_word_eq
    {grammar : Grammar C B X Tag} {path : List B} {block : B}
    {tag : Tag} {embedded : C} {input : X}
    (parse : grammar.classifyWord (path ++ [block]) =
      .outerComplete tag embedded)
    (tagEq : grammar.tagOf input = tag) :
    path ++ [block] = grammar.outerWord (grammar.tagOf input) embedded := by
  rw [grammar.outer_complete_sound _ _ _ parse, tagEq]

/-- One completed word cannot carry two competing terminal-programming
obligations.  Parser soundness plus outer injectivity fixes `(tag, embedded)`,
and the state's functional inner index then fixes the input. -/
theorem outerLinked_unique
    {grammar : Grammar C B X Tag} {state : State C B X Tag}
    {word : List B} {tag₁ tag₂ : Tag} {embedded₁ embedded₂ : C}
    {input₁ input₂ : X}
    (parse₁ : grammar.classifyWord word =
      .outerComplete tag₁ embedded₁)
    (parse₂ : grammar.classifyWord word =
      .outerComplete tag₂ embedded₂)
    (inner₁ : state.inner embedded₁ = some input₁)
    (inner₂ : state.inner embedded₂ = some input₂) :
    tag₁ = tag₂ ∧ embedded₁ = embedded₂ ∧ input₁ = input₂ := by
  have outerEq : grammar.outerWord tag₁ embedded₁ =
      grammar.outerWord tag₂ embedded₂ := by
    rw [← grammar.outer_complete_sound _ _ _ parse₁,
      ← grammar.outer_complete_sound _ _ _ parse₂]
  have pairEq : (tag₁, embedded₁) = (tag₂, embedded₂) :=
    grammar.outer_injective outerEq
  have tagEq : tag₁ = tag₂ := congrArg Prod.fst pairEq
  have embeddedEq : embedded₁ = embedded₂ := congrArg Prod.snd pairEq
  subst embedded₂
  have inputEq : input₁ = input₂ := by
    rw [inner₁] at inner₂
    exact Option.some.inj inner₂
  exact ⟨tagEq, rfl, inputEq⟩

/-- The dependent public-interface split preserves the invariant for the
actual next state returned by the machine. -/
theorem simulatorStep_tableConsistent [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : Query C B X)
    {next : State C B X Tag} {answer : AnswerAt query}
    (consistent : TableConsistent state iv)
    (step : simulatorStep grammar iv coins state query = some (next, answer)) :
    TableConsistent next iv := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | prim =>
      simp only [simulatorStep, Option.some.injEq] at step
      have nextEq : (primitiveStep grammar iv coins state input).1 = next :=
        congrArg Prod.fst step
      rw [← nextEq]
      exact primitiveStep_tableConsistent grammar iv coins state input consistent
  | eval =>
      simp only [simulatorStep, Option.some.injEq] at step
      have nextEq : (evalStep coins state input).1 = next :=
        congrArg Prod.fst step
      rw [← nextEq]
      exact evalStep_tableConsistent coins state iv input consistent

/-- Induction over `Machine.runFrom`: every state reachable after an arbitrary
adaptive query history has a certified compression path for every live word. -/
theorem simulatorRunFrom_tableConsistent [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) (state next : State C B X Tag)
    (consistent : TableConsistent state iv)
    (run : (simulatorMachine grammar iv coins).runFrom state history =
      some next) :
    TableConsistent next iv := by
  induction history generalizing state next with
  | nil =>
      have nextEq : state = next := Option.some.inj run
      rwa [← nextEq]
  | cons query rest ih =>
      rw [Machine.runFrom_cons] at run
      generalize hmove : (simulatorMachine grammar iv coins).step state query =
        move at run
      cases move with
      | none => simp at run
      | some moved =>
          simp only [Option.bind_some] at run
          change simulatorStep grammar iv coins state query = some moved at hmove
          have nextConsistent : TableConsistent moved.1 iv :=
            simulatorStep_tableConsistent grammar iv coins state query consistent
              hmove
          exact ih moved.1 next nextConsistent run

/-- In particular, the simulator's initialized run satisfies the invariant at
every reachable history. -/
theorem simulatorRun_tableConsistent [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (history : List (Query C B X)) (next : State C B X Tag)
    (run : (simulatorMachine grammar iv coins).run history = some next) :
    TableConsistent next iv := by
  exact simulatorRunFrom_tableConsistent grammar iv coins history
    (initialState iv) next (initialState_tableConsistent iv) run

end MDSimulator
end RandomSystemsModel
end SequenceHash
