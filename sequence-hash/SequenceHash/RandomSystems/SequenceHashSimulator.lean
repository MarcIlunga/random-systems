import RandomSystems.ResourceMachine
import SequenceHash.RandomSystems.MDHash

/-!
# A typed compression-graph simulator for SequenceHash

This module is the executable, abstract-grammar layer of the stable-v1
SequenceHash indifferentiability proof.  `WordClass` is the
construction-supplied parser result.  All other branches are generated from
the source observations themselves: interface tags, table and path `Option`s,
the parser result, endpoint lookup, tag equality, and sampled-destination
tests.

The simulator and its proof eliminators follow that native decision tree
without a wildcard branch.  Consequently a new parser result or semantic test
creates a new Lean proof obligation instead of disappearing into a curated
catch-all case.
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

/-! ## Typed public interface -/

/-- The two public interfaces of the indifferentiability experiment. -/
inductive Interface where
  | prim
  | eval
deriving DecidableEq, Fintype

/-- Inputs at the public compression and SequenceHash interfaces. -/
def Input (C B X : Type u) : Interface → Type u
  | .prim => C × B
  | .eval => X

/-- Both interfaces return a chaining value; native typing retains its tag. -/
def Output (C : Type u) : Interface → Type u := fun _ => C

abbrev Query (C B X : Type u) :=
  InterfaceQuery (Input C B X) (Output C)

abbrev Reply (C B X : Type u) :=
  FlatAnswer
    (SignatureUniverse.ofInterfaces (Input C B X) (Output C))
    (Boundary.ofInterfaces (Input C B X) (Output C))

/-! ## Abstract stable-v1 block grammar -/

/-- A total parser classification for a block word.  `innerComplete` remains
live because an inner word may be a prefix of a longer inner word.  An
`outerComplete` word is terminal. -/
inductive WordClass (X Tag C : Type u) where
  | innerPrefix
  | innerComplete (input : X)
  | outerPrefix
  | outerComplete (tag : Tag) (embedded : C)
  | invalid
deriving DecidableEq, Fintype

/-- The construction-facing grammar.  The simulator consumes only
`classifyWord` and `tagOf`; the remaining fields are the specification
contract used by the byte-level realization and graph-invariant proof. -/
structure Grammar (C B X Tag : Type u) where
  innerWord : X → List B
  outerWord : Tag → C → List B
  tagOf : X → Tag
  classifyWord : List B → WordClass X Tag C
  classify_inner : ∀ input,
    classifyWord (innerWord input) = .innerComplete input
  inner_nonempty : ∀ input, innerWord input ≠ []
  inner_complete_sound : ∀ word input,
    classifyWord word = .innerComplete input → word = innerWord input
  inner_prefix_sound : ∀ word,
    classifyWord word = .innerPrefix →
      ∃ input suffix, suffix ≠ [] ∧ innerWord input = word ++ suffix
  classify_outer : ∀ tag embedded,
    classifyWord (outerWord tag embedded) = .outerComplete tag embedded
  outer_nonempty : ∀ tag embedded, outerWord tag embedded ≠ []
  outer_complete_sound : ∀ word tag embedded,
    classifyWord word = .outerComplete tag embedded →
      word = outerWord tag embedded
  outer_prefix_sound : ∀ word,
    classifyWord word = .outerPrefix →
      ∃ tag embedded suffix, suffix ≠ [] ∧
        outerWord tag embedded = word ++ suffix
  inner_injective : Function.Injective innerWord
  outer_injective : Function.Injective (fun pair : Tag × C =>
    outerWord pair.1 pair.2)
  roles_disjoint : ∀ input tag embedded,
    innerWord input ≠ outerWord tag embedded
  outer_terminal : ∀ tag embedded suffix,
    suffix ≠ [] → classifyWord (outerWord tag embedded ++ suffix) = .invalid

/-! ## Simulator state -/

/-- The replay state of the simulator.  Functions are used instead of maps so
the mathematical state has no implementation-specific balancing invariant. -/
structure State (C B X Tag : Type u) where
  table : C × B → Option C
  word : C → Option (List B)
  inner : C → Option X
  pending : Tag × C → Option C
  loose : Finset C
  seen : Finset X
  join : Bool

def initialState [DecidableEq C] (iv : C) : State C B X Tag where
  table := fun _ => none
  word := fun value => if value = iv then some [] else none
  inner := fun _ => none
  pending := fun _ => none
  loose := ∅
  seen := ∅
  join := false

/-! ## Exhaustiveness discipline

The simulator below deliberately does **not** flatten its observations into a
hand-written transition enum.  Its control flow eliminates the source data
directly:

1. the primitive-table `Option`;
2. the reachable-word `Option`;
3. every constructor of the construction-supplied `WordClass`;
4. the completed-inner `Option`; and
5. the decidable tag equality.

The proof receipts repeat that native elimination tree with named branches and
no wildcard.  This is stronger than checking a curated list: changing any
lookup result or parser constructor changes the generated Lean goals.
-/

/-! ## State updates -/

def installTable [DecidableEq C] [DecidableEq B]
    (state : State C B X Tag) (query : C × B) (answer : C) :
    State C B X Tag :=
  { state with table := Function.update state.table query (some answer) }

def recordEval [DecidableEq X]
    (state : State C B X Tag) (input : X) : State C B X Tag :=
  { state with seen := insert input state.seen }

def recordLoose [DecidableEq C]
    (state : State C B X Tag) (root : C) : State C B X Tag :=
  { state with loose := insert root state.loose }

def recordPending [DecidableEq C] [DecidableEq Tag]
    (state : State C B X Tag) (tag : Tag) (embedded answer : C) :
    State C B X Tag :=
  { state with
      pending := Function.update state.pending (tag, embedded) (some answer) }

def installLive [DecidableEq C]
    (state : State C B X Tag) (value : C) (word : List B)
    (completed : Option X) : State C B X Tag :=
  { state with
      word := Function.update state.word value (some word)
      inner := match completed with
        | some input => Function.update state.inner value (some input)
        | none => state.inner }

def markJoin (state : State C B X Tag) : State C B X Tag :=
  { state with join := true }

/-- Propagate a nonterminal live path exactly when its sampled endpoint is
fresh.  The tests are kept in source form so the proof sees the IV, live,
loose-root, and fresh branches separately. -/
def propagate [DecidableEq C]
    (state : State C B X Tag) (iv value : C) (word : List B)
    (completed : Option X) : State C B X Tag :=
  if value = iv then
    markJoin state
  else
    match state.word value with
    | some _previous => markJoin state
    | none =>
        if value ∈ state.loose then
          markJoin state
        else
          installLive state value word completed

/-! ## Simulator and real machines -/

/-- The ideal random oracle and the simulator's independent lazy tape. -/
abbrev Coins (C B X : Type u) :=
  (X → C) × (C × B → C)

def ordinaryPrimitiveStep [DecidableEq C] [DecidableEq B]
    (coins : Coins C B X) (state : State C B X Tag) (query : C × B) :
    State C B X Tag × C :=
  let answer := coins.2 query
  (installTable state query answer, answer)

def loosePrimitiveStep [DecidableEq C] [DecidableEq B]
    (coins : Coins C B X) (state : State C B X Tag) (query : C × B) :
    State C B X Tag × C :=
  let answer := coins.2 query
  (recordLoose (installTable state query answer) query.1, answer)

def livePrimitiveStep [DecidableEq C] [DecidableEq B]
    (iv : C) (coins : Coins C B X) (state : State C B X Tag)
    (query : C × B) (word : List B) (completed : Option X) :
    State C B X Tag × C :=
  let answer := coins.2 query
  let next := installTable state query answer
  (propagate next iv answer word completed, answer)

def pendingPrimitiveStep [DecidableEq C] [DecidableEq B] [DecidableEq Tag]
    (coins : Coins C B X) (state : State C B X Tag) (query : C × B)
    (tag : Tag) (embedded : C) : State C B X Tag × C :=
  let answer := coins.2 query
  let next := installTable state query answer
  (recordPending next tag embedded answer, answer)

def linkedPrimitiveStep [DecidableEq C] [DecidableEq B]
    (coins : Coins C B X) (state : State C B X Tag) (query : C × B)
    (input : X) : State C B X Tag × C :=
  let answer := coins.1 input
  (installTable state query answer, answer)

/-- A construction-interface query exposes only the ideal-oracle answer.  The
membership split is nevertheless retained: it is the source-level distinction
between a repeated and a fresh construction query. -/
def evalStep [DecidableEq X] (coins : Coins C B X) (state : State C B X Tag)
    (input : X) : State C B X Tag × C :=
  if input ∈ state.seen then
    (state, coins.1 input)
  else
    (recordEval state input, coins.1 input)

/-- Primitive execution follows the native observation tree.  In particular,
`inner = none` and `inner = some input` with a wrong tag remain distinct
branches even though both use the same unlinked-terminal action. -/
def primitiveStep [DecidableEq C] [DecidableEq B] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : C × B) : State C B X Tag × C :=
  match state.table query with
  | some answer => (state, answer)
  | none =>
      match state.word query.1 with
      | none => loosePrimitiveStep coins state query
      | some path =>
          let word := path ++ [query.2]
          match grammar.classifyWord word with
          | .innerPrefix => livePrimitiveStep iv coins state query word none
          | .innerComplete input =>
              livePrimitiveStep iv coins state query word (some input)
          | .outerPrefix => livePrimitiveStep iv coins state query word none
          | .outerComplete tag embedded =>
              match state.inner embedded with
              | none => pendingPrimitiveStep coins state query tag embedded
              | some input =>
                  if grammar.tagOf input = tag then
                    linkedPrimitiveStep coins state query input
                  else
                    pendingPrimitiveStep coins state query tag embedded
          | .invalid => ordinaryPrimitiveStep coins state query

/-- The simulator is total, and its dependent interface split is the first
native case distinction in the execution tree. -/
def simulatorStep [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : Query C B X) :
    Option (State C B X Tag × AnswerAt query) :=
  match query with
  | ⟨.eval, input⟩ => some (evalStep coins state input)
  | ⟨.prim, point⟩ => some (primitiveStep grammar iv coins state point)

def simulatorMachine [DecidableEq C] [DecidableEq B] [DecidableEq X]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X) :
    InterfaceMachine (Input C B X) (Output C) where
  State := State C B X Tag
  init := initialState iv
  step := simulatorStep grammar iv coins

/-- A real shared-compression world at one fixed compression function. -/
def realMachine (evaluate : Compression C B → X → C)
    (compression : Compression C B) :
    InterfaceMachine (Input C B X) (Output C) where
  State := Unit
  init := ()
  step _ query :=
    match query with
    | ⟨.prim, cb⟩ => some ((), compression cb.1 cb.2)
    | ⟨.eval, input⟩ => some ((), evaluate compression input)

/-- The abstract short-customization SequenceHash evaluation determined by a
typed grammar: compute the inner endpoint and then the matching outer word. -/
def sequenceEval (grammar : Grammar C B X Tag) (iv : C)
    (compression : Compression C B) (input : X) : C :=
  let embedded := mdIterate compression iv (grammar.innerWord input)
  mdIterate compression iv
    (grammar.outerWord (grammar.tagOf input) embedded)

/-- The real joint random system as a law of shared-compression machines. -/
noncomputable def realDependentP
    [Fintype C] [Fintype B] [Nonempty C]
    [DecidableEq C] [DecidableEq B]
    (grammar : Grammar C B X Tag) (iv : C) :
    DependentPDS.Prob
      (SignatureUniverse.ofInterfaces (Input C B X) (Output C))
      (Boundary.ofInterfaces (Input C B X) (Output C)) :=
  Machine.lawOf
    (fun compression => realMachine (sequenceEval grammar iv) compression)
    (Dist.uniform (Compression C B)) Dist.uniform_isProbDist

/-- The ideal random oracle together with the framing-aware simulator, sampled
from independent random-oracle and primitive-tape functions. -/
noncomputable def idealDependentP
    [Fintype C] [Fintype B] [Fintype X] [Nonempty C]
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    DependentPDS.Prob
      (SignatureUniverse.ofInterfaces (Input C B X) (Output C))
      (Boundary.ofInterfaces (Input C B X) (Output C)) :=
  Machine.lawOf
    (fun coins => simulatorMachine grammar iv coins)
    (Dist.uniform (Coins C B X)) Dist.uniform_isProbDist

/-- One-time flattening of the native typed real law into the established
fixed-alphabet PDS engine. -/
noncomputable def realP
    [Fintype C] [Fintype B] [Nonempty C]
    [DecidableEq C] [DecidableEq B]
    (grammar : Grammar C B X Tag) (iv : C) :
    PFunPDS.Prob (Query C B X) (Reply C B X) :=
  (realDependentP grammar iv).flatten

/-- One-time flattening of the native typed ideal/simulator law. -/
noncomputable def idealP
    [Fintype C] [Fintype B] [Fintype X] [Nonempty C]
    [DecidableEq C] [DecidableEq B] [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) :
    PFunPDS.Prob (Query C B X) (Reply C B X) :=
  (idealDependentP grammar iv).flatten

/-! ## Generated case receipts -/

/-- Native two-branch eliminator for a construction query.  Applying this
theorem to a state invariant creates separate repeated/fresh obligations. -/
theorem evalStep_cases [DecidableEq X]
    (coins : Coins C B X) (state : State C B X Tag) (input : X)
    (P : State C B X Tag × C → Prop)
    (repeated : input ∈ state.seen → P (state, coins.1 input))
    (fresh : input ∉ state.seen →
      P (recordEval state input, coins.1 input)) :
    P (evalStep coins state input) := by
  by_cases hseen : input ∈ state.seen
  · simpa only [evalStep, hseen, if_pos] using repeated hseen
  · simpa only [evalStep, hseen, if_neg] using fresh hseen

/-- Native eliminator for primitive execution.  Its nine premises are obtained
from the actual lookup/parser tree, not from a separately curated transition
enum.  The two unlinked terminal orders are intentionally distinct premises:
unknown endpoint and known endpoint with a wrong tag. -/
theorem primitiveStep_cases [DecidableEq C] [DecidableEq B] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : C × B)
    (P : State C B X Tag × C → Prop)
    (repeated : ∀ answer,
      state.table query = some answer → P (state, answer))
    (looseRoot :
      state.table query = none → state.word query.1 = none →
        P (loosePrimitiveStep coins state query))
    (innerPrefix : ∀ path,
      state.table query = none → state.word query.1 = some path →
      grammar.classifyWord (path ++ [query.2]) = .innerPrefix →
        P (livePrimitiveStep iv coins state query (path ++ [query.2]) none))
    (innerComplete : ∀ path input,
      state.table query = none → state.word query.1 = some path →
      grammar.classifyWord (path ++ [query.2]) = .innerComplete input →
        P (livePrimitiveStep iv coins state query (path ++ [query.2])
          (some input)))
    (outerPrefix : ∀ path,
      state.table query = none → state.word query.1 = some path →
      grammar.classifyWord (path ++ [query.2]) = .outerPrefix →
        P (livePrimitiveStep iv coins state query (path ++ [query.2]) none))
    (outerUnknown : ∀ path tag embedded,
      state.table query = none → state.word query.1 = some path →
      grammar.classifyWord (path ++ [query.2]) = .outerComplete tag embedded →
      state.inner embedded = none →
        P (pendingPrimitiveStep coins state query tag embedded))
    (outerWrongTag : ∀ path tag embedded input,
      state.table query = none → state.word query.1 = some path →
      grammar.classifyWord (path ++ [query.2]) = .outerComplete tag embedded →
      state.inner embedded = some input → grammar.tagOf input ≠ tag →
        P (pendingPrimitiveStep coins state query tag embedded))
    (outerLinked : ∀ path tag embedded input,
      state.table query = none → state.word query.1 = some path →
      grammar.classifyWord (path ++ [query.2]) = .outerComplete tag embedded →
      state.inner embedded = some input → grammar.tagOf input = tag →
        P (linkedPrimitiveStep coins state query input))
    (invalid : ∀ path,
      state.table query = none → state.word query.1 = some path →
      grammar.classifyWord (path ++ [query.2]) = .invalid →
        P (ordinaryPrimitiveStep coins state query)) :
    P (primitiveStep grammar iv coins state query) := by
  cases htable : state.table query with
  | some answer =>
      simpa only [primitiveStep, htable] using repeated answer htable
  | none =>
      cases hword : state.word query.1 with
      | none =>
          simpa only [primitiveStep, htable, hword] using
            looseRoot htable hword
      | some path =>
          cases hparse : grammar.classifyWord (path ++ [query.2]) with
          | innerPrefix =>
              simpa only [primitiveStep, htable, hword, hparse] using
                innerPrefix path htable hword hparse
          | innerComplete input =>
              simpa only [primitiveStep, htable, hword, hparse] using
                innerComplete path input htable hword hparse
          | outerPrefix =>
              simpa only [primitiveStep, htable, hword, hparse] using
                outerPrefix path htable hword hparse
          | outerComplete tag embedded =>
              cases hinner : state.inner embedded with
              | none =>
                  simpa only [primitiveStep, htable, hword, hparse, hinner] using
                    outerUnknown path tag embedded htable hword hparse hinner
              | some input =>
                  by_cases htag : grammar.tagOf input = tag
                  · simpa only [primitiveStep, htable, hword, hparse, hinner,
                      htag, if_pos] using
                      outerLinked path tag embedded input htable hword hparse
                        hinner htag
                  · simpa only [primitiveStep, htable, hword, hparse, hinner,
                      htag, if_neg] using
                      outerWrongTag path tag embedded input htable hword hparse
                        hinner htag
          | invalid =>
              simpa only [primitiveStep, htable, hword, hparse] using
                invalid path htable hword hparse

/-- Native four-branch eliminator for destination propagation.  It exposes
the three source tests, so a new collision class cannot be hidden inside a
summary constructor. -/
theorem propagate_cases [DecidableEq C]
    (state : State C B X Tag) (iv value : C) (word : List B)
    (completed : Option X) (P : State C B X Tag → Prop)
    (initial : value = iv → P (markJoin state))
    (live : ∀ previous, value ≠ iv → state.word value = some previous →
      P (markJoin state))
    (loose : value ≠ iv → state.word value = none →
      value ∈ state.loose → P (markJoin state))
    (fresh : value ≠ iv → state.word value = none →
      value ∉ state.loose → P (installLive state value word completed)) :
    P (propagate state iv value word completed) := by
  by_cases hiv : value = iv
  · simpa only [propagate, hiv, if_pos] using initial hiv
  · cases hword : state.word value with
    | some previous =>
        simpa only [propagate, hiv, if_neg, hword] using
          live previous hiv hword
    | none =>
        by_cases hloose : value ∈ state.loose
        · simpa only [propagate, hiv, if_neg, hword, hloose, if_pos] using
            loose hiv hword hloose
        · simpa only [propagate, hiv, if_neg, hword, hloose] using
            fresh hiv hword hloose

/-! ## First invariant: monotonicity of the graph-join flag -/

/-- Once the graph-join flag is set, every destination branch keeps it set.
The four native destination obligations are discharged separately. -/
theorem propagate_join_monotone [DecidableEq C]
    (state : State C B X Tag) (iv value : C) (word : List B)
    (completed : Option X) (hjoin : state.join = true) :
    (propagate state iv value word completed).join = true := by
  apply propagate_cases state iv value word completed
      (P := fun next => next.join = true)
  · intro _hiv
    rfl
  · intro _previous _hne _hword
    rfl
  · intro _hne _hword _hloose
    rfl
  · intro _hne _hword _hfresh
    simpa [installLive] using hjoin

/-- Every primitive observation branch preserves an already-fired join flag.
Applying `primitiveStep_cases` makes Lean present the repeated, loose-root,
three live parser cases, two distinct unlinked cases, linked case, and invalid
case as separate obligations. -/
theorem primitiveStep_join_monotone [DecidableEq C] [DecidableEq B]
    [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : C × B)
    (hjoin : state.join = true) :
    (primitiveStep grammar iv coins state query).1.join = true := by
  apply primitiveStep_cases grammar iv coins state query
      (P := fun result => result.1.join = true)
  · intro _answer _htable
    exact hjoin
  · intro _htable _hword
    simpa [loosePrimitiveStep, recordLoose, installTable] using hjoin
  · intro path _htable _hword _hparse
    simp only [livePrimitiveStep]
    apply propagate_join_monotone
    simpa [installTable] using hjoin
  · intro path input _htable _hword _hparse
    simp only [livePrimitiveStep]
    apply propagate_join_monotone
    simpa [installTable] using hjoin
  · intro path _htable _hword _hparse
    simp only [livePrimitiveStep]
    apply propagate_join_monotone
    simpa [installTable] using hjoin
  · intro path tag embedded _htable _hword _hparse _hinner
    simpa [pendingPrimitiveStep, recordPending, installTable] using hjoin
  · intro path tag embedded input _htable _hword _hparse _hinner _htag
    simpa [pendingPrimitiveStep, recordPending, installTable] using hjoin
  · intro path tag embedded input _htable _hword _hparse _hinner _htag
    simpa [linkedPrimitiveStep, installTable] using hjoin
  · intro path _htable _hword _hparse
    simpa [ordinaryPrimitiveStep, installTable] using hjoin

/-- The repeated/fresh construction split also preserves an already-fired
join flag. -/
theorem evalStep_join_monotone [DecidableEq X]
    (coins : Coins C B X) (state : State C B X Tag) (input : X)
    (hjoin : state.join = true) :
    (evalStep coins state input).1.join = true := by
  apply evalStep_cases coins state input
      (P := fun result => result.1.join = true)
  · intro _hseen
    exact hjoin
  · intro _hfresh
    simpa [recordEval] using hjoin

/-- Every simulator step is defined; no query case is silently dropped. -/
theorem simulator_step_isSome [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : Query C B X) :
    (simulatorStep grammar iv coins state query).isSome := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | prim => rfl
  | eval => rfl

/-- The dependent public-interface split cannot clear a fired graph join.
Both obligations come from the live `Query` interface constructor. -/
theorem simulatorStep_join_monotone [DecidableEq C] [DecidableEq B]
    [DecidableEq X] [DecidableEq Tag]
    (grammar : Grammar C B X Tag) (iv : C) (coins : Coins C B X)
    (state : State C B X Tag) (query : Query C B X)
    (hjoin : state.join = true) :
    (simulatorStep grammar iv coins state query).get
        (simulator_step_isSome grammar iv coins state query) |>.1.join = true := by
  rcases query with ⟨interface, input⟩
  cases interface with
  | prim =>
      simpa only [simulatorStep, Option.get_some] using
        primitiveStep_join_monotone grammar iv coins state input hjoin
  | eval =>
      simpa only [simulatorStep, Option.get_some] using
        evalStep_join_monotone coins state input hjoin

end MDSimulator
end RandomSystemsModel
end SequenceHash
