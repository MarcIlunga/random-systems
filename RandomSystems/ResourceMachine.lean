/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.TypedResource

/-!
# Resources as packages

The resource-side analogue of `ProtocolFn.ofStep`: a stateful "package"
presentation of a typed resource (Jost thesis, Fig. 2.2 style) whose
`DependentDDS` well-formedness obligations (`empty_not_mem`, `prefix_closed`)
are discharged once, generically, in `Machine.toDDS`.

Authoring a resource this way costs a state type, an initial state, and one
`step` function.  With `SignatureUniverse.ofInterfaces` there is no code layer
either: the signature is exactly the per-interface input and output alphabets
(`InterfaceMachine`).

`Machine.toDDS_eq_of_bisim` makes the state representation *refactorable*: two
machines related by a bisimulation with equal answers denote the same
resource, so nothing proved about the denotation has to be reproved when the
state changes shape.

Partiality contract (DESIGN.md §10.8):
* `step state query = none`  — the extended history is OUTSIDE the domain:
  blocking divergence after flattening (`Part.none`).  No continuation.
* a rejection that permits continuation is an ORDINARY VALUE of the answer
  fibre (e.g. `Option.none`, or a named error constructor), written
  `some (state, value)` like any other answer.
The two are different authorial acts and neither is a default: `Machine.step`
is a total function into `Option`, so Lean's own exhaustiveness checking
forces the author to decide each case explicitly.  Nothing is totalized on
the author's behalf (DESIGN.md §4 item 11).
-/

namespace RandomSystems.CR18.TypedResource

universe c i s u v

/-- A stateful package denoting a typed resource: persistent state, its
initialization, and one total step function from the active query to an
optional (next state, answer-in-the-query's-fibre) pair.  `none` marks the
extended history as outside the resource domain (blocking divergence); a
rejection after which the caller may continue must be an ordinary value in
the advertised answer fibre. -/
structure Machine {I : Type i} (U : SignatureUniverse.{c, u, v})
    (sigma : Boundary U I) where
  State : Type s
  init : State
  step : (state : State) → (query : Query U sigma) →
    Option (State × AnswerAt query)

/-- A package at a **one-code-per-interface** signature: the whole declaration
is the two per-interface alphabet families, with no code inductive and no
interface-to-code map.  See `SignatureUniverse.ofInterfaces` for the scope of
that simplification. -/
abbrev InterfaceMachine {I : Type c} (input : I → Type u) (output : I → Type v) :=
  Machine (SignatureUniverse.ofInterfaces input output)
    (Boundary.ofInterfaces input output)

/-- The dependent resource denoted at a one-code-per-interface signature. -/
abbrev InterfaceResource {I : Type c} (input : I → Type u) (output : I → Type v) :=
  DependentDDS (SignatureUniverse.ofInterfaces input output)
    (Boundary.ofInterfaces input output)

/-- The queries a one-code-per-interface package reads. -/
abbrev InterfaceQuery {I : Type c} (input : I → Type u) (output : I → Type v) :=
  Query (SignatureUniverse.ofInterfaces input output)
    (Boundary.ofInterfaces input output)

namespace Machine

variable {I : Type i} {U : SignatureUniverse.{c, u, v}} {sigma : Boundary U I}

/-- Every declared machine transition returns an answer.  This is stronger
than totality of a bounded denotation and is the natural package-level
condition for machines such as lazy random-function simulators. -/
def StepTotal (m : Machine U sigma) : Prop :=
  ∀ state query, (m.step state query).isSome

/-- Run the package from a state through a query list; `none` as soon as any
step is undefined. -/
def runFrom (m : Machine U sigma) :
    m.State → List (Query U sigma) → Option m.State
  | state, [] => some state
  | state, query :: rest =>
      (m.step state query).bind fun next => runFrom m next.1 rest

/-- The state reached after a history, from the initial state. -/
def run (m : Machine U sigma) (history : List (Query U sigma)) :
    Option m.State :=
  m.runFrom m.init history

variable (m : Machine U sigma)

@[simp]
theorem runFrom_nil (state : m.State) : m.runFrom state [] = some state := by
  simp [runFrom]

@[simp]
theorem runFrom_cons (state : m.State) (query : Query U sigma)
    (rest : List (Query U sigma)) :
    m.runFrom state (query :: rest) =
      (m.step state query).bind fun next => m.runFrom next.1 rest := by
  simp [runFrom]

theorem runFrom_append (state : m.State)
    (left right : List (Query U sigma)) :
    m.runFrom state (left ++ right) =
      (m.runFrom state left).bind fun middle => m.runFrom middle right := by
  induction left generalizing state with
  | nil => simp
  | cons query rest ih =>
      simp only [List.cons_append, runFrom_cons]
      cases hstep : m.step state query with
      | none => simp
      | some next => simp [ih]

/-- The machine's move at the last query of a nonempty history: run over the
strict prefix, then take one step at the final query. -/
def lastStep (history : List (Query U sigma)) (nonempty : history ≠ []) :
    Option (m.State × AnswerAt (history.getLast nonempty)) :=
  (m.run history.dropLast).bind fun state =>
    m.step state (history.getLast nonempty)

/-- Running a full history is running its strict prefix and then the last
step, forgetting the answer. -/
theorem run_eq_lastStep_map (history : List (Query U sigma))
    (nonempty : history ≠ []) :
    m.run history = (m.lastStep history nonempty).map Prod.fst := by
  conv_lhs => rw [← List.dropLast_append_getLast nonempty]
  rw [run, runFrom_append, lastStep, ← run, Option.map_bind]
  refine congrArg _ (funext fun state => ?_)
  cases hstep : m.step state (history.getLast nonempty) with
  | none => simp [hstep]
  | some next => simp [hstep]

/-- Interpret the package as a native dependent resource.  The domain is
"every step defined"; `empty_not_mem` and `prefix_closed` are discharged
here, once, for every package.

**Scheduling caveat.**  `m.run` folds the history through the state machine, so
`isSome` may depend on the *order* of queries and not merely on which were
asked.  Unlike the `countWith`-budget domains of the symmetric endpoints, a
`Machine` is therefore **not** `DependentDDS.ScheduleAgnostic` in general: this
constructor is expressive enough to encode a scheduling constraint.  Any
machine whose security statement should admit a rushing adversary owes its own
`ScheduleAgnostic` receipt — see `RandomSystems.CR18.TypedResource` and
`STATUS.md` §11.31. -/
def toDDS : DependentDDS U sigma where
  domain := {history | history ≠ [] ∧ (m.run history).isSome}
  empty_not_mem := by simp
  prefix_closed := by
    intro left right hprefix leftNonempty rightMember
    refine ⟨leftNonempty, ?_⟩
    obtain ⟨suffix, rfl⟩ := hprefix
    have hsome := rightMember.2
    rw [run, runFrom_append] at hsome
    cases h : m.runFrom m.init left with
    | none => rw [h] at hsome; simp at hsome
    | some state => simp [run, h]
  output := fun history nonempty member =>
    ((m.lastStep history nonempty).get (by
      have hsome := member.2
      rw [m.run_eq_lastStep_map history nonempty] at hsome
      simpa using hsome)).2

/-- A step-total machine reaches a state after every finite query history. -/
theorem runFrom_isSome_of_stepTotal (total : StepTotal m)
    (state : m.State) (history : List (Query U sigma)) :
    (m.runFrom state history).isSome := by
  induction history generalizing state with
  | nil => simp
  | cons query rest inductionHypothesis =>
      cases transition : m.step state query with
      | none =>
          have impossible := total state query
          simp [transition] at impossible
      | some next =>
          simpa [runFrom_cons, transition] using
            inductionHypothesis next.1

/-- Package-level totality implies that `Machine.run` succeeds on every
history. -/
theorem run_isSome_of_stepTotal (total : StepTotal m)
    (history : List (Query U sigma)) : (m.run history).isSome := by
  exact runFrom_isSome_of_stepTotal m total m.init history

@[simp]
theorem toDDS_domain :
    m.toDDS.domain = {history | history ≠ [] ∧ (m.run history).isSome} :=
  rfl

/-- Membership in the package resource's domain, in machine vocabulary. -/
theorem mem_toDDS_domain_iff (history : List (Query U sigma)) :
    history ∈ m.toDDS.domain ↔
      history ≠ [] ∧ (m.run history).isSome :=
  Iff.rfl

/-- The package resource answers whatever the step function prescribed at
the last query.  Stated with the prescription as a hypothesis, so no
transport across `List.getLast` is ever needed. -/
theorem toDDS_output (history : List (Query U sigma))
    (nonempty : history ≠ []) (member : history ∈ m.toDDS.domain)
    {state : m.State} {answer : AnswerAt (history.getLast nonempty)}
    (hstep : m.lastStep history nonempty = some (state, answer)) :
    m.toDDS.output history nonempty member = answer := by
  simp [toDDS, hstep]

/-- Initialization sampling (Jost §2.1.2: "`x ←$ X`" in the Initialization
block): a seed-indexed family of packages under a seed law denotes a
probability law over deterministic resources.  Observationally this agrees
with the paper's lazy first-query initialization, since nothing about a
resource is observable before its first query. -/
noncomputable def lawOf {Omega : Type*} (machine : Omega → Machine U sigma)
    (seed : RandomSystems.Dist Omega) (normalized : seed.isProbDist) :
    DependentPDS.Prob U sigma :=
  ⟨RandomSystems.Dist.fTransform (fun omega => (machine omega).toDDS) seed,
    RandomSystems.Dist.fTransform_isProbDist _ normalized⟩

end Machine

/-- Two dependent resources with equal domains and pointwise-equal outputs
are equal.  Migration receipt tool: a package re-expression of an existing
fold-style model is proved equal through this. -/
theorem DependentDDS.ext' {I : Type i} {U : SignatureUniverse.{c, u, v}}
    {sigma : Boundary U I} {left right : DependentDDS U sigma}
    (domainEq : left.domain = right.domain)
    (outputEq : ∀ (history : List (Query U sigma))
      (nonempty : history ≠ [])
      (memLeft : history ∈ left.domain)
      (memRight : history ∈ right.domain),
      left.output history nonempty memLeft =
        right.output history nonempty memRight) :
    left = right := by
  obtain ⟨domL, emptyL, prefixL, outL⟩ := left
  obtain ⟨domR, emptyR, prefixR, outR⟩ := right
  subst domainEq
  simp only [DependentDDS.mk.injEq, heq_eq_eq, true_and]
  funext history nonempty member
  exact outputEq history nonempty member member

namespace Machine

variable {I : Type i} {U : SignatureUniverse.{c, u, v}} {sigma : Boundary U I}

/-! ### Bisimulation: the state representation is refactorable

`toDDS` is determined by `run`, so a relation on states holding at
initialization and preserved by `step` with **equal answers** already fixes
the denoted resource.  Changing how a resource stores its state therefore
costs one relation proof, not a reproof of anything stated about the
resource.

The step condition is spelled without an `Option` relation lifting (mathlib
and Batteries have none): a single `Option.map` equation says the two moves
are defined on exactly the same side and carry the same answer, and a second
clause says the successor states stay related. -/

/-- A bisimulation is preserved along an entire history. -/
theorem runFrom_bisim {m₁ m₂ : Machine U sigma}
    {rel : m₁.State → m₂.State → Prop}
    (hstep : ∀ {state₁ : m₁.State} {state₂ : m₂.State}, rel state₁ state₂ →
      ∀ query : Query U sigma,
        (m₁.step state₁ query).map Prod.snd =
            (m₂.step state₂ query).map Prod.snd ∧
          ∀ next₁ next₂, m₁.step state₁ query = some next₁ →
            m₂.step state₂ query = some next₂ → rel next₁.1 next₂.1)
    (history : List (Query U sigma)) :
    ∀ {state₁ : m₁.State} {state₂ : m₂.State}, rel state₁ state₂ →
      (m₁.runFrom state₁ history).isSome =
          (m₂.runFrom state₂ history).isSome ∧
        ∀ final₁ final₂, m₁.runFrom state₁ history = some final₁ →
          m₂.runFrom state₂ history = some final₂ → rel final₁ final₂ := by
  induction history with
  | nil =>
      intro state₁ state₂ related
      refine ⟨rfl, ?_⟩
      simp only [runFrom_nil, Option.some.injEq]
      rintro _ _ rfl rfl
      exact related
  | cons query rest ih =>
      intro state₁ state₂ related
      obtain ⟨answers, successors⟩ := hstep related query
      cases move₁ : m₁.step state₁ query with
      | none =>
          have move₂ : m₂.step state₂ query = none := by
            rw [move₁] at answers
            simpa using answers.symm
          simp [move₁, move₂]
      | some next₁ =>
          cases move₂ : m₂.step state₂ query with
          | none =>
              rw [move₁, move₂] at answers
              simp at answers
          | some next₂ =>
              have := ih (successors next₁ next₂ move₁ move₂)
              simpa [move₁, move₂] using this

/-- **Bisimulation.** A relation holding at initialization and preserved by
`step` with equal answers identifies the denoted resources.  Nothing about
`toDDS` other than `run` is used, so the two machines may have entirely
different state types. -/
theorem toDDS_eq_of_bisim {m₁ m₂ : Machine U sigma}
    (rel : m₁.State → m₂.State → Prop) (hinit : rel m₁.init m₂.init)
    (hstep : ∀ {state₁ : m₁.State} {state₂ : m₂.State}, rel state₁ state₂ →
      ∀ query : Query U sigma,
        (m₁.step state₁ query).map Prod.snd =
            (m₂.step state₂ query).map Prod.snd ∧
          ∀ next₁ next₂, m₁.step state₁ query = some next₁ →
            m₂.step state₂ query = some next₂ → rel next₁.1 next₂.1) :
    m₁.toDDS = m₂.toDDS := by
  have agree : ∀ history : List (Query U sigma),
      (m₁.run history).isSome = (m₂.run history).isSome ∧
        ∀ final₁ final₂, m₁.run history = some final₁ →
          m₂.run history = some final₂ → rel final₁ final₂ :=
    fun history => runFrom_bisim hstep history hinit
  refine DependentDDS.ext' ?_ ?_
  · ext history
    simp only [toDDS_domain, Set.mem_setOf_eq, (agree history).1]
  · intro history nonempty memberLeft memberRight
    -- Both machines reach a state after the strict prefix …
    obtain ⟨reached₁, atPrefix₁⟩ :
        ∃ state, m₁.run history.dropLast = some state := by
      cases hrun : m₁.run history.dropLast with
      | none =>
          exfalso
          have hsome := memberLeft.2
          rw [m₁.run_eq_lastStep_map history nonempty] at hsome
          simp [lastStep, hrun] at hsome
      | some state => exact ⟨state, rfl⟩
    obtain ⟨reached₂, atPrefix₂⟩ :
        ∃ state, m₂.run history.dropLast = some state := by
      cases hrun : m₂.run history.dropLast with
      | none =>
          exfalso
          have hsome := memberRight.2
          rw [m₂.run_eq_lastStep_map history nonempty] at hsome
          simp [lastStep, hrun] at hsome
      | some state => exact ⟨state, rfl⟩
    -- … in related states, so they answer the last query identically.
    have related : rel reached₁ reached₂ :=
      (agree history.dropLast).2 reached₁ reached₂ atPrefix₁ atPrefix₂
    obtain ⟨answers, _⟩ := hstep related (history.getLast nonempty)
    have last₁ : m₁.lastStep history nonempty =
        m₁.step reached₁ (history.getLast nonempty) := by
      simp [lastStep, atPrefix₁]
    have last₂ : m₂.lastStep history nonempty =
        m₂.step reached₂ (history.getLast nonempty) := by
      simp [lastStep, atPrefix₂]
    cases move₁ : m₁.step reached₁ (history.getLast nonempty) with
    | none =>
        exfalso
        have hsome := memberLeft.2
        rw [m₁.run_eq_lastStep_map history nonempty, last₁, move₁] at hsome
        simp at hsome
    | some next₁ =>
        cases move₂ : m₂.step reached₂ (history.getLast nonempty) with
        | none =>
            exfalso
            rw [move₁, move₂] at answers
            simp at answers
        | some next₂ =>
            rw [move₁, move₂] at answers
            rw [m₁.toDDS_output history nonempty memberLeft
                (state := next₁.1) (answer := next₁.2) (by rw [last₁, move₁]),
              m₂.toDDS_output history nonempty memberRight
                (state := next₂.1) (answer := next₂.2) (by rw [last₂, move₂])]
            simpa using answers

end Machine

/-! ## Worked example: Jost thesis Figure 2.2, verbatim

`AuthChan` (printed p. 28) and `Key`, re-expressed as packages.  Compare
line-for-line with the figure:

```
Resource AuthChan
  Initialization
    M_A[·] ← ⊥ ; m_B ← ⊥ ; n ← 0
  Interface A
    Input: (send, m) ∈ E.C
      n ← n+1 ; M_A[n] ← m ; output ok
  Interface B
    Input: receive
      output m_B
  Interface E
    Input: (leak, i) ∈ ℕ
      output M_A[i]
  Interface I, I ∈ {E,F}
    Input: (deliver, i) ∈ ℕ
      m_B ← M_A[i] ; output ok
```
-/

namespace JostFigure22

/-- The four interfaces of Fig. 2.1/2.2: Alice, Bob, Eve, and the free
interface F. -/
inductive Iface | A | B | E | F
  deriving DecidableEq

/-- Alice sends a message. -/
inductive SenderIn (M : Type) | send (message : M)

/-- Bob asks for the delivered message. -/
inductive ReceiverIn | receive

/-- Eve leaks a sent message or delivers one; `(leak, i)` and
`(deliver, i)` are two input patterns AT THE SAME interface. -/
inductive EveIn | leak (index : ℕ) | deliver (index : ℕ)

/-- The free interface delivers. -/
inductive FreeIn | deliver (index : ℕ)

/-- Jost's `ok`. -/
inductive Ok | ok

/-- Eve's answer fibre: a leak answer (`M_A[i]`, possibly `⊥` — an ordinary
value, NOT divergence) or a delivery acknowledgement. -/
inductive EveOut (M : Type) | leaked (message? : Option M) | ok

/-- The channel's per-interface input alphabets — with
`SignatureUniverse.ofInterfaces` this and `chanOut` are the ENTIRE signature
declaration: no code inductive, no interface-to-code map. -/
def chanIn (M : Type) : Iface → Type
  | .A => SenderIn M
  | .B => ReceiverIn
  | .E => EveIn
  | .F => FreeIn

/-- The channel's per-interface output alphabets. -/
def chanOut (M : Type) : Iface → Type
  | .A => Ok
  | .B => Option M
  | .E => EveOut M
  | .F => Ok

/-- The package state: `M_A`, `m_B`, `n` — exactly the figure's
Initialization block, as data. -/
structure ChanState (M : Type) where
  sent : ℕ → Option M
  delivered : Option M
  count : ℕ

/-- Fig. 2.2's `AuthChan`, one clause per pseudocode line.  Every clause is
`some _`: Jost's channel is total on its declared per-interface patterns,
and all its `⊥`s are values. -/
def authChan (M : Type) : InterfaceMachine (chanIn M) (chanOut M) where
  State := ChanState M
  init := ⟨fun _ => none, none, 0⟩
  step state query :=
    match query with
    | ⟨.A, .send m⟩ =>
        some ({ state with
          count := state.count + 1,
          sent := Function.update state.sent (state.count + 1) (some m) },
          .ok)
    | ⟨.B, .receive⟩ => some (state, state.delivered)
    | ⟨.E, .leak i⟩ => some (state, .leaked (state.sent i))
    | ⟨.E, .deliver i⟩ => some ({ state with delivered := state.sent i }, .ok)
    | ⟨.F, .deliver i⟩ => some ({ state with delivered := state.sent i }, .ok)

/-- The denoted resource: obligations discharged by `toDDS`, no per-model
proof. -/
def authChanResource (M : Type) : InterfaceResource (chanIn M) (chanOut M) :=
  (authChan M).toDDS

section Regression

variable {M : Type} (m₀ m₁ : M)

/-- send, deliver 1, receive — Bob gets Alice's first message. -/
example :
    (authChanResource M).output
      [⟨.A, .send m₀⟩, ⟨.E, .deliver 1⟩, ⟨.B, .receive⟩]
      (by simp) (by simp [authChanResource, Machine.run, authChan]) =
      some m₀ := by
  apply Machine.toDDS_output
  simp [Machine.lastStep, Machine.run, authChan, Function.update]
  rfl

/-- Leaking an unsent index answers `⊥` as a VALUE: the history stays in the
domain and interaction continues. -/
example :
    (authChanResource M).output
      [⟨.A, .send m₀⟩, ⟨.E, .leak 7⟩]
      (by simp) (by simp [authChanResource, Machine.run, authChan]) =
      .leaked none := by
  apply Machine.toDDS_output
  simp [Machine.lastStep, Machine.run, authChan, Function.update]
  rfl

/-- Two sends then leak 2 — the figure's `M_A[n] ← m` bookkeeping. -/
example :
    (authChanResource M).output
      [⟨.A, .send m₀⟩, ⟨.A, .send m₁⟩, ⟨.E, .leak 2⟩]
      (by simp) (by simp [authChanResource, Machine.run, authChan]) =
      .leaked (some m₁) := by
  apply Machine.toDDS_output
  simp [Machine.lastStep, Machine.run, authChan, Function.update]
  rfl

end Regression

/-! ### The `Key` resource: sampling in Initialization -/

/-- Key's two interfaces. -/
inductive KeyIface | a | b
  deriving DecidableEq

/-- `fetch`. -/
inductive FetchIn | fetch

/-- One code SHARED by both interfaces (Fig. 2.2 writes "Interface
I, I ∈ {A, B}"): the boundary is not injective, so `Boundary.ofInterfaces`
does not apply and the code layer is written by hand. -/
def keySig (K : Type) : SignatureUniverse.{0, 0, 0} where
  Code := Unit
  input _ := FetchIn
  output _ := K

def keyBoundary (K : Type) : Boundary (keySig K) KeyIface := fun _ => ()

/-- The deterministic fibre of Fig. 2.2's `Key` at a fixed sampled key. -/
def keyMachine (K : Type) (k : K) : Machine (keySig K) (keyBoundary K) where
  State := Unit
  init := ()
  step _ query :=
    match query with
    | ⟨_, .fetch⟩ => some ((), k)

/-- Fig. 2.2's `Key`: `Initialization k ←$ K` becomes a pushforward law over
the deterministic fibres — a `Prob`, not a single deterministic system. -/
noncomputable def keyLaw (K : Type) [Fintype K] [Nonempty K] :
    DependentPDS.Prob (keySig K) (keyBoundary K) :=
  Machine.lawOf (keyMachine K) (RandomSystems.Dist.uniform K)
    RandomSystems.Dist.uniform_isProbDist

/-! ### Genuine partiality: what Jost's notation cannot say

A one-message channel whose SECOND send is outside the domain.  The `none`
branch is an explicit authorial act — the package cannot be written without
deciding it, and the elaborated term contains no default. -/

/-- One-message variant: second send diverges (domain restriction), receive
before delivery answers `⊥` as a value (continuation allowed).  The two
partialities are different constructors on different sides of `Option`. -/
def oneShotChan (M : Type) : InterfaceMachine (chanIn M) (chanOut M) where
  State := ChanState M
  init := ⟨fun _ => none, none, 0⟩
  step state query :=
    match query with
    | ⟨.A, .send m⟩ =>
        if state.count = 0 then
          some ({ state with
            count := 1,
            sent := Function.update state.sent 1 (some m) }, .ok)
        else
          none   -- second send: history OUTSIDE the domain
    | ⟨.B, .receive⟩ => some (state, state.delivered)
    | ⟨.E, .leak i⟩ => some (state, .leaked (state.sent i))
    | ⟨.E, .deliver i⟩ => some ({ state with delivered := state.sent i }, .ok)
    | ⟨.F, .deliver i⟩ => some ({ state with delivered := state.sent i }, .ok)

/-- The second send is not in the domain: the machine vocabulary decides
domain membership by computation. -/
example {M : Type} (m₀ m₁ : M) :
    [(⟨.A, .send m₀⟩ : InterfaceQuery (chanIn M) (chanOut M)), ⟨.A, .send m₁⟩] ∉
      ((oneShotChan M).toDDS).domain := by
  simp [Machine.run, oneShotChan]

/-- The first send is. -/
example {M : Type} (m₀ : M) :
    [(⟨.A, .send m₀⟩ : InterfaceQuery (chanIn M) (chanOut M))] ∈
      ((oneShotChan M).toDDS).domain := by
  simp [Machine.run, oneShotChan]

/-! ### Refactoring the state: the same channel, kept as a log

`ChanState` stores the sent messages as a partial function `ℕ → Option M`
updated pointwise, plus a counter.  `ChanLog` stores them as the list of
messages in send order and has no counter at all.  The two are visibly
different data; `Machine.toDDS_eq_of_bisim` shows they denote the *same*
resource, so the three regressions above hold of the log presentation
without being restated. -/

/-- Jost's `M_A[i]` read off a send-ordered log: the figure indexes from `1`
(`n ← n+1 ; M_A[n] ← m`), and `M_A[0]` is never written, so it stays `⊥`. -/
def logLookup {M : Type} (log : List M) (index : ℕ) : Option M :=
  if index = 0 then none else log[index - 1]?

/-- Appending the `n+1`-st message extends the lookup at exactly index
`n+1`. -/
theorem logLookup_append {M : Type} (log : List M) (message : M) (index : ℕ) :
    logLookup (log ++ [message]) index =
      if index = log.length + 1 then some message else logLookup log index := by
  rcases Nat.eq_zero_or_pos index with rfl | positive
  · simp [logLookup]
  simp only [logLookup, if_neg (show index ≠ 0 by omega)]
  rcases lt_trichotomy (index - 1) log.length with below | atEnd | beyond
  · rw [List.getElem?_append_left below, if_neg (by omega)]
  · rw [atEnd, List.getElem?_append_right (Nat.le_refl _), if_pos (by omega)]
    simp
  · rw [List.getElem?_append_right (by omega), if_neg (by omega),
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- 1-based buffer lookup commutes with mapping the entries. -/
theorem logLookup_map {A B : Type} (f : A → B) (l : List A) (i : ℕ) :
    logLookup (l.map f) i = (logLookup l i).map f := by
  by_cases hz : i = 0
  · simp [logLookup, hz]
  · simp [logLookup, hz]

/-- The log presentation: the send-ordered messages, and the delivered
message.  No counter — `n` is the log's length. -/
structure ChanLog (M : Type) where
  log : List M
  delivered : Option M

/-- Fig. 2.2's `AuthChan` again, over the log state. -/
def authChanLog (M : Type) : InterfaceMachine (chanIn M) (chanOut M) where
  State := ChanLog M
  init := ⟨[], none⟩
  step state query :=
    match query with
    | ⟨.A, .send m⟩ => some ({ state with log := state.log ++ [m] }, .ok)
    | ⟨.B, .receive⟩ => some (state, state.delivered)
    | ⟨.E, .leak i⟩ => some (state, .leaked (logLookup state.log i))
    | ⟨.E, .deliver i⟩ =>
        some ({ state with delivered := logLookup state.log i }, .ok)
    | ⟨.F, .deliver i⟩ =>
        some ({ state with delivered := logLookup state.log i }, .ok)

/-- The bisimulation: the counter is the log's length, the delivered messages
agree, and the pointwise sent map is the log's lookup. -/
def chanRel {M : Type} (state : ChanState M) (logged : ChanLog M) : Prop :=
  state.count = logged.log.length ∧ state.delivered = logged.delivered ∧
    ∀ index, state.sent index = logLookup logged.log index

/-- **The refactor is free.**  The pointwise-update channel and the log
channel denote the same resource, so everything already proved about
`authChanResource` transfers with no restatement. -/
theorem authChan_toDDS_eq_authChanLog_toDDS (M : Type) :
    (authChan M).toDDS = (authChanLog M).toDDS := by
  refine Machine.toDDS_eq_of_bisim chanRel
    ⟨rfl, rfl, fun index => by simp [authChan, authChanLog, logLookup]⟩ ?_
  rintro state logged ⟨counts, delivers, lookups⟩ ⟨interface, input⟩
  match interface, input with
  | .A, .send m =>
      refine ⟨rfl, ?_⟩
      intro next₁ next₂ move₁ move₂
      simp only [authChan, authChanLog, Option.some.injEq] at move₁ move₂
      subst move₁
      subst move₂
      refine ⟨by simp [counts], delivers, fun index => ?_⟩
      simp only [logLookup_append, ← counts]
      by_cases hit : index = state.count + 1
      · subst hit
        simp
      · rw [Function.update_of_ne hit, lookups index, if_neg hit]
  | .B, .receive =>
      refine ⟨by simp [authChan, authChanLog, delivers], ?_⟩
      intro next₁ next₂ move₁ move₂
      simp only [authChan, authChanLog, Option.some.injEq] at move₁ move₂
      subst move₁
      subst move₂
      exact ⟨counts, delivers, lookups⟩
  | .E, .leak i =>
      refine ⟨by simp [authChan, authChanLog, lookups i], ?_⟩
      intro next₁ next₂ move₁ move₂
      simp only [authChan, authChanLog, Option.some.injEq] at move₁ move₂
      subst move₁
      subst move₂
      exact ⟨counts, delivers, lookups⟩
  | .E, .deliver i =>
      refine ⟨rfl, ?_⟩
      intro next₁ next₂ move₁ move₂
      simp only [authChan, authChanLog, Option.some.injEq] at move₁ move₂
      subst move₁
      subst move₂
      exact ⟨counts, lookups i, lookups⟩
  | .F, .deliver i =>
      refine ⟨rfl, ?_⟩
      intro next₁ next₂ move₁ move₂
      simp only [authChan, authChanLog, Option.some.injEq] at move₁ move₂
      subst move₁
      subst move₂
      exact ⟨counts, lookups i, lookups⟩

end JostFigure22

end RandomSystems.CR18.TypedResource
