/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.EventComposition
import RandomSystemsCC.ResourceParallel
import RandomSystemsCC.TypedParallel

/-!
# The dependency plain CC cannot express: a channel that degrades when a memory leaks

This is the example Jost opens Chapter 3 with (pp. 7, 32) and returns to when
motivating renaming (p. 36):

> "in secure messaging protocols it is common that for instance the leakage of
> one parties memory (one module) can affect the security of a communication
> channel (another module).  Yet, requesting the memory resource to explicitly
> inform the channel resource about the leakage not only seems unnatural, but is
> in the traditional system model of Constructive Cryptography outright
> impossible.  As a consequence, one would have to model the memory and
> communication channel as one joint resource."

The estate's own version of that verdict is `DESIGN.md` §11.1 rule 2 —
capabilities "needed by one construction are multiplexed into one dependent
typed resource" — recorded there as "a workaround, not a principle".  This file
makes the trade concrete on both sides.

## What is proved

* `chanResource` is a genuine `RandomSystems.CR18.TypedResource.DependentDDS`
  over the event-augmented alphabet, and `chanResource_isEventAware` proves it
  satisfies Jost Definition 3.2.3 with associated event-set `{msgSent}` — so
  `IsEventAware` is a *witnessed* predicate, not an empty one.  Note what the
  channel's event-set does **not** contain: `memLeaked`.  The channel *depends*
  on that event and never *triggers* it.

* `channelGuarantee` is the channel's confidentiality condition, stated as a
  `CompositeEvent` in the sense of §3.2.2 — "the memory leaked before the
  message was sent" — which is a legitimate composite event exactly because
  `EventHistory.precedes_mono` holds.  This is where the deliberate asymmetry of
  Definition 3.2.2 earns its keep: `chanLeak_of_leaked_first` needs the case
  where the memory has leaked and the message has *not yet* been sent.

* `channel_needs_foreign_event` is the impossibility: the channel's behaviour is
  **not** a function of its own events.  Two global histories that agree on
  everything in the channel's event-set produce different leakage.  In the
  traditional system model, where a resource's behaviour is a function of its
  own interaction, no separate channel resource can do this.

* `memLeaked_not_forgeable` is what makes the dependency *sound* rather than
  merely expressible: a compatible distinguisher (Definition 3.3.1) cannot
  fabricate `memLeaked`, so the name really is evidence about the memory.

* `memory_channel_split` runs the general parallel-composition theorem on this
  pair: the two event-sets are disjoint, so inside the composite each module
  still sees a legal interaction of its own.

* `monolith_needs_memory_queries` is the cost of the plain-CC alternative.
  `JointQuery` is the alphabet the joint resource is forced to carry, and the
  theorem shows the joint resource's answer depends on the *memory's queries* —
  which is only possible when the memory and the channel are the same module.

The contrast in one line: without events the dependency has to travel through a
shared **query alphabet** (`JointQuery`), which fuses the two modules; with
events it travels through the global **event history**, which leaves them apart.
-/

namespace RandomSystemsCC.Events.ChannelExample

open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Events

/-! ## Names and the two event-sets -/

/-- The two names in play.  `memLeaked` belongs to the memory module, `msgSent`
to the channel module — and Jost's whole discipline is that ownership of a name
is what decides who may trigger it. -/
inductive ChannelEvent
  /-- The memory module exported the fact that it was read. -/
  | memLeaked
  /-- The channel module exported the fact that a message went out. -/
  | msgSent
  deriving DecidableEq

open ChannelEvent

/-- The memory module's associated event-set `𝒩_Mem`. -/
def memoryEvents : Set ChannelEvent := {memLeaked}

/-- The channel module's associated event-set `𝒩_Chan`.  It does **not**
contain `memLeaked`: the channel reads that name, it never writes it. -/
def channelEvents : Set ChannelEvent := {msgSent}

theorem memory_channel_disjoint : Disjoint memoryEvents channelEvents := by
  rw [Set.disjoint_left]
  rintro n rfl h
  exact absurd h (by simp [channelEvents])

theorem memLeaked_not_channel : memLeaked ∉ channelEvents := by
  simp [channelEvents]

/-! ## The channel's guarantee, as a composite event -/

/-- **The cross-module condition.**  The channel's confidentiality is lost
exactly when the memory leaked before the message went out.  This is a
composite event in the sense of §3.2.2 — a monotone condition on the global
history — and it is monotone because `EventHistory.precedes_mono` is. -/
def channelGuarantee : CompositeEvent ChannelEvent := precedesEvent memLeaked msgSent

/-- The channel's leakage: the message becomes visible exactly on
`channelGuarantee`. -/
def chanLeak {Msg : Type} (history : EventHistory ChannelEvent) (message : Msg) :
    Option Msg :=
  if history.Precedes memLeaked msgSent then some message else none

theorem chanLeak_none_of_not_precedes {Msg : Type} {history : EventHistory ChannelEvent}
    {message : Msg} (safe : ¬ history.Precedes memLeaked msgSent) :
    chanLeak history message = none := by simp [chanLeak, safe]

/-- **The asymmetric disjunct of Definition 3.2.2, put to work.**  If the memory
has leaked and the message has not gone out yet, the channel is already
compromised — we do not have to wait for the send, and Jost's p. 34 remark
("we do not need to insist that the memory actually leaked", in its mirror
form) is exactly this case. -/
theorem chanLeak_of_leaked_first {Msg : Type} {history : EventHistory ChannelEvent}
    (message : Msg) (leaked : history.Occurred memLeaked)
    (notSent : ¬ history.Occurred msgSent) :
    chanLeak history message = some message := by
  simp [chanLeak, EventHistory.precedes_of_not_occurred leaked notSent]

/-- Compromise is never undone: once the guarantee is lost it stays lost, along
every continuation of the interaction. -/
theorem chanLeak_mono {Msg : Type} {E F : EventHistory ChannelEvent} (extends' : E ≤ F)
    {message : Msg} (compromised : chanLeak E message = some message) :
    chanLeak F message = some message := by
  by_cases pre : E.Precedes memLeaked msgSent
  · simp [chanLeak, EventHistory.precedes_mono extends' pre]
  · simp [chanLeak, pre] at compromised

/-! ## The impossibility: the channel is not a function of its own events -/

/-- **The dependency plain CC cannot express.**  Two global histories that agree
on *every* name the channel owns produce different channel behaviour.

In the traditional Constructive Cryptography system model a resource's behaviour
is a function of its own interaction, so no separate channel resource can
realize this: the deciding information (`memLeaked`) never crosses the channel's
interface and is not in its event-set.  With a global event history it does not
have to cross any interface at all. -/
theorem channel_needs_foreign_event {Msg : Type} (message : Msg) :
    ∃ E F : EventHistory ChannelEvent,
      (∀ n ∈ channelEvents, E.Occurred n ↔ F.Occurred n) ∧
        chanLeak E message ≠ chanLeak F message := by
  refine ⟨⟨[memLeaked, msgSent], by decide⟩, ⟨[msgSent], by decide⟩, ?_, ?_⟩
  · rintro n rfl
    simp [EventHistory.Occurred]
  · have compromised : chanLeak (⟨[memLeaked, msgSent], by decide⟩ : EventHistory ChannelEvent)
        message = some message := by
      refine if_pos ?_
      exact ⟨by simp [EventHistory.Occurred], Or.inr (by decide)⟩
    have safe : chanLeak (⟨[msgSent], by decide⟩ : EventHistory ChannelEvent)
        message = none := by
      rw [chanLeak]
      refine if_neg ?_
      rintro ⟨occurred, -⟩
      simp [EventHistory.Occurred] at occurred
    rw [compromised, safe]
    exact Option.some_ne_none message

/-- **The event is trustworthy.**  A distinguisher compatible with the
memory/channel pair (Definition 3.3.1) cannot fabricate `memLeaked`: if the name
shows up in what it hands the channel, the memory really produced it.  This is
what turns "the channel reads a foreign name" from a modelling hack into a sound
guarantee. -/
theorem memLeaked_not_forgeable {strategy : EventStrategy ChannelEvent}
    (compatible : IsCompatible (memoryEvents ∪ channelEvents) strategy)
    (trace : List (Step ChannelEvent))
    (announced : memLeaked ∈ (strategy trace).names) :
    memLeaked ∈ (Step.final EventHistory.nil trace).names :=
  not_triggers_of_compatible compatible trace (Or.inl rfl) announced

/-- Jost's parallel composition on this pair: the event-sets are disjoint, so
the composite is event-aware with `𝒩_Mem ∪ 𝒩_Chan` and **both modules still see
a legal interaction of their own** inside it. -/
theorem memory_channel_split {trace : List (TaggedStep ChannelEvent)}
    (par : ParDisciplined memoryEvents channelEvents EventHistory.nil trace) :
    Disciplined (memoryEvents ∪ channelEvents) EventHistory.nil (trace.map Prod.snd) ∧
      Disciplined memoryEvents EventHistory.nil (proj true trace) ∧
        Disciplined channelEvents EventHistory.nil (proj false trace) :=
  ⟨par.merged, ParDisciplined.proj memory_channel_disjoint true par,
    ParDisciplined.proj memory_channel_disjoint false par⟩

/-! ## The channel as a resource on the estate's carrier

Everything above is about the event axis.  This section exhibits an actual
`DependentDDS` over the augmented alphabet and discharges Definition 3.2.3 for
it, so that `IsEventAware` has a witness. -/

section Carrier

variable {Msg : Type}

/-- The channel's query alphabet: Alice sends, Eve asks what leaked. -/
inductive ChanQuery (Msg : Type)
  /-- Alice submits a message. -/
  | send (message : Msg)
  /-- Eve reads whatever the channel is currently leaking. -/
  | leak
  deriving DecidableEq

/-- The channel's signature universe: a single code, one query alphabet, and
`Option Msg` answers (`none` = nothing observable). -/
def chanUniverse (Msg : Type) : SignatureUniverse.{0, 0, 0} where
  Code := Unit
  input _ := ChanQuery Msg
  output _ := Option Msg

/-- The channel's single interface. -/
def chanBoundary (Msg : Type) : Boundary (chanUniverse Msg) Unit := fun _ => ()

/-- Queries of the event-aware channel: a plain query paired with the global
event history, exactly Jost's `𝒳 × 2^ℰ`. -/
abbrev ChanStep (Msg : Type) :=
  Query (withEvents (chanUniverse Msg) ChannelEvent) (chanBoundary Msg)

/-- The plain query carried by an event-aware channel step. -/
def chanQueryOf (step : ChanStep Msg) : ChanQuery Msg := queryBase step

/-- The most recent message Alice submitted. -/
def lastSent (history : List (ChanStep Msg)) : Option Msg :=
  (history.filterMap fun step =>
    match chanQueryOf step with
    | .send message => some message
    | .leak => none).getLast?

/-- The event history the channel returns.  On a send it triggers its own event
`msgSent`; on a leak query it triggers nothing — the channel never writes
`memLeaked`. -/
def chanEventsAfter (history : List (ChanStep Msg)) : EventHistory ChannelEvent :=
  match history.getLast? with
  | none => EventHistory.nil
  | some step =>
      match chanQueryOf step with
      | .send _ => (queryHist step).cons msgSent
      | .leak => queryHist step

@[simp] theorem chanEventsAfter_nil :
    chanEventsAfter ([] : List (ChanStep Msg)) = EventHistory.nil := rfl

theorem chanEventsAfter_concat (history : List (ChanStep Msg)) (step : ChanStep Msg) :
    chanEventsAfter (history ++ [step]) =
      match chanQueryOf step with
      | .send _ => (queryHist step).cons msgSent
      | .leak => queryHist step := by
  simp [chanEventsAfter]

/-- The channel's answer.  A leak query reveals the last message exactly on
`channelGuarantee` — the *foreign* condition this whole file is about. -/
def chanAnswer (history : List (ChanStep Msg)) : Option Msg :=
  match history.getLast? with
  | none => none
  | some step =>
      match chanQueryOf step with
      | .send _ => none
      | .leak => (lastSent history).bind (chanLeak (queryHist step))

/-- **Definition 3.2.3's second clause, as a domain restriction.**  The channel
is "only defined if `ℰ_{Y_{i-1}}` is a prefix of `ℰ_{X_i}` and all additional
elements are *not* from `𝒩_Chan`" — so that condition, at every step, *is* the
domain. -/
def chanDomain (Msg : Type) : Set (List (ChanStep Msg)) :=
  {history | history ≠ [] ∧ ∀ front step, front ++ [step] <+: history →
    ExtendsWithin channelEventsᶜ (chanEventsAfter front) (queryHist step)}

/-- **The event-aware channel, on the estate's own resource carrier.** -/
def chanResource (Msg : Type) :
    DependentDDS (withEvents (chanUniverse Msg) ChannelEvent) (chanBoundary Msg) where
  domain := chanDomain Msg
  empty_not_mem := by rintro ⟨empty, -⟩; exact empty rfl
  prefix_closed := by
    rintro left right isPrefix nonempty ⟨-, steps⟩
    exact ⟨nonempty, fun front step inner => steps front step (inner.trans isPrefix)⟩
  output history nonempty _ := (chanAnswer history, chanEventsAfter history)

@[simp] theorem chanResource_domain (Msg : Type) :
    (chanResource Msg).domain = chanDomain Msg := rfl

/-- The resource's state history is the event history it computes — including at
the empty interaction, where both are `∅`. -/
theorem stateHist_chanResource {history : List (ChanStep Msg)}
    (member : history = [] ∨ history ∈ chanDomain Msg) :
    stateHist (chanResource Msg) history = chanEventsAfter history := by
  rcases member with rfl | member
  · simp
  · rw [stateHist_eq _ member.1 member]
    rfl

/-- **Jost Definition 3.2.3 for the channel, with associated event-set
`𝒩_Chan = {msgSent}`.**

Both clauses land: the channel only ever appends `msgSent` (`appends`), and it
is only defined where the environment has extended the previous output with
names that are not its own (`defined`) — which is precisely how `chanDomain` was
written.  `memLeaked` appears nowhere in the event-set, which is the whole
point: the channel *depends* on it without *owning* it. -/
theorem chanResource_isEventAware (Msg : Type) :
    IsEventAware channelEvents (chanResource Msg) := by
  constructor
  case appends =>
    intro front step member
    have frontState : stateHist (chanResource Msg) (front ++ [step])
        = chanEventsAfter (front ++ [step]) :=
      stateHist_chanResource (Or.inr member)
    rw [frontState, chanEventsAfter_concat]
    cases hq : chanQueryOf step with
    | send message =>
        exact ⟨EventHistory.le_cons _ _, by
          intro n mem notMem
          rcases EventHistory.mem_cons_names.mp mem with inside | rfl
          · exact absurd inside notMem
          · rfl⟩
    | leak => exact ExtendsWithin.refl _ _
  case defined =>
    intro front step member
    have frontState : stateHist (chanResource Msg) front = chanEventsAfter front := by
      refine stateHist_chanResource ?_
      by_cases empty : front = []
      · exact Or.inl empty
      · exact Or.inr ((chanResource Msg).prefix_closed ⟨[step], rfl⟩ empty member)
    rw [frontState]
    exact member.2 front step (List.prefix_refl _)

/-- Non-vacuity of `chanDomain`: a one-step interaction in which the environment
supplies the empty history is legal. -/
theorem chanDomain_singleton (step : ChanStep Msg)
    (fresh : queryHist step = EventHistory.nil) : [step] ∈ chanDomain Msg := by
  refine ⟨by simp, ?_⟩
  rintro front inner isPrefix
  have lenLe : (front ++ [inner]).length ≤ ([step] : List (ChanStep Msg)).length :=
    isPrefix.length_le
  simp only [List.length_append, List.length_cons, List.length_nil] at lenLe
  have frontNil : front = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst frontNil
  have single : [inner] = [step] :=
    (by simpa using isPrefix : ([inner] : List (ChanStep Msg)) <+: [step]).eq_of_length (by simp)
  have stepEq : inner = step := by simpa using single
  subst stepEq
  rw [fresh]
  exact ⟨le_rfl, fun n mem notMem => absurd mem notMem⟩

end Carrier

/-! ## The plain-CC alternative, and what it costs -/

/-- **The query alphabet the monolithic model is forced to carry.**  Without a
global event history the memory and the channel cannot be separate resources, so
there is one resource, and therefore one alphabet, holding *both* modules'
operations.  This is `DESIGN.md` §11.1 rule 2 — multiplexing every capability
into one dependent resource — in its smallest possible instance. -/
inductive JointQuery (Msg : Type)
  /-- The memory module's operation, now living in the channel's alphabet. -/
  | readMemory
  /-- The channel module's operation. -/
  | send (message : Msg)
  deriving DecidableEq

/-- The global history the joint resource has to reconstruct internally from its
own query log — the information the event-aware model reads off the global
event history instead. -/
def jointHistory {Msg : Type} (log : List (JointQuery Msg)) : EventHistory ChannelEvent :=
  log.foldl (fun history query =>
    match query with
    | .readMemory => history.cons memLeaked
    | .send _ => history.cons msgSent) EventHistory.nil

/-- The joint resource's leakage. -/
def jointLeak {Msg : Type} (log : List (JointQuery Msg)) (message : Msg) : Option Msg :=
  chanLeak (jointHistory log) message

/-- Whether a joint query is a channel operation. -/
def isSend {Msg : Type} : JointQuery Msg → Bool
  | .readMemory => false
  | .send _ => true

/-- **What the monolith costs.**  The joint resource's *channel* answer depends
on the *memory's* queries: two logs with identical channel operations give
different leakage.  In the traditional system model that is only expressible
because the two modules have been fused into one resource — which is exactly the
modularity loss Jost's global event history exists to avoid, and exactly what
`channel_needs_foreign_event` shows a separate channel resource cannot do
without events. -/
theorem monolith_needs_memory_queries {Msg : Type} (message : Msg) :
    ∃ quiet noisy : List (JointQuery Msg),
      quiet.filter isSend = noisy.filter isSend ∧
        jointLeak quiet message ≠ jointLeak noisy message := by
  refine ⟨[JointQuery.send message], [JointQuery.readMemory, JointQuery.send message], ?_, ?_⟩
  · simp [isSend]
  · have safe : jointLeak [JointQuery.send message] message = none := by
      rw [jointLeak, chanLeak]
      refine if_neg ?_
      rintro ⟨occurred, -⟩
      simp [jointHistory, EventHistory.cons, EventHistory.Occurred] at occurred
    have compromised :
        jointLeak [JointQuery.readMemory, JointQuery.send message] message = some message := by
      rw [jointLeak, chanLeak]
      refine if_pos ?_
      refine ⟨by simp [jointHistory, EventHistory.cons, EventHistory.Occurred], Or.inr ?_⟩
      simp [jointHistory, EventHistory.cons]
    rw [safe, compromised]
    exact (Option.some_ne_none message).symm

end RandomSystemsCC.Events.ChannelExample

/-! ## The carrier-level payoff: `∥` exists on the event-augmented alphabet

`memory_channel_split` above composes the two modules on Jost's *event* axis
(disjoint event-sets, `Events.ParDisciplined.proj`).  These receipts pin the
other half — that Abstract Cryptography's own `R ∥ S` is available on the
event-augmented carrier at all, so `[R, S]` and CC's parallel-composition rule
are statable about event-aware resources.

Both `Par` instances are gated on `HasSumCode`, and
`Events.instHasSumCodeWithEvents` is the only thing that supplies it here: the
augmented alphabets distribute over `⊕` strictly up to `Equiv.sumProdDistrib`
and never on the nose, so under a type-equality alphabet law the event carrier
would have had no parallel composition whatsoever.  It is also the estate's
only `∥`-capable signature whose boundary equivalence is not the identity: the
two `DemoU` universes of `RandomSystemsCC.ParallelChecks` and
`RandomSystemsCC.TypedParallelChecks` both supply `Equiv.refl`.
-/

namespace RandomSystemsCC.Events

open AbstractCrypto
open RandomSystems.CR18.TypedResource
open scoped AbstractCrypto

universe c i u

noncomputable section

/-- Parallel composition on the strict single-signature carrier over the
event-augmented alphabet. -/
example {N : Type u} {U : SignatureUniverse.{c, u, u}} [DecidableEq U.Code]
    [HasSumCode U] : Par (RandomSystemsCC.CR18.Resource (withEvents U N)) :=
  inferInstance

/-- **The acceptance receipt**: `Par` on the carrier every CC endpoint of this
estate lives on, over the event-augmented alphabet. -/
example {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
    [DecidableEq I] [DecidableEq U.Code] [HasSumCode U] :
    Par (RandomSystemsCC.TypedFinite.Phi I (withEvents U N)) :=
  inferInstance

/-- MauRen11 eq. (3) comes with it: the contextual metric on event-aware
resources is `∥`-non-expanding, which is the metric premise of
`CC.SecurelyConstructs.par`/`par_left`. -/
example {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
    [DecidableEq I] [DecidableEq U.Code] [HasSumCode U] :
    IsNonexpandingPar (RandomSystemsCC.TypedFinite.Phi I (withEvents U N)) :=
  inferInstance

end

end RandomSystemsCC.Events
