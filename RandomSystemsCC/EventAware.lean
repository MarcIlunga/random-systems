/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.EventHistory
import RandomSystems.TypedAction

/-!
# Event-aware systems (Jost, Ch. 3 §3.2.2)

`RandomSystemsCC.EventHistory` settled the *object* half of Jost's Chapter 3:
the global event history, the happened-before relation, and the identification
of his composite events with GegMau26's event algebra on the `LowerSet`s of the
dual extension order.  This module settles the *system* half — Definition 3.2.3
— on the estate's own resource carrier.

## Definition 3.2.3 on `DependentDDS`

Jost augments the alphabet, `𝒳' := 𝒳 × 2^ℰ`, and then constrains the augmented
system by two clauses that pull in opposite directions:

* **the resource may append only its own events** — `ℰ_{X_i}` is a prefix of
  `ℰ_{Y_i}` and every additional name is from `𝒩_R`;
* **the environment may append only other people's** — the resource is *only
  defined* when `ℰ_{Y_{i-1}}` is a prefix of `ℰ_{X_i}` and every additional name
  is **not** from `𝒩_R`.

`withEvents` is the augmented signature universe and `IsEventAware` is the pair
of clauses, verbatim, as a predicate on `RandomSystems.CR18.TypedResource.DependentDDS`
over it.  This is the route Jost himself points at (p. 35): "event-aware systems
are a special case of the regular ones — with certain additional restrictions on
when the operators are defined".  Nothing about the carrier changes; the
`withEvents` universe is an ordinary `SignatureUniverse`, so every theorem the
estate proves about `DependentDDS`, `DependentPDS`, `Resource` and the converter
action applies to event-aware systems unchanged.  `act_comm_withEvents` below
spends that observation on the one place where Jost explicitly claims it —
composition order invariance.

Both clauses are instances of a single relation, `ExtendsWithin S E F`: `F`
extends `E` and every name it adds is from `S`.  The resource's clause is
`ExtendsWithin 𝒩_R`, the environment's is `ExtendsWithin 𝒩_Rᶜ`, and Jost's
asymmetry is exactly the complement.

## The event trace, and why it is the working representation

Jost's *convention* (p. 35) is that the event history is **not** passed as
input and output: "we consider the global event history is an additional
component that models event-awareness in an abstract manner, rather than as
inputs and outputs that need to be explicitly passed between components".
`evTrace` extracts that abstract component from a carrier interaction — the
list of `(ℰ_{X_i}, ℰ_{Y_i})` pairs — and `Disciplined` is Definition 3.2.3
transcribed onto it.  `IsEventAware.disciplined` and `isEventAware_of_disciplined`
show the two are the same condition, so the composition results of
`RandomSystemsCC.EventComposition`, which are proved on traces, are results
about carrier resources.
-/

namespace RandomSystemsCC.Events

open RandomSystems.CR18.TypedResource

universe c i u

/-! ## Histories: the facts Definition 3.2.3 needs -/

namespace EventHistory

variable {N : Type u}

/-- The empty history, `ℰ_{Y_0}`: nothing has occurred yet. -/
def nil : EventHistory N := ⟨[], List.nodup_nil⟩

@[simp] theorem nil_names : (nil : EventHistory N).names = [] := rfl

@[simp] theorem not_occurred_nil (n : N) : ¬ (nil : EventHistory N).Occurred n := by
  simp [Occurred]

/-- The empty history precedes every history. -/
theorem nil_le (E : EventHistory N) : (nil : EventHistory N) ≤ E := by
  simp [le_iff]

theorem names_subset_of_le {E F : EventHistory N} (h : E ≤ F) :
    ∀ n ∈ E.names, n ∈ F.names := fun _ mem => (le_iff.mp h).subset mem

theorem le_cons [DecidableEq N] (E : EventHistory N) (n : N) : E ≤ E.cons n := by
  unfold cons
  split
  · exact le_rfl
  · exact le_iff.mpr ⟨[n], rfl⟩

@[simp] theorem mem_cons_names [DecidableEq N] {E : EventHistory N} {m n : N} :
    m ∈ (E.cons n).names ↔ m ∈ E.names ∨ m = n := by
  unfold cons
  split <;> simp_all

/-- Along an extension a name that has already occurred keeps its position.
This is what makes the happened-before relation monotone. -/
theorem idxOf_eq_of_le [DecidableEq N] {E F : EventHistory N} (h : E ≤ F)
    {n : N} (mem : n ∈ E.names) : F.names.idxOf n = E.names.idxOf n := by
  obtain ⟨tail, split⟩ := le_iff.mp h
  rw [← split]
  exact List.idxOf_append_of_mem mem

/-- A name absent from `E` can only appear *after* everything `E` records. -/
theorem length_le_idxOf_of_le [DecidableEq N] {E F : EventHistory N} (h : E ≤ F)
    {n : N} (notMem : n ∉ E.names) : E.names.length ≤ F.names.idxOf n := by
  obtain ⟨tail, split⟩ := le_iff.mp h
  rw [← split, List.idxOf_append_of_notMem notMem]
  exact Nat.le_add_right _ _

instance decidablePrecedes [DecidableEq N] (E : EventHistory N) (n₁ n₂ : N) :
    Decidable (E.Precedes n₁ n₂) :=
  inferInstanceAs (Decidable (E.Occurred n₁ ∧
    (¬ E.Occurred n₂ ∨ E.names.idxOf n₁ < E.names.idxOf n₂)))

/-- **The happened-before relation is monotone.**  Both of Jost's disjuncts
survive an extension: an already-recorded order cannot be rewritten, and if
`n₂` finally occurs it necessarily occurs after everything already present.

This is what licenses reading `ℰ_{n₁} ≺ ℰ_{n₂}` as a *composite event* rather
than as a transient condition. -/
theorem precedes_mono [DecidableEq N] {E F : EventHistory N} (h : E ≤ F)
    {n₁ n₂ : N} (pre : E.Precedes n₁ n₂) : F.Precedes n₁ n₂ := by
  obtain ⟨occ₁, rest⟩ := pre
  refine ⟨names_subset_of_le h _ occ₁, ?_⟩
  by_cases occ₂F : F.Occurred n₂
  · refine Or.inr ?_
    by_cases occ₂E : E.Occurred n₂
    · rw [idxOf_eq_of_le h occ₁, idxOf_eq_of_le h occ₂E]
      rcases rest with notOcc | order
      · exact absurd occ₂E notOcc
      · exact order
    · rw [idxOf_eq_of_le h occ₁]
      exact lt_of_lt_of_le (List.idxOf_lt_length_of_mem occ₁)
        (length_le_idxOf_of_le h occ₂E)
  · exact Or.inl occ₂F

end EventHistory

/-- `ℰ_{n₁} ≺ ℰ_{n₂}` as a composite event in the sense of §3.2.2 — the
monotone condition "`n₁` happened before `n₂`", carried by `precedes_mono`. -/
def precedesEvent {N : Type u} [DecidableEq N] (n₁ n₂ : N) : CompositeEvent N where
  carrier := {E | (OrderDual.ofDual E).Precedes n₁ n₂}
  lower' := by
    intro E F hFE hE
    exact EventHistory.precedes_mono (E := OrderDual.ofDual E)
      (F := OrderDual.ofDual F) hFE hE

@[simp] theorem mem_precedesEvent {N : Type u} [DecidableEq N] {n₁ n₂ : N}
    {E : (EventHistory N)ᵒᵈ} :
    E ∈ precedesEvent n₁ n₂ ↔ (OrderDual.ofDual E).Precedes n₁ n₂ := Iff.rfl

/-! ## `ExtendsWithin`: both clauses of Definition 3.2.3, once -/

/-- `F` extends `E`, and every name `F` adds is drawn from `S`.

Definition 3.2.3's two clauses are this relation at `S := 𝒩_R` (what the
resource itself may append) and at `S := 𝒩_Rᶜ` (what the environment may
append).  Keeping them one relation is not cosmetic: the parallel-composition
argument of `RandomSystemsCC.EventComposition` is a single chain of
`ExtendsWithin.trans` steps alternating between the two. -/
structure ExtendsWithin {N : Type u} (S : Set N) (E F : EventHistory N) : Prop where
  /-- The extension order (`ℰ_{X_i}` is a prefix of `ℰ_{Y_i}`). -/
  le : E ≤ F
  /-- Every additional name is from `S`. -/
  mem_of_new : ∀ n ∈ F.names, n ∉ E.names → n ∈ S

namespace ExtendsWithin

variable {N : Type u} {S T : Set N} {E F G : EventHistory N}

@[refl] theorem refl (S : Set N) (E : EventHistory N) : ExtendsWithin S E E :=
  ⟨le_rfl, fun _ mem notMem => absurd mem notMem⟩

theorem mono (sub : S ⊆ T) (h : ExtendsWithin S E F) : ExtendsWithin T E F :=
  ⟨h.le, fun n mem notMem => sub (h.mem_of_new n mem notMem)⟩

/-- Chaining two extensions accumulates the two name budgets. -/
theorem trans (h₁ : ExtendsWithin S E F) (h₂ : ExtendsWithin T F G) :
    ExtendsWithin (S ∪ T) E G := by
  refine ⟨h₁.le.trans h₂.le, fun n mem notMem => ?_⟩
  by_cases inF : n ∈ F.names
  · exact Or.inl (h₁.mem_of_new n inF notMem)
  · exact Or.inr (h₂.mem_of_new n mem inF)

theorem trans_same (h₁ : ExtendsWithin S E F) (h₂ : ExtendsWithin S F G) :
    ExtendsWithin S E G := by
  simpa using h₁.trans h₂

/-- The contrapositive used everywhere downstream: a name outside the budget
cannot have been introduced by this step, so it was already there. -/
theorem mem_of_notMem_set (h : ExtendsWithin S E F) {n : N} (mem : n ∈ F.names)
    (notMem : n ∉ S) : n ∈ E.names := by
  by_contra new
  exact notMem (h.mem_of_new n mem new)

end ExtendsWithin

/-! ## The event-augmented signature universe -/

/-- **Jost's augmented alphabet `𝒳' := 𝒳 × 2^ℰ`** as a signature universe:
the codes are unchanged, and every input and output alphabet is paired with
the global event history.

Because this is an ordinary `SignatureUniverse`, an event-aware resource is
an ordinary `DependentDDS`, an event-aware law is an ordinary `DependentPDS`,
and the whole converter/action/metric tower applies verbatim.  Event-awareness
is a *predicate* on those objects (`IsEventAware`), never a new carrier. -/
def withEvents (U : SignatureUniverse.{c, u, u}) (N : Type u) :
    SignatureUniverse.{c, u, u} where
  Code := U.Code
  input code := U.input code × EventHistory N
  output code := U.output code × EventHistory N

@[simp] theorem withEvents_code (U : SignatureUniverse.{c, u, u}) (N : Type u) :
    (withEvents U N).Code = U.Code := rfl

instance instDecidableEqWithEventsCode (U : SignatureUniverse.{c, u, u})
    (N : Type u) [DecidableEq U.Code] : DecidableEq (withEvents U N).Code :=
  inferInstanceAs (DecidableEq U.Code)

/-- **The augmented alphabet is `⊕`-closed whenever the base one is**, so the
event carrier has Abstract Cryptography's parallel composition: `Par` on both
resource carriers is gated on `HasSumCode`, and without this instance Jost's
`[R, S]` and CR1's parallel-composition rule could not even be *stated* for
event-aware resources.

The codes are unchanged, so `sumCode` and its injectivity are inherited
verbatim.  The alphabet law is the only content, and it is exactly why
`HasSumCode` asks for an equivalence rather than a type equality:
`(X ⊕ Y) × 2^ℰ` and `(X × 2^ℰ) ⊕ (Y × 2^ℰ)` are `Equiv.sumProdDistrib`, and
they are *not* the same type — under an equality field this universe would
have had no `∥` at all. -/
instance instHasSumCodeWithEvents {U : SignatureUniverse.{c, u, u}}
    {N : Type u} [HasSumCode U] : HasSumCode (withEvents U N) where
  sumCode := HasSumCode.sumCode (U := U)
  inputEquiv a b :=
    ((HasSumCode.inputEquiv (U := U) a b).prodCongr
        (Equiv.refl (EventHistory N))).trans
      (Equiv.sumProdDistrib (U.input a) (U.input b) (EventHistory N))
  outputEquiv a b :=
    ((HasSumCode.outputEquiv (U := U) a b).prodCongr
        (Equiv.refl (EventHistory N))).trans
      (Equiv.sumProdDistrib (U.output a) (U.output b) (EventHistory N))
  sumCode_inj := HasSumCode.sumCode_inj (U := U)

section Alphabet

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
variable {σ : Boundary U I}

/-- The event history the environment supplies with a query — Jost's `ℰ_{X_i}`. -/
def queryHist (query : Query (withEvents U N) σ) : EventHistory N := query.2.2

/-- The payload half of a query: the plain `𝒳` component. -/
def queryBase (query : Query (withEvents U N) σ) : U.input (σ query.1) := query.2.1

@[simp] theorem queryHist_mk (interface : I) (value : U.input (σ interface))
    (history : EventHistory N) :
    queryHist (U := U) (σ := σ) ⟨interface, (value, history)⟩ = history := rfl

@[simp] theorem queryBase_mk (interface : I) (value : U.input (σ interface))
    (history : EventHistory N) :
    queryBase (U := U) (σ := σ) ⟨interface, (value, history)⟩ = value := rfl

end Alphabet

/-! ## Definition 3.2.3 -/

section EventAware

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
variable {σ : Boundary U I}

open scoped Classical in
/-- The global event history as it stands after the interaction `history` —
Jost's `ℰ_{Y_i}` where `i` is the length of `history`, and `ℰ_{Y_0} = ∅`.

Defined off the domain as `∅` so that it is a total function; every statement
below that uses it carries the domain hypothesis. -/
noncomputable def stateHist (resource : DependentDDS (withEvents U N) σ) :
    List (Query (withEvents U N) σ) → EventHistory N
  | [] => EventHistory.nil
  | query :: rest =>
      if member : query :: rest ∈ resource.domain then
        (resource.output (query :: rest) (by simp) member).2
      else EventHistory.nil

@[simp] theorem stateHist_nil (resource : DependentDDS (withEvents U N) σ) :
    stateHist resource [] = EventHistory.nil := rfl

theorem stateHist_eq (resource : DependentDDS (withEvents U N) σ)
    {history : List (Query (withEvents U N) σ)} (nonempty : history ≠ [])
    (member : history ∈ resource.domain) :
    stateHist resource history = (resource.output history nonempty member).2 := by
  cases history with
  | nil => exact absurd rfl nonempty
  | cons _ _ => simp [stateHist, member]

/-- **Jost Definition 3.2.3.**  An event-aware resource with associated
event-set `𝒩_R`, spelled on the estate's carrier over the augmented alphabet
`withEvents U N`.

`appends` is the first clause: the resource may only ever *add* names, and only
its own.  `defined` is the second: the resource is only defined where the
environment has extended the previous output with names that are *not* its own.
The two clauses are the same relation at complementary budgets, which is
precisely Jost's design — a name has exactly one owner, and ownership decides
who is allowed to trigger it. -/
structure IsEventAware (events : Set N) (resource : DependentDDS (withEvents U N) σ) :
    Prop where
  /-- Clause 1: `ℰ_{X_i} ⊑ ℰ_{Y_i}`, additions from `𝒩_R`. -/
  appends : ∀ {history : List (Query (withEvents U N) σ)}
    {query : Query (withEvents U N) σ}, history ++ [query] ∈ resource.domain →
    ExtendsWithin events (queryHist query) (stateHist resource (history ++ [query]))
  /-- Clause 2: defined only when `ℰ_{Y_{i-1}} ⊑ ℰ_{X_i}`, additions **not**
  from `𝒩_R`. -/
  defined : ∀ {history : List (Query (withEvents U N) σ)}
    {query : Query (withEvents U N) σ}, history ++ [query] ∈ resource.domain →
    ExtendsWithin eventsᶜ (stateHist resource history) (queryHist query)

namespace IsEventAware

variable {events : Set N} {resource : DependentDDS (withEvents U N) σ}

/-- One interaction step never retracts the global history, and everything it
adds is either the environment's or the resource's own. -/
theorem step (aware : IsEventAware events resource)
    {history : List (Query (withEvents U N) σ)} {query : Query (withEvents U N) σ}
    (member : history ++ [query] ∈ resource.domain) :
    ExtendsWithin Set.univ (stateHist resource history)
      (stateHist resource (history ++ [query])) := by
  have chain := (aware.defined member).trans (aware.appends member)
  exact chain.mono (fun _ _ => Set.mem_univ _)

theorem step_le (aware : IsEventAware events resource)
    {history : List (Query (withEvents U N) σ)} {query : Query (withEvents U N) σ}
    (member : history ++ [query] ∈ resource.domain) :
    stateHist resource history ≤ stateHist resource (history ++ [query]) :=
  (aware.step member).le

/-- **The global event history only grows along an interaction.**  Occurrence
is monotone at the level of whole runs, not only at the level of a single
`cons`. -/
theorem mono (aware : IsEventAware events resource)
    {short long : List (Query (withEvents U N) σ)} (prefix' : short <+: long)
    (member : long ∈ resource.domain) :
    stateHist resource short ≤ stateHist resource long := by
  obtain ⟨tail, rfl⟩ := prefix'
  induction tail using List.reverseRecOn with
  | nil => simp
  | append_singleton front query ih =>
      rw [← List.append_assoc] at member ⊢
      by_cases empty : short ++ front = []
      · have shortNil : short = [] := (List.append_eq_nil_iff.mp empty).1
        subst shortNil
        simpa using EventHistory.nil_le _
      · have earlier : short ++ front ∈ resource.domain :=
          resource.prefix_closed ⟨[query], rfl⟩ empty member
        exact (ih earlier).trans (aware.step_le member)

/-- **The environment cannot trigger the resource's events.**  If one of the
resource's own names shows up in a query, the resource had already produced it.
This is the modularity guarantee Jost's ownership discipline buys: `𝒩_R` names
are evidence about `R`, never about the environment. -/
theorem own_name_already_occurred (aware : IsEventAware events resource)
    {history : List (Query (withEvents U N) σ)} {query : Query (withEvents U N) σ}
    (member : history ++ [query] ∈ resource.domain) {n : N} (own : n ∈ events)
    (occurred : n ∈ (queryHist query).names) :
    n ∈ (stateHist resource history).names :=
  (aware.defined member).mem_of_notMem_set occurred (by simpa using own)

/-- **A resource only ever triggers its own events.** -/
theorem new_name_is_own (aware : IsEventAware events resource)
    {history : List (Query (withEvents U N) σ)} {query : Query (withEvents U N) σ}
    (member : history ++ [query] ∈ resource.domain) {n : N}
    (occurred : n ∈ (stateHist resource (history ++ [query])).names)
    (fresh : n ∉ (queryHist query).names) : n ∈ events :=
  (aware.appends member).mem_of_new n occurred fresh

end IsEventAware

end EventAware

/-! ## The event trace

Jost's working convention (p. 35) is that the event history is a global side
component rather than an explicitly routed input/output.  `evTrace` is that
component: the sequence of `(ℰ_{X_i}, ℰ_{Y_i})` pairs an interaction produces,
with the payload forgotten. -/

/-- One step of an interaction, seen only through the event axis: what the
environment supplied, and what came back. -/
abbrev Step (N : Type u) : Type u := EventHistory N × EventHistory N

/-- **Definition 3.2.3 on a trace.**  Starting from the history `start`, each
step must extend it with foreign names only, and the answer must extend the
query with own names only. -/
def Disciplined {N : Type u} (events : Set N) :
    EventHistory N → List (Step N) → Prop
  | _, [] => True
  | start, step :: rest =>
      ExtendsWithin eventsᶜ start step.1 ∧ ExtendsWithin events step.1 step.2 ∧
        Disciplined events step.2 rest

@[simp] theorem disciplined_nil {N : Type u} (events : Set N) (start : EventHistory N) :
    Disciplined events start ([] : List (Step N)) := trivial

@[simp] theorem disciplined_cons {N : Type u} {events : Set N}
    {start : EventHistory N} {step : Step N} {rest : List (Step N)} :
    Disciplined events start (step :: rest) ↔
      ExtendsWithin eventsᶜ start step.1 ∧ ExtendsWithin events step.1 step.2 ∧
        Disciplined events step.2 rest := Iff.rfl

/-- The history reached after a trace. -/
def Step.final {N : Type u} (start : EventHistory N) : List (Step N) → EventHistory N
  | [] => start
  | step :: rest => Step.final step.2 rest

@[simp] theorem Step.final_nil {N : Type u} (start : EventHistory N) :
    Step.final start ([] : List (Step N)) = start := rfl

@[simp] theorem Step.final_cons {N : Type u} (start : EventHistory N) (step : Step N)
    (rest : List (Step N)) :
    Step.final start (step :: rest) = Step.final step.2 rest := rfl

/-- A disciplined trace can be extended by one legal step. -/
theorem Disciplined.snoc {N : Type u} {events : Set N} {start : EventHistory N}
    {trace : List (Step N)} (disciplined : Disciplined events start trace)
    {step : Step N}
    (env : ExtendsWithin eventsᶜ (Step.final start trace) step.1)
    (own : ExtendsWithin events step.1 step.2) :
    Disciplined events start (trace ++ [step]) := by
  induction trace generalizing start with
  | nil => exact ⟨env, own, trivial⟩
  | cons head rest ih =>
      obtain ⟨envHead, ownHead, restDisciplined⟩ := disciplined
      exact ⟨envHead, ownHead, ih restDisciplined env⟩

theorem Disciplined.final_le {N : Type u} {events : Set N} {start : EventHistory N}
    {trace : List (Step N)} (disciplined : Disciplined events start trace) :
    start ≤ Step.final start trace := by
  induction trace generalizing start with
  | nil => simp
  | cons head rest ih =>
      obtain ⟨env, own, restDisciplined⟩ := disciplined
      exact (env.le.trans own.le).trans (ih restDisciplined)

section Trace

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
variable {σ : Boundary U I}

/-- The event trace of an interaction, accumulated from the prefix `seen`. -/
noncomputable def evTraceFrom (resource : DependentDDS (withEvents U N) σ)
    (seen : List (Query (withEvents U N) σ)) :
    List (Query (withEvents U N) σ) → List (Step N)
  | [] => []
  | query :: rest =>
      (queryHist query, stateHist resource (seen ++ [query])) ::
        evTraceFrom resource (seen ++ [query]) rest

/-- The event trace of a complete interaction — Jost's `⟨ℰ_{X_i}, ℰ_{Y_i}⟩`. -/
noncomputable def evTrace (resource : DependentDDS (withEvents U N) σ)
    (history : List (Query (withEvents U N) σ)) : List (Step N) :=
  evTraceFrom resource [] history

/-- **Definition 3.2.3 implies its trace form.**  Every interaction an
event-aware resource admits produces a disciplined event trace, so every
theorem proved about `Disciplined` is a theorem about event-aware resources. -/
theorem IsEventAware.disciplined_from {events : Set N}
    {resource : DependentDDS (withEvents U N) σ} (aware : IsEventAware events resource)
    {seen rest : List (Query (withEvents U N) σ)}
    (member : seen ++ rest ∈ resource.domain) :
    Disciplined events (stateHist resource seen) (evTraceFrom resource seen rest) := by
  induction rest generalizing seen with
  | nil => trivial
  | cons query tail ih =>
      have stepMember : seen ++ [query] ∈ resource.domain := by
        refine resource.prefix_closed ?_ (by simp) (by simpa using member)
        exact ⟨tail, by simp⟩
      refine ⟨aware.defined stepMember, aware.appends stepMember, ?_⟩
      exact ih (by simpa using member)

theorem IsEventAware.disciplined {events : Set N}
    {resource : DependentDDS (withEvents U N) σ} (aware : IsEventAware events resource)
    {history : List (Query (withEvents U N) σ)} (member : history ∈ resource.domain) :
    Disciplined events EventHistory.nil (evTrace resource history) := by
  have := aware.disciplined_from (seen := []) (rest := history) (by simpa using member)
  simpa [evTrace] using this

theorem evTraceFrom_concat (resource : DependentDDS (withEvents U N) σ)
    (seen rest : List (Query (withEvents U N) σ)) (query : Query (withEvents U N) σ) :
    evTraceFrom resource seen (rest ++ [query]) =
      evTraceFrom resource seen rest ++
        [(queryHist query, stateHist resource (seen ++ rest ++ [query]))] := by
  induction rest generalizing seen with
  | nil => simp [evTraceFrom]
  | cons head tail ih => simpa [evTraceFrom] using ih (seen ++ [head])

theorem final_evTraceFrom (resource : DependentDDS (withEvents U N) σ)
    (seen rest : List (Query (withEvents U N) σ)) :
    Step.final (stateHist resource seen) (evTraceFrom resource seen rest)
      = stateHist resource (seen ++ rest) := by
  induction rest generalizing seen with
  | nil => simp [evTraceFrom]
  | cons head tail ih => simpa [evTraceFrom] using ih (seen ++ [head])

/-- The last step of a disciplined trace is itself disciplined, relative to the
history the earlier steps reached. -/
theorem Disciplined.of_concat {events : Set N} {start : EventHistory N}
    {trace : List (Step N)} {step : Step N}
    (disciplined : Disciplined events start (trace ++ [step])) :
    ExtendsWithin eventsᶜ (Step.final start trace) step.1 ∧
      ExtendsWithin events step.1 step.2 := by
  induction trace generalizing start with
  | nil => exact ⟨disciplined.1, disciplined.2.1⟩
  | cons head rest ih => exact ih disciplined.2.2

/-- **The trace form implies Definition 3.2.3.**  Together with
`IsEventAware.disciplined` this pins the two down as the same condition, so the
trace layer is a faithful representation of the carrier notion and not a
weakening of it: a resource whose every admitted interaction has a disciplined
event trace *is* event-aware in the sense of Definition 3.2.3. -/
theorem isEventAware_of_disciplined {events : Set N}
    {resource : DependentDDS (withEvents U N) σ}
    (hyp : ∀ history ∈ resource.domain,
      Disciplined events EventHistory.nil (evTrace resource history)) :
    IsEventAware events resource := by
  have step : ∀ {history : List (Query (withEvents U N) σ)}
      {query : Query (withEvents U N) σ}, history ++ [query] ∈ resource.domain →
      ExtendsWithin eventsᶜ (stateHist resource history) (queryHist query) ∧
        ExtendsWithin events (queryHist query)
          (stateHist resource (history ++ [query])) := by
    intro history query member
    have trace := hyp _ member
    rw [evTrace, evTraceFrom_concat] at trace
    have reached := trace.of_concat
    rw [show (EventHistory.nil : EventHistory N) = stateHist resource [] from rfl,
      final_evTraceFrom] at reached
    exact reached
  exact ⟨fun member => (step member).2, fun member => (step member).1⟩

end Trace

/-! ## Compatibility of event sets, and composition order invariance

Jost, p. 35: parallel composition needs the event-sets disjoint as well as the
interface sets, attaching a converter is only defined when its event-set is
disjoint from the resource's ("the converter is *compatible* with the
resource"), and "composition order invariance, Proposition 2.2.3, still holds.
It is not affected by the additional conditions imposed by event-awareness." -/

/-- Jost's compatibility side condition: two event-sets may be combined only
when they are disjoint, so that every name has exactly one owner. -/
def EventCompatible {N : Type u} (left right : Set N) : Prop := Disjoint left right

theorem eventCompatible_comm {N : Type u} {left right : Set N} :
    EventCompatible left right ↔ EventCompatible right left := disjoint_comm

theorem eventCompatible_union {N : Type u} {events left right : Set N}
    (hl : EventCompatible events left) (hr : EventCompatible events right) :
    EventCompatible events (left ∪ right) :=
  Disjoint.union_right hl hr

/-- **The side condition of composition order invariance is symmetric.**
Attaching `first` and then `second` requires `second` to be compatible with the
resource's *grown* event-set `events ∪ first`; attaching them the other way
round requires the mirror image.  Both follow from the same premise — the three
sets pairwise disjoint — so neither order is defined without the other, which
is exactly Jost's "not affected by the additional conditions". -/
theorem eventCompatible_attach_comm {N : Type u} {events first second : Set N}
    (compatFirst : EventCompatible events first)
    (compatSecond : EventCompatible events second)
    (compatBoth : EventCompatible first second) :
    EventCompatible (events ∪ first) second ∧ EventCompatible (events ∪ second) first :=
  ⟨Disjoint.union_left compatSecond compatBoth,
    Disjoint.union_left compatFirst (disjoint_comm.mp compatBoth)⟩

section OrderInvariance

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
variable [DecidableEq I] [DecidableEq U.Code]

/-- **Jost Proposition 2.2.3 in the event-aware system algebra.**  Converters
at distinct interfaces commute over the augmented alphabet `𝒳 × 2^ℰ` — and the
proof is the estate's existing `Primitive.act_comm`, instantiated, because
`withEvents U N` is an ordinary signature universe.

That the theorem is *literally* the old one, rather than a re-proof, is Jost's
point: event-awareness restricts when the operators are defined
(`eventCompatible_attach_comm`), it does not change what they compute. -/
theorem act_comm_withEvents {first second : I} (different : first ≠ second)
    (primitiveFirst : Primitive I (withEvents U N) first)
    (primitiveSecond : Primitive I (withEvents U N) second)
    (resource : Resource I (withEvents U N)) :
    primitiveFirst.act (primitiveSecond.act resource)
      = primitiveSecond.act (primitiveFirst.act resource) :=
  Primitive.act_comm different primitiveFirst primitiveSecond resource

end OrderInvariance

end RandomSystemsCC.Events
