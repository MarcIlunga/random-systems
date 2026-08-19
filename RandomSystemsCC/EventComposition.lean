/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.EventAware

/-!
# Composition, distinguishers and renaming for event-aware systems (Jost §§3.2.2–3.3.2)

`RandomSystemsCC.EventAware` put Definition 3.2.3 on the estate's carrier and
showed (`IsEventAware.disciplined`, `isEventAware_of_disciplined`) that it is
the same condition as `Disciplined` on the *event trace* — the sequence of
`(ℰ_{X_i}, ℰ_{Y_i})` pairs.  Jost's own convention (p. 35) is to treat the
event history as "an additional component that models event-awareness in an
abstract manner, rather than as inputs and outputs that need to be explicitly
passed between components", and this module works in exactly that
representation.

## What is here

* **Parallel composition** (p. 34).  `ParDisciplined` is the discipline of a
  two-component composite: one *global* environment clause, and a per-component
  own-clause.  `ParDisciplined.merged` is "`[R,S]` has associated event-set
  `𝒩_R ∪ 𝒩_S`".  `ParDisciplined.proj` is the reason Jost demands the event-sets
  be **disjoint**: inside a globally legal interaction each component still sees
  a legal interaction, because everything the *other* component appends is
  foreign to it.  `proj_fails_without_disjoint` shows the requirement is not
  decorative — with overlapping event-sets a globally legal interaction drives a
  component outside its own definedness restriction.

* **Compatible distinguishers**, Definition 3.3.1 (p. 36).  Jost's two bullets
  are the two fields of one `ExtendsWithin 𝒩ᶜ`: the environment extends the last
  output it saw, and triggers none of the resources' events.  `disciplined_run`
  is the point of the definition — a compatible distinguisher never drives an
  event-aware resource outside the restriction that makes it defined — and
  `incompatible_run_not_disciplined` shows an incompatible one does.

* **Event renaming**, §3.3.2 and Proposition 3.3.3 (p. 37), together with the
  explicit **non-theorem** that an event mapping is not a relaxation.

## Scope, stated precisely

Everything about the *payload* half of the alphabet is untouched here, by
Jost's own design: Definition 3.3.2's first bullet is "in terms of input-output
behavior, it behaves equivalently to R", so an event mapping has no payload
content at all, and a protocol converter is event-oblivious by convention
(p. 35), so it has no event content.  `queryMapBase_comm_queryMapEvents` is that
observation on the estate's augmented alphabet, and it is what makes
Proposition 3.3.3's first equation hold "directly from the definition".

The composite resource `[R,S]` is *not* built as a second `DependentDDS`
combinator.  The estate's `RandomSystems.CR18.TypedResource.DependentDDS.parallel`
composes at a `sumBoundary` — one interface set, each interface carrying a sum
code — whereas Jost's `[R,S]` joins *disjoint* interface sets around a *shared*
event component, so the two do not line up and a fresh combinator would have to
be built.  What is proved here is the event-axis content of that combinator,
which is where every hypothesis of §3.2.2 lives; the payload-axis content is the
ordinary parallel composition the estate already has.
-/

namespace RandomSystemsCC.Events

open RandomSystems.CR18.TypedResource

universe c i u

/-! ## Parallel composition -/

/-- A step of a two-component interaction, tagged with the component that
answered it (`true` = left). -/
abbrev TaggedStep (N : Type u) : Type u := Bool × Step N

/-- The sub-interaction one component of a composite sees. -/
def proj {N : Type u} (side : Bool) (trace : List (TaggedStep N)) : List (Step N) :=
  trace.filterMap fun tagged => if tagged.1 = side then some tagged.2 else none

@[simp] theorem proj_nil {N : Type u} (side : Bool) :
    proj side ([] : List (TaggedStep N)) = [] := rfl

@[simp] theorem proj_cons {N : Type u} (side : Bool) (tagged : TaggedStep N)
    (rest : List (TaggedStep N)) :
    proj side (tagged :: rest) =
      if tagged.1 = side then tagged.2 :: proj side rest else proj side rest := by
  by_cases same : tagged.1 = side <;> simp [proj, same]

/-- **Definition 3.2.3 for a parallel composite.**  The environment clause is
*global* — it quantifies over `(𝒩_R ∪ 𝒩_S)ᶜ`, the composite's own event-set —
while the own-clause is charged to whichever component answered. -/
def ParDisciplined {N : Type u} (left right : Set N) :
    EventHistory N → List (TaggedStep N) → Prop
  | _, [] => True
  | start, tagged :: rest =>
      ExtendsWithin (left ∪ right)ᶜ start tagged.2.1 ∧
        ExtendsWithin (cond tagged.1 left right) tagged.2.1 tagged.2.2 ∧
          ParDisciplined left right tagged.2.2 rest

@[simp] theorem parDisciplined_nil {N : Type u} (left right : Set N)
    (start : EventHistory N) :
    ParDisciplined left right start ([] : List (TaggedStep N)) := trivial

@[simp] theorem parDisciplined_cons {N : Type u} {left right : Set N}
    {start : EventHistory N} {tagged : TaggedStep N} {rest : List (TaggedStep N)} :
    ParDisciplined left right start (tagged :: rest) ↔
      ExtendsWithin (left ∪ right)ᶜ start tagged.2.1 ∧
        ExtendsWithin (cond tagged.1 left right) tagged.2.1 tagged.2.2 ∧
          ParDisciplined left right tagged.2.2 rest := Iff.rfl

section Parallel

variable {N : Type u} {left right : Set N}

private theorem cond_subset_union (side : Bool) : cond side left right ⊆ left ∪ right := by
  cases side
  · show right ⊆ left ∪ right
    exact Set.subset_union_right
  · show left ⊆ left ∪ right
    exact Set.subset_union_left

private theorem cond_subset_compl (disj : Disjoint left right) {b side : Bool}
    (different : b ≠ side) : cond b left right ⊆ (cond side left right)ᶜ := by
  cases b <;> cases side
  · exact absurd rfl different
  · show right ⊆ leftᶜ
    exact fun _ mem => Set.disjoint_right.mp disj mem
  · show left ⊆ rightᶜ
    exact fun _ mem => Set.disjoint_left.mp disj mem
  · exact absurd rfl different

private theorem union_compl_subset_cond_compl (side : Bool) :
    (left ∪ right)ᶜ ⊆ (cond side left right)ᶜ :=
  Set.compl_subset_compl.mpr (cond_subset_union side)

/-- **The composite carries the union of the event-sets** (Jost p. 34: "the
resulting resource `[R,S]` has the associated event-set `𝒩_R ∪ 𝒩_S`").
Forgetting which component answered turns a parallel-disciplined interaction
into an ordinary `𝒩_R ∪ 𝒩_S`-disciplined one. -/
theorem ParDisciplined.merged {start : EventHistory N} :
    ∀ {trace : List (TaggedStep N)}, ParDisciplined left right start trace →
      Disciplined (left ∪ right) start (trace.map Prod.snd) := by
  intro trace
  induction trace generalizing start with
  | nil => exact fun _ => trivial
  | cons tagged rest ih =>
      rintro ⟨env, own, restPar⟩
      exact ⟨env, own.mono (cond_subset_union tagged.1), ih restPar⟩

/-- **Why the event-sets must be disjoint** (Jost p. 34: "Besides the party's
interface sets having to be disjoint, however, also the associated event-sets
have to be disjoint").

Inside an interaction that is legal for the composite, each component still
sees an interaction that is legal *for it*.  The environment's appends are
foreign to both components by the global clause; the *other* component's
appends are foreign to this one exactly because the event-sets are disjoint.
Without that, the other component's own events would look, to this one, like an
environment that triggered its events — which its definedness restriction
forbids.

The statement is generalized over an earlier history `seen` because the
induction has to walk past the other component's steps, during which the global
history advances while this component's does not. -/
theorem ParDisciplined.proj_from (disj : Disjoint left right) (side : Bool) :
    ∀ {trace : List (TaggedStep N)} {seen start : EventHistory N},
      ExtendsWithin (cond side left right)ᶜ seen start →
      ParDisciplined left right start trace →
      Disciplined (cond side left right) seen (proj side trace) := by
  intro trace
  induction trace with
  | nil => exact fun _ _ => trivial
  | cons tagged rest ih =>
      rintro seen start reach ⟨env, own, restPar⟩
      by_cases same : tagged.1 = side
      · rw [proj_cons, if_pos same]
        refine ⟨reach.trans_same (env.mono (union_compl_subset_cond_compl _)), ?_, ?_⟩
        · rw [← same]; exact own
        · exact ih (ExtendsWithin.refl _ _) restPar
      · rw [proj_cons, if_neg same]
        refine ih ?_ restPar
        exact reach.trans_same
          ((env.mono (union_compl_subset_cond_compl _)).trans_same
            (own.mono (cond_subset_compl disj same)))

/-- `ParDisciplined.proj_from` at the start of an interaction: both components
of a legal composite interaction see a legal interaction of their own. -/
theorem ParDisciplined.proj (disj : Disjoint left right) (side : Bool)
    {trace : List (TaggedStep N)}
    (par : ParDisciplined left right EventHistory.nil trace) :
    Disciplined (cond side left right) EventHistory.nil (proj side trace) :=
  ParDisciplined.proj_from disj side (ExtendsWithin.refl _ _) par

end Parallel

/-- The singleton history over `Unit`, for the separating examples below. -/
def unitOccurred : EventHistory Unit := ⟨[()], List.nodup_singleton _⟩

/-- **The disjointness requirement is not decorative.**  With overlapping
event-sets there is an interaction that is legal for the composite and whose
left projection is *illegal* for the left component: the right component
triggered a name the left one owns, which to the left component is
indistinguishable from an environment that triggered its own event — precisely
what Definition 3.2.3's second clause rules out.

Both components own the single available name here, so the two event-sets are
maximally non-disjoint; the environment appends nothing at all. -/
theorem proj_fails_without_disjoint :
    ∃ (left right : Set Unit) (trace : List (TaggedStep Unit)),
      ¬ Disjoint left right ∧
        ParDisciplined left right EventHistory.nil trace ∧
        ¬ Disciplined (cond true left right) EventHistory.nil (proj true trace) := by
  refine ⟨Set.univ, Set.univ,
    [(false, (EventHistory.nil, unitOccurred)), (true, (unitOccurred, unitOccurred))],
    ?_, ?_, ?_⟩
  · intro disj
    exact Set.disjoint_left.mp disj (Set.mem_univ ()) (Set.mem_univ ())
  · refine ⟨ExtendsWithin.refl _ _, ⟨EventHistory.nil_le _, fun _ _ _ => trivial⟩, ?_⟩
    exact ⟨ExtendsWithin.refl _ _, ExtendsWithin.refl _ _, trivial⟩
  · rintro ⟨env, -, -⟩
    exact env.mem_of_new () (by simp [unitOccurred]) (by simp) (Set.mem_univ ())

/-! ## Compatible distinguishers (Definition 3.3.1) -/

/-- The event-axis behaviour of a distinguisher: with each input it announces
the current global event history, as a function of what it has seen. -/
abbrev EventStrategy (N : Type u) : Type u := List (Step N) → EventHistory N

/-- The event-axis behaviour of a resource: given the interaction so far and
the history the distinguisher supplied, the history it hands back. -/
abbrev EventResponder (N : Type u) : Type u :=
  List (Step N) → EventHistory N → EventHistory N

/-- **Jost Definition 3.3.1.**  A distinguisher for resources whose event-sets
together are `events` is *compatible* if

* "with each input, it provides an event list which is an extension of the one
  last output it is interacting with" — the `le` field, and
* "it neither triggers events that are associated with either `R` or `S`" — the
  `mem_of_new` field, at the complement of `events`.

Jost's two bullets are the two halves of a single `ExtendsWithin eventsᶜ`, and
that is exactly the environment clause of Definition 3.2.3.  Compatibility is
therefore not an extra axiom: it is the obligation the resource's definedness
restriction places on whoever is driving it. -/
def IsCompatible {N : Type u} (events : Set N) (strategy : EventStrategy N) : Prop :=
  ∀ trace, ExtendsWithin eventsᶜ (Step.final EventHistory.nil trace) (strategy trace)

/-- The resource-side obligation: only ever append, and only own names. -/
def IsResponder {N : Type u} (events : Set N) (responder : EventResponder N) : Prop :=
  ∀ trace start, ExtendsWithin events start (responder trace start)

/-- The interaction between a distinguisher and a resource, on the event axis,
for `steps` queries. -/
def run {N : Type u} (strategy : EventStrategy N) (responder : EventResponder N) :
    ℕ → List (Step N)
  | 0 => []
  | steps + 1 =>
      let earlier := run strategy responder steps
      earlier ++ [(strategy earlier, responder earlier (strategy earlier))]

@[simp] theorem run_zero {N : Type u} (strategy : EventStrategy N)
    (responder : EventResponder N) : run strategy responder 0 = [] := rfl

/-- **The point of Definition 3.3.1.**  A compatible distinguisher never drives
an event-aware resource outside the restriction that makes it defined: the
interaction it generates is disciplined, step for step.

This is why "the distinguishing advantage is then accordingly only defined for
compatible distinguishers, and the ε-relaxation only quantifies over compatible
distinguishers" (p. 36) — for an incompatible one there is nothing to measure,
because the resource is not defined on what it produced. -/
theorem disciplined_run {N : Type u} {events : Set N} {strategy : EventStrategy N}
    {responder : EventResponder N} (compatible : IsCompatible events strategy)
    (responds : IsResponder events responder) (steps : ℕ) :
    Disciplined events EventHistory.nil (run strategy responder steps) := by
  induction steps with
  | zero => trivial
  | succ steps ih =>
      exact ih.snoc (compatible _) (responds _ _)

/-- The restriction to compatible distinguishers is non-vacuous: the strategy
that simply hands back the last output it saw is compatible with every
event-set.  Together with `incompatible_run_not_disciplined` this shows the
restriction is proper in both directions — it rules something out, and it does
not rule everything out. -/
theorem isCompatible_echo {N : Type u} (events : Set N) :
    IsCompatible events (fun trace => Step.final EventHistory.nil trace) :=
  fun _ => ExtendsWithin.refl _ _

/-- Definition 3.3.1's second bullet, isolated: a compatible distinguisher
never triggers an event associated with either resource. -/
theorem not_triggers_of_compatible {N : Type u} {events : Set N}
    {strategy : EventStrategy N} (compatible : IsCompatible events strategy)
    (trace : List (Step N)) {n : N} (own : n ∈ events)
    (announced : n ∈ (strategy trace).names) :
    n ∈ (Step.final EventHistory.nil trace).names :=
  (compatible trace).mem_of_notMem_set announced (by simpa using own)

/-- **An incompatible distinguisher does break the resource.**  The
distinguisher below announces the empty history on every input, so after the
resource has triggered its event it is no longer supplying an extension of the
last output — and the interaction it generates is not disciplined, i.e. the
resource is not defined on it.  Quantifying the advantage over all
distinguishers would therefore be quantifying over undefined behaviour. -/
theorem incompatible_run_not_disciplined :
    ∃ (strategy : EventStrategy Unit) (responder : EventResponder Unit),
      IsResponder Set.univ responder ∧ ¬ IsCompatible Set.univ strategy ∧
        ¬ Disciplined (Set.univ : Set Unit) EventHistory.nil (run strategy responder 2) := by
  refine ⟨fun _ => EventHistory.nil, fun _ start => start.cons (),
    fun _ start => ⟨EventHistory.le_cons start (), fun _ _ _ => trivial⟩, ?_, ?_⟩
  · intro compatible
    have step := (compatible [(EventHistory.nil, unitOccurred)]).le
    have : (unitOccurred : EventHistory Unit).names <+: [] := EventHistory.le_iff.mp step
    simp [unitOccurred] at this
  · rintro ⟨-, -, env, -⟩
    have : ((EventHistory.nil : EventHistory Unit).cons ()).names <+: [] :=
      EventHistory.le_iff.mp env.le
    simp [EventHistory.cons] at this

/-! ## Event renaming (§3.3.2) -/

section Renaming

variable {N : Type u} [DecidableEq N]

/-- Re-record a list of names through `f`, first occurrence wins.  Written with
`EventHistory.cons`, so duplicates are "dropped if necessary" (Definition 3.3.2)
by the same idempotent append that makes occurrence monotone. -/
def consAll (f : N → N) : EventHistory N → List N → EventHistory N
  | accumulated, [] => accumulated
  | accumulated, name :: rest => consAll f (accumulated.cons (f name)) rest

/-- **Jost Definition 3.3.2** on a history: `τ` applied to the global event
history, leaving names outside its domain unchanged (that is carried by
`IsRenaming.id_outside`) and dropping the duplicates it creates. -/
def renameHist (f : N → N) (history : EventHistory N) : EventHistory N :=
  consAll f EventHistory.nil history.names

theorem le_consAll (f : N → N) (accumulated : EventHistory N) (names : List N) :
    accumulated ≤ consAll f accumulated names := by
  induction names generalizing accumulated with
  | nil => exact le_rfl
  | cons name rest ih =>
      exact (EventHistory.le_cons accumulated (f name)).trans (ih _)

theorem consAll_append (f : N → N) (accumulated : EventHistory N) (front back : List N) :
    consAll f accumulated (front ++ back) = consAll f (consAll f accumulated front) back := by
  induction front generalizing accumulated with
  | nil => rfl
  | cons name rest ih => simpa [consAll] using ih (accumulated.cons (f name))

theorem mem_consAll (f : N → N) {accumulated : EventHistory N} {names : List N} {m : N} :
    m ∈ (consAll f accumulated names).names ↔
      m ∈ accumulated.names ∨ ∃ n ∈ names, f n = m := by
  induction names generalizing accumulated with
  | nil => simp [consAll]
  | cons name rest ih =>
      rw [consAll, ih]
      simp only [EventHistory.mem_cons_names, List.mem_cons]
      constructor
      · rintro ((mem | rfl) | ⟨n, memRest, image⟩)
        · exact Or.inl mem
        · exact Or.inr ⟨name, Or.inl rfl, rfl⟩
        · exact Or.inr ⟨n, Or.inr memRest, image⟩
      · rintro (mem | ⟨n, (rfl | memRest), image⟩)
        · exact Or.inl (Or.inl mem)
        · exact Or.inl (Or.inr image.symm)
        · exact Or.inr ⟨n, memRest, image⟩

@[simp] theorem mem_renameHist (f : N → N) {history : EventHistory N} {m : N} :
    m ∈ (renameHist f history).names ↔ ∃ n ∈ history.names, f n = m := by
  simp [renameHist, mem_consAll]

/-- Renaming preserves the extension order — the renamed history is again a
monotone record, so `τ(R)` is again an event-aware system. -/
theorem renameHist_mono (f : N → N) {E F : EventHistory N} (h : E ≤ F) :
    renameHist f E ≤ renameHist f F := by
  obtain ⟨tail, split⟩ := EventHistory.le_iff.mp h
  have : renameHist f F = consAll f (renameHist f E) tail := by
    rw [renameHist, ← split, consAll_append, renameHist]
  rw [this]
  exact le_consAll _ _ _

theorem ExtendsWithin.rename {S : Set N} {E F : EventHistory N} (f : N → N)
    (h : ExtendsWithin S E F) :
    ExtendsWithin (f '' S) (renameHist f E) (renameHist f F) := by
  refine ⟨renameHist_mono f h.le, ?_⟩
  intro m mem notMem
  obtain ⟨n, memF, image⟩ := (mem_renameHist f).mp mem
  have notMemE : n ∉ E.names := by
    intro memE
    exact notMem ((mem_renameHist f).mpr ⟨n, memE, image⟩)
  exact ⟨n, h.mem_of_new n memF notMemE, image⟩

/-- **Jost's renaming hypothesis**, made explicit.  `τ : 𝒩_R → 𝒩` is partial —
outside `𝒩_R` it does nothing — and Proposition 3.3.3 is stated "for every
protocol `π` and resource `S` that do not depend on events renamed by `τ`",
which is `fresh`: no name outside `𝒩_R` is a `τ`-image, so no other module's
event is disturbed and no `τ`-image collides with one.  `injOn` is what makes
Definition 3.3.2's third bullet — "upon every input, it undoes `τ`" — possible
at all. -/
structure IsRenaming (f : N → N) (events : Set N) : Prop where
  /-- Names outside the renaming's domain are left unchanged. -/
  id_outside : ∀ n ∉ events, f n = n
  /-- The renaming's images are fresh: they collide with nothing outside its
  domain. -/
  fresh : ∀ n ∉ events, n ∉ f '' events
  /-- The renaming is injective where it acts. -/
  injOn : ∀ a ∈ events, ∀ b ∈ events, f a = f b → a = b

namespace IsRenaming

variable {f : N → N} {events : Set N}

omit [DecidableEq N] in
theorem image_compl_subset (mapping : IsRenaming f events) :
    f '' eventsᶜ ⊆ (f '' events)ᶜ := by
  rintro m ⟨n, notMem, rfl⟩
  rw [mapping.id_outside n notMem]
  exact mapping.fresh n notMem

omit [DecidableEq N] in
theorem image_eq_self {other : Set N} (mapping : IsRenaming f events)
    (disj : Disjoint events other) : f '' other = other := by
  ext m
  constructor
  · rintro ⟨n, mem, rfl⟩
    rwa [mapping.id_outside n (Set.disjoint_right.mp disj mem)]
  · intro mem
    exact ⟨m, mem, mapping.id_outside m (Set.disjoint_right.mp disj mem)⟩

/-- **Definition 3.3.2's third bullet is available**: the outside history
determines the inside one, name by name.  Jost implements the undo with a
recalled list of modifications; here it is `injOn` (inside the domain) together
with `fresh` and `id_outside` (outside it) that make the recall unnecessary. -/
theorem occurred_renameHist (mapping : IsRenaming f events)
    {history : EventHistory N} (n : N) :
    f n ∈ (renameHist f history).names ↔ n ∈ history.names := by
  rw [mem_renameHist]
  constructor
  · rintro ⟨m, mem, image⟩
    have same : m = n := by
      by_cases nOwn : n ∈ events
      · by_cases mOwn : m ∈ events
        · exact mapping.injOn m mOwn n nOwn image
        · rw [mapping.id_outside m mOwn] at image
          exact absurd ⟨n, nOwn, image.symm⟩ (mapping.fresh m mOwn)
      · rw [mapping.id_outside n nOwn] at image
        by_cases mOwn : m ∈ events
        · exact absurd ⟨m, mOwn, image⟩ (mapping.fresh n nOwn)
        · rwa [mapping.id_outside m mOwn] at image
    exact same ▸ mem
  · intro mem
    exact ⟨n, mem, rfl⟩

end IsRenaming

/-- Renaming a step of an interaction (Definition 3.3.2: `τ` on the output,
undone on the input, so on the event axis both coordinates move together). -/
def renameStep (f : N → N) (step : Step N) : Step N :=
  (renameHist f step.1, renameHist f step.2)

/-- Renaming a step of a composite interaction leaves the tag alone: the event
mapping does not change *who* answered. -/
def renameTagged (f : N → N) (tagged : TaggedStep N) : TaggedStep N :=
  (tagged.1, renameStep f tagged.2)

/-- **`τ` maps disciplined interactions to disciplined interactions**, with
event-set `img(τ) = τ(𝒩_R)`.  `IsRenaming.fresh` is exactly the hypothesis that
makes the environment clause survive: what the environment was allowed to
append before is still foreign after the mapping. -/
theorem Disciplined.rename {f : N → N} {events : Set N} (mapping : IsRenaming f events)
    {start : EventHistory N} :
    ∀ {trace : List (Step N)}, Disciplined events start trace →
      Disciplined (f '' events) (renameHist f start) (trace.map (renameStep f)) := by
  intro trace
  induction trace generalizing start with
  | nil => exact fun _ => trivial
  | cons step rest ih =>
      rintro ⟨env, own, restDisc⟩
      exact ⟨(env.rename f).mono mapping.image_compl_subset, own.rename f, ih restDisc⟩

/-- **Proposition 3.3.3, second equation: `[τ(R), S] = τ([R, S])`.**

Read componentwise on the event axis, the equation says that renaming the
composite's interaction and then restricting to a component is the same as
restricting first and then renaming — which is what licenses writing `τ(R)` in
place of `R` inside a parallel composition.  It holds unconditionally, because
`renameTagged` does not touch the tag. -/
theorem proj_renameTagged (f : N → N) (side : Bool) (trace : List (TaggedStep N)) :
    proj side (trace.map (renameTagged f)) = (proj side trace).map (renameStep f) := by
  induction trace with
  | nil => rfl
  | cons tagged rest ih =>
      by_cases same : tagged.1 = side <;>
        simp [proj_cons, renameTagged, same, ih]

/-- **Proposition 3.3.3, second equation, with the side conditions.**  If `τ`
renames only the left component's events and `S`'s event-set is disjoint from
`τ`'s domain — Jost's "`S` that does not depend on events renamed by `τ`" —
then the renamed composite is again parallel-disciplined, at event-sets
`img(τ)` and `𝒩_S`.  Together with `proj_renameTagged`, that is the equation. -/
theorem ParDisciplined.rename {f : N → N} {left right : Set N}
    (mapping : IsRenaming f left) (disj : Disjoint left right)
    {start : EventHistory N} :
    ∀ {trace : List (TaggedStep N)}, ParDisciplined left right start trace →
      ParDisciplined (f '' left) right (renameHist f start)
        (trace.map (renameTagged f)) := by
  have rightFixed : f '' right = right := mapping.image_eq_self disj
  have envBudget : f '' (left ∪ right)ᶜ ⊆ (f '' left ∪ right)ᶜ := by
    rintro m ⟨n, notMem, rfl⟩
    have notLeft : n ∉ left := fun contra => notMem (Or.inl contra)
    have notRight : n ∉ right := fun contra => notMem (Or.inr contra)
    rw [mapping.id_outside n notLeft]
    exact fun contra => contra.elim (mapping.fresh n notLeft) notRight
  intro trace
  induction trace generalizing start with
  | nil => exact fun _ => trivial
  | cons tagged rest ih =>
      rintro ⟨env, own, restPar⟩
      refine ⟨(env.rename f).mono envBudget, ?_, ih restPar⟩
      have : f '' (cond tagged.1 left right) = cond tagged.1 (f '' left) right := by
        cases tagged.1
        · simpa using rightFixed
        · simp
      exact this ▸ own.rename f

/-! ### An event mapping is not a relaxation -/

/-- The image of a specification under an event mapping.  Written on event
traces, which is all an event mapping sees (Definition 3.3.2: "in terms of
input-output behavior, it behaves equivalently to R"). -/
def renameSpec (f : N → N) (spec : Set (List (Step N))) : Set (List (Step N)) :=
  (fun trace => trace.map (renameStep f)) '' spec

end Renaming

/-! ### Proposition 3.3.3, first equation: `π τ(R) = τ(π R)` -/

section ObliviousConverter

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

/-- How an **event-oblivious** converter rewrites a query: only the payload.
This is Jost's standing convention (p. 35) — "converters implementing protocols
do not depend on the event history, since an event formalizes something that
*might* be observable, rather than something that is guaranteed to be observable
by the honest parties". -/
def queryMapBase (rewrite : (code : U.Code) → U.input code → U.input code)
    (query : Query (withEvents U N) σ) : Query (withEvents U N) σ :=
  ⟨query.1, (rewrite (σ query.1) query.2.1, query.2.2)⟩

/-- How an **event mapping** rewrites a query: only the event history.  This is
Definition 3.3.2's first bullet — `τ(R)` "behaves equivalently to `R`" in terms
of input-output behaviour, so it has no payload content whatsoever. -/
def queryMapEvents (relabel : EventHistory N → EventHistory N)
    (query : Query (withEvents U N) σ) : Query (withEvents U N) σ :=
  ⟨query.1, (query.2.1, relabel query.2.2)⟩

@[simp] theorem queryHist_queryMapBase
    (rewrite : (code : U.Code) → U.input code → U.input code)
    (query : Query (withEvents U N) σ) :
    queryHist (queryMapBase (N := N) rewrite query) = queryHist query := rfl

@[simp] theorem queryHist_queryMapEvents (relabel : EventHistory N → EventHistory N)
    (query : Query (withEvents U N) σ) :
    queryHist (queryMapEvents (U := U) relabel query) = relabel (queryHist query) := rfl

/-- **Proposition 3.3.3, first equation: `π τ(R) = τ(π R)`.**

Jost's proof is one sentence — "This follows directly from the definition of
`τ(R)`" — and this is that sentence.  On the augmented alphabet `𝒳 × 2^ℰ` an
event-oblivious protocol converter moves only the first factor and an event
mapping moves only the second, so the two commute *definitionally*: there is no
interference to rule out, and none of the hypotheses of the proposition (that
`π` does not depend on events renamed by `τ`) are needed for this half beyond
obliviousness itself. -/
theorem queryMapBase_comm_queryMapEvents
    (rewrite : (code : U.Code) → U.input code → U.input code)
    (relabel : EventHistory N → EventHistory N) :
    (queryMapBase (N := N) (σ := σ) rewrite) ∘ (queryMapEvents relabel)
      = (queryMapEvents relabel) ∘ (queryMapBase rewrite) := rfl

/-- The same commutation along a whole interaction history. -/
theorem map_queryMapBase_comm_queryMapEvents
    (rewrite : (code : U.Code) → U.input code → U.input code)
    (relabel : EventHistory N → EventHistory N)
    (history : List (Query (withEvents U N) σ)) :
    (history.map (queryMapEvents relabel)).map (queryMapBase rewrite)
      = (history.map (queryMapBase rewrite)).map (queryMapEvents relabel) := by
  simp only [List.map_map]
  rfl

end ObliviousConverter

/-- **The explicit non-theorem** (Jost p. 37: "an event mapping is not a
relaxation (a mapped specification is not a superset of the original one)").

A relaxation `φ` is inflationary by Definition 2.2.6 — `R ∈ φ(R)` for every
resource, which is what makes `𝓡 ⊆ 𝓡^φ` and the whole "ignore the relaxation
and reapply it later" calculus of Proposition 2.2.7 work.  An event mapping
fails that at the first non-identity name: renaming the only event of a
one-step specification produces a specification the original is not in.  So
none of Proposition 2.2.7 is available for event mappings, and Jost's
Corollary 3.3.4 has to be proved separately from Proposition 3.3.3 rather than
inherited. -/
theorem renameSpec_not_inflationary :
    ∃ (f : Bool → Bool) (trace : List (Step Bool)),
      trace ∉ renameSpec f {trace} := by
  refine ⟨fun _ => false, [(EventHistory.nil, ⟨[true], List.nodup_singleton _⟩)], ?_⟩
  rintro ⟨t, memSpec, image⟩
  rw [Set.mem_singleton_iff] at memSpec
  subst memSpec
  have := congrArg (fun l => (l.map Prod.snd).map EventHistory.names) image
  simp [renameStep, renameHist, consAll, EventHistory.cons] at this

end RandomSystemsCC.Events
