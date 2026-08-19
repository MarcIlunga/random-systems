/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.EventAware
import RandomSystemsCC.RelaxationFibre

/-!
# The from-until relaxations commute (Jost, Ch. 5 §5.3, open question p. 101)

Jost's Chapter 5 introduces two atomic relaxations on the event carrier:

* `R^{P]} := {S | until_P(R) = until_P(S)}` (Definition 5.3.2), where `until_P(R)`
  behaves like `R` but **halts** the moment the monotone predicate `P(ℰ)` becomes
  true — every later answer, *including the answer to the query that triggered
  the condition*, is `⊥`;
* `R^{[P} := {S | from_P(R) = from_P(S)}` (Definition 5.3.7), where `from_P(R)`
  only accepts queries once `P(ℰ)` is true and answers `⊥` before.

Definition 5.3.11 combines them, `R^{[P₁,P₂]} := {S | until_{P₂}(from_{P₁}(R)) =
until_{P₂}(from_{P₁}(S))}`, and Theorem 5.3.12 identifies that combination with
the union over `n` of all alternating composites, and with the two **three-fold**
composites `((R^{[P₁})^{P₂]})^{[P₁}` and `((R^{P₂]})^{[P₁})^{P₂]}`.  On p. 101 the
thesis records the two-fold case as open: "While the from-projection and the
until-projection commute … it is an interesting open question whether the two
respective relaxations actually commute", and the same page adds that the
combined relaxation "apparently neither corresponds to `(R^{[P₁})^{P₂]}` nor
`(R^{P₂]})^{[P₁}`".

**This module settles it affirmatively, in the sharp form:**
`fromThenUntil_eq_intervalRelax` and `untilThenFrom_eq_intervalRelax` prove

    (R^{[P₁})^{P₂]}  =  R^{[P₁,P₂]}  =  (R^{P₂]})^{[P₁}

so Theorem 5.3.12's union **collapses at `n = 2`** (`intervalRelax_union_collapse`)
and the outer relaxation of its three-fold composites is redundant.
`spec_untilRelax_specFromRelax` and `spec_fromRelax_specUntilRelax` carry the same
statement to Jost's specification level, where the relaxations are unions over
the members; that step is separate because a resource-level fibre identity does
not by itself give a specification-level one.

## Why the answer is not abstract

`RandomSystemsCC.IntervalWise.Blocked` exhibits two **idempotent** self-maps of
`Fin 3` that **commute** — the two properties Jost's projections have (p. 101) —
whose fibre relations nevertheless fail to permute.  So the retraction calculus
alone can never decide this; the content has to come from what event-aware
systems are.

## The proof: positionwise gluing

Both projections are transparent about *which sub-transcripts they forward*.
`from_P` forwards a query only when `P` accepts it, and Figure 5.3 shows a
rejected query returning `⊥` with the rest of the code — every state update
included — skipped, so the underlying system is fed exactly the accepted
sub-transcript.  `until_P` forwards a transcript only while no query has
triggered `P`, and on that region the forwarded transcript is the transcript
itself.  Hence, writing

* `FromWindow P₁ x` for "`P₁` accepted every query of `x`", and
* `UntilWindow P₂ x` for "`P₂` accepted none of them",

both **prefix-closed by construction** (indeed sublist-closed), we get the three
characterizations `fromP_eq_iff`, `untilP_eq_iff`, `untilP_fromP_eq_iff`: the two
atomic relaxations and the combined one are agreement on `FromWindow P₁`, on
`UntilWindow P₂`, and on their conjunction.  The collapse is then the gluing
`glue`: run `R` where `from_{P₁}` looks and `S` where only `until_{P₂}` looks.
The regions overlap exactly in `FromWindow P₁ ∧ UntilWindow P₂`, which is where
the hypothesis puts `R = S`, and outside both regions the glued system is simply
`⊥`, which no projection observes.

Note what the gluing does *not* use: Jost's monotonicity of `P` (Definitions
5.3.1/5.3.6) and the commutation of the two projections (p. 101) are both
unnecessary, because the windows are prefix-closed by construction rather than by
monotonicity.  Monotonicity is nevertheless part of Jost's definitions and is
kept here — `CompositeEvent` *is* the monotone-predicate type, and `holdsAt_mono`
is its content — so the statement proved is his; only the proof is more general.

## `⊥`, and why the projections are `Option`-valued

`⊥` is not a value of any `U.output`, and it cannot be modelled by leaving the
carrier's `domain`: `until_P(R)`'s defined region is prefix-closed but
`from_P(R)`'s is not (a prefix of an accepted transcript need not be accepted),
so `DependentDDS.domain` — prefix-closed by fiat — cannot express it.  A
projected system is therefore an `Answers`, a total map from transcripts to
`Option (FlatAnswer …)` with `none` as Jost's `⊥`, and `answers` is the carrier
resource read as one.  `answers_injective` is the receipt that this loses
nothing, and `getLast?_accepted` is the receipt that flattening the answer type
does not lose the interface tag either: `from_P` answers at the interface of the
query it was asked.

## The obligations Jost's definitions impose on the witness

Definition 3.2.3 makes event-awareness a *property* of a carrier resource, so a
witness for the collapse has to be checked against it and not merely
constructed.  `glue_isEventAware` does that — both clauses — and
`intervalRelax_witness_isEventAware` is the resulting statement: inside the
event-aware subcategory the collapse holds with an event-aware witness.  The
boundary case is where the clauses bite: at the transcript where the glued system
switches from `R` to `S` the *previous* answer came from `R` and the incoming
query must extend it, and that is legitimate precisely because the switch happens
inside the overlap window, where `R` and `S` answer identically.

## Event-awareness is indispensable

`Necessity.historyBlind_collapse_fails` is the converse half.  With
`P₁ = P₂ = ℰ_a` the overlap window contains only the empty transcript, so the
hypothesis of the collapse is **vacuous**; yet `from_{ℰ_a}` forwards everything on
the history in which `a` has occurred, and `until_{ℰ_a}` forwards everything on the
empty history.  A resource that cannot read the global event history sees the same
query payloads in both and is forced to answer both alike, so no history-blind
witness exists.  The affirmative answer above therefore holds *because of* Jost's
Chapter 3 extension, not despite it.
-/

namespace RandomSystemsCC.IntervalWise

open RandomSystems.CR18.TypedResource
open RandomSystemsCC.Events

universe c i u

/-! ## Monotone conditions, read on a query -/

section Conditions

variable {N : Type u}

/-- Jost's monotone predicate `P(ℰ)` (§3.2.2, Definitions 5.3.1/5.3.6) evaluated
at an ordinary history.  `CompositeEvent N` is the type of monotone conditions,
so monotonicity is not a side hypothesis here but part of the argument's type. -/
def holdsAt (P : CompositeEvent N) (history : EventHistory N) : Prop :=
  OrderDual.toDual history ∈ P

/-- Monotonicity, as Definitions 5.3.1 and 5.3.6 require it. -/
theorem holdsAt_mono {P : CompositeEvent N} {early late : EventHistory N} (extends' : early ≤ late)
    (held : holdsAt P early) : holdsAt P late :=
  P.lower (a := OrderDual.toDual early) (b := OrderDual.toDual late) extends' held

end Conditions

section Windows

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

/-- The queries `P` accepts: the environment supplied a history satisfying `P`. -/
def Accepts (P : CompositeEvent N) (query : Query (withEvents U N) σ) : Prop :=
  holdsAt P (queryHist query)

/-- The transcripts every one of whose queries satisfies `φ`.  Closed under
sublists, hence under prefixes — which is the only structural property the
gluing below uses. -/
def Window (φ : Query (withEvents U N) σ → Prop)
    (transcript : List (Query (withEvents U N) σ)) : Prop := ∀ query ∈ transcript, φ query

theorem Window.sublist {φ : Query (withEvents U N) σ → Prop}
    {short long : List (Query (withEvents U N) σ)} (sub : List.Sublist short long)
    (window : Window φ long) : Window φ short := fun _ mem => window _ (sub.subset mem)

theorem Window.prefix {φ : Query (withEvents U N) σ → Prop}
    {short long : List (Query (withEvents U N) σ)} (pre : short <+: long)
    (window : Window φ long) : Window φ short := fun _ mem => window _ (pre.subset mem)

@[simp] theorem window_nil (φ : Query (withEvents U N) σ → Prop) :
    Window φ ([] : List (Query (withEvents U N) σ)) := by simp [Window]

/-- **The sub-transcripts `from_P` forwards** (Definition 5.3.6): `P` accepted
every query. -/
def FromWindow (P : CompositeEvent N) (transcript : List (Query (withEvents U N) σ)) : Prop :=
  Window (Accepts (U := U) (σ := σ) P) transcript

/-- **The transcripts `until_P` forwards** (Definition 5.3.1): `P` accepted no
query, so the halting condition has not been triggered — including by the current
query, whose answer Jost's definition already sends to `⊥`. -/
def UntilWindow (P : CompositeEvent N) (transcript : List (Query (withEvents U N) σ)) : Prop :=
  Window (fun query => ¬ Accepts (U := U) (σ := σ) P query) transcript

/-- The overlap: what the combined projection of Definition 5.3.11 forwards. -/
def IntervalWindow (P₁ P₂ : CompositeEvent N)
    (transcript : List (Query (withEvents U N) σ)) : Prop :=
  FromWindow P₁ transcript ∧ UntilWindow P₂ transcript

theorem intervalWindow_nil (P₁ P₂ : CompositeEvent N) :
    IntervalWindow (U := U) (σ := σ) P₁ P₂ [] := ⟨window_nil _, window_nil _⟩

/-- The two windows meet only on the empty transcript when the two conditions
coincide — the vacuity the necessity counterexample runs on. -/
theorem eq_nil_of_intervalWindow_self {P : CompositeEvent N}
    {transcript : List (Query (withEvents U N) σ)}
    (window : IntervalWindow P P transcript) : transcript = [] := by
  rcases transcript with _ | ⟨head, tail⟩
  · rfl
  · exact absurd (window.1 head (by simp)) (window.2 head (by simp))

end Windows

/-! ## Behaviours with `⊥` -/

section Answers

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

/-- **A behaviour carrying Jost's `⊥`.**  `none` is the special symbol `⊥`.  The
projections of Definitions 5.3.1 and 5.3.6 have to land here rather than back on
`DependentDDS`, because `from_P(R)`'s defined region is not prefix-closed and
`DependentDDS.domain` is. -/
abbrev Answers (U : SignatureUniverse.{c, u, u}) (N : Type u) (σ : Boundary U I) :=
  List (Query (withEvents U N) σ) → Option (FlatAnswer (withEvents U N) σ)

open scoped Classical in
/-- A carrier resource read as a behaviour: `⊥` exactly where it is undefined. -/
noncomputable def answers (resource : DependentDDS (withEvents U N) σ) : Answers U N σ :=
  fun transcript =>
    if member : transcript ∈ resource.domain then
      some ⟨(transcript.getLast (resource.history_ne_nil member)).1,
        resource.answer transcript member⟩
    else none

theorem answers_eq_none_iff {resource : DependentDDS (withEvents U N) σ}
    {transcript : List (Query (withEvents U N) σ)} :
    answers resource transcript = none ↔ transcript ∉ resource.domain := by
  by_cases member : transcript ∈ resource.domain <;> simp [answers, member]

theorem answers_eq_some {resource : DependentDDS (withEvents U N) σ}
    {transcript : List (Query (withEvents U N) σ)} (member : transcript ∈ resource.domain)
    (nonempty : transcript ≠ []) :
    answers resource transcript =
      some ⟨(transcript.getLast nonempty).1, resource.output transcript nonempty member⟩ := by
  simp only [answers, member, dif_pos, DependentDDS.answer]

theorem answers_eq_of_output {left right : DependentDDS (withEvents U N) σ}
    {transcript : List (Query (withEvents U N) σ)} (nonempty : transcript ≠ [])
    (memL : transcript ∈ left.domain) (memR : transcript ∈ right.domain)
    (same : left.output transcript nonempty memL = right.output transcript nonempty memR) :
    answers left transcript = answers right transcript := by
  rw [answers_eq_some memL nonempty, answers_eq_some memR nonempty, same]

theorem mem_domain_of_answers_ne_none {resource : DependentDDS (withEvents U N) σ}
    {transcript : List (Query (withEvents U N) σ)} (ne : answers resource transcript ≠ none) :
    transcript ∈ resource.domain := by
  by_contra notMem
  exact ne (answers_eq_none_iff.2 notMem)

@[simp] theorem answers_nil (resource : DependentDDS (withEvents U N) σ) :
    answers resource [] = none :=
  answers_eq_none_iff.2 resource.empty_not_mem

/-- Extensionality for the carrier: a resource is its domain plus its answers. -/
theorem dependentDDS_ext {left right : DependentDDS (withEvents U N) σ}
    (domains : left.domain = right.domain)
    (outputs : ∀ (transcript : List (Query (withEvents U N) σ)) (nonempty : transcript ≠ [])
      (memL : transcript ∈ left.domain) (memR : transcript ∈ right.domain),
      left.output transcript nonempty memL = right.output transcript nonempty memR) :
    left = right := by
  obtain ⟨domainL, emptyL, prefixL, outputL⟩ := left
  obtain ⟨domainR, emptyR, prefixR, outputR⟩ := right
  subst domains
  congr 1
  funext transcript nonempty member
  exact outputs transcript nonempty member member

/-- **The behaviour determines the resource.**  Reading a carrier resource through
the flat, `⊥`-valued `Answers` type loses nothing, so defining the relaxations on
`answers` below is not a coarsening. -/
theorem answers_injective :
    Function.Injective (answers (I := I) (N := N) (U := U) (σ := σ)) := by
  intro left right same
  refine dependentDDS_ext ?_ ?_
  · ext transcript
    refine not_iff_not.mp ?_
    rw [← answers_eq_none_iff, ← answers_eq_none_iff, congrFun same transcript]
  · intro transcript nonempty memL memR
    have step := congrFun same transcript
    rw [answers_eq_some memL nonempty, answers_eq_some memR nonempty] at step
    simpa using step

/-- The event history a behaviour reports, `∅` where it answers `⊥`. -/
noncomputable def answerHist (behaviour : Answers U N σ)
    (transcript : List (Query (withEvents U N) σ)) : EventHistory N :=
  (behaviour transcript).elim EventHistory.nil fun answer => answer.2.2

theorem stateHist_of_not_mem {resource : DependentDDS (withEvents U N) σ}
    {transcript : List (Query (withEvents U N) σ)} (notMem : transcript ∉ resource.domain) :
    stateHist resource transcript = EventHistory.nil := by
  rcases transcript with _ | ⟨head, tail⟩
  · rfl
  · simp [stateHist, notMem]

/-- `answerHist` on a carrier resource is Jost's `ℰ_{Y_i}` — the module's bridge
between behavioural equality and Definition 3.2.3. -/
theorem answerHist_answers (resource : DependentDDS (withEvents U N) σ)
    (transcript : List (Query (withEvents U N) σ)) :
    answerHist (answers resource) transcript = stateHist resource transcript := by
  by_cases member : transcript ∈ resource.domain
  · have nonempty := resource.history_ne_nil member
    rw [stateHist_eq resource nonempty member, answerHist, answers_eq_some member nonempty]
    rfl
  · simp [answerHist, answers, member, stateHist_of_not_mem member]

theorem stateHist_congr {left right : DependentDDS (withEvents U N) σ}
    {transcript : List (Query (withEvents U N) σ)}
    (same : answers left transcript = answers right transcript) :
    stateHist left transcript = stateHist right transcript := by
  rw [← answerHist_answers, ← answerHist_answers, answerHist, answerHist, same]

/-- Two resources agree on a set of transcripts. -/
def AgreeOn (window : List (Query (withEvents U N) σ) → Prop)
    (left right : DependentDDS (withEvents U N) σ) : Prop :=
  ∀ transcript, window transcript → answers left transcript = answers right transcript

theorem AgreeOn.symm {window : List (Query (withEvents U N) σ) → Prop}
    {left right : DependentDDS (withEvents U N) σ} (agree : AgreeOn window left right) :
    AgreeOn window right left := fun transcript mem => (agree transcript mem).symm

end Answers

/-! ## The two projections -/

section Projections

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

open scoped Classical in
/-- The accepted sub-transcript `from_P` forwards to the underlying system. -/
noncomputable def accepted (P : CompositeEvent N)
    (transcript : List (Query (withEvents U N) σ)) : List (Query (withEvents U N) σ) :=
  transcript.filter fun query => decide (Accepts P query)

theorem accepted_sublist (P : CompositeEvent N)
    (transcript : List (Query (withEvents U N) σ)) :
    List.Sublist (accepted P transcript) transcript := List.filter_sublist

theorem fromWindow_accepted (P : CompositeEvent N)
    (transcript : List (Query (withEvents U N) σ)) :
    FromWindow P (accepted P transcript) := by
  intro query mem
  rw [accepted, List.mem_filter] at mem
  simpa using mem.2

theorem accepted_eq_self {P : CompositeEvent N} {transcript : List (Query (withEvents U N) σ)}
    (window : FromWindow P transcript) : accepted P transcript = transcript := by
  rw [accepted, List.filter_eq_self]
  intro query mem
  simpa using window query mem

/-- `P` accepts the query currently being answered — the condition under which
Definition 5.3.6's projection answers at all. -/
def AcceptsLast (P : CompositeEvent N) (transcript : List (Query (withEvents U N) σ)) : Prop :=
  ∃ query, transcript.getLast? = some query ∧ Accepts P query

theorem acceptsLast_of_window {P : CompositeEvent N}
    {transcript : List (Query (withEvents U N) σ)} (window : FromWindow P transcript)
    (nonempty : transcript ≠ []) : AcceptsLast P transcript :=
  ⟨transcript.getLast nonempty, List.getLast?_eq_some_getLast nonempty,
    window _ (List.getLast_mem nonempty)⟩

open scoped Classical in
/-- **Jost Definition 5.3.1**, `until_P(R)`: the system halts the moment `P(ℰ)`
becomes true, and *every* answer from then on — including the answer to the query
that triggered the condition — is `⊥`.  On the region it does forward, the
forwarded transcript is the transcript itself, so no reindexing occurs. -/
noncomputable def untilP (P : CompositeEvent N) (behaviour : Answers U N σ) : Answers U N σ :=
  fun transcript =>
    if UntilWindow (U := U) (σ := σ) P transcript then behaviour transcript else none

open scoped Classical in
/-- **Jost Definition 5.3.6**, `from_P(R)`: queries are only accepted once `P(ℰ)`
is true and answered `⊥` before, so the underlying system is fed exactly the
accepted sub-transcript — Figure 5.3's `require` skips the rest of the code, state
updates included. -/
noncomputable def fromP (P : CompositeEvent N) (behaviour : Answers U N σ) : Answers U N σ :=
  fun transcript =>
    if AcceptsLast (U := U) (σ := σ) P transcript then behaviour (accepted P transcript) else none

theorem untilP_apply_of_window {P : CompositeEvent N} {behaviour : Answers U N σ}
    {transcript : List (Query (withEvents U N) σ)} (window : UntilWindow P transcript) :
    untilP P behaviour transcript = behaviour transcript := by
  classical simp [untilP, window]

theorem untilP_apply_of_not_window {P : CompositeEvent N} {behaviour : Answers U N σ}
    {transcript : List (Query (withEvents U N) σ)} (window : ¬ UntilWindow P transcript) :
    untilP P behaviour transcript = none := by
  classical simp [untilP, window]

theorem fromP_apply_of_acceptsLast {P : CompositeEvent N} {behaviour : Answers U N σ}
    {transcript : List (Query (withEvents U N) σ)} (last : AcceptsLast P transcript) :
    fromP P behaviour transcript = behaviour (accepted P transcript) := by
  classical simp [fromP, last]

theorem fromP_apply_of_not_acceptsLast {P : CompositeEvent N} {behaviour : Answers U N σ}
    {transcript : List (Query (withEvents U N) σ)} (last : ¬ AcceptsLast P transcript) :
    fromP P behaviour transcript = none := by
  classical simp [fromP, last]

theorem fromP_apply_of_window {P : CompositeEvent N} {behaviour : Answers U N σ}
    {transcript : List (Query (withEvents U N) σ)} (window : FromWindow P transcript)
    (nonempty : transcript ≠ []) : fromP P behaviour transcript = behaviour transcript := by
  rw [fromP_apply_of_acceptsLast (acceptsLast_of_window window nonempty), accepted_eq_self window]

/-- **The flat answer type keeps the interface tag.**  `from_P` reindexes the
transcript, but the query being answered survives the reindexing, so the answer
`from_P(R)` returns is one of `R`'s answers at the interface actually queried. -/
theorem getLast?_accepted {P : CompositeEvent N} {transcript : List (Query (withEvents U N) σ)}
    {query : Query (withEvents U N) σ} (last : transcript.getLast? = some query)
    (accepts : Accepts P query) : (accepted P transcript).getLast? = some query := by
  classical
  have nonempty : transcript ≠ [] := by
    rintro rfl; simp at last
  have same : transcript.getLast nonempty = query := by
    rw [List.getLast?_eq_some_getLast nonempty] at last
    exact Option.some_injective _ last
  have split : transcript.dropLast ++ [query] = transcript := by
    rw [← same]; exact List.dropLast_append_getLast nonempty
  calc (accepted P transcript).getLast?
      = (accepted P (transcript.dropLast ++ [query])).getLast? := by rw [split]
    _ = some query := by
        rw [accepted, List.filter_append]
        simp [accepts]

end Projections

/-! ## The three characterizations -/

section Characterizations

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}
variable {P P₁ P₂ : CompositeEvent N} {R S : DependentDDS (withEvents U N) σ}

/-- **Definition 5.3.2 is agreement on `UntilWindow P`.** -/
theorem untilP_eq_iff :
    untilP P (answers R) = untilP P (answers S) ↔ AgreeOn (UntilWindow P) R S := by
  constructor
  · intro same transcript window
    have step := congrFun same transcript
    rwa [untilP_apply_of_window window, untilP_apply_of_window window] at step
  · intro agree
    funext transcript
    by_cases window : UntilWindow (U := U) (σ := σ) P transcript
    · rw [untilP_apply_of_window window, untilP_apply_of_window window]
      exact agree transcript window
    · rw [untilP_apply_of_not_window window, untilP_apply_of_not_window window]

/-- **Definition 5.3.7 is agreement on `FromWindow P`.**  Surjectivity of the
reindexing onto its window is what makes this an equivalence: every transcript
all of whose queries `P` accepts is forwarded verbatim, namely by itself. -/
theorem fromP_eq_iff :
    fromP P (answers R) = fromP P (answers S) ↔ AgreeOn (FromWindow P) R S := by
  constructor
  · intro same transcript window
    rcases eq_or_ne transcript [] with rfl | nonempty
    · simp
    · have step := congrFun same transcript
      rwa [fromP_apply_of_window window nonempty, fromP_apply_of_window window nonempty] at step
  · intro agree
    funext transcript
    by_cases last : AcceptsLast (U := U) (σ := σ) P transcript
    · rw [fromP_apply_of_acceptsLast last, fromP_apply_of_acceptsLast last]
      exact agree _ (fromWindow_accepted P transcript)
    · rw [fromP_apply_of_not_acceptsLast last, fromP_apply_of_not_acceptsLast last]

/-- **Definition 5.3.11 is agreement on the overlap.**  Kept in the printed
`until ∘ from` orientation. -/
theorem untilP_fromP_eq_iff :
    untilP P₂ (fromP P₁ (answers R)) = untilP P₂ (fromP P₁ (answers S)) ↔
      AgreeOn (IntervalWindow P₁ P₂) R S := by
  constructor
  · intro same transcript window
    rcases eq_or_ne transcript [] with rfl | nonempty
    · simp
    · have step := congrFun same transcript
      rwa [untilP_apply_of_window window.2, untilP_apply_of_window window.2,
        fromP_apply_of_window window.1 nonempty, fromP_apply_of_window window.1 nonempty] at step
  · intro agree
    funext transcript
    by_cases window : UntilWindow (U := U) (σ := σ) P₂ transcript
    · rw [untilP_apply_of_window window, untilP_apply_of_window window]
      by_cases last : AcceptsLast (U := U) (σ := σ) P₁ transcript
      · rw [fromP_apply_of_acceptsLast last, fromP_apply_of_acceptsLast last]
        exact agree _ ⟨fromWindow_accepted P₁ transcript,
          Window.sublist (accepted_sublist P₁ transcript) window⟩
      · rw [fromP_apply_of_not_acceptsLast last, fromP_apply_of_not_acceptsLast last]
    · rw [untilP_apply_of_not_window window, untilP_apply_of_not_window window]

end Characterizations

/-! ## The relaxations -/

section Relaxations

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

/-- **Jost Definition 5.3.2**, `R^{P]}`. -/
noncomputable def untilRelax (P : CompositeEvent N) (R : DependentDDS (withEvents U N) σ) :
    Set (DependentDDS (withEvents U N) σ) := fibre (fun S => untilP P (answers S)) R

/-- **Jost Definition 5.3.7**, `R^{[P}`. -/
noncomputable def fromRelax (P : CompositeEvent N) (R : DependentDDS (withEvents U N) σ) :
    Set (DependentDDS (withEvents U N) σ) := fibre (fun S => fromP P (answers S)) R

/-- **Jost Definition 5.3.11**, `R^{[P₁,P₂]}`, in the printed orientation. -/
noncomputable def intervalRelax (P₁ P₂ : CompositeEvent N)
    (R : DependentDDS (withEvents U N) σ) : Set (DependentDDS (withEvents U N) σ) :=
  fibre (fun S => untilP P₂ (fromP P₁ (answers S))) R

/-- `(R^{[P₁})^{P₂]}`. -/
noncomputable def fromThenUntil (P₁ P₂ : CompositeEvent N)
    (R : DependentDDS (withEvents U N) σ) : Set (DependentDDS (withEvents U N) σ) :=
  fibreComp (fun S => fromP P₁ (answers S)) (fun S => untilP P₂ (answers S)) R

/-- `(R^{P₂]})^{[P₁}`. -/
noncomputable def untilThenFrom (P₁ P₂ : CompositeEvent N)
    (R : DependentDDS (withEvents U N) σ) : Set (DependentDDS (withEvents U N) σ) :=
  fibreComp (fun S => untilP P₂ (answers S)) (fun S => fromP P₁ (answers S)) R

variable {P₁ P₂ : CompositeEvent N} {R S : DependentDDS (withEvents U N) σ}

theorem mem_untilRelax : S ∈ untilRelax P₂ R ↔ AgreeOn (UntilWindow P₂) S R := untilP_eq_iff

theorem mem_fromRelax : S ∈ fromRelax P₁ R ↔ AgreeOn (FromWindow P₁) S R := fromP_eq_iff

theorem mem_intervalRelax :
    S ∈ intervalRelax P₁ P₂ R ↔ AgreeOn (IntervalWindow P₁ P₂) S R := untilP_fromP_eq_iff

end Relaxations

/-! ## The glued witness -/

section Glue

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

open scoped Classical in
/-- **The witness.**  `glue P₁ P₂ R S` runs `R` on the transcripts `from_{P₁}`
forwards and `S` on the remaining transcripts `until_{P₂}` forwards; outside both
windows it is `⊥`, which neither projection observes.  No hypothesis relating `R`
and `S` enters the *definition*: the else-branch is licensed by domain membership
alone. -/
noncomputable def glue (P₁ P₂ : CompositeEvent N) (R S : DependentDDS (withEvents U N) σ) :
    DependentDDS (withEvents U N) σ where
  domain := {transcript | (transcript ∈ R.domain ∧ FromWindow P₁ transcript) ∨
    (transcript ∈ S.domain ∧ UntilWindow P₂ transcript)}
  empty_not_mem := by
    rintro (⟨member, -⟩ | ⟨member, -⟩)
    · exact R.empty_not_mem member
    · exact S.empty_not_mem member
  prefix_closed := by
    rintro short long pre nonempty (⟨member, window⟩ | ⟨member, window⟩)
    · exact Or.inl ⟨R.prefix_closed pre nonempty member, Window.prefix pre window⟩
    · exact Or.inr ⟨S.prefix_closed pre nonempty member, Window.prefix pre window⟩
  output transcript nonempty member :=
    if branch : transcript ∈ R.domain ∧ FromWindow P₁ transcript then
      R.output transcript nonempty branch.1
    else S.output transcript nonempty (member.resolve_left branch).1

variable (P₁ P₂ : CompositeEvent N) (R S : DependentDDS (withEvents U N) σ)

theorem mem_glue_domain {transcript : List (Query (withEvents U N) σ)} :
    transcript ∈ (glue P₁ P₂ R S).domain ↔
      (transcript ∈ R.domain ∧ FromWindow P₁ transcript) ∨
        (transcript ∈ S.domain ∧ UntilWindow P₂ transcript) := Iff.rfl

theorem glue_output_left {transcript : List (Query (withEvents U N) σ)}
    (nonempty : transcript ≠ []) (member : transcript ∈ (glue P₁ P₂ R S).domain)
    (branch : transcript ∈ R.domain ∧ FromWindow P₁ transcript) :
    (glue P₁ P₂ R S).output transcript nonempty member =
      R.output transcript nonempty branch.1 := dif_pos branch

theorem glue_output_right {transcript : List (Query (withEvents U N) σ)}
    (nonempty : transcript ≠ []) (member : transcript ∈ (glue P₁ P₂ R S).domain)
    (branch : ¬ (transcript ∈ R.domain ∧ FromWindow P₁ transcript))
    (memS : transcript ∈ S.domain) :
    (glue P₁ P₂ R S).output transcript nonempty member =
      S.output transcript nonempty memS := dif_neg branch

end Glue

section GlueAgreement

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}
variable {P₁ P₂ : CompositeEvent N} {R S : DependentDDS (withEvents U N) σ}

/-- On the window `from_{P₁}` observes, the glued system is `R`. -/
theorem answers_glue_of_fromWindow (agree : AgreeOn (IntervalWindow P₁ P₂) R S)
    {transcript : List (Query (withEvents U N) σ)} (window : FromWindow P₁ transcript) :
    answers (glue P₁ P₂ R S) transcript = answers R transcript := by
  by_cases memR : transcript ∈ R.domain
  · have memT : transcript ∈ (glue P₁ P₂ R S).domain := Or.inl ⟨memR, window⟩
    exact answers_eq_of_output ((glue P₁ P₂ R S).history_ne_nil memT) memT memR
      (glue_output_left P₁ P₂ R S _ memT ⟨memR, window⟩)
  · have notMemT : transcript ∉ (glue P₁ P₂ R S).domain := by
      rintro (⟨member, -⟩ | ⟨member, windowV⟩)
      · exact memR member
      · refine memR (mem_domain_of_answers_ne_none ?_)
        rw [agree transcript ⟨window, windowV⟩]
        exact fun none' => (answers_eq_none_iff.1 none') member
    rw [answers_eq_none_iff.2 notMemT, answers_eq_none_iff.2 memR]

/-- On the window `until_{P₂}` observes, the glued system is `S`. -/
theorem answers_glue_of_untilWindow (agree : AgreeOn (IntervalWindow P₁ P₂) R S)
    {transcript : List (Query (withEvents U N) σ)} (window : UntilWindow P₂ transcript) :
    answers (glue P₁ P₂ R S) transcript = answers S transcript := by
  by_cases windowW : FromWindow (U := U) (σ := σ) P₁ transcript
  · rw [answers_glue_of_fromWindow agree windowW]
    exact agree transcript ⟨windowW, window⟩
  · have branch : ¬ (transcript ∈ R.domain ∧ FromWindow P₁ transcript) := fun h => windowW h.2
    by_cases memS : transcript ∈ S.domain
    · have memT : transcript ∈ (glue P₁ P₂ R S).domain := Or.inr ⟨memS, window⟩
      exact answers_eq_of_output ((glue P₁ P₂ R S).history_ne_nil memT) memT memS
        (glue_output_right P₁ P₂ R S _ memT branch memS)
    · have notMemT : transcript ∉ (glue P₁ P₂ R S).domain := by
        rintro (⟨-, windowW'⟩ | ⟨member, -⟩)
        · exact windowW windowW'
        · exact memS member
      rw [answers_eq_none_iff.2 notMemT, answers_eq_none_iff.2 memS]

end GlueAgreement

/-! ## Definition 3.2.3 for the witness -/

section EventAware

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}
variable {P₁ P₂ : CompositeEvent N} {R S : DependentDDS (withEvents U N) σ} {events : Set N}

/-- **The glued witness is event-aware** in the sense of Definition 3.2.3, with
the same associated event-set.  Both clauses are checked, and the boundary case is
the point: at the transcript where the glued system switches from `R` to `S` the
previous answer came from `R`, so the incoming query has to extend *`R`'s*
history — legitimate exactly because the switch happens inside the overlap window,
where `R` and `S` answer identically. -/
theorem glue_isEventAware (agree : AgreeOn (IntervalWindow P₁ P₂) R S)
    (awareR : IsEventAware events R) (awareS : IsEventAware events S) :
    IsEventAware events (glue P₁ P₂ R S) := by
  have key : ∀ (history : List (Query (withEvents U N) σ)) (query : Query (withEvents U N) σ),
      history ++ [query] ∈ (glue P₁ P₂ R S).domain →
      ExtendsWithin eventsᶜ (stateHist (glue P₁ P₂ R S) history) (queryHist query) ∧
        ExtendsWithin events (queryHist query)
          (stateHist (glue P₁ P₂ R S) (history ++ [query])) := by
    intro history query member
    by_cases window : FromWindow (U := U) (σ := σ) P₁ (history ++ [query])
    · have memR : history ++ [query] ∈ R.domain := by
        refine mem_domain_of_answers_ne_none ?_
        rw [← answers_glue_of_fromWindow (P₂ := P₂) agree window]
        exact fun none' => (answers_eq_none_iff.1 none') member
      rw [stateHist_congr (answers_glue_of_fromWindow (P₂ := P₂) agree window),
        stateHist_congr (answers_glue_of_fromWindow (P₂ := P₂) agree
          (Window.prefix (List.prefix_append history [query]) window))]
      exact ⟨awareR.defined memR, awareR.appends memR⟩
    · obtain ⟨memS, windowV⟩ := member.resolve_left (fun h => window h.2)
      rw [stateHist_congr (answers_glue_of_untilWindow (P₁ := P₁) agree windowV),
        stateHist_congr (answers_glue_of_untilWindow (P₁ := P₁) agree
          (Window.prefix (List.prefix_append history [query]) windowV))]
      exact ⟨awareS.defined memS, awareS.appends memS⟩
  exact ⟨fun member => (key _ _ member).2, fun member => (key _ _ member).1⟩

end EventAware

/-! ## The collapse -/

section Collapse

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}
variable (P₁ P₂ : CompositeEvent N) (R : DependentDDS (withEvents U N) σ)

/-- **The collapse, in Jost's printed orientation.**  `(R^{[P₁})^{P₂]}` is already
`R^{[P₁,P₂]}`, so the combined relaxation of Definition 5.3.11 needs no transitive
closure and Theorem 5.3.12's outer relaxation is redundant. -/
theorem fromThenUntil_eq_intervalRelax :
    fromThenUntil P₁ P₂ R = intervalRelax P₁ P₂ R := by
  ext S
  constructor
  · intro member
    obtain ⟨T, hT, hS⟩ := mem_fibreComp.1 member
    have agreeRT : AgreeOn (FromWindow P₁) T R := fromP_eq_iff.1 hT
    have agreeST : AgreeOn (UntilWindow P₂) S T := untilP_eq_iff.1 hS
    refine mem_intervalRelax.2 fun transcript window => ?_
    rw [agreeST transcript window.2, agreeRT transcript window.1]
  · intro member
    have agree : AgreeOn (IntervalWindow P₁ P₂) R S := (mem_intervalRelax.1 member).symm
    refine mem_fibreComp.2 ⟨glue P₁ P₂ R S, ?_, ?_⟩
    · exact fromP_eq_iff.2 fun transcript window => answers_glue_of_fromWindow agree window
    · exact untilP_eq_iff.2 fun transcript window =>
        (answers_glue_of_untilWindow agree window).symm

/-- **The mirror orientation**, free from `fibreComp_swap_of_eq_fibre`: the collapse
in one order forces it in the other, because a fibre relation is symmetric.
Together with the previous theorem this is the affirmative answer to the open
question on p. 101 — the two relaxations commute. -/
theorem untilThenFrom_eq_intervalRelax :
    untilThenFrom P₁ P₂ R = intervalRelax P₁ P₂ R :=
  fibreComp_swap_of_eq_fibre (fun R' => fromThenUntil_eq_intervalRelax P₁ P₂ R') R

/-- The two two-fold composites agree. -/
theorem fromThenUntil_eq_untilThenFrom :
    fromThenUntil P₁ P₂ R = untilThenFrom P₁ P₂ R :=
  (fromThenUntil_eq_intervalRelax P₁ P₂ R).trans
    (untilThenFrom_eq_intervalRelax P₁ P₂ R).symm

/-- **Theorem 5.3.12's union collapses at `n = 2`.**  The union over all `n` and
all alternating words in `{P₂], [P₁}` is already the two-fold composite. -/
theorem intervalRelax_union_collapse :
    (⋃ steps : List Bool,
        fibreChain (fun S => fromP P₁ (answers S)) (fun S => untilP P₂ (answers S)) steps R)
      = intervalRelax P₁ P₂ R :=
  iUnion_fibreChain_eq_fibre (fun R' => fromThenUntil_eq_intervalRelax P₁ P₂ R') R

/-- **The witness can be taken event-aware.**  Inside Jost's Definition 3.2.3
subcategory the collapse holds with an event-aware witness, so the statement is
about event-aware resources and not merely about the ambient carrier. -/
theorem intervalRelax_witness_isEventAware {events : Set N}
    {S : DependentDDS (withEvents U N) σ} (awareR : IsEventAware events R)
    (awareS : IsEventAware events S) (member : S ∈ intervalRelax P₁ P₂ R) :
    ∃ T, IsEventAware events T ∧ T ∈ fromRelax P₁ R ∧ S ∈ untilRelax P₂ T := by
  have agree : AgreeOn (IntervalWindow P₁ P₂) R S := (mem_intervalRelax.1 member).symm
  refine ⟨glue P₁ P₂ R S, glue_isEventAware agree awareR awareS, ?_, ?_⟩
  · exact fromP_eq_iff.2 fun transcript window => answers_glue_of_fromWindow agree window
  · exact untilP_eq_iff.2 fun transcript window =>
      (answers_glue_of_untilWindow agree window).symm

end Collapse

/-! ## The specification level

Jost's relaxations are relaxations of *specifications*: `𝓡^{[P}` is the union of
`R^{[P}` over the members `R ∈ 𝓡`.  A resource-level fibre identity does not by
itself give the specification-level identity, so it is derived here explicitly. -/

section Specifications

variable {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}

/-- `𝓡^{P]}`. -/
noncomputable def specUntilRelax (P : CompositeEvent N)
    (spec : Set (DependentDDS (withEvents U N) σ)) : Set (DependentDDS (withEvents U N) σ) :=
  ⋃ R ∈ spec, untilRelax P R

/-- `𝓡^{[P}`. -/
noncomputable def specFromRelax (P : CompositeEvent N)
    (spec : Set (DependentDDS (withEvents U N) σ)) : Set (DependentDDS (withEvents U N) σ) :=
  ⋃ R ∈ spec, fromRelax P R

/-- `𝓡^{[P₁,P₂]}`. -/
noncomputable def specIntervalRelax (P₁ P₂ : CompositeEvent N)
    (spec : Set (DependentDDS (withEvents U N) σ)) : Set (DependentDDS (withEvents U N) σ) :=
  ⋃ R ∈ spec, intervalRelax P₁ P₂ R

/-- The two-fold composite `(R^{[P₁})^{P₂]}` *is* the specification-level
until-relaxation of the from-relaxation of a single resource — the reading of
Jost's nested notation, made unambiguous. -/
theorem fromThenUntil_eq_spec (P₁ P₂ : CompositeEvent N)
    (R : DependentDDS (withEvents U N) σ) :
    fromThenUntil P₁ P₂ R = specUntilRelax P₂ (fromRelax P₁ R) := rfl

/-- Likewise for the mirror composite `(R^{P₂]})^{[P₁}`. -/
theorem untilThenFrom_eq_spec (P₁ P₂ : CompositeEvent N)
    (R : DependentDDS (withEvents U N) σ) :
    untilThenFrom P₁ P₂ R = specFromRelax P₁ (untilRelax P₂ R) := rfl

variable (P₁ P₂ : CompositeEvent N) (spec : Set (DependentDDS (withEvents U N) σ))

/-- **The collapse at the specification level**, printed orientation.  The
union-moving argument is `specFibre_specFibre_of_collapse`, which needs only the
two-fold collapse and no property of the projections. -/
theorem spec_untilRelax_specFromRelax :
    specUntilRelax P₂ (specFromRelax P₁ spec) = specIntervalRelax P₁ P₂ spec :=
  specFibre_specFibre_of_collapse (fun R => fromThenUntil_eq_intervalRelax P₁ P₂ R) spec

/-- **The collapse at the specification level**, mirror orientation. -/
theorem spec_fromRelax_specUntilRelax :
    specFromRelax P₁ (specUntilRelax P₂ spec) = specIntervalRelax P₁ P₂ spec :=
  specFibre_specFibre_of_collapse (fun R => untilThenFrom_eq_intervalRelax P₁ P₂ R) spec

end Specifications

/-! ## Event-awareness is indispensable

The affirmative answer above is a theorem *about the event carrier*.  Its witness
reads the global event history to decide which of `R` and `S` to run, and it has
to: a resource that cannot read the history has no such witness. -/

namespace Necessity

/-- The payload projection of a transcript: what a resource that cannot read the
global event history sees. -/
def payloads {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}} {σ : Boundary U I}
    (transcript : List (Query (withEvents U N) σ)) :
    List (Σ interface : I, U.input (σ interface)) :=
  transcript.map fun query => ⟨query.1, queryBase query⟩

/-- The payload half of a resource's answer, `⊥` included. -/
noncomputable def payloadAnswer {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
    {σ : Boundary U I} (resource : DependentDDS (withEvents U N) σ)
    (transcript : List (Query (withEvents U N) σ)) :
    Option (Σ interface : I, U.output (σ interface)) :=
  (answers resource transcript).elim none fun answer => some ⟨answer.1, answer.2.1⟩

theorem payloadAnswer_eq_none_iff {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
    {σ : Boundary U I} {resource : DependentDDS (withEvents U N) σ}
    {transcript : List (Query (withEvents U N) σ)} :
    payloadAnswer resource transcript = none ↔ answers resource transcript = none := by
  cases step : answers resource transcript <;> simp [payloadAnswer, step]

/-- **History-blindness.**  Wherever it answers at all, the resource's payload
answer depends only on the payload transcript.  The domain is deliberately
exempt: Definition 3.2.3's second clause *forces* an event-aware resource to
refuse queries whose reported history is inconsistent with its own last answer,
so requiring a history-independent domain would exclude every event-aware
resource and make the notion vacuous. -/
def HistoryBlind {I : Type i} {N : Type u} {U : SignatureUniverse.{c, u, u}}
    {σ : Boundary U I} (resource : DependentDDS (withEvents U N) σ) : Prop :=
  ∀ left right, payloads left = payloads right →
    payloadAnswer resource left ≠ none → payloadAnswer resource right ≠ none →
      payloadAnswer resource left = payloadAnswer resource right

/-! ### The witnessing instance: one interface, one event name -/

/-- One interface, `Unit` payloads in and `Bool` payloads out. -/
def sig : SignatureUniverse.{0, 0, 0} :=
  SignatureUniverse.ofInterfaces (fun _ : Unit => Unit) (fun _ : Unit => Bool)

/-- The identity boundary of `sig`. -/
def bdry : Boundary sig Unit :=
  Boundary.ofInterfaces (fun _ : Unit => Unit) (fun _ : Unit => Bool)

/-- The single event name `a`, as the composite event `ℰ_a`. -/
def evt : CompositeEvent Unit := atom ()

/-- The history in which `a` has occurred. -/
def fired : EventHistory Unit := ⟨[()], List.nodup_singleton _⟩

theorem accepts_evt_iff {query : Query (withEvents sig Unit) bdry} :
    Accepts evt query ↔ () ∈ (queryHist query).names := Iff.rfl

/-- **The two witnesses.**  `oneShot b` accepts a single query, answers `b` and
echoes the incoming history, so it triggers no event and its associated event-set
is `∅`.  Accepting only one query is what makes Definition 3.2.3's second clause
hold with no further side condition: the only history it is ever asked to extend
is the empty one. -/
noncomputable def oneShot (b : Bool) : DependentDDS (withEvents sig Unit) bdry where
  domain := {transcript | transcript.length = 1}
  empty_not_mem := by simp
  prefix_closed := by
    rintro short long pre nonempty member
    have bound : short.length ≤ long.length := pre.length_le
    have positive : short.length ≠ 0 := by simpa using nonempty
    have target : long.length = 1 := member
    show short.length = 1
    omega
  output transcript nonempty _ := (b, queryHist (transcript.getLast nonempty))

theorem mem_oneShot_domain {b : Bool} {transcript : List (Query (withEvents sig Unit) bdry)} :
    transcript ∈ (oneShot b).domain ↔ transcript.length = 1 := Iff.rfl

theorem eq_nil_of_append_mem {b : Bool} {history : List (Query (withEvents sig Unit) bdry)}
    {query : Query (withEvents sig Unit) bdry}
    (member : history ++ [query] ∈ (oneShot b).domain) : history = [] := by
  have : (history ++ [query]).length = 1 := member
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem stateHist_oneShot {b : Bool} {transcript : List (Query (withEvents sig Unit) bdry)}
    (nonempty : transcript ≠ []) (member : transcript ∈ (oneShot b).domain) :
    stateHist (oneShot b) transcript = queryHist (transcript.getLast nonempty) := by
  rw [stateHist_eq (oneShot b) nonempty member]
  rfl

/-- The witnesses are event-aware with the empty event-set: they never trigger an
event, and the only history they are asked to extend is the empty one. -/
theorem oneShot_isEventAware (b : Bool) : IsEventAware (∅ : Set Unit) (oneShot b) := by
  constructor
  · intro history query member
    obtain rfl := eq_nil_of_append_mem member
    rw [stateHist_oneShot (by simp) member]
    simp only [List.nil_append, List.getLast_singleton]
    exact ExtendsWithin.refl _ _
  · intro history query member
    obtain rfl := eq_nil_of_append_mem member
    refine ⟨EventHistory.nil_le (queryHist query), fun name _ _ => ?_⟩
    simp

theorem payloadAnswer_oneShot (b : Bool) {transcript : List (Query (withEvents sig Unit) bdry)}
    (member : transcript ∈ (oneShot b).domain) :
    payloadAnswer (oneShot b) transcript = some ⟨(), b⟩ := by
  have nonempty : transcript ≠ [] := (oneShot b).history_ne_nil member
  rw [payloadAnswer, answers_eq_some member nonempty]
  rfl

theorem oneShot_historyBlind (b : Bool) : HistoryBlind (oneShot b) := by
  intro left right _ leftNe rightNe
  have memL : left ∈ (oneShot b).domain :=
    mem_domain_of_answers_ne_none fun none' => leftNe (payloadAnswer_eq_none_iff.2 none')
  have memR : right ∈ (oneShot b).domain :=
    mem_domain_of_answers_ne_none fun none' => rightNe (payloadAnswer_eq_none_iff.2 none')
  rw [payloadAnswer_oneShot b memL, payloadAnswer_oneShot b memR]

/-! ### The counterexample -/

/-- A single query at the only interface, carrying the given history. -/
def probe (history : EventHistory Unit) : Query (withEvents sig Unit) bdry := ⟨(), ((), history)⟩

theorem payloads_probe (left right : EventHistory Unit) :
    payloads [probe left] = payloads [probe right] := rfl

theorem fromWindow_probe_fired : FromWindow evt [probe fired] := by
  intro query mem
  rw [List.mem_singleton] at mem
  subst mem
  exact accepts_evt_iff.2 (by simp [probe, queryHist, fired])

theorem untilWindow_probe_nil : UntilWindow evt [probe EventHistory.nil] := by
  intro query mem
  rw [List.mem_singleton] at mem
  subst mem
  intro held
  simpa [probe, queryHist] using accepts_evt_iff.1 held

theorem answers_oneShot_probe (b : Bool) (history : EventHistory Unit) :
    answers (oneShot b) [probe history] = some ⟨(), (b, history)⟩ := by
  have member : [probe history] ∈ (oneShot b).domain := mem_oneShot_domain.2 rfl
  rw [answers_eq_some member (by simp)]
  rfl

/-! ### Non-vacuity: the composite is strictly coarser than either factor

Without these two receipts the collapse could hold because `intervalRelax` is
everything.  It is not: the same pair of resources that `intervalRelax` identifies
is separated by *each* atomic relaxation, so the two-fold composite is strictly
larger than either factor and the collapse is a statement with content. -/

theorem not_mem_fromRelax : oneShot true ∉ fromRelax evt (oneShot false) := by
  intro member
  have clash := (fromP_eq_iff.1 member) _ fromWindow_probe_fired
  rw [answers_oneShot_probe, answers_oneShot_probe] at clash
  simp at clash
  have payload : true = false := congrArg Prod.fst clash
  simp at payload

theorem not_mem_untilRelax : oneShot true ∉ untilRelax evt (oneShot false) := by
  intro member
  have clash := (untilP_eq_iff.1 member) _ untilWindow_probe_nil
  rw [answers_oneShot_probe, answers_oneShot_probe] at clash
  simp at clash
  have payload : true = false := congrArg Prod.fst clash
  simp at payload

/-- **Event-awareness cannot be dropped.**  Both witnesses are event-aware and
history-blind, and the hypothesis of the collapse holds *vacuously* — the overlap
window `FromWindow evt ∧ UntilWindow evt` contains only the empty transcript — yet
no history-blind resource can be the witness the collapse produces.  So the
affirmative answer to Jost's open question holds because of the Chapter 3
extension: it is false in a framework whose resources cannot read the global event
history. -/
theorem historyBlind_collapse_fails :
    oneShot true ∈ intervalRelax evt evt (oneShot false) ∧
      HistoryBlind (oneShot false) ∧ HistoryBlind (oneShot true) ∧
      IsEventAware (∅ : Set Unit) (oneShot false) ∧
      IsEventAware (∅ : Set Unit) (oneShot true) ∧
      ¬ ∃ T, HistoryBlind T ∧ T ∈ fromRelax evt (oneShot false) ∧
        oneShot true ∈ untilRelax evt T := by
  refine ⟨mem_intervalRelax.2 fun transcript window => ?_,
    oneShot_historyBlind false, oneShot_historyBlind true,
    oneShot_isEventAware false, oneShot_isEventAware true, ?_⟩
  · rw [eq_nil_of_intervalWindow_self window]
    simp
  · rintro ⟨T, blind, hT, hS⟩
    have onFired : answers T [probe fired] = answers (oneShot false) [probe fired] :=
      (fromP_eq_iff.1 hT) _ fromWindow_probe_fired
    have onNil : answers (oneShot true) [probe EventHistory.nil]
        = answers T [probe EventHistory.nil] :=
      (untilP_eq_iff.1 hS) _ untilWindow_probe_nil
    have firedVal : payloadAnswer T [probe fired] = some ⟨(), false⟩ := by
      rw [payloadAnswer, onFired, answers_oneShot_probe]
      rfl
    have nilVal : payloadAnswer T [probe EventHistory.nil] = some ⟨(), true⟩ := by
      rw [payloadAnswer, ← onNil, answers_oneShot_probe]
      rfl
    have clash := blind _ _ (payloads_probe fired EventHistory.nil)
      (by rw [firedVal]; simp) (by rw [nilVal]; simp)
    rw [firedVal, nilVal] at clash
    simp at clash

end Necessity

end RandomSystemsCC.IntervalWise
