/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCrypto.EventAlgebra

/-!
# The global event history (Jost, Ch. 3 §3.2.1)

Jost's *Constructive Cryptography with Events* adds a **global event history**
to the system algebra, and presents it (p. 33) as "an alternative instantiation
of Constructive Cryptography's higher-level axioms", so that (p. 31) "results
proven at those abstraction levels directly translate over".  That is our
architecture exactly — axioms at the AC layer, instantiate concretely, inherit
the theorems — so events slot in rather than displacing anything.

## What this file settles, and why it comes first

The estate already carries **two** event-flavoured notions:

* GegMau26's `AbstractCrypto.EventAlgebra` (a `CoheytingAlgebra` plus the
  linear-occurrence axiom E5), adopted as a design guide in `DESIGN.md` §10.6;
* the monotone-binary-output machinery (`RandomSystems.SystemMBO`, `GameOf`,
  CR18 Thm 4.17) — and Jost states outright (p. 33) that events **generalize**
  MPR07's MBOs.

So the first obligation is not to build anything but to check whether Jost's
composite events are a *third* notion or an instance of one we have.  They are
an instance, and the fit is exact:

* Jost's composite events are the **monotone predicates** `P(ℰ)` on histories
  (§3.2.2, "an event is essentially just a named monotone condition").
* Monotone predicates for the extension order are the **upper sets** of that
  order, i.e. the `LowerSet`s of its dual.
* GegMau26 Def 9 asks that every **principal up-set** be a chain.  The
  extension order fails this — `[a]` extends to both `[a,b]` and `[a,c]`, which
  are incomparable — but its **dual** satisfies it, because the prefixes of a
  fixed history are totally ordered.  `forestOrder` below is that observation.
* GegMau26's existing `instance : EventAlgebra (LowerSet P)` for a forest `P`
  then applies, giving `compositeEventAlgebra` with no new axioms.

The practical consequence is that the `⊓`/`⊔`/`\` calculus for composite
events, and E5, are **inherited** rather than re-proved, and that the events
axis stops being orthogonal to the rest of the estate.
-/

namespace RandomSystemsCC.Events

open AbstractCrypto

variable {N : Type*}

/-- **Jost Definition 3.2.1.**  A global event history is a list of names
without duplicates.  Duplicate-freeness is what makes "the event `n` occurred"
a well-defined *monotone* condition rather than a count. -/
structure EventHistory (N : Type*) where
  /-- The names that have occurred, in order of occurrence. -/
  names : List N
  /-- No event occurs twice. -/
  nodup : names.Nodup

namespace EventHistory

@[ext] theorem ext {E F : EventHistory N} (h : E.names = F.names) : E = F := by
  cases E; cases F; simp at h; simp [h]

/-- `ℰₙ` — the event `n` has occurred. -/
def Occurred (E : EventHistory N) (n : N) : Prop := n ∈ E.names

instance [DecidableEq N] (E : EventHistory N) (n : N) :
    Decidable (E.Occurred n) := inferInstanceAs (Decidable (n ∈ E.names))

/-- `ℰ ⁺← ℰₙ` — append `n` if it has not occurred, leave the history unchanged
otherwise.  Idempotent by construction, which is what keeps occurrence
monotone. -/
def cons [DecidableEq N] (E : EventHistory N) (n : N) : EventHistory N :=
  if h : n ∈ E.names then E
  else ⟨E.names ++ [n], by simpa using E.nodup.append (by simp) (by simpa using h)⟩

@[simp] theorem cons_occurred [DecidableEq N] (E : EventHistory N) (n : N) :
    (E.cons n).Occurred n := by
  unfold cons Occurred
  split <;> simp_all

/-- Occurrence is never retracted. -/
theorem occurred_cons [DecidableEq N] {E : EventHistory N} {m : N} (n : N)
    (h : E.Occurred m) : (E.cons n).Occurred m := by
  unfold cons Occurred at *
  split <;> simp_all

/-- Histories are ordered by **extension**: `E ≤ F` when `F` continues `E`.
This is the direction time runs, so every reachable history is `≥` its past. -/
instance : PartialOrder (EventHistory N) where
  le E F := E.names <+: F.names
  le_refl _ := List.prefix_refl _
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm _ _ h₁ h₂ :=
    ext (h₁.eq_of_length (le_antisymm h₁.length_le h₂.length_le))

theorem le_iff {E F : EventHistory N} : E ≤ F ↔ E.names <+: F.names := Iff.rfl

/-- **Jost Definition 3.2.2**, the happened-before relation: `ℰₙ₁ ≺ ℰₙ₂` holds
if both occurred with `n₁` first, **or if only `n₁` has occurred so far**.

The second disjunct is a deliberate asymmetry, justified on p. 34: "if we
express the condition that a message is secure if the key has been securely
erased before the memory leaked, then we do not need to insist that the memory
actually leaked."  It is not an oversight and must not be "fixed". -/
def Precedes [DecidableEq N] (E : EventHistory N) (n₁ n₂ : N) : Prop :=
  E.Occurred n₁ ∧
    (¬ E.Occurred n₂ ∨ E.names.idxOf n₁ < E.names.idxOf n₂)

/-- The asymmetric clause, isolated: an event that has occurred precedes every
event that has not. -/
theorem precedes_of_not_occurred [DecidableEq N] {E : EventHistory N} {n₁ n₂ : N}
    (h₁ : E.Occurred n₁) (h₂ : ¬ E.Occurred n₂) : E.Precedes n₁ n₂ :=
  ⟨h₁, Or.inl h₂⟩

/-- Nothing precedes anything in the empty history — `≺` still requires its
first argument to have occurred. -/
theorem not_precedes_empty [DecidableEq N] (n₁ n₂ : N) :
    ¬ (⟨[], List.nodup_nil⟩ : EventHistory N).Precedes n₁ n₂ := by
  rintro ⟨h, -⟩; simpa [Occurred] using h

end EventHistory

/-! ## The reconciliation with GegMau26

Everything below is inherited, not re-proved. -/

open EventHistory

/-- The **dual** of the extension order is a forest order: the principal up-set
of a history in the dual is its set of prefixes in the original, and prefixes
of a fixed list are totally ordered (`List.prefix_or_prefix_of_prefix`).

The undualized order is *not* a forest — `[a]` extends to both `[a,b]` and
`[a,c]` — which is exactly why composite events are `LowerSet`s of the dual
rather than of the order itself. -/
instance forestOrder : ForestOrder (EventHistory N)ᵒᵈ where
  isChain_Ici E F hF G hG _ := by
    have hF' : (OrderDual.ofDual F).names <+: (OrderDual.ofDual E).names := hF
    have hG' : (OrderDual.ofDual G).names <+: (OrderDual.ofDual E).names := hG
    -- In the dual, `F ≤ G` unfolds to `(ofDual G).names <+: (ofDual F).names`,
    -- so the two disjuncts land the other way round than they read.
    rcases List.prefix_or_prefix_of_prefix hF' hG' with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- **Jost's composite events form a GegMau26 event algebra.**

A composite event is a monotone predicate on histories (§3.2.2); monotone
predicates for the extension order are the `LowerSet`s of its dual; and
GegMau26's `EventAlgebra (LowerSet P)` instance applies to any forest `P`.

So the `⊓`/`⊔`/`\` calculus on composite events, and the linear-occurrence
axiom E5, come for free.  Nothing here is a third notion of "event". -/
noncomputable instance compositeEventAlgebra :
    EventAlgebra (LowerSet (EventHistory N)ᵒᵈ) := inferInstance

/-- A composite event, in Jost's sense: a monotone condition on the history. -/
abbrev CompositeEvent (N : Type*) := LowerSet (EventHistory N)ᵒᵈ

/-- The atomic event `ℰₙ`, as a composite event: the set of histories in which
`n` has occurred.  It is a `LowerSet` of the dual precisely because occurrence
is never retracted (`occurred_cons`). -/
def atom [DecidableEq N] (n : N) : CompositeEvent N where
  carrier := {E | (OrderDual.ofDual E).Occurred n}
  lower' := by
    intro E F hFE hE
    have extends' : (OrderDual.ofDual E).names <+: (OrderDual.ofDual F).names := hFE
    exact extends'.subset hE

end RandomSystemsCC.Events
