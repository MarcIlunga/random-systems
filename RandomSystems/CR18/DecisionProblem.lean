/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# CR18 §4.1.1 — Decision Problems

Faithful model of Maurer's §4.1.1. The text says, literally:

> A decision problem is characterized by an instance set `X` and a predicate `P : X → {0,1}`.
> The problem consists of deciding, for a given `x ∈ X`, whether `P(x) = 1`.

and, for the witness form:

> A specific type of decision problem is characterized by a predicate `Q : X × W → {0,1}` …
> the problem consists of deciding … whether there exists a witness `w ∈ W` such that
> `Q(x,w) = 1`, i.e., `P(x) := ∃w Q(x,w)`.

So §4.1.1 is *entirely predicates*. We model a predicate by Lean's native `X → Prop`
(equivalently `Set X`): `{0,1}` is the two truth values and "`P(x) = 1`" is "`P x` holds".

Two modeling commitments, both forced by the discipline of saying only what the text says:

* **No procedure to run.** "Deciding `x`" introduces *no* executor, algorithm, trace, or loop —
  the answer for an instance `x` simply *is* `P x`. A decision problem is a predicate, full stop.
* **`Prop`, not `Bool`.** The witness form `P(x) := ∃w Q(x,w)` is literally an existential, which
  is `Prop`-valued. Modelling the predicate in `Bool` would force a decidability bridge on that
  `∃` (undecidable in general), and a forced "constructed = intended" bridge is exactly the smell
  of a wrong model. `Prop` makes `P(x) := ∃w Q(x,w)` hold by definition.
-/

namespace RandomSystems.CR18

universe u v

/-- CR18 §4.1.1: a **decision problem** on instance set `X` is a predicate `P : X → {0,1}` —
Lean's `X → Prop` (= `Set X`). "Deciding `x`" is asking whether `P x` holds; there is no
execution, the answer for an instance *is* the predicate value. -/
abbrev DecisionProblem (X : Type u) : Type u := X → Prop

/-- CR18 §4.1.1, "a specific type of decision problem": from a witness predicate
`Q : X × W → {0,1}` over a witness set `W`, the decision problem `P(x) := ∃ w, Q(x,w)` — decide
whether instance `x` admits a witness. It is a `DecisionProblem X` *by construction* (the return
type), exactly the text's "is a specific type of decision problem", and `P(x)` unfolds to the
existential definitionally. -/
def DecisionProblem.ofWitness {X : Type u} {W : Type v} (Q : X × W → Prop) :
    DecisionProblem X :=
  fun x => ∃ w, Q (x, w)

/-- CR18 Example 4.2: primality is a decision problem on `ℕ` (the text notes it is in `P`).
Modelled with Lean's existing `Nat.Prime`; the decision problem *is* that predicate. -/
def primality : DecisionProblem ℕ := fun n => n.Prime

end RandomSystems.CR18
