/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.CR18.DecisionProblem
import RandomSystems.CR18.AbstractProblem

/-!
# CR18 §4.1.2 — Search Problems

Faithful model of Maurer's §4.1.2. The text says, literally:

> Definition 4.1. A search problem is a 4-tuple `(X, W, Q, P_X)` consisting of an instance set
> `X`, a solution set (or witness set) `W`, a predicate `Q : X × W → {0,1}`, as well as a
> probability distribution `P_X` over the instance set. … The search problem `(X, W, Q, P_X)`
> consists of finding, for a given instance `x ∈ X` drawn according to `P_X`, a `w ∈ W` such
> that `Q(x,w) = 1`. Typically one considers cases where every instance `x` has at least one
> solution `w`, but other cases can also be considered by allowing a special output "no
> solution".

Same philosophy as `DecisionProblem` (§4.1.1) — predicates and functions, no executions, no
traces:

* **"A 4-tuple" is literally a product**, not a record. With `X, W` as the type parameters the
  remaining data is the pair `(Q, P_X)`, so `SearchProblem X W := (X × W → Prop) × PMF X` — the
  same move as `DecisionProblem X := X → Prop`, an abbrev to a plain type expression. The first
  component is the solution predicate `Q`, the second the instance distribution `P_X`.
* The two run-time-flavoured words, "drawn" and "finding", introduce **no** sampler and **no**
  solver. A search problem is just this data; "a solution for `x`" is any `w` with `Q (x, w)`,
  i.e. the relation `Q` itself. We do not model an algorithm, its output, or its trace.
* `Q` is again a `Prop`-valued predicate, so it agrees with the witness predicate of §4.1.1 and
  the underlying decision problem `∃w Q(x,w)` holds definitionally.
* `P_X` is a probability distribution over the instance set — Lean's existing `PMF X`.
-/

namespace RandomSystems.CR18

/-- CR18 **Definition 4.1**: a **search problem** is the 4-tuple `(X, W, Q, P_X)` — instance set
`X`, solution (witness) set `W`, solution predicate `Q : X × W → {0,1}`, instance distribution
`P_X`. With `X, W` as type parameters it is the *product* of the predicate and the distribution:
`·.1` is the solution predicate `Q` (`w` solves `x` iff `(·.1) (x, w)`), `·.2` is the instance
distribution `P_X` (`PMF X`). "Finding, for `x` drawn from `P_X`, a `w` with `Q(x,w)`" is *not* a
procedure: a search problem is this data, and a solution for `x` is any `w` with `(·.1) (x, w)`. -/
abbrev SearchProblem (X W : Type*) : Type _ := (X × W → Prop) × PMF X

-- The whole development is classical / measure-theoretic (e.g. `PMF.toOuterMeasure`); rather than
-- annotate each definition, the section is `noncomputable`.
noncomputable section

variable {X W : Type*}

/-- CR18 §4.1.2, opening sentence ("the search problem corresponding to a decision problem"). The
decision problem *underlying* a search problem forgets the instance distribution `sp.2` and asks
only whether a solution *exists*: `P(x) := ∃ w, Q(x,w)` — exactly `DecisionProblem.ofWitness` on
the solution predicate `sp.1`. -/
def SearchProblem.toDecision (sp : SearchProblem X W) : DecisionProblem X :=
  DecisionProblem.ofWitness sp.1

/-- CR18 §4.1.2: the **typical** case, "every instance `x` has at least one solution `w`". The
complementary case is the text's "no solution"; modelling solutions as the relation `sp.1` (not a
solver with a `none` output) makes that case simply the negation of this — no special value. -/
def SearchProblem.Total (sp : SearchProblem X W) : Prop :=
  ∀ x, ∃ w, sp.1 (x, w)

/-- CR18 **Example 4.5** (function inversion `I_f`). For `f : W → X`, inverting `f` is the search
problem whose solution predicate is `Q (x, w) := f w = x` and whose instance distribution is
`f(U)` — the uniform distribution on the domain `W` pushed through `f`. The DL problem (Example
4.4) is also of this form; a function whose inversion problem is hard is a *one-way function*.
Built entirely from Lean's existing `PMF` infrastructure (`PMF.uniformOfFintype`, `PMF.map`). -/
def inversion [Fintype W] [Nonempty W] (f : W → X) : SearchProblem X W :=
  (fun (x, w) => f w = x, (PMF.uniformOfFintype W).map f)

/-- The decision problem underlying function inversion is exactly "`x` is in the range of `f`",
and it holds definitionally — no bridge. -/
example [Fintype W] [Nonempty W] (f : W → X) (x : X) :
    (inversion f).toDecision x ↔ ∃ w, f w = x := Iff.rfl

/-! ## §4.4.3 compatibility: a search problem *is* a Def-4.2 abstract problem

This is the bridge the abstract `Problem` typeclass (§4.4.3) exists for: a §4.1.2 search problem
becomes a Def-4.2 problem by supplying its solver set, performance set, and performance function.
No execution — the performance is a probability, defined as a measure. -/

/-- CR18 §4.4.3 / Def 4.2 **instance**: a search problem `(Q, P_X)` is an abstract problem. Its
solver set is the deterministic algorithms `X → W` (guess a witness for each instance); its
performance set is the probabilities `ℝ≥0∞` (the values lie in `[0,1]`); and its performance
function `p̂` is the **success probability** — the `P_X`-mass of the instances the solver gets
right: `p̂(f) = Pr_{x ~ P_X}[Q(x, f x)]`, i.e. the `P_X`-outer-measure of `{x | Q(x, f x)}`.
(Randomized solvers `X → PMF W` are the obvious generalization.) -/
instance searchProblemIsProblem :
    Problem (SearchProblem X W) (X → W) ENNReal where
  perf := fun (Q, PX) f => PX.toOuterMeasure {x | Q (x, f x)}

/-- Specializing Def 4.2's `a`-solver through the instance: an `a`-solver for a search problem is
exactly a solver whose success probability is at least `a` — definitionally. -/
example (sp : SearchProblem X W) (a : ENNReal) (f : X → W) :
    Problem.IsASolver sp a f ↔ a ≤ sp.2.toOuterMeasure {x | sp.1 (x, f x)} := Iff.rfl

end

end RandomSystems.CR18
