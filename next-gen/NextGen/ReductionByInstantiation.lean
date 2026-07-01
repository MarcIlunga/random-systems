/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist

/-!
# CR18 §4.7.3 — Reductions by Multiple Instantiation

CR18 §4.7.3, the second basic reduction type: the reduction function `σ^q` maps a (probabilistic)
solver — e.g. a winner `W` — to its `q`-fold independent instantiation `W^q` (Def 4.9):

> `σ^q : W ↦ σ^q(W) = W^q`.

It is *just a function* — the q-fold i.i.d. power `Dist.iidPow` (§4.7.1) read as a reduction. (No new
type, no structure; `σ[q]` is a scoped notation for it, like `ρ[c]` for §4.7.2's `ρ^C`.)
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

/-- CR18 §4.7.3: the **multiple-instantiation reduction** `σ^q : W ↦ W^q`, sending a solver/winner to
its `q`-fold independent instantiation (Def 4.9, `Dist.iidPow`). Just a function. -/
noncomputable def sigmaPow {A : Type*} (q : ℕ) (W : Dist A) : Dist (Fin q → A) :=
  Dist.iidPow W q

/-- `σ[q]` is Maurer's reduction `σ^q` (Lean can't superscript a variable). -/
scoped notation:max "σ[" q "]" => sigmaPow q

@[simp] theorem sigmaPow_eq {A : Type*} (q : ℕ) (W : Dist A) : σ[q] W = Dist.iidPow W q := rfl

end RandomSystems.CR18
