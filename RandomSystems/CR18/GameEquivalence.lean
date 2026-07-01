/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18.PDS

/-!
# CR18 §4.10.1 / Definition 4.15 — Pre-winning behavior of a game

A game is a system with a **monotone binary output** (MBO) `A`, so its output type is `Y × Bool`
(`false = 0 = not won`). CR18 Definition 4.15 (p.105) defines the **pre-winning behavior** of a game
`G` as the sequence of conditional distributions

> `p^G_{Y_i, A_i=0 | X^i Y^{i-1}, A_{i-1}=0}`   for `i ≥ 1`   (4.34)

— "how `G` can be won, but not what happens afterwards."

It is **derived from the behavior** (Def 3.18). We use the `PFunPDS` behavior — the *(potentially
partial) function*

```
  PFunPDS.Behavior X Y = (i : ℕ) → Y × (Vector X (i+1) × Vector Y i) →. NNReal
```

— `b(G) i (yᵢ, xⁱ⁺¹, yⁱ)` is the conditional probability `p^G_{Y_{i+1}|X^{i+1}Y^i}` (partial: `⊥` when
the conditioning event has probability 0). It is built from `Pr[· | s ←$ S, ·]` conditioning, *not* by
filtering a finite support, so it carries **no `DecidableEq`** — conditioning is not a decidability fact.

The pre-winning behavior is that kernel restricted to the not-yet-won region: set every previous MBO bit
to `false` (condition on `A_{i-1}=0`) and read off the `A_i = false` part of the next output. Purely a
reindexing of the partial-function behavior — no new probability machinery, no `DecidableEq`.
-/

namespace RandomSystems.CR18

universe u v

variable {X : Type u} {Y : Type v}

/-- **CR18 Definition 4.15: the pre-winning behavior**, as a transformation of the partial-function
behavior (Def 3.18). For a behavior `b : PFunPDS.Behavior X (Y × Bool)` whose `Bool` component is the
MBO `A` (`false = 0 = not won`), `prewinBehavior b` is the `PFunPDS.Behavior X Y` obtained by setting
every previous MBO bit to `false` (condition on the not-yet-won region `A_{i-1}=0`) and reading the
`A_i = false` part of the next output: `p^G_{Y_i, A_i=0 | X^i Y^{i-1}, A_{i-1}=0}`. No `DecidableEq`. -/
def prewinBehavior (b : PFunPDS.Behavior X (Y × Bool)) : PFunPDS.Behavior X Y :=
  fun i arg => b i ((arg.1, false), (arg.2.1, arg.2.2.map (fun y => (y, false))))

/-- The pre-winning behavior of a **game system** `G` — a `PFunPDS` with MBO output `Y × Bool` — is the
pre-winning behavior of its behavior `b(G)` (Def 3.18). This is the literal CR18 Definition 4.15,
exhibited as derived from the (`DecidableEq`-free, partial-function) behavior `PFunPDS.behavior G`. -/
noncomputable def gamePrewinBehavior (G : PFunPDS X (Y × Bool)) : PFunPDS.Behavior X Y :=
  prewinBehavior (PFunPDS.behavior G)

/-- Compatibility witness: each round of the pre-winning behavior is `b(G)`'s value at the not-won
history. No `DecidableEq` instances appear — the leak is gone. -/
theorem gamePrewinBehavior_eq (G : PFunPDS X (Y × Bool)) (i : ℕ) :
    gamePrewinBehavior G i
      = fun arg => PFunPDS.behavior G i
          ((arg.1, false), (arg.2.1, arg.2.2.map (fun y => (y, false)))) :=
  rfl

/-- **CR18 Definition 4.16: equivalence as games** (`≡ᵍ`): two games are equivalent as games iff their
pre-winning behavior (Def 4.15) is identical — they behave the same as long as the game is not won. -/
def GameEquiv (G H : PFunPDS X (Y × Bool)) : Prop :=
  gamePrewinBehavior G = gamePrewinBehavior H

@[inherit_doc GameEquiv] scoped infix:50 " ≡ᵍ " => GameEquiv

end RandomSystems.CR18
