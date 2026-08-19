/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Complexity.AdvantageSeq

/-!
# Eval case 2 — chain bound

A hybrid argument over a chain of `n + 1` systems: given a bound on each
adjacent hop, bound the endpoints.

This is deliberately the shape an agent is most tempted to hand-roll — an
induction over the chain, or a fold of `maxAdvantage_triangle` — when the
library already proves it in general.
-/

namespace RandomSystems.CR18.Complexity.Eval

universe u v

variable {X : Type u} {Y : Type v}

/-- **Chain bound.** If consecutive systems in a trace are `eps i`-close, the
endpoints are `∑ eps`-close.

Prove this. -/
theorem chain_bound (systems : SystemTrace X Y) (n : Nat) (eps : Nat → ℝ)
    (hstep : ∀ i, i < n → Δ(systems i, systems (i + 1)) ≤ eps i) :
    Δ(systems 0, systems n) ≤ ∑ i ∈ Finset.range n, eps i := by
  sorry

end RandomSystems.CR18.Complexity.Eval
