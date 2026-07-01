/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist

/-!
# CR18 Definitions 4.5 & 4.17 — winning probability & Γ (next-gen, function-based)

Function-based game-performance layer: the winning predicate `win : Winner → Game → Prop` (Maurer's
`ω`) is a **plain function argument**, NOT a structure field — there is no `GameStructure` record. It
is `Prop`-valued (not `Bool`), to match the concrete winning predicate `PFunDDS.Wins` (Def 3.23),
which is an existential over the interaction run, deliberately *not* `decide`d to `Bool`. A
probabilistic game/winner is a `Dist` over the deterministic carrier, and

  `winProb win W G = ∑_{w,g} W(w)·G(g)·⟦win w g⟧`   (Def 4.5)
  `maxWinProb win G = Γ(G) = sup_{W prob.dist} winProb win W G`   (Def 4.17)

The indicator `⟦win w g⟧` is the classical `if win w g then 1 else 0` (`open Classical` supplies the
decidability of the `Prop`; no `DecidableEq` on any carrier). This is the same functional as
`ReductionByConverter.winProb` specialized, so the §4.7.2 (4.10) reduction-by-converter plugs in.
-/

namespace RandomSystems.CR18.GamePerf

open RandomSystems (Dist)
open Classical

universe u v

variable {Winner : Type u} {Game : Type v}

/-- **CR18 Definition 4.5**: the winning probability of probabilistic winner `W` against probabilistic
game `G`, with winning predicate `win` (a `Prop`, e.g. `PFunDDS.Wins`). Function-based: `win` is an
argument, not a structure field; the indicator is the classical `if`. -/
noncomputable def winProb (win : Winner → Game → Prop) (W : Dist Winner) (G : Dist Game) : NNReal :=
  W.sum fun w wp => G.sum fun g gp => wp * gp * if win w g then 1 else 0

/-- `winProb` is bounded above by the game's total mass — and hence by `1` for a probability
distribution winner against a probability distribution game. -/
theorem winProb_le_weight (win : Winner → Game → Prop) (W : Dist Winner) (G : Dist Game)
    (hW : W.isProbDist) : winProb win W G ≤ G.weight := by
  have hinner : ∀ (w : Winner) (wp : NNReal),
      (G.sum fun g gp => wp * gp * if win w g then 1 else 0) ≤ wp * G.weight := by
    intro w wp
    calc (G.sum fun g gp => wp * gp * if win w g then 1 else 0)
        ≤ G.sum fun _ gp => wp * gp := by
          apply Finsupp.sum_le_sum; intro g _; split <;> simp
      _ = wp * G.weight := by rw [Dist.weight_eq_finsupp_sum, Finsupp.mul_sum]
  calc winProb win W G
      ≤ W.sum fun _ wp => wp * G.weight := by
        apply Finsupp.sum_le_sum; intro w _; exact hinner w (W w)
    _ = (W.sum fun _ wp => wp) * G.weight := by rw [← Finsupp.sum_mul]
    _ = G.weight := by
        have hWsum : (W.sum fun _ wp => wp) = 1 := by
          rw [← Dist.weight_eq_finsupp_sum]; exact hW
        rw [hWsum, one_mul]

/-- **CR18 Definition 4.17**: the maximal winning probability `Γ(G) := sup_W G(W)`, the supremum of
`winProb win · G` over **probability-distribution** winners (the restriction is essential: `Dist` is a
sub-distribution of arbitrary weight, so the unrestricted sup is junk). -/
noncomputable def maxWinProb (win : Winner → Game → Prop) (G : Dist Game) : NNReal :=
  sSup ((fun W : Dist Winner => winProb win W G) '' {W | W.isProbDist})

/-- The set of winning probabilities of probability-distribution winners is bounded above (by the
game's mass), so `Γ` is a genuine supremum. -/
theorem bddAbove_winProb_image (win : Winner → Game → Prop) (G : Dist Game) :
    BddAbove ((fun W : Dist Winner => winProb win W G) '' {W | W.isProbDist}) :=
  ⟨G.weight, by rintro x ⟨W', hW', rfl⟩; exact winProb_le_weight win W' G hW'⟩

/-- **CR18 Definition 4.17**: `G(W) ≤ Γ(G)` — the winning probability of any probability-distribution
winner is a lower bound on the maximal winning probability. -/
theorem winProb_le_maxWinProb (win : Winner → Game → Prop) (G : Dist Game) (W : Dist Winner)
    (hW : W.isProbDist) : winProb win W G ≤ maxWinProb win G :=
  le_csSup (bddAbove_winProb_image win G) ⟨W, hW, rfl⟩

end RandomSystems.CR18.GamePerf
