/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.MaxWinProb
import NextGen.PreWinFactorization

/-!
# CR18 Definition 4.5 (concrete) — the winning probability of a game, via `Wins`

The concrete winning probability is **reuse only**: `GamePerf.winProb` (Def 4.5, now `Prop`-valued)
instantiated at the concrete winning predicate `PFunDDS.Wins` (Def 3.23), read at the `DDS` level
(`Wins` uses only `g.val`). The game is a `PFunPDS X (Y × Bool) = Dist (DDS X (Y × Bool))` — the same
carrier as `gamePrewinBehavior`/`massYAfalse`/`≡ᵍ`, so there is no representation bridge.

This file fixes the concrete `winProb`/`notWonProb` and the elementary decomposition
`winProb + notWonProb = weight·weight`. The substantive step — `notWonProb` factors through the
pre-winning behavior (eq 4.37 → Lemma 4.15) — is built on top, reusing `massYAfalse`.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)

universe u v

variable {X : Type u} {Y : Type v}

/-- DDS-level form of CR18 Def 3.23 `Wins` (which reads only `g.val`): the winner `w` wins the
`(X, Y × Bool)`-system `g` iff some MBO bit turns `true` somewhere in the generic interaction
transcript `transcript g (winnerView w)` (Def 3.7). For a game `gg : DDG`, `Wins w gg = winsDDS w gg.val`. -/
def winsDDS (w : PFunDDS.Winner X Y) (g : PFunDDS.DDS X (Y × Bool)) : Prop :=
  ∃ n, ∃ y : Y, (some (y, true) : Option (Y × Bool))
    ∈ PFunDDS.transcriptOutputs (PFunDDS.transcript g (PFunDDS.winnerView w) n)

/-- **CR18 Definition 4.5 (concrete)**: the winning probability of probabilistic winner `W` against
the probabilistic game `G : PFunPDS X (Y × Bool)`. Pure reuse of `GamePerf.winProb` at `winsDDS`. -/
noncomputable def winProb (W : Dist (PFunDDS.Winner X Y)) (G : PFunPDS X (Y × Bool)) : NNReal :=
  GamePerf.winProb winsDDS W G

/-- CR18 notation for the winning probability `G(W)` (Def 4.5). Fullwidth parens `（ ）` render
Maurer's `G(W)` without clashing with function application (`Dist` coerces to a function). -/
@[inherit_doc winProb] scoped notation:max G "（" W "）" => winProb W G

/-- The complementary **not-won** probability — `GamePerf.winProb` at `¬ winsDDS`. -/
noncomputable def notWonProb (W : Dist (PFunDDS.Winner X Y)) (G : PFunPDS X (Y × Bool)) : NNReal :=
  GamePerf.winProb (fun w g => ¬ winsDDS w g) W G

/-- **won + not-won = total mass**: the winning and not-winning probabilities partition the product
mass (the two indicators sum to `1`). Hence for probability distributions, `winProb = 1 − notWonProb`. -/
theorem winProb_add_notWonProb (W : Dist (PFunDDS.Winner X Y)) (G : PFunPDS X (Y × Bool)) :
    winProb W G + notWonProb W G = W.weight * G.weight := by
  classical
  unfold winProb notWonProb GamePerf.winProb
  rw [← Finsupp.sum_add]
  rw [Dist.weight_eq_finsupp_sum, Finsupp.sum_mul]
  refine Finsupp.sum_congr fun w _ => ?_
  rw [← Finsupp.sum_add]
  rw [Dist.weight_eq_finsupp_sum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  by_cases h : winsDDS w g <;> simp [h] <;> ring

/-- **CR18 Definition 4.17 (concrete)**: the **maximal winning probability** `Γ(G) := sup_W G(W)` —
the supremum of the concrete winning probability over all **probability-distribution** winners `W`.
Faithful to the topic: it is *literally a supremum* (`GamePerf.maxWinProb` at the concrete winning
predicate `winsDDS`, Def 3.23). Two points kept true to Maurer:
* the supremum is over probability-distribution winners only (an arbitrary sub-distribution winner
  would give junk — `Dist` carries no normalization);
* the query bound is **not** baked in. Maurer's `Γ` is the plain `sup`; the `q`-query maximal
  probability is `Γ ([q]G)` — impose the bound by the filter `[q]` on the *game* (§3.4.3), not here. -/
noncomputable def maxWinProb (G : PFunPDS X (Y × Bool)) : NNReal :=
  GamePerf.maxWinProb winsDDS G

@[inherit_doc] scoped notation "Γ" => maxWinProb

/-- **CR18 Definition 4.17**: `G(W) ≤ Γ(G)` — every probability-distribution winner's winning
probability is a lower bound on the maximum. Reuse of `GamePerf.winProb_le_maxWinProb`. -/
theorem winProb_le_maxWinProb (W : Dist (PFunDDS.Winner X Y)) (G : PFunPDS X (Y × Bool))
    (hW : W.isProbDist) : G（W） ≤ Γ G :=
  GamePerf.winProb_le_maxWinProb winsDDS G W hW

/-- The defining supremum of `Γ` is over a set bounded above (by `G.weight`), so `Γ(G)` is a genuine
least upper bound, not a junk `sSup`. -/
theorem bddAbove_winProb_image (G : PFunPDS X (Y × Bool)) :
    BddAbove ((fun W : Dist (PFunDDS.Winner X Y) => winProb W G) '' {W | W.isProbDist}) :=
  GamePerf.bddAbove_winProb_image winsDDS G

end RandomSystems.CR18
