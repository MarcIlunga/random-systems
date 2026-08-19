/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.Dist
import RandomSystems.DistExpect

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
noncomputable def winProb (win : Winner → Game → Prop) (W : Dist Winner) (G : Dist Game) : ℝ :=
  W.sum fun w wp => G.sum fun g gp => wp * gp * if win w g then 1 else 0

/-- `winProb` is bounded above by the game's total mass — and hence by `1` for a probability
distribution winner against a probability distribution game.  (The game law must
be non-negative; over the signed carrier this is no longer structural.) -/
theorem winProb_le_weight (win : Winner → Game → Prop) (W : Dist Winner) {G : Dist Game}
    (hW : W.isProbDist) (hG : G.NonNeg) : winProb win W G ≤ G.weight := by
  have hinner : ∀ (w : Winner) (wp : ℝ), 0 ≤ wp →
      (G.sum fun g gp => wp * gp * if win w g then 1 else 0) ≤ wp * G.weight := by
    intro w wp hwp
    calc (G.sum fun g gp => wp * gp * if win w g then 1 else 0)
        ≤ G.sum fun _ gp => wp * gp := by
          apply Finsupp.sum_le_sum; intro g _; split <;>
            simp [mul_nonneg hwp (hG g)]
      _ = wp * G.weight := by rw [Dist.weight_eq_finsupp_sum, Finsupp.mul_sum]
  calc winProb win W G
      ≤ W.sum fun _ wp => wp * G.weight := by
        apply Finsupp.sum_le_sum; intro w _; exact hinner w (W w) (hW.nonNeg w)
    _ = (W.sum fun _ wp => wp) * G.weight := by rw [← Finsupp.sum_mul]
    _ = G.weight := by
        have hWsum : (W.sum fun _ wp => wp) = 1 := by
          rw [← Dist.weight_eq_finsupp_sum]; exact hW.weight_eq
        rw [hWsum, one_mul]

/-- `winProb` of a non-negative winner law against a non-negative game law is
non-negative. -/
theorem winProb_nonneg (win : Winner → Game → Prop) {W : Dist Winner} {G : Dist Game}
    (hW : W.NonNeg) (hG : G.NonNeg) : 0 ≤ winProb win W G := by
  unfold winProb
  rw [Finsupp.sum]
  refine Finset.sum_nonneg fun w _ => ?_
  rw [Finsupp.sum]
  refine Finset.sum_nonneg fun g _ => ?_
  refine mul_nonneg (mul_nonneg (hW w) (hG g)) ?_
  split <;> norm_num

/-- `winProb` against an arbitrary (possibly signed) game law is bounded above
by the game's positive-part mass, for a probability-distribution winner.  This
is what keeps advantage suprema genuinely bounded on the signed carrier. -/
theorem winProb_le_sum_posPart (win : Winner → Game → Prop) (W : Dist Winner)
    (G : Dist Game) (hW : W.isProbDist) :
    winProb win W G ≤ G.sum fun _ gp => max gp 0 := by
  have hinner : ∀ (w : Winner) (wp : ℝ), 0 ≤ wp →
      (G.sum fun g gp => wp * gp * if win w g then 1 else 0)
        ≤ wp * G.sum fun _ gp => max gp 0 := by
    intro w wp hwp
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_le_sum
    intro g _
    split
    · rw [mul_one]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hwp
    · rw [mul_zero]
      exact mul_nonneg hwp (le_max_right _ _)
  calc winProb win W G
      ≤ W.sum fun _ wp => wp * G.sum fun _ gp => max gp 0 := by
        apply Finsupp.sum_le_sum; intro w _; exact hinner w (W w) (hW.nonNeg w)
    _ = (W.sum fun _ wp => wp) * G.sum fun _ gp => max gp 0 := by
        rw [← Finsupp.sum_mul]
    _ = _ := by rw [← Dist.weight_eq_finsupp_sum, hW.weight_eq, one_mul]

/-- Companion lower bound: `winProb` dominates the game's negative-part mass. -/
theorem sum_negPart_le_winProb (win : Winner → Game → Prop) (W : Dist Winner)
    (G : Dist Game) (hW : W.isProbDist) :
    (G.sum fun _ gp => min gp 0) ≤ winProb win W G := by
  have hinner : ∀ (w : Winner) (wp : ℝ), 0 ≤ wp →
      wp * (G.sum fun _ gp => min gp 0)
        ≤ (G.sum fun g gp => wp * gp * if win w g then 1 else 0) := by
    intro w wp hwp
    rw [Finsupp.mul_sum]
    apply Finsupp.sum_le_sum
    intro g _
    split
    · rw [mul_one]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) hwp
    · rw [mul_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hwp (min_le_right _ _)
  calc (G.sum fun _ gp => min gp 0)
      = (W.sum fun _ wp => wp) * G.sum fun _ gp => min gp 0 := by
        rw [← Dist.weight_eq_finsupp_sum, hW.weight_eq, one_mul]
    _ = W.sum fun _ wp => wp * G.sum fun _ gp => min gp 0 := by
        rw [← Finsupp.sum_mul]
    _ ≤ winProb win W G := by
        apply Finsupp.sum_le_sum; intro w _; exact hinner w (W w) (hW.nonNeg w)

/-- **won + not-won = total mass** (generic complement law): the two indicators sum to `1`
pointwise, so the winning probabilities at `win` and its complement partition the product mass. -/
theorem winProb_add_compl (win : Winner → Game → Prop) (W : Dist Winner) (G : Dist Game) :
    winProb win W G + winProb (fun w g => ¬ win w g) W G = W.weight * G.weight := by
  classical
  unfold winProb
  rw [← Finsupp.sum_add, Dist.weight_eq_finsupp_sum, Finsupp.sum_mul]
  refine Finsupp.sum_congr fun w _ => ?_
  rw [← Finsupp.sum_add, Dist.weight_eq_finsupp_sum, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  by_cases h : win w g <;> simp [h]

/-- Winning probability depends on the winning predicate only through its values on the winner
distribution's support. -/
theorem winProb_congr_left {win win' : Winner → Game → Prop} (W : Dist Winner) (G : Dist Game)
    (h : ∀ w ∈ W.support, ∀ g, win w g ↔ win' w g) :
    winProb win W G = winProb win' W G := by
  unfold winProb
  refine Finsupp.sum_congr fun w hw => Finsupp.sum_congr fun g _ => ?_
  classical
  by_cases hwin : win w g
  · rw [if_pos hwin, if_pos ((h w hw g).mp hwin)]
  · rw [if_neg hwin, if_neg (fun h' => hwin ((h w hw g).mpr h'))]

/-- **`winProb` is affine in the winner law**: `G(W) = 𝔼_{w ∼ W}[G(δ_w)]`, i.e. a probabilistic
winner's performance is the `W`-average of the performances of the deterministic winners it mixes.
Signed layer — no hypothesis on `W` or `G` at all, since the identity is bilinearity of Def 4.5's
double sum, not normalization.

This is the engine of CR18's remark after Definition 2.7 ("probabilistic distinguishers are not more
powerful than deterministic ones"): a supremum of an affine functional over a simplex is attained on
the extreme points.  `CR18.maxAdvantage_eq_sSup_deterministic` is that consequence, for `∆`. -/
theorem winProb_eq_expect_single (win : Winner → Game → Prop) (W : Dist Winner)
    (G : Dist Game) :
    winProb win W G = W.expect fun w => winProb win (Finsupp.single w 1) G := by
  unfold winProb Dist.expect
  refine Finsupp.sum_congr fun w _ => ?_
  show (Finsupp.sum G fun g gp => W w * gp * if win w g then 1 else 0)
      = W w * ((Finsupp.single w 1).sum fun w' wp =>
          Finsupp.sum G fun g gp => wp * gp * if win w' g then 1 else 0)
  rw [Finsupp.sum_single_index (by simp), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun g _ => by ring

/-- **CR18 Definition 4.17**: the maximal winning probability `Γ(G) := sup_W G(W)`, the supremum of
`winProb win · G` over **probability-distribution** winners (the restriction is essential: `Dist` is a
sub-distribution of arbitrary weight, so the unrestricted sup is junk). -/
noncomputable def maxWinProb (win : Winner → Game → Prop) (G : Dist Game) : ℝ :=
  sSup ((fun W : Dist Winner => winProb win W G) '' {W | W.isProbDist})

/-- The set of winning probabilities of probability-distribution winners is bounded above (by the
game's positive-part mass), so `Γ` is a genuine supremum. -/
theorem bddAbove_winProb_image (win : Winner → Game → Prop) (G : Dist Game) :
    BddAbove ((fun W : Dist Winner => winProb win W G) '' {W | W.isProbDist}) :=
  ⟨G.sum fun _ gp => max gp 0, by
    rintro x ⟨W', hW', rfl⟩; exact winProb_le_sum_posPart win W' G hW'⟩

/-- **CR18 Definition 4.17**: `G(W) ≤ Γ(G)` — the winning probability of any probability-distribution
winner is a lower bound on the maximal winning probability. -/
theorem winProb_le_maxWinProb (win : Winner → Game → Prop) (G : Dist Game) (W : Dist Winner)
    (hW : W.isProbDist) : winProb win W G ≤ maxWinProb win G :=
  le_csSup (bddAbove_winProb_image win G) ⟨W, hW, rfl⟩

end RandomSystems.CR18.GamePerf
