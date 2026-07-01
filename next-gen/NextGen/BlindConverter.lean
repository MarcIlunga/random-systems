/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import NextGen.WinProb
import NextGen.Theorem417

/-!
# CR18 Definition 4.20 — the blind converter `b`, and `Γ(bŜ)`

CR18 Definition 4.20: *for a game `S` we define `bS` as the game system `S` for which the outputs `Yᵢ`
are blocked, i.e. `b` is the simple converter that is transparent for the queries `Xᵢ` but blocks the
replies `Yᵢ`.* Maurer reads this at the **winner** level: "to win game `bS` means to win game `S`
blindly, without seeing the outputs … equivalently this means to win the game **non-adaptively**, since
the inputs `x₁,…,xq` can be interpreted as being chosen in advance, before seeing any outputs."

So `b` blocks a winner's view of the replies. A winner is a `DDE X Y = List (Option Y) → Option X`
(Def 3.23); its query at round `i` is `w [y₁,…,yᵢ₋₁]`. **Blocking the replies** means the query may
depend only on *how many* replies have been seen (the round number `= length`), never on their values —
exactly Maurer's `p^W_{Xᵢ|Xⁱ⁻¹}` (non-adaptive) versus `p^W_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}` (adaptive), cf. eq. (4.35).
We therefore take the **lightest faithful** representation:

* `IsBlind w` (the action of the converter `b` on a deterministic winner) — a `Prop`, not a structure:
  `w`'s output depends only on the length of its reply history.
* `Γ(bŜ)` (`blindMaxWinProb`) — `Γ` restricted to **blind**-support winner distributions, exactly as
  `Γ(Ŝ)` is the unrestricted sup (`maxWinProb`, Def 4.17). The PDF's `Γ(bS) ≤ Γ(S)` is then the trivial
  inclusion of blind winners into all winners.

No new probability machinery and no operational converter cascade: `b` is a property of winners, and
`Γ(bŜ)` reuses `GamePerf.maxWinProb` at the same concrete winning predicate `winsDDS` (Def 3.23) over
the smaller set of winners. The sharpening of Theorem 4.17 (`∆(S,T) ≤ Γ(bŜ)`) is built on top.
-/

namespace RandomSystems.CR18

open RandomSystems (Dist)
open Classical
open scoped RandomSystems.CR18.CondEquiv

universe u v

variable {X : Type u} {Y : Type v}

/-! ## CR18 Definition 4.20 — `b` as blindness of a winner -/

/-- **CR18 Definition 4.20 (winner level)**: a winner `w` is **blind** — the converter `b` has been
applied, blocking the replies `Yᵢ` — when its query depends only on the *number* of replies seen, never
on their values. Equivalently `w` is **non-adaptive**: the queries `x₁,…,xq` are chosen in advance,
independent of the reply history (`p^W_{Xᵢ|Xⁱ⁻¹}`, not `p^W_{Xᵢ|Xⁱ⁻¹Yⁱ⁻¹}`). A `Prop` on the winner
function, not a structure. -/
def IsBlind (w : PFunDDS.Winner X Y) : Prop :=
  ∀ l₁ l₂ : List (Option Y), l₁.length = l₂.length → w l₁ = w l₂

/-- **`bŜ` at the probabilistic level**: a game-winner distribution `W` is blind when every winner in
its support is blind (`b` blocks the replies of each realization). This is the set of winners over which
`Γ(bŜ)` is the supremum. -/
def IsBlindDist (W : Dist (PFunDDS.Winner X Y)) : Prop :=
  ∀ w ∈ W.support, IsBlind w

/-! ## CR18 Definition 4.17 / 4.20 — `Γ(bŜ)`, the non-adaptive maximal winning probability -/

/-- **CR18 Definition 4.20 + 4.17 — `Γ(bŜ)`**: the maximal winning probability of the game `Ŝ` over
**blind** (non-adaptive) winner distributions only. The blind/non-adaptive analogue of `Γ(Ŝ)`
(`maxWinProb`, Def 4.17): the same concrete winning probability `winProb · Ŝ` (`winsDDS`, Def 3.23),
the same supremum, but over the smaller set `{W | IsBlindDist W ∧ W.isProbDist}` — "the best probability
in winning a game `S` non-adaptively." -/
noncomputable def blindMaxWinProb (Shat : PFunPDS X (Y × Bool)) : NNReal :=
  sSup ((fun W : Dist (PFunDDS.Winner X Y) => winProb W Shat)
    '' {W | IsBlindDist W ∧ W.isProbDist})

@[inherit_doc blindMaxWinProb] scoped notation "Γᵇ" => blindMaxWinProb

/-- The defining set of `Γ(bŜ)` is bounded above (by `Ŝ.weight`, as for `Γ`), so `Γ(bŜ)` is a genuine
least upper bound, not a junk `sSup`. -/
theorem bddAbove_blindWinProb_image (Shat : PFunPDS X (Y × Bool)) :
    BddAbove ((fun W : Dist (PFunDDS.Winner X Y) => winProb W Shat)
      '' {W | IsBlindDist W ∧ W.isProbDist}) := by
  refine ⟨Shat.weight, ?_⟩
  rintro x ⟨W, ⟨_, hW⟩, rfl⟩
  exact GamePerf.winProb_le_weight winsDDS W Shat hW

/-- **`Ŝ(W) ≤ Γ(bŜ)`** for a blind probability-distribution winner `W`: its winning probability is a
lower bound on the non-adaptive maximum. -/
theorem winProb_le_blindMaxWinProb (W : Dist (PFunDDS.Winner X Y)) (Shat : PFunPDS X (Y × Bool))
    (hblind : IsBlindDist W) (hW : W.isProbDist) : winProb W Shat ≤ Γᵇ Shat :=
  le_csSup (bddAbove_blindWinProb_image Shat) ⟨W, ⟨hblind, hW⟩, rfl⟩

/-- **CR18 §4.11.2 — `Γ(bŜ) ≤ Γ(Ŝ)`**: "the best probability in winning a game `S` non-adaptively
(i.e. `Γ(bS)`) is generally lower than the best probability in winning it adaptively (i.e. `Γ(S)`)."
*Trivial*: the blind winners are a subset of all winners, so the smaller supremum is `≤` the larger
(`winProb_le_maxWinProb` on each blind winner bounds the `Γᵇ`-defining set by `Γ`). -/
theorem blindMaxWinProb_le_maxWinProb (Shat : PFunPDS X (Y × Bool)) : Γᵇ Shat ≤ Γ Shat := by
  -- every blind winner's probability is `≤ Γ(Ŝ)` (it is a winner at all); `csSup_le'` then bounds the
  -- supremum over the smaller (possibly empty) set — no nonemptiness needed for `NNReal`.
  refine csSup_le' ?_
  rintro x ⟨W, ⟨_, hW⟩, rfl⟩
  exact winProb_le_maxWinProb W Shat hW

/-! ## CR18 §4.11.2 — the non-adaptive sharpening of Theorem 4.17

The PDF's headline conclusion `∆(S,T) ≤ Γ(bŜ)` is the **non-adaptive** bound. Its proof (eq. 4.39/4.40)
absorbs the copying converter `T̃` (Def 4.21) into the winner, turning the adaptive distinguisher `D`
into the **blind** game winner `D·T̃` for `bŜ`. The blindness is the load-bearing fact: `T̃` ignores the
right-interface replies, so the resulting winner's queries do not depend on the game's `Y`-outputs.

We make this precise at the **winner level**: a distinguisher `D` is *non-adaptive* (`b` applies) when
its query/verdict depends only on the number of replies seen. For such a `D`, the winner `ddToDDE D`
that the Theorem-4.17 chain plays against `Ŝ` is itself blind (`IsBlind`), so the existing bound
`Ŝ(D) ≤ Γ(Ŝ)` (`winProb_le_maxWinProb`) sharpens to `Ŝ(D) ≤ Γ(bŜ)` (`winProb_le_blindMaxWinProb`),
giving the non-adaptive `∆^D(S,T) ≤ Γ(bŜ)`. -/

/-- **CR18 Definition 4.20 (distinguisher level)** — a distinguisher `D` is **non-adaptive (blind)** when
its **query schedule** depends only on the *number* of replies seen, never on their values: the queries
`x₁,…,xq` are chosen in advance. The distinguisher analogue of `IsBlind`, stated as exactly what the
chain consumes — `ddToDDE d` (the query-issuing view, Def 3.24) is a blind winner. Stating it on the
query view (rather than full `d.val`) is the **weakest faithful** form: Maurer's non-adaptivity is about
the query schedule, and `winsDDS` reads the game's MBO, *not* `D`'s verdict (which `ddToDDE` discards),
so a reply-dependent verdict does not break non-adaptivity. -/
def IsBlindDDD (d : PFunDDS.DDD X Y) : Prop :=
  IsBlind (PFunDDS.ddToDDE d)

/-- The winner-image `ddToDDE d` of a non-adaptive distinguisher is a blind winner — by definition. -/
theorem isBlind_ddToDDE {d : PFunDDS.DDD X Y} (hd : IsBlindDDD d) : IsBlind (PFunDDS.ddToDDE d) := hd

/-- The winner distribution `fTransform ddToDDE D` is blind-supported whenever every distinguisher in
`D`'s support is non-adaptive — so it is admissible in the `Γ(bŜ)` supremum. -/
theorem isBlindDist_fTransform_ddToDDE (D : Dist (PFunDDS.DDD X Y))
    (hD : ∀ d ∈ D.support, IsBlindDDD d) :
    IsBlindDist (Dist.fTransform PFunDDS.ddToDDE D) := by
  intro w hw
  obtain ⟨d, hd, rfl⟩ := mem_support_fTransform _ _ hw
  exact isBlind_ddToDDE (hD d hd)

/-- **CR18 Theorem 4.17, non-adaptive sharpening (per blind distinguisher) — ABSTRACT HELPER, not the
paper endpoint (MODELING_REVIEW #2, fix F1.2).** For a **non-adaptive (blind)** distinguisher `D`, the
distinguishing advantage between `S = Ŝ⁻` and `T` is bounded by the *non-adaptive* maximal game-winning
probability `Γ(bŜ)`. The proof is the existing Theorem-4.17 chain (`theorem_4_17_mass_abstract`, via
`gameEnhance`), whose winner `fTransform ddToDDE D` is blind-supported (`isBlindDist_fTransform_ddToDDE`),
so its winning probability is bounded by `Γ(bŜ)` (`winProb_le_blindMaxWinProb`).

This is a **free-`Ŝ` abstract helper**, kept (proof unchanged) only as an early version of the blind
bound — it is *not* a faithful CR18 endpoint, for two reasons the cardinal rule forbids: it takes the
derived game `Shat` as an input with property hypotheses (`hCE`/`hmono`), and it **assumes** the
distinguisher is blind (`hblind`). The paper's all-`D` Theorem 4.17 *derives* blindness by absorption
through the copying converter `T̃` ("the claim `∆(S,T) ≤ Γ(bŜ)` trivially follows since `DT̃` is a game
winner for any choice of `D`", CR18_LN.txt:5694), and constructs `Ŝ := gameOf S cond` from a base `S`.

* The `hblind`-free, base-object public theorem is `RandomSystems.CR18.theorem_4_17` (GameOf.lean), which
  derives blindness via the absorbed winner (`theorem_4_17_condEquiv_absorbed_abstract`, BlindAbsorption.lean).
* This helper retains `hblind`-on-`D` only to record the sharpening for the already-non-adaptive case. -/
theorem theorem_4_17_condEquiv_blind_abstract
    (D : Dist (PFunDDS.DDD X Y)) (Shat : PFunPDS X (Y × Bool))
    (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) (hD : D.isProbDist)
    (hblind : ∀ d ∈ D.support, IsBlindDDD d) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ) ≤ (Γᵇ Shat : ℝ) := by
  have hEq : MassYAfalseEq Shat (gameEnhance T Shat) :=
    fun j ys xs => (massYAfalse_gameEnhance_eq_abstract T Shat hCE hT hTtot hmono j ys xs).symm
  -- Lemma 4.16 (mass form) bounds the advantage by the *winning probability* of `D`-as-winner against
  -- `Ŝ` (not yet taking the supremum) — keeping the concrete winner so we can use its blindness.
  have key := lemma_4_16'_mass_abstract D Shat (gameEnhance T Shat) i hShat
    (gameEnhance_isProbDist T Shat hT hShat) hEq hQ
    (TotalUpTo_of_totalOnNonempty hStot (i + 1))
    (gameEnhance_totalUpTo T Shat (i + 1) (TotalUpTo_of_totalOnNonempty hTtot (i + 1))
      (TotalUpTo_of_totalOnNonempty hStot (i + 1)))
  rw [ignoreMBO_gameEnhance T Shat hShat hStot] at key
  -- the winner `fTransform ddToDDE D` is blind, so its winning probability is `≤ Γ(bŜ)`.
  refine key.trans ?_
  have hD' : (Dist.fTransform PFunDDS.ddToDDE D).isProbDist := by
    exact Dist.fTransform_isProbDist PFunDDS.ddToDDE hD
  have hbound : winProb (Dist.fTransform PFunDDS.ddToDDE D) Shat ≤ Γᵇ Shat :=
    winProb_le_blindMaxWinProb (Dist.fTransform PFunDDS.ddToDDE D) Shat
      (isBlindDist_fTransform_ddToDDE D hblind) hD'
  exact_mod_cast hbound

/-- **CR18 Theorem 4.17, non-adaptive, per-winner form — ABSTRACT HELPER (MODELING_REVIEW #2, fix
F1.2).** Same hypotheses as `theorem_4_17_condEquiv_blind_abstract`, but the conclusion stops at the
*specific* `q`-query winner's winning probability `Ŝ(D) = winProb (fTransform ddToDDE D) Ŝ`, **before**
the `Γ(bŜ)` supremum. This is the shape §4.11.3 needs (the switching bound is the collision probability
of a winner making exactly `q+1` queries, not the unfiltered-`Γᵇ` supremum, which `≈ 1`).

Free-`Ŝ` abstract helper, **not** the paper endpoint: it takes `Shat` with `hCE`/`hmono`. The faithful,
base-object, blindness-deriving per-winner endpoint is `theorem_4_17_condEquiv_absorbed_winProb_abstract`
(BlindAbsorption.lean), routed by the public `RandomSystems.CR18.theorem_4_17` (GameOf.lean). Kept (proof
unchanged) as an early version. -/
theorem theorem_4_17_condEquiv_blind_winProb_abstract (D : Dist (PFunDDS.DDD X Y))
    (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y) (i : ℕ)
    (hShat : Shat.isProbDist) (hT : T.isProbDist) (hCE : Shat |≡ T) (hmono : MonotoneMBO Shat)
    (hStot : CondEquiv.TotalOnNonempty Shat) (hTtot : CondEquiv.TotalOnNonempty T)
    (hQ : ∀ d ∈ D.support, QueriesExactly (PFunDDS.ddToDDE d) (i + 1)) :
    (advantage D (PFunPDS.ignoreMBO Shat) T : ℝ)
      ≤ (winProb (Dist.fTransform PFunDDS.ddToDDE D) Shat : ℝ) := by
  have hEq : MassYAfalseEq Shat (gameEnhance T Shat) :=
    fun j ys xs => (massYAfalse_gameEnhance_eq_abstract T Shat hCE hT hTtot hmono j ys xs).symm
  have key := lemma_4_16'_mass_abstract D Shat (gameEnhance T Shat) i hShat
    (gameEnhance_isProbDist T Shat hT hShat) hEq hQ
    (TotalUpTo_of_totalOnNonempty hStot (i + 1))
    (gameEnhance_totalUpTo T Shat (i + 1) (TotalUpTo_of_totalOnNonempty hTtot (i + 1))
      (TotalUpTo_of_totalOnNonempty hStot (i + 1)))
  rwa [ignoreMBO_gameEnhance T Shat hShat hStot] at key

end RandomSystems.CR18
