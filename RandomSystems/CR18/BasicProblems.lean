/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18.AbstractProblem
import RandomSystems.Dist
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# CR18 §4.5.1 — Games and Multi-games (Definition 4.5)

Verbatim (anti-drift anchor):

> To instantiate the concept of a game, we consider a setting with a set `G` of (deterministic)
> games and a set `W` of (deterministic) winners, and a function `ω : W × G → {0,1}`, where
> `ω(w,g) = 1` is interpreted as `w` winning game `g`.¹⁹
>
> **Definition 4.5.** A game `G` is a `G`-valued random variable over `G`, a winner `W` is a
> `W`-valued random variable,²⁰ the performance set is `Ω = [0,1]`, and the performance of `W` for
> game `G` is the winning probability, i.e. `Ĝ(W) := Pr_{W,G}[ω(W,G) = 1]`.
>
> **Multi-games.** A more general setting is when a game consists of several (say `k`) subgames,
> i.e. when there are `k` functions `ω₁,…,ωₖ` with `ωᵢ : W × G → {0,1}`, where `ωᵢ(w,g) = 1` is
> interpreted as `w` winning the `i`-th subgame of `g`. Such a game is called a multi-game.²¹
>
> ¹⁹ `G` and `W` are understood as arbitrary (abstract) sets, not necessarily discrete systems.
> ²⁰ That is, the solver set `Σ` is the set of `W`-valued random variables.
> ²¹ We often use the same symbol `g`/`G` for a game or a multi-game.

## Modeling (tight — everything is a function)

* The winning condition `ω : W × G → Bool` is a **function**.
* A game / winner is a **random variable** — a `Dist` (the law of the RV).
* The performance is the **winning probability** `Pr_{W,G}[ω(W,G)=1]`, which the `Dist` API gives
  in one line: the independent joint `Dist.prod winner game` and the event mass `Dist.mass`.

**Generality (fn 19/20) — note this.** `G` and `W` are *arbitrary types* `{G W : Type*}` — the
§4.5.1 game is far more general than §3.7's concrete `PFunDDS.DDG`/`Winner` (instantiate `G`/`W`
with anything). A game is then a Def-4.2 `Problem` whose **solver set is the winner-RVs `Dist W`**
(fn 20) and whose performance set is `[0,1] ⊆ NNReal`. A multi-game is just a *family* of winning
conditions (fn 21).
-/

namespace RandomSystems.CR18

noncomputable section

variable {G W : Type*}

/-- §4.5.1 / Def 4.5: the **winning probability** `Ĝ(W) = Pr_{W,G}[ω(W,G)=1]` — the probability,
under the independent product of the winner-RV `winner` and the game-RV `game`, that the winning
function `ω` holds. -/
def winProb (ω : W × G → Bool) (game : Dist G) (winner : Dist W) : NNReal :=
  (Dist.prod winner game).mass (fun p => ω p = true)

/-- §4.5.1: a winning probability is at most `1` when the game and winner are genuine probability
distributions (their independent product is then a probability distribution). No `Fintype` on
`G`/`W` — `Dist.weight_prod`/`prod_isProbDist` are support-based. -/
theorem winProb_le_one (ω : W × G → Bool) {game : Dist G} {winner : Dist W}
    (hg : game.isProbDist) (hw : winner.isProbDist) : winProb ω game winner ≤ 1 := by
  rw [winProb]; exact Dist.mass_le_one (Dist.prod_isProbDist winner game hw hg) _

/-- §4.5.1 / Def 4.5: a **game is a Def-4.2 problem**. The problem object is the game-RV `Dist G`,
the solver set is the winner-RVs `Dist W` (fn 20), the performance set is `[0,1] ⊆ NNReal`, and the
performance is the winning probability `winProb ω`. (`G`, `W` are arbitrary — fn 19; `ω` is data, so
this is a problem-valued function of `ω`, not a global instance.) -/
@[reducible] def gameProblem (ω : W × G → Bool) : Problem (Dist G) (Dist W) NNReal where
  perf := winProb ω

/-- §4.5.1: a **multi-game** with `k = |ι|` subgames is a *family* `ω : ι → (W × G → Bool)` of
winning conditions (fn 21). The `i`-th subgame's performance is `winProb (ω i)`; combining the
subgames (`g∨`, `g∧`) is Definition 4.6. -/
def MultiGame (ι G W : Type*) : Type _ := ι → (W × G → Bool)

variable {ι : Type*}

/-- CR18 **Definition 4.6**: for a multi-game `mg` with `k = |ι|` subgames, the **OR-game** `g∨` is
the single game of winning **at least one** subgame — `ω(w, g∨) = ⋁ᵢ ωᵢ(w,g)`. The result is again
a single game `W × G → Bool` (hence `gameProblem (orGame mg)`). -/
def orGame [Fintype ι] (mg : MultiGame ι G W) : W × G → Bool :=
  fun p => decide (∃ i, mg i p = true)

/-- CR18 **Definition 4.6**: the **AND-game** `g∧` is the single game of winning **all** subgames —
`ω(w, g∧) = ⋀ᵢ ωᵢ(w,g)`. Again a single game `W × G → Bool`. -/
def andGame [Fintype ι] (mg : MultiGame ι G W) : W × G → Bool :=
  fun p => decide (∀ i, mg i p = true)

/-- `g∨` is won iff at least one subgame is won. -/
@[simp] theorem orGame_eq_true [Fintype ι] (mg : MultiGame ι G W) (p : W × G) :
    orGame mg p = true ↔ ∃ i, mg i p = true := by simp [orGame]

/-- `g∧` is won iff every subgame is won. -/
@[simp] theorem andGame_eq_true [Fintype ι] (mg : MultiGame ι G W) (p : W × G) :
    andGame mg p = true ↔ ∀ i, mg i p = true := by simp [andGame]

/-- Notation `g⋁` for the **OR-game** `g∨` (`orGame`) — a non-clashing close variant of the paper's
`g∨` (`∨` is Lean's `Or`); the big vee reads literally as "OR of the subgames". -/
scoped postfix:max "⋁" => orGame

/-- Notation `g⋀` for the **AND-game** `g∧` (`andGame`) — close variant of the paper's `g∧`
(`∧` is Lean's `And`); the big wedge reads literally as "AND of the subgames". -/
scoped postfix:max "⋀" => andGame

example [Fintype ι] (mg : MultiGame ι G W) (p : W × G) :
    (mg⋁ p = true ↔ ∃ i, mg i p = true) ∧ (mg⋀ p = true ↔ ∀ i, mg i p = true) :=
  ⟨orGame_eq_true mg p, andGame_eq_true mg p⟩

/-! ## CR18 §4.5.2 — Distinction Problems (Definition 4.7) — verbatim (anti-drift anchor)

> To instantiate the concept of a distinction problem … we consider a setting with a set `O` of
> objects, a set `D` of (deterministic) distinguishers, and a function `κ : D × O → {0,1}`.
>
> **Definition 4.7.** A distinction problem is a pair `(S0, S1)` of `O`-valued random variables (or,
> more precisely, distributions), and will be denoted as `⟨S0 | S1⟩`. A distinguisher `D` is a
> `D`-valued random variable, and the performance of `D` for distinction problem `⟨S0 | S1⟩` is
> `⟨S0|S1⟩(D) := Δ_D(S0,S1) = Pr_{D,S1}[κ(D,S1)=1] − Pr_{D,S0}[κ(D,S0)=1]`. Moreover
> `⟨S0|Sk⟩ = sum(⟨S0|S1⟩, …, ⟨Sk−1|Sk⟩)`  (4.6).

Modeling — the exact mirror of §4.5.1 games, and just as short: `κ : D × O → Bool` is a function;
objects/distinguishers are `Dist`s; the advantage **reuses** the §4.5.1 winning probability
`winProb κ S dist = Pr_{D,S}[κ=1]`, so `Δ_D = winProb S1 − winProb S0` (signed, `[−1,1] ⊆ ℝ`).
**Generality:** `O`, `D` are arbitrary types; the solver set is the distinguisher-RVs `Dist D`,
exactly as winners are the solvers for games. -/

variable {O D : Type*}

/-- §4.5.2 / Def 4.7: the **distinguishing advantage** `Δ_D(S0,S1) = Pr_{D,S1}[κ=1] − Pr_{D,S0}[κ=1]`
— the performance of distinguisher `dist` for `⟨S0|S1⟩`. Reuses §4.5.1's `winProb` (the winning
probability `Pr_{D,S}[κ=1]`); signed, in `[−1,1] ⊆ ℝ`. -/
def distAdv (κ : D × O → Bool) (S0 S1 : Dist O) (dist : Dist D) : ℝ :=
  (winProb κ S1 dist : ℝ) - (winProb κ S0 dist : ℝ)

/-- §4.5.2 / Def 4.7: a **distinction problem** `⟨S0|S1⟩` (a pair of object-RVs) is a Def-4.2 problem
— problem object the pair `Dist O × Dist O`, solver set the distinguisher-RVs `Dist D`, performance
set `[−1,1] ⊆ ℝ`, performance the advantage `distAdv`. (`O`, `D` arbitrary.) -/
@[reducible] def distinctionProblem (κ : D × O → Bool) : Problem (Dist O × Dist O) (Dist D) ℝ where
  perf := fun (S0, S1) dist => distAdv κ S0 S1 dist

/-- §4.5.2 notation: `⟨S0 | S1⟩` denotes the **distinction problem** — the pair `(S0, S1)` of
object-RVs (Def 4.7). -/
scoped notation:max "⟨" S0 " | " S1 "⟩" => (S0, S1)

/-- The `⟨S0 | S1⟩` notation is the problem object of `distinctionProblem`, with the advantage as
performance. -/
example (κ : D × O → Bool) (S0 S1 : Dist O) (dist : Dist D) :
    (distinctionProblem κ).perf ⟨S0 | S1⟩ dist = distAdv κ S0 S1 dist := rfl

/-- §4.5.2 (4.6): the advantage **telescopes** — `⟨S0|Sk⟩(D) = ∑ᵢ ⟨Sᵢ₋₁|Sᵢ⟩(D)`, i.e.
`Δ_D(S0,Sk) = ∑_{i<k} Δ_D(Sᵢ,Sᵢ₊₁)` for a sequence `S : ℕ → Dist O` (the hybrid sum). -/
theorem distAdv_telescope (κ : D × O → Bool) (S : ℕ → Dist O) (dist : Dist D) (k : ℕ) :
    distAdv κ (S 0) (S k) dist = ∑ i ∈ Finset.range k, distAdv κ (S i) (S (i + 1)) dist := by
  simp only [distAdv]
  exact (Finset.sum_range_sub (fun i => (winProb κ (S i) dist : ℝ)) k).symm

/-- §4.5.2: `d'` **complements** `d` — it outputs the negated bit on every object,
`κ(d', s) = κ(d, s) ⊕ 1 = !(κ(d, s))` for all `s`. -/
def Complements (κ : D × O → Bool) (d' d : D) : Prop :=
  ∀ s, κ (d', s) = !(κ (d, s))

/-- §4.5.2: a distinguisher class `D'` is **closed under complementing the output bit** if for
every `d ∈ D'` there is a `d' ∈ D'` complementing it (`κ(d', s) = κ(d, s) ⊕ 1`). This is the setup
for Lemma 4.7: with it the advantage flips sign — `Δ_{d'}(S0,S1) = −Δ_d(S0,S1)` — so the class
advantage `Δ_{D'} = sup_{D∈D'} Δ_D` is symmetric (and `Δ_{D'}` is a pseudo-metric). -/
def ComplementClosed (κ : D × O → Bool) (D' : Set D) : Prop :=
  ∀ d ∈ D', ∃ d' ∈ D', Complements κ d' d

/-! ### CR18 Lemma 4.7 — `Δ_{D'}` is a pseudo-metric when `D'` is complement-closed -/

/-- §4.5.2 / Lemma 4.7: the advantage of a single (deterministic) distinguisher `d` for `⟨S0|S1⟩`,
`Δ_d(S0,S1) = Pr_{S1}[κ(d,·)=1] − Pr_{S0}[κ(d,·)=1]` (the deterministic case of `distAdv`). -/
def detAdv (κ : D × O → Bool) (S0 S1 : Dist.ProbDist O) (d : D) : ℝ :=
  (S1.val.mass (fun s => κ (d, s) = true) : ℝ) - (S0.val.mass (fun s => κ (d, s) = true) : ℝ)

@[simp] theorem detAdv_self (κ : D × O → Bool) (S : Dist.ProbDist O) (d : D) :
    detAdv κ S S d = 0 := by simp [detAdv]

/-- The advantage telescopes per distinguisher: `Δ_d(S0,S2) = Δ_d(S0,S1) + Δ_d(S1,S2)`. -/
theorem detAdv_add (κ : D × O → Bool) (S0 S1 S2 : Dist.ProbDist O) (d : D) :
    detAdv κ S0 S2 d = detAdv κ S0 S1 d + detAdv κ S1 S2 d := by
  simp only [detAdv]; ring

/-- The complement sign-flip: complementing the distinguisher negates the advantage —
`Δ_{d'}(S0,S1) = −Δ_d(S0,S1)`. (Uses that the objects are probability distributions.) -/
theorem detAdv_complement {κ : D × O → Bool} {d' d : D} (h : Complements κ d' d)
    (S0 S1 : Dist.ProbDist O) : detAdv κ S0 S1 d' = - detAdv κ S0 S1 d := by
  have key : ∀ S : Dist.ProbDist O,
      (S.val.mass (fun s => κ (d', s) = true) : ℝ)
        = 1 - (S.val.mass (fun s => κ (d, s) = true) : ℝ) := by
    intro S
    have heq : S.val.mass (fun s => κ (d', s) = true) = S.val.mass (fun s => ¬ (κ (d, s) = true)) :=
      S.val.mass_congr fun s => by rw [h s]; simp
    have hsum := Dist.mass_add_compl S.val (fun s => κ (d, s) = true)
    have hcast : (S.val.mass (fun s => κ (d, s) = true) : ℝ)
        + (S.val.mass (fun s => ¬ (κ (d, s) = true)) : ℝ) = 1 := by
      rw [← NNReal.coe_add, hsum, (S.property : S.val.weight = 1)]; simp
    rw [heq]; linarith
  unfold detAdv; rw [key S0, key S1]; ring

/-- The advantage is antisymmetric in the two objects: `Δ_d(S1,S0) = −Δ_d(S0,S1)`. -/
theorem detAdv_swap (κ : D × O → Bool) (S0 S1 : Dist.ProbDist O) (d : D) :
    detAdv κ S1 S0 d = - detAdv κ S0 S1 d := by simp only [detAdv]; ring

/-- A single distinguisher's advantage never exceeds `1` (the objects are probability
distributions, so each mass lies in `[0,1]`). -/
theorem detAdv_le_one (κ : D × O → Bool) (S0 S1 : Dist.ProbDist O) (d : D) :
    detAdv κ S0 S1 d ≤ 1 := by
  have h1 : (S1.val.mass (fun s => κ (d, s) = true) : ℝ) ≤ 1 := by
    exact_mod_cast Dist.mass_le_one S1.property (fun s => κ (d, s) = true)
  have h0 : (0 : ℝ) ≤ (S0.val.mass (fun s => κ (d, s) = true) : ℝ) := NNReal.coe_nonneg _
  simp only [detAdv]; linarith

/-- §4.5.2 / Lemma 4.7: the **class advantage** `Δ_{D'}(S0,S1) = sup_{d ∈ D'} Δ_d(S0,S1)`. -/
def classAdv (κ : D × O → Bool) (D' : Set D) (S0 S1 : Dist.ProbDist O) : ℝ :=
  sSup ((fun d => detAdv κ S0 S1 d) '' D')

theorem bddAbove_detAdv (κ : D × O → Bool) (D' : Set D) (S0 S1 : Dist.ProbDist O) :
    BddAbove ((fun d => detAdv κ S0 S1 d) '' D') :=
  ⟨1, by rintro x ⟨d, _, rfl⟩; exact detAdv_le_one κ S0 S1 d⟩

/-- Pseudo-metric property 1 (fn 23): `Δ_{D'}(S,S) = 0`. -/
theorem classAdv_self (κ : D × O → Bool) (D' : Set D) (hne : D'.Nonempty)
    (S : Dist.ProbDist O) : classAdv κ D' S S = 0 := by
  have himg : (fun d => detAdv κ S S d) '' D' = {0} := by
    rw [Set.eq_singleton_iff_nonempty_unique_mem]
    exact ⟨hne.image _, by rintro x ⟨d, _, rfl⟩; exact detAdv_self κ S d⟩
  rw [classAdv, himg, csSup_singleton]

/-- Pseudo-metric property 2 (fn 23): symmetry `Δ_{D'}(S0,S1) = Δ_{D'}(S1,S0)`. This is where
complement-closure of `D'` is used — it makes the advantage set symmetric under negation. -/
theorem classAdv_comm {κ : D × O → Bool} {D' : Set D} (hcc : ComplementClosed κ D')
    (S0 S1 : Dist.ProbDist O) : classAdv κ D' S0 S1 = classAdv κ D' S1 S0 := by
  have himg : (fun d => detAdv κ S1 S0 d) '' D' = (fun d => detAdv κ S0 S1 d) '' D' := by
    refine Set.ext fun x => ⟨?_, ?_⟩
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨d', hd', hcomp⟩ := hcc d hd
      refine ⟨d', hd', ?_⟩
      show detAdv κ S0 S1 d' = detAdv κ S1 S0 d
      rw [detAdv_complement hcomp S0 S1]; exact (detAdv_swap κ S0 S1 d).symm
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨d', hd', hcomp⟩ := hcc d hd
      refine ⟨d', hd', ?_⟩
      show detAdv κ S1 S0 d' = detAdv κ S0 S1 d
      rw [detAdv_swap, detAdv_complement hcomp S0 S1, neg_neg]
  simp only [classAdv]; rw [himg]

/-- Pseudo-metric property 3 (fn 23): triangle inequality
`Δ_{D'}(S0,S2) ≤ Δ_{D'}(S0,S1) + Δ_{D'}(S1,S2)` (from per-distinguisher telescoping). -/
theorem classAdv_triangle {κ : D × O → Bool} {D' : Set D} (hne : D'.Nonempty)
    (S0 S1 S2 : Dist.ProbDist O) :
    classAdv κ D' S0 S2 ≤ classAdv κ D' S0 S1 + classAdv κ D' S1 S2 := by
  refine csSup_le (hne.image _) ?_
  rintro x ⟨d, hd, rfl⟩
  have h1 : detAdv κ S0 S1 d ≤ classAdv κ D' S0 S1 :=
    le_csSup (bddAbove_detAdv κ D' S0 S1) ⟨d, hd, rfl⟩
  have h2 : detAdv κ S1 S2 d ≤ classAdv κ D' S1 S2 :=
    le_csSup (bddAbove_detAdv κ D' S1 S2) ⟨d, hd, rfl⟩
  show detAdv κ S0 S2 d ≤ classAdv κ D' S0 S1 + classAdv κ D' S1 S2
  rw [detAdv_add κ S0 S1 S2 d]; linarith

/-- **CR18 Lemma 4.7** (Mathlib-native). When `D'` is nonempty and complement-closed, the class
advantage `Δ_{D'}` makes the objects `Dist.ProbDist O` a `PseudoMetricSpace` (fn 23). This is a
`def`, not an `instance` — the metric is parametrized by `κ`/`D'` — but it carries the whole Mathlib
pseudo-metric API onto `Δ_{D'}` (`dist_nonneg`, `dist_triangle4`, balls, …) once activated with
`letI`/`haveI`. The three structure fields are exactly the §4.5.2 lemmas; the remaining
`PseudoMetricSpace` data (`edist`, uniformity, bornology) take their canonical defaults. -/
@[reducible] def classAdvPseudoMetricSpace {κ : D × O → Bool} {D' : Set D}
    (hne : D'.Nonempty) (hcc : ComplementClosed κ D') : PseudoMetricSpace (Dist.ProbDist O) where
  dist := classAdv κ D'
  dist_self := classAdv_self κ D' hne
  dist_comm := classAdv_comm hcc
  dist_triangle := classAdv_triangle hne

/-- Reuse payoff: nonnegativity of `Δ_{D'}` is now *free* from the Mathlib pseudo-metric API
(`dist_nonneg`), with no bespoke proof. -/
theorem classAdv_nonneg {κ : D × O → Bool} {D' : Set D}
    (hne : D'.Nonempty) (hcc : ComplementClosed κ D') (S0 S1 : Dist.ProbDist O) :
    0 ≤ classAdv κ D' S0 S1 :=
  @dist_nonneg (Dist.ProbDist O) (classAdvPseudoMetricSpace hne hcc) S0 S1

/-! ## CR18 §4.5.3 — Bit-Guessing Problems (Definition 4.8) — verbatim (anti-drift anchor)

> To instantiate the concept of a bit-guessing problem … we again, as for distinction problems,
> consider a setting with a set `O` of objects, a set `D` of (deterministic) distinguishers, and a
> function `κ : D × O → {0,1}`.
>
> **Definition 4.8.** A bit-guessing problem is a pair, an `O × {0,1}`-valued random variable
> `(S, B)`, and is denoted as `[S; B]`. A distinguisher (or bit-guesser) `D` is a `D`-valued random
> variable, and the performance of `D` for bit-guessing problem `[S; B]` is
> `[S; B](D) := Λ_D(S,B) = 2·Pr_{D,S}[κ(D,S)=B] − 1`. The performance `[S;B](D)` is between `−1` and
> `1`, where performance `1` means `D`'s guess is correct with probability `1`, and `−1` means
> correct with probability `0`. We recall Lemmas 2.3/2.4: `[SU; U] = ⟨S0 | S1⟩` (4.7) (`U` an
> unbiased bit independent of everything) and `(S,B) = 2·⟨(S,B) | (S,U)⟩ρ` (4.8).

Modeling — again the §4.5.1 game/winner: the **third** instance after games (§4.5.1) and distinction
(§4.5.2). The winning function is "**guess correct**", `ω(d, (s,b)) = (κ(d,s) == b)` (a `Bool`, no `decide`:
both sides already are bits), so the success probability is *exactly* `winProb`; the performance is the affine rescaling `Λ = 2·winProb −
1` carrying `[0,1]` onto `[−1,1]`. **Faithfulness note:** `(S, B)` is a *single, possibly correlated*
`O × {0,1}`-valued RV — so it is one `Dist (O × Bool)`, *not* a pair of marginals (contrast
`⟨S0 | S1⟩`, which is genuinely two independent object-RVs). `[S; B]` is the paper's display name for
this joint RV. (4.7)/(4.8) are recalled Chapter-2 identities (Lemmas 2.3/2.4), not reproved here. -/

/-- §4.5.3 / Def 4.8: the **guess-correct** winning function — bit-guesser `d`'s guess `κ(d,s)`
matches the secret bit `b`. This is a §4.5.1 winning function `ω : D × (O × {0,1}) → Bool` (winners
`= D`, games `= O × {0,1}`), so bit-guessing is once more an abstract game. -/
def bitGuessWin (κ : D × O → Bool) : D × (O × Bool) → Bool :=
  fun (d, s, b) => κ (d, s) == b

/-- §4.5.3 / Def 4.8: the **bit-guessing advantage** `Λ_D(S,B) = 2·Pr_{D,S}[κ(D,S)=B] − 1` — the
performance of bit-guesser `dist` for `[S; B]`. The success probability `Pr[κ(D,S)=B]` is the §4.5.1
`winProb` of the guess-correct game, affinely rescaled from `[0,1]` to `[−1,1]`. -/
def bitGuessAdv (κ : D × O → Bool) (SB : Dist (O × Bool)) (dist : Dist D) : ℝ :=
  2 * (winProb (bitGuessWin κ) SB dist : ℝ) - 1

/-- §4.5.3 / Def 4.8: a **bit-guessing problem** `[S; B]` is a Def-4.2 problem — problem object the
joint RV `Dist (O × {0,1})`, solver set the bit-guesser-RVs `Dist D`, performance set `[−1,1] ⊆ ℝ`,
performance the advantage `bitGuessAdv`. (`O`, `D` arbitrary — fn 19/20.) -/
@[reducible] def bitGuessProblem (κ : D × O → Bool) : Problem (Dist (O × Bool)) (Dist D) ℝ where
  perf SB dist := bitGuessAdv κ SB dist

/-- §4.5.3: the bit-guessing performance is at most `1` (guess correct with probability `1`), when
`[S;B]` and the bit-guesser are genuine probability distributions. -/
theorem bitGuessAdv_le_one (κ : D × O → Bool) {SB : Dist (O × Bool)} {dist : Dist D}
    (hSB : SB.isProbDist) (hd : dist.isProbDist) : bitGuessAdv κ SB dist ≤ 1 := by
  have h : (winProb (bitGuessWin κ) SB dist : ℝ) ≤ 1 := by
    exact_mod_cast winProb_le_one (bitGuessWin κ) hSB hd
  simp only [bitGuessAdv]; linarith

/-- §4.5.3: the bit-guessing performance is at least `−1` (guess correct with probability `0`). -/
theorem neg_one_le_bitGuessAdv (κ : D × O → Bool) (SB : Dist (O × Bool)) (dist : Dist D) :
    -1 ≤ bitGuessAdv κ SB dist := by
  have h : (0 : ℝ) ≤ (winProb (bitGuessWin κ) SB dist : ℝ) := NNReal.coe_nonneg _
  simp only [bitGuessAdv]; linarith

end

end RandomSystems.CR18
