/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.CR18.Distance
import RandomSystems.CR18.DDS
import RandomSystems.CR18.PFunDDS
import RandomSystems.CR18.PFunConverter
import RandomSystems.CR18.PDS
import RandomSystems.CR18.DDE
import RandomSystems.CR18.HistMap
import RandomSystems.CR18.Converter
import RandomSystems.CR18.Behavior
import RandomSystems.CR18.Game
import RandomSystems.CR18.Indist
import RandomSystems.CR18.AUH
import RandomSystems.CR18.DistProd
import RandomSystems.CR18.AdvMetric
import RandomSystems.CR18.Monotonicity
import RandomSystems.CR18.SwitchingPort
import RandomSystems.CR18.DecisionProblem
import RandomSystems.CR18.SearchProblem
import RandomSystems.CR18.AbstractProblem
import RandomSystems.CR18.BasicProblems
-- `RandomSystems.CR18.Counterexamples` (Def 4.19 boundary witnesses + 4.19' non-vacuity)
-- is kept OUT of the default build — import it on demand.

/-!
# Maurer's Random Systems Theory (CR18)

Faithful Lean 4 formalization of Ueli Maurer's lecture notes
*"Cryptography: Random Systems"* (CR18).

This is a **parallel namespace** (`RandomSystems.CR18.*`) that develops
the CR18 theory directly from the source text, independently of the
existing `RandomSystems.*` development (which follows Lanzenberger–Maurer,
TCC 2020). Nothing here imports or modifies the existing modules, and the
existing modules do not depend on anything here.

## Scope

The formalization targets, in priority order:

* **Chapter 3** (full): discrete systems, random systems, equivalence,
  monotone conditions, the distinguishing problem.
* **Chapter 4**, §4.5 / §4.10 / §4.11.
* **Chapter 2**, §2.3.
* The VIL / URF material.

See `random-systems/design/CR18_FORMALIZATION_CHECKLIST.md` for the
item-by-item plan.

## Conventions

* Faithful modeling of discrete systems as **partial functions** (Def 3.2),
  with finite alphabets as the default instantiation.
* Each definition / lemma lands as its own submodule under
  `RandomSystems/CR18/`, and adds its `import` line below as it lands.
* Only build criterion: `lake build RandomSystems.CR18` compiles
  (`sorry` permitted; the existing build must never break).

## Submodules

* `DecisionProblem` — Chapter 4, §4.1.1 (decision problems; predicate `X → Prop`, witness form
  `P(x) := ∃w Q(x,w)`).
* `SearchProblem` — Chapter 4, §4.1.2 (search problems; Def 4.1 4-tuple `(X,W,Q,P_X)`, the
  underlying decision problem, function inversion `I_f`). Also the §4.4.3 bridge: a search problem
  is a Def-4.2 `Problem` (solvers `X → W`, performance = success probability `Pr_{P_X}[Q(x,f x)]`).
* `AbstractProblem` — Chapter 4, §4.4 thread. §4.4.2 Preliminaries (function notation, pinned to
  existing Lean infra); §4.4.3 / Def 4.2: a problem object `p` *equipped with* a solver set, a
  performance set, and a performance function `p̂` — the typeclass `Problem P Solver Perf`
  (`Solver` `outParam`; `[PartialOrder Perf]` a standing class condition; `perf p = p̂`, `p ≠ p̂`);
  the `a`-solver notion; concrete problems (search, distinction, games)
  instantiate it. §4.4.4 Upper bounds: `p̂ ≤ᶜ ε` = Maurer's `p̂ ≤ ε` (`ε` the constant function,
  the §4.4.2 pointwise order); `le_const_iff`. §4.4.5 / Def 4.3 reduction: a τ-reduction is the
  reduction *function* (Def 4.3: "ρ is called a τ-reduction"), so `Reduction p q τ` is the subtype
  `{ ρ : Σp → Σq // τ ∘ p̄ ≤ q̄ ∘ ρ }` carved out by (4.1) (`CoeFun`, so `r s = ρ s`);
  `Reduction.spec`. §4.4.6 interpretations: `Reduction.upperBound` = ineq (4.3), the upper-bound
  reading `p̄ ≤ lam ∘ q̄ ∘ r` from a ≤-respecting `lam` with `id ≤ lam ∘ τ` (4.2);
  `reduction_iff_upperBound` = the (4.1) ⟺ (4.3) equivalence under equality in (4.2);
  `reduction_iff_upperBound_of_orderIso` = the `λ = τ⁻¹` (order-iso) case;
  `reduction_iff_upperBound_of_strictMono` = the concrete "`Ω_p,Ω_q` intervals of ℝ, `τ` strictly
  ≤-respecting" case (`StrictMono` + onto ⇒ order-iso). §4.4.7 complexity interpretation (tight,
  no theorems — the paper stops there): `complexityClass γ c = {s | γ s ≤ c}`, derived performance
  `derivedPerf` (`p'(c) = sup{p̄ s | s ∈ Σc}`), derived reduction `derivedReduction`
  (`ρ'(c) = sup{γ(ρ s) | s ∈ Σc}`). §4.4.8 composition (both theorems, one `le_trans` each): Lemma
  4.5 `reduction_comp` (two (4.1) reduction inequalities compose to a `(τ'∘τ)`-reduction, fn
  `ρ'∘ρ`); Lemma 4.6 `upperBound_comp` (two (4.3)-form bounds compose). §4.4.9 generalized
  reductions: a list of problems is a product problem (`instProblemPi : Problem (∀ i, P i)
  (∀ i, S i) (∀ i, Ω i)`, perf = the §4.4.2 direct product `perf_pi`), so (4.4)/(4.5) are basic
  `Reduction`/upper-bound at product problems and every reduction lemma applies unchanged; footnote
  18 = `Monotone` on the Pi order (`monotone_iff_forall_le`); `tupling` = the §4.4.2 `[ρ₁,…,ρₖ]`.
  §4.4.10 / Def 4.4 worst-case problems: `worstCasePerf ps s = ⨅ p ∈ ps, p̄ s` (the infimum / worst
  performance, dual of §4.4.7's sup), and a set of problems *is* its worst-case problem
  (`instProblemWorstCase : Problem (Set P) S Ω`). Notation: `p̄` =
  `Problem.perf p` (`scoped postfix "̄"`); shared binders via a `variable` block.
* `BasicProblems` — Chapter 4, §4.5. §4.5.1 / Def 4.5 games: `ω : W × G → Bool` (winning fn, `G`/`W`
  *arbitrary* sets — fn 19), a game/winner is a `Dist`, `winProb ω game winner = (winner ⊗
  game).mass {ω = 1}` the winning probability, `gameProblem ω : Problem (Dist G) (Dist W) NNReal`
  (solver = winner-RVs, fn 20); `MultiGame ι G W := ι → (W × G → Bool)` (a family of subgames). Def
  4.6: `orGame`/`andGame` = `g∨`/`g∧`, the OR/AND of the subgame winning fns (win at-least-one / all)
  — a single game again (`orGame_eq_true`/`andGame_eq_true`). §4.5.2 / Def 4.7 distinction problems:
  `κ : D × O → Bool`, advantage `distAdv κ S0 S1 dist = winProb κ S1 dist − winProb κ S0 dist`
  (reuses §4.5.1's `winProb`!), `distinctionProblem κ : Problem (Dist O × Dist O) (Dist D) ℝ`;
  (4.6) `distAdv_telescope` (the hybrid sum, via `Finset.sum_range_sub`); `Complements`/
  `ComplementClosed` (the complement-closed distinguisher class). Lemma 4.7: per-distinguisher
  advantage `detAdv κ S0 S1 d = Pr_{S1}[κ(d,·)=1] − Pr_{S0}[κ(d,·)=1]` (the deterministic case),
  with `detAdv_self`/`detAdv_add` (telescoping)/`detAdv_swap`/`detAdv_complement` (the sign-flip
  `Δ_{d'}=−Δ_d` under `Complements`, via `mass_add_compl`); class advantage `classAdv κ D' = sup_{d∈D'}
  detAdv` (a `sSup`). Lemma 4.7 lands as the **Mathlib-native** `classAdvPseudoMetricSpace` — when
  `D'` is nonempty and complement-closed, `Δ_{D'}` is a `PseudoMetricSpace (Dist.ProbDist O)` (fn 23;
  a parametrized `def`, not a global `instance`), whose three fields are `classAdv_self`
  (diagonal-zero), `classAdv_comm` (symmetry from complement-closure), `classAdv_triangle`
  (telescoping + `le_csSup`/`csSup_le` over the `bddAbove_detAdv` bound); the rest take canonical
  defaults. Payoff: `classAdv_nonneg` is then free via Mathlib's `dist_nonneg` (and the whole
  pseudo-metric API — balls, `dist_triangle4`, … — is reusable through `letI`). §4.5.3 / Def 4.8 bit-guessing problems (the **third** instance of the
  §4.5.1 game/winner, after games and distinction): the winning fn is "guess correct"
  `bitGuessWin κ (d,(s,b)) = (κ(d,s) == b)`, the performance `bitGuessAdv κ [S;B] D = 2·winProb
  − 1` is the affine `[0,1]→[−1,1]` rescaling of that game's `winProb`, and `bitGuessProblem κ :
  Problem (Dist (O × Bool)) (Dist D) ℝ`; `[S;B]` is a *single, possibly correlated* `O × {0,1}`-RV
  (`Dist (O × Bool)`), not a marginal pair (contrast `⟨S0|S1⟩`); `bitGuessAdv_le_one` /
  `neg_one_le_bitGuessAdv` give the fn-noted `[−1,1]` range ((4.7)/(4.8) are recalled Chapter-2
  identities, deferred). Upstreamed: `winProb_le_one` (a §4.5.1 game result) lives next to `winProb`;
  the generic mass facts `Dist.mass_add_compl`/`mass_le_weight`/`mass_le_one` now live in
  `RandomSystems.Dist` (their proper home). Notation:
  `⟨S0 | S1⟩` =
  the distinction problem `(S0, S1)` (`scoped`); `g⋁`/`g⋀` = `orGame`/`andGame` (the multi-game OR/AND
  — non-clashing close variants of the paper's `g∨`/`g∧`, since `∨`/`∧` are Lean's `Or`/`And`). (The
  §4.4.2 `(·)`/`[·]` combinators still collide with tuple/list syntax → `Prod.map`/`tupling`.)
* §4.7.1 / **Definition 4.9** (multiple independent instantiation) is the generic construction
  `Dist.iidPow` in `RandomSystems.Dist` (its home, beside the binary independent product
  `Dist.prod`): `X^q = Dist.iidPow X q : Dist (Fin q → A)`, the `q`-fold i.i.d. power, with
  `iidPow_apply` the defining product-mass `X^q(f) = ∏ i, X (f i)` (independence + identical
  marginals) and `iidPow_isProbDist`/`iidPow_weight` (`|X^q| = |X|^q`, so `X^q` is again a random
  variable). The countable power `⟨X⟩ = X^∞` of Def 4.9 is **deliberately omitted** — by footnote
  24 it is uncountable and leaves discrete probability, which this development excludes.
* §4.7.1 / **Definition 4.10** (cloning) is the companion `Dist.clonePow`: `X^[q] = Dist.clonePow X
  q`, the `q`-fold *clone* power — `q` fully-correlated clones `X₁ = ⋯ = X_q`, modeled as the
  pushforward (`fTransform`) of `X` along the diagonal `a ↦ (a,…,a)`. `clonePow_apply` shows it is
  supported on constant tuples (mass `X a` at the constant-`a` tuple, `0` otherwise — the "all
  equal" content), and `clonePow_weight`/`clonePow_isProbDist` (`|X^[q]| = |X|`) make it a random
  variable. Contrast `iidPow` (independent) — same marginal `X`, opposite correlation (Example
  4.11). Both reuse generic `Dist` machinery (`prod`-free pushforward / support product); neither
  needs `Fintype` on the carrier.
-/
