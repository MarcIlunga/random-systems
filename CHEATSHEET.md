# RandomSystems / CR18 / AbstractCrypto — Framework Reuse Index

**This is the project's REUSE INDEX, not just a reference.** Before you write *any* local helper
lemma or definition in a security proof, find it here first. If the fact you need is listed below,
**cite the framework name** — do not re-derive it, and do not mint a `gazi_*` / `hctr2_*` local copy
of something that already exists. Reviewers reject proofs that re-prove anything catalogued here.

Every entry cites the file where the name is defined (paths relative to the repo root; the
`RandomSystems/` prefix is dropped inside a category when unambiguous). All names were read from
source. Notation lives under [Notation & vocabulary](#0-notation--vocabulary).

---

## Contents

- [By goal — what are you trying to do?](#by-goal--what-are-you-trying-to-do)
- [REUSE THIS — do NOT re-derive](#reuse-this--do-not-re-derive)
- [0. Notation & vocabulary](#0-notation--vocabulary)
- [1. Distinguishing advantage `Δ` — triangle, telescope, symmetry](#1-distinguishing-advantage-δ--triangle-telescope-symmetry)
- [2. Systems & constructions](#2-systems--constructions)
- [3. DPI / converter monotonicity (query-budget accounting)](#3-dpi--converter-monotonicity-query-budget-accounting)
- [4. Switching lemma & birthday](#4-switching-lemma--birthday)
- [5. Condition-equivalence & the blind game (adaptive → nonadaptive)](#5-condition-equivalence--the-blind-game-adaptive--nonadaptive)
- [6. `Dist` facts](#6-dist-facts)
- [7. Custom tactics](#7-custom-tactics)
- [8. AbstractCrypto — indifferentiability (R3/R5 layer)](#8-abstractcrypto--indifferentiability-r3r5-layer)
- [9. H-technique (R4 ONLY — a SEPARATE route)](#9-h-technique-r4-only--a-separate-route)

---

## By goal — what are you trying to do?

| I want to… | Reach for | File |
| --- | --- | --- |
| Bound an **adaptive** advantage by a **nonadaptive collision game** (the general adaptive→nonadaptive tool) | `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv`, or the packaged `maxAdvantage_filterQueries_seededConditionCGame_le` / `…_seededHashThenURF_le` | `BlindAbsorption`, `SwitchingLemma` |
| Apply a converter/protocol to a resource | `PFunPDS.applyDDC (DDC.ofStep step) S` (or `α ·ᶜ s` at the deterministic level) | `ResourceView`, `StepConverter` |
| Model a keyed function as a system; ideal side | `ofFunDist Df` / `functionEvaluator f`; ideal = `PFunPDS.URF` (`𝖱`), permutation `PFunPDS.URP` (`𝖯`) | `PDS`, `PFunDDS` |
| Triangle / telescope / hop advantages | `maxAdvantage_triangle`, `maxAdvantage_le_adjacent_sum`, `advantage_telescope`, `maxAdvantage_three_hop_le` | `AbsorbDPI`, `Complexity/AdvantageSeq` |
| Query-budget a converter (DPI) | `maxAdvantage_filterQueries_applyDDC_le` (needs `DDC.AnswersWithin`); unbudgeted `maxAdvantage_applyDDC_le`; filter monotone `maxAdvantage_filterQueries_le` | `AbsorbDPI` |
| Birthday / collision bound | `bday` + `bday_mono`, `pairCollisionUnionBound` + `pairCollisionUnionBound_le_birthday`, `pcoll` + `pcoll_eq_one_sub_descFactorial_div` (closed form) + `pcoll_le_birthday_tight`/`pcoll_le_birthday`, `birthday_bound`; lower bound `min_le_pcoll` | `HTechnique/Derivation`, `SwitchingLemma`, `Counting` |
| URF↔URP switching | `urf_urp_switching`, or `URFURPSwitchingBound.of_finite` / `PRF.FunctionVsPermutation.bound` | `SwitchingLemma`, `Complexity/SwitchingBridge`, `Complexity/PRF` |
| Sum of two random permutations (XoP) vs URF | `sop_randomness_expander` (`Δ ≤ q²/\|G\|`, by condition C) | `SumOfPermutations` |
| Prove `Ŝ |≡ T` (condition C) from a first-collision predicate | `condEquiv_of_transcript_mass_reductions`; for the seed-hash instance `seededHashThenURF_condEquiv` | `SwitchingLemma` |
| State the headline CR18 Thm 4.17 (`Ŝ |≡ T → Δ ≤ Γᵇ`) | `maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf`, or `BlindTheorem417Hyp.bound` | `GameOf`, `Complexity/SwitchingBridge` |
| Bound `Δ` by a **win probability** (game) | `advantage_le_blindMaxWinProb_gameOf`, `advantage_le_blindMaxWinProb_of_condEquiv` | `GameOf`, `BlindAbsorption` |
| Compose ε-relaxed **constructions** (indifferentiability) | `Constructs.eball_trans`, `Indifferentiable.trans`, `Indifferentiable.construct` | `abstract-crypto` |
| Discharge Maurer's "standing" side conditions (game is total monotone-MBO prob system) | `cr18_standing` (register facts with `@[cr18_standing]`) | `CR18TacticsCore` |
| Compute a `Dist.mass` fibered sum to a closed form | `cr18_mass x` (expand→swap→collapse) | `CR18TacticsCore` |
| Char-2 / GF(2) XOR-cancellation arithmetic | `char2`, `char2_norm`, `char2_iff` | `HCTR2` |
| PRF/PRP security via the H-technique (R4) | `advPRF` / `advNPRF` / `advPRP`; endpoint `adv_le_of_extFixedQueryRep_eq_on_good` | `HTechnique/SecurityDefs`, `HTechnique/Derivation` |

---

## REUSE THIS — do NOT re-derive

These generic facts get re-spelled as local helpers constantly. Each has a canonical framework name;
use it.

- **Adjacent-sum / telescoping triangle inequality for advantages** — do not hand-roll a hybrid sum.
  Use `maxAdvantage_le_adjacent_sum` (`Δ(S₀,Sₙ) ≤ ∑ Δ(Sᵢ,Sᵢ₊₁)`), the exact identity
  `advantage_telescope`, or the ready 3-hop `maxAdvantage_three_hop_le` (`Complexity/AdvantageSeq.lean`).
- **Uniform random function restricted along an embedding is uniform** — `uniform_restrict`
  (`SwitchingLemma.lean`): `fTransform (fun F i => F (e i)) (uniform (J→O)) = uniform (I→O)`. Also
  `Dist.fTransform_equiv_uniform`, `Dist.fTransform_bijection_uniform`,
  `Dist.fTransform_uniform_eq_uniform_of_card_fiber_mul` for the fiber-count versions.
- **`Dist` product-map / marginalization** — `Dist.prod`, `Dist.prodProbDist`, `Dist.mass_prod_and`,
  `Dist.mass_prod_fst`, `Dist.mass_prod_snd`, `Dist.mass_prod_eq_double_sum` (`Dist.lean`), and the
  seed-integration combinators in `SwitchingLemma.lean`: `mass_prod_eq_sum_fiber` (Fubini — the general
  one), `mass_prod_congr_fiber` (fibers proportional by a constant: integrates a per-seed factorization
  over an independent component), `mass_prod_good_eq_mass_mul` (fiber constant on a good seed set).
- **statDist manipulations** — `statDist_triangle`, `statDist_le_weight`, `statDist_symm_of_eq_weight`,
  `statDist_fTransform_le` (data-processing), `statDist_fTransform_injective`, `statDist_partition`,
  and the whole `hTechnique_*` family (`hTechnique_eq_on_good`, `oneSided_hTechnique`, …) in
  `StatDist.lean`. Do not re-prove a bespoke total-variation bound.
- **Product-uniform evaluation** (drop an ignored independent coordinate) — `Dist.prod_uniform`,
  `Dist.fTransform_fst_uniform`, `Dist.fTransform_snd_uniform`, `Dist.fTransform_map_snd_prod_uniform`,
  `Dist.fTransform_eval_snd_prod_uniform`, `Dist.uniform_mass_eval` (`Dist.lean`). The hash-assignment
  fiber count is `uniform_hash_assignment_mass_eq` (`SwitchingLemma.lean`).
- **Birthday-cover principle** — do not re-index protocol events into `Fin q × Fin q` by hand. Use
  `mass_le_pairCollisionUnionBound_of_cover` / `…_of_cover_injOn` (`SwitchingLemma.lean`): supply a
  cover and a `≤ 1/|X|` leaf bound and get the pair-union bound.
- **Filter/strip bookkeeping** (`[q]`, `gameOf`, MBO projections) — never unfold by hand; the
  `cr18_filter` / `cr18_game` / `cr18_prob` / `cr18_pushforward` normalizers do it once. The whole
  `condEquiv_filterQueries`, `massAfalse_filterQueries`, `monotoneMBO_filterQueries` family lives in
  `CondEquiv.lean`.

---

## 0. Notation & vocabulary

The vocabulary is `scoped`, so `open`/`open scoped` the relevant namespace.

- `` Δ(S, T) `` and `` 〈S | T〉 `` (`Distinguishing.lean`) — both are `maxAdvantage S T`, the signed
  best-distinguisher advantage. They are *definitionally equal* (CR18 §4.11.3's overlined-angle form).
- `` ⌈q⌉ G `` (`PDS.lean`) — `PFunPDS.filterQueries q G`, the `q`-query-budgeted system.
- `` 𝖱 X `` / `` 𝖯 X `` (`SwitchingLemma.lean`) — `PFunPDS.URF (X:=X)(Y:=X)` and `PFunPDS.URP X`.
- `` Γ `` (`WinProb.lean`) — `maxWinProb`, the max game-winning probability.
- `` Γᵇ `` (`BlindConverter.lean`) — `blindMaxWinProb`, the *blind* (nonadaptive) max win probability.
- `` α ·ᶜ S `` (`PFunConverter.lean`) — `PFunConverter.DDC.apply α S` (deterministic converter apply).
- `` [q]ᶠ `` / `` ⟦q⟧ᶠ `` (`PFunConverter.lean`) — `PFunConverter.queryLimit q`, the query-limiting filter converter.
- `` S ⋆ₚ[op] T `` (`PFunConverter.lean`) — `combine op S T`; `` cascᶜ `` / `` comb⋆ᶜ[op] `` are the cascade/combine converters.
- `` b(S) `` / `` bᶜ(S) `` (`PDS.lean`) — `behavior S` / `cumulativeBehavior S` (Def 3.18 / 3.20).
- `` b⟦S⟧ `` / `` bₑ⟦E⟧ `` (`PDS.lean`) — `behaviorKernel` / `envBehaviorKernel` (conditional kernels).
- `` ℙ⟦X⟧ `` / `` ℙ⟦X ∣ Y⟧ `` (`Dist.lean`) — `Dist.PMF` / `Dist.condPMFOf` probability macros.
- `` S ≡ᵦ T `` (`PDS.lean`) — `BehaviorEq` (behavioral equivalence, an `Equivalence`).
- `` Ŝ |≡ T `` (`CondEquiv.lean`) — `CondEquiv Ŝ T` (CR18 Def 4.19 conditional equivalence).
- `` Adv[q](S, T) `` / `` Advᶜ[q](S, T) `` / `` Δ[q](S, T) `` (`HTechnique/Derivation.lean`) —
  adaptive / bounded-adaptive transcript advantage / law-δ (H-technique surface).
- `` δ(P, Q) `` / `` Pr[B ∣ P] `` / `` tr[q](S, E) `` / `` tr(S, xs) `` (`HTechnique/Derivation.lean`) —
  `statDist` / `probBad` / deterministic & fixed-query transcript distributions.
- `` ℛ —[π]→ 𝒮 `` (`abstract-crypto: Specifications/Basic.lean`) — `Constructs π ℛ 𝒮`.

---

## 1. Distinguishing advantage `Δ` — triangle, telescope, symmetry

- `` `maxAdvantage` `` / `` `advantage` `` (`Distinguishing.lean`) — `advantage D S T` is one
  distinguisher's signed advantage; `maxAdvantage S T = Δ(S,T)` is the sup over probabilistic
  distinguishers. The object every distinguishing bound targets.
- `` `advantage_le_maxAdvantage` `` (`Distinguishing.lean`) — `advantage D S T ≤ Δ(S,T)` for prob `D`.
  Reach for it to lift a single-distinguisher bound to the sup.
- `` `maxAdvantage_le_of_forall_advantage_le` `` (`Distinguishing.lean`) — the converse packaging:
  prove `∀ D, advantage D S T ≤ c` to conclude `Δ(S,T) ≤ c`. The standard `Δ`-bound entry point.
- `` `maxAdvantage_self_le_zero` `` (`Distinguishing.lean`) — `Δ(S,S) ≤ 0`.
- `` `maxAdvantage_triangle` `` (`AbsorbDPI.lean`) — `Δ(S,U) ≤ Δ(S,T) + Δ(T,U)`. The hop/hybrid workhorse.
- `` `maxAdvantage_le_adjacent_sum` `` (`Complexity/AdvantageSeq.lean`) — generalized triangle over a
  `SystemTrace`: `Δ(systems 0, systems n) ≤ ∑ i, Δ(systems i, systems (i+1))`.
- `` `advantage_telescope` `` (`Complexity/AdvantageSeq.lean`) — the *exact* per-distinguisher identity
  `advantage D (systems 0) (systems n) = ∑ advantage D (systems i) (systems (i+1))`.
- `` `maxAdvantage_three_hop_le` `` (`Complexity/AdvantageSeq.lean`) — from three local bounds
  `Δ(0,1)≤b0, Δ(1,2)≤b1, Δ(2,3)≤b2` concludes `Δ(0,3) ≤ b0+b1+b2`. Go-to for a standard 3-hybrid.
- `` `AdjacentMaxAdvantageBounded.traceBound` `` / `` `.threeHopBound` `` (`Complexity/AdvantageSeq.lean`) —
  turn per-hop `stepBound`s into the endpoint `Δ(systems 0, systems n) ≤ ∑ stepBound i`.
- `` `SystemTrace` `` / `` `adjacentMaxAdvantageSum` `` (`Complexity/AdvantageSeq.lean`) — the trace type
  (`Nat`-indexed PFun systems) and the RHS sum object of the telescoping inequality.
- `` `maxAdvantage_filterQueries_swap_le` `` / `` `maxAdvantage_filterQueries_comm` `` (`AbsorbDPI.lean`) —
  `Δ` symmetry at the filtered surface for weight-equal total systems (`edist_comm` analogue).

## 2. Systems & constructions

### Carriers and ideal objects (`PDS.lean` unless noted)
- `` `PFunPDS X Y` `` — a probabilistic discrete system as a `Dist (PFunDDS.DDS X Y)`; the central
  carrier type. `` `PFunPDS.Prob` `` (`ProbPDS`) is the probability-distribution refinement.
- `` `PFunPDS.filterQueries` `` (= `⌈q⌉`) — restrict a system to answer only its first `q` queries.
- `` `PFunPDS.ofFunDist` `` — build a system from a `Dist (X → Y)` (sample a function, evaluate it).
  The canonical "keyed function family as a random system" constructor.
- `` `PFunPDS.URF` `` / `` `PFunPDS.URP` `` (= `𝖱`/`𝖯`) — the uniform random function / permutation
  ideals. `` `PFunPDS.R` `` / `` `PFunPDS.P` `` are the `Fin (2^m)→Fin (2^n)` bit-width instances.
- `` `PFunPDS.ofPermDist` `` — system from a `Dist (Equiv.Perm X)`; `ofPermDist_eq_ofFunDist` bridges to `ofFunDist`.
- `` `IsRandomFunction` `` / `` `IsRandomPermutation` `` — the predicates; `URF_isRandomFunction`,
  `URP_isRandomFunction`, `P_isRandomPermutation`, `ofFunDist_isRandomFunction` supply instances.
- `` `PFunPDS.behavior` `` / `` `cumulativeBehavior` `` (= `b(S)`/`bᶜ(S)`) — Def 3.18 / 3.20 input-output
  behaviors; `cumulativeBehavior_eq_behavior_prod`, `behaviorOf_eq_cumulative_div` relate them.
- `` `PFunPDS.behaviorKernel` `` / `` `envBehaviorKernel` `` (= `b⟦S⟧`/`bₑ⟦E⟧`) — conditional-behavior kernels.
- `` `BehaviorEq` `` (= `≡ᵦ`) — behavioral equivalence with `refl`/`symm`/`trans`/`equivalence`; `of_eq` from `S = T`.

### Evaluators (`PFunDDS.lean`)
- `` `functionEvaluator f` `` — `f : X → Y` as a DDS answering `f` on the last input of every nonempty history.
- `` `historyEvaluator g` `` — DDS whose answer depends on the whole nonempty history (callback gets the domain proof). Backbone of `seededConditionCGame` and CBC/hash games.

### Converters and application
- `` `PFunPDS.applyDDC α S` `` (`ResourceView.lean`) — pushforward of the deterministic converter apply;
  *applying a converter creates a random system*. **The** converter-on-resource idiom:
  `cbcReal = applyDDC (ofStep cbcStep) 𝖱`-style.
- `` `PFunConverter.DDC.apply` `` (= `α ·ᶜ S`) / `` `DDC.ofStep` `` (`StepConverter.lean`) — deterministic
  apply, and the converter built from a per-round `step : U → List Y → X ⊕ V` (query `inl x` or output `inr v`).
- `` `DDC.simple c d` `` / `` `simpleStep` `` (`StepConverter.lean`) — the pointwise converter
  `c : U → X` (encode input) then `d : Y → V` (decode output); `simple_functionEvaluator`,
  `simple_simple_apply` are its computation lemmas.
- `` `DDC.feedback g` `` (`StepConverter.lean`) — the feedback converter (loop the output back through `g : Y → X`).
- `` `DDC.AnswersWithin step R` `` (`StepConverter.lean`) — the Def 3.8 round bound: `step` outputs within
  `R` rounds. The hypothesis for the query-budgeted DPI.
- `` `PFunConverter.queryLimit q` `` (= `[q]ᶠ`/`⟦q⟧ᶠ`) (`PFunConverter.lean`) — the query-limiting filter
  converter; `queryLimit_filter_apply_eq_filterQueries` identifies it with `⌈q⌉`.
- `` `cascade` `` / `` `combine op` `` / `` `cascadeConverter` `` / `` `combineConverter op` ``
  (`PFunConverter.lean`) — cascade `S;T`, parallel `S ⋆ₚ[op] T`, and their converter forms
  (`cascᶜ`, `comb⋆ᶜ[op]`); `cascadeViaConverter_eq_cascade`, `combineViaConverter_eq_combine` bridge them.
- `` `attachAt i α` `` (`PFunConverter.lean`) — attach a converter at interface `i` of a multi-interface
  `Resource`; `attachAt_comm` gives interface-disjoint commutation.

## 3. DPI / converter monotonicity (query-budget accounting)

The data-processing inequality: applying a converter cannot increase `Δ`. All in `AbsorbDPI.lean`.

- `` `maxAdvantage_filterQueries_applyDDC_le` `` — **the query-budgeted converter DPI**: for `step` with
  round bound `R` applied to two random-function resources, a `q`-query distinguisher of the applied
  systems is `≤` a `q·R`-query distinguisher of the resources:
  `Δ(⌈q⌉ applyDDC(ofStep step) P₁, ⌈q⌉ …P₂) ≤ Δ(⌈q·R⌉ P₁, ⌈q·R⌉ P₂)`. Needs `DDC.AnswersWithin step R`
  and `IsRandomFunction` on both. This is what a CBC/NMAC-style reduction into the switching lemma uses.
- `` `maxAdvantage_applyDDC_le` `` — the unbudgeted 1-Lipschitz form: `Δ(αS, αT) ≤ Δ(S,T)` for total
  `S, T` (needs a converter round bound `B` and `TotalOnNonempty` on both).
- `` `maxAdvantage_filterQueries_le` `` — `[q]`-filter monotonicity: `Δ(⌈q⌉S, ⌈q⌉T) ≤ Δ(S,T)` for total systems.
- `` `verdictProb_absorb` `` / `` `advantage_absorb` `` — the "absorb" identity underneath the DPI: a
  distinguisher of `applyDDC (ofStep step) S` equals a pushed-forward distinguisher of `S`.
- `` `queriesAtMostN_absorb_of_roundBound` `` — the absorbed run of a `q`-query winner against an
  `R`-round converter makes `≤ q·R` resource queries. The query-accounting core of the budgeted DPI.
- `` `PFunDDS.padDDD` `` / `` `padDDDDist` `` (`GameOf.lean`) — pad a distinguisher to *exactly* `q`
  queries (its normal form under `⌈q⌉`); the machinery behind the filtered `Δ` lemmas.

## 4. Switching lemma & birthday

### Birthday scalars and arithmetic
- `` `bday q N` `` / `` `bday_mono` `` (`HTechnique/Derivation.lean`) — the birthday defect `q(q−1)/(2N)`
  as `NNReal`, monotone in `q`. The reusable birthday constant.
- `` `pcoll t q` `` / `` `pcoll_eq_one_sub_descFactorial_div` `` (`SwitchingLemma.lean`) — the true collision
  probability of `q` uniform draws from `Fin t` (`Dist.mass … Collides`) and its closed form
  `1 − (t)_q/t^q`. That closed form is the bridge: `` `pcoll_le_birthday_tight` `` (`≤ q(q−1)/(2t)`),
  `` `pcoll_le_birthday` `` (`≤ q²/(2t)`, the rounded form), and the Boneh–Shoup two-sided bounds
  `` `min_le_pcoll` `` / `` `one_sub_exp_le_pcoll` `` / `` `pcoll_le_one_sub_exp` `` are all
  `Counting.lean` arithmetic transported along it. **`min_le_pcoll` is the only collision *lower*
  bound in the tree** — what an attack argument needs.
- `` `inv_card_le_iidPow_two_mass_collides` `` (`SwitchingLemma.lean`) — uniformity minimises collision
  probability at two draws (Boneh–Shoup Cor. B.2 at `k = 2`); arithmetic core `Counting.inv_card_le_sum_sq`.
- `` `pairCollisionUnionBound X q` `` (`SwitchingLemma.lean`) — the pair-count union-bound scalar
  `#{i<j} / |X|`; `` `pairCollisionUnionBound_le_birthday` `` gives `≤ ½q²/|X|` (CR18 Lemma 4.18).
- `` `birthday_bound` `` / `` `switching_ratio_le` `` / `` `falling_factorial_lower_bound` `` /
  `` `factorial_ratio_eq_descFactorial_inv` `` (`Counting.lean`) — the raw `1 − (N)_q/N^q ≤ q(q−1)/(2N)`
  arithmetic and the PRP/PRF ideal-vs-real mass-ratio lemmas. The number-theory core shared by CR18 and HCTR2.
  Two-sided (Boneh–Shoup Thm B.1): `` `min_le_one_sub_prod_sub_div_pow` `` (`≥ min{q(q−1)/4N, 0.63}`),
  `` `one_sub_exp_le_one_sub_prod_sub_div_pow` ``, `` `one_sub_prod_sub_div_pow_le_one_sub_exp` `` (needs `2q ≤ N`);
  engine `` `exp_neg_le_one_sub_half` `` (`e^{−x} ≤ 1 − x/2` on `[0,1]`).
- **Weierstrass `1 − ∑ aᵢ ≤ ∏ (1 − aᵢ)` has exactly one proof**: `` `Counting.one_sub_sum_le_prod_one_sub` ``
  (`Finset ι`, `ℝ`). `` `chain_product_lower_bound` `` (`range`, `≥` direction) and
  `` `nnreal_one_sub_sum_le_prod` `` (`NNReal`, hypothesis-free) specialize it. Do not write a fifth.
- `` `mass_le_pairCollisionUnionBound_of_cover` `` / `` `…_of_cover_injOn` `` (`SwitchingLemma.lean`) —
  the reusable birthday-cover combinator (see [REUSE THIS](#reuse-this--do-not-re-derive)).
- `` `uniform_mass_listCollision_le_pairCollisionUnionBound` `` (`SwitchingLemma.lean`) — **the leaf a
  condition-C endpoint actually asks for**: a uniform random function collides on a fixed `List` of `≤ q`
  inputs with mass `≤ pairCollisionUnionBound`. The older
  `` `uniform_mass_blindQueryCollision_le_pairCollisionUnionBound` `` is the optional-*vector* form;
  `blindQueryList` and `seededHashCollision` both speak `List`, so reach for the list one.

### The switching lemmas
- `` `urf_urp_switching X q` `` (`SwitchingLemma.lean`) — CR18 Lemma 4.19:
  `Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X) ≤ ½q²/|X|`. The headline URF↔URP statement.
- `` `URFURPSwitchingBound.of_finite` `` (`Complexity/SwitchingBridge.lean`) — the same bound as a reusable
  endpoint for any finite nonempty `X`; `` `PRF.FunctionVsPermutation.bound` `` (`Complexity/PRF.lean`) is
  the Boneh–Shoup Thm 4.6 PRF-layer wrapper.
- `` `filterURF_collisionCond_condEquiv_filterURP` `` (`SwitchingLemma.lean`) — the condition-C fact
  `gameOf (⌈q⌉ 𝖱 X) collisionCond |≡ ⌈q⌉ 𝖯 X` powering the switching lemma.
- `` `blindMaxWinProb_filterURF_collisionCond_le_birthday` `` (`SwitchingLemma.lean`) — the collision
  game's blind win prob is `≤ ½q²/|X|`.
- `` `collisionCond` `` / `` `ioCollision` `` / `` `monotone_collisionCond` `` (`SwitchingLemma.lean`) — the
  input-output collision predicate on a transcript and its prefix-monotonicity.

### Counting engine (`Counting.lean`, also mirrored in `SwitchingLemma.lean`)
- `` `card_function_fiber_finset` `` / `` `card_function_injOn_finset` `` / `` `card_perm_fiber_finset` `` —
  the fiber cardinalities (functions/permutations agreeing on a finite input set); the counting backbone.
- `` `multiShift` `` / `` `card_filter_shift` `` — the shift-bijection used to count collision-free assignments.
- `` `sum_prod_trichotomy` `` / `` `sq_sum_eq_sum_sq_add_two_mul_sorted` `` — the `∑ n(n−1)` sorted-pair
  identities behind the total-block birthday budget.

## 5. Condition-equivalence & the blind game (adaptive → nonadaptive)

**This is the framework's adaptive→nonadaptive engine.** A monotone-MBO *game* `Ŝ` that is conditionally
equivalent (`|≡`) to a plain system `T` lets you replace an **adaptive** distinguishing advantage
`Δ(S,T)` by a **nonadaptive** blind win probability `Γᵇ` of a fixed-query collision game — which then
reduces to a per-schedule seed-mass (birthday) leaf. Use the packaged endpoints; only supply the
scheme-specific collision predicate and its mass bound.

### The core relation (`CondEquiv.lean`)
- `` `CondEquiv Ŝ T` `` (= `Ŝ |≡ T`) — CR18 Def 4.19: the `Yⁱ`-output law of game `Ŝ` conditioned on
  "MBO not yet fired" (`Aᵢ=0`) equals `T`'s cumulative output law, stated cross-multiplied (division-free).
- `` `massYAfalse` `` / `` `massAfalse` `` / `` `massY` `` / `` `massDom` `` — the four unnormalized masses
  (game numerator/normalizer, plain numerator/normalizer) that `CondEquiv` cross-multiplies.
- `` `TotalOnNonempty T` `` — Maurer's "defined on the histories under discussion"; the side condition on
  the systems. `massDom_eq_one_of_totalOnNonempty` collapses the normalizer to `1`.
- `` `condEquiv_filterQueries` `` — `S |≡ T → ⌈q⌉S |≡ ⌈q⌉T`; the `[q]`-filter preserves condition C.
- `` `condEquiv_of_transcript_mass_reductions` `` (`SwitchingLemma.lean`) — **the way you prove a fresh
  `|≡`**: supply the good-world transcript-mass reductions (numerator/normalizer factorizations) and get `Ŝ |≡ T`.

### Win-probability layer
- `` `blindMaxWinProb` `` (= `Γᵇ`) / `` `maxWinProb` `` (= `Γ`) (`BlindConverter.lean`, `WinProb.lean`) —
  blind (nonadaptive) and general max win probability; `winProb_le_blindMaxWinProb`,
  `blindMaxWinProb_le_maxWinProb`, `blindMaxWinProb_fTransform_le` relate/transport them.
- `` `IsBlind` / `IsBlindDist` `` (`BlindConverter.lean`) — the nonadaptive (schedule-fixed) winner predicate.
- `` `blindQueryList w q` `` / `` `blindQueryVector` `` (`SwitchingLemma.lean`) — a blind winner's fixed
  `q`-query schedule; `blindQueryList_length_le`, `isPrefix_blindQueryList` are the reduction glue.

### The endpoints (reach for these, top-down)
- `` `maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf` `` (`GameOf.lean`) — **CR18 Thm 4.17 headline**:
  `gameOf S cond |≡ T → Δ(S,T) ≤ Γᵇ(gameOf S cond)`. Base-object form (constructs `Ŝ := gameOf S cond`).
- `` `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` `` (`BlindAbsorption.lean`) — the
  **filtered** Thm 4.17: `Ŝ |≡ T → Δ(⌈q⌉S, ⌈q⌉T) ≤ Γᵇ(⌈q⌉Ŝ)`, with the standing facts as
  `cr18_standing` autoParams. The composable, `q`-budgeted form (use this for concrete schemes).
- `` `advantage_le_blindMaxWinProb_gameOf` `` / `` `advantage_le_blindMaxWinProb_of_condEquiv` `` /
  `` `advantage_le_absorbedWinnerProb_of_condEquiv` `` (`GameOf.lean`, `BlindAbsorption.lean`) —
  per-distinguisher forms (blindness is *derived* from absorption; no `hblind` hypothesis).
- `` `BlindTheorem417Hyp.bound` `` (`Complexity/SwitchingBridge.lean`) — the named-hypothesis-package
  wrapper for Thm 4.17.

### Seed-indexed condition C — the single source of truth (`SwitchingLemma.lean`)
- `` `seededConditionCGame D F bad` `` — a seed-indexed last-query evaluator carrying a monotone
  condition-C failure bit; `_monotoneMBO`, `_totalOnNonempty`, `_isProbDist` supply its standing facts.
- `` `maxAdvantage_filterQueries_seededConditionCGame_le` `` — **public condition-C endpoint**: given
  `seededConditionCGame D F bad |≡ T` and a per-blind-schedule seed-mass bound
  `D.mass (fun a => bad a (blindQueryList w q)) ≤ ε`, concludes `Δ(⌈q⌉ ignoreMBO(…), ⌈q⌉ T) ≤ ε`.
  This is the reusable "Step 2" of any CR18 MBO-game proof (CBC-MAC, random-outer NMAC, …).
- `` `seededConditionCGame_ignoreMBO` `` — **`Ŝ⁻ = ofFunDist (fTransform F D)`**: stripping the monitor bit
  from *any* seed-indexed condition-C game returns the plain seed-evaluator system. Do not re-prove a
  per-scheme `…Game_ignoreMBO`; `seededHashThenURFGame_ignoreMBO` and `CBCMAC.cbcGame_ignoreMBO` are
  instances of it.
- `` `seededHashCollision H a l` `` / `` `seededHashThenURFGame` `` / `` `seededHashThenURF_condEquiv` `` —
  the hash-then-URF instance: condition C = "no two distinct queried inputs collide under the sampled hash".
- `` `maxAdvantage_filterQueries_seededHashThenURF_le` `` — the packaged first-collision bound
  `Δ(⌈q⌉ ignoreMBO(seededHashThenURFGame D H), ⌈q⌉ URF) ≤ ε` from the per-schedule hash-collision mass.
- `` `blindMaxWinProb_filterQueries_monitored_le` `` — `Γᵇ` of a seed-indexed monitored last-query game is
  `≤` any per-schedule mass bound; the reduction from the blind game to the seed leaf.

### Sum-of-permutations worked instance (`SumOfPermutations.lean`)
- `` `sopReal` / `sopIdeal` / `sopSeed` / `sopMidFunction` / `sopBad` / `sopGame` `` — XoP over a finite
  abelian `G` (`x ↦ π₁x + π₂x`) versus the URF, with the seed `(π, f)` and the bad event "the sampled
  *function* `f` collides on two distinct queried inputs" (`seededHashCollision`, reused).
- `` `sop_randomness_expander` `` — `Δ(⌈q⌉ sopReal, ⌈q⌉ sopIdeal) ≤ q²/|G|`, through
  `pairCollisionUnionBound`. **Note the direction**: the game sits on the *ideal* side and `sopReal` is
  the conditionally-equivalent target (`sop_condEquiv`), because conditioning on a seed event cannot
  enlarge a support and `sopReal`'s answer law is not full. `maxAdvantage_comm` flips it back.
- `` `sopSeed_mass_agree_and_good` `` — the fiber factorization: the URF/URP identity
  `uniform_function_agree_and_injOn_eq_perm_agree_mul_injOn` integrated over the independent permutation
  seed component with `mass_prod_congr_fiber`. This is how a *randomized* reduction step gets absorbed
  without a parallel-composition non-expansion.

### CBC-MAC worked instance (`CBCMAC.lean`)
- `` `cbcReal bf` / `cbcRealP bf` / `Vn` `` — CBC-MAC over `𝖱`/`𝖯` and the VIL-URF `Vₙ`; `cbcGame`,
  `cbcBad`, `cbcGame_ignoreMBO`, `cbc_condEquiv`, `mass_cbcBad_le` are the instance's condition-C data.
- `` `cbc_mac_randomness_expander` `` — **CR18 Thm 6.1**: `Δ(⌈q⌉ cbcReal, ⌈q⌉ Vn) ≤ ½(qL)²/|X|` for
  prefix-free `bf`. `` `cbc_mac_randomness_expander_urp` `` is the block-cipher corollary (triangle +
  budgeted DPI into the switching lemma). Read this as the template for a new MBO-game proof.

## 6. `Dist` facts

Core probability layer, `Dist.lean` unless noted. `Dist A = A →₀ NNReal`; `ProbDist A` is the weight-1 subtype.

- `` `Dist.uniform` `` / `` `uniform_apply` `` / `` `uniform_isProbDist` `` / `` `weight_uniform` `` — the
  uniform distribution and its mass/weight facts. `unitProbDist` is the `PUnit` point mass.
- `` `Dist.mass` `` / `` `massSet` `` / `` `evalPred` `` — event mass; `mass_add_compl`, `mass_le_weight`,
  `mass_le_one`, `mass_congr`, `mass_mono`, `mass_singleton`, `mass_eq_zero_of_forall_not`,
  `sum_mass_le_weight_of_pairwise_disjoint`, `sum_mass_eq_weight_of_pairwise_disjoint_of_cover`.
- `` `Dist.isProbDist` `` / `` `weight` `` — the weight-1 predicate and total weight; `weight_eq_sum`,
  `weight_eq_weight_of_isProbDist`.
- `` `Dist.fTransform f X` `` — pushforward of `X` along `f`. Key lemmas: `fTransform_apply_eq_mass`,
  `mass_fTransform`, `weight_fTransform`, `fTransform_isProbDist`, `fTransform_comp`, `fTransform_id`,
  `fTransform_injective_apply`, `mem_support_fTransform`.  Use
  `fTransform_comp_eq_of_pointwise` when two random variables share a source and stripping the
  richer one pointwise recovers the plain one; this derives the marginal law without a
  transcript- or product-specific bridge.
- `` `fTransform_bijection_uniform` `` / `` `fTransform_equiv_uniform` `` /
  `` `fTransform_uniform_eq_uniform_of_card_fiber_mul` `` — uniform is preserved by bijections /
  equivalences / equal-fiber maps. (See [REUSE THIS](#reuse-this--do-not-re-derive).)
- `` `Dist.prod X Y` `` / `` `prodProbDist` `` — independent product; `prod_apply`, `weight_prod`,
  `prod_isProbDist`, `prod_uniform`, `mass_prod_eq_double_sum`, `mass_prod_and`, `mass_prod_fst`,
  `mass_prod_snd`, `mass_prod_unitProbDist_right`, `indepRV_prodProbDist`.
- `` `fTransform_fst_uniform` `` / `` `fTransform_snd_uniform` `` / `` `fTransform_map_snd_prod_uniform` `` /
  `` `fTransform_eval_snd_prod_uniform` `` / `` `uniform_mass_eval` `` — product-uniform projection /
  evaluation (drop an ignored independent coordinate).
- `` `Dist.iidPow X q` `` / `` `clonePow X q` `` — `q`-fold i.i.d. / cloned power; `iidPow_isProbDist`,
  `clonePow_isProbDist`, and `iidPow_uniform_eq_uniform_fun` (`SwitchingLemma.lean`).
- `` `uniform_mass_eq_card_filter` `` / `` `uniform_mass_eq_mass_mul_mass_of_card_mul_eq` `` /
  `` `uniform_mass_le_inv_card_of_card_mul_le` `` — uniform mass as a fiber cardinality; the `≤ 1/|X|`
  leaf bounds for birthday covers.
- `` `Dist.PMF` `` (= `ℙ⟦·⟧`) / `` `condPMFOf` `` (= `ℙ⟦·∣·⟧`) / `` `RV` `` / `` `IndepRV` `` /
  `` `iIndepRV` `` — random-variable layer; `PMF_apply`, `mass_eval`, `condPMFOf_get_of_indep`,
  `mass_biForall_lt_eq_prod` (product of coordinatewise masses under independence).
- `` `Dist.marginal` `` / `` `marginalAt` `` / `` `restrict` `` / `` `cond` `` / `` `condEvent` `` — marginals, conditioning, restriction.

## 7. Custom tactics

The `cr18_*` suite packages paper-level bookkeeping so a lemma body is its mathematical argument plus a
finisher. Core layer in `CR18TacticsCore.lean`; game/filter/transcript layer in `CR18Tactics.lean`.

- `` `cr18_standing` `` (`CR18TacticsCore.lean`) — **discharge Maurer's standing side conditions** (game is
  a monotone-MBO probability system, total on the histories under discussion, stripped-system = the real
  construction). Register a protocol's facts once with `attribute [cr18_standing] …`; then autoParams
  `(:= by cr18_standing)` vanish, so paper theorems apply with only their math inputs.
- `` `cr18_pushforward` `` (`CR18TacticsCore.lean`) — pushforward/distribution normalizer (delegates to the
  `dist_simp` set + `Dist.mass_fTransform`, `Dist.evalPred_fTransform`).
- `` `cr18_prob` `` (`CR18TacticsCore.lean`) — probability-system bookkeeping (`isProbDist` of `URF`/`URP`/
  `ofFunDist`/`ofPermDist`/`filterQueries`/`uniform`/`fTransform`).
- `` `cr18_mass x` `` (`CR18TacticsCore.lean`) — **compute a `Dist.mass`/`probBad` fibered sum in one shot**
  (`cr18_mass_expand` → `cr18_sum_swap x` → `cr18_ite_collapse`), naming the surviving binder `x`.
- `` `cr18_card` `` (`CR18TacticsCore.lean`) — cardinality normalizer for the counting side of collision
  bounds (unfold `Fintype.card` of prod/sum/pi/perm/`Fin`, push casts).
- `` `cr18_arith` `` / `` `cr18_arith!` `` (`CR18TacticsCore.lean`) — arithmetic closers: `gcongr`/`omega`/
  `linarith`/`ring`/`norm_num`/`positivity` (`!` adds `bound`/`grind` for `NNReal`/char-`p`).
- `` `cr18_algebra` `` (`CR18TacticsCore.lean`) — field/char-`p`/permutation algebra closer (`ring`/`abel`
  then `grind` for XOR cancellation, hash congruence, `π a = b ⟹ π.symm b = a`).
- `` `cr18_adv_le` `` (`CR18TacticsCore.lean`) — reduce a law-level advantage bound to its pointwise
  transcript bound via the shared supremum shell.
- `` `cr18_routine` `` (`CR18TacticsCore.lean`) — layer-independent "this is trivial" closer.
- `` `cr18_filter` `` / `` `cr18_game` `` / `` `cr18_transcript` `` (`CR18Tactics.lean`) — normalizers for
  the `[q]` query filter / `gameOf`-MBO projections / transcript shapes.
- `` `cr18_simp` `` / `` `cr18_grind` `` / `` `cr18_close` `` (`CR18Tactics.lean`) — the conservative
  simplifier, the heavier grind pass, and the omnibus game-aware finisher.
- `` `dist_simp` `` (`DistSimpAttr.lean`) — the curated pushforward/uniform/weight simp set (attribute).
  `htechnique_dist_simp` (`HTechnique/TacticsSimpAttr.lean`) is the H-technique analogue.
- `` `char2` `` / `` `char2_norm` `` / `` `char2_iff` `` (`HCTR2.lean`) — GF(2)/characteristic-2
  arithmetic: `ring_nf` + `CharTwo.two_eq_zero`, and `linear_combination` over char-2 for XOR-cancellation
  goals and their iff forms. The go-to for `2x = 0`, `a ⊕ a = 0`-style hash algebra.
- `` `hctr2_ite_arith` `` / `` `ite_add_ite_dir` `` (`HCTR2.lean`) — the `_dir` **direction-partition
  splitter**: `hctr2_ite_arith` splits an `ite` grid and closes each branch; `ite_add_ite_dir` is the
  collapse lemma merging the `QueryDir.fwd`/`inv` slices of a valid pair into one per-pair charge
  (`(if A∧K∧d=inv then w else 0) + (if …fwd…) = if A∧K then w else 0`). Companions `ite_add_ite_of_disjoint`, `ite_kind_or`.

### H-technique tactics (`HTechnique/Tactics.lean`, `HTechnique/TacticsCore.lean`)
- `` `htechnique_adv_le` `` — advantage-shell reducer: turn `Adv`/`advPRF`/`advPRP`/`fixedQueryAdv ≤ ε`
  into pointwise transcript bounds via the `SecurityDefs` `*_le_of_pointwise` shells. Start most H-technique endpoint proofs with this.
- `` `htechnique_simp` `` / `` `htechnique_grind` `` — the main H-technique simplifier (CR18 bookkeeping +
  fixed-query/compression bundles + `simp`), and its grind pass. `htechnique_core_simp` is the import-cycle-safe core.
- `` `htechnique_total` `` — discharge `KStepTotal` / `TotalOnNonempty` side conditions for the migrated models.
- `` `htechnique_fixed_query` `` / `` `htechnique_compress` `` — normalize fixed-query transcript laws to
  system-factor form / collapse repeated-query tuples to the canonical injective query.

### Complexity-layer reduction tactics (`Complexity/Tactics.lean`)
- `` `cr18_hop_cases` `` — discharge a finite adjacent-hop `AdjacentMaxAdvantageBounded` goal by
  `interval_cases` + `simp_all`.
- `` `cr18_trace_arith` `` — normalize the finite sums from short hybrid traces.
- `` `cr18_reduction_from` `` / `` `cr18_reduction_bound_from` `` / `` `cr18_comp_reductions` `` /
  `` `cr18_solver_class_map_from` `` / `` `cr18_bound_transfer_from` `` — build/compose/transfer costed reductions.

## 8. AbstractCrypto — indifferentiability (R3/R5 layer)

> **Migration warning (2026-07-20).** This section is a historical,
> superseded snapshot and is non-operative as a reuse index. Its typed
> `ConstructiveCrypto.ResourceTheory` names and paths, concrete carrier claims,
> and completed RS-bridge/example receipts refer to a deleted or gated
> generation. Relevant current AC declarations live in the flat
> `AbstractCrypto` modules; the later heterogeneous `DiscreteSystems`
> experiment and bundled compatibility shim have also been deleted. There is
> no completed full RS-to-AC instantiation here to mirror: re-audit each
> declaration against source before reuse.

The constructive-cryptography / indifferentiability layer, in the sibling repo `../abstract-crypto/`.
Paths below are relative to that repo. This is the **R3/R5 metric/indifferentiability layer** (distinct
from the pure-`Δ` random-systems work above).

### The `constructs` calculus (`AbstractCrypto/Specifications/`)
- `` `Constructs π ℛ 𝒮` `` (= `ℛ —[π]→ 𝒮`) (`Basic.lean`) — JM20 Def 1 / CR18 Def 5.4: `π • ℛ ⊆ 𝒮`, the
  base relation every construction reduces to. `constructs_singleton_iff`, `constructs_one_of_subset`, `Constructs.mono`.
- `` `Constructs.simulator_trans` `` (`Basic.lean`) — JM20 Prop 2.1: transitivity of constructs with
  simulators (needs interface-disjoint `Commute`). `Constructs.simulator_par` is the parallel version.
- `` `Relaxation` `` / `` `Relaxation.Compatible` `` (`Relaxations.lean`) — CR18 Def 5.5: extensive monotone
  maps on `Set Φ` and the pull-through property that lets a relaxation chain.
- `` `Relaxation.eball ε` `` (`Relaxations.lean`) — the ε-relaxation `ℛ^ε` from a `PseudoEMetricSpace`; the
  metric slack in every quantitative statement. `eball_eball_subset` (JM20 Thm 2: errors add via triangle),
  `eball_compatible` (JM20 Thm 3, under `IsNonexpandingSMul`).
- `` `Constructs.eball_trans` `` (`Relaxations.lean`) — **JM20 Cor 1.1: THE composition theorem** for
  ε-relaxed constructions — `R —[π]→ S^ε` and `S —[π']→ T^ε'` give `R —[π'∘π]→ T^(ε+ε')`.
  `Constructs.eball_par` is the parallel-composition corollary.
- `` `Relaxation.star H` `` (`Relaxations.lean`) — CR18 Def 5.9 *-relaxation `ℛ^∗` (no guarantee at an
  adversary interface, via simulator submonoid `H`); `star_compatible` under interface commutation.
- `` `constructs_of_simulator` `` (`Relaxations.lean`) — MR16's key demotion: one simulator with
  `edist (π•R) (σ•S) ≤ ε` proves the doubly-relaxed `{R} —[π]→ eball ε (star H {S})`. Every
  indifferentiability proof funnels through this.

### Indifferentiability (`AbstractCrypto/Specifications/Indifferentiability.lean`)
- `` `Indifferentiable` `` — MR16 Def 23: `∃ π, ∃ σ∈H, edist (π•R) (σ•S) ≤ ε`.
- `` `Indifferentiable.construct` `` — MR16 Lemma 5: indifferentiability *is* the construction of `(S^∗)^ε`.
- `` `Indifferentiable.trans` `` — MRH04 composition: reductions chain with additive error `ε+ε'`.

### Non-expansion and the metric resource algebra
- `` `IsNonexpandingSMul` `` / `` `edist_smul_le` `` / `` `IsNonexpandingPar` `` / `` `nonexpandingEnd` ``
  (`AbstractCrypto/Algebra/Nonexpanding.lean`) — every scalar acts 1-Lipschitz ("attaching a converter
  cannot increase advantage", the DPI at this layer), the parallel version, and the canonical working
  monoid `M` of 1-Lipschitz endomorphisms.
- `` `ResourceAlgebra` `` / `` `ParResourceAlgebra` `` (`ConstructiveCrypto/ResourceTheory/Algebra.lean`) —
  MauRen11 Def 14 signature-indexed resources with `attach` and its laws; the serial/parallel base structure.
- `` `MetricResourceAlgebra` `` (`ConstructiveCrypto/ResourceTheory/Metric.lean`) — **the central R3/R5
  structure** (`extends ResourceAlgebra`): + per-signature pseudo-emetric with `equiv_iff_edist` and `edist_attach_le`
  (Def 16 non-expansion). Instantiate it for a concrete scheme. `edistQ` is the quotient distance actually
  used; `instPseudoEMetricQ` / `instNonexpandingAt` auto-activate the `eball` relaxations and JM20 Cor 1.
- `` `ProtocolIndifferentiable` `` (`ConstructiveCrypto/ResourceTheory/TwoPartyShapes.lean`) — the headline
  fixed-protocol indifferentiability def; `` `.constructs` `` (MR16 Lemma 5) turns a datum into a
  `Constructs … (eball ε (star …))` ready for `Constructs.eball_trans`. `ConstructsSecurely` /
  `.toConstructs` is the Alice/Bob/Eve availability+security package. `attachNE`, `neMonoidAt` lift a
  concrete converter into the working monoid / simulator class.
- `` `DistinguisherClass` `` / `` `.edistD` `` / `` `.metricAlgebra` `` (`ConstructiveCrypto/ResourceTheory/
  Distinguisher.lean`) — MauRen11 Def 15/16: derive the R3/R5 metric layer from a distinguisher-advantage
  class (`edistD = ⨆ t, adv t`) instead of postulating it. The entry point for choosing IT vs computational security.

### RS ↔ CC ↔ AC — how the three layers connect (`RandomSystemsCC/`)
**Key fact: CC resources ARE RS PDS — there is NO resource bridge.** The
`RandomSystemsCC` library instantiates the abstract-crypto CC algebra over PDS:
- `` `ResP σ := PFunPDS (Σ i, σ.In i) (Σ i, σ.Out i)` `` (`ProbAlgebra.lean:25`) —
  the CC `ResourceAlgebra` carrier **is a `PFunPDS`** (up to CR18 Def 3.20 behavioral
  equivalence, `cumulativeBehavior`). So a CC resource literally is a PDS system.
- `` `attachP` `` `= `` `PFunPDS.applyDDC` `` (`attachP_eq_applyDDC`, `ProbAlgebra.lean:178`)
  — CC converter *application* is exactly PDS converter application.
- `` `probMetricAlgebra n` `` — the concrete `MetricResourceAlgebra` over PDS; use this
  as `A` when instantiating `ProtocolIndifferentiable` at the PDS level.
- **Metric ↔ `Δ` transport** (so a CC `edist` bound becomes a PDS `Δ` bound and back):
  `` `edistD_le_maxAdvantage` `` (`ProbMetric.lean:668`, `edistD ≤ maxAdvantage`),
  `` `ofReal_maxAdvantage_le_edistD` `` / `` `edistD_eq_maxAdvantage` ``
  (`VerdictBehavior.lean:524/562`, the reverse / the equality).
- `` `Sponge.lean` `` — the WORKED `ProtocolIndifferentiable`-instantiated-at-PDS example; mirror it.

**⚠ THE ONE REAL GAP (not a bridge — a converter fragment).** `ProbAlgebra`'s `Conv`
is reused *verbatim* from `DetAlgebra.lean`: **only the memoryless simple-converter
fragment `(X → X) × (Y → Y)`**. The full PDS converter algebra
(`PFunConverter.DDC.ofStep` / `applyDDC` — type-changing, multi-call) is **NOT yet
exposed as a CC `Conv`**. Consequence: a scheme whose converter is type-changing or
multi-call (e.g. SequenceMAC's 4-call schedule) cannot yet be a CC `Conv`, even though
its resources are PDS. **To state indifferentiability over PDS for such a scheme
(R5), extend the CC `Conv` to the full `DDC`/`ofStep` converter — do NOT build a
resource carrier.** For R3 (indiff→PRF) you don't need any of this: take the indiff
consequence `Δ(⌈q⌉ SM_H, ⌈q⌉ SM_RO) ≤ ε_ind` as a plain PDS hypothesis.

## 9. H-technique (R4 ONLY — a SEPARATE route)

> **This layer is a SEPARATE proof route, used for R4 only.** It is **not** the Gaži/CBC pure-`Δ`
> (condition-equivalence) route of sections 1–5. Do not mix the two: a proof is either a `Δ`/blind-game
> proof or an H-technique/transcript-distance proof. Files under `HTechnique/`.

### Security definitions & notation (`HTechnique/SecurityDefs.lean`, notation in `HTechnique/Derivation.lean`)
- `` `Adv` `` (= `Adv[q](S, T)` = `adaptiveTranscriptAdvantage`) — thesis Def 2.26 adaptive advantage: the
  sup, over `q`-query-total deterministic environments, of `statDist` between the two transcript laws.
- `` `Adv_le_of_pointwise` `` — bound `Adv[q]` by a uniform pointwise transcript-distance bound (the
  adaptive shell reducer; pairs with `htechnique_adv_le` / `cr18_adv_le`).
- `` `fixedQueryAdv` `` — the non-adaptive advantage: sup over *fixed* query tuples of the fixed-query
  transcript-law `statDist`. `fixedQueryAdv_le_of_pointwise` reduces it to a per-tuple bound.
- `` `advPRF F` `` / `` `advNPRF F` `` / `` `advPRP F` `` — adaptive / non-adaptive PRF and PRP advantage of
  `F` vs the internally built `ProbPDS.urf` / `ProbPDS.urp`; `advNPRF_le_advPRF`, `advPRF_le_of_pointwise`, `advPRP_le_of_pointwise`.
- `` `filteredDelta_le_Adv` `` — bridge the raw CR18 filtered `Δ(⌈q⌉ S.val, ⌈q⌉ T.val)` to the thesis `Adv`
  (needs `KStepTotal` both and a `DeltaFilteredFiniteQueryNormalization`). Connects a Maurer `Δ` bound to the H-technique surface.
- Notations: `` `tr[q](S, E)` `` = `deterministicTranscriptDist`, `` `tr(S, xs)` `` = `fixedQueryTranscriptDist`,
  `` `Δ[q](S, T)` `` = `lawDelta`, `` `δˡ(P, Q)` `` = `lawStatDist`, `` `Pr[B ∣ P]` `` = `probBad`,
  `` `σ⁺(S, aug)` `` / `` `tr⁺(S, aug, xs)` `` = extended system-factor / extended fixed-query dist.

### Carrier-free law H core (`RandomSystem.lean`, namespace `RandomSystems.CR18`)

- `` `δ_hTechnique_le_on_good` `` — zero-defect two-cell H on arbitrary carriers. `Bad`
  automatically partitions `ideal.support`; the only pointwise premise is
  `ideal a ≤ real a` at supported good points. No normalization or weight bound.
- `` `δ_hTechnique_le_on_good_of_bad_le` `` — plug-in form adding the bad-mass premise and
  concluding `δ ideal real ≤ beta`; applying it exposes the good-dominance and bad-mass
  obligations directly.
- `` `δ_hTechnique_ratio` `` / `` `δ_hTechnique_ratio_of_bad_le` `` — nonzero-defect forms;
  the ratio premise is support-local and `ideal.weight ≤ 1` pays only for the defect term.
- `` `δ_hTechnique_le_on_good_fTransform` `` / `` `δ_hTechnique_ratio_fTransform` `` — the
  same law-level H bounds followed by any common deterministic observation (DPI); no
  transcript or product carrier is built into the statements.

### The fixed-query H-technique endpoints (`HTechnique/Derivation.lean`)

- `` `adv_le_of_fixedQuery_ratio_of_good` `` — **the workhorse**: a non-adaptive good-transcript ratio
  `(1−ε)·tr(T,xs)(t) ≤ tr(S,xs)(t)` for all `t ∉ Bad`, plus a uniform bad bound `Pr[Bad ∣ tr(T,E)] ≤ δb`,
  yields `Adv[q](S,T) ≤ δb + ε` (needs `KStepTotal` on both).
- `` `adv_le_of_fixedQuery_eq_on_good` `` — equality-on-good variant (`tr(S,xs)=tr(T,xs)` off `Bad`) giving `Adv ≤ δb`.
- `` `adv_le_of_fixedQuery_expectation` `` — expectation-method form: transcript-dependent error `ε(t)` with
  `𝔼_{tr(T,E)}[ε·𝟙good] ≤ c` gives `Adv ≤ δb + c`. For amortized error bounds.
- `` `statDist_le_of_extension` `` — data-processing: `π₁⋆ P' = P`, `π₁⋆ Q' = Q` ⟹ `δ(P,Q) ≤ δ(P',Q')`.
  The lemma that justifies revealing extra info (`aug`) before bounding distance.

### The extended-representative (σ⁺) endpoints (`HTechnique/Derivation.lean`)
- `` `adv_le_of_extFixedQueryRep_eq_on_good` `` — **the HCTR2-shaped endpoint**: equal *extended* fixed-query
  transcript masses on all good extended transcripts (over the sample `Ω` and transcript, via `aug`), plus a
  uniform bad-mass bound `δb` on the ideal extension, concludes `Adv[q](PMF pR FR, PMF pI FI) ≤ δb`. The
  good-event fixed-query representative bridge; needs `KStepTotal` on both.
- `` `adv_le_of_extFixedQueryRep_ratio_of_good` `` / `` `…_ratio_of_good_filtered` `` — the ratio (`≥ 1−ε`)
  variants; `extended_ratio_of_extFixedQueryRep_ratio_of_good` (Layer-B transfer) and the plain-extension
  `adv_le_of_extended_eq_on_good` / `adv_le_of_extended_ratio_of_good` / `adv_le_of_extFixedQuery_ratio_of_good` are siblings.
- `` `extendedTranscriptDistRep` `` / `` `extFixedQueryTranscriptDistRep` `` — the representative extended
  transcript dist (`σ⁺_{p,F,aug}(t,z)·η_E(t)`) and its fixed-query facade; the objects for HCTR2-style internal-value reveals.

### Fundamental theorem, coupling, and filtered layers (`HTechnique/Derivation.lean`)
- `` `adaptiveTranscriptAdvantage_le_lawDelta` `` — thesis Thm 2.31: `Adv[q](S,T) ≤ Δ[q](S,T)`;
  `adaptiveTranscriptAdvantage_le_lawStatDist` is the concrete `Adv ≤ δˡ(S.val, T.val)` case.
- `` `lawStatDist_le_mass_ne` `` — thesis Thm 2.32 coupling reading: any joint `J` with the right marginals
  gives `δˡ(P,Q) ≤ J.mass (·.1 ≠ ·.2)`. Bound advantage by a coupling's disagreement probability.
- `` `filteredAdaptiveTranscriptAdvantage Filt S T` `` — advantage restricted to `EnvRespects Filt`
  environments (non-pointless / birthday filters), with a metric toolkit `filteredAdv_mono`,
  `filteredAdv_triangle`, `filteredAdv_symm`, `statDist_le_filteredAdv`, and the filtered endpoint
  `adv_le_of_fixedQuery_ratio_of_good_filtered`.
- `` `bday q N` `` / `` `bday_mono` `` — the birthday defect used by the (adaptive, both-direction) switching step here (see §4).

### Permutation ideals and directions (`HTechnique/StrongPRP.lean`)
- `` `QueryDir` `` (`fwd`/`inv`) — the two-sided-oracle query tag; `QueryDir.eq_inv_of_ne_fwd` is its
  dichotomy. This is the type the `_dir` splitters (`ite_add_ite_dir`, `hctr2_ite_arith`; see §7) case-split on.
- `` `strongURP` `` / `` `tweakableURP` `` / `` `tweakableStrongURP` `` — the (tweakable) (strong) uniform
  random permutation ideals with both directions (`strongPermFunction`, `tweakablePermFunction`,
  `forwardOnly` per Jha–Nandi Def 3.6); `*_KStepTotal` / `*_consistent` are their standing data.
- `` `advSPRP` / `advTPRP` / `advTSPRP` `` — SPRP / tweakable-PRP / tweakable-SPRP advantages vs the ideals above.
- `` `fixedQueryRepresentative` `` (`HTechnique/FixedQuery.lean`) — the canonical fixed-query environment representative.
- `` `tprp` / `rnd` / `NP` `` (`HTechnique/TweakablePRP.lean`) — the tweakable-PRP real/ideal `ProbPDS`, the
  §3.4 "no-pointless" transcript filter, and the worked bound `tprp_rnd`
  (`filteredAdaptiveTranscriptAdvantage NP tprp rnd ≤ C(q,2)/N_min`), with `prp_rnd_bad_bound`, `good_ratio_transcript`.

### GF(2¹²⁸) field arithmetic (`HTechnique/GF2Field.lean`)
- `` `GF128` `` / `` `gf128_card` `` — the field `GF(2¹²⁸) = AdjoinRoot mPoly` and its cardinality
  `Fintype.card GF128 = 2¹²⁸` (the reusable size fact for collision/union bounds).
- `` `mPoly` `` / `` `mPoly_irreducible` `` — the POLYVAL reduction polynomial `X¹²⁸+X¹²⁷+X¹²⁶+X¹²¹+1`
  (`mPoly_monic`, `mPoly_natDegree`) and its kernel-checked irreducibility (`instance : Fact (Irreducible mPoly)`).
- `` `xGF` `` / `` `xGF_pow_n_ne_x` `` / `` `uPolyval` `` — the image of the indeterminate, the paper p.7
  load-bearing fact `xGF ^ 128 ≠ xGF` (consumed by `degenerate_hash_poly_ne_X`), and the Montgomery unit `u = x⁻¹²⁸`.
- `` `f2Mul` / `f2Mod` / `f2MulMod` / `f2PowMod` / `f2Gcd` `` — carryless (GF(2)) multiply / reduce / modmul
  / modexp / gcd on `Nat` bit-patterns (kernel-computable).
- `` `toPoly` `` and `` `toPoly_f2Mul` / `toPoly_f2Mod_congr` / `dvd_toPoly_f2Gcd` `` — the `ℕ → (ZMod 2)[X]`
  bit-encoding bridge and its homomorphism lemmas; use these to prove GF(2¹²⁸) field facts from the bit ops.
