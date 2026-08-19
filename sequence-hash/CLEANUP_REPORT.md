# SequenceHash Formalization — Cleanup & Criticism Report

Survey date: 2026-07-15. Scope: all of `sequence-hash/SequenceHash/**/*.lean` (3.6k lines), judged
against the gold standard `RandomSystems/CBCMAC.lean` / `CBCStructureGraph.lean`, the RS high-level
surface, and the reuse contract in `CHEATSHEET.md`. Read-only survey; no code was changed.

Verdict up front: R1 (`Encoding.lean`, `Spec.lean`, `SoundEncoding.lean`) and R3
(`SequenceMACIndiff.lean`) are close to standard. The R2 Gaži engine
(`SequenceMACPRF.lean`, 1572 lines) is the debt concentration: it contains at least **four
scheme-agnostic micro-theories developed inline**, a **5x copy-pasted normalization block**, a
**CHEATSHEET-banned wrapper lemma**, and **zero `grind` / one `cr18_*`** against 95 `simp` and
148 `have`. Roughly 500-600 lines of that file are generic mathematics that belongs in RS core.

---

## Executive summary — top 10 cleanups, ranked

1. **Extract the inline `piLaw` micro-theory** (`SequenceMACPRF.lean:303-446`, 9 nested `have`
   lemmas, ~145 lines inside ONE theorem) into an upstream `Dist.pi` in `Dist.lean`; two of its
   lemmas re-derive `iidPow_uniform_eq_uniform_fun` (`SwitchingLemma.lean:128`) and two more are
   literal copy-pastes of each other at two type instantiations.
2. **Upstream the mixture-convexity of advantage** hand-rolled in `gazi_outer_prf_hop`
   (`SequenceMACPRF.lean:1152-1332`): `mix`/`hfilter`/`hverdict`/`hmix_adv` are ~180 lines of
   `Finsupp.sum` bookkeeping proving the generic fact `Δ(Σ wK·S_K, Σ wK·T_K) ≤ sup_K Δ(S_K,T_K)`.
3. **Kill the 5x-duplicated fixed-query normalization block** (`SequenceMACPRF.lean:561-573,
   640-653, 835-846, 961-971, 1437-1450`) with one upstream lemma
   `statDist_fixedQueryTranscriptDist_functionEvaluator_urf` in `FunctionEvaluator.lean`.
4. **Delete `gazi_uniform_restrict`** (`SequenceMACPRF.lean:210-215`) — its body is
   `exact uniform_restrict e`. A banned `gazi_*` copy of a catalogued framework fact, consumed at
   4 call sites including `SequenceMACRealization.lean:296`.
5. **Upstream `gazi_statDist_le_adjacent_sum`** (`SequenceMACPRF.lean:276-291`) to
   `StatDist.lean` — the statDist telescoping/adjacent-sum does not exist upstream and is
   scheme-agnostic; and **upstream `gazi_prod_map_right` + Realization's `hprod`**
   (`SequenceMACPRF.lean:239-274`, `SequenceMACRealization.lean:209-234`) as one
   `Dist.fTransform_prod_map`, killing ~60 lines of manual `Finset.sum_bij`.
6. **Automation deficit in `SequenceMACPRF.lean`**: grind 0, cr18 1, simp-family 95, have 148,
   unfold 38, change 22 — versus CBCMAC's 11 / 6 / 22 / 60 / 14 at two-thirds the length. Casts
   alone (the ℝ-valued `fixedQueryDelta`, line 197) force 8+ `exact_mod_cast`/`push_cast` sites.
7. **Restructure `gazi_lemma5_depth_hybrid`** (`SequenceMACPRF.lean:579-971`; 393 lines, one
   theorem): hoist `Pref`/`prefAt`/`row`/`finish`/`addrR`/`addrI` to top-level definitions with
   named lemmas; the 50-line `addrI.inj'` proof (718-770) and the bare-hands `q = 0` branch
   (830-869) are prime `grind`/generic-lemma targets.
8. **Two-hop triangle via `SystemTrace`** (`SequenceMACPRF.lean:1507-1519`): 13 lines constructing
   a `SystemTrace` and summing a range, where `maxAdvantage_triangle _ _ _` is one line. Plainly
   roundabout.
9. **De-duplicate the five shared small helpers** proven 2-3x across files: `AnswersWithin
   (simpleStep ..) 1`, the `hrawTwo/Three/Four` evaluator facts, the `hquery` getD-covering
   lemma, the `mass_prod_snd`-then-`weight = 1` chain, and `uniform_fixedQuery_collision_le`
   (already consumed cross-file from `SequenceMACIndiff.lean:253` — it is framework material).
10. **Readability of the R3 seed** (`SequenceMACIndiff.lean:105-126`): the nested-product seed
    forces `a.2.2.2`-style projections at 10+ sites; replace with a structure (named fields
    `key`, `rawK`, `rawS`, `innerTag`) or named projection defs.

---

## Quantified automation table

Occurrence counts (grep on tokens; simp* = `simp`+`simpa`+`simp_rw`+`simp_all`). Gold standard row
first. `arith` = `gcongr`+`omega`+`bound`+`positivity`.

| File | lines | grind | cr18_* | simp* | have | calc | arith | unfold |
|---|---|---|---|---|---|---|---|---|
| **CBCMAC.lean (gold)** | 1006 | **11** | **6** | **22** | **60** | 2 | 55 | 14 |
| SequenceMACPRF.lean | 1572 | **0** | **1** | **95** | **148** | 15 | 37 | **38** |
| SequenceMACRealization.lean | 411 | 0 | 0 | 11 | 10 | 1 | 3 | 5 |
| SequenceMACIndiff.lean | 338 | 0 | 0 | 7 | 11 | 2 | 2 | 3 |
| RectHashThenPRF.lean | 446 | 0 | 0 | 1 | 12 | 4 | 29 | 6 |
| Converter.lean | 104 | 0 | 0 | 4 | 2 | 0 | 2 | 1 |
| Spec.lean | 271 | 0 | 0 | 21 | 28 | 3 | 10 | 9 |
| Encoding.lean | 164 | 0 | 0 | 14 | 8 | 0 | 1 | 0 |
| MDHash / Finite / SoundEncoding | 172 | 0 | 0 | 4 | 0 | 0 | 0 | 0 |

**Worst offender: `SequenceMACPRF.lean`.** Normalized per 1000 lines it runs simp 60 / have 94
versus CBCMAC's simp 22 / have 60 — with *zero* grind and *one* cr18 call
(`compReal_isProbDist`, line 113). Additional smells unique to this file: 22 `change` tactics and
5 `show ... from rfl` rewrites (lines 562-566, 643-647, 837-840, 962-965, 1441-1444 — the same
definitional unfoldings restated five times), symptoms of findings #3 and the `Prob`-wrapper
mismatch (M2 below). The support files are individually small enough that their raw counts are
acceptable; their problem is duplication (category 5), not tactic sprawl.

---

## 1. Modeling

| Location | Problem | Concrete fix | Impact | Upstream? |
|---|---|---|---|---|
| `SequenceMACPRF.lean:65` vs `MDHash.lean:17` | `abbrev CompressionFamily C B := C → B → C` duplicates `abbrev Compression State Block := State → Block → State` — two names for the same type, in two files, one importing the other. `SequenceMACRealization.lean:247` then writes `MACPRF.CompressionFamily (HashOutput L) B` while MDHash-side code writes `Compression`. | Keep ONE (suggest `Compression` in `MDHash.lean`, since it is the layer-neutral home); make `CompressionFamily` at most a deprecated alias, or delete it and rename uses. | M | N |
| `SequenceMACPRF.lean:100-102` vs `169-187` | Split-brain system presentation: `compReal`/`nmacReal`/`sequenceMACReal` are raw `PFunPDS` built via `ofFunDist ∘ fTransform`, while `cascadeReal`/`multiCompReal` are `PFunPDS.Prob` built via `Prob.functionEvaluator`. The mismatch forces the 14-line `hreal` bridge (453-465: `unfold`+`change`+`fTransform_comp` to prove the two spellings equal) and the `⟨compReal f, compReal_isProbDist f⟩` anonymous-constructor noise in `CompNASecure` (151-158). | Define `compRealP : PFunPDS.Prob B C := Prob.functionEvaluator uniformP (f ·)` once and set `compReal := compRealP.val` (same for the ideal side: `compIdealP := Prob.urf`). State `CompNASecure` through `fixedQueryDelta compRealP Prob.urf xs ≤ εna`. `hreal` and all subtype constructors disappear. | H | N |
| `SequenceMACPRF.lean:197-202` | `fixedQueryDelta` is ℝ-valued via an immediate NNReal-to-ℝ coercion of `statDist`. Every consumer then pays cast tax: `exact_mod_cast`/`push_cast` at 573, 628, 670, 953, 980-988, 1460, 1481. | Make `fixedQueryDelta` NNReal-valued; coerce once at the `Δ`-surface endpoints (`cascade_na_pf_fixedQuery_bound`, `gazi_outer_random_collision_bound`). | M | N |
| `SequenceMACIndiff.lean:105-116` | `SequenceMACSeparatedSeed L = K × (H × (H × (Seq → H)))` — right-nested products read as `a.1`, `a.2.1`, `a.2.2.1`, `a.2.2.2` at 10+ sites (121, 126, 145, 218, 264...). Pen-and-paper this is "the key, the two raw answers, the inner tag function"; in the file it is tuple soup. | Introduce a `structure SeparatedSeed` with fields `key rawK rawS innerTag` (plus its `Dist` as `fTransform` of the product along the obvious equiv), or at minimum four named projection `def`s used everywhere. | M | N |
| `SequenceMACPRF.lean:70-71` + `1420-1426` | `cascade` is defined as `mdIterate` but proofs mix the two spellings — line 597 computes with `mdIterate` directly, then 1420-1424 needs `change cascade ...`/`unfold zs appendDelimiter cascade` to cross back. | Make `cascade` an `abbrev` (or add `@[simp] cascade_def`), then never `change` between the two names again. | L | N |
| `SequenceMACRealization.lean:347` | `sequenceMAC_prf_bound_concrete` states the compression hop as a raw `Δ(⌈q⌉ compReal f, ⌈q⌉ compIdeal)` and then re-folds it into `epsComp` in the final calc step (401-407). The statement should speak the named quantity. | State the bound with `MACPRF.epsComp q f`; drop the `unfold MACPRF.epsComp; ring` step. | L | N |
| `Spec.lean:124-140` | `pad_take` and `pad_length_of_length_eq` are general facts about the top-level `pad` (used by three files), proven as local `have`s inside the collision theorem. The header's "obligations remain local" discipline is being over-applied: these are spec-level pad lemmas, not proof-local obligations, and R5 will need them again. | Hoist both to top-level theorems next to `pad` (Spec.lean:33). | M | N |

## 2. High-level lemma use

| Location | Problem | Concrete fix | Impact | Upstream? |
|---|---|---|---|---|
| `SequenceMACPRF.lean:1507-1519` | `htriangle` constructs a 3-entry `Complexity.SystemTrace`, invokes `maxAdvantage_le_adjacent_sum`, unfolds `adjacentMaxAdvantageSum`, and simps two `Finset.sum_range_succ` — to obtain a **two-hop triangle inequality**. | `maxAdvantage_triangle (⌈q⌉ nmacReal ℓ f pad) (⌈q⌉ nmacOuterRandom ℓ f pad) (⌈q⌉ macIdeal ℓ)`. One line. `SystemTrace` is for n-hop hybrids, not n = 2. | M | N |
| `SequenceMACPRF.lean:1152-1332` | `gazi_outer_prf_hop` re-derives advantage convexity from scratch instead of a DPI-style framework step. The actual crypto content is 15 lines (`hone` + `hpoint` via `maxAdvantage_filterQueries_applyDDC_le`); the other ~180 lines prove that a keyed mixture's advantage is the mixture of advantages. | See category 3, U3: upstream `maxAdvantage_mixture_le` and apply it. Target size of this proof after cleanup: ~40 lines. | H | Y |
| `SequenceMACPRF.lean:280-291` | Manual induction + calc for statDist telescoping while the repo's advantage layer has `maxAdvantage_le_adjacent_sum`/`advantage_telescope` as the canonical pattern. The statDist analogue is missing upstream, so the file inlined it — right math, wrong home. | Upstream as `statDist_le_adjacent_sum` in `StatDist.lean` (near `statDist_triangle`, StatDist.lean:~180) and delete here. | M | Y |
| `SequenceMACPRF.lean:1360-1366` | `hleaf`'s trivial-bound branch (when `card C ≤ q²` the birthday term exceeds 1) hand-computes `1 ≤ q²/|C|` through `le_div_iff₀` + `exact_mod_cast`. | `mass_le_one` + `cr18_arith` (its `NNReal` `bound`/`gcongr` pass closes `1 ≤ (q²:NNReal)/|C|` from `hcard` directly). | L | N |
| `RectHashThenPRF.lean:369-372` | `le_trans (le_of_eq (Dist.mass_congr _ fun h => Iff.intro (fun hb => hb) (fun hb => hb))) ...` — a `mass_congr` across an *identity* iff. It rewrites a predicate to itself. | Delete the `le_trans (le_of_eq ...)` wrapper; `exact uniformK_hashBadAt_le Hf xv` typechecks (the predicates are definitionally equal). | L | N |
| `SequenceMACIndiff.lean:312-317` | `change` restating the entire goal followed by `exact hsep` — the `hsep` obtained from the endpoint is already the goal up to unfolding `SM_RO_separated`. | `simpa [SM_RO_separated] using hsep` (one line), or make `SM_RO_separated` reducible for this proof. | L | N |
| `SequenceMACRealization.lean:394,400` | `add_le_add (le_of_eq rfl) hpull` and `add_le_add (le_refl _) hnmac` inside a calc. | `gcongr` both times (the repo standard; cf. CBCMAC's 55 arith-closer sites). | L | N |

## 3. Generic-lemma discovery + upstreaming (and reuse failures)

No `private` declarations exist in the tree (checked) — good. The `gazi_*` prefix, however, is
used exactly the way the CHEATSHEET forbids in one case, and hides four genuinely new
framework-grade facts in the others.

**Reuse failures (fact already existed upstream):**

| Location | Problem | Concrete fix | Impact | Upstream? |
|---|---|---|---|---|
| `SequenceMACPRF.lean:210-215` | `gazi_uniform_restrict` — body is `exact uniform_restrict e`. Verbatim violation of CHEATSHEET "do not mint a `gazi_*` local copy". Consumed at 237, 623, 943 and leaks into `SequenceMACRealization.lean:296` (`pullbackBlockSystem_URF`), spreading the bad name. | Delete; call `uniform_restrict` at all 4 sites. | M | N (exists) |
| `SequenceMACPRF.lean:426-446` | `piLaw_const_uniform_C` and `piLaw_const_uniform_BC` re-derive `iidPow_uniform_eq_uniform_fun` (`SwitchingLemma.lean:128`) — `piLaw` of a constant distribution *is* `Dist.iidPow` (`Dist.lean:1186`, `iidPow_apply` is the same `∏ i, X (x i)` formula). Two copies, one per codomain type, of a catalogued fact. | Prove `piLaw (fun _ => D) = iidPow D q` (one `Finsupp.ext`+`iidPow_apply` line) and use `iidPow_uniform_eq_uniform_fun`; both 10-line blocks collapse. Subsumed entirely by U1 below. | M | N (exists) |
| `RandomSystems` cross-check | `PrefixFree` (CBCMAC.lean:88), `queryPairSet` (SwitchingLemma.lean:846), `uniform_function_pair_eq_mass_of_codomain` (SwitchingLemma.lean:167), `mass_le_pairCollisionUnionBound_of_cover_injOn`, `maxAdvantage_filterQueries_seededHashThenURF_le` are all correctly reused — credit where due. | — | — | — |

**Generic facts buried in sequence proofs (should be generalized and upstreamed):**

| Id | Location | Buried fact | Upstream target (name the lemma) | Impact |
|---|---|---|---|---|
| U1 | `SequenceMACPRF.lean:303-446` | Heterogeneous finite product law: `piLaw D`, `piLaw_apply` (307), `piLaw_weight` (311), `piLaw_split` (324, fTransform along `Equiv.piSplitAt`), **`piLaw_change_one` (360: the one-coordinate hybrid-swap `statDist (pi D) (pi D') = statDist (D i) (D' i)`)**, `piLaw_map_C`/`piLaw_map_BC` (384/405 — the *same lemma* stated twice, at `C` and `B → C`). All indexed over generic `I`. | `Dist.pi (D : I → Dist A) : Dist (I → A)` in `Dist.lean` (generalizing `iidPow`; add `pi_const_eq_iidPow`), with `pi_apply`, `weight_pi`, `pi_eq_fTransform_prod_splitAt`, `pi_map` (one polymorphic statement), and `statDist_pi_update` — the hybrid-step lemma every one-coordinate-at-a-time argument in the repo wants. | H |
| U2 | `SequenceMACPRF.lean:239-274` and `SequenceMACRealization.lean:209-234` | `Dist.prod P (fTransform g X) = fTransform (fun p => (p.1, g p.2)) (prod P X)` (35 lines of `Finset.sum_bij`), and its two-sided sibling `prod (fTransform f P) (fTransform g Q) = fTransform (Prod.map f g) (prod P Q)` (25 more lines). Nothing of this shape exists in `Dist.lean` (checked: only the `*_prod_uniform` specials at Dist.lean:1540-1605). | `Dist.fTransform_prod_map (f) (g) : prod (fTransform f P) (fTransform g Q) = fTransform (Prod.map f g) (prod P Q)` in `Dist.lean`; derive the one-sided forms with `fTransform_id`. Both local proofs become one `rw`. | H |
| U3 | `SequenceMACPRF.lean:1152-1332` | (a) `hnmac`/`houter` (1155-1199 / 1200-1239, near-identical 45-line twins): `ofFunDist (fTransform g (prod P X)) = P.sum fun a w => w • ofFunDist (fTransform (g a) X)` — conditioning a product law on its first coordinate. (b) `hfilter` (1242): `⌈q⌉` commutes with `Dist.sum`-mixtures. (c) `hverdict`+`hmix_adv` (1256-1315): `advantage D (mix S) (mix T) = Σ w_K · advantage D (S K) (T K)`. | Three upstream lemmas: `Dist.fTransform_prod_eq_sum_smul` (Dist.lean), `PFunPDS.filterQueries_sum_smul` (PDS.lean), and `advantage_mixture` + corollary `maxAdvantage_mixture_le : (∀ a, Δ(S a, T a) ≤ ε) → Δ(mix S, mix T) ≤ ε` (Distinguishing.lean). This is THE standard "average over the key" step; NMAC will not be the last construction to need it. | H |
| U4 | `SequenceMACPRF.lean:276-291` | statDist adjacent-sum telescope (generic `laws : ℕ → Dist A`). Missing upstream (StatDist.lean has only `statDist_triangle` and `statDist_le_sum_of_forall_tsub_le`). | `statDist_le_adjacent_sum` in `StatDist.lean`. | M |
| U5 | `SequenceMACPRF.lean:217-237` | `gazi_eval_prod_uniform`: evaluation addressed through a `P ↪ I ⊕ J` split of two independent uniform function tables is one uniform table. Generic; already phrased via `sumArrowEquivProdArrow` + `uniform_restrict`. | Move next to `uniform_restrict` in `SwitchingLemma.lean` as `uniform_eval_sumSplit` (drop the `gazi_` prefix). | M |
| U6 | `SequenceMACPRF.lean:561-573, 640-653, 835-846, 961-971, 1437-1450` (+ `SequenceMACIndiff` consuming the same shape) | The normalization "functionEvaluator vs urf fixed-query transcript statDist = statDist of the two output-vector laws" — `fixedQueryTranscriptDist_functionEvaluator` + `_urf` + `fixedInputLiftDist` unfold + `statDist_fTransform_injective (fixedInputTranscriptPrefix_injective ..)`, copy-pasted **five times**. | `statDist_fixedQueryTranscriptDist_functionEvaluator_urf` in `FunctionEvaluator.lean` (that file already flags one lemma "candidate for upstream" at line 115 — this is its statDist companion). Local corollary: `fixedQueryDelta_functionEvaluator_urf`. | H |
| U7 | `SequenceMACPRF.lean:1081-1106` | `uniform_fixedQuery_collision_le` — birthday for a uniform function on a fixed tuple with repeated inputs excluded. Already consumed cross-scheme at `SequenceMACIndiff.lean:253`; nothing SequenceMAC-specific in it. | Move to `SwitchingLemma.lean` next to `uniform_function_pair_eq_mass_of_codomain` (167). | M |
| U8 | `SequenceMACIndiff.lean:279-292`, `RectHashThenPRF.lean:155-158, 411-414` | The `mass_prod_snd` then `rw [show P.weight = 1 ...]; one_mul` chain, 5 occurrences (Indiff runs it three times in one calc to marginalize three coordinates). | `Dist.mass_prod_snd_of_isProbDist : P.isProbDist → (prod P Q).mass (E ∘ .2) = Q.mass E` (and `_fst_`) in `Dist.lean:1378` vicinity; the Indiff calc becomes three one-line steps or one `simp [mass_prod_snd_of_isProbDist]`. | M |
| U9 | `SequenceMACPRF.lean:1122-1127`, `SequenceMACRealization.lean:351-356` | `hone : AnswersWithin (simpleStep c d) 1`, proven twice by identical `cases ys` scripts. | `PFunConverter.DDC.simpleStep_answersWithin_one` in `StepConverter.lean:622` vicinity. | L |
| U10 | `Converter.lean:74-84`, `SequenceMACRealization.lean:157-173` | `hrawTwo/hrawThree/hrawFour`: `(functionEvaluator H).1 (xs ++ [x₁,…,xₙ]) = Part.some (H xₙ)` — three arities, two files, all re-associating onto `CausalApply.functionEvaluator_raw_append` (CausalApply.lean:159). | One upstream lemma `functionEvaluator_raw_concat : ys ≠ [] → (functionEvaluator f).1 (xs ++ ys) = Part.some (f (ys.getLast h))` in `CausalApply.lean`; all five local `have`s die. | M |
| U11 | `SequenceMACPRF.lean:1390-1398`, `SequenceMACIndiff.lean:238-246` | `hquery`, verbatim twice: every member of a blind schedule `l` with `l.length ≤ q` is hit by the `Fin q`-indexed `l.getD` covering. | `blindQueryList_exists_getD` (or a bare `List.exists_getD_eq_of_mem_of_length_le`) in `SwitchingLemma.lean` next to `blindQueryList_length_le`. | L |
| U12 | `SequenceMACPRF.lean:847-866` | Inside the `q = 0` branch: two pushforwards into a subsingleton (`Fin 0 → C`) of equal-weight laws are equal — proven by hand with `Subsingleton.elim` + `weight_eq_sum` juggling. | `Dist.fTransform_eq_of_subsingleton : Subsingleton B → X.weight = Y.weight → fTransform f X = fTransform g Y` in `Dist.lean`; the whole 40-line `q = 0` branch becomes ~6 lines. | M |

## 4. Notation & automation (non-negotiable)

| Location | Problem | Concrete fix | Impact | Upstream? |
|---|---|---|---|---|
| `SequenceMACPRF.lean` (whole file) | grind 0 / cr18 1 / simp* 95 / have 148 / unfold 38 / change 22. The counterexample to the project's own automation mandate. Biggest contributors: the `piLaw` block (U1), the mixture block (U3), the 5x normalization block (U6), the cast churn from the ℝ-valued `fixedQueryDelta`, and the list combinatorics in `gazi_lemma5_depth_hybrid`. | Execute dispatch queue D1-D5 (below). Structural extraction alone removes ~55 `have`s and ~30 `simp`s; then a tactic pass converts the surviving cast/arith steps to `cr18_arith`/`gcongr`/`omega` and the list/`Subtype.ext` chains (e.g. `addrI.inj'` at 723-770, `same_side` at 599-618, `exists_prefixFree_appendDelimiter` at 1029-1067) to `grind`-first scripts. Target: grind >= 8, cr18 >= 4, simp <= 45, have <= 85. | H | N |
| `SequenceMACPRF.lean:197` | The central non-adaptive object `fixedQueryDelta S T xs` has no notation, so statements read as function soup while the adaptive side enjoys `Δ(⌈q⌉ ·, ⌈q⌉ ·)`. | Scoped notation, e.g. `Δᶠ⟨xs⟩(S, T)` (or `Δ(S, T ∣ xs)`), declared next to the definition; use in `CompNASecure`, Lemmas 5/6, Proposition 1. | M | N |
| `SequenceMACPRF.lean:481-502` | `hstep`'s equality-of-hybrids uses `split_ifs` with two `omega`-killed impossible branches and duplicated `Dist.fTransform_isProbDist` cases. | `piLaw`-upstreaming (U1) turns this into one `statDist_pi_update` application; the `D`-hybrid definition (477-479) stays as the only scheme content. | M | Y |
| `SequenceMACPRF.lean:1029-1031` | `push Not at hnone` — non-idiomatic spelling of `push_neg at hnone`. | `push_neg at hnone`. | L | N |
| `SequenceMACPRF.lean:562-566, 643-647, 837-840, 962-965, 1441-1444` | Five `rw [show multiCompReal q f = Prob.functionEvaluator … from rfl, show … = Prob.urf from rfl]` incantations — definitional facts restated inline instead of `@[simp]`/`rfl`-lemmas. | Dies with U6; if any survive, add `@[simp] multiCompReal_def`-style lemmas once. | M | N |
| `Spec.lean:174-181, 224-234`; `SequenceMACIndiff.lean:174-187` | Fixed-width field peeling by chained `List.append_cancel_left` + `List.append_inj_left (by simp)` — 3 near-identical multi-step blocks for peeling `encodeMSBF` fields off framed concatenations. | One local lemma in `Encoding.lean`: `encodeMSBF_append_cancel : encodeMSBF a ++ xs = encodeMSBF b ++ ys → a = b ∧ xs = ys` (from `length_encodeMSBF` + `encodeMSBF_injective`); each block becomes 1-2 applications. | M | N |
| `RectHashThenPRF.lean:91-107, 122-136` | Twin 16-line `rw [show … from funext fun ω => propext (Iff.intro …)]` blocks to rewrite under a binder with `transcriptSystemEvent_functionEvaluatorRV_iff`. | `simp only [transcriptSystemEvent_functionEvaluatorRV_iff]`-driven `Dist.mass_congr` (or mark the iff `@[simp]` locally); both blocks shrink to ~3 lines. | L | N |

## 5. Reuse failures / repetitions / dead code

| Location | Problem | Concrete fix | Impact |
|---|---|---|---|
| `SequenceMACPRF.lean:384-425` | `piLaw_map_C` vs `piLaw_map_BC`: byte-identical proofs, only `C` vs `B → C` differs. Copy-paste inside a single proof term. | One polymorphic `pi_map` (U1). | H |
| `SequenceMACPRF.lean:1155-1199 vs 1200-1239` | `hnmac` vs `houter`: 45-line twins differing only in the sampled object (`C` vs `B → C`). | One generic conditioning lemma (U3a) applied twice. | H |
| `SequenceMACPRF.lean:426-446` | `piLaw_const_uniform_C` vs `_BC`: same twin disease. | `iidPow_uniform_eq_uniform_fun` (already upstream). | M |
| 5x normalization block (see U6) | Largest literal copy-paste in the tree (~12 lines x 5). | U6. | H |
| `Converter.lean:63-100` vs `SequenceMACRealization.lean:134-195` | The calls/rounds realization proofs share the whole skeleton (`calls` list, `rounds`, `hraw*`, `apply_ofStep_functionEvaluator_of_round`, branch `simp`s). Acceptable duplication of *structure* (different schedules) but the `hraw*` helpers are pure copy-paste (U10), and the four-way branch `simp` lists repeat the same 7-lemma set 4 times (183-195). | U10 plus a local `macro`/`simp` set (`seqmac_realize_simps`) for the shared lemma list. | M |
| `sequence-hash/dispatch/SequenceMACPRF-advPRF-superseded.lean` | Superseded proof kept as a loose `.lean` among dispatch cards. Not in the build glob (lakefile `andSubmodules SequenceHash`), so harmless, but it still greps as live Lean and references the abandoned `advPRF` route. | Rename to `.lean.txt` or move under `dispatch/archive/` so surveys and greps stop tripping on it. | L |
| `SequenceMACPRF.lean:299` (`gazi_lemma6_row_hybrid`) | Unnecessary hypothesis shape: takes `hna : CompNASecure q f εna` but uses only the single tuple `bs = (zs ·).2` (line 470: `hna bs`). The lemma is per-tuple; taking the universally quantified assumption widens the interface for nothing. | Take `h : statDist ... (bs) ≤ εna`-shaped input (or keep `hna` but note it in the docstring); cheap, improves layering with Lemma 5's `hrows`-style parameterization, which already does this correctly. | L |

## 6. Anything basically dumb

| Location | What | Say it plainly |
|---|---|---|
| `SequenceMACPRF.lean:1507-1519` | `SystemTrace` + range-sum machinery for a 2-element triangle inequality. | Using a combine harvester to mow two blades of grass. `maxAdvantage_triangle`, one line. |
| `RectHashThenPRF.lean:369-372` | `mass_congr` across `Iff.intro (fun hb => hb) (fun hb => hb)`. | A rewrite by reflexivity, dressed up. Delete. |
| `SequenceMACPRF.lean:210-215` | A named, doc-less theorem whose proof is `exact uniform_restrict e`. | This is exactly the `gazi_*` transcription the CHEATSHEET's first page bans. |
| `SequenceMACPRF.lean:579-971` | One theorem, 393 lines, ~30 `let`/`have` bindings deep, with a 50-line embedded injectivity proof (723-770) and a 40-line degenerate-case branch (830-869). | The depth hybrid IS the paper's real content, but nobody can review a 400-line term. Hoist `Pref`, `prefAt`, `row`, `finish`, `addrR`, `addrI` to top-level defs with named injectivity/computation lemmas; the theorem body should read like Gaži's Appendix A paragraph. |
| `SequenceMACIndiff.lean:148-152` | The witness history for the outer call is an inline four-way `if` nest inside an anonymous `⟨…⟩` constructor inside a `refine`. | Name it (`separatedCallHistory a`), give it the `length ≤ 3` lemma, and the `sequenceMACSeparatedOuterCall` def stops being a proof-within-a-definition. |
| `SequenceMACPRF.lean:1029` | `push Not at hnone`. | Nobody else in the repo spells `push_neg` this way. |

---

## Cleanup dispatch queue (ordered, one Codex dispatch each)

Reminder per standing rule: dispatch ONLY via `sequence-hash/dispatch/codex-dispatch.sh <card> <out>`.

**D1 — Upstream `Dist.pi` and re-base Lemma 6.**
Files: `RandomSystems/Dist.lean` (+`SwitchingLemma.lean` bridge), `SequenceMACPRF.lean`.
Add `Dist.pi`, `pi_apply`, `weight_pi`, `pi_eq_fTransform_prod_splitAt`, `pi_map`,
`statDist_pi_update`, `pi_const_eq_iidPow`; rewrite `gazi_lemma6_row_hybrid` (297-573) on top,
deleting the 9 inline `piLaw_*` haves.
Expected delta: SequenceMACPRF −~180 lines, −~35 have, −~20 simp; Lemma 6 body ≤ 100 lines.

**D2 — Upstream the fixed-query normalizer (U6) + `fixedQueryDelta` polish.**
Files: `RandomSystems/FunctionEvaluator.lean`, `SequenceMACPRF.lean`.
Add `statDist_fixedQueryTranscriptDist_functionEvaluator_urf`; make `fixedQueryDelta`
NNReal-valued with scoped notation; replace the 5 normalization blocks and the 5
`rw [show ... from rfl]` incantations; delete the `q = 0` branch via U12
(`Dist.fTransform_eq_of_subsingleton`).
Expected delta: −~110 lines, −8 cast sites, −22 `change`/`show` sites.

**D3 — Upstream mixture convexity (U3) and shrink `gazi_outer_prf_hop`.**
Files: `RandomSystems/Dist.lean`, `RandomSystems/PDS.lean`, `RandomSystems/Distinguishing.lean`,
`SequenceMACPRF.lean`.
Add `Dist.fTransform_prod_eq_sum_smul`, `PFunPDS.filterQueries_sum_smul`, `advantage_mixture`,
`maxAdvantage_mixture_le`; rewrite `gazi_outer_prf_hop` to: split key, one-call converter DPI
(`maxAdvantage_filterQueries_applyDDC_le`), `maxAdvantage_mixture_le`.
Expected delta: 220 → ~40 lines; −~35 have.

**D4 — Delete/upstream the remaining `gazi_*` generic layer (U2, U4, U5) + fix the dumb spots.**
Files: `RandomSystems/Dist.lean`, `RandomSystems/StatDist.lean`, `RandomSystems/SwitchingLemma.lean`,
`SequenceMACPRF.lean`, `SequenceMACRealization.lean`.
`fTransform_prod_map` (kills `gazi_prod_map_right` + Realization `hprod`),
`statDist_le_adjacent_sum`, `uniform_eval_sumSplit`; delete `gazi_uniform_restrict` (4 call
sites); replace the `SystemTrace` triangle with `maxAdvantage_triangle`; `push_neg` spelling;
`gcongr` at Realization:394/400.
Expected delta: −~120 lines across both files; the file-level `gazi_` prefix survives only on the
paper-named Lemmas 5/6.

**D5 — Small-helper batch (U7-U11) + Indiff seed structure.**
Files: `RandomSystems/SwitchingLemma.lean`, `RandomSystems/StepConverter.lean`,
`RandomSystems/CausalApply.lean`, `RandomSystems/Dist.lean`, `SequenceMACPRF.lean`,
`SequenceMACIndiff.lean`, `SequenceMACRealization.lean`, `Converter.lean`,
`RectHashThenPRF.lean`.
Upstream `uniform_fixedQuery_collision_le`, `mass_prod_snd_of_isProbDist`,
`simpleStep_answersWithin_one`, `functionEvaluator_raw_concat`, the getD-covering lemma; convert
`SequenceMACSeparatedSeed` to a structure with named fields; drop the RectHashThenPRF no-op
`mass_congr` and compress its twin `propext` blocks.
Expected delta: −~130 lines total across 5 files; Indiff calc at 279-292 collapses to 3 lines.

**D6 — Restructure `gazi_lemma5_depth_hybrid` (the 393-line monolith).**
Files: `SequenceMACPRF.lean` only (uses D1/D2/D4 output).
Hoist `Pref`, `prefAt`, `row`, `finish`, `addrR`, `addrI` (+ their injectivity/computation
lemmas, `same_side` as a `PrefixFreeQueries` lemma) to top level; grind-first the list
combinatorics (`take`/`drop`/`getElem?` chains at 698-712, 780-827).
Expected delta: theorem body ≤ 150 lines reading like Appendix A; +4-6 grind, −~25 have.

**D7 — Spec/Encoding polish + model unification.**
Files: `Spec.lean`, `Encoding.lean`, `SequenceMACIndiff.lean`, `SequenceMACPRF.lean`, `MDHash.lean`,
`SequenceMACRealization.lean`.
Hoist `pad_take`/`pad_length_of_length_eq`; add `encodeMSBF_append_cancel` and use at the 3
peeling sites; merge `CompressionFamily` into `Compression`; introduce `compRealP`/`compIdealP`
`Prob` wrappers and restate `CompNASecure` through `fixedQueryDelta`; state
`sequenceMAC_prf_bound_concrete` with `epsComp`.
Expected delta: −~60 lines; `hreal` bridge (453-465) deleted; statements read paper-first.

**D8 — Final automation pass + verify counts.**
Files: all sequence files.
Sweep remaining `have`-towers into `cr18_arith`/`gcongr`/`omega`/`grind`; re-run the count table
and record it in `sequence-hash/STATUS.md`-equivalent (per the 3-docs rule, PLAN.md §status).
Gate: SequenceMACPRF at grind ≥ 8, cr18 ≥ 4, simp* ≤ 45, have ≤ 85, no `change`-count above 6;
`lake build SequenceHash` clean and `lean_verify` axiom-clean on the three guardrail theorems.
