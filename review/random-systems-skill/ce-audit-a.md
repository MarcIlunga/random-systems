# Independent audit: conditional-equivalence skill reference

Date: 2026-08-06

Audited text:

- `/Users/marcilunga/.codex/skills/random-systems-proofs/references/conditional-equivalence.md`, all lines 1–241.
- `/Users/marcilunga/.codex/skills/random-systems-proofs/references/creative-search.md`, lines 31–58 only.

I did not read any pre-existing audit report or sketch. This report compares the target text directly with the three requested primary PDFs and the current Lean source/declarations.

## Verdict meanings

- **VERIFIED** — matches the primary source/current declaration at the stated scope.
- **OVERSTATED** — has a correct core but omits a material premise, scope restriction, or qualification.
- **FALSE** — conflicts with the primary source or current library.
- **STALE** — was plausibly once accurate, but its current line/location/build-status claim has drifted.
- **NORMATIVE-NOT-FACTUAL** — workflow or style advice rather than a theorem/factual claim.

## Primary-source map and verification receipts

PDF page references below are one-based PDF leaves.

- **CR18** — `papers/CR18_LN.pdf`:
  - Def. 3.22 (MBO monotonicity): printed p. 71, PDF leaf 42.
  - Def. 4.19 (one enhanced system versus one ordinary target): printed p. 108, PDF leaf 60.
  - Defs. 4.20–4.21 and Thm. 4.17: printed pp. 109–110, PDF leaf 61.
- **MPR07** — `papers/MaPiRe07.pdf`:
  - Defs. 9–10 (MBO, stripping, masking/restricted equivalence): printed p. 138, PDF p. 9.
  - Lemma 5: printed p. 140, PDF p. 11; construction/proof: printed pp. 141–142, PDF pp. 12–13.
- **Lanzenberger thesis** — `papers/thesis (1).pdf`:
  - Lemma 2.8 (coupling is an honest joint distribution): printed p. 13, PDF p. 23.
  - Def. 2.17 (transcript-law equivalence): printed p. 16, PDF p. 26.
  - Thms. 2.31–2.32 (attained representatives and coupling): printed p. 20, PDF p. 30.
  - Thm. 2.37 (winnability): printed p. 24, PDF p. 34.

Focused checks run against the current tree:

- `lake env lean RandomSystems/CondEquiv.lean` — success.
- `lake env lean RandomSystems/GameOf.lean` — success.
- `lake env lean RandomSystems/SwitchingLemma.lean` — success.
- `lake env lean RandomSystems/CBCMAC.lean` — success.
- `lake build RandomSystems.RandomSystemCoupling` — success.
- `lake env lean RandomSystems/CBCStructureGraph.lean` — failure at several migrated APIs and warning that `mass_cbcGraphBad_le` uses `sorry`.
- `lake build RandomSystems.GameWinnability` — failure at several `NNReal`/`Real` migration points and warning that a declaration uses `sorry`; consequently `LanzenbergerChain.lean` cannot currently be checked through that import, although its source declarations are present.

## Bottom-line conclusions

1. Strict CR18 conditional equivalence is genuinely **one-sided**: an MBO-enhanced source `Ŝ` is related to an ordinary target `T`. Thm. 4.17 is an implication from that CE identity (plus game/standing assumptions) to a blind-game upper bound. It is not an exactness or completeness theorem.
2. MPR07 Lemma 5 is a different, symmetric construction: it enhances both systems, makes the two masked/pre-winning systems restricted equivalent, and represents `δ_k^D(S,T)` exactly as both winning probabilities. It does not choose equivalent PDS representatives and is not a static coupling theorem.
3. Lanzenberger's Thms. 2.31–2.32 are the representative/attainment/coupling layer. Their thesis scope is finite systems with a common domain. An unqualified coupling is an honest nonnegative joint distribution.
4. CE has no intrinsic birthday or other asymptotic rate. CR18 supplies a reduction to a winning probability; a separate probability theorem supplies every concrete rate.
5. An MBO is not “free” without qualification. It is a design variable only among monotone conditions for which the new CE identity and winning-probability bound are proved. Shrinking/refining a bad event does not automatically preserve CE.
6. The blind reduction absorbs the original adaptive distinguisher together with the target-side reply process into a winner blind to the *live game's* responses. In the packaged seeded endpoint, the leaf is therefore a uniform claim over each blind winner's fixed issued-query list `blindQueryList w q` (length at most `q`). It does not leave an “adaptive blind winner,” nor does it select one universal schedule independent of `w`.
7. Several library pointers have drifted, and `CBCStructureGraph.lean` is not a completed, compiling counting route.

## Claim-by-claim audit: `conditional-equivalence.md`

### CE-00 — line 1

- **Exact claim:** “Conditional equivalence (CR18 Thm 4.17).”
- **Verdict:** **VERIFIED**.
- **Primary evidence:** CR18 printed p. 110/PDF leaf 61 states Thm. 4.17 and its `Δ(S,T) ≤ Γ(bŜ)` corollary. Current Lean headline forms are `maxAdvantage_le_blindMaxWinProb_of_deltaFiniteQueryNormalization` at `RandomSystems/GameOf.lean:1343` and `maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf` at `:1472`.
- **Safest replacement wording:** “Conditional equivalence and CR18 Theorem 4.17.”

### CE-01 — lines 15–17

- **Exact claim:** “The bad thing is a condition the distinguisher triggers. Use it when transcripts are not enough: adaptive, stateful systems where the bad event is something the adversary causes rather than a property of the transcript.”
- **Verdict:** **OVERSTATED**.
- **Primary evidence:** CR18 Def. 4.19 and Thm. 4.17 do use an MBO that a winner can provoke, but nothing says transcripts are “not enough.” Indeed CR18's own `gameOf` examples use transcript conditions, and Lean defines `gameOf (S) (cond : List (X × Y) → Bool)` at `RandomSystems/GameOf.lean:988`. All distinguishing behavior is still transcript-law behavior. The contrast with an H-technique transcript predicate is a routing heuristic, not a mathematical limitation.
- **Safest replacement wording:** “Use CE when the proof is naturally expressed by a hidden prefix-monotone condition that the interaction may trigger, especially when that condition depends on hidden seed/state rather than only on the visible transcript.”

### CE-02 — line 19

- **Exact claim:** ``Δ(S,T) ≤ Γᵇ(gameOf S cond)``.
- **Verdict:** **OVERSTATED**.
- **Primary evidence:** CR18 Thm. 4.17, printed p. 110/PDF leaf 61, has the antecedent `Ŝ |≡ T` and requires `Ŝ` to arise by enhancing `S` with an MBO. The actual Lean theorem at `RandomSystems/GameOf.lean:1343–1348` also requires monotonicity, both probability-law hypotheses, both totality hypotheses, and `DeltaFiniteQueryNormalization`, before accepting `gameOf S cond |≡ T`.
- **Safest replacement wording:** “If `cond` is monotone and `gameOf S cond |≡ T` (with the standing probability/totality/normalization hypotheses), then `Δ(S,T) ≤ Γᵇ(gameOf S cond)`.”

### CE-03 — lines 25–29

- **Exact claim:** Strict CR18 CE relates one MBO-enhanced `Ŝ` to one ordinary `T`, equates response behavior while the MBO is zero, and Thm. 4.17 turns that into a blind-winning bound.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** CR18 Def. 4.19, printed p. 108/PDF leaf 60, defines `Ŝ |≡ T` by equality of `p^{Ŝ}_{Y^i|X^i,A_i=0}` and `p^T_{Y^i|X^i}`. Thm. 4.17, printed p. 110/PDF leaf 61, derives the blind-game bound. Lean's one-sided relation is exactly `def CondEquiv (Shat : PFunPDS X (Y × Bool)) (T : PFunPDS X Y)` at `RandomSystems/CondEquiv.lean:118–122`.
- **Safest replacement wording:** The existing wording is safe; “cumulative response law conditioned on `A_i=0`” is slightly more exact than “response behavior while the MBO is zero.”

### CE-04 — lines 30–34

- **Exact claim:** MPR07 Lemma 5 enhances both systems with MBOs, makes the pre-winning parts equivalent, and is exact for each distinguisher/horizon; this should not be called completeness for strict one-sided CE.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** MPR07 Defs. 9–10, printed p. 138/PDF p. 9, define stripping `S⁻`, masking `S†`, and restricted equivalence `S† ≡ T†`. Lemma 5, printed p. 140/PDF p. 11, constructs `Ŝ,T̂` with `Ŝ⁻ ≡ S`, `T̂⁻ ≡ T`, `Ŝ† ≡ T̂†`, and `δ_k^D(S,T)=ν_k^D(Ŝ)=ν_k^D(T̂)` for all `D`. This is a two-game statement, not CR18 Def. 4.19's one-game/ordinary-target relation.
- **Safest replacement wording:** “MPR07 Lemma 5 constructs both enhanced systems once and gives exact **transcript distance** `δ_k^D` for every `D` (and each horizon `k`); it is not a completeness theorem for CR18's one-sided `Ŝ |≡ T`.”

### CE-05 — lines 35–39

- **Exact claim:** Representative selection/coupling attainment are Lanzenberger equivalence-class operations (Def. 2.17, Thms. 2.31–2.32), winnability is Thm. 2.37, and representative replacement is not CE.
- **Verdict:** **VERIFIED** (with an omitted scope qualification).
- **Primary evidence:** Thesis Def. 2.17, printed p. 16/PDF p. 26, defines transcript-law equivalence and classes. Thm. 2.31 and Thm. 2.32, printed p. 20/PDF p. 30, choose representatives attaining class distance and then an honest coupling. Thm. 2.37 is printed p. 24/PDF p. 34. In Lean, `Equivalent` is a separate relation at `RandomSystems/RandomSystem.lean:539–541`; `CondEquiv` is at `RandomSystems/CondEquiv.lean:118–122`. Source wrappers are `theorem_2_31_distance_eq_advantage_attained` at `RandomSystems/LanzenbergerChain.lean:200–207` and `theorem_2_32_coupling_theorem` at `:252–264`.
- **Safest replacement wording:** Add: “The thesis attainment/coupling theorems are for its finite, common-domain setting; the current Lean wrappers make those hypotheses explicit.” Also note that the current `GameWinnability.lean`/Thm. 2.37 wrapper is not build-clean.

### CE-06 — lines 41–50

- **Exact claim:** The five-step “allowed design sequence,” ending with “use a coupling only if an actual nonnegative joint law is constructed.”
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** The sequencing is a repository discipline. Its final terminology rule is consistent with thesis Lemma 2.8, printed p. 13/PDF p. 23, which calls a joint distribution a coupling, and with Lean's `DistCoupling` structure at `RandomSystems/Coupling.lean:45–53`, whose `joint` has an explicit `nonneg` field and two marginal equalities.
- **Safest replacement wording:** Label it explicitly: “Repository modeling discipline (not a theorem): …”. Retain the requirement that signed joints be called virtual joints/quasi-couplings, not unqualified couplings.

### CE-07 — lines 51–54

- **Exact claim:** Designing a simulator with CE in mind is valid, but this is not a “representative choice” absent a separate equivalence proof.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** The distinction is well founded: `CondEquiv` relates a chosen enhanced source to a chosen target (`CondEquiv.lean:118–122`), whereas representative membership is `Equivalent` (`RandomSystem.lean:539–541`). Neither source theorem licenses silently changing the externally intended ideal resource.
- **Safest replacement wording:** “One may design the ideal-world simulator so that the resulting target `T` admits a CE proof, provided the simulator is separately shown to realize the intended ideal resource. Do not call this representative selection unless an `Equivalent` proof is supplied.”

### CE-08 — lines 58–62

- **Exact claim:** Once source/target are fixed, `cond` is a “free parameter”; refining it automatically refines the bound “on the same endpoint, with the same plumbing.”
- **Verdict:** **OVERSTATED**.
- **Primary evidence:** The endpoint quantifies over `bad`, but it also requires a new prefix-monotonicity proof and a new CE proof for that exact `bad`: `hmono` and `hCE` at `RandomSystems/SwitchingLemma.lean:1895–1899`, plus a per-schedule probability theorem at `:1900–1901`. CR18 Thm. 4.17 says “if … one can define an MBO such that `Ŝ |≡ T`,” not that every smaller/refined MBO preserves CE. Winning probability only decreases after an event-inclusion comparison is proved.
- **Safest replacement wording:** “For a fixed source/target pair, the MBO is a design variable **among prefix-monotone conditions that can be proved to establish CE**. Changing it reuses the theorem schema but creates fresh monotonicity, CE, and winning-probability obligations; a smaller event is not automatically a valid or tighter proof.”

### CE-09 — lines 64–67

- **Exact claim:** A loose bound can come from a loose MBO or a simulator whose good kernel is unnecessarily hard to match.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** This is diagnostic advice, not a theorem. It is compatible with the endpoint's two creative inputs (`hCE`, `hleaf`) at `SwitchingLemma.lean:1897–1901`.
- **Safest replacement wording:** “When diagnosing slack, inspect both the CE identity induced by the simulator and the probability charged by the chosen MBO.”

### CE-10 — lines 69–75

- **Exact claim:** MPR07 Lemma 5, source location printed pp. 140–142, and the four displayed properties including exact `δ_k^D`/winning-probability equality.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** The statement is on printed p. 140/PDF p. 11, and its construction/proof spans printed pp. 141–142/PDF pp. 12–13. All four properties are present verbatim in substance.
- **Safest replacement wording:** Keep, but call property (iii) “restricted equivalence of the masked systems (`Ŝ† ≡ T̂†` in MPR's notation)” so “pre-winning” is clearly an explanatory gloss.

### CE-11 — lines 77–81

- **Exact claim:** The MPR construction strips pointwise common transition mass, establishes symmetric exactness, and does not yield exact strict one-sided CR18 CE for a preselected `T`.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** MPR07 printed pp. 140–142/PDF pp. 11–13 defines the common part by minima of cumulative conditional masses (`m_{x^i,y^i} := min(p^S_{Y^i|X^i},p^T_{Y^i|X^i})`) and recursively chooses consistent residual parameters. Its conclusion is restricted equivalence between **two** enhanced systems. CR18 Def. 4.19 instead compares one enhanced system's `A_i=0` conditional law with the full ordinary law of `T`.
- **Safest replacement wording:** Existing wording is safe; replace “pointwise common transition mass” by “pointwise common cumulative response mass, assembled recursively into consistent transitions” for source-level precision.

### CE-12 — lines 83–92

- **Exact claim:** Four “valid moves” when a bound disappoints.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** These are design options inferred from the distinct source objects, not a complete theorem classification. The separation of CE (`CondEquiv.lean:118–122`), equivalence (`RandomSystem.lean:539–541`), and honest coupling (`Coupling.lean:45–53`) supports the terminology.
- **Safest replacement wording:** Prefix with “Possible redesign moves (each requires its own new proof obligations): …”.

### CE-13 — lines 94–102

- **Exact claim:** CE or the name “collision” supplies no rate; a concrete CE identity and a separate winning-probability bound are both required, including for a replacement condition.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** CR18 Thm. 4.17 ends at `Γ(bŜ)` (printed p. 110/PDF leaf 61), with no function of `q` or domain size. The packaged Lean endpoint takes arbitrary `ε : NNReal` and requires `hleaf` to prove the rate (`SwitchingLemma.lean:1896,1900–1902`). `seededHashCollision` itself is only the predicate at `:1916–1918`; monotonicity is separately proved at `:1927–1931`.
- **Safest replacement wording:** Existing wording is safe.

### CE-14 — lines 104–107

- **Exact claim:** The tree's ready-made predicates silently decide the constant; MBO search should be a fan-out task.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** This is workflow advice. A predicate alone does not mathematically determine a constant; the separate probability proof does.
- **Safest replacement wording:** “A ready-made predicate commits you to a particular CE/probability problem and may constrain the eventual constant; treat it as a candidate, not as evidence of the bound.”

### CE-15 — lines 109–112

- **Exact claim:** “There are two doors. Pick the packaged one”; Door 1 is “almost always right.”
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** This is routing advice. The current tree also has a history-aware packaged endpoint, `maxAdvantage_filterQueries_seededHistoryConditionCGame_le` at `RandomSystems/HistoryConditionC.lean:450–481`, so the binary presentation is not an exhaustive library taxonomy.
- **Safest replacement wording:** “Prefer the most specialized applicable packaged endpoint; use the raw theorem only when no packaged seeded/history-aware wrapper matches.”

### CE-16 — line 113

- **Exact claim:** `RandomSystems/SwitchingLemma.lean:1864` is the packaged endpoint location.
- **Verdict:** **STALE**.
- **Primary evidence:** The declaration now begins at `RandomSystems/SwitchingLemma.lean:1891`; line 1864 is an argument line of `seededConditionCGame_isProbDist`.
- **Safest replacement wording:** “`RandomSystems/SwitchingLemma.lean:1891` (search by declaration name; line numbers may drift).”

### CE-17 — lines 115–126

- **Exact claim:** The displayed signature of `maxAdvantage_filterQueries_seededConditionCGame_le`.
- **Verdict:** **OVERSTATED** as a purported complete signature; otherwise the displayed explicit arguments and conclusion are correct.
- **Primary evidence:** Current source at `SwitchingLemma.lean:1891–1902` has two material premises omitted by the excerpt: `[Nonempty I]` and `[∀ a l, Decidable (bad a l)]`, as well as implicit `{A I O : Type*}`. Every displayed explicit hypothesis and the conclusion match.
- **Safest replacement wording:** Mark the code “abridged signature” or include:

  ```lean
  theorem maxAdvantage_filterQueries_seededConditionCGame_le
      {A I O : Type*} [Nonempty I]
      (D : Dist A) (F : A → I → O) (bad : A → List I → Prop)
      [∀ a l, Decidable (bad a l)] ...
  ```

### CE-18 — lines 128–129

- **Exact claim:** The applicability test is a seed-indexed last-query function evaluator carrying a monotone bad bit.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** `seededConditionCGame` is exactly the pushforward of `a ↦ historyEvaluator (fun l h => (F a (l.getLast h), decide (bad a l)))` at `SwitchingLemma.lean:1835–1840`. The dedicated history-aware generalization explicitly says this wrapper covers a seed-indexed function evaluator, while stateful answers require another wrapper (`HistoryConditionC.lean:8–11`).
- **Safest replacement wording:** “Use this endpoint when the visible answer on a nonempty history is exactly `F a` applied to the last query; use the history-aware endpoint when the visible answer depends on the full history.”

### CE-19 — lines 129–131

- **Exact claim:** The endpoint “covers CBC-MAC, NMAC, the switching-lemma family, and most keyed constructions.”
- **Verdict:** **OVERSTATED**.
- **Primary evidence:** Current proved instantiations include CBC-MAC (`CBCMAC.lean:163–164`, endpoint use at `:1086–1092`), hash-then-URF (`SwitchingLemma.lean:2084–2089`, use at `:2193–2200`), and sum-of-permutations (`SumOfPermutations.lean:254–258`; tight route `SumOfPermutationsTight.lean:794–800`). No current NMAC security theorem instantiates this endpoint; NMAC appears only in comments/model definitions. “Most keyed constructions” is unbounded and contradicted by the need for `HistoryConditionC.lean` for stateful visible outputs.
- **Safest replacement wording:** “Current instantiations include CBC-MAC, seeded hash-then-URF, and sum-of-permutations. A random-outer NMAC hop has the same intended shape, but no completed NMAC endpoint in this tree was found.”

### CE-20 — lines 133–142

- **Exact claim:** The obligation table lists all hypotheses and their routine/creative classes.
- **Verdict:** **OVERSTATED**.
- **Primary evidence:** The six displayed explicit proof obligations do match `SwitchingLemma.lean:1895–1901`: `hmono`, `hCE`, `hD`, `hT`, `hTtot`, and `hleaf`. But the table omits `[Nonempty I]` and decidability of `bad` (`:1892–1894`). The `[ROUTINE]`/`[CREATIVE]` labels and suggested tactics are workflow classifications, not theorem facts. `cr18_prob` and `cr18_total` do exist (`CR18TacticsCore.lean:35`, `TotalityTactics.lean:43`) but are import/model dependent.
- **Safest replacement wording:** “Explicit theorem hypotheses are the six rows below, in addition to `[Nonempty I]` and decidability of `bad`; the ROUTINE/CREATIVE labels are proof-planning guidance.”

### CE-21 — lines 143–147

- **Exact claim:** `hleaf` sees `blindQueryList w q`, so the blind reduction has removed adaptivity and the counting layer gets a fixed list.
- **Verdict:** **VERIFIED**, with one precision qualification.
- **Primary evidence:** `hleaf` is exactly the per-blind-winner claim at `SwitchingLemma.lean:1900–1901`. `blindQueryList` is a fixed list extracted from `blindQueryVector` at `:795–820`; `isPrefix_blindQueryList` at `:822–830` moves any schedule-consistent run into that fixed list using monotonicity. CR18's proof, printed p. 110/PDF leaf 61, absorbs the target-copying system into the winner, making the winner blind to the live game. Lean formalizes this in `BlindAbsorption.lean:15–20` and `:673–705`.
- **Safest replacement wording:** “For each blind winner `w`, the counting leaf receives its fixed issued-query list `blindQueryList w q`; the proof must be uniform over all such `w`. The original adaptive distinguisher has been absorbed with the target reply process and no longer adapts to the monitored game's live replies.”

### CE-22 — lines 149–151

- **Exact claim:** The three support facts exist, are supplied inside the wrapper, and live at `SwitchingLemma.lean:1833–1858`.
- **Verdict:** **STALE**.
- **Primary evidence:** Names and internal use are correct: `seededConditionCGame_monotoneMBO` at `:1844–1852`, `seededConditionCGame_totalOnNonempty` at `:1855–1860`, `seededConditionCGame_isProbDist` at `:1863–1868`; they are passed at `:1908–1910`. The claimed range omits the probability theorem and includes the definition header instead.
- **Safest replacement wording:** “Supporting facts are `seededConditionCGame_monotoneMBO` (`:1844`), `..._totalOnNonempty` (`:1855`), and `..._isProbDist` (`:1863`); all are supplied in the wrapper.”

### CE-23 — line 155

- **Exact claim:** Raw theorem locations are `GameOf.lean:1343` (unfiltered), `:1359` (filtered `q+1`), and `:1383` (all `q`).
- **Verdict:** **VERIFIED**.
- **Primary evidence:** Those are the current declaration starts:
  - `maxAdvantage_le_blindMaxWinProb_of_deltaFiniteQueryNormalization`, `:1343`;
  - `maxAdvantage_filterQueries_le_blindMaxWinProb_of_deltaFilteredFiniteQueryNormalization`, `:1359`;
  - `..._all`, `:1383`.
- **Safest replacement wording:** Existing wording is safe; add declaration names to make it robust against future line drift.

### CE-24 — lines 157–164

- **Exact claim:** The displayed raw signature.
- **Verdict:** **VERIFIED** as an abridged rendering.
- **Primary evidence:** It matches `GameOf.lean:1343–1348`: `S`, `T`, `cond`, monotonicity, `isProbDist` twice, `TotalOnNonempty` twice, normalization, then the CE implication and `Δ ≤ Γᵇ` conclusion. The excerpt's `_` placeholders merely suppress the explicit `S`/`T` in the totality premises.
- **Safest replacement wording:** Label it “abridged current signature,” or copy the exact declaration.

### CE-25 — line 166

- **Exact claim:** “Seven hypotheses plus the conditional equivalence.”
- **Verdict:** **FALSE**.
- **Primary evidence:** The theorem at `GameOf.lean:1343–1348` has six non-CE hypotheses: `hcond`, `hS`, `hT`, `hStot`, `hTtot`, `hNorm`; then it takes the CE implication. `S`, `T`, and `cond` are data arguments, not hypotheses.
- **Safest replacement wording:** “Six side-condition hypotheses plus conditional equivalence (in addition to the three data arguments `S`, `T`, and `cond`).”

### CE-26a — line 167

- **Exact claim:** `Γᵇ` is a supremum “over adaptive blind winners.”
- **Verdict:** **FALSE**.
- **Primary evidence:** `IsBlind` requires a winner's query to depend only on reply-history length, not values (`RandomSystems/BlindConverter.lean:51–52`); `blindMaxWinProb` takes the supremum over blind-supported winner distributions (`:67–69`). Thus the winners are nonadaptive with respect to the live game. The *original* adaptive distinguisher is converted by target absorption (`BlindAbsorption.lean:15–20`).
- **Safest replacement wording:** “`Γᵇ` is the supremum over blind/nonadaptive winner distributions. The original adaptive distinguisher has already been absorbed with `T` into such a blind winner.”

### CE-26b — lines 166–168

- **Exact claim:** The raw door leaves the `Γᵇ` bound to the caller, while Door 1 discharges that extra obligation.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** The raw theorem concludes at `Γᵇ` (`GameOf.lean:1343–1348`). Door 1 bounds filtered `Γᵇ` using `blindMaxWinProb_filterQueries_monitored_le` at `SwitchingLemma.lean:1911–1913` and leaves only `hleaf`.
- **Safest replacement wording:** “The raw theorem leaves a separate blind-winning-probability bound; Door 1 packages it into the per-fixed-schedule `hleaf` premise.”

### CE-27 — lines 170–171

- **Exact claim:** Use raw Door 2 only when the real system is not a seeded evaluator, and explain why.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** It is sensible routing advice but not exhaustive. A non-last-query seeded system may fit the history-aware packaged endpoint at `HistoryConditionC.lean:450–481`; other specialized wrappers can also avoid raw `Γᵇ`.
- **Safest replacement wording:** “Use the raw theorem only after checking all applicable specialized wrappers (including the history-aware one), and document why none matches.”

### CE-28 — lines 175–189

- **Exact claim:** The skeleton has the right argument order and should compile before filling holes.
- **Verdict:** **VERIFIED** as an illustrative skeleton, assuming the omitted ambient typeclass premises and `my_game_ignoreMBO` are available.
- **Primary evidence:** The explicit argument order matches `SwitchingLemma.lean:1891–1902`. The concrete CBC proof uses the same structure at `CBCMAC.lean:1082–1094`.
- **Safest replacement wording:** Add a comment that `[Nonempty I]` and decidability of `bad` must already be in scope.

### CE-29a — lines 191–196

- **Exact claim:** `CBCMAC.lean` should be read only after independent routing/stages 1–3 because it is a worked instance, not a template.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** This is learning/workflow advice. The file is a genuine concrete instance, but no PDF or Lean declaration can establish the claimed optimal reading order.
- **Safest replacement wording:** “Workflow recommendation: route the problem and inventory its obligations before consulting `CBCMAC.lean`, then use it as a concrete instance rather than copying scheme-specific lemmas.”

### CE-29b — lines 195–196

- **Exact claim:** Reading the CBC instance first “is exactly what happened when this skill was first tested.”
- **Verdict:** **OVERSTATED**.
- **Primary evidence:** This anecdotal process claim has no primary-paper or Lean-source receipt and is not independently auditable from the requested sources.
- **Safest replacement wording:** Remove the anecdote, or link a dated test record that directly supports it.

### CE-29c — lines 193–200

- **Exact claim:** `CBCMAC.lean` proves the randomness-expander bound through this endpoint in a three-hop `calc`.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** `cbc_mac_randomness_expander` is at `RandomSystems/CBCMAC.lean:1076–1094`. Its `calc` (1) rewrites with `cbcGame_ignoreMBO`, (2) invokes `maxAdvantage_filterQueries_seededConditionCGame_le`, and (3) applies `pairCollisionUnionBound_le_birthday`. The file compiles in the focused check.
- **Safest replacement wording:** Existing wording is safe.

### CE-30 — lines 198–201

- **Exact claim:** The CBC proof has “exactly two scheme-specific inputs,” CE and fixed-schedule bad mass; everything else is a citation.
- **Verdict:** **OVERSTATED** unless “inputs” is explicitly restricted to **creative** obligations.
- **Primary evidence:** The endpoint call at `CBCMAC.lean:1086–1092` also consumes scheme-specific monotonicity `cbcBad_monotone`; the proof's first hop consumes `cbcGame_ignoreMBO`; the construction itself and prefix-freeness are scheme-specific. The two substantial mathematical leaves are indeed `cbc_condEquiv` (`:931–949`) and `mass_cbcBad_le` (`:694–697`).
- **Safest replacement wording:** “The endpoint leaves two scheme-specific **creative** inputs—`cbc_condEquiv` and the fixed-schedule `mass_cbcBad_le`; monotonicity, strip identity, and standing facts are additional scheme-specific but routine cited lemmas.”

### CE-31a — lines 203–207, 210–211

- **Exact claim:** Every instance of this packaged endpoint supplies a CE identity and a fixed-schedule bad-mass bound.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** Those are precisely `hCE` at `SwitchingLemma.lean:1897` and `hleaf` at `:1900–1901`.
- **Safest replacement wording:** “This endpoint's two non-generic mathematical obligations are the exact CE identity and a bad-mass bound uniform over blind fixed schedules.”

### CE-31b — lines 206–209

- **Exact claim:** For a keyed cascade, the CE proof is “typically” a group-action/re-randomization/fiber-balance argument.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** CBC's CE proof really does close with a balanced-fiber count (`CBCMAC.lean:922–949`), but this single instance does not establish a theorem that keyed cascades generally admit such an action.
- **Safest replacement wording:** “In CBC-MAC, the CE leaf is discharged by a balanced-fiber argument. Other constructions need their own exact conditional-law proof; a group action is one possible method, not a guaranteed template.”

### CE-32 — lines 215–217

- **Exact claim:** `CondEquiv.lean` defines `|≡` in guarded cross-multiplied, division-free form; `TotalOnNonempty` is at line 96.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** `TotalOnNonempty` is `CondEquiv.lean:96–97`. `CondEquiv` is `:118–122`, guarded by nonzero `massAfalse` and `massDom` normalizers and expressed as a product equality. The source contains no `DecidableEq` premise for the relation.
- **Safest replacement wording:** Existing wording is safe; optionally add the definition start `:118`.

### CE-33 — lines 218–219

- **Exact claim:** `condEquiv_filterDom` at `:203` and `condEquiv_filterQueries` at `:237` preserve CE.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** Exact current declarations are `CondEquiv.lean:203–205` and `:237–240`.
- **Safest replacement wording:** Existing factual wording is safe. “Never re-prove” is workflow advice, not part of the theorem.

### CE-34 — line 220

- **Exact claim:** `RandomSystems/GameOf.lean` contains `gameOf`, `Γᵇ`, and the blind machinery.
- **Verdict:** **OVERSTATED** as a location claim.
- **Primary evidence:** `gameOf` is defined in `GameOf.lean:988`, and that file contains the Thm. 4.17 bridge. But `IsBlind` and `blindMaxWinProb`/`Γᵇ` are defined in `RandomSystems/BlindConverter.lean:51–69`; absorption is in `BlindAbsorption.lean`.
- **Safest replacement wording:** “`GameOf.lean` — `gameOf` and Thm. 4.17 endpoints; `BlindConverter.lean` — `IsBlind` and `Γᵇ`; `BlindAbsorption.lean` — adaptive-distinguisher absorption.”

### CE-35 — lines 221–222

- **Exact claim:** `CBCStructureGraph.lean` is a route to the same CBC bound “with a tolerant CE and a full counting engine.”
- **Verdict:** **FALSE**.
- **Primary evidence:** The tolerant CE declaration exists and is proved at `CBCStructureGraph.lean:317–333`. However the central count `mass_cbcGraphBad_le` is explicitly `sorry` at `:1423–1428`, and its own docstring says it is the sole remaining obligation and that the stated constant is not reached by the present descriptor union (`:1409–1422`). Downstream `blindMaxWinProb_cbcGraphGame_le` and `cbc_mac_beyond_birthday` depend on it (`:1435–1461`). A focused `lake env lean` also fails at multiple earlier migrated APIs, so the file is not currently build-clean.
- **Safest replacement wording:** “`CBCStructureGraph.lean` — experimental tolerant-CE route. The CE lemma is present, but the counting endpoint is admitted and the file currently does not compile; do not cite it as a completed bound.”

### CE-36 — lines 223–224

- **Exact claim:** `seededHashCollision` is at `SwitchingLemma.lean:1889`, with a monotonicity theorem, and is reusable.
- **Verdict:** **STALE**.
- **Primary evidence:** `seededHashCollision` now starts at `SwitchingLemma.lean:1916`; `seededHashCollision_monotone` starts at `:1927`. It is used in the hash-then-URF wrapper at `:2087–2089` and the sum-of-permutations route.
- **Safest replacement wording:** “`seededHashCollision` (`SwitchingLemma.lean:1916`) and `seededHashCollision_monotone` (`:1927`) are the reusable fixed-list hash-collision predicate and monotonicity lemma.”

### CE-37 — lines 228–229

- **Exact claim:** If `Γᵇ` is in the goal, “you are on Door 2.”
- **Verdict:** **OVERSTATED**.
- **Primary evidence:** Door 1's own proof has an intermediate `Γᵇ` goal at `SwitchingLemma.lean:1903–1913`, and public specialized `Γᵇ` lemmas are legitimate probability-layer endpoints. What is true is that a **final user obligation** to prove raw `Γᵇ` often indicates the specialized wrapper was not applied.
- **Safest replacement wording:** “If your top-level scheme proof is left with a raw `Γᵇ` goal, check whether a packaged seeded/history-aware endpoint can replace that manual step.”

### CE-38 — lines 231–233

- **Exact claim:** `hCE` is an equality, not a bound; the residual difference is charged by `Γᵇ`/`hleaf`.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** `CondEquiv` is a cross-multiplied equality at `CondEquiv.lean:118–122`. The packaged endpoint uses CE for the first `Δ ≤ Γᵇ` hop and `hleaf` for `Γᵇ ≤ ε` at `SwitchingLemma.lean:1903–1913`.
- **Safest replacement wording:** Existing wording is safe.

### CE-39 — lines 235–236

- **Exact claim:** An MBO must be monotone; an event that can un-fire is not an MBO.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** CR18 Def. 3.22, printed p. 71/PDF leaf 42, requires `a_i=1 → a_j=1` for all `j≥i`. The packaged theorem requires prefix-monotonicity at `SwitchingLemma.lean:1895` and derives `MonotoneMBO` at `:1908`.
- **Safest replacement wording:** Existing wording is safe.

### CE-40 — line 237

- **Exact claim:** If an event can un-fire, strengthen it to its monotone closure.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** Monotone closure makes a candidate condition monotone, but neither CR18 nor Lean says it preserves CE or gives an acceptable probability. Those obligations must be reproved for the closure.
- **Safest replacement wording:** “A monotone closure is a possible replacement MBO, but it creates a new CE identity and winning-probability obligation and may loosen the bound.”

### CE-41 — lines 239–241

- **Exact claim:** The `ignoreMBO` rewrite is library-supplied and “every construction in the tree has one.”
- **Verdict:** **OVERSTATED**.
- **Primary evidence:** There is a generic strip theorem for the seeded wrapper at `SwitchingLemma.lean:1874–1885` and instance lemmas such as `cbcGame_ignoreMBO` at `CBCMAC.lean:1047–1058` and `cbcGraphGame_ignoreMBO` at `CBCStructureGraph.lean:273–283`. This does not establish the universal claim for every game construction, and a genuinely new construction may still need an instance equation.
- **Safest replacement wording:** “Search first for a generic or instance-specific `ignoreMBO` lemma. The seeded and major current instances have one; a new construction may need to prove its own strip identity.”

## Claim-by-claim audit: `creative-search.md` lines 31–58

### CS-01 — lines 31–38

- **Exact claim:** After fixing source and simulator, the MBO is “a free parameter among the conditions that actually establish strict conditional equivalence,” and its winning probability is the resulting CR18 bound.
- **Verdict:** **VERIFIED**, with “free” understood only in the explicitly qualified design-variable sense.
- **Primary evidence:** CR18 Thm. 4.17, printed p. 110/PDF leaf 61, accepts any MBO enhancement satisfying `Ŝ |≡ T` and bounds by that game's blind winning probability. The current endpoint makes the exact additional constraints explicit: decidability, prefix-monotonicity, CE, probability/totality, and the winning-probability leaf (`SwitchingLemma.lean:1891–1902`).
- **Safest replacement wording:** “After fixing the source and target, the MBO is a **candidate design variable**, constrained by monotonicity and a fresh strict-CE proof; the separately proved blind winning probability yields the upper bound.”

### CS-02 — lines 40–45

- **Exact claim:** CE imposes no birthday or other asymptotic rate; `q²/N`, `q³/N²`, etc. arise only from a separate analysis of the particular winning probability.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** CR18 Thm. 4.17's conclusion is only `Δ(S,T) ≤ Γ(bŜ)` (printed p. 110/PDF leaf 61). Lean's generic theorem has arbitrary `ε` and requires `hleaf` to supply it (`SwitchingLemma.lean:1896,1900–1902`). The CBC birthday rate is introduced only by `mass_cbcBad_le` and `pairCollisionUnionBound_le_birthday` (`CBCMAC.lean:1085–1094`).
- **Safest replacement wording:** Existing wording is safe.

### CS-03 — lines 47–53

- **Exact claim:** Changing the MBO or simulator creates new CE/probability obligations; a smaller bad event alone proves nothing; strict CE is distinct from symmetric games, H bad sets, couplings, and representative selection.
- **Verdict:** **VERIFIED**.
- **Primary evidence:** The exact MBO occurs in both `hCE` and `hleaf` (`SwitchingLemma.lean:1897–1901`), so changing it changes both propositions. Strict CE (`CondEquiv.lean:118–122`), representative equivalence (`RandomSystem.lean:539–541`), and honest coupling (`Coupling.lean:45–53`) are separate declarations. MPR07 Def. 10/Lemma 5 (printed pp. 138, 140–142/PDF pp. 9, 11–13) uses symmetric restricted equivalence instead.
- **Safest replacement wording:** Existing wording is safe; add “and monotonicity” to the list of renewed obligations.

### CS-04 — lines 55–57

- **Exact claim:** Stage 1 must be Lean-free/high-freedom; a ready-made predicate is only a candidate, not evidence.
- **Verdict:** **NORMATIVE-NOT-FACTUAL**.
- **Primary evidence:** The first clause is process policy. The second is logically sound: neither `seededHashCollision` (`SwitchingLemma.lean:1916–1918`) nor any predicate name supplies the endpoint's `hCE` and `hleaf` premises.
- **Safest replacement wording:** “Workflow rule: keep the initial mathematical exploration independent of the available predicates. Treat any library predicate as a candidate until its CE and probability obligations are identified.”

## Recommended minimal corrections

The highest-priority edits, if the skill is later revised, are:

1. Qualify every “free MBO” statement: a changed MBO requires new monotonicity, CE, and probability proofs.
2. Replace “adaptive blind winners” by “blind/nonadaptive winners obtained by absorbing the original adaptive distinguisher with the target reply process.”
3. Fix current source locations: endpoint `SwitchingLemma.lean:1891`; support facts `:1844`, `:1855`, `:1863`; `seededHashCollision` `:1916` and monotonicity `:1927`.
4. Add the hidden endpoint premises `[Nonempty I]` and decidability of `bad`; correct “seven hypotheses” to six side conditions plus CE in the raw theorem.
5. Downgrade `CBCStructureGraph.lean` to an incomplete/non-build-clean experimental route; do not call it a full counting engine.
6. Narrow the endpoint coverage claim to formalized users (CBC-MAC, hash-then-URF, sum-of-permutations) and point stateful-output constructions to `HistoryConditionC.lean`.
7. Split the related-source pointer across `GameOf.lean`, `BlindConverter.lean`, and `BlindAbsorption.lean`.
