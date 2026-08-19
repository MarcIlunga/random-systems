# Independent audit of `random-systems-proofs`: core and planning guide

Status: **COMPLETE INDEPENDENT AUDIT**  
Audit date: 2026-08-06  
Repository snapshot: current working tree at `236fbcd453baaced942850f31f2e1a604c81d932` (the tree is dirty; all findings below describe the files actually present, not the clean commit alone).

## Scope and method

This report audits every substantive applicability, theorem, library, tactic, workflow-status, and empirical claim in:

- `/Users/marcilunga/.codex/skills/random-systems-proofs/SKILL.md`, including its frontmatter;
- `/Users/marcilunga/.codex/skills/random-systems-proofs/references/sketch-and-plan.md`;
- `/Users/marcilunga/.codex/skills/random-systems-proofs/agents/openai.yaml`.

The other referenced guides were checked only far enough to verify the navigation descriptions in `SKILL.md`; their internal claims are outside this report. I did not use the audited skill as authority. Lean claims were checked against current declarations and, where useful, by focused compilation or deliberately failing probes. Claims attributed to Lanzenberger's thesis or Maurer's CR18 lecture notes were checked against the primary PDFs.

Labels mean:

- **VERIFIED** — supported as stated, with the stated or obvious hypotheses.
- **OVERSTATED** — has a sound scoped core, but its quantifier, causal wording, completeness claim, or omitted hypotheses make the sentence unsafe.
- **FALSE** — contradicted by a source, theorem signature, or reproducible counterexample/probe.
- **STALE** — may describe an earlier tree, but not the current build or inventory.
- **UNVERIFIED** — no reproducible evidence was supplied or found for an empirical or causal claim.
- **NORMATIVE** — a proposed workflow/style rule, not a fact forced by Lean or the mathematics.

The audit treats words such as “every,” “always,” “never,” “exactly,” “must compile,” and “routine” as real quantifiers, not emphasis.

## Executive verdict

The skill's central source-level facts are mostly sound: transcript laws are pushforwards; one-sided distance is asymmetric at unequal weight; the repository's `Adv S T` corresponds to raw `Δ(T,S)` under non-negativity; CR18 conditional equivalence has the stated one-sided conditioned-law shape; and the named H, CE, coupling, and counting infrastructure largely exists.

The current text is nevertheless unsafe as an operational skill. Its most consequential errors are:

1. It presents a heuristic taxonomy as a closed and exhaustive theorem about all repository proofs.
2. It treats finite tactic bundles as decision procedures and says tactic failure proves a modeling error. Two small Lean probes refute this directly.
3. Its advertised stage-4 skeleton cannot type-check: the cited endpoint concludes `Adv[q](S,T)`, while the example goal is raw filtered `Δ`.
4. It says every packaged endpoint has already removed adaptivity and hands over a fixed schedule. That is specific to the blind-game CE route, not H, coupling, winnability, or every endpoint.
5. It omits normalization/shared-domain hypotheses from metric claims.
6. It overstates what the SequenceHash dispatch script enforces: the script checks that a sentence is present in a preamble, not that the resulting sketch follows it.
7. Two advertised surfaces are presently stale: `RandomSystems.HTechnique.Tactics` and `RandomSystems.LanzenbergerChain` do not fresh-build in the current tree.

The safe repair is not to discard the workflow. It is to identify policy as policy, scope theorem claims to named declarations and hypotheses, remove claims of tactic completeness, and replace universal route language with explicit heuristics.

## Primary-source checks

| Claim checked | Verdict | Evidence and conservative reading |
|---|---|---|
| One-sided statistical distance is asymmetric for unequal weights. | **VERIFIED** | `papers/thesis (1).pdf`, printed p. 12, Definition 2.4 and its following remark. |
| Data processing for an `f`-transformation is Lemma 2.7. | **VERIFIED** | `papers/thesis (1).pdf`, printed p. 13, Lemma 2.7. The current Lean analogue is `RandomSystems/RandomSystem.lean:161-166`, with non-negativity of the second law explicit. |
| `Adv` and class distance occur as Definitions 2.26 and 2.28; Theorem 2.31 bounds advantage by class distance. | **VERIFIED** | `papers/thesis (1).pdf`, printed pp. 18, 20, and the proof on printed p. 22. The analytic step is DPI, but the complete theorem also performs supremum/infimum bookkeeping. |
| CR18 Definition 4.19 is one-sided conditional equivalence between an MBO-enhanced system and a plain target. | **VERIFIED** | `papers/CR18_LN.pdf`, printed p. 108. Current Lean definition: `RandomSystems/CondEquiv.lean:101-124`. It is not representative selection and not a coupling. |
| CR18's blind game is nonadaptive and Theorem 4.17 bounds advantage by blind winning probability. | **VERIFIED** | `papers/CR18_LN.pdf`, printed pp. 109-110. Current packaged filtered endpoint: `RandomSystems/GameOf.lean:1416-1459`. “Blind” supports a fixed query schedule for this reduction, not a universal claim about every technique. |

## Audit of `SKILL.md`

### Metadata, scope, and advertised workflow

| Lines | Claim unit | Label | Evidence / reasoning | Conservative action |
|---:|---|---|---|---|
| 1-4 | The package is named `random-systems-proofs`. | **VERIFIED** | Matches the directory name and `$random-systems-proofs` prompt. | Keep. |
| 3 | Use it for **ANY theorem** in either `RandomSystems` or `RandomSystemsCC`. | **OVERSTATED** | The same file excludes pure definitions and CC/AC layer questions at lines 87-93. Both libraries contain many statements that are not security-bound proofs. | Replace “ANY theorem” with “security-bound theorems and their supporting RS lemmas.” |
| 3 | The useful technique menu includes H-technique, conditional equivalence, coupling, winnability, and counting. | **VERIFIED** | Named declarations/modules exist for all five. This verifies availability, not exhaustiveness or current build health. | Keep, adding “among others” and current status caveats. |
| 3 | The skill “picks” the technique and determines the finished proof shape. | **NORMATIVE** | This is the intended service contract, not a theorem or automated guarantee. | Keep as an aspiration, phrased “helps choose.” |
| 8-15 | An independent audit is in progress and theorem/terminology claims must be rechecked. | **VERIFIED** | This report is that audit; the warning accurately separates CE, symmetric games, representatives, coupling, and H-technique. | Keep until corrections land, then replace with a dated audit link. |
| 17 | Every security statement in the library is an advantage bound. | **FALSE** | The libraries also contain equivalence, totality, probability, coupling existence, structural, simulation, metric, and construction theorems. Even security-relevant statements need not syntactically be a bound. | Delete; replace with “Most headline indistinguishability results are expressed as advantage or distance bounds.” |
| 18 | The library uses a **closed set of seven** technique families. | **FALSE** | No Lean theorem or registry closes the proof-method space. The document itself includes arithmetic/counting as phases and allows new infrastructure. `skills/PROOF-WORKFLOWS.md` records a proposed taxonomy, not mathematical exhaustiveness. | Replace “closed set” with “current routing checklist.” |
| 18-20 | Proof shape is knowable before attempting the proof. | **OVERSTATED** | Existing endpoints often expose obligations in advance; novel reductions, modeling discoveries, or missing bridges can change the shape. | Replace with “For an existing packaged endpoint, its explicit hypotheses determine an initial obligation list.” |
| 22-34 | Six stages and their gates are required. | **NORMATIVE** | Neither Lean nor repository tooling enforces them. Lines 70-73 say so explicitly. | Keep only as workflow policy and call it “recommended/default,” unless project owners intentionally mandate it in `AGENTS.md`. |
| 36-40 | Starting with Lean/library search is the rule agents break most and has a measured failure cost. | **UNVERIFIED** | No reproducible corpus, denominator, or measurement protocol is given. | Rephrase as experience-based guidance; omit “most” and “measured.” |
| 42-48 | Searching before sketching anchors the proof and causes loose bounds. | **NORMATIVE** | Plausible methodology advice, but causal and not universally true; source inspection can reveal available exact endpoints and prevent reinventing false models. | Present as a risk, not a rule against all early source reading. |
| 50-53 | Missing infrastructure is expected and definitions/lemmas may be added “freely.” | **OVERSTATED** | Repository ownership, API compatibility, dependencies, and existing abstractions constrain changes. `AGENTS.md` says to search and reconsider after failed fixes; it does not authorize indiscriminate public framework changes. | Replace “freely” with “when justified, after reuse and ownership checks.” |
| 55-65 | The freedom table accurately states what Lean permits at each stage. | **NORMATIVE** | It is a process allocation, not a verified property. A stage-4 skeleton can require creative elaboration or bridge work. | Keep as guidance, remove “must compile” as a factual guarantee. |
| 67-68 | `sketch-and-plan.md` contains stages 1-3. | **VERIFIED** | Its headings are Stage 1, Stage 2, and Stage 3. | Keep. |
| 70 | Nothing mechanically enforces the workflow. | **VERIFIED** | There is no goal-shape tactic/typeclass/hook enforcing these six stages. The SequenceHash dispatch wrapper enforces only preamble inclusion. | Keep. |
| 71-73 | A two-dispatch, 67-tool-call run produced no sketch after the guide was read. | **UNVERIFIED** | A narrative is recorded at `skills/PROOF-WORKFLOWS.md:536-567`, but this audit found no reproducible trace and the description/table are not a controlled measurement. | Mark explicitly as an anecdote or delete. |
| 75-78 | A persisted sketch is the only reviewable/reusable reasoning artifact. | **OVERSTATED** | A proof, comments, paper note, design document, or recorded transcript can also be reviewable. | Replace “only” with “a useful persistent artifact.” |
| 80-86 | The skill is appropriate for RS security bounds, repairs, route selection, and slack review. | **VERIFIED** | This matches the available infrastructure and package purpose. | Keep. |
| 87-93 | The listed exclusions delimit the intended scope. | **NORMATIVE** | Sensible routing policy, but it contradicts frontmatter's “ANY theorem” and the skill can still help with supporting algebra. | Keep after reconciling frontmatter; say “usually not needed.” |

### Routing and obligation classification

| Lines | Claim unit | Label | Evidence / reasoning | Conservative action |
|---:|---|---|---|---|
| 97-110 | The routing tree is exhaustive and its numbered items are technique families. | **OVERSTATED** | It is a useful heuristic. Counting and arithmetic are discharge phases, not alternatives at the same semantic level; new reductions and exact arguments can cross categories. | Title it “routing heuristic”; remove implications of closure. |
| 98 | Exact zero should be checked before accepting a positive bound. | **NORMATIVE** | Good optimization advice, not a theorem that it is always the cheapest first check. | Keep as “check when plausible.” |
| 101-107 | Bad transcript → H, triggered condition → CE, disagreement → coupling, winning → winnability. | **OVERSTATED** | These describe canonical proof objects, but the same mathematics can admit multiple routes. A CE condition may depend on hidden system randomness; it need not literally be “triggered by the adversary.” | Replace arrows with “often suggests.” Define CE using the MBO-conditioned law. |
| 114-118 | Exactness/family-II omissions are the most common failures in the repository. | **UNVERIFIED** | No auditable issue sample or count is supplied. | Recast as “common risks observed by maintainers.” |
| 120-121 | A sketch must name a rejected technique or it has not selected one. | **NORMATIVE** | Useful comparison discipline, but not mathematical necessity when there is only one plausible route. | Keep as a default template field, allow “no serious alternative.” |
| 125-130 | The quoted §9 route warning appears in `CHEATSHEET.md`. | **VERIFIED** | The quoted text is present at `CHEATSHEET.md:496-497`. | Keep, but scope it to the layer covered by that warning. |
| 131 | A module is architected for one route. | **OVERSTATED** | Some files expose several endpoints or bridge routes; architecture is not a one-route invariant. | Replace with “A theorem or local API may already privilege one route.” |
| 131-133, 394-397 | A CE-architected theorem was proved through H with about 90 lines of glue and no new mathematics. | **UNVERIFIED** | `skills/PROOF-WORKFLOWS.md:536-547` records this as a project observation, but no controlled reproduction or stable diff is identified here. | Label as a dated case study with exact commit/file, or omit the number. |
| 135-138 | Existing file architecture must be part of routing; going against it accidentally is never right. | **NORMATIVE** | Useful engineering advice; “never” is rhetorical, not a verifiable law. | Keep without the universal word. |
| 142 | Every endpoint hypothesis falls into exactly `[LIB]`, `[ROUTINE]`, or `[CREATIVE]`. | **NORMATIVE** | These are workflow labels imposed by the author. A hypothesis can be partly automated, blocked by imports, or require adaptation; classification is contextual. | Say “Classify each node provisionally into one of…” |
| 146 | A `[LIB]` fact must never be reproved. | **OVERSTATED** | Reuse is preferred, but a wrapper, stronger theorem, namespace boundary, or dependency constraint can justify another result. | Replace “Never” with “Prefer citing or generalizing the existing theorem.” |
| 147, 170-173 | A `[ROUTINE]` tactic is guaranteed to close its goal; failure proves a modeling bug. | **FALSE** | `cr18_total` and `cr18_prob` are finite tactic bundles, not complete procedures. `review/random-systems-skill/audit-probes/TotalityIncompletenessProbe.lean` gives goals already proved by `cbcReal_totalOnNonempty` and `cbcReal_isProbDist`; `cr18_total` and `cr18_prob` respectively fail. | Replace with “On failure, check imports and model first, then inspect the tactic's registered surface and use the named theorem if needed.” |
| 150 | If all nodes are creative, routing is wrong. | **FALSE** | A genuinely new theorem can require only new mathematical nodes even when the best existing endpoint is correctly selected. | Replace with “Recheck for a missing packaged endpoint.” |

### Tactic and skeleton claims

| Lines | Claim unit | Label | Evidence / reasoning | Conservative action |
|---:|---|---|---|---|
| 156 | `cr18_total` and `htechnique_total` discharge arbitrary `KStepTotal` / `TotalOnNonempty` goals. | **OVERSTATED** | `RandomSystems/TotalityTactics.lean:43-59` enumerates specific constructors and an Aesop rule set. `RandomSystems/HTechnique/Tactics.lean:79-89` adds SoP and PRP specializations. The probe above exhibits a named totality fact they do not discover. | Say “try standard registered constructors.” |
| 157 | `cr18_prob` discharges `isProbDist`. | **OVERSTATED** | `RandomSystems/CR18TacticsCore.lean:35-44` is only `simp only` over a fixed list. It fails on `cbcReal` although `cbcReal_isProbDist` exists. | Say “normalizes the registered standard probability constructors.” |
| 158 | `cr18_routine` discharges standing side conditions. | **OVERSTATED** | It is a finite `first` over `grind`, arithmetic, algebra, and pushforward simplification (`CR18TacticsCore.lean:130-139`). No completeness property is proved. | Replace “discharges” with “tries.” |
| 159 | `cr18_filter`, `cr18_game`, and `cr18_transcript` exist in `CR18Tactics`. | **VERIFIED** | Definitions occur at `RandomSystems/CR18Tactics.lean:22-57`. | Keep, describe them as rewrite bundles rather than guaranteed solvers. |
| 160 | `htechnique_compress` handles repeated queries generically. | **OVERSTATED** | Its rewrite list is SoP-specific (`RandomSystems/HTechnique/Tactics.lean:45-51`). | Say “compresses the registered SoP transcript-law forms.” |
| 161 | `htechnique_adv_le` applies the named advantage shells. | **VERIFIED** | `RandomSystems/HTechnique/Tactics.lean:68-74` tries PRF, PRP, `Adv`, fixed-query, then the core shell. | Keep with the build-status caveat below. |
| 162 | `cr18_arith`, `cr18_algebra`, and `cr18_close` are arithmetic/game closers. | **VERIFIED** | They exist as finite tactic bundles in `CR18TacticsCore.lean:68-99` and `CR18Tactics.lean:72-78`. | Replace categorical “discharges” with “tries.” |
| 163 | `FiniteTranscriptSpace` and `DiscreteTranscriptSpace` are inferred instances. | **OVERSTATED** | The names are only abbreviations for `Fintype` and `DecidableEq` (`RandomSystems/CR18Names.lean:35-49`). `inferInstance` succeeds only when carrier instances are derivable. | Say “use `inferInstance` when the corresponding carrier instances are in scope.” |
| 165 | These tactics are not globally available; their defining module must be imported. | **VERIFIED** | `CBCImportProbe.lean`, importing only `RandomSystems.CBCMAC`, reports `cr18_total` as unknown. | Keep. |
| 166 | `CBCMAC.lean` imports none of the tactic modules. | **FALSE** | It does not import `TotalityTactics`, hence lacks `cr18_total`, but it receives core tactics transitively and uses `cr18_algebra`. | Replace with the precise `TotalityTactics` statement. |
| 167-168 | Missing tactics may be solved by adding the import or proving the obligation explicitly. | **NORMATIVE** | Both are legitimate engineering options subject to dependency policy. | Keep without implying that import is always desirable. |
| 177-186 | The displayed stage-4 skeleton compiles for a raw filtered-`Δ` goal. | **FALSE** | `adv_le_of_fixedQuery_eq_on_good` concludes `Adv[q](S,T) ≤ δb` (`RandomSystems/HTechnique/Derivation.lean:439-447`), not `Δ(⌈q⌉ Real,⌈q⌉ Ideal)`. The missing bridge is `filteredDelta_le_Adv` (`HTechnique/SecurityDefs.lean:127-139`) plus its normalization hypothesis. Lines 214-217 later show the correct `Δ → Adv` hop. | Replace the example with a `calc` using `filteredDelta_le_Adv`, or change the theorem goal to `Adv[q](Real,Ideal)`. |
| 188 | Lean does not check that a user-written DAG listed every generated obligation. | **VERIFIED** | No such checker exists in the skill or library. | Keep. |
| 189-194 | A skeleton mismatch/compile failure has only three possible causes: wrong bound, wrong endpoint, or unavailable routine hypothesis. | **FALSE** | Syntax, namespaces, implicit arguments, coercions, missing imports, stale oleans, migrated carrier types, and actual library defects are additional causes. | Replace with a non-exhaustive diagnostic list. |
| 196-198 | A measured exception says all-`[LIB]` DAGs should skip the skeleton. | **UNVERIFIED** | No reproducible measurement is linked. This is a style preference. | Mark as optional advice. |

Current build status matters to the tactic table:

- `lake build RandomSystems.CR18Tactics RandomSystems.TotalityTactics RandomSystems.HTechnique.Derivation` succeeds.
- `lake build RandomSystems.HTechnique.Tactics` fails through `RandomSystems/HTechnique/SoP/VisibleLaw.lean`, beginning with current `ℝ`/`NNReal` mismatches at lines 85, 99, and 118 and several `sorry` warnings. Therefore the H tactic source exists, but the advertised import surface is **STALE** as a fresh-build recommendation.

### Proof presentation and source discovery

| Lines | Claim unit | Label | Evidence / reasoning | Conservative action |
|---:|---|---|---|---|
| 200-239 | Top-level `calc`, named creative facts, named bad events, visible variants, and hoisted plumbing are mandatory proof shapes. | **NORMATIVE** | These are readability conventions, not logical or Lean requirements. They are reasonable project style if adopted explicitly. | Keep as style guidance and replace “must/never” with project-policy language. |
| 206-208 | A CBC H proof hid one of five analyses in nested `le_trans`. | **UNVERIFIED** | No stable file/commit/diff is cited in this text. | Cite the exact artifact or present as a hypothetical anti-pattern. |
| 214-217 | The mathematically correct H assembly has a `Δ → Adv → bad mass → headline` chain. | **VERIFIED** | `filteredDelta_le_Adv` supplies the first hop; the H endpoints supply the second; arithmetic supplies the third, under their explicit hypotheses. | Keep and make this the canonical skeleton. |
| 241-244 | `ControlledNaturalLanguage.lean` “renders” H proofs as paper prose. | **OVERSTATED** | `RandomSystemsCC/ControlledNaturalLanguage.lean:196-246` defines prose-shaped syntax macros that elaborate to theorem applications and named goals. It does not render an arbitrary proof into prose. | Replace “renders” with “provides prose-shaped syntax for writing.” |
| 248-252 | `CHEATSHEET.md` is a goal-organized reuse index. | **VERIFIED** | File and cited route warning exist. “Always first” is workflow policy, not a theorem. | Keep with policy wording. |
| 253 | `LanzenbergerChain.lean` has one row for every numbered item in Chapter 2. | **OVERSTATED** | It is a curated cross-reference for many major definitions and lemmas, but not a literal row for every numbered item (for example, not all elementary definitions/lemmas have explicit rows). | Replace with “curated cross-reference for major Chapter 2 items.” |
| 253 | `LanzenbergerChain.lean` currently does not compile due to an unfinished signed-carrier migration. | **VERIFIED** | `lake build RandomSystems.LanzenbergerChain` fails in imported `RandomSystems/GameWinnability.lean` and `RandomSystems/MultiSystemCoupling.lean` with many `ℝ`/`NNReal` errors and `sorry` warnings. | Keep, naming the actual failing imports. |
| 253 | Only items “behind `BoundedAttainment`” are unauditable. | **OVERSTATED** | `BoundedAttainment` itself builds in the attempted chain; failures occur later in multiple imports. Source declarations can still be inspected even if the aggregate module fails. | Replace with a per-module build-status statement. |
| 253 | An agent twice missed `behavior_equivalent_iff_transcript_equivalent`. | **UNVERIFIED** | The theorem exists at `RandomSystems/RandomSystem.lean:839-842`; the asserted agent history is not reproducible from the skill. | Retain only the theorem lookup example, not the count. |
| 254-258 | The listed grep and Lean-search/verification tools exist. | **VERIFIED** | The repository configures `lean-lsp`; the current tool surface includes local search, state search, Loogle, LeanSearch, LeanFinder, premise search, and verification. | Keep. |
| 260-262 | Preferred iteration is goal-state inspection, then single-file `lake env lean`, reserving full builds for gates. | **NORMATIVE** | It agrees with current `AGENTS.md`; it is repository policy rather than a mathematical claim. | Keep. |

### Mathematical modeling claims

| Lines | Claim unit | Label | Evidence / reasoning | Conservative action |
|---:|---|---|---|---|
| 268-269 | `transcriptDist` is a deterministic pushforward of the source law. | **VERIFIED** | Definition is exactly `Dist.fTransform ... S` at `RandomSystems/RandomSystem.lean:497-503`. | Keep. |
| 269-270 | `δ_fTransform_le` is the data-processing lemma corresponding to thesis Lemma 2.7. | **VERIFIED** | Primary thesis printed p. 13; Lean declaration `RandomSystem.lean:161-166`, requiring non-negativity of the second law. | Keep with the hypothesis visible. |
| 274 | Theorem 2.31's easy half is “one DPI application.” | **OVERSTATED** | The key analytic inequality is one DPI application, confirmed by the thesis proof and Lean line 8374. The complete result also rewrites equivalent representatives and performs `sInf`/`sSup` bookkeeping (`RandomSystem.lean:8366-8376`). | Say “its analytic core is DPI.” |
| 275 | Pushing along a verdict directly gives `maxAdvantage ≤ Adv`; hence verdicts can simply be dropped. | **OVERSTATED** | Current equality theorem `adv_eq_maxAdvantage_swap` needs non-negativity and a substantial construction over finite transcript witnesses (`RandomSystem.lean:1819` onward), not a bare one-line DPI. | Cite the named theorem and hypotheses instead of deriving it rhetorically from DPI. |
| 276 | Any “give the adversary extra information” step is one forgetful-projection DPI. | **OVERSTATED** | This is true when both observations are pushforwards of the same source, the coarse observation is recoverable from the fine one, and the relevant non-negativity holds. It is not true for arbitrary model changes or extra interactive responses. | State those conditions explicitly. |
| 278-285 | One should **never** model extra information as a new system; observation refinement always suffices and is invisible during interaction. | **OVERSTATED** | Post-hoc deterministic annotations of a fixed execution law fit this pattern. Information revealed during interaction can change future queries and may require an augmented interface/system. | Scope to deterministic post-processing revealed only after the interaction. |
| 287-290 | Orientation is `Adv S T = Δ(T,S)` and unequal-weight orientation matters. | **VERIFIED** | `RandomSystems/RandomSystem.lean:1805-1823` proves the equality under non-negativity and gives the unequal-weight counterexample in its docstring. Probability systems regain symmetry. | Keep with the non-negativity/probability scope. |
| 292-294 | `δ` agrees with the whole-carrier one-sided expression when the second law is nonnegative. | **VERIFIED** | `statDist_eq_δ_of_nonneg`, `RandomSystem.lean:85-113`. | Keep. |
| 294-295 | Without non-negativity, partition additivity is false. | **FALSE** | The current theorem `δ_sum_of_disjoint_support` assumes non-negativity (`RandomSystem.lean:459-479`), but that proves only that this implementation uses it. Under its pairwise-disjoint union-of-support hypothesis, a direct cellwise argument still separates the sum even for signed second laws. No counterexample or necessity theorem supports the stronger sentence. | Replace with “The current declaration requires non-negativity; do not remove it without proving a generalized lemma.” |
| 297-300 | A `Fintype` hypothesis on an H lemma is always caused by `statDist`, never H. | **OVERSTATED** | This is documented for the specific ratio pair `hTechnique_ratio` versus `δ_hTechnique_ratio` (`RandomSystem.lean:936-953`). Other H endpoints can require finite transcript or partition carriers for independent reasons. | Scope the statement to these named ratio lemmas. |
| 302-306 | Dependent-type friction is a modeling smell and malformed inputs should be represented as garbage rather than ill-typed. | **NORMATIVE** | This is one useful total-model design choice, not a theorem applicable to every dependent protocol. | Keep as a repository modeling preference with exceptions. |
| 308-310 | A CR18 number in a docstring does not by itself prove exact thesis conformance. | **VERIFIED** | CR18 and the thesis use related but non-identical models; the repository itself records reconciliation notes, e.g. `LanzenbergerChain.lean:28-31` and `GameOf.lean:1468-1471`. | Keep. |

### “Rationalizations” and status claims

| Lines | Claim unit | Label | Evidence / reasoning | Conservative action |
|---:|---|---|---|---|
| 316-323 | One must never start in Lean or defer search until blocked. | **NORMATIVE** | This is a proposed process. Early goal inspection and source reading can be productive, especially for repairs where the mathematical statement already exists. | Present as a default for new proofs, not a universal prohibition. |
| 325-328 | The library has about 6,000 declarations and 189 notations. | **STALE** | A reproducible current source-line count gives 10,591 declaration-like lines using `rg` over `RandomSystems` and `RandomSystemsCC`; `notation` appears as a word 194 times and 64 lines begin with an actual notation declaration. Counts depend on methodology, which the skill does not state. | Remove hard-coded counts or generate them with a documented command. |
| 330-332, 190-198 in the planning guide | Existing generic facts must **always** be generalized in place, public; never use a specialized/private helper. | **OVERSTATED** | Ownership, API stability, dependency boundaries, local abstraction, and lack of authority to alter callers can justify a wrapper or private helper. | Replace with a preference plus ownership/caller checks. |
| 334-338 | `LanzenbergerChain.lean` names every Chapter 2 item and must be consulted before any missing verdict. | **OVERSTATED** | It is useful but incomplete as a literal numbered-item table and presently fails aggregate compilation. | Say “consult its curated mapping, then verify source/build status.” |
| 340-344 | Modeling extra information as a new system always creates a strictly stronger adversary. | **FALSE** | It can create a simulation obligation; it is not strictly stronger when the extra field is deterministic/redundant or unavailable during interaction. | Scope to interactive information that genuinely enlarges the observable response. |
| 346-349 | A theorem statement must never mention proof devices. | **NORMATIVE** | Auxiliary/augmented objects are legitimate theorem parameters when they are part of a reusable reduction. Headline corollaries may hide them. | Rephrase as an API/presentation preference for headline statements. |
| 351-355 | Every imported paper term/bad event must be classified as killed, shrunk, or retained. | **NORMATIVE** | Strong adaptation discipline, not a theorem. | Keep as a paper-adaptation checklist. |
| 357-359 | Every packaged endpoint has already performed the adaptive reduction and CE hands over a fixed schedule. | **FALSE** | The blind-game CE endpoint performs a nonadaptive reduction (`GameOf.lean:1416-1459`; CR18 printed pp. 109-110). H endpoints still quantify over all query environments (`Derivation.lean:444-447`), and coupling/winnability endpoints have their own adaptive obligations. | Replace with a statement restricted to the packaged blind-game CE endpoint. |
| 361-362 | Direct statistical-distance manipulation always means family II was skipped. | **FALSE** | Exact `L1` evaluation, an H lemma, or a coupling identity may legitimately operate directly on distance after all useful reshaping. | Replace with “Before direct manipulation, check whether a hybrid or DPI simplifies it.” |
| 364-365 | If `cr18_total` fails, the system definition is wrong. | **FALSE** | The explicit `cbcReal` probe refutes this: the named totality theorem exists but is outside the tactic's finite rule set. | Delete; use the diagnostic replacement given above. |
| 367-369 | The most specialized endpoint should be preferred; the partition form creates exactly two extra creative goals. | **OVERSTATED** | Specialization often reduces obligations, but exact counts depend on the endpoint and existing lemmas. The current equality and partition H endpoints each expose two principal hypotheses (`Derivation.lean:439-447`, `732-740`). | Keep the preference, delete the fixed “two extra” count. |
| 371-373 | The H ratio direction is `(1-eps) * ideal ≤ real`. | **VERIFIED** | This is exactly the hypothesis of `δ_hTechnique_ratio` (`RandomSystem.lean:949-953`) and the fixed-query endpoints. | Scope explicitly to this one-sided H orientation. |
| 375-378 | `maxEDist ≤ ofReal Δ` holds unconditionally; equality holds on every shared-domain object. | **OVERSTATED** | The inequality requires both laws to be probability distributions (`StrictContextAdvantage.lean:403-409`). Equality additionally requires a common fixed domain (`StrictContextSharedDomain.lean:934-945`), or total laws under a common `filterDom` (`976-990`). | State all normalization and domain hypotheses. |
| 380-383 | After the second failed fix, the cause is usually wrong statement shape or duplicate infrastructure. | **NORMATIVE** | This is a useful stop-and-reassess heuristic, not a diagnosis theorem. | Keep as heuristic; do not infer cause without inspecting the goal. |
| 385-387 | A `sorry`-free theorem can depend transitively on `sorryAx`; audit axioms. | **VERIFIED** | Lean's theorem dependencies can contain axioms introduced by admitted helpers; `#print axioms`/verification is the correct check. | Keep. |
| 389-392 | Compilation and an axiom audit are insufficient for readability. | **NORMATIVE** | A style/review standard, not a factual defect in a theorem. | Keep as project policy. |
| 399-416 | The listed reference files and `skills/PROOF-WORKFLOWS.md` exist and roughly contain the described topics. | **VERIFIED** | File existence and headings were checked. This verdict does not certify every internal claim in those other guides. | Keep; add per-reference audit status if they remain authoritative. |

## Audit of `references/sketch-and-plan.md`

| Lines | Claim unit | Label | Evidence / reasoning | Conservative action |
|---:|---|---|---|---|
| 1-14 | Lean checks elaboration/type correctness rather than discovering the intended theorem; stages 1-3 are a pre-Lean workflow. | **NORMATIVE** | The first clause is a fair informal distinction; the prescribed ordering is workflow policy. | Keep as motivation, not a universal ban on inspection. |
| 16-18 | The SequenceHash dispatch script enforces sketch adaptation and fails if the rule is missing. | **OVERSTATED** | `sequence-hash/dispatch/codex-dispatch.sh:22-30` checks only that `PREAMBLE.txt` is nonempty and contains the literal phrase `REALLY ADAPT, NEVER TRANSCRIBE`. It cannot verify that the generated sketch actually adapts rather than transcribes. | Replace with “enforces inclusion of the adaptation instruction in every canonical dispatch prompt.” |
| 22-28 | Stage 1's artifact must be Markdown with no Lean. | **NORMATIVE** | A workflow requirement, not a property of the proof. | Keep if project policy; permit theorem signatures when useful unless intentionally forbidden. |
| 30-69 | The template's object/claim/argument/route/adaptation fields are required. | **NORMATIVE** | Good documentation schema, not mathematically necessary. | Keep as a default template. |
| 49 | Every parameter must be explicit and “up to constants” is forbidden. | **NORMATIVE** | Appropriate for a final finite theorem; an exploratory sketch may legitimately start asymptotically. | Say “state the intended finite form when known; record asymptotic status otherwise.” |
| 71-81 | Transcribing paper events is the most common source of loose formal bounds; every source term must be killed/shrunk/left. | **UNVERIFIED** | No issue sample or frequency data is supplied. The adaptation table is a policy. | Remove “most common”; retain the table as required project review metadata. |
| 78-81 | SequenceHash's construction-specific adaptation rule generalizes to every RS proof. | **OVERSTATED** | It generalizes well to adapted paper proofs, but not to original proofs or exact reuse where no construction-specific source terms exist. | Scope to “when adapting a paper proof to a modified construction.” |
| 83-85 | A2's opening disclaimer is what stopped formalization drift. | **UNVERIFIED** | The disclaimer exists at `sequence-hash/sketches/A2-sequencemac-prf.md:19-23`; the causal claim cannot be established from the artifact. | Say only that it records and helps reviewers check the route choice. |
| 89-91 | PDFs must never be searched/extracted because extraction silently fails throughout the paper set. | **OVERSTATED** | The scanned thesis has poor/no searchable text, but `papers/CR18_LN.pdf` has a usable text layer and `CR18_LN.txt` exists. Extraction is useful for locating passages; visual inspection is necessary for authoritative verification. | Replace with “Use extraction for navigation when available, then verify the rendered page; do not treat zero hits as absence.” |
| 93-94 | Passed-forward source premises should be checked in the primary source. | **NORMATIVE** | Sound research practice. | Keep. |
| 96-99 | If the exact bound/technique is not known, Lean cannot help clarify it. | **OVERSTATED** | Lean will not choose the intended theorem, but inspecting definitions, counterexamples, or endpoint hypotheses can reveal an impossible bound or missing assumption. | Replace “will not help” with “will not substitute for the mathematical argument.” |
| 103-119 | The technique uniquely determines the complete DAG node set. | **FALSE** | A named endpoint determines its explicit hypotheses; model bridges, normalization, conversions, imports, and construction-specific intermediate lemmas add nodes. Line 119 itself admits additions. | Replace with “Start the DAG from the endpoint's explicit hypotheses, then add bridge and construction nodes.” |
| 110-117 | The table gives useful canonical principal obligations for H, CE, coupling, and a union bound. | **VERIFIED** | The H rows match current endpoint shapes (`Derivation.lean:439-447`, `732-740`); the other rows are accurate high-level decompositions, not exact Lean signatures. | Label the table “typical principal obligations.” |
| 121-129 | The node schema and three labels are mandatory. | **NORMATIVE** | Documentation convention. | Keep as template. |
| 131-135 | Creative nodes must always be proved leaves-first or their statements silently drift. | **OVERSTATED** | Leaves-first is often efficient; top-down theorem design and mutually refined statements are legitimate. Drift is a risk, not a logical consequence. | Say “prefer leaves-first once interfaces are stable.” |
| 137-152 | A typical CE proof has the displayed DAG, `bad_monotone` is routine, and exactly two leaves carry all mathematics. | **OVERSTATED** | Some CE games have difficult monotonicity, normalization, filtration, or MBO construction obligations. The diagram is an example, not a general shape theorem. | Label it “one common packaged-CE pattern”; remove the exact-two conclusion. |
| 154-158 | An all-creative DAG proves the route is wrong. | **FALSE** | New research can have an all-creative remainder after a correct endpoint choice. | Replace “is wrong” with “warrants a second reuse/routing check.” |
| 162-169 | Every node must receive exactly REUSE/ADAPT/NEW; ADAPT always means public in-place generalization. | **OVERSTATED** | The three search outcomes are useful, but “adapt” may properly mean a wrapper, a downstream corollary, or a local bridge when ownership/dependencies prohibit changing the original API. | Split reuse verdict from mutation policy. |
| 170-183 | The listed tools/search surfaces exist. | **VERIFIED** | Files and current Lean-LSP search tools were checked. | Keep. |
| 172 | Stop at the first search hit. | **NORMATIVE** | First hit may be weaker, deprecated, in a broken module, or wrong for the intended route. | Replace with “inspect the first plausible hit and continue when tightness/status is unclear.” |
| 184-186 | A good share of creative counting nodes reduce to Mathlib facts; repo grep does not search Mathlib. | **OVERSTATED** | The second clause is true. “A good share” has no count. | Keep only the concrete search-scope fact. |
| 188-198 | Never create a specialized or private generic helper; always generalize the existing framework theorem in place. | **OVERSTATED** | This ignores API ownership, scope, dependency cycles, stability, and whether the existing theorem should remain narrow. | Replace with a preference and require justification for either generalization or wrapper. |
| 200-203 | A `NEW` verdict should carry a search record. | **NORMATIVE** | Useful anti-duplication policy. | Keep. |
| 207-211 | After stage 3, stage 4 is mechanical. | **FALSE** | Endpoint elaboration, coercions, normalization bridges, model mismatch, and stale imports can remain. The false skeleton in `SKILL.md:180-186` is itself a counterexample. | Replace with “Stage 4 should expose any remaining interface/elaboration obligations early.” |
| 213-215 | If generated goals differ from the DAG, only the endpoint or plan can be wrong. | **FALSE** | The actual theorem signature, inferred instances, implicit arguments, imports, coercions, and current build state may differ from expectations without invalidating either mathematical route. | Use a non-exhaustive diagnostic checklist. |

## Audit of `agents/openai.yaml`

| Lines | Claim unit | Label | Evidence / reasoning | Conservative action |
|---:|---|---|---|---|
| 1-2 | The interface display name is “Random Systems Proofs.” | **VERIFIED** | Matches package identity. | Keep. |
| 3 | The short description is “Structure and verify Random Systems proofs.” | **VERIFIED** | Accurate at a high level and substantially safer than the frontmatter's “ANY theorem.” | Keep. |
| 4 | The default prompt asks the skill to formalize an RS security argument in Lean. | **NORMATIVE** | Appropriate default behavior, not a factual claim. | Keep. |

## Reproducible Lean and build evidence

The audit added only two diagnostic probes; it did not edit the skill package:

- `review/random-systems-skill/audit-probes/CBCImportProbe.lean`
- `review/random-systems-skill/audit-probes/TotalityIncompletenessProbe.lean`

Observed commands and outcomes:

```text
lake env lean review/random-systems-skill/audit-probes/CBCImportProbe.lean
  -> line 6: unknown tactic `cr18_total`

lake env lean review/random-systems-skill/audit-probes/TotalityIncompletenessProbe.lean
  -> `cr18_total`: Aesop made no progress on `cbcReal`, although
     `cbcReal_totalOnNonempty` is a named theorem
  -> `cr18_prob`: simp made no progress, although `cbcReal_isProbDist` is a named theorem

lake build RandomSystems.CR18Tactics RandomSystems.TotalityTactics \
  RandomSystems.HTechnique.Derivation
  -> succeeds

lake build RandomSystems.HTechnique.Tactics
  -> fails in RandomSystems/HTechnique/SoP/VisibleLaw.lean

lake build RandomSystems.LanzenbergerChain
  -> fails in RandomSystems/GameWinnability.lean and
     RandomSystems/MultiSystemCoupling.lean
```

## Minimum safe edits, in priority order

1. Replace the frontmatter's “ANY theorem” with the narrower security-proof scope.
2. Delete “closed set of seven technique families.” Call the tree a routing heuristic.
3. Replace every “tactic failure means modeling bug” claim with a three-way diagnostic: imports, registered tactic surface, then model.
4. Fix the stage-4 example by inserting `filteredDelta_le_Adv` or changing its goal to `Adv`.
5. Restrict fixed-schedule/adaptivity language to the packaged blind-game CE endpoint.
6. Add probability and fixed-domain hypotheses to the strict-metric statements.
7. Scope the `Fintype` explanation to the named H ratio lemma and retract the unsupported partition-additivity necessity claim.
8. Mark `HTechnique.Tactics` and `LanzenbergerChain` as currently non-building aggregate surfaces.
9. Replace “enforces sketch adaptation” with “enforces inclusion of the adaptation instruction.”
10. Convert workflow universals (`always`, `never`, `mechanical`, `exactly`) into explicit repository policy or conservative defaults.

## Coverage statement

Every line range in the two requested Markdown files that asserts an applicability rule, theorem interpretation, declaration/tactic capability, build/status fact, empirical measurement, or universal workflow consequence is represented above. Pure headings, code-fence delimiters, table formatting, and template placeholders with no independent claim were grouped with their surrounding normative unit. The four-line agent metadata file and the `SKILL.md` frontmatter are also covered.
