# Blind cross-review B: `SKILL.md`, `agents/openai.yaml`, and `references/sketch-and-plan.md`

Audit date: 2026-08-06.  Lean evidence snapshot: the then-current, dirty working tree (the audit does not assume `HEAD`).

Frozen skill inputs:

- `SKILL.md` — 416 lines, SHA-256 `d2ed1ec00b459ce342cc738b40848bc718f2522cba79ee0ca3b8d64c15e0f962`;
- `agents/openai.yaml` — 4 lines, SHA-256 `ec74a5f360b4c1c237cb7f5ce6f5d24a83e0969c090102773a59e55cb5b3c973`;
- `references/sketch-and-plan.md` — 215 lines, SHA-256 `a94ef630b3ea43b9c41a14f624171927e9eae206db0c16789505b9d429afe072`.

`SKILL.md` was concurrently rewritten to a 212-line version after the evidence pass.  The line references and verdicts below intentionally audit the frozen 416-line input above, not that moving post-audit rewrite.

## Scope and method

I audited only:

- `/Users/marcilunga/.codex/skills/random-systems-proofs/SKILL.md`;
- `/Users/marcilunga/.codex/skills/random-systems-proofs/agents/openai.yaml`;
- `/Users/marcilunga/.codex/skills/random-systems-proofs/references/sketch-and-plan.md`.

I did **not** open `core-and-plan-audit.md` or any other audit report.  I did not edit any skill file.  Each mixed sentence below is split where one part has a different verdict.  Repeated absolutes are recorded again at their repeated line rather than silently inheriting a verdict.

Verdicts mean:

- **VERIFIED** — current Lean/source or a visually checked primary PDF supports the claim as written;
- **OVERSTATED** — a sound core is missing material hypotheses, scope, or exceptions;
- **FALSE** — a current counterexample, signature, or internal contradiction refutes it;
- **STALE** — it describes an older surface/build state, not the current working tree/runtime;
- **UNVERIFIED** — no reproducible primary artifact supports it;
- **NORMATIVE** — a policy or style choice, not a truth-apt factual claim.  This verdict is not an endorsement.

## Evidence receipts used below

- **E1 (distance/source model):** `RandomSystems/RandomSystem.lean:72-94,161-166,501-527,886-892,1810-1821,8335-8376`.  In particular, `transcriptDist` is a pushforward, `δ_fTransform_le` requires a non-negative second law, `Adv S T` is built from `δ(tr(S,e),tr(T,e))`, `adv_eq_maxAdvantage_swap` needs both laws non-negative, and the easy half of Theorem 2.31 uses one `δ_fTransform_le` after representative rewrites.
- **E2 (H signatures):** `RandomSystems/HTechnique/Derivation.lean:398-447,488-499,724-756`; `RandomSystems/RandomSystem.lean:903-985,1034-1121`; `RandomSystems/StatDist.lean:481-525,577-600`.  The fixed-query ratio/equality/expectation/partition endpoints and the carrier-free `δ`/`statDist` variants are present, with the hypotheses shown there.
- **E3 (tactics):** `RandomSystems/TotalityTactics.lean:35-59`; `RandomSystems/CR18TacticsCore.lean:28-44,65-76,94-139`; `RandomSystems/CR18Tactics.lean:21-78`; `RandomSystems/HTechnique/Tactics.lean:30-89`.  These are conservative macros over finite lists of rewrites/applications, not completeness procedures.
- **E4 (CBC imports/probe):** `RandomSystems/CBCMAC.lean:5-12` imports `SwitchingLemma`; `RandomSystems/SwitchingLemma.lean:5-8` imports `CR18Tactics`.  `CBCMAC.lean:949` itself uses `cr18_algebra`.  A temporary `import RandomSystems.CBCMAC` probe produced `unknown tactic` for `cr18_total`, while `cr18_prob` on a true goal supplied as hypothesis failed with ``simp made no progress``.  The probe was deleted.
- **E5 (conditional-equivalence endpoint):** `RandomSystems/SwitchingLemma.lean:1844-1868,1887-1913`.  The packaged endpoint has `hmono`, `hCE`, two probability receipts, totality, and a fixed blind-schedule leaf; not all are automatically routine.
- **E6 (strict metric):** `RandomSystems/StrictContextAdvantage.lean:401-409` proves `maxEDist ≤ ofReal Δ` only for two `isProbDist` laws.  `RandomSystems/StrictContextSharedDomain.lean:913-945` proves equality only for two normalized laws whose support atoms share one displayed domain.  `:976-989` is the same-predicate restriction corollary.
- **E7 (controlled language):** `RandomSystemsCC/ControlledNaturalLanguage.lean:11-45,205-245` contains both condition-C and H-coefficient styles and exposes named `?good_ratio`, `?bad_probability`, and `?good_equality` goals.
- **E8 (current build/status):** `lake env lean RandomSystems/BoundedAttainment.lean` succeeds.  `lake env lean RandomSystems/GameWinnability.lean` fails with many current `NNReal`/`Real` errors and warns of a `sorry`; `lake env lean RandomSystems/LanzenbergerChain.lean` stops because the `GameWinnability.olean` is absent.  `lake env lean RandomSystems/CBCStructureGraph.lean` fails at several locations and source line 1428 is `sorry`.
- **E9 (discovery/runtime):** `.mcp.json:1-11` configures `uvx lean-lsp-mcp`, but this audit session exposed none of `lean_goal`, `lean_local_search`, `lean_state_search`, `lean_loogle`, `lean_leansearch`, `lean_leanfinder`, `lean_hammer_premise`, or `lean_verify`.  `lake env lean <file>` and `#print axioms` remain available.
- **E10 (SequenceHash precedent):** `sequence-hash/PLAN.md:119-189`; `sequence-hash/dispatch/codex-dispatch.sh:22-29,44-48`; `sequence-hash/sketches/A2-sequencemac-prf.md:19-23`.  The wrapper checks that `PREAMBLE.txt` contains the literal `REALLY ADAPT, NEVER TRANSCRIBE`; it does not inspect a produced sketch for compliance.
- **E11 (inventory counts):** a current lexical scan over tracked `RandomSystems*` Lean files found 9,816 declaration-start lines, 77 actual `notation` declaration lines, and 184 occurrences of the word `notation`; including untracked working-tree files increases declaration-start lines to 11,332.  No counting method reproduces “~6,000 declarations with 189 notations.”
- **P1 (thesis, visually checked):** `papers/thesis (1).pdf`, printed pp. 12-24 (PDF pp. 22-34): Def. 2.4 says `δ` is asymmetric at unequal weight; Lemma 2.7 is DPI; Defs. 2.12/2.14/2.17 make transcripts, shared domains, and compatible environments explicit; Def. 2.26 defines `Adv`; Thms. 2.31/2.32 and 2.37 have the stated distance/coupling/winnability shapes.  The thesis defines distributions as non-negative in Def. 2.1; it does not start from the repository's signed `Finsupp` extension.
- **P2 (CR18, visually checked):** `papers/CR18_LN.pdf`, printed p. 71 (PDF p. 42), pp. 108-111 (PDF pp. 60-62): Def. 3.22 is the output-bit MBO model; Def. 4.19 is conditional equivalence; Def. 4.20 is blind observation; Thm. 4.17 gives the blind-game bound; Lemmas 4.18/4.19 give birthday/switching results.
- **E12 (PDF text layers):** `pdftotext 'papers/thesis (1).pdf' -` yields only 108 bytes (page separators), while `pdftotext papers/CR18_LN.pdf -` yields 351,777 bytes.  Visual verification is mandatory, but extraction quality is not uniform across the paper set.

## Executive findings

The reliability notice is warranted, but the body still contains high-risk universal advice.  The largest issues are:

1. The frontmatter says **ANY** theorem in either library, while “When NOT to Use” excludes whole `RandomSystemsCC` layers and pure-Mathlib subgoals.
2. “Every security statement is an advantage bound” is false (`RandomSystems/Complexity/IidGames.lean:29-31` is an equality-form security theorem), and the alleged closed seven-family taxonomy is neither closed nor consistently enumerated.
3. Tactic failure does not diagnose a modeling bug.  The macros are deliberately conservative; a true, hypothesized `isProbDist` goal is already a counterexample to the claim.
4. Current status routing is stale: `LanzenbergerChain` is blocked by broken `GameWinnability`; `CBCStructureGraph` has compile errors and a `sorry`; `BoundedAttainment` itself is auditable.
5. The metric and orientation advice drops hypotheses.  “Unconditional” strict-metric comparison still assumes normalized laws, shared-domain equality needs a common domain, and `Adv S T = Δ(T,S)` needs non-negative laws.
6. `sketch-and-plan.md` contains useful templates, but its “never inspect Lean first,” “first hit wins,” “always generalize in place,” and “all-creative means wrong routing” absolutes are workflow preferences with real counterexamples.

## Claim ledger: `SKILL.md`

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SK-001 | 1-4: frontmatter is valid and names `random-systems-proofs`. | VERIFIED | Both frontmatter blocks parse as YAML; the name matches the skill directory and `openai.yaml` prompt token. | Keep. |
| SK-002 | 3: “Routes and structures Random Systems / Constructive Cryptography proofs in Lean 4.” | OVERSTATED | The files do route several RS proof styles, but the skill expressly excludes CC composition/AC/resource lifting at 91 and several current routes are broken (E8). | “Routes selected RandomSystems proof obligations and points to current RS proof surfaces; verify CC-layer applicability separately.” |
| SK-003 | 3: use for “ANY theorem in the RandomSystems or RandomSystemsCC libraries.” | FALSE | Contradicted by the skill's own lines 89-93; a pure algebra lemma or a CC assembly theorem does not need this workflow. | Replace `ANY theorem` with “security-bound or RS-model theorem whose proof needs one of the listed techniques.” |
| SK-004 | 3: use for every listed advantage/PRF/PRP/MAC/indifferentiability/refactor/`sorry` case. | OVERSTATED | Some listed tasks are CC composition or pure Mathlib leaves excluded later; “indifferentiability” may live in the AC layer. | Make the list examples conditioned on an RS distance/game obligation. |
| SK-005 | 3: it “picks” H, CE, coupling, winnability, or counting, names obligations, points at reuse, and fixes final shape. | OVERSTATED | It offers heuristic routing and partial ledgers, not a checked selector; the CE ledger omits `hmono` (E5), and current tool/status gaps remain (E8-E9). | “Suggests a candidate route and provisional obligation ledger; confirm against the endpoint signature.” |
| SK-006 | 8-10: the skill/references are under an independent claim audit on 2026-08-06. | VERIFIED | This audit task itself establishes that status at the stated date. | Keep; remove or close it when the audit is actually resolved. |
| SK-007 | 10-12: “verify every theorem interpretation, declaration signature, tactic-capability claim, and applicability claim.” | NORMATIVE | This is a sound audit policy, not a theorem. | Keep while provisional; say which checks are mandatory before code edits. |
| SK-008 | 13-15: never transfer terminology/completeness among CE, symmetric MBO games, representative theory, couplings, and H. | NORMATIVE | P1/P2 and E1/E5 show distinct models, so the caution is well motivated; “never” is still policy language. | “Keep these notions separate unless an explicit bridge theorem is cited.” |
| SK-009 | 17: “Every security statement in this library is an advantage bound.” | FALSE | `RandomSystems/Complexity/IidGames.lean:29-31` states `sampleGame_same_secure` as equality of a performance function to zero; CC construction security also has equality/perfect-construction forms (e.g. `TypedConstruct.lean:195-211`). | Delete.  Say only that many flagship RS endpoints are distance/advantage bounds. |
| SK-010 | 18: “closed set of seven technique families.” | FALSE | The file names only families I, II, III, and VI in routing; the companion map also introduces IV/V and legacy condition-based routes, with no coherent seventh family.  New routes can be added to Lean. | Replace with an explicitly non-exhaustive current list and enumerate it consistently. |
| SK-011 | 18-20: proof shape is knowable before attempting it and most work is routing/reuse. | OVERSTATED | Endpoint signatures constrain many proofs, but creative theorem discovery, modeling, and elaboration can change the route.  No Lean/PDF establishes this empirical generalization. | “For packaged endpoints, a useful provisional obligation shape is often knowable early.” |
| SK-012 | 22: “Six stages, three of them before Lean.” | VERIFIED | This accurately describes the process defined by lines 27-34. | Keep as the skill's chosen workflow, not a property of the library. |
| SK-013 | 22-23: “Do not skip a gate; the gates are the whole mechanism.” | NORMATIVE | Process mandate. | Soften to a default; allow explicit exceptions for diagnosis, named-theorem repair, or trivial library reuse. |
| SK-014 | 28: “SKETCH ... NO Lean, NO library search.” | NORMATIVE | Strong workflow rule; it conflicts with named-theorem repair where the exact statement is the object to sketch. | “Draft the mathematical argument before implementation search; first read the target statement and allowed project authorities.” |
| SK-015 | 29: every DAG node must be `[LIB]/[ROUTINE]/[CREATIVE]`. | NORMATIVE | This is an imposed triage taxonomy, not a Lean fact; it lacks `BLOCKED/MODEL/IMPORT` states. | Add at least `[MODEL]` and `[BLOCKED]`, or call the three labels a first-pass heuristic. |
| SK-016 | 30: reuse search must be `CHEATSHEET → grep → local search → mathlib`. | NORMATIVE | Search order is a preference; the runtime may lack the named local tools (E9), and source authority may need to precede the cheatsheet. | “Suggested order when tools are available; verify the final hit against source.” |
| SK-017 | 31: skeleton must apply one endpoint, `sorry` every creative leaf, and compile. | NORMATIVE | Useful method, but not every proof has a single endpoint or permits inserting `sorry`. | “For a multi-obligation endpoint, prefer a compiling scratch skeleton; do not commit new `sorry`s.” |
| SK-018 | 32: fill leaves in DAG order, leaves first. | NORMATIVE | Dependency-respecting order is sensible, but mutually informative statements or API exploration can justify another order. | “Default to dependency order; revise the DAG when proof discovery changes dependencies.” |
| SK-019 | 33: receipts must include axiom audit, no `sorry`, and reused/generalized report. | NORMATIVE | Repository policy, not a factual claim.  `#print axioms` supports the axiom receipt. | Keep as a release gate; specify allowed axioms and scope. |
| SK-020 | 36,38-40: Stage 1 is Lean-free; never open/grep/lookup before a sketch. | NORMATIVE | Absolute is unsafe for repair/refactor tasks and conflicts with the repo instruction to inspect the actual goal state. | Permit reading the theorem statement, goal, DESIGN/STATUS, and primary source before the sketch; defer implementation search. |
| SK-021 | 39-40: measured failure that agents burn most opening context surveying Lean. | UNVERIFIED | No primary dispatch log, token trace, or reproducible measurement was found; the companion prose repeats the assertion only. | Delete “Measured” or cite a durable experiment artifact with denominator and protocol. |
| SK-022 | 42-45: searching first anchors agents and causes inherited loose bounds. | OVERSTATED | Plausible cognitive-risk rationale, but causal and universal wording has no primary measurement; source inspection can also reveal a stronger endpoint. | Present as a possible failure mode, not a deterministic effect. |
| SK-023 | 47-48: library search is stage 3 and deliberately after the DAG. | VERIFIED | Accurate description of this workflow. | Prefix “In this workflow”. |
| SK-024 | 50: “Missing infrastructure is expected.” | UNVERIFIED | No rate or inventory is supplied. | “Missing infrastructure may occur.” |
| SK-025 | 50-51: “You may add definitions, lemmas, and general framework facts freely.” | NORMATIVE | This is an authorization/style rule and can create API churn in a dirty tree. | “Add only in-scope, source-faithful infrastructure after reuse search and module-owner review.” |
| SK-026 | 51-53: absence must never decide the mathematics; if an object is needed, build it. | NORMATIVE | Sound aspiration, but formalizability, scope, and source model can legitimately constrain a task. | “Do not weaken the mathematical claim merely because a helper is absent; surface any required model/API extension explicitly.” |
| SK-027 | 57-62: freedom table; stage 4 has one endpoint/exact arguments/must compile and leaf order is fixed. | NORMATIVE | These are process prescriptions, not library facts; some arguments are multi-endpoint calculations. | Label the table “default workflow for packaged endpoints.” |
| SK-028 | 64-65: a sketch considering only formalized material “is not a sketch.” | NORMATIVE | Definition by policy. | “Such a sketch is likely too implementation-driven.” |
| SK-029 | 67-68: always read `sketch-and-plan.md` before starting any proof. | NORMATIVE | Overbroad for trivial repairs and pure library reuse. | “Read it for nontrivial security proofs or route selection.” |
| SK-030 | 70: “Nothing enforces any of this.” | FALSE | SequenceHash's wrapper mechanically enforces the presence of its preamble phrase (E10), and AGENTS/process instructions impose gates, although Lean does not. | “Lean does not enforce this general workflow; one SequenceHash dispatch wrapper enforces only preamble presence.” |
| SK-031 | 70-71: no goal-shape tactic, technique typeclass, or hook enforces it. | VERIFIED | Source search found no such RS routing declaration; E3 contains bookkeeping tactics only. | Keep, scoped to the current RS tree. |
| SK-032 | 71: absence of enforcement is a deliberate choice. | UNVERIFIED | Design prose repeats the choice, but this is intent attribution rather than a kernel/PDF fact. | Attribute it to `skills/PROOF-WORKFLOWS.md` as current design intent. |
| SK-033 | 71-73: two dispatches/67 calls/zero sketches/straight grep-to-edit. | UNVERIFIED | No raw call trace or two-dispatch primary artifact was found. | Supply links to immutable dispatch logs or delete the numbers. |
| SK-034 | 75-76: sketch is always the first deliverable and must be `sketches/<result>.md`. | NORMATIVE | Conflicts with `sketch-and-plan.md:27`, which says it is “not a deliverable”; path may not exist in every project. | Choose one term: “first working artifact”; make path project-relative and conditional. |
| SK-035 | 77-78: it is the **only** artifact making routing reviewable; transcript-only reasoning cannot be checked/corrected/reused. | FALSE | A plan, proof comments, review log, commit, or recorded transcript can also make routing reviewable. | “A maintained sketch is the preferred durable routing artifact.” |

### Applicability and routing

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SK-036 | 82-85: use for new `Δ` bounds, repairs/refactors, paper-route selection, and slack review. | OVERSTATED | Appropriate for nontrivial RS security work, but frontmatter and these bullets do not state the later exclusions or current route/build gaps. | Add “when an RS endpoint/technique is actually involved; confirm current build status first.” |
| SK-037 | 89: never use for pure Mathlib goals; “just prove them.” | NORMATIVE | Sensible applicability boundary, but such a subgoal may occur inside an RS proof and the skill's arithmetic guidance can still matter. | “Do not invoke the full routing workflow for an isolated pure-Mathlib leaf.” |
| SK-038 | 90: never use for definitions with no bound attached. | NORMATIVE | A model definition may be the prerequisite of the requested bound; the exclusion is a workflow choice. | “Use the skill once the modeling task is tied to a security theorem.” |
| SK-039 | 91: never use for CC composition, AC, or resource lifting. | FALSE | Contradicts frontmatter's `RandomSystemsCC`/indifferentiability applicability and E7, which deliberately spans condition C, H, and construction assembly. | Narrow frontmatter to RS bounds, or explicitly add the relevant CC/AC workflow; do not state both. |
| SK-040 | 92-93: once inside creative combinatorics, stop using the skill and think freely. | NORMATIVE | Applicability/style rule. | “The skill no longer prescribes the mathematics inside the creative leaf, but its source/reuse/receipt rules still apply.” |
| SK-041 | 98: always check zero distance first. | NORMATIVE | A useful heuristic, not universally cheapest (the target may visibly be nonzero). | “Check exact equality early when plausible.” |
| SK-042 | 98: “δ = 0 beats every δ ≤ ε.” | OVERSTATED | This requires `0 ≤ ε`; security bounds usually use `NNReal`, but the displayed statement does not say so. | “If `0 ≤ ε`, an exact zero result implies the requested bound.” |
| SK-043 | 99: split/strip means family II (hybrid/DPI/restriction). | NORMATIVE | These current transformations exist, but the family number is an internal taxonomy. | Remove numbering unless the complete taxonomy is defined in one place. |
| SK-044 | 100-102: a bad transcript routes to H-technique. | OVERSTATED | H endpoints do use transcript predicates (E2), but CE can also monitor a transcript-derived monotone condition. | “H is a candidate when likelihood/equality statements are naturally transcript-local.” |
| SK-045 | 102-104: an adaptive/stateful triggered condition routes to conditional equivalence. | OVERSTATED | P2/E5 support CE for monotone conditions and blind reduction, but CE requires its precise MBO/conditional-law hypotheses. | Add “when a condition-C/MBO satisfying the CE endpoint can be constructed.” |
| SK-046 | 104-106: disagreement under shared randomness routes to coupling. | VERIFIED | `RandomSystems/Coupling.lean:149` gives `coupling_bound`, and `RandomSystemCoupling.lean:48-62` supplies optimal probability couplings. | Keep as a candidate route, not an exclusive classification. |
| SK-047 | 106-107: adversary winning a game routes to winnability. | OVERSTATED | P1 verifies the thesis route, but current `GameWinnability.lean` does not compile (E8). | Mark the route currently unavailable pending the migration repair. |
| SK-048 | 108: probability discharge is “family VI counting.” | OVERSTATED | Some residual probability goals are analytic, algebraic, or direct library facts rather than combinatorial counting. | “Use counting or the appropriate probability/analytic lemma for the residual mass goal.” |
| SK-049 | 109: arithmetic is handled by `cr18_arith` / `cr18_algebra` / `cr18_close`. | OVERSTATED | The macros exist (E3), but are finite tactic portfolios and do not close all arithmetic goals. | “Try these macros on matching routine tails; inspect the remaining goal on failure.” |
| SK-050 | 114-115: exact-zero avenues include behavioral quotient, relabeling invariance, and non-adaptive sufficiency. | VERIFIED | `RandomSystemQuotient.lean:128-183`, `StrictRelabel.lean:579-635`, and `RandomSystem.lean:785-824` provide corresponding exact statements. | Keep, with exact declaration names. |
| SK-051 | 114-115: family I is commonly skipped. | UNVERIFIED | No measurement or corpus count. | Say “can be skipped.” |
| SK-052 | 116-118: family II is the most omitted step and head-on `Δ` is the single most common self-inflicted difficulty. | UNVERIFIED | No primary failure log or sample protocol. | Remove superlatives or cite a reproducible review dataset. |
| SK-053 | 120-121: every sketch must state the chosen and rejected technique. | NORMATIVE | Strong review convention; a trivial or uniquely typed route may have no plausible alternative. | “For non-obvious route choices, record the main rejected alternative and reason.” |
| SK-054 | 125-129: the quoted CHEATSHEET §9 warning exists. | VERIFIED | `CHEATSHEET.md:494-510` contains the quoted R4-specific warning and also a `filteredDelta_le_Adv` bridge. | Keep as an exact quote, but preserve its SequenceHash/R4 scope. |
| SK-055 | 125-138: the R4 warning is part of global routing for every module. | OVERSTATED | The warning is project-route-specific; E7 is one module intentionally containing both CE and H styles, and CHEATSHEET itself documents a bridge. | “For SequenceHash R4, follow §9; elsewhere inspect the target module's actual surface.” |
| SK-056 | 131-133,394-397: an H proof of a CE theorem was axiom-clean and cost ~90 lines/zero mathematics. | UNVERIFIED | No current Lean proof or immutable experiment artifact matching this description was found; current SequenceHash plan says CBC has no H proof. | Cite the exact file/commit and axiom receipt, or delete the measurement. |
| SK-057 | 135-138: “A module is architected for one route.” | FALSE | E7 is a direct counterexample: one module implements both CE and H proof styles, plus construction assembly. | “Many application modules favor one route; inspect imports and endpoints.” |
| SK-058 | 137-138: going against the grain can be right; doing it by accident never is. | NORMATIVE | Review maxim. | “Record intentional cross-route bridges explicitly.” |

### Obligation ledger and tactic claims

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SK-059 | 142: every endpoint hypothesis falls into exactly `[LIB]/[ROUTINE]/[CREATIVE]`. | OVERSTATED | The taxonomy omits model changes, missing imports, blocked dependencies, inconsistent statements, and performance/build obligations. | Call it a three-way first pass and add `[MODEL]`/`[BLOCKED]`. |
| SK-060 | 146: a `[LIB]` theorem must **never** be reproved. | NORMATIVE | Usually good reuse policy, but an existing theorem may be private, wrong-shaped, deprecated, or depend on inadmissible axioms. | “Reuse an applicable, admissible public theorem; otherwise document why adaptation/replacement is needed.” |
| SK-061 | 147: if a `[ROUTINE]` tactic fails, fix the model, not the proof. | FALSE | E3-E4: the tactics are incomplete; `cr18_prob` fails on a true goal already available as a hypothesis. | “Inspect the goal, imports, and tactic coverage; only diagnose a model bug from semantic evidence.” |
| SK-062 | 150,156-158: if every DAG node is creative, routing is wrong and a packaged endpoint exists. | FALSE | A genuinely new theorem or new counting result can have only creative leaves; no current Lean declaration proves endpoint completeness. | “All-creative is a signal to repeat reuse/routing search, not proof that routing is wrong.” |
| SK-063 | 156: `cr18_total` and `htechnique_total` discharge `KStepTotal` / `TotalOnNonempty`. | OVERSTATED | E3: they try registered standard constructors and assumptions; `htechnique_total` adds selected SoP/PRP constructors.  They do not decide all such propositions. | “Try these tactics for registered constructors and in-scope assumptions.” |
| SK-064 | 157: `cr18_prob` discharges `isProbDist`. | OVERSTATED | E3-E4: it is a fixed `simp only` bundle and can make no progress on a true arbitrary `isProbDist` hypothesis. | “Normalizes common registered `isProbDist` goals.” |
| SK-065 | 158: `cr18_routine` discharges standing side conditions. | OVERSTATED | E3: it tries `grind`, arithmetic, algebra, and pushforward simplification; there is no completeness guarantee. | “Tries common layer-independent bookkeeping goals.” |
| SK-066 | 159: `cr18_filter` / `cr18_game` / `cr18_transcript` normalize the filter, game/MBO, and transcript shapes. | VERIFIED | Exact macro rewrite sets are at E3. | Keep “normalize,” not “discharge all.” |
| SK-067 | 160: `htechnique_compress` rewrites repeated queries to the canonical injective tuple. | VERIFIED | `HTechnique/Tactics.lean:42-51` is exactly that simp bundle. | Keep, qualified by matching SoP declarations/imports. |
| SK-068 | 161: `htechnique_adv_le` reduces `advPRF`/`advPRP`/`Adv` shells to pointwise goals. | VERIFIED | `HTechnique/Tactics.lean:64-74` tries the four named shells then `cr18_adv_le`. | Keep; add `fixedQueryAdv` because the macro supports it. |
| SK-069 | 162: the three `cr18_*` tactics close “the arithmetic tail.” | OVERSTATED | E3 shows a portfolio, not a complete arithmetic decision procedure. | “Try on routine arithmetic/algebra tails.” |
| SK-070 | 163: `inferInstance` discharges `FiniteTranscriptSpace` / `DiscreteTranscriptSpace`. | OVERSTATED | These abbreviate `Fintype`/`DecidableEq` (`HTechnique/TranscriptLawPublic.lean:30-42`); inference succeeds only when constituent instances exist. | “Use `inferInstance` when the carrier instances are derivable; otherwise supply/model them explicitly.” |
| SK-071 | 165: tactic modules are not globally available; check imports. | VERIFIED | E4 demonstrates differing transitive availability. | Keep. |
| SK-072 | 166: `CBCMAC.lean` imports none of the tactic modules. | FALSE | It transitively imports `CR18Tactics` through `SwitchingLemma`, and uses `cr18_algebra` at line 949 (E4). | “`CBCMAC` reaches `CR18Tactics` transitively but does not reach `TotalityTactics`.” |
| SK-073 | 166-168: `cr18_total` is unavailable in `CBCMAC` unless its module is added. | VERIFIED | E4's import probe reports `unknown tactic`. | Keep the precise conclusion, delete the false “none of the tactic modules” premise. |
| SK-074 | 168: a tactic that does not resolve is an import problem. | FALSE | E4's `cr18_prob` counterexample has the tactic imported; goal mismatch/incomplete coverage is another cause. | “First distinguish unknown tactic/import failure from an in-scope tactic that leaves a goal.” |
| SK-075 | 170-173: when available, tactic failure is always a modeling bug. | FALSE | Directly refuted by E3-E4. | Delete. |
| SK-076 | 171: `cr18_total` failure implies unintended partiality. | FALSE | It can also mean an unregistered but valid constructor, missing supporting hypothesis, or unsupported goal form; its own docstring says “standard constructors.” | “May indicate missing totality evidence or registration; inspect semantics before changing the model.” |
| SK-077 | 171-172: `cr18_prob` failure implies the weight is not normalized. | FALSE | E4 gives a normalized goal by hypothesis that the macro does not use. | “May indicate missing rewrite coverage or evidence; check the actual `isProbDist` hypothesis.” |
| SK-078 | 172: instance-search failure implies the carrier is wrong. | FALSE | It can mean a missing import, local instance, stuck metavariable, or intentionally noncomputable/classical instance. | “Inspect the missing instance and metavariables; change the carrier only for semantic reasons.” |
| SK-079 | 172-173: hand-proving any failed routine obligation buries a bug. | FALSE | A small explicit proof can be the correct receipt for an unregistered custom constructor. | “Prefer registering reusable facts; an explicit proof is acceptable when the obligation is genuinely local and documented.” |

### Skeleton and proof-shape claims

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SK-080 | 177: always apply the endpoint with named creative holes, `sorry` each, and compile. | NORMATIVE | Useful scratch workflow, but not every theorem has one endpoint and committed `sorry` may violate gates. | “Use a temporary compiling skeleton for multi-obligation endpoints; remove all admissions before integration.” |
| SK-081 | 179-186: the displayed `adv_le_of_fixedQuery_eq_on_good` skeleton has the endpoint's argument order and two creative legs. | VERIFIED | E2 at `Derivation.lean:439-447` has `S T Bad δb hS hT h_eq h_bad` exactly. | State that `cr18_total` succeeds only for registered systems/imports. |
| SK-082 | 188: named metavariables give `case` labels. | VERIFIED | Lean elaborates named holes into corresponding goals for this endpoint shape. | Keep as a convenience, not an arity contract. |
| SK-083 | 188-190: nothing checks the planned obligation count; compare goals to the DAG. | OVERSTATED | Lean checks that all actual goals close, but does not compare them with an external DAG.  The first clause is true only about that external plan. | “Lean checks actual goals, not correspondence with your external DAG.” |
| SK-084 | 189-190: if goals differ, the endpoint or plan must be wrong. | FALSE | Implicit-instance goals, import changes, elaboration choices, or a stale signature can also explain a mismatch. | “Pause and reconcile the actual signature, imports, and plan before continuing.” |
| SK-085 | 192: do this even for every single-obligation proof. | NORMATIVE | A direct `exact`/`simpa` can be clearer and safer for a one-hop proof. | “Use a skeleton when it adds diagnostic value.” |
| SK-086 | 192-194: noncompilation has exactly three causes: bad bound, bad endpoint, or unavailable routine hypothesis. | FALSE | Syntax errors, namespace/import drift, coercions, missing instances, stale oleans, and unrelated upstream failures are counterexamples (E8). | Replace with a non-exhaustive diagnostic checklist. |
| SK-087 | 196-198: measured exception—if all nodes are `[LIB]`, skip skeleton and write a `calc`. | UNVERIFIED | No measurement artifact; direct proof shape depends on the theorem, not just the labels. | “A direct proof may be preferable when every obligation is an immediate citation.” |
| SK-088 | 200-204: every cryptographer's proof is a chain of hops. | FALSE | Structural induction, bijection/counting, coupling construction, and exact equivalence proofs need not be inequality chains. | “When the mathematical argument is a sequence of bounds, expose it as a chain.” |
| SK-089 | 206-208: a measured CBC-MAC H proof buried a five-analysis chain. | UNVERIFIED | No current proof/log supports the described experiment; current `CBCMAC` is CE-based. | Cite the exact artifact or delete. |
| SK-090 | 210-211: the top level **always** must be a `calc`; nested `le_trans` deletes quantities. | NORMATIVE | Style rule; one-step proofs, equalities, inductions, and combinatorial constructions are counterexamples to universal applicability. | “Prefer a top-level `calc` for multi-hop inequalities when it materially exposes intermediate quantities.” |
| SK-091 | 224-226: creative obligations must be named `have`s before `calc`; never inline a forty-line case. | NORMATIVE | Readability convention. | “Prefer named lemmas/`have`s for substantial reusable legs; a short local case may remain inline.” |
| SK-092 | 228-230: every bad event must be named; never use an anonymous lambda. | NORMATIVE | Naming helps reused/complex events, but a one-use simple predicate can be clearer inline. | “Name nontrivial or reused bad events.” |
| SK-093 | 232-235: every H proof must state the variant visibly. | NORMATIVE | Good review practice, not a Lean requirement. | “Document non-obvious variant/degenerate-case choices.” |
| SK-094 | 237-239: routine plumbing must never occur between mathematical hops. | NORMATIVE | Style preference; a local side condition may be clearest at its use site. | “Hoist repeated or distracting plumbing; keep short local receipts near their use when clearer.” |
| SK-095 | 241-244: `ControlledNaturalLanguage.lean` renders paper-style H skeletons with named goals, and DESIGN aims at pen-and-paper readability. | VERIFIED | E7 and `DESIGN.md:398-406`. | Keep. |

### Discovery and current-status claims

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SK-096 | 248: read the library from the environment, never from memory. | NORMATIVE | Sound reliability rule. | “Verify unstable/signature-sensitive claims against the current environment.” |
| SK-097 | 252: CHEATSHEET is curated by goal and **always first**. | OVERSTATED | Its headings/coverage are current (`CHEATSHEET.md:31-574`), but it is dirty working-tree prose and cannot outrank primary source/current signature in all tasks. | “Use it as the first reuse index after reading the target/source authorities.” |
| SK-098 | 253: `LanzenbergerChain.lean` is a thesis-item-to-name table with one row per numbered Ch. 2 item and source errata. | OVERSTATED | The source file claims this at `:10-18` and contains extensive tables/errata, but it cannot currently elaborate (E8); completeness against every numbered item was not mechanically certified. | “A broad, currently noncompiling name table; verify each row against the source and underlying module.” |
| SK-099 | 253: an agent twice falsely claimed `Adv` behavior dependence was missing. | UNVERIFIED | No primary interaction trace. | Cite the trace or remove “measured failure.” |
| SK-100 | 253: `LanzenbergerChain.lean` currently does not compile because of unfinished `dist-real` migration. | VERIFIED | E8: its immediate blocker is missing `GameWinnability.olean`; that source has many `NNReal`/`Real` mismatches. | Keep, name `GameWinnability` as the blocker. |
| SK-101 | 253: “items behind `BoundedAttainment` are written but not auditable.” | OVERSTATED | `BoundedAttainment.lean` itself compiles cleanly (E8).  Only the wrappers in the blocked aggregate file cannot be checked through that file. | “The aggregate wrappers after the broken import are not elaborated; audit `BoundedAttainment` directly, which currently compiles.” |
| SK-102 | 254: grep over the three trees finds names/idioms. | VERIFIED | Ordinary source search works; `rg` is the repo-preferred equivalent. | Say `rg`, not `grep`, to match AGENTS. |
| SK-103 | 255-257: the named `lean_*` search tools are available for local/mathlib search. | STALE | None was exposed in this audit runtime (E9), despite `.mcp.json` configuring a server. | “When exposed by lean-lsp MCP, use ...; otherwise use `rg`, `#check`, and a focused scratch file.” |
| SK-104 | 258: `#print axioms` and `lean_verify` provide the receipt. | OVERSTATED | `#print axioms` is available; `lean_verify` was not exposed (E9). | Make `#print axioms` canonical and `lean_verify` optional when available. |
| SK-105 | 260-262: iterate with lean-lsp/`lean_goal`; fall back to single-file Lean; reserve `lake build`. | OVERSTATED | This matches AGENTS as a preference, but lean-lsp tools are absent here (E9).  Focused `lake env lean` is verified usable. | Put availability first: “Use goal-state tooling when exposed; otherwise focused `lake env lean`.” |
| SK-106 | 262: every subagent brief must contain that dev loop. | NORMATIVE | Coordination rule, not a factual claim. | Keep only when subagents are actually authorized. |

### Mathematical/modeling claims

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SK-107 | 268-270: `transcriptDist S e m` is the pushforward of `S`; DPI is `δ_fTransform_le`/thesis Lemma 2.7. | VERIFIED | E1; P1 printed pp. 12-14 defines f-transform/DPI/transcript, and Lean gives the exact definition. | Keep with exact namespace `RandomSystems.CR18`. |
| SK-108 | 273-275: pushing along `tr(·,e)` gives `Adv ≤ Δ`; the easy half of Thm. 2.31 is one DPI application. | VERIFIED | E1 at `RandomSystem.lean:8362-8376`; P1 printed p. 20/22.  The Lean proof rewrites representatives then applies one `δ_fTransform_le`. | Keep; state non-negativity hypotheses. |
| SK-109 | 275: pushing along `verdict` gives `maxAdvantage ≤ Adv`. | OVERSTATED | A per-distinguisher verdict is a pushforward, but the global relation additionally needs the DDD-to-environment/prefix bridge, orientation, normalization, and suprema. `adv_eq_maxAdvantage_swap` is the current clean theorem (E1). | Cite `adv_eq_maxAdvantage_swap` with non-negativity and swapped arguments instead of claiming one bare DPI. |
| SK-110 | 276: any “give the adversary extra information” step is a forgetful-projection DPI. | OVERSTATED | True only when both compared observations are deterministic images of common underlying laws and the plain observation factors through the richer one. | Add those factorization/common-source hypotheses. |
| SK-111 | 278-279: to give more information, **never** build a new system; always refine observation. | FALSE | Extra information may change the interactive response interface/state, in which case it is not post-processing of the same law. | “For post-interaction auxiliary data that does not affect responses, prefer a richer observation of the same source.” |
| SK-112 | 279-280: a wider-alphabet second system always forces a simulation obligation. | OVERSTATED | A relation is needed if transporting a bound back to the original system, but definitional equality, an existing converter bridge, or a theorem already phrased on that system can discharge it. | “Usually introduces a relation/transport obligation unless an existing equality/bridge supplies it.” |
| SK-113 | 280-283: a common source law, richer map, and `Prod.fst` projection reduce the step to one DPI. | VERIFIED | E1 (`δ_hTechnique_*_fTransform`) and E2 support arbitrary deterministic observation; the claim is correct under its stated common-source/projection setup. | Keep the setup explicit. |
| SK-114 | 283-285: information only in the observation is invisible to the environment, so late reveal is structural. | OVERSTATED | Correct when the interaction responses and environment inputs are unchanged and augmentation is computed after the run; not true for interactive leakage. | Add “post-interaction, response-independent augmentation.” |
| SK-115 | 287-290: `δ` is asymmetric at unequal weight. | VERIFIED | P1 Def. 2.4; E1. | Keep. |
| SK-116 | 288-290: `Adv S T` is `Δ(T,S)` without qualification. | OVERSTATED | E1's `adv_eq_maxAdvantage_swap` requires `S.NonNeg` and `T.NonNeg`; the notation `Δ` in that theorem is verdict-based `maxAdvantage`, not class-distance `CR18.Δ`. | “For non-negative laws, `Adv S T = maxAdvantage T S`.” Avoid overloading `Δ` in prose. |
| SK-117 | 289-290: naive `Adv S T = Δ(S,T)` is refutable at subdistribution weight. | VERIFIED | `RandomSystem.lean:1810-1818` records the `S=0` counterexample and the theorem immediately below. | Keep, with the two `Δ` notions disambiguated. |
| SK-118 | 290: “Ideal system first.” | NORMATIVE | Orientation mnemonic depends on which endpoint/notation is being used. | State named arguments and inequality rather than a universal mnemonic. |
| SK-119 | 292: `NonNeg` side conditions are “Def 2.4 content.” | OVERSTATED | P1 Def. 2.1 already restricts distributions to non-negative weights; the explicit hypotheses arise because the repository extends `Dist` to signed `ℝ` finsupps. | “`NonNeg` restores the thesis's positive-distribution invariant inside the signed repository extension.” |
| SK-120 | 292-294: support-sum equals whole-carrier Def. 2.4 sum **only when** the second argument is non-negative. | FALSE | Non-negativity is a sufficient uniform bridge (`statDist_eq_δ_of_nonneg`), not necessary for every individual pair; if the first law has full support, equality can hold with a negative second law. | “Non-negativity is the reusable sufficient hypothesis; without it the equality is not valid uniformly.” |
| SK-121 | 294-295: omitting `NonNeg` makes partition additivity false. | UNVERIFIED | Current `δ_sum_of_disjoint_support` assumes non-negativity (`RandomSystem.lean:462-467`), but the tree provides no necessity counterexample for that exact disjoint-support statement. | “The current theorem requires `NonNeg`; do not claim necessity without a counterexample.” |
| SK-122 | 297-300: an old H lemma's `Fintype`/weight requirements come from `statDist` symmetrization/univ summation, while the `δ`-native form removes them. | VERIFIED | E2 signatures and proofs: old `hTechnique_ratio` uses `statDist_symm_of_eq_weight` and `Finset.univ`; `δ_hTechnique_ratio` has no `Fintype` or equal-weight premise. | Keep, identify the old and new declaration names. |
| SK-123 | 299: `List (X × Option Y)` is an infinite carrier. | OVERSTATED | It is infinite when `X` is inhabited; for empty `X` it collapses to the singleton empty list.  In generic code there is no automatic `Fintype` instance. | “Typically infinite (when `X` is inhabited), and no generic `Fintype` is available.” |
| SK-124 | 299-300: the `δ`-native theorem has strictly weaker hypotheses. | VERIFIED | E2 gives concrete missing premises (`Fintype`, equal weights) and broader support-local ratio. | Keep, scoped to the compared theorem pair. |
| SK-125 | 302: dependent-type friction is a modeling smell. | NORMATIVE | Heuristic, not a semantic theorem. | “Persistent cast friction can signal an over-indexed model; inspect before changing it.” |
| SK-126 | 303-306: HCTR2 `sub` is total past the end and `blocks` accepts arbitrary width, allowing a total malformed-input predicate. | VERIFIED | `RandomSystems/HCTR2_FINAL.lean:119-186,2540-2546`. | Scope explicitly to the HCTR2 bitstring layer. |
| SK-127 | 305-306: when casts threaten, always name the intermediate rather than cast around it. | NORMATIVE | Style rule. | “Prefer a named intermediate when it clarifies dependent equalities.” |
| SK-128 | 308-310: CR18 numbering/docstrings do not prove thesis conformance; check the thesis. | VERIFIED | P1/P2 show genuine model differences (shared domain/compatible partial environments versus CR18 completion/MBO). | Keep. |

### Repeated absolutes and empirical claims in “Rationalizations to Reject”

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SK-129 | 316-319: Lean only tells whether text typechecks, not what is being proved. | OVERSTATED | Lean displays the exact proposition and proof state; it does not establish that the proposition matches informal intent. | “Lean checks the formal proposition, not its correspondence to your intended/source theorem.” |
| SK-130 | 318-319: never-provable bounds survive a surprising amount of tactic work. | UNVERIFIED | No primary example/measurement is cited. | Say “can survive” or cite a concrete failed formalization. |
| SK-131 | 321-323: searching only at a wall is always too late; search stage 3 before any Lean. | NORMATIVE | Useful duplication warning, but later search can still save work and early statement inspection is necessary for repair. | “Perform a reuse search before implementing a new helper, and repeat it when the goal changes.” |
| SK-132 | 325-328: every `NEW` verdict must have the four-step search record. | NORMATIVE | Audit policy; current runtime lacks several named tools (E9). | Require a reproducible search record using available tools, not fixed tool names. |
| SK-133 | 327-328: library is “~6,000 declarations with 189 notations.” | STALE | E11 does not reproduce either figure on the current tree, even under several reasonable lexical scopes. | Delete volatile counts or generate them with a documented script and snapshot hash. |
| SK-134 | 330-332: always generalize an existing wrong-type theorem in place/public; never specialize, use `private`, or add a local generic helper. | NORMATIVE | API policy with unsafe universal scope; generalization can break callers, imports, performance, and source fidelity. | “Prefer upstream public generalization when backwards-compatible and genuinely shared; otherwise add the smallest well-placed adapter with rationale.” |
| SK-135 | 334-338: `LanzenbergerChain` covers every numbered Ch. 2 item; no `MISSING` verdict without checking it. | OVERSTATED | Extensive name table exists but aggregate does not compile (E8), and completeness is self-asserted rather than checked. | “Search the table and underlying modules, then verify the row/source/build before deciding.” |
| SK-136 | 336-338: the same nonexistent gap was asserted twice in one session. | UNVERIFIED | No trace. | Cite or delete. |
| SK-137 | 340-342: modeling extra information as another system means one always owes a simulation. | OVERSTATED | See SK-112. | Use SK-112 replacement. |
| SK-138 | 341-343: a new system always adds a spurious ordering condition. | FALSE | A system can expose information from the start or through an explicit interface without a “revealed late” premise; the issue is construction-dependent. | “A late-reveal simulation may introduce an ordering obligation; check the interface semantics.” |
| SK-139 | 342-343: the new system is always a strictly stronger adversary than the bad-event analysis supports. | FALSE | Strength depends on the interface and restrictions; a definitional relabel or equivalent system need not strengthen anything. | Delete or make construction-specific. |
| SK-140 | 346-349: an augmented object must never appear in a theorem statement. | NORMATIVE | Proof-device hiding is a real risk, but an augmentation theorem can itself be a legitimate reusable statement. | “Headline security statements should mention intended worlds; state augmentation lemmas separately with an explicit projection/soundness theorem.” |
| SK-141 | 351-355: every imported paper term/event must have a kills/shrinks/leaves row. | NORMATIVE | Strong adaptation discipline. | Keep for paper adaptations; permit `not applicable` and require source citations. |
| SK-142 | 357-359: every packaged endpoint already reduces adaptivity and hands a fixed query schedule. | FALSE | E2's packaged H endpoints retain `h_bad : ∀ E : QQueryEnvironment ...`; only the CE blind endpoint E5 has the fixed blind-schedule leaf. | “The packaged CE endpoint performs this reduction; inspect other endpoint signatures individually.” |
| SK-143 | 361-362: direct statistical-distance manipulation always means family II was skipped. | FALSE | The H core itself proves direct distribution-level `δ`/`statDist` bounds (E2), and foundational metric lemmas legitimately manipulate distance. | “Before a difficult direct calculation, check whether a hybrid/DPI/restriction simplifies it.” |
| SK-144 | 364-365: if `cr18_total` fails, the system definition is wrong. | FALSE | SK-076/E3-E4. | Use SK-076 replacement. |
| SK-145 | 367-369: using `partition` when `eq_on_good` applies creates two extra creative goals. | FALSE | Current fixed-query endpoints each expose two creative legs: equality+bad mass versus cell ratio+weighted cell bound (E2).  Partition can make the legs harder, but not “two extra” by signature. | “Use the most specialized endpoint because its obligations are usually simpler; list the actual signature before comparing counts.” |
| SK-146 | 371-373: current H ratio direction is `(1-ε)·ideal ≤ real`. | VERIFIED | E2 at `Derivation.lean:398-405` has T/ideal on the left and S/real on the right. | Keep with named `S`/`T` mapping. |
| SK-147 | 372-373: reversing the inequality “type-checks against nothing.” | FALSE | The reversed inequality is still a valid Lean proposition and can fit the endpoint after swapping worlds/advantage orientation. | “It will not discharge this endpoint in the stated world order.” |
| SK-148 | 375-377: `maxEDist ≤ ofReal Δ` holds unconditionally. | FALSE | E6 requires `left.isProbDist` and `right.isProbDist`. | “For normalized laws, `maxEDist ≤ ENNReal.ofReal Δ`.” |
| SK-149 | 376-377: equality holds on every shared-domain object. | OVERSTATED | E6 requires two normalized laws and one common displayed domain `D`; “shared-domain object” is too loose. | State the exact `maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain` hypotheses. |
| SK-150 | 377-378: accepting `≤` when equality is available is always silent headline slack. | NORMATIVE | Equality is preferable for tight transfer, but an inequality may be the intended abstraction or enough for a local lemma. | “Use the equality receipt for normalized common-domain headline results when its hypotheses hold.” |
| SK-151 | 380-383: after exactly the second failed fix, always stop and restate; difficulty is usually self-inflicted. | NORMATIVE | The “second” threshold and “usually” frequency are unsupported. | “After repeated local failures, re-check statement shape and existing infrastructure before further patching.” |
| SK-152 | 385-387: a source-level `sorry`-free theorem can still depend on `sorryAx`; axiom-audit it. | VERIFIED | Lean's axiom dependency is transitive; `#print axioms` is the correct receipt. | Keep. |
| SK-153 | 389-392: compile+axiom-clean is never sufficient unless the argument is visible as the prescribed `calc`. | NORMATIVE | Review standard, not logical correctness; many readable proofs are not `calc`s. | “Also review proof readability and correspondence to the mathematical argument.” |
| SK-154 | 394-397: closing a goal proves viability, not route fit. | VERIFIED | Logical distinction is sound; no theorem says the proof is maintainable/appropriate merely because it typechecks. | Keep without the unverified ~90-line anecdote. |

### Reference-index claims

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SK-155 | 401-402: `sketch-and-plan.md` contains stages 1-3, template, adaptation table, DAG, search order/verdicts. | VERIFIED | Direct contents at lines 1-215. | Keep. |
| SK-156 | 403-405: `creative-search.md` contains fan-out/six angles/briefing/effort/synthesis and must be read whenever the bound is unknown or must improve a paper. | NORMATIVE | The file contains those topics, but mandatory use is workflow policy. | “Use for open-ended route discovery or bound improvement.” |
| SK-157 | 406-407: `h-technique.md` has three axes, five analyses, and exact creative nodes per variant. | OVERSTATED | The reference lists these, and E2 verifies five base analyses; “exact nodes” omits routine/typeclass/projection details and is not checked across every axis combination. | “Provisional creative-node summaries; confirm the chosen endpoint signature.” |
| SK-158 | 408-409: `conditional-equivalence.md` gives packaged/raw doors and CBC worked example. | VERIFIED | The reference headings and `CBCMAC.lean` support this. | Keep, add current build receipt for any recommended example. |
| SK-159 | 410-411: `counting.md` provides six doors including structure graphs, SoP, birthday tails. | STALE | The reference does list them, but a key advertised structure-graph implementation currently fails and contains `sorry` (E8). | Add a quarantine warning beside `CBCStructureGraph`; route to working counting files by default. |
| SK-160 | 412-413: `reshape-and-exact.md` covers families I/II/IV/V, coupling, winnability, metric receipt. | OVERSTATED | It contains those topics, but the winnability implementation is currently broken (E8), and the family numbering contributes to the inconsistent “seven” taxonomy. | Keep topic names, remove family numbers, add build status. |
| SK-161 | 415-416: full derivation exists at `skills/PROOF-WORKFLOWS.md`. | VERIFIED | The repo file exists and contains the stated derivation/design. | Use a repo-root-qualified link; note it is design prose, not primary evidence. |

## Claim ledger: `agents/openai.yaml`

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| OA-001 | 1-4: file is valid YAML with an `interface` map. | VERIFIED | Parsed successfully into the three expected scalar fields. | Keep. |
| OA-002 | 2: display name “Random Systems Proofs.” | VERIFIED | Consistent with frontmatter name and scope. | Keep. |
| OA-003 | 3: “Structure and verify Random Systems proofs.” | OVERSTATED | The skill structures work, but it cannot itself verify provisional interpretation/status claims; multiple advertised routes are currently broken (E8). | “Plan and audit selected Random Systems proofs.” |
| OA-004 | 4: default prompt asks the skill to formalize “this Random Systems security argument.” | OVERSTATED | Valid invocation syntax, but it omits the skill's exclusions and reliability requirement. | “Use $random-systems-proofs to plan and formalize this RS security bound; verify the route and signatures against current source.” |

## Claim ledger: `references/sketch-and-plan.md`

### Stage 1 and source-reading claims

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SP-001 | 1,5-8,12: stages 1-3 occur before Lean. | VERIFIED | Accurate description of this document's intended workflow. | Prefix “In this workflow.” |
| SP-002 | 12-14: Lean does not tell what you are proving; only whether it typechecks. | OVERSTATED | Lean shows the exact formal proposition/goal but cannot validate informal/source correspondence. | Use SK-129 replacement. |
| SP-003 | 13-14: a never-provable bound can survive much tactic work. | UNVERIFIED | No concrete primary case or measurement. | “A misstated bound can consume substantial elaboration effort before the mismatch becomes clear.” |
| SP-004 | 16: `sequence-hash/sketches/*.md` and `PLAN.md` §0.5 are in-repo precedents. | VERIFIED | E10: both exist and contain the described sketch/adaptation process. | Keep. |
| SP-005 | 16-18: a dispatch script fails loudly if the sketch-adaptation rule is missing. | OVERSTATED | E10: it fails if the **preamble file lacks one literal phrase**; it does not inspect the sketch or task output. | “The wrapper refuses dispatch if `PREAMBLE.txt` lacks the literal adaptation-policy marker.” |
| SP-006 | 18: the SequenceHash precedent generalizes to any RS proof. | OVERSTATED | Paper adaptation tables and dispatch guardrails do not fit every exact equality, refactor repair, or library lemma. | “Selected parts generalize to nontrivial paper-derived security proofs.” |
| SP-007 | 24: the sketch artifact must be Markdown/prose/LaTeX with no Lean. | NORMATIVE | Format rule. | Permit exact declaration names/types in a separate implementation map after the mathematical sketch. |
| SP-008 | 26-27: always place it beside work at `sketches/<result>.md` or scratch. | NORMATIVE | Path convention, not universal across repos. | “Use the repository's designated sketch/research-note location.” |
| SP-009 | 27: the sketch “is not a deliverable.” | FALSE | Directly conflicts with `SKILL.md:75`, which calls it “your first deliverable.” | Use one term consistently: “first working artifact.” |
| SP-010 | 27-28: it may be wrong and is cheaper to correct there. | NORMATIVE | Workflow rationale; “cheaper” is plausible but unmeasured. | “It may be revised before implementation; record status/uncertainty.” |
| SP-011 | 35-36: every sketch must name the technique in its first three sentences. | NORMATIVE | Style constraint. | “Name the proposed route near the start once enough source/model context is stated.” |
| SP-012 | 45-49: every parameter must be bound and no “up to constants.” | NORMATIVE | Appropriate for an exact formal target, but exploratory sketches can state provisional asymptotics with status labels. | “Before Stage 2, freeze an exact typed target with all parameters/hypotheses.” |
| SP-013 | 57-60: every sketch must name one rejected technique. | NORMATIVE | See SK-053. | Apply only when another route is genuinely plausible. |
| SP-014 | 62: an adaptation table is required whenever an argument comes from a paper. | NORMATIVE | Strong source-discipline policy. | Keep for nontrivial adaptations; allow a one-row “verbatim specialization” receipt when nothing changes, with proof. |
| SP-015 | 71-76: “paper is a template, not the answer”; blunt transcription is the most common loose-bound cause. | OVERSTATED | The adaptation warning is sound, but “most common” has no audit corpus. | Delete the superlative; require explicit term/event comparison. |
| SP-016 | 74-76: inherited extra terms remain provable but loose/invisible. | OVERSTATED | True when the extra term is non-negative and the source proof specializes, but not every copied term remains provable in a changed construction. | “Unnecessary non-negative terms can survive as silent slack; verify each specialization.” |
| SP-017 | 78-81: SequenceHash `PLAN.md` §3c requires kills/shrinks/leaves for every term/event. | VERIFIED | E10 lines 174-189. | Keep as attribution to that project. |
| SP-018 | 80-81: separation typically kills bookkeeping/aliasing, not inherent loss. | UNVERIFIED | Construction-dependent heuristic, not a primary theorem. | “Do not assume separation removes cascade-inherent terms; justify each row.” |
| SP-019 | 83-85: A2 opens by rejecting H and stating no H object belongs. | VERIFIED | E10 `A2-sequencemac-prf.md:19-23`. | Keep. |
| SP-020 | 83-85: that sentence is what stopped formalization drift. | UNVERIFIED | Causal process claim lacks a dispatch trace linking the sentence to the outcome. | “It records the intended route and makes drift reviewable.” |
| SP-021 | 89: papers must always be read visually. | NORMATIVE | PDF skill and E12 support visual verification for authoritative reading. | “Visually inspect every cited/relevant page; extraction may assist navigation.” |
| SP-022 | 89-91: never grep or extract a PDF text layer. | NORMATIVE | Overly restrictive: E12 shows CR18 has a useful text layer, while the thesis does not. | “Do not treat extraction as authoritative; use it only for navigation and confirm visually.” |
| SP-023 | 89-91: extraction fails silently across this repo's paper set, yielding zero hits for visible terms. | OVERSTATED | Verified for the scanned thesis, refuted as a set-wide implication by CR18's 351,777-byte text layer (E12). | “Some scanned PDFs (notably the thesis) have unusable text layers.” |
| SP-024 | 93-94: every passed-forward design premise must be checked in the source. | NORMATIVE | Sound source-audit rule. | Keep and require printed/PDF page coordinates. |
| SP-025 | 98-99: if a sketch cannot name technique/exact bound, mathematics is not understood and Lean cannot help. | FALSE | Lean/source inspection can reveal an incorrect endpoint, inferred parameter, or counterexample and thereby improve understanding. | “Do not begin implementation until the target is sufficiently precise; use Lean probes as diagnostic evidence, not a substitute for the argument.” |

### Stage 2 obligation-DAG claims

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SP-026 | 105: DAG artifact is a half-page node list with dependencies. | NORMATIVE | Format/size convention. | “Keep it as small as the proof permits.” |
| SP-027 | 107-108: node set is not invented; it is determined by the technique. | FALSE | Line 119 concedes sketch-specific intermediate nodes; endpoint instantiation also adds typeclass, normalization, monotonicity, and model-bridge obligations (E2/E5). | “The endpoint determines a base set; instantiation and the sketch may add nodes.” |
| SP-028 | 112: H `eq_on_good` creative nodes are good equality + ideal bad probability. | VERIFIED | E2 `Derivation.lean:439-447`, apart from routine totality/typeclass premises. | Label table “creative endpoint legs only.” |
| SP-029 | 113: H `ratio_of_good` creative nodes are good ratio + ideal bad probability. | VERIFIED | E2 `:398-406`, apart from routine premises. | Same qualification. |
| SP-030 | 114: H `partition` creative nodes are cell ratio + weighted cell bound. | VERIFIED | E2 `:732-740`. | Same qualification; delete the contradictory “two extra” claim elsewhere. |
| SP-031 | 115: packaged CE has exactly conditional equivalence + blind-schedule bad mass. | OVERSTATED | E5 also requires prefix monotonicity `hmono`, probability receipts, and ideal totality; `hmono` is not automatically routine for arbitrary `bad`. | List `bad_monotone` explicitly and label which receipts are library/tactic-proven for the chosen construction. |
| SP-032 | 116: coupling nodes are marginals + disagreement bound. | VERIFIED | Conceptually matches `DistCoupling` construction and `coupling_bound` (`Coupling.lean:149-151`). | Clarify that marginal proofs are fields of the coupling object and may split into two goals. |
| SP-033 | 117: union-bound nodes are cover + leaf sum. | OVERSTATED | This is a useful decomposition, but current union-bound lemmas can also require `NonNeg`, decidability, finite index/cardinality, or injectivity. | “Typical creative nodes; confirm the selected counting lemma's side conditions.” |
| SP-034 | 119: additional nodes come from sketch intermediates. | VERIFIED | Correct and directly contradicts the absolute at 107. | Keep; revise 107 accordingly. |
| SP-035 | 133: fill order is always leaves-first. | NORMATIVE | Default dependency order. | “Prefer topological order; allow statement/API discovery to revise the DAG.” |
| SP-036 | 133-135: proving a creative node before dependencies necessarily causes statement drift. | FALSE | It can be proved parametrically under explicit assumptions without drift; theorem statements themselves fix assumptions. | “Prematurely fixing a node can risk a non-composable statement; record dependencies explicitly.” |
| SP-037 | 137-149: displayed CE graph is a typical packaged CE proof. | OVERSTATED | It is plausible, but `bad_monotone` is labeled `[ROUTINE]` without a named tactic; E5 shows it is a caller premise. | Mark it `[LIB]` only when a named monotonicity theorem exists, otherwise `[CREATIVE]`/`[MODEL]`. |
| SP-038 | 151-152: exactly two leaves carry the whole typical CE proof; everything else is plumbing/citation. | UNVERIFIED | Depends on construction; no endpoint guarantees the two displayed sublemmas suffice. | “In this illustrative decomposition, two leaves are intended to carry the construction-specific content.” |
| SP-039 | 156: every node must have statement/class. | NORMATIVE | Planning gate. | Keep, add evidence/status field and expanded classes. |
| SP-040 | 156-158: if every node is creative, routing is wrong and a packaged endpoint exists. | FALSE | Same counterexample/reasoning as SK-062. | Use SK-062 replacement. |

### Stage 3 reuse-search and handoff claims

| ID | Exact line(s) and claim | Verdict | Evidence and reasoning | Safest replacement / delete |
|---|---|---|---|---|
| SP-041 | 164: exactly one verdict per node. | NORMATIVE | Audit format. | Allow compound states such as `BLOCKED(import)`, `ADAPT`, or multiple alternative reusable lemmas. |
| SP-042 | 166: REUSE means cite and never restate. | NORMATIVE | Reuse rule with exceptions (adapter, deprecation, axiom policy). | “Cite directly when the theorem applies and has admissible dependencies.” |
| SP-043 | 167: ADAPT always means generalize in place/public. | NORMATIVE | Unsafe universal API rule; see SK-134. | Use SK-134 replacement. |
| SP-044 | 168: NEW requires a one-line search record. | NORMATIVE | Sensible audit requirement. | Keep, using available tools and exact queries/scopes. |
| SP-045 | 172: listed order is always cheapest/highest-yield. | UNVERIFIED | No timing/hit-rate evidence; source authority and goal state can be cheaper than prose search. | “Suggested order; reorder when the target/source or runtime makes another step cheaper.” |
| SP-046 | 172: always stop at the first hit. | FALSE | First hit can be loose, deprecated, axiom-tainted, wrong orientation, or too specialized—the very slack risks the skill warns about. | “Record the first plausible hit, then compare strength/hypotheses with the target before stopping.” |
| SP-047 | 176: CHEATSHEET covers the listed topic areas. | VERIFIED | Current headings at `CHEATSHEET.md:89-574` cover each listed area. | Keep, avoid claiming completeness. |
| SP-048 | 177: repo grep also finds the worked example one should copy. | OVERSTATED | It can find examples, but there may be no applicable one and copying can inherit slack/model errors. | “Search for a source-faithful worked analogue; verify its route and status before adapting.” |
| SP-049 | 178-182: all named lean-lsp search tools are usable in the stated order. | STALE | E9: none is exposed in the current session. | Add availability guards and focused `#check`/scratch fallbacks. |
| SP-050 | 184-186: steps 5-7 matter because a good share of creative counting bottoms out in mathlib. | UNVERIFIED | “Good share” has no counted corpus. | “Many counting leaves may reduce to mathlib facts; search mathlib when the residual goal is generic.” |
| SP-051 | 185-186: grepping this repo does not search mathlib. | VERIFIED | A repo-scoped `rg` cannot inspect dependency source outside its roots. | Keep. |
| SP-052 | 190-194: always generalize in place; never write a specialized copy. | NORMATIVE | See SK-134. | Use SK-134 replacement. |
| SP-053 | 196-198: never `private`, never a local generic helper; every general fact must be public framework API. | NORMATIVE | Private/local lemmas can be appropriate proof organization, prevent API pollution, and avoid dependency cycles. | “Promote genuinely reusable stable facts; keep proof-local helpers local unless another caller is identified.” |
| SP-054 | 202-203: a `NEW` without search record is never a verdict. | NORMATIVE | Audit convention. | Keep as process policy. |
| SP-055 | 209-211: after stage 3 one always has exact bound, endpoint, obligation names/fill order, and reuse/new decision; stage 4 is mechanical. | OVERSTATED | Open modeling choices, blocked imports, endpoint mismatch, and creative statement refinement can remain; E8 supplies current upstream blockers. | “This is the desired readiness state; if any item remains uncertain, mark it explicitly rather than calling Stage 4 mechanical.” |
| SP-056 | 211: stage 4 must write `refine`, `sorry` leaves, and compile. | NORMATIVE | See SK-080. | Use temporary scratch skeleton wording and admission-removal gate. |
| SP-057 | 213-214: goal/DAG mismatch has only endpoint-wrong or plan-wrong causes. | FALSE | Missing instances/imports, changed signatures, coercion elaboration, and stale dependencies are additional causes. | “Reconcile signature, environment, and plan.” |
| SP-058 | 214-215: Lean gives no warning and DAG is the only check. | FALSE | Lean exposes actual goals and rejects unresolved goals/type mismatches; source review, theorem signatures, tests, and proof review are also checks. | “Lean does not compare goals with your external intent; use the DAG as one review receipt.” |

## Recommended disposition

Before relying on this skill for autonomous proof repair:

1. Keep the reliability notice and make it fail closed: current endpoint signatures/build receipts outrank all routing prose.
2. Remove the false universal premises (`ANY theorem`, every security statement, closed seven families, tactic failure = model bug, every packaged endpoint fixed-schedule).
3. Replace `always`/`never` workflow rules with defaults plus explicit exceptions for diagnosis, trivial proofs, source checks, and API compatibility.
4. Correct current quarantine/status: `GameWinnability`/`LanzenbergerChain` and `CBCStructureGraph` are not reliable routes; `BoundedAttainment` itself currently compiles.
5. State exact positivity/normalization/shared-domain hypotheses for orientation and strict-metric bridges.
6. Make all search-tool advice capability-conditional and keep `lake env lean <file>`/`#check` as the portable fallback.
7. Reconcile the sketch's status (“first deliverable” versus “not a deliverable”) and label DAG tables as **creative legs only**, not complete endpoint signatures.
