# Blind audit B: proof-family references

Status: **independent cross-review, frozen working-tree snapshot**

This report audits the factual content of the following files without editing
them:

- `h-technique.md`, SHA-256
  `035cc360c02cae09b4d004cc0fb8bda43ab392602cdd077da119bc4cf018196a`;
- `counting.md`, SHA-256
  `a044e39fefce65d1c8b0efcab60194587d9cf60a3d1f85840ee1d9d4caebce12`;
- `reshape-and-exact.md`, SHA-256
  `5a6e998ab2e00e2a64f2cc9994fda0a3db16718eebdfbcaa4b172620fbaeff3e`;
- `creative-search.md`, SHA-256
  `6d71c6aa3ef1797d054b2dced348630e4e3c6fd35778f6e8da0991e45eb2341e`,
  excluding lines 31--58 as required by the review brief.

Seal note: a final integrity check found that `reshape-and-exact.md` had moved
after the audit, from the frozen hash above to
`c61076d43c9a4402ea1b6b4b25a4a93b8ae4752912b413b2bbf6996153fe24f4`.
This report remains intentionally pinned to the earlier hash whose text and
line numbers were actually audited; it makes no claim about the post-audit
revision. The other three target hashes still matched at sealing time.

Except for the explicitly marked H-010 row, the Lean evidence below comes from
independent declaration inspection plus focused
`lake env lean FILE` checks in the current tree. Paper claims were checked
against the local primary PDFs (`LanMau20.pdf`, `thesis (1).pdf`,
`Maurer02.pdf`, and `CR18_LN.pdf`). The Jha--Nandi numerical claim was checked
against the journal article, and the multi-agent claim against Anthropic's
first-party engineering report.

Verdicts:

- **VERIFIED**: the statement and its stated scope agree with the current
  declaration, focused build, or primary source.
- **QUALIFY**: the core statement is right, but its wording can invite a
  stronger reading than the evidence supports.
- **HEURISTIC / NORMATIVE**: useful project advice, but not a theorem or an
  empirically established universal claim.
- **STALE STATUS**: source text exists, but the current module does not build
  or its proof depends on admitted material.
- **FALSE**: contradicted by the current declaration or source.

## Executive conclusion

The current revisions are substantially accurate. I found **no false theorem
signature or numerical theorem claim in the three mathematical references**.
The most important remaining qualifications are status-related:

1. `RandomSystems.HTechnique.Tactics` still does not build because
   `RandomSystems/HTechnique/SoP/VisibleLaw.olean` is absent; the reference now
   says this correctly.
2. The winnability/representative wrappers and several legacy condition-based
   modules remain unusable as current release receipts because their import
   chain fails and/or contains admissions; the reference now says this
   correctly.
3. `CBCStructureGraph.lean` still has an admitted central mass theorem; the
   counting reference now warns against presenting the headline as complete.
4. The exact SoP source argument is closed in source, but its current aggregate
   import path is not build-clean because of the signed-distribution migration.
   The revised references avoid claiming otherwise.

The residual recommendations below are mostly small scope clarifications, not
mathematical corrections.

## `h-technique.md`

| Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement or action |
| --- | --- | --- | --- | --- |
| 3--4 | This reference applies when the comparison is equality or a one-sided likelihood bound outside a transcript-prefix predicate. | VERIFIED | `adv_le_of_fixedQuery_eq_on_good` and `adv_le_of_fixedQuery_ratio_of_good` have precisely those hypotheses. Expectation and partition variants extend the same pattern. | Keep. |
| 17--20 | The ordinary fixed-query endpoints compare fixed-query transcript laws and lift to adaptive transcript advantage. | VERIFIED | `RandomSystems/HTechnique/Derivation.lean:398--487`; the proofs invoke the adaptive pointwise lift after transferring the fixed-query hypothesis. | Keep. |
| 22--35 | The displayed equality-on-good signature is the current endpoint shape. | VERIFIED | It matches `Derivation.lean:439--447`, modulo display notation and implicit universe/typeclass parameters. It includes both `KStepTotal` hypotheses, the pointwise equality for every query vector/transcript, and the adaptive bad-mass premise for every `QQueryEnvironment`. | Keep. If copy/paste compilation is intended, label the block “schematic signature”; as paper notation it is already safe. |
| 37--43 | Ratio-on-good replaces equality by `(1-eps) * tr(T,xs)(t) <= tr(S,xs)(t)` and concludes `delta_b + eps`. | VERIFIED | Exact declaration at `Derivation.lean:398--407`. | Keep. |
| 43--45 | In the repository's one-sided H theorem, ideal mass is on the left and real mass on the right. | VERIFIED | The endpoint's actual inequality has `tr(T, xs)` on the multiplicative left and `tr(S, xs)` on the right; the theorem concludes `Adv(S,T)`. | Keep. |
| 47--50 | The derivation contains expectation, partition, selected extended, and filtered variants, but not a complete Cartesian-product API. | VERIFIED | Current declarations include ordinary expectation/ratio/partition/equality, selected extended endpoints, fixed-query representative endpoints, and filtered forms. Not every transcript-model/analysis/filter triple exists. | Keep. This correction is important. |
| 54--67 | The endpoint-choice table and “prefer the narrowest matching endpoint” rule are workflow recommendations, not a theorem hierarchy. | HEURISTIC / NORMATIVE | The mapping is consistent with the endpoint hypotheses, but “narrowest” is a proof-engineering policy. The text correctly labels it as such. | Keep. |
| 64--67 | A missing combination requires a justified bridge or a new theorem at the correct layer; names do not prove existence. | VERIFIED as methodology | This is logically sound and avoids the former Cartesian-product overclaim. | Keep. |
| 69--71 (H-010) | Selector and labelled-spine tooling lives in the sibling `ccprover`, not this repository. | **CONTAMINATED — do not count toward the independent-review gate** | An overbroad source search accidentally displayed another review's verdict for this exact availability/location claim before my source check. Direct inspection subsequently found `../ccprover/CCProver/Surface/Techniques.lean` defines the three axes, the 15-case selector, and `#h_grammar`, while `../ccprover/CCProver/RS/Teaching/OrdinaryH.lean` provides the labelled teaching spine; no corresponding command was found in `random-systems`. Because of the exposure, this evidence is recorded for traceability but requires a fresh reviewer. | Keep only after independent confirmation; do not use this row as one of the two blind reviews. |
| 75--78 | Ordinary adaptive H requires an ideal bad-probability bound for every `QQueryEnvironment`; one externally fixed schedule is insufficient without a uniform transfer. | VERIFIED | Both ordinary endpoints quantify `h_bad : forall E : QQueryEnvironment ...`. A bound uniform over all schedules/environments can discharge it, but a theorem about one chosen schedule cannot. The revised “unless” clause captures this. | Keep. |
| 80--84 | The fixed-query fact, totality, and uniform adaptive bad-mass bound are distinct obligations. | VERIFIED | These are separate arguments in the endpoint signatures. | Keep. |
| 86--88 | The packaged CE leaf instead uses each blind winner's fixed `blindQueryList`; H and CE schedule scopes must not be interchanged. | VERIFIED | `maxAdvantage_filterQueries_seededConditionCGame_le` in `SwitchingLemma.lean:1891--1905` asks for `D.mass (bad a (blindQueryList w q)) <= eps` uniformly in `w`. | Keep. |
| 92--94 | Repeated-query compression is not generic for stateful systems and needs an exact construction-specific theorem. | VERIFIED | A stateful oracle can react differently on repetitions. `QueryCompression.lean` proves an evaluator-specific identity, not a universal stateful identity. | Keep. |
| 98--99 | `transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress` is exact in the function-evaluator scope. | VERIFIED | `RandomSystems/QueryCompression.lean:150--166` gives equality of the original transcript law and the pushforward of the compressed transcript law for `functionEvaluatorRV`. | Keep. |
| 100--101 | `compressedQuery_bound` transports the cubic numerical side condition. | VERIFIED | `QueryCompression.lean:116--119` proves compressed-cardinality cubed is at most `N^2` from `q^3 <= N^2`; it is not a law equality. | Keep. |
| 102--103 | `htechnique_compress` is a narrow SoP rewrite tactic over registered transcript-law lemmas. | VERIFIED | `RandomSystems/HTechnique/Tactics.lean` defines it as a fixed `simp only` bundle of SoP compression lemmas. | Keep. |
| 105 | None of the preceding objects is a generic stateful-query compression theorem. | VERIFIED | Their signatures/scopes are construction-specific. | Keep. |
| 109--111 | H tactics are finite rewrite/constructor collections and are not decision procedures for totality, normalization, compression, or reductions. | VERIFIED | `htechnique_total`, `htechnique_adv_le`, and the compression tactic are explicit finite `first`/`simp only` bundles. | Keep. |
| 113--115 | The three tactic descriptions match their current roles. | VERIFIED | Direct inspection of `RandomSystems/HTechnique/Tactics.lean` and `TotalityTactics.lean`. | Keep. |
| 117--118 | A theorem can exist even when automation does not know it, so imports and the goal should be checked first. | VERIFIED as methodology | Registered tactic branches are strictly smaller than the theorem surface. | Keep. |
| 119--121 | The aggregate H-tactics build is currently blocked by an imported SoP migration file. | VERIFIED, snapshot-sensitive | Fresh check: `lake env lean RandomSystems/HTechnique/Tactics.lean` fails because `RandomSystems/HTechnique/SoP/VisibleLaw.olean` does not exist. A focused build of `VisibleLaw.lean` exposes signed-carrier migration errors. | Keep, but retain “in the audited snapshot” because this is transient. |
| 125--137 | The equality-on-good proof plan has totality, fixed-query equality, and uniform adaptive bad mass; constructions can add further obligations. | VERIFIED | This is exactly the core endpoint signature, with an appropriately explicit warning that wrappers can generate more goals. | Keep. |
| 141--147 | The top-level application skeleton names the correct endpoint and orders its principal hypotheses correctly. | VERIFIED | It matches the declaration in namespace `RandomSystems.CR18.HTechniqueDerivation`. | Keep. |
| 149--152 | Ratio proofs must state the one-sided inequality; extended proofs additionally require projection, nonnegativity, weight, and totality assumptions according to the selected signature. | VERIFIED | The extended endpoints in `Derivation.lean` carry precisely these extra premises, although the exact list varies by endpoint. | Keep. |
| 154 | Focused compilation plus `#print axioms` is required as a delivery check. | NORMATIVE | Appropriate repository policy, not a mathematical assertion. | Keep. |

## `counting.md`

| Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement or action |
| --- | --- | --- | --- | --- |
| 3--5 | Counting is a downstream obligation, not necessarily the whole security proof family. | HEURISTIC / NORMATIVE | This is a useful architectural distinction and avoids falsely classifying ratios, couplings, or CE bridges as mere counting. | Keep. |
| 17--23 | Carrier/law, nonnegativity, event decidability, quantifier scope, and required bound should be recorded before counting. | NORMATIVE | All are real premises that occur in the cited Lean endpoints. | Keep. |
| 25--27 | A counting leaf may be raw mass, ratio defect, coupling disagreement, or cardinality rather than `probBad`. | VERIFIED | All four goal shapes occur in the current library (`Dist.mass`, H expectation/ratio, `DistCoupling.prDisagree`, and finite fiber lemmas). | Keep. |
| 31--39 | The displayed `probBad_iUnion_le` is the current finite-index union theorem. | VERIFIED | Exact declaration at `RandomSystems/StatDist.lean:467--477`, including `hD`, two `Fintype` instances, and decidability of each piece. | Keep. |
| 41--47 | A correct application supplies the nonnegativity proof first. | VERIFIED | `hD` is the first explicit argument after the implicit distribution; the displayed refinement has the correct order. | Keep. |
| 49--60 | `mass_biUnion_le` has the displayed finite-`Finset` signature and requires `[Nonempty A]` and `X.NonNeg`. | VERIFIED | Exact declaration at `RandomSystems/SwitchingLemma.lean:55--57`. | Keep. |
| 62--64 | Event cover and leaf estimates are separate, overlaps are allowed, and the resulting sum may be loose. | VERIFIED | The union theorem assumes only an existential cover and uses subadditivity; it does not require disjointness. | Keep. |
| 66--69 | `probBad_le_of_ratio` uses normalized/nonnegative laws, zero comparison-law bad mass, and a pointwise one-sided ratio. | VERIFIED | Exact declaration at `Derivation.lean:3849--3855`; `P` and `Q` each have nonnegativity and weight-one premises, `Q.mass B = 0`, and `(1-delta)Q <= P` on good points. | Keep. |
| 73--77 | The packaged seeded CE endpoint fixes `blindQueryList w q` for each winner and is uniform in `w`. | VERIFIED | `SwitchingLemma.lean:1891--1905`. | Keep. |
| 78--79 | Ordinary adaptive H quantifies bad mass over every query environment. | VERIFIED | `Derivation.lean:398--447`. | Keep. |
| 80--81 | A coupling's counting leaf is determined by its chosen joint law and may preserve adaptive state. | VERIFIED with scope | This is a structural possibility, not a guarantee that every coupling is causal/adaptive. “May” is the correct qualifier. | Keep. |
| 83--84 | Schedule scopes cannot be swapped without a reduction; repeated-query compression is construction-specific. | VERIFIED | Follows from the incompatible endpoint quantifiers and evaluator-specific compression theorem. | Keep. |
| 88--97 | Exact fibers, partitions, conditional products, ratios, expectations, symmetry, and direct coupling are alternatives to a union bound. | VERIFIED as catalogue | Corresponding techniques/declarations occur in the tree. The list does not assert universal applicability. | Keep. |
| 99--105 | `pairCollisionUnionBound_le_birthday` bounds the particular expression by `1/2 * r^2 / card(X)`. | VERIFIED | Exact theorem at `SwitchingLemma.lean:1705--1718`. It is an `NNReal` expression cast to `Real`, exactly as the text indicates. | Keep. |
| 107--108 | The generic pair-collision theorem does not supply a construction-specific event cover. | VERIFIED | Its theorem statement mentions only `pairCollisionUnionBound X r`; no construction event occurs. | Keep. |
| 110--118 | The five-layer exact-cardinality workflow distinguishes event, descriptor/fiber, count, mass, and numerical simplification. | NORMATIVE | Sound proof organization, not a universal theorem dependency graph. | Keep. |
| 122--130 | Verification bullets require premises/casts/axiom inspection rather than trusting notation or automation. | NORMATIVE | Appropriate formalization discipline. | Keep. |
| 132--134 | `CBCStructureGraph.lean` is not a completed beyond-birthday route because its central mass bound is admitted and the headline has `sorryAx`. | VERIFIED, snapshot-sensitive | `mass_cbcGraphBad_le` at `CBCStructureGraph.lean:1423--1428` ends in `sorry`; the downstream theorem invokes it. The file header also labels the counting leg open/provisional. | Keep. |

### Jha--Nandi numerical context

The revised counting reference no longer states a precise Jha--Nandi formula,
so there is no numerical overclaim to correct. For context, the primary journal
paper gives the corrected structure-graph analysis with order
`O(sigma*q/2^n)` and explicit fixed-message-length terms including
`12*ell*q^2/2^n + 16*ell^4*q^2/2^(2n)`. This supports describing the intended
route as beyond-birthday in the appropriate parameter regime, but it does not
turn the admitted Lean mass theorem into a completed result.

Primary source: Ashwin Jha and Mridul Nandi, “Revisiting Structure Graphs:
Applications to CBC-MAC and EMAC,” *Journal of Mathematical Cryptology*,
DOI [10.1515/jmc-2016-0030](https://doi.org/10.1515/jmc-2016-0030).

## `reshape-and-exact.md`

| Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement or action |
| --- | --- | --- | --- | --- |
| 20--27 | Before bounding, one should check exact equivalence after behavioral, relabelling, restriction/post-processing, or construction-specific compression transformations. | VERIFIED as catalogue / NORMATIVE as priority | The tree contains the corresponding quotient/equivalence, strict relabelling, DPI/filter, and evaluator-compression results. Applicability remains construction-specific, as the text says. | Keep. |
| 29--32 | `compressedQuery_bound` is numerical, while `transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress` is the exact evaluator-law result. | VERIFIED | `QueryCompression.lean:116--119` versus `150--166`. | Keep. |
| 34--36 | Lanzenberger's nonadaptive-sufficiency theorem is about exact transcript equivalence, not arbitrary numerical adaptive advantage. | VERIFIED | Thesis Lemma 2.18 (printed p. 16) characterizes equivalence by compatible nonadaptive deterministic environments. Lean: `RandomSystem.lean:785--789` and wrapper `LanzenbergerChain.lean:180--189`. Neither states a general numerical advantage reduction. | Keep. |
| 40--43 | Triangle, application/DPI, parallel, and query-filter inequalities exist, but their side conditions differ. | VERIFIED | `maxAdvantage_triangle` has no extra premise; `maxAdvantage_apply_le` requires both laws nonnegative and an `Emulable` converter; `maxAdvantage_par_le` requires probability laws; `maxAdvantage_filterQueries_le` requires a dummy value and totality. The generalized wording is accurate. | Keep. |
| 45--55 | The hybrid calculation is justified by triangle inequality, while choosing the hybrid is separate mathematical work. | VERIFIED | `maxAdvantage_triangle` in `AbsorbDPI.lean:1030--1040` has the displayed orientation. | Keep. |
| 57--61 | Additivity lemmas exist for appropriate disjoint-support decompositions and their current nonnegativity assumptions must be respected without claiming logical necessity. | VERIFIED | `TranscriptBranchDistance.lean` contains such a branchwise decomposition and currently assumes nonnegativity on the second law. The wording correctly distinguishes theorem signature from necessity. | Keep. |
| 65--68 | `transcriptDist` is a deterministic pushforward, so DPI compares deterministic coarse/fine observations under its premises. | VERIFIED | Modern `RandomSystem.transcriptDist` is defined as `Dist.fTransform (fun s => transcript s e n) S` at `RandomSystem.lean:501--503`. | Keep. |
| 70--77 | Post-hoc annotations can use observation refinement, whereas information exposed during interaction may change later queries and require simulation/interface work. | VERIFIED as modeling principle | A deterministic pushforward cannot model feedback from newly revealed information into later queries. “May” avoids overclaiming. | Keep. |
| 81--87 | An unqualified coupling is a nonnegative joint with two marginals; the standard proof obligations are construction, marginals, and disagreement. | VERIFIED | `DistCoupling` contains a nonnegative joint and the two marginal equalities; `coupling_bound` at `Coupling.lean:149--150` bounds distance by disagreement. | Keep. |
| 89--92 | `optimal_probability_coupling_exists` gives a normalized joint of two fixed normalized PDS laws whose DDS disagreement equals raw `delta S.val T.val`. | VERIFIED | Exact declaration at `RandomSystemCoupling.lean:48--66`. | Keep. |
| 94--100 | That theorem alone does not choose equivalent representatives, identify class distance, ensure causality, or estimate the exact expression. | VERIFIED | None of those conclusions appears in its signature. The stronger representative theorem is a separate declaration with finite common-domain/bounded hypotheses. | Keep. |
| 102--104 | A sequential coupling can be looser than maximal coupling, and one should separate joint-law loss from estimation loss. | VERIFIED possibility / NORMATIVE diagnosis | Maximality is an existence property for fixed laws; a tractable causal construction need not attain it. The wording uses “can,” not “must.” | Keep. |
| 108--111 | Representatives are selected by transcript-law equivalence rather than strict CE; current attainment/coupling theorems make finite/common-domain assumptions explicit. | VERIFIED with scope | Thesis Theorem 2.31 and the Lanzenberger--Maurer attainment/coupling results work at the random-system equivalence-class level. The modern Lean representative-coupling theorem is `exists_equivalent_representatives_with_probability_coupling_disagreement_eq_optimal_advantage_of_finite_common_domain_and_bounded` in `RandomSystemCoupling.lean:112--131`. | Keep. “Current Lean theorem” could be inserted before “finite, common-domain setting” if readers might interpret it as a claim about every abstract formulation in the papers. |
| 113--116 | The thesis winnability theorem says optimal winnability equals winnability and supplies an attaining representative; it is not merely `Delta <= nu`, nor intrinsically an MBO theorem. | VERIFIED | Thesis Theorem 2.37, printed p. 24, states `nu(S^A)=omega(S^A)` and attainment. Its alternative proof on printed p. 26 uses the representative theorem. MBO monotonicity is an extra property of a chosen game/event, not part of the theorem statement. | Keep. |
| 118--119 | CE, winnability, and representative attainment can be bridged but are not synonyms. | VERIFIED conceptual distinction | Their definitions and theorem premises differ. In particular, CE is a relation between systems under an event, while representative equivalence/attainment is an equivalence-class statement. | Keep. This distinction directly prevents mixing “representative” language into a CE endpoint. |
| 121--124 | The current `LanzenbergerChain`/`GameWinnability` path is build-blocked and includes admitted material. | VERIFIED, snapshot-sensitive | Fresh focused checks fail in the signed-distribution migration/import chain; `GameWinnability.lean` also emits admission warnings. Therefore its source declarations are not current release receipts. | Keep. |
| 128--135 | A signed joint is an algebraic expansion, not an honest coupling; sound use needs an exact signed identity plus a norm/positive-part conversion. | VERIFIED | Negative coefficients violate `Dist.NonNeg`/`DistCoupling`. A signed decomposition can still bound a genuine distance only through a separately proved analytic inequality. | Keep. |
| 137--139 | Signed objects cannot instantiate an ordinary distribution/coupling theorem without a new signed-carrier theorem. | VERIFIED | The Lean premises require `Dist`, nonnegativity, and the ordinary marginal equations. Signed coefficients do not satisfy those premises by notation alone. | Keep. |
| 143--149 | Outside normalized laws, orientation matters; under nonnegativity, `Adv S T = Delta(T,S)`. | VERIFIED | Exact theorem `adv_eq_maxAdvantage_swap` at `RandomSystem.lean:1819--1822`. The swap is forced by the repository's advantage convention. | Keep. |
| 153--160 | The displayed strict-metric inequality and its two probability hypotheses are exact. | VERIFIED | `StrictContextAdvantage.lean:403--409`. | Keep. |
| 162--172 | Equality with `ENNReal.ofReal Delta` additionally requires a shared fixed domain, with the displayed signature. | VERIFIED | `StrictContextSharedDomain.lean:934--945`. | Keep. |
| 174--176 | The narrower `filterDom` result should only be used for that shape; neither inequality nor equality is unconditional/arbitrary-domain. | VERIFIED | `maxEDist_filterDom_eq_ofReal_maxAdvantage_filterDom_of_total` is a corollary for filtered total laws. Both generic results have explicit normalization, and equality has shared-domain premises. | Keep. |
| 180--183 | Legacy condition, composition, amplification, representative, and winnability source files can fail current builds or depend on admissions. | VERIFIED, snapshot-sensitive | Focused checks: `Legacy/ConditionBased.lean`, `Legacy/Equiv.lean`, `GameWinnability.lean`, and dependent wrappers are not build-clean; the amplification theorem contains an admitted branch. | Keep. |
| 185--187 | Current amplification and CBC structure-graph headlines must not be presented as complete when `#print axioms` exposes `sorryAx`. | VERIFIED | `Legacy/Amplification.lean` has `sorry` in `amplification_theorem`; `CBCStructureGraph.lean` has `sorry` in `mass_cbcGraphBad_le`, which feeds the headline. | Keep. |

### Exactness, optimality, and nonadaptivity receipts

These were called out explicitly in the review brief.

- **Exact nonadaptive claim:** VERIFIED only for transcript-law equivalence.
  Thesis Lemma 2.18 and
  `transcript_equivalent_of_nonadaptive_transcript_equivalent` do not say that
  every numerical adaptive advantage is attained nonadaptively.
- **Maximal coupling exactness:** VERIFIED for two fixed normalized laws.
  `optimal_probability_coupling_exists` does not by itself prove optimality at
  the random-system equivalence-class level.
- **Representative-level optimality:** VERIFIED under the modern Lean
  theorem's finite common-domain/bounded hypotheses. The longer theorem at
  `RandomSystemCoupling.lean:112--131` produces equivalent representatives and
  a normalized joint whose disagreement is exactly `Adv`.
- **Winnability optimality:** VERIFIED in the primary thesis statement, but
  **STALE STATUS** as a current Lean release claim because the wrapper path is
  not build-clean and includes admitted material.
- **Legacy `delta_eq_advantage`:** not claimed by the revised reference. This
  is good: the legacy source theorem depends on an admitted attainment lemma
  and its module is not currently buildable.

## `creative-search.md`, audited lines 1--30 and 59--117 only

| Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement or action |
| --- | --- | --- | --- | --- |
| 1--4 | The file is project workflow advice, not a theorem of completeness or optimality. | VERIFIED self-description | The allowed sections are framed as selection and review policies, not mathematical implications. | Keep. |
| 17--23 | Independent scouts are most useful for unknown targets, genuinely different decompositions, suspected construction-specific slack, or source interpretation review. | HEURISTIC / NORMATIVE | Reasonable delegation criteria, but no universal performance theorem establishes these exact four triggers. | Keep because the file explicitly labels itself advice. |
| 25--26 | A single elaboration error or tightly dependent fragments should not be parallelized. | HEURISTIC / NORMATIVE | Usually sound due coordination overhead, but project/tool conditions can produce exceptions. | Keep as guidance, not as an absolute empirical law. “Usually do not” would be maximally cautious. |
| 30 | Every scout should receive the same mathematical statement and evidence set. | NORMATIVE | This controls experimental comparability; it is not a theorem. | Keep. |
| 59--60 | Exploration categories can overlap, so a scout should state its distinctive question and report convergence. | HEURISTIC / NORMATIVE | Sound review hygiene. | Keep. |
| 62--64 | Changing an MBO, simulator, coupling, or representative changes the obligations of the proof object; merely naming one does not establish the desired rate. | VERIFIED logical claim | The security conclusion follows only after the selected object's hypotheses, identity, and bad/disagreement bound are proved. | Keep. |
| 68--77 | Blind first-pass independence and source-based resolution reduce cross-contamination; vote counts do not settle mathematical disagreement. | VERIFIED as review methodology | Direct source/Lean evidence is dispositive in a way majority agreement is not. | Keep. |
| 79--81 | Paper-design scouts should normally return mathematics; a focused formal probe is useful for a precise uncertainty. | HEURISTIC / NORMATIVE | Workflow policy, correctly qualified by “normally” and “appropriate when.” | Keep. |
| 85--95 | Each proposal should state a finite theorem, define objects, give the implication chain and inequality locations, compare regimes, discuss attacks, and isolate unproved lemmas. | NORMATIVE | These are appropriate completeness criteria for a pen-and-paper proposal. | Keep. |
| 97--99 | Consensus can reflect either shared conclusions or a shared blind spot/premise/effort/decomposition failure. | VERIFIED possibility | Consensus is not logically sufficient for truth; each listed failure mode is possible. The sentence does not claim a probability. | Keep. |
| 101--103 | Mathematical validity comes before strength, scope, simplicity, and formalization cost; a distinct runner-up can be worth preserving. | NORMATIVE | Explicit project value ordering, not a factual theorem. | Keep. |
| 107--114 | Before Lean, merge the paper proof, enumerate obligations, distinguish imported facts from new lemmas, mark conjectures, and compare generated goals. | NORMATIVE | Sound formalization workflow and consistent with repository policy. | Keep. |
| 116--117 | Formalization validates a complete selected argument but does not make an incomplete paper argument proved retroactively. | VERIFIED logical claim | Lean proves the encoded theorem from the encoded premises; an omitted mathematical lemma remains an omission unless encoded and proved. | Keep. |

### Required 90.2% attribution check

The review brief separately required the “90.2%” claim to be checked. At the
hash audited here, its target occurrence lies inside the expressly excluded
line interval, so I did not inspect or quote that line and cannot attach an
exact target line number without violating the scope restriction.

The underlying narrow claim is **VERIFIED** against Anthropic's first-party
report: Anthropic says its lead-agent/subagent system (Claude Opus 4 leading
Claude Sonnet 4 subagents) outperformed a single-agent Claude Opus 4 setup by
90.2% on Anthropic's **internal research evaluation**. The article also argues
for parallel, independent directions in breadth-first research. This does
**not** establish that multi-agent work is generally 90.2% better, that the
gain transfers to theorem proving, or that any fixed fan-out is optimal.

Safest wording:

> In one Anthropic internal research evaluation, an Opus 4 lead coordinating
> Sonnet 4 subagents outperformed a single Opus 4 agent by 90.2%. Treat this as
> system-specific empirical motivation for independent exploration, not a
> general theorem about mathematical research.

Primary source: Anthropic, [How we built our multi-agent research
system](https://www.anthropic.com/engineering/multi-agent-research-system).

## Build receipts

The following focused checks succeeded in the audited snapshot:

- `RandomSystems/HTechnique/Derivation.lean`;
- H examples `HashThenPRF.lean`, `TweakablePRP.lean`, `StrongPRP.lean`,
  `HCTR2Paper.lean`, and `IdealCompression.lean`;
- `RandomSystems/RandomSystemQuotient.lean` and `StrictRelabel.lean`;
- `RandomSystems/AbsorbDPI.lean`, `BlindAbsorption.lean`, and
  `BlindConverter.lean`;
- `RandomSystems/Coupling.lean`, `DistCoupling.lean`, and
  `RandomSystemCoupling.lean`;
- `RandomSystems/StrictContextAdvantage.lean`,
  `StrictContextSharedDomain.lean`, and `AttainmentCounterexample.lean`;
- `RandomSystems/CBCMAC.lean`.

The following relevant focused checks failed or exposed admissions:

- `RandomSystems/HTechnique/Tactics.lean`: missing imported
  `HTechnique/SoP/VisibleLaw.olean`;
- `RandomSystems/HTechnique/SoP/VisibleLaw.lean`: signed-carrier type migration
  errors and admissions;
- `RandomSystems/GameWinnability.lean`, `LanzenbergerChain.lean`, and
  `Legacy/ConditionBased.lean`: build/import failures in the migration path,
  with admitted material;
- `RandomSystems/Legacy/Equiv.lean` and its dependent legacy fundamental,
  system-coupling, composition, and amplification paths;
- `RandomSystems/CBCStructureGraph.lean`: central admitted mass bound;
- `RandomSystems/MultiSystemCoupling.lean`: signed-carrier migration errors and
  admissions.

## Final recommended changes

No mandatory mathematical rewrite is needed for the three current
mathematical references. Retain their present scope warnings. Two optional
clarifications would make them even safer:

1. In `h-technique.md`, call the displayed Lean block a “schematic signature”
   if it is not intended for direct copy/paste with all namespace/import
   details.
2. In `reshape-and-exact.md:108--111`, say “the current Lean attainment and
   representative-coupling theorems” before the finite/common-domain phrase,
   distinguishing the implementation receipt from every abstract formulation
   in the papers.

The creative-search material is correctly marked as advice. Keep the 90.2%
claim narrowly tied to Anthropic's one internal evaluation and do not promote
it to a general theorem or theorem-proving benchmark.
