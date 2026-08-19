# Independent audit of the proof-family references

Date: 2026-08-06

## Scope and method

This ledger audits every substantive claim in the following frozen skill
references:

- `h-technique.md`, lines 1--164;
- `counting.md`, lines 1--141;
- `reshape-and-exact.md`, lines 1--183;
- `creative-search.md`, except lines 31--58, which belong to the separate
  conditional-equivalence audit.

Line numbers refer to the SHA-256 snapshots recorded in
`review/random-systems-skill/AUDIT_PLAN.md`. Pure headings, contents lists,
and separators are covered but need no independent factual verdict. Workflow
preferences are marked `NORMATIVE`; that label does not endorse them as the
only sound workflow.

Claims about the library were checked against the declarations in this
checkout, with `#check`/`#print axioms` receipts in
`FamilyAuditScratch.lean`. Claims about papers were checked against the local
primary PDFs. A focused import that is currently blocked by the repository's
signed-carrier migration is reported as `STALE` or `UNVERIFIED`, not silently
treated as proved. This report does not edit or trust the skill itself.

## Verdicts

| Verdict | Meaning |
| --- | --- |
| `VERIFIED` | The claim follows from a current declaration or the cited primary source. |
| `OVERSTATED` | A materially narrower claim is supported. |
| `FALSE` | The current declaration or primary source contradicts the claim. |
| `STALE` | The claim described an older surface or cannot currently be reproduced in this checkout. |
| `UNVERIFIED` | Adequate primary evidence was not found. |
| `NORMATIVE` | Advice or a preference rather than a checkable theorem/status claim. |

## Executive findings

The reference set is not safe to use unchanged. The principal defects are:

1. It mixes distinct proof objects. Conditional equivalence, H-technique bad
   sets, winnability, raw distribution couplings, system-level representative
   attainment, and representative-augmented transcript laws are not
   interchangeable notions.
2. `optimal_probability_coupling_exists` is a maximal coupling of two *raw
   normalized PDS laws* and attains their static `δ`; it does not by itself say
   that disagreement equals system advantage. The latter requires the much
   stronger finite/common-domain/bounded representative theorem.
3. The displayed winnability formula `Δ ≤ ν(S^A)` is not Theorem 2.37. The
   theorem is `ν(S^A) = ω(S^A)` plus attainment by an equivalent
   representative. It neither asks for an MBO nor identifies CE with
   winnability.
4. Query compression is described far beyond its formal scope.
   `compressedQuery_bound` is only a numerical monotonicity lemma; the exact
   compression equality applies to function-evaluator laws, and the tactic is
   SoP-specific.
5. Both displayed `probBad_iUnion_le` skeletons fail against the current
   signature because they omit the distribution nonnegativity proof and pass
   `D` in its place.
6. The CBC structure-graph headline depends on `sorryAx`; the source itself
   says the advertised second-term constant is not reached by the unfinished
   descriptor-pair union bound.
7. The amplification theorem is admitted and is not Lanzenberger--Maurer
   Theorem 3 as printed. The paper's theorem uses the `ξ` correction
   coefficients, not `choose n (k-1) * eps^k`.
8. The metric comparison is conditional on normalized laws, and the cited
   filter theorem is narrower than the generic shared-domain equality. The
   claimed “CR18 deletion rewind” explanation is obsolete and contradicted by
   the current source notes.

## A. `h-technique.md`

| ID | Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement |
| --- | --- | --- | --- | --- | --- |
| H-001 | 14 | In an ordinary H-technique proof, the exceptional object is a predicate on transcripts. | `VERIFIED` | `adv_le_of_fixedQuery_{eq_on_good,ratio_of_good,expectation,partition}` quantify `Bad`/`cell` over `TranscriptPrefix`; see `RandomSystems/HTechnique/Derivation.lean:398-760`. | “The ordinary fixed-query H endpoints use a bad predicate or defect function on transcript prefixes.” |
| H-002 | 14 | H-technique is the library's “most-used family.” | `UNVERIFIED` | No usage census, stable metric, or primary source is supplied. A declaration-count grep does not establish “most used.” | Delete the popularity claim. |
| H-003 | 14-15 | H-technique is the only family with a complete labelled-spine surface “today.” | `FALSE` | No labelled-spine commands are present in `random-systems`. They occur in the sibling `ccprover/CCProver/RS/Prover/GoalProtocol.lean` and `CCProver/Surface/Techniques.lean`. Lines 97-101 later acknowledge this. | “A labelled H spine exists in the sibling `ccprover` project, not in this repository.” |
| H-004 | 17-29 | Five analyses are all implementations/specializations of one general `hTechnique_partition` statement. | `OVERSTATED` | Mathematically, partition can encode the other defect shapes, and `hTechnique_ratio_via_partition` does so for good/bad. But the implementation proves `hTechnique_partition` *from* `hTechnique_expectation` (`Derivation.lean:664`) and several adaptive endpoints are separate lifts. | “The five analyses express related defect decompositions. Partition subsumes them mathematically; the Lean dependency graph is not a single-root API.” |
| H-005 | 21-27 | The displayed implication directions accurately describe the current dependency graph. | `FALSE` | The diagram puts partition above expectation, while `hTechnique_partition` explicitly invokes `hTechnique_expectation`; `adv_le_of_fixedQuery_ratio` invokes `adv_le_of_fixedQuery_ratio_of_good`. | Relabel the diagram “mathematical specialization map,” or reverse the implementation arrows. |
| H-006 | 31 | There are fifteen declarations named `adv_le_of_*` on the cited H surface. | `VERIFIED` | Current source has thirteen in `HTechnique/Derivation.lean` (lines 398, 439, 488, 540, 732, 797, 836, 1076, 1270, 1308, 2073, 2305, 2334) and two in `HTechnique/IdealCompression.lean:420,463`. | Retain, but call it a snapshot count. |
| H-007 | 31-39 | The fifteen declarations are the Cartesian product of the four transcript models, five analyses, and three filters. | `FALSE` | A full product would have 60 declarations. The existing set is sparse and not generated by orthogonal composition; several combinations do not exist. | “The names use three descriptive axes, but only a sparse set of combinations is implemented.” |
| H-008 | 36-38 | The listed transcript-model/analysis/filter vocabulary matches current declaration names. | `OVERSTATED` | The vocabulary is useful, but `ratio_of_good` versus table label `ratio`, `extFixedQueryRep`, and filtered suffixes are not a uniform grammar implemented by the library. | Present it as a naming mnemonic, not a grammar theorem. |
| H-009 | 41-43 | `extended` is orthogonal to analysis and composes with all five analyses. | `FALSE` | The current extended endpoints are equality-on-good and ratio-on-good, plus a filtered ratio endpoint. There is no extended expectation, partition, or perfect-ratio endpoint. | “Extended transcripts are a model variation currently supported by selected equality/ratio endpoints.” |
| H-010 | 45-47 | `selectHTechnique` and `#h_grammar` are available here. | `FALSE` | Neither declaration occurs in this repository. They occur only in sibling `ccprover/CCProver/Surface/Techniques.lean:209,253`. | Explicitly qualify both commands as sibling-`ccprover` tools. |
| H-011 | 46 | The sibling selector currently reports 15 of 60 combinations. | `VERIFIED` | `ccprover/CCProver/Surface/Techniques.lean` contains the 60-cell selector matrix with 15 named entries. | Retain only with the sibling-project qualification. |
| H-012 | 48-49 | The fifteen endpoints live in `RandomSystems.CR18.HTechniqueDerivation.adv_le_of_*`, except two in `RandomSystems.HTechnique.IdealCompression`. | `VERIFIED` | Current declaration inventory matches this split. | Retain. |
| H-013 | 53 | `ccprover/CCProver/RS/Teaching/OrdinaryH.lean:8-14` is “the library's own” selection rule. | `STALE` | It is not part of this repository, and the path is relative to a sibling checkout. It can be prior-art guidance, not current-library authority. | “The sibling `ccprover` teaching file recommends the following heuristic.” |
| H-014 | 55-64 | The analysis-selection table and “take the most special variant” are theorem facts. | `NORMATIVE` | These are proof-engineering heuristics. “Fewest obligations” holds for the shown common cases but is not a formal ordering over every endpoint. | Keep as advice and remove categorical wording. |
| H-015 | 71-80 | The listed creative nodes are exactly the generated obligations for each analysis. | `OVERSTATED` | The theorem signatures support the broad categories, but Lean does not generate these labels, endpoint hypotheses vary, and the “representative” row is an H extended-fixed-query RV endpoint, not a universal representative technique. | Call these recommended plan labels and give the exact theorem signature beside each. |
| H-016 | 83-90 | The displayed `adv_le_of_fixedQuery_eq_on_good` skeleton matches the current endpoint's argument order. | `VERIFIED` | `#check` confirms arguments `S T Bad δb hS hT h_eq h_bad` and the universally quantified ideal bad-mass premise. | Retain, subject to H-017. |
| H-017 | 87 | `htechnique_total` can be assumed to close both arbitrary totality goals in that generic skeleton. | `OVERSTATED` | The macro in `HTechnique/Tactics.lean:79-89` tries `cr18_total` and a fixed list of SoP/strong/tweakable constructors. It is not a completeness procedure for arbitrary `S,T`. | Write `(by htechnique_total)` only when the systems are among registered constructors; otherwise supply named totality lemmas. |
| H-018 | 93-95 | Compiling the skeleton and checking the residual goal count by eye is a sound workflow. | `NORMATIVE` | This is process advice, not a theorem. It does not guarantee semantic completeness. | Retain as a review step, not a correctness guarantee. |
| H-019 | 97-101 | Labelled spines and typed examples exist in sibling `ccprover`, which depends on this repository rather than conversely. | `VERIFIED` | `CCProver/RS/Prover/GoalProtocol.lean` and `CCProver/Surface/Techniques.lean` contain the spines; imports point from `ccprover` to `RandomSystems`. | Retain. |
| H-020 | 105-108 | `cr18_total`/`htechnique_total` and inferred finite/discrete transcript instances routinely discharge the listed side conditions. | `OVERSTATED` | The abbreviations and tactics exist, but tactic coverage is constructor-specific and typeclass inference requires the underlying finite/decidable instances. | State the required hypotheses and say the tactics *attempt* registered cases. |
| H-021 | 109 | Extended endpoint weight obligations are discharged by `cr18_prob` “and friends.” | `OVERSTATED` | `adv_le_of_extended_ratio_of_good` requires nonnegativity, two projections, equal weights, and ideal weight at most one. `cr18_prob` is a simplification bundle, not a general solver. | List the exact hypotheses and cite named probability lemmas for the chosen extensions. |
| H-022 | 110 | `htechnique_compress` is underwritten by `compressedQuery_bound`. | `FALSE` | `compressedQuery_bound` (`QueryCompression.lean:116`) only transports `q^3 <= N^2` to the compressed cardinality. Exact law compression is `transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress` (`:150`), and `htechnique_compress` itself rewrites only two SoP transcript laws. | Cite the exact law-compression theorem, and state its function-evaluator scope. |
| H-023 | 111 | `htechnique_adv_le` reduces the listed security shells to pointwise goals. | `VERIFIED` | Macro body at `HTechnique/Tactics.lean:62-75` tries the four `SecurityDefs` shells and `cr18_adv_le`. | “The tactic attempts these registered shell reductions.” |
| H-024 | 113-115 | An arbitrary query vector may always be replaced by its injective distinct-entry vector before counting. | `FALSE` | This is exact for sampled function evaluators through `QueryCompression.lean:150`, not for an arbitrary history-dependent system. Repeats can affect a general stateful system. | Restrict compression to systems with a proved repeated-query consistency/compression theorem. |
| H-025 | 117-118 | `htechnique_compress` is `simp only` over a fixed rewrite set and can do nothing off shape. | `VERIFIED` | The macro body at `HTechnique/Tactics.lean:45-51` contains exactly two SoP compression laws plus simplification identities. | Retain, and name the SoP scope explicitly. |
| H-026 | 119-123 | A CBC-MAC H leaf was measured at about 60 lines, principally due to manual compression and impossible transcripts. | `UNVERIFIED` | No commit, theorem range, measurement protocol, or source annotation identifies this experiment. | Delete, or cite an exact file/commit/line range and define how lines were counted. |
| H-027 | 125-126 | Re-indexing is always the caller's responsibility when the ideal is indexed by distinct queries. | `OVERSTATED` | It is caller work only when no existing exact compression bridge matches the model. | “If no registered compression theorem matches the model, provide the re-indexing proof explicitly.” |
| H-028 | 130-135 | The fixed-query ratio orientation is `(1-eps) * ideal <= real`. | `VERIFIED` | Confirmed by `adv_le_of_fixedQuery_ratio_of_good` and `probBad_le_of_ratio`. | Retain. |
| H-029 | 137 | Reversing the ratio “costs an hour.” | `NORMATIVE` | Rhetorical workflow warning, not an auditable fact. | Delete the time estimate. |
| H-030 | 139-146 | The H bad-probability obligation is universally quantified over exact-query environments. | `VERIFIED` | `#check adv_le_of_fixedQuery_eq_on_good` confirms `forall E : QQueryEnvironment ...`. | Retain. |
| H-031 | 146 | A bound for only one schedule cannot discharge the universal H premise. | `VERIFIED` | Immediate from the signature. A theorem uniform in the schedule can of course be introduced and applied to arbitrary `E`. | Clarify “one fixed, externally chosen schedule.” |
| H-032 | 148-150 | The extended endpoint has two projection hypotheses from extensions to visible transcript laws. | `VERIFIED` | `#check adv_le_of_extended_ratio_of_good` shows `h_projS` and `h_projT`. Whether they are “routine” is advice. | Keep the signature fact; label difficulty assessment as heuristic. |
| H-033 | 152-153 | Every ideal bad-probability goal should be closed by `probBad_iUnion_le`. | `NORMATIVE` | Union bounds are one route and can be loose or inapplicable; exact counting, martingales, or structural lemmas may be preferable. | “Consider the union bound when `Bad` has a useful finite cover.” |
| H-034 | 157-164 | The named exemplar files/directories exist. | `VERIFIED` | All six paths exist in the current tree. | Retain. |
| H-035 | 159-164 | The short descriptions exactly characterize each exemplar. | `OVERSTATED` | HashThenPRF uses equality-on-good, TweakablePRP contains ratio arguments, StrongPRP supplies totality specializations, and HCTR2Paper has a GF128 endpoint. `IdealCompression` contains only two filtered equality endpoints beyond imports, and “heaviest counting” is subjective. | Use declaration names rather than superlatives; say the files *include* the stated patterns. |

## B. `counting.md`

| ID | Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement |
| --- | --- | --- | --- | --- | --- |
| C-001 | 16-19 | Every family-III proof ends in counting, with a goal always of the displayed probability/mass form. | `FALSE` | A coupling proof may end in a disagreement estimate, an H ratio proof can be purely pointwise, and a winnability proof need not expose `probBad`. | “Many bad-event proofs eventually require a mass bound of one of these forms.” |
| C-002 | 25 | `probBad_iUnion_le` is at `StatDist.lean:294` and has the table's shape. | `STALE` | It is currently at `StatDist.lean:467`. Its signature also requires `hD : D.NonNeg` before `B` and `P`. | Update the line and print the complete signature. |
| C-003 | 26 | `mass_biUnion_le` is at `SwitchingLemma.lean:55` and is a finite mass union bound. | `VERIFIED` | Current declaration is `RandomSystems.CR18.mass_biUnion_le X hX s E`; it additionally requires `[Nonempty A]` and `X.NonNeg`. | Retain with namespace and hypotheses. |
| C-004 | 27 | `probBad_le_of_ratio` is at `Derivation.lean:3499` with the stated conceptual shape. | `STALE` | It is currently at line 3849. `#check` also shows both nonnegativity and both weight-equals-one hypotheses. | Update location and include all premises. |
| C-005 | 28 | `CBCStructureGraph.lean` currently proves the Jha--Nandi `O(q^2 L / 2^n)` headline. | `FALSE` | `mass_cbcGraphBad_le` ends in `sorry` at line 1428; `#print axioms cbc_mac_beyond_birthday` contains `sorryAx`. The source comment says the stated second-term constant is not reachable by the current descriptor union bound. | “The file contains a proved CE bridge and partial graph-counting lemmas; the final counting/headline theorem remains admitted.” |
| C-006 | 29 | The SoP directories implement orbit/partition or compatible-count analyses. | `VERIFIED` | Current `RandomSystems/SoP/` and `HTechnique/SoP/` contain the named machinery and mathematical notes. | Retain. |
| C-007 | 30 | SwitchingLemma and the URF evaluator provide standard collision/birthday machinery. | `VERIFIED` | `pairCollisionUnionBound_le_birthday` is at `SwitchingLemma.lean:1705`; URF evaluator instances are present. | Retain with exact declaration names. |
| C-008 | 32 | Nearly every library proof ends through the union bound. | `UNVERIFIED` | No census is supplied, and several major routes are exact counting, ratio, or coupling arguments. | Delete the frequency claim. |
| C-009 | 36-52 | Splitting a finite bad event into a logical cover and leaf-mass sum is a valid and often useful proof plan. | `VERIFIED` | This is exactly what `probBad_iUnion_le` proves once nonnegativity and decidability hypotheses hold. Claims about where “real thinking” belongs are normative. | Retain as a conditional plan. |
| C-010 | 40 | The first displayed union-bound application elaborates. | `FALSE` | Current signature is `probBad_iUnion_le hD B P hB`; the skeleton passes `D` where `hD : D.NonNeg` is expected and omits nonnegativity. | `refine le_trans (RandomSystems.probBad_iUnion_le hD Bad P ?cover) ?sum`. |
| C-011 | 49-52 | A good descriptor family has individually tractable event masses, often uniform closed forms. | `NORMATIVE` | This is design advice, not a universal property. | Retain as a heuristic without “the creative act” exclusivity. |
| C-012 | 57-65 | The statement-first skeleton elaborates modulo the two holes. | `FALSE` | It repeats the same missing-`hD` argument error as C-010. | Add `hD : D.NonNeg` and call `probBad_iUnion_le hD Bad ...`. |
| C-013 | 67-68 | Failure of the skeleton usually means only missing `Fintype` or decidability. | `OVERSTATED` | It can also be a namespace, carrier, nonnegativity, coercion, or event-cover shape mismatch. | List these as common possibilities, not an exhaustive diagnosis. |
| C-014 | 72-74 | The packaged conditional-equivalence endpoint hands the leaf a fixed blind list `blindQueryList w q`. | `VERIFIED` | CR18 Theorem 4.17 (local `CR18_LN.pdf`, printed pp. 109-110) reduces to the blind game; the Lean wrapper's leaf is quantified over `w` with `blindQueryList w q`. | Retain with the exact wrapper name and hypotheses. |
| C-015 | 76-78 | The H bad bound is universal over adaptive query environments. | `VERIFIED` | Confirmed by current H endpoint signatures. | Retain. |
| C-016 | 78 | After `htechnique_compress`, every H transcript law is at a fixed injective query vector. | `FALSE` | The tactic is SoP-specific and exact compression is proved only for function-evaluator-style laws. Moreover the H theorem still quantifies over an adaptive `E`; fixed-query factorization is used inside its proof, not as a generic schedule replacement. | Separate the universal adaptive premise from any model-specific fixed-query counting lemma. |
| C-017 | 80-82 | Every CE or H counting problem is over a fixed schedule, so any adaptive next-query argument skipped a reduction. | `FALSE` | The CE blind leaf is fixed-schedule. The H `h_bad` premise remains adaptive and often must exploit a history-dependent invariant uniformly. | Restrict this warning to the CE blind leaf and explicitly proved fixed-schedule reductions. |
| C-018 | 84-88 | The listed normalizations carry no mathematical content in general. | `OVERSTATED` | Exact normalization itself can require a substantive model theorem; arbitrary repeated queries cannot be erased for a stateful system. | “After an exact model-specific normalization theorem is proved, subsequent rewriting is bookkeeping.” |
| C-019 | 92 | `compressedQuery_bound` replaces arbitrary query vectors by distinct-entry vectors. | `FALSE` | The theorem only proves a numerical cubic side condition after compression. See `QueryCompression.lean:116`; exact evaluator-law compression is at line 150. | Replace the theorem name and state the evaluator scope. |
| C-020 | 93-96 | `cr18_filter`, mass/sum/ite, cardinality, arithmetic, and algebra tactics exist at the cited core locations. | `VERIFIED` | Current `CR18TacticsCore.lean` contains the named tactics; minor line numbers should be treated as volatile. | Retain names, omit fragile line numbers. |
| C-021 | 98-99 | `cr18_close` runs `grind`, arithmetic, then normalization/grind. | `VERIFIED` | Macro body uses a `first` chain over the stated classes of finishers. It attempts them; it is not complete. | “Try `cr18_close`; inspect the remaining goal if none of its registered finishers closes it.” |
| C-022 | 103-108 | `pairCollisionUnionBound_le_birthday` gives the displayed half-square bound. | `VERIFIED` | `SwitchingLemma.lean:1705` states exactly `pairCollisionUnionBound X r <= (1/2) r^2 / card X`. | Retain. |
| C-023 | 112 | `CBCStructureGraph.lean` has 1400+ lines. | `VERIFIED` | Current file has 1463 lines. | Retain only if file size is useful; otherwise omit. |
| C-024 | 112-116 | The structure-graph file contains a proven tolerant-CE bridge and a full counting engine with the stated headline. | `FALSE` | The CE bridge and several leaf lemmas are complete, but `mass_cbcGraphBad_le` is admitted and propagates `sorryAx` to the headline. | State the completed bridge and partial leaves separately from the open corrected-Lemma-10/counting obligation. |
| C-025 | 115-116 | The Jha--Nandi route is what changes a naive `(qL)^2/2^n` term to order `q^2 L/2^n`. | `VERIFIED` | Jha--Nandi, IACR ePrint 2016/161, presents the structure-graph analysis and the linear-in-message-length improvement while correcting BPR's invalid lemma. This does not verify the unfinished Lean theorem. | Retain as a paper result, not a formalization-status claim. |
| C-026 | 118-120 | The listed SoP notes exist and contain written mathematics. | `VERIFIED` | `SoP.md`, `SoP1.md`, and `SoP2.md` exist in the current tree. | Retain. |
| C-027 | 122 | ANOVA/Mayer files are at `Legacy/Applications/XoP*.lean`. | `STALE` | The actual path is `RandomSystems/Legacy/Applications/XoP*.lean`. | Include the `RandomSystems/` prefix. |
| C-028 | 122-123 | ANOVA/Mayer is rarely the right first move. | `NORMATIVE` | Proof-strategy preference. | Keep only as an explicit heuristic. |
| C-029 | 127-129 | Users should never re-prove a union bound. | `NORMATIVE` | Reuse is normally preferable, but a different carrier or sharper inequality can justify a new lemma. | “Reuse these finite union bounds when their hypotheses and constant fit.” |
| C-030 | 131 | Query vectors with repeats should always be compressed first. | `FALSE` | Generic compression is unsound for history-dependent systems. | Add the exact-compression precondition. |
| C-031 | 133-135 | A universal H premise needs a bound uniform in `E`. | `VERIFIED` | Direct from the endpoint signature. | Retain. |
| C-032 | 137-138 | A slack cover can only cost the numerical bound, never the proof. | `OVERSTATED` | A cover may also make the desired theorem unprovable at the target constant or fail to align with available leaf lemmas. | “If the union sum is too large, refine the descriptor family or change the counting method.” |
| C-033 | 140-141 | Existing cast/arithmetic tactics know all relevant idioms. | `NORMATIVE` | They cover many recurring forms but provide no completeness guarantee. | “Try the existing arithmetic tactics before writing new cast lemmas.” |

## C. `reshape-and-exact.md`

| ID | Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement |
| --- | --- | --- | --- | --- | --- |
| R-001 | 16-17 | The file exhausts families I, II, IV, V and the remaining family-III techniques. | `OVERSTATED` | This is a local taxonomy, not an exhaustive theorem classification. The entries themselves omit hypotheses and include legacy/incomplete surfaces. | Call it a routing overview, not an exhaustive partition. |
| R-002 | 19-22 | Exact equivalence (`distance = 0`) is stronger than a positive upper bound. | `VERIFIED` | Elementary order fact, assuming both statements concern the same metric/domain. | Retain. |
| R-003 | 26 | Behavioural quotient/equivalence infrastructure exists at the named paths. | `VERIFIED` | `RandomSystemQuotient.lean` and legacy `Equiv` exist. The legacy module is presently migration-sensitive. | Qualify the layer. |
| R-004 | 27 | Strict relabelling by bijections preserves the metric. | `VERIFIED` | `RandomSystems/StrictRelabel.lean` contains the relabelling invariance theorem. | Retain with exact theorem name. |
| R-005 | 28 | `compressedQuery_bound` is an exact Family-I query-compression theorem. | `FALSE` | It only preserves the numerical hypothesis `q^3 <= N^2` after shrinking the query set. It proves no system equivalence. | Replace it with the relevant exact evaluator-law compression theorem, under its hypotheses. |
| R-006 | 29,32-33 | Lemma 2.18 removes the entire adaptive apparatus whenever a new proof satisfies a special hypothesis. | `OVERSTATED` | Thesis Lemma 2.18 (`thesis (1).pdf`, printed p.16) and `LanzenbergerChain.lean:180` characterize *exact transcript equivalence*: equality under all nonadaptive deterministic environments iff full equivalence. They do not reduce arbitrary nonzero advantage bounds to nonadaptive adversaries. | “For an exact-equivalence goal, it suffices to prove equality for every nonadaptive deterministic environment.” |
| R-007 | 30 | `delta_eq_advantage` is LM20 Theorem 1 and permits moving between `Delta` and `Adv` without qualification. | `OVERSTATED` | The legacy theorem at `Legacy/FundamentalTheorem.lean:216` is a finite fixed-`q` result. The modern source-bounded theorem requires nonnegativity, finite input, common domain, and a uniform bound (`LanzenbergerChain.lean:205ff`). | State the exact model and hypotheses for the chosen theorem. |
| R-008 | 32-33 | Nonadaptive sufficiency should be checked on every proof. | `NORMATIVE` | Workflow preference; it applies only to exact-equivalence obligations in the cited theorem. | Restrict the advice accordingly. |
| R-009 | 35-39 | Hybrid reshaping is “pure algebra” and the most commonly omitted step. | `UNVERIFIED` | The triangle step is algebraic, but selecting and modeling a hybrid can be substantive. No omission census supports “most often.” | “Check whether a useful intermediate system exposes reusable bounds.” |
| R-010 | 43 | `maxAdvantage_triangle` has no side conditions. | `VERIFIED` | Current signature at `AbsorbDPI.lean:1030` is `(S T U) : Delta(S,U) <= ...`. | Retain. |
| R-011 | 44 | `maxAdvantage_apply_le` requires only a converter and `Emulable`. | `OVERSTATED` | `#check` shows additional `S.NonNeg` and `T.NonNeg` hypotheses. | Include both nonnegativity hypotheses. |
| R-012 | 45 | Parallel composition requires four `isProbDist` proofs and no additional creative object. | `VERIFIED` | `#check maxAdvantage_par_le` confirms four normalized-law premises. “Nothing” should mean no extra construction beyond the four proofs. | Retain with that wording. |
| R-013 | 46 | Query restriction requires only two `TotalOnNonempty` proofs. | `OVERSTATED` | The theorem also takes `dummy : X`, `q`, and the two systems. More importantly it is an inequality, not exact normalization. | Print the full signature, including the dummy value. |
| R-014 | 47 | Branch distance is additive over disjoint answer cells without normalization. | `VERIFIED` | `TranscriptBranchDistance.lean:35` proves the equality and does not assume unit weights. It does require nonnegativity of every right branch. | Retain and add `forall y in ys, (Tf y).NonNeg`. |
| R-015 | 48 | `maxAdvantage_le_of_forall_advantage_le` fixes a probability distinguisher and reduces a supremum bound pointwise. | `VERIFIED` | Current signature at `Distinguishing.lean:164`. | Retain; “doorway” is metaphorical. |
| R-016 | 50-59 | The CBC headline route at the cited lines is triangle + converter/DPI + switching. | `VERIFIED` | Current `CBCMAC.lean` contains that route, but at shifted lines around 1070-1110 rather than the frozen citation. | Update line numbers or omit them. |
| R-017 | 50-52 | The CBC theorem contains “no new mathematics at all.” | `NORMATIVE` | It reuses existing lemmas, but the model/converter and budget accounting are still mathematical choices. | “The endpoint is assembled from previously proved bounds.” |
| R-018 | 63-70 | `coupling_bound` and `DistCoupling` have the displayed distribution-level meaning. | `VERIFIED` | Current locations are `Coupling.lean:45` and `:149`, not `:41` and `:136`. A `DistCoupling` includes joint nonnegativity and two marginals; normalization is not a field. | Update locations and include nonnegativity. |
| R-019 | 74-75 | `system_coupling_exists` says a system coupling always exists. | `OVERSTATED` | Legacy theorem requires finite fixed-`q` types, equal weights, and `Nonempty (Fin q -> X)`. It is not an unrestricted theorem over the modern carrier. | “Under the legacy finite fixed-query hypotheses and equal weights, a system coupling exists.” |
| R-020 | 76-78 | `optimal_probability_coupling_exists` gives a coupling whose disagreement equals system-level `Delta`/optimal distinguishing advantage. | `FALSE` | `#check` shows disagreement equals raw static `delta S.val T.val` for the two supplied normalized PDS laws. It does not select equivalent representatives. | “This theorem is the maximal-coupling lemma for raw normalized laws.” |
| R-021 | 76-78 | Coupling has no inherent slack for random-system advantage without further hypotheses. | `OVERSTATED` | The system-level tight theorem is `exists_equivalent_representatives_with_probability_coupling_disagreement_eq_optimal_advantage_of_finite_common_domain_and_bounded`, requiring `[Fintype X]` and a common-domain/query-bound witness. Lanzenberger--Maurer Theorem 2 is stated under its finite random-system setting (`LanMau20.pdf`, p.15). | Cite the system-level theorem and all of its hypotheses. |
| R-022 | 80-84 | A hand-built coupling may be looser than the optimal coupling. | `VERIFIED` | `coupling_bound` is an inequality, while maximal-coupling existence is existential. | Retain. |
| R-023 | 87-92 | `SoP2.lean` contains an exact compatible-count L1 theorem and a sequential `2q^3/(3N^2)` coupling theorem. | `OVERSTATED` | The source contains both, but the exact formula uses `m = min(q,N)`, and the sequential theorem has the side condition `q^3 <= N^2` and first proves the sharper finite polynomial. A focused import is currently blocked by the legacy XoP signed migration, so current kernel reproducibility is `STALE`. | State formulas and hypotheses exactly; label the current build status. |
| R-024 | 91 | The exact SoP theorem is `Adv = 1/2 sum_y |C_G(y)/(N)_m^2 - 1/N^m|`. | `VERIFIED` | `SoP/SoP2.lean:5048` and `SoP2.md` Theorem 6 give this form with `m=min(q,N)`. | Add the definition of `m` and carrier assumptions. |
| R-025 | 92 | The online corollary is unconditionally `Adv <= 2q^3/(3N^2)`. | `FALSE` | The final corollary is under `q^3 <= N^2`; the preceding bound is `q(q-1)(2q-1)/(3N^2)`. | Include the side condition and sharper predecessor. |
| R-026 | 94-103 | The quoted SoP note distinguishes global maximal and sequential couplings, and the conceptual loss split is sound. | `VERIFIED` | `SoP2.md` makes this distinction. The general lesson is explanatory, not a theorem that every construction admits the same analysis. | Retain as interpretation. |
| R-027 | 108-114 | A direct distribution coupling proof needs a joint, marginal proofs, and disagreement bound; no labelled spine is in this repository. | `VERIFIED` | `DistCoupling` and `coupling_bound` give these obligations; no local coupling spine was found. | Retain, while noting normalized-joint obligations if a probability coupling is required. |
| R-028 | 111 | Shared randomness is the criterion for choosing coupling. | `NORMATIVE` | Shared randomness is a useful construction heuristic, not a necessary-and-sufficient applicability theorem. | “Coupling is especially natural when useful shared randomness can be exposed.” |
| R-029 | 118 | Winnability gives `Delta <= nu(S^A)`. | `FALSE` | Thesis Theorem 2.37 (`thesis (1).pdf`, printed p.24) and `LanzenbergerChain.lean:283` state `supWinProb = infWinnability` plus attainment. No generic pairwise-distance inequality of the displayed form is the theorem. | Replace with the exact equality/attainment statement. |
| R-030 | 118-120 | `theorem_2_37_winnability_theorem` and the bounded workhorse formalize the thesis theorem. | `STALE` | Their source statements match the thesis and contain completed terms, but `lake build RandomSystems.GameWinnability` currently fails in the signed-distribution migration. They are not currently a reproducible library endpoint in this audited checkout. | State “source implementation present; focused module currently fails to build” until repaired and audited. |
| R-031 | 122 | The creative input to the winnability theorem is an MBO. | `FALSE` | The theorem takes a random game `G`, fixed-domain and boundedness hypotheses. It neither defines nor requires a monotone bit output. | “Creative work is designing or reducing to a random game whose `supWinProb` is the desired quantity.” |
| R-032 | 124-126 | Conditional equivalence is a winnability argument constructed by `gameOf`. | `FALSE` | CE is a one-sided conditional-law identity plus a blind-winning bound. The winnability theorem is representative attainment for a random game. `gameOf` can encode CE data, but this does not identify the two theorems or their proof obligations. | Keep CE and winnability as separate methods; state an explicit reduction if one is used. |
| R-033 | 125-126 | CE should be preferred unless the game is already given. | `NORMATIVE` | Strategy preference, not a theorem. | Keep only as project-local advice. |
| R-034 | 128-137 | The legacy condition-based theorem, types, and locations are as stated. | `VERIFIED` | `TranscriptCondition` is at line 60, `maxConditionFailure` at 88, and `statDist_le_conditionFailure_single` at 241 in `Legacy/ConditionBased.lean`. It uses finite `Fin q` transcript structures. | Retain. |
| R-035 | 128 | The condition-based method is attributable to Maurer, EUROCRYPT 2002. | `VERIFIED` | `papers/Maurer02.pdf` is the primary source for the condition-based random-system technique. | Retain with full citation. |
| R-036 | 133-140 | A legacy condition-based proof must account for its model boundary before composing with modern PFun results. | `VERIFIED` | The declarations inhabit different structures/namespaces; bridge modules exist. | Retain, but do not claim CE is mathematically identical. |
| R-037 | 139-140 | CE should be the default replacement for condition-based reasoning. | `NORMATIVE` | Project workflow preference. | Keep as advice only after comparing exact hypotheses and constants. |
| R-038 | 146 | `CausalApply.winProb_apply` proves the converter reduction equality. | `STALE` | The source theorem at `ReductionByConverter.lean:80` has the displayed equality, but its focused module currently fails to build under the signed migration. | State source status and re-check after migration. |
| R-039 | 147 | `ReductionByInstantiation.lean` implements the multiple-instantiation reduction technique. | `OVERSTATED` | It currently defines only `sigmaPow q W := Dist.iidPow W q` plus a reflexive lemma. It does not package a solver-reduction theorem. | “The file defines CR18's `sigma^q` map; application-specific reduction theorems remain to be supplied.” |
| R-040 | 148 | Complexity game-hop/game-sequence infrastructure exists. | `VERIFIED` | `RandomSystems/Complexity/`, `GameHop`, and `GameSeq` modules exist. | Retain with exact import paths. |
| R-041 | 154 | `Legacy.CC.Composition` is the full CC composition theorem “reason modular proofs work.” | `OVERSTATED` | `Legacy/CC/Composition.lean` explicitly implements a simpler single-interface construction and says the full simulator-bearing framework is not modeled there. | “A simplified single-interface serial composition theorem is implemented in the legacy layer.” |
| R-042 | 155 | `amplification_theorem` is LM20 Theorem 3 and is proved/citable. | `FALSE` | `Legacy/Amplification.lean:119` contains `sorry`. Its claimed bound `choose n (k-1) * eps^k` is not Lanzenberger--Maurer Theorem 3; the paper uses a sum of `xi` correction coefficients and Bernoulli event terms (`LanMau20.pdf`, p.22). | Delete the attribution and do not cite the admitted theorem. |
| R-043 | 156 | `threshold_combiner_bound_1_2` is LM20 Definitions 14-15 and proved/citable. | `STALE` | Its source proof closes and yields `2*eps`, but the enclosing legacy import chain currently fails. It is not LM20 Theorem 3, and the module header's `2eps^2` summary contradicts the declaration. | Cite the exact local theorem only after the legacy module builds and its paper attribution is checked. |
| R-044 | 157 | The named absorption/blinding modules exist. | `VERIFIED` | `AbsorbDPI.lean`, `BlindAbsorption.lean`, and `BlindConverter.lean` are present. | Retain. |
| R-045 | 159-163 | All four named legacy theorems are proved and citable. | `FALSE` | `amplification_theorem` contains `sorry`; the focused legacy equivalence chain presently fails. Source presence is not current citable status. | Give per-theorem build/axiom status; do not make a blanket claim. |
| R-046 | 167 | `Delta` simply “is the advantage.” | `OVERSTATED` | In the modern CR18 namespace `Delta(S,T)` notation denotes `maxAdvantage`, while unparenthesized class-distance notation is also used elsewhere. The reference then invokes Lanzenberger class-distance results, so the unqualified sentence invites exactly the notion-mixing at issue. | Always write the declaration name: `maxAdvantage`, raw `delta`, or class distance `PFunPDS.Delta`. |
| R-047 | 169 | `maxEDist <= ofReal Delta` holds unconditionally. | `OVERSTATED` | `#check maxEDist_le_maxAdvantage` requires both systems to be `isProbDist`. “Unconditional” is only relative to domain restrictions. | “For normalized laws, the unrestricted-carrier strict metric is at most `ofReal maxAdvantage`.” |
| R-048 | 170-172 | Equality holds on shared-domain normalized laws. | `VERIFIED` | `maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain` at `StrictContextSharedDomain.lean:934` requires two probability proofs and a common fixed domain. | Cite this generic theorem and all hypotheses. |
| R-049 | 171-172 | `maxEDist_filterDom_eq_ofReal_maxAdvantage` is the generic shared-domain equality theorem. | `OVERSTATED` | It is a corollary only for same-predicate `filterDom` restrictions of two total laws. The generic theorem is the declaration at line 934. | Use the generic theorem for arbitrary shared-domain laws; use the filter corollary only for its exact shape. |
| R-050 | 174 | The CBC applications are at lines 1875 and 1891. | `STALE` | They are currently around `CBCMAC.lean:1887,1903`. | Omit volatile line numbers or update them. |
| R-051 | 176-179 | Headline results should always attach the equality receipt rather than accept an available inequality. | `NORMATIVE` | Sensible anti-slack policy when the equality hypotheses are proved; not every statement has those hypotheses. | Add “when the shared-domain and normalization premises are available.” |
| R-052 | 181 | The metric/advantage gap is a CR18 deletion rewind on the advantage side. | `FALSE` | Current `StrictContextSharedDomain.lean` explains the distinction through unrestricted versus public shared stall domains; `STATUS.md` explicitly withdraws the deletion-rewind interpretation. | Delete. Describe the two observation models and the shared-domain equality theorem. |
| R-053 | 182-183 | `AttainmentCounterexample.lean` proves max advantage `1/2`, class distance `1`, and no `maxEDist` statement. | `STALE` | The source is written to prove those first two claims and indeed contains no maxEDist theorem, but the focused module currently fails during signed-carrier migration. | “The source records this intended counterexample; it is not currently build-verified.” |

## D. `creative-search.md` outside lines 31--58

| ID | Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement |
| --- | --- | --- | --- | --- | --- |
| E-001 | 15-23 | The four listed situations are sufficient reasons to escalate to parallel exploration. | `NORMATIVE` | Resource-allocation guidance, not an empirical or mathematical theorem. | Keep as project policy if desired. |
| E-002 | 25-26 | Anthropic reported a 90.2% improvement of a multi-agent system over a single-agent baseline. | `VERIFIED` | Anthropic, “How we built our multi-agent research system” (13 June 2025), reports an Opus 4 lead with Sonnet 4 subagents outperforming single-agent Opus 4 by 90.2% on an internal research evaluation: <https://www.anthropic.com/engineering/multi-agent-research-system>. | Retain with the model, benchmark, date, and “internal evaluation” scope. |
| E-003 | 26-27 | The 90.2% gain specifically comes from breadth-first independent directions. | `OVERSTATED` | The article says multi-agent systems excel on breadth-first queries, but it also says token usage explains 80% of performance variance. It does not establish the skill's single causal explanation. | “Anthropic reports the approach is particularly suitable for breadth-first research; the same article identifies increased token use as a major performance correlate.” |
| E-004 | 28-29 | A single agent commits and rationalizes, whereas five agents' disagreement supplies the information. | `UNVERIFIED` | This is rhetoric not supported by the cited experiment, and no five-agent ablation is provided. | Delete or label as a brainstorming heuristic. |
| E-005 | 61-64 | Overlap is the main failure mode, and Anthropic documented the stated supply-chain duplication example. | `OVERSTATED` | The official article does document one subagent researching a 2021 topic while two duplicated current 2025 supply-chain work. One anecdote does not prove overlap is *the* main failure mode. | Retain the example and say “a documented failure mode.” |
| E-006 | 66-78 | The six proposed scouting angles are genuinely independent and the last two produce non-obvious answers. | `NORMATIVE` | These are useful briefing categories but can overlap, and no source establishes the productivity ranking. | Present them as candidate angles; require explicit non-overlap in each brief. |
| E-007 | 80-88 | Anthropic recommends briefs specifying objective, output format, tools/sources, and boundaries. | `VERIFIED` | The official article's delegation discussion gives these four fields. | Retain with the citation. |
| E-008 | 90-91 | Scouts should report honest negative results. | `NORMATIVE` | Sound research-management advice, not an empirical theorem from the cited article. | Retain as policy. |
| E-009 | 93-94 | Scouts must never write Lean. | `NORMATIVE` | Local workflow policy. Small formal probes can sometimes falsify an idea cheaply; the categorical ban is not externally justified. | “Stage-1 scouts normally return mathematics; use only minimal formal probes when they resolve a concrete ambiguity.” |
| E-010 | 98-99 | Agents are poor at sizing their own effort. | `OVERSTATED` | Anthropic reports that agents can struggle to judge appropriate effort, but this is a scoped engineering observation, not a universal capability claim. | “The cited system observed effort-sizing errors, so briefs should state an effort budget.” |
| E-011 | 101-106 | The table's exact fan-out counts are evidence-backed scaling rules. | `NORMATIVE` | Anthropic suggests roughly one agent for simple tasks, 2-4 for comparisons, and more than 10 for complex research. The skill's `5+` threshold is a local compromise, not the cited result. | Label the table project-local and avoid attributing its exact counts to Anthropic. |
| E-012 | 107 | Parallel rather than serial scouting is where the wall-clock saving occurs. | `OVERSTATED` | Parallel tool work plainly can reduce latency, and Anthropic reports large time reductions, but coordination, serial dependencies, and contention can erase the gain. | “Run independent scouts in parallel when concurrency and task independence permit.” |
| E-013 | 111-122 | The three synthesis criteria and runner-up record define the correct winner-selection procedure. | `NORMATIVE` | Research-process advice. “Best provable bound” and formalization cost can conflict with other goals such as sharpness, explanatory value, or theorem scope. | Keep as a checklist, not a total ordering. |
| E-014 | 124-126 | If all scouts obtain the incumbent bound, then either it is tight on the carrier or all scouts share a blind spot. | `OVERSTATED` | Other explanations include insufficient effort, a false shared assumption, an unsuitable decomposition of tasks, or a bound requiring unavailable literature/machinery. Agreement is evidence, not a dichotomy. | “Unanimous failure to improve is evidence to reassess tightness, shared assumptions, task design, and search coverage.” |

## Primary-source and Lean receipts

### Primary sources inspected

- `papers/CR18_LN.pdf`, printed pp. 109--111: conditional equivalence,
  Theorem 4.17, blindness, and the birthday lemma.
- `papers/thesis (1).pdf`, printed p. 16 (Lemma 2.18), p. 20
  (Theorems 2.31--2.32 context), and p. 24 (Theorem 2.37).
- `papers/LanMau20.pdf`, p. 10 (branch decomposition context), p. 15
  (Theorems 1--2), and p. 22 (Theorem 3 and its `xi` coefficients).
- `papers/Maurer02.pdf`, condition-based random-system proof method.
- Jha--Nandi, IACR ePrint 2016/161: <https://eprint.iacr.org/2016/161>.
- Anthropic, “How we built our multi-agent research system”:
  <https://www.anthropic.com/engineering/multi-agent-research-system>.

### Current-checkout receipts

The focused scratch import compiled on 2026-08-06 and established the current
signatures for:

- `probBad_iUnion_le`;
- `mass_biUnion_le`;
- `probBad_le_of_ratio`;
- the fixed-query and extended H endpoints;
- triangle-adjacent data processing, parallel composition, and query filter;
- branch additivity;
- raw and representative-level optimal coupling theorems;
- strict-context metric comparison/equality;
- `sigmaPow`;
- the CBC structure-graph headline.

`#print axioms` found no `sorryAx` in the checked union bound, H endpoint,
branch-additivity theorem, raw maximal coupling, system representative
coupling, or filter-domain metric equality. It did find `sorryAx` in
`cbc_mac_beyond_birthday`, inherited from `mass_cbcGraphBad_le`.

Focused builds of `Legacy.Applications.XoP`, `Legacy.Equiv`,
`ReductionByConverter`, `GameWinnability`, and `AttainmentCounterexample`
failed in this audited checkout during the in-progress signed-distribution
migration. These failures justify only the per-row `STALE` assessments above;
they are not claims that the underlying mathematics is false.

## Coverage receipt

| File | Covered factual/advisory ranges |
| --- | --- |
| `h-technique.md` | 14-15, 17-49, 51-64, 66-101, 103-126, 128-153, 155-164 |
| `counting.md` | 16-32, 34-52, 54-68, 70-82, 84-99, 101-123, 125-141 |
| `reshape-and-exact.md` | 16-33, 35-59, 61-114, 116-140, 142-163, 165-183 |
| `creative-search.md` | 15-29, 59-126; lines 31-58 deliberately excluded |

## Release recommendation

Do not release the audited references unchanged. At minimum, remove the
method-identification claims (`R-020`, `R-029`, `R-031`, `R-032`), repair the
two non-elaborating union-bound skeletons (`C-010`, `C-012`), restrict query
compression to proved evaluator-law shapes (`H-022`, `H-024`, `C-016`--`C-019`,
`R-005`), and mark the CBC and amplification headlines admitted/incomplete
(`C-005`, `C-024`, `R-042`). A rewrite should use declaration names
(`maxAdvantage`, raw `delta`, class distance, strict CE, winnability, and
representative attainment) instead of recycling `Delta`, “bad event,” or
“coupling” across incompatible notions.
