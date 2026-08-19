# Conditional-equivalence reference: direct-source cross-review

Date: 2026-08-06

## Scope and independence note

This report audits every factual claim in:

- `/Users/marcilunga/.codex/skills/random-systems-proofs/references/conditional-equivalence.md`;
- `/Users/marcilunga/.codex/skills/random-systems-proofs/references/creative-search.md`, lines 31--58.

Line numbers refer to the frozen skill text inspected on the date above. No
skill file was edited. I did not open `ce-audit-a.md` or any other verdict
report. However, before this reassignment my prior context had already
displayed `CE_CLAIM_INDEX.md`. The conclusions below were rederived directly
from primary PDFs and current Lean declarations, but this report should not be
represented as perfectly blind to claim partitioning.

Headings, contents lists, and separators carry no factual claim. Workflow
preferences are labeled `NORMATIVE`, not silently accepted as theorem facts.

## Verdicts

| Verdict | Meaning |
| --- | --- |
| `VERIFIED` | The claim follows from the primary source or current declaration. |
| `OVERSTATED` | A narrower statement is supported, but the written statement is not. |
| `FALSE` | The primary source or current declaration contradicts the claim. |
| `STALE` | The declaration exists but the cited location/surface is outdated. |
| `UNVERIFIED` | No adequate primary evidence was found. |
| `NORMATIVE` | Local advice or a preference rather than a checkable fact. |

## Executive result

The terminology boundary added to the reference is mostly correct and should
be preserved: strict one-sided CR18 conditional equivalence, MPR07's symmetric
restricted-equivalence construction, and Lanzenberger's representative and
coupling theorems are different results. In particular, choosing an equivalent
PDS representative is not a conditional-equivalence operation.

The reference is nevertheless unsafe unchanged in four places:

1. It treats condition refinement as automatically refining the bound. A
   smaller bad event changes the monitored game and can destroy conditional
   equivalence; there is no generic refinement theorem supplying the new CE
   identity or comparing the two blind winning probabilities.
2. It repeatedly describes blind winners as if adaptivity survives. By
   definition, `IsBlind` makes each query depend only on the round number, and
   `blindQueryList w q` is a fixed list. The raw theorem's `Gamma^b` is a
   supremum over nonadaptive blind winner distributions.
3. The packaged endpoint is accurately represented in substance, but its
   location is stale and the displayed signature omits `[Nonempty I]` and the
   decidability family for `bad`. Claims that it covers NMAC and “most keyed
   constructions” are not established by the current tree.
4. The CBC structure-graph route does not contain a complete counting engine:
   its final counting theorem is admitted. The ordinary CBC packaged-CE result,
   by contrast, is axiom-clean in the current focused check.

## A. `conditional-equivalence.md`

| ID | Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement |
| --- | --- | --- | --- | --- | --- |
| CE-B-001 | 15 | The characteristic “bad thing” in CE is a condition the distinguisher triggers. | `OVERSTATED` | CR18 models an internal monotone binary output that an interaction may provoke. The bit may depend on internal randomness and the query/answer history; “caused by the distinguisher” is useful intuition, not a definition. | “CE uses a monitored system carrying an internal monotone binary output whose value may be affected by the interaction.” |
| CE-B-002 | 15-17 | CE is for cases where transcripts are not enough, especially adaptive/stateful events rather than transcript properties. | `FALSE` | CR18 Examples 4.14--4.15 use input/output collision predicates, and current `gameOf S cond` takes `cond : List (X × Y) → Bool`, explicitly a transcript predicate. CE can also monitor seed/state events, but there is no transcript-versus-CE dichotomy. | “Use CE when a monotone monitored condition yields conditional equality and a tractable blind winning bound; the condition may itself be transcript-defined.” |
| CE-B-003 | 19 | Unconditionally, `Delta(S,T) <= Gamma^b(gameOf S cond)`. | `OVERSTATED` | CR18 Theorem 4.17 requires a monotone MBO and conditional equivalence. The Lean endpoint additionally exposes normalization, probability, and totality hypotheses; the filtered wrapper also needs a strip identity. | Display the implication with all standing assumptions, or label the formula schematic. |
| CE-B-004 | 25-26 | CR18 Definition 4.19 relates one MBO-enhanced system to one ordinary target. | `VERIFIED` | `CR18_LN.pdf`, printed p.108, defines conditional equivalence between an `(X,Y)×{0,1}` system and an `(X,Y)` system. `CondEquiv.lean:118` has exactly these two arguments. “Strict” is local disambiguating terminology, not CR18's adjective. | Retain, noting that “strict” is a local label. |
| CE-B-005 | 26-27 | CE is equality of response behavior while the MBO is zero. | `OVERSTATED` | Definition 4.19 equates conditional cumulative output distributions for every history where both conditional laws are defined. The Lean definition uses guarded cross-multiplied masses. It is not pointwise equality of deterministic response functions. | “CE equates the cumulative visible-output distribution conditioned on `A_i=0` with the target's cumulative output distribution.” |
| CE-B-006 | 28-29 | CR18 Theorem 4.17 converts CE into a bound by blind winning probability. | `VERIFIED` | `CR18_LN.pdf`, printed pp.109--110: if the enhanced source is conditionally equivalent to `T`, then `Delta(S,T) <= Gamma(b Shat)`. Current Lean endpoints implement this under explicit framework hypotheses. | Retain with those hypotheses. |
| CE-B-007 | 30-31 | MPR07 Lemma 5 enhances both source systems with MBOs. | `VERIFIED` | `MaPiRe07.pdf`, printed p.140, Lemma 5 constructs `Shat` and `That`, both `(X,Y×{0,1})` random systems with MBOs. | Retain. |
| CE-B-008 | 31-32 | The two enhanced systems have equivalent pre-winning/common parts. | `VERIFIED` | Lemma 5(iii) states restricted equivalence of the masked systems; Definition 10 says this means equivalence as long as the MBO is zero. | Prefer the paper's term “restricted equivalent” and define the masking operator. |
| CE-B-009 | 32-33 | The MPR construction is exact for every fixed distinguisher and horizon. | `VERIFIED` | Lemma 5(iv) gives `delta_k^D(S,T) = nu_k^D(Shat) = nu_k^D(That)` for every `D`; `k` is arbitrary. The exact quantity is transcript statistical distance, not an arbitrary preselected verdict advantage. | Retain with the `delta_k^D` qualification. |
| CE-B-010 | 33-34 | MPR07 Lemma 5 is not a completeness theorem for strict one-sided CE to a preselected target. | `VERIFIED` | Lemma 5 constructs two new enhanced systems and asserts restricted equivalence between them. It does not assert `Shat |equiv T` for the original ordinary target `T`. | Retain. |
| CE-B-011 | 35-37 | Representative selection and coupling attainment are Lanzenberger equivalence-class results. | `VERIFIED` | Thesis Definition 2.17 (printed p.16) defines equivalent PDS/equivalence classes; Theorems 2.31--2.32 (p.20) give distance/advantage attainment and coupling; Theorem 2.37 (p.24) gives winnability attainment for games. | Retain. |
| CE-B-012 | 38-39 | Choosing an equivalent PDS representative is not an operation of CR18 conditional equivalence. | `VERIFIED` | Definition 4.19 changes neither representative nor equivalence class; it relates an enhanced source to an ordinary target through conditional output laws. Representative replacement is a separate observational-equivalence claim. | Retain. |
| CE-B-013 | 38-39 | A proof that replaces a representative should expose a separate equivalence hop. | `NORMATIVE` | This is sound presentation guidance derived from the distinct definitions. | Retain as project policy. |
| CE-B-014 | 41-48 | The five-step design sequence is required by the cited theorems. | `NORMATIVE` | The sources do not prescribe this workflow or order. It is a sensible method-boundary checklist. | Label it explicitly as a recommended sequence. |
| CE-B-015 | 43-47 | Simulator design, optional representative replacement, and adjoining MBOs are separate transformations with separate obligations. | `VERIFIED` | They change different mathematical objects: target system, PDS representative, and monitored output alphabet/conditional law, respectively. | Retain. |
| CE-B-016 | 49 | An unqualified probability coupling requires a nonnegative joint law with the required marginals. | `VERIFIED` | The classical coupling theorem and current `DistCoupling`/`Dist.ProbDist` coupling declarations use honest nonnegative joints. Signed joints must be explicitly qualified and are not couplings in this source sense. | Retain. |
| CE-B-017 | 51-54 | Designing the simulator with CE in mind is valid and changes the target; it is not representative selection without an equivalence proof. | `VERIFIED` | This follows directly from the argument positions of Definition 4.19 and Definition 2.17. A simulator defines the ordinary target behavior, whereas representative selection stays inside an equivalence class. | Retain. |
| CE-B-018 | 58-59 | Once real system and target are fixed, `cond` is a free parameter. | `OVERSTATED` | `gameOf S cond` strips to `S` for any `cond`, but Theorem 4.17 applies only after proving monotonicity, CE, probability/totality, and normalization. Thus `cond` is a design variable constrained by new proof obligations, not a freely substitutable theorem parameter. | “One may choose any monotone condition for which the strip identity, CE identity, and endpoint hypotheses are proved.” |
| CE-B-019 | 59-60 | Refining the condition automatically refines the numerical bound on the same endpoint and with the same proof plumbing. | `FALSE` | A smaller winning event can fail CE; a larger one can increase `Gamma^b`; changing the bit changes the game. No generic Lean theorem transfers CE or orders blind winning probabilities under arbitrary predicate refinement. | “A proposed refinement requires a fresh CE proof and a comparison or fresh estimate of the new blind winning probability.” |
| CE-B-020 | 61-62 | Simulator design is another degree of freedom before the systems are fixed. | `VERIFIED` | The target `T` is an input to CE, so redesigning the simulator changes the identity to be proved. “Equally important” is evaluative. | Keep the factual first sentence; label importance as heuristic. |
| CE-B-021 | 64-67 | A disappointing bound can result from a coarse MBO or a poorly chosen simulator. | `VERIFIED` | Both choices affect whether CE holds and the size/analyzability of the monitored winning event. | Replace “the single most important habit” with a nonexclusive diagnostic. |
| CE-B-022 | 64-67 | Diagnosing the MBO and simulator is “the single most important habit” in this family. | `NORMATIVE` | This is an emphasis choice, not a theorem or exhaustive diagnosis. Slack can also enter when estimating `Gamma^b`, in a hybrid/reduction, in a query-budget relaxation, or in a metric conversion. | “Inspect the MBO, simulator, winning-probability estimate, and outer reductions separately.” |
| CE-B-023 | 69-75 | The cited source, lemma number, and printed pages are correct. | `VERIFIED` | `MaPiRe07.pdf`, printed pp.140--142 (PDF pages 11--13), contains Lemma 5 and its construction. | Retain. |
| CE-B-024 | 73-75 | The four displayed MPR07 properties match Lemma 5. | `VERIFIED` | Items (i)--(iv) match the paper, modulo typography: erasure gives `S,T`, restricted/masked systems are equivalent, and transcript distance equals both win probabilities for every `D`. | Use the paper's exact restricted-system symbol or define the local glyph. |
| CE-B-025 | 75 | The exact quantity in Lemma 5(iv) is `delta_k^D`, the statistical distance of the two transcript laws. | `VERIFIED` | This is exactly Definition 12 and Lemma 5(iv). It implies optimal information-theoretic distinguishing statements, but the displayed equality itself is deliberately about transcript distance. | Retain `delta_k^D` explicitly and state any optimal-decision corollary separately. |
| CE-B-026 | 77 | The minus operator erases the MBO. | `VERIFIED` | MPR07 Definition 9(i) defines `S^-` by ignoring the MBO. | Retain. |
| CE-B-027 | 77-79 | The restricted systems agree before winning, and the construction splits pointwise common transition mass. | `VERIFIED` | Definition 10 and Lemma 5(iii) give restricted equivalence. Equations (4)--(5), printed pp.141--142, use minima of cumulative conditional masses and recursively allocate residual mass. | Retain with “restricted/masked systems,” not only “laws.” |
| CE-B-028 | 79-81 | The symmetric condition-game method can attain transcript distance but does not imply exact strict CE to the original fixed target. | `VERIFIED` | This is precisely the logical scope of MPR07 Lemma 5 versus CR18 Definition 4.19. | Retain. |
| CE-B-029 | 83-92 | The four listed responses to a loose bound are source-mandated moves. | `NORMATIVE` | They are proof-design options, not consequences of one theorem. | Keep as a checklist. |
| CE-B-030 | 85-86 | Refining a fixed-pair MBO is valid once one identifies overcharging. | `OVERSTATED` | Diagnosing overcharge only proposes a new predicate. One must reprove monotonicity and CE and estimate the new blind winning probability. | Add all three obligations explicitly. |
| CE-B-031 | 87-90 | Simulator redesign can enlarge a matchable good kernel; symmetric games are available when both sides need residual branches. | `VERIFIED` | This accurately separates target redesign from the MPR two-game construction. “Larger honest kernel” is intuition, not a formal term. | Retain with formal obligations stated. |
| CE-B-032 | 91-92 | Representative selection must remain a separate Maurer--Lanzenberger hop. | `VERIFIED` | Follows from thesis Definition 2.17 and Theorems 2.31--2.32, which are not Definition 4.19. | Retain. |
| CE-B-033 | 94-98 | Conditional equivalence and the word “collision” impose no asymptotic rate; the winning-probability theorem supplies it. | `VERIFIED` | Theorem 4.17 only upper-bounds advantage by `Gamma(b Shat)`. CR18 Lemma 4.18 supplies a birthday estimate in the switching example. Other games may have different rates. | Retain. |
| CE-B-034 | 94-98 | `seededHashCollision` is not useful merely because it is named “collision”; its CE identity and blind winning-probability estimate must be proved. | `VERIFIED` | Both are genuine hypotheses in the route. The endpoint also has standing monotonicity, strip, probability, totality, nonempty-carrier, and decidability obligations, which the later table lists. | Retain. |
| CE-B-035 | 100-102 | A replacement condition cannot improve the theorem until its CE identity and winning-probability estimate have both been proved. | `VERIFIED` | These are necessary: a smaller event without CE is unsound, and CE without a smaller proved winning bound gives no numerical improvement. Standing endpoint hypotheses still apply. | Retain and optionally mention an explicit comparison with the incumbent. |
| CE-B-036 | 104-106 | Choosing a ready-made bad predicate is already a decision affecting the final constant. | `OVERSTATED` | The predicate constrains the monitored event, but it does not determine the quality of its probability estimate. Different analyses can give different constants, and the predicate may fail CE entirely. | “The predicate constrains the event to be estimated; the final constant also depends on its analysis and outer reductions.” |
| CE-B-037 | 104-107 | Sketching before search and fan-out for difficult MBO design are mandatory mathematical consequences. | `NORMATIVE` | Local workflow policy. | Retain only as policy, not evidence about CE. |
| CE-B-038 | 109-113 | There are exactly two doors and the packaged one is almost always correct. | `NORMATIVE` | The library offers these two highlighted endpoints, but other wrappers and direct per-distinguisher theorems exist. “Almost always” has no usage evidence. | “Two common entry points are the seeded wrapper and the assumption-explicit `gameOf` theorem.” |
| CE-B-039 | 113 | The packaged endpoint is at `SwitchingLemma.lean:1864`. | `STALE` | It is currently at `SwitchingLemma.lean:1891`. | Update the line or omit volatile line numbers. |
| CE-B-040 | 115-126 | The displayed packaged signature is exact. | `OVERSTATED` | Argument order and conclusion match, but the declaration also has `{A I O}`, `[Nonempty I]`, and `[forall a l, Decidable (bad a l)]`. A current `#check` confirms these omitted premises. | Print the full signature or mark omitted typeclass context with an ellipsis. |
| CE-B-041 | 128-129 | The wrapper exactly models a seed-indexed last-query evaluator with a history-monotone bit. | `VERIFIED` | `seededConditionCGame` samples `a` from `D`, visibly returns `F a (l.getLast h)`, and outputs `decide (bad a l)`. Its strip is `ofFunDist (fTransform F D)`. | Retain. |
| CE-B-042 | 128-131 | Every such evaluator should use this endpoint. | `NORMATIVE` | It is a natural fit, but another theorem may give a sharper or simpler route. | “This endpoint applies directly when its exact model and hypotheses match.” |
| CE-B-043 | 130 | The endpoint formally covers the current CBC-MAC proof. | `VERIFIED` | `CBCMAC.lean:1086` invokes it; `cbc_mac_randomness_expander` is axiom-clean in the focused check. | Retain. |
| CE-B-044 | 130 | The endpoint formally covers NMAC in the current tree. | `UNVERIFIED` | Current source comments mention Gaži's random-outer NMAC hop, but no NMAC theorem invokes the wrapper. | “The wrapper was designed to match Gaži's NMAC shape; no current NMAC endpoint demonstrates it.” |
| CE-B-045 | 130 | The endpoint covers the switching-lemma family. | `VERIFIED` | `seededHashThenURFGame` and its bound invoke the wrapper; the base URF/URP switching theorem also uses the `gameOf` CE route. | Retain with the concrete theorem names. |
| CE-B-046 | 130-131 | The endpoint covers “most keyed constructions.” | `FALSE` | It covers a distribution of deterministic functions fixed by one seed. Stateful, randomized-per-query, multi-interface, or non-last-query constructions need other models. | Delete the breadth claim. |
| CE-B-047 | 133-141 | The obligations listed correspond to actual endpoint hypotheses. | `VERIFIED` | Current `#check` shows `hmono`, `hD`, `hT`, `hTtot`, `hCE`, and `hleaf`, plus typeclass context. | Retain and add omitted typeclasses. |
| CE-B-048 | 137-139 | Monotonicity/probability/totality are always routine and closed by the listed tactics. | `OVERSTATED` | They are short for registered standard models, but `cr18_prob`/`cr18_total` are not complete solvers for arbitrary `D,T`. Monotonicity can be a substantive invariant. | Label them “standing/model obligations; often reusable,” not universally routine. |
| CE-B-049 | 140 | `hCE` asserts exact conditional-law equality, not a numerical closeness bound. | `VERIFIED` | `CondEquiv` is an equality of cross-multiplied masses guarded by nonzero normalizers. | Retain with that precision. |
| CE-B-050 | 141 | `hleaf` is the seed mass of `bad` on a blind winner's fixed query list. | `VERIFIED` | Exact current signature uses `D.mass (fun a => bad a (blindQueryList w q)) <= eps`. | Retain. |
| CE-B-051 | 143-147 | The packaged wrapper removes response adaptivity before the leaf counting problem. | `VERIFIED` | `IsBlind w` means `w l1 = w l2` whenever histories have equal length; `blindQueryList w q` is therefore a fixed optional/stopping schedule independent of answers. | Retain, scoped to this wrapper. |
| CE-B-052 | 145-147 | No response-adaptive query choice survives into the packaged endpoint's counting leaf. | `VERIFIED` | `hleaf` is uniformly quantified over deterministic blind winners but evaluates one fixed list for each; CE reasoning lies in a separate premise, not in the counting leaf. | Retain with this scope. |
| CE-B-053 | 149-151 | The three named seeded-game facts exist and are invoked inside the wrapper. | `VERIFIED` | Current theorem body calls monotonicity, probability, and totality facts. | Retain. |
| CE-B-054 | 151 | Those facts are located at `SwitchingLemma.lean:1833-1858`. | `STALE` | Current locations are approximately 1844, 1855, and 1863. | Omit line numbers or update them. |
| CE-B-055 | 155 | The three raw theorem locations 1343, 1359, and 1383 correspond to unfiltered, successor-filtered, and all-`q` endpoints. | `VERIFIED` | Current `GameOf.lean` declarations appear at those lines with those roles. | Retain. |
| CE-B-056 | 157-164 | The displayed unfiltered theorem signature is correct. | `VERIFIED` | Current `#check` confirms `S T cond`, monotonicity, two probability proofs, two totality proofs, finite-query normalization, then CE implies the blind bound. | Retain. |
| CE-B-057 | 166 | The raw theorem has “seven hypotheses plus conditional equivalence.” | `FALSE` | Before the CE implication it has six proposition-valued premises: monotonicity, two probability proofs, two totality proofs, and normalization. CE is the seventh. `S,T,cond` are data arguments, not additional hypotheses. | “Six standing/normalization premises, followed by the CE implication.” |
| CE-B-058 | 166-167 | `Gamma^b` is a supremum over adaptive blind winners. | `FALSE` | `BlindConverter.lean:51-71` defines blind winners as reply-value independent and `Gamma^b` as the supremum over blind winner distributions. CR18 Definition 4.20 explicitly calls this nonadaptive. | “`Gamma^b` is the maximal winning probability over nonadaptive blind winner distributions.” |
| CE-B-059 | 166-168 | Door 1 completely discharges the `Gamma^b` proof obligation. | `OVERSTATED` | Door 1 packages the supremum/run reduction, but the user still proves `hleaf`, a uniform fixed-schedule seed-mass bound. | “Door 1 reduces the blind supremum to `hleaf`.” |
| CE-B-060 | 170-171 | Door 2 should be used only when the real system is not a seeded evaluator. | `NORMATIVE` | A seeded system may still need Door 2 for a different monitor, state exposure, or theorem shape. | “Prefer the wrapper when its exact seeded last-query model matches; otherwise explain the raw route.” |
| CE-B-061 | 175-187 | The skeleton uses the packaged endpoint with the correct explicit argument order. | `VERIFIED` | It supplies `D F bad hmono q Ideal eps hCE hD hT hTtot hleaf`, matching current declaration order. Ambient typeclass assumptions are hidden by the ellipsis. | Retain as schematic code and mention the omitted typeclasses. |
| CE-B-062 | 177-179 | The MBO-strip equality is a necessary explicit hop from the named real system to the generic game. | `VERIFIED` | The wrapper concludes about `ignoreMBO (seededConditionCGame ...)`; a construction-specific realization equality such as `cbcGame_ignoreMBO` identifies it with `Real`. | Retain. |
| CE-B-063 | 189 | Compiling the skeleton before filling holes is a theorem requirement. | `NORMATIVE` | Proof-development advice. | Retain as policy if desired. |
| CE-B-064 | 193-196 | `CBCMAC.lean` is a completed instance of this endpoint. | `VERIFIED` | `cbc_mac_randomness_expander` invokes the wrapper and its focused `#print axioms` contains no `sorryAx`. | Retain. |
| CE-B-065 | 193-196 | Readers must not inspect the instance before routing because doing so necessarily prevents transferable learning. | `NORMATIVE` | Pedagogical policy and anecdote, not a mathematical fact. | Move to workflow guidance or delete. |
| CE-B-066 | 198-201 | The CBC result has a three-hop `calc`: strip, packaged endpoint, birthday arithmetic. | `VERIFIED` | `CBCMAC.lean:1081-1095` has exactly this structure. | Retain. |
| CE-B-067 | 199-201 | CBC has exactly two scheme-specific inputs and every other input is generic. | `OVERSTATED` | The two creative inputs are CE and the leaf count, but the proof also supplies scheme-specific monotonicity, strip/realization, probability, totality, prefix-freeness, and block-length facts through named lemmas. | “The wrapper leaves two principal creative obligations; the model-specific standing facts are cited separately.” |
| CE-B-068 | 203-211 | Every scheme using the wrapper needs its own CE proof and fixed-schedule leaf bound. | `VERIFIED` | These are direct hypotheses of the endpoint. | Retain. |
| CE-B-069 | 206-209 | A keyed cascade CE proof is typically a group-action/fiber-balance rerandomization. | `UNVERIFIED` | The current CBC proof does use a rerandomization/fiber count, but one example does not establish typicality across keyed cascades. | “CBC's CE proof uses a rerandomization/fiber-balance argument; other constructions may differ.” |
| CE-B-070 | 210-211 | The wrapper's leaf is pure combinatorics on a fixed query list because blindness removed response adaptivity. | `VERIFIED` | Exact signature and `blindQueryList` definition support this statement. | Retain. |
| CE-B-071 | 215-217 | `CondEquiv.lean` defines `|equiv` in guarded, cross-multiplied, division-free form without `DecidableEq`; `TotalOnNonempty` is at line 96. | `VERIFIED` | `CondEquiv.lean:96,118` and its definition body match. The definition quantifies over nonzero `massAfalse` and `massDom` normalizers. | Retain. |
| CE-B-072 | 218-219 | `condEquiv_filterDom` and `condEquiv_filterQueries` preserve CE. | `VERIFIED` | Current declarations at lines 203 and 237 compile; focused import succeeds. | Retain. |
| CE-B-073 | 218-219 | A filtered CE variant should never be reproved. | `NORMATIVE` | Reuse advice; a different filter/operator may need a new theorem. | “Reuse these exact same-filter preservation lemmas when they match.” |
| CE-B-074 | 220 | `GameOf.lean` contains `gameOf`, blind machinery, and Theorem 4.17 endpoints. | `OVERSTATED` | `gameOf` and endpoints are there; the foundational `IsBlind`/`Gamma^b` definitions live in `BlindConverter.lean`, imported by `GameOf`. | “`GameOf.lean` assembles `gameOf` with the imported blind machinery and public endpoints.” |
| CE-B-075 | 221-222 | `CBCStructureGraph.lean` has a proved tolerant CE route to the CBC bound. | `OVERSTATED` | `cbcGraphGame_condEquiv` is proved and axiom-clean, but “tolerant CE” is informal and the final bound also depends on unfinished counting. | “The graph game has a proved CE lemma; the final quantitative theorem is not complete.” |
| CE-B-076 | 221-222 | `CBCStructureGraph.lean` contains a full counting engine establishing the same CBC bound. | `FALSE` | `mass_cbcGraphBad_le` ends in `sorry`, and the headline inherits `sorryAx`; the file's own comment says the stated second-term constant is not reached by the current descriptor union. | Mark the counting leg open/admitted. |
| CE-B-077 | 223-224 | `seededHashCollision` and its monotonicity theorem exist and model collisions of distinct queried inputs. | `VERIFIED` | Current definitions at `SwitchingLemma.lean:1916,1927` match this meaning. | Retain with updated locations. |
| CE-B-078 | 223 | `seededHashCollision` is at line 1889. | `STALE` | It is currently at line 1916. | Update or omit the line. |
| CE-B-079 | 224 | All hash-collision proofs should reuse this predicate. | `NORMATIVE` | It fits seed-indexed deterministic hashes and distinct-input collisions, not every hash model or collision notion. | Scope the reuse advice to its exact type and event. |
| CE-B-080 | 228-229 | If `Gamma^b` appears in a user goal, the proof is necessarily on Door 2 and should not bound it directly. | `FALSE` | `Gamma^b` can appear inside custom wrappers, game theorems, or while proving a reusable Door-1-style leaf reduction. The statement is workflow advice, not a logical classification. | “Before proving a blind-supremum bound directly, check for a wrapper reducing it to a fixed-schedule leaf.” |
| CE-B-081 | 231-233 | `hCE` is exact equality, not a numerical bound. | `VERIFIED` | Current `CondEquiv` is an equality of guarded cross-products. | Retain. |
| CE-B-082 | 232-233 | In the direct CE endpoint, divergence outside the exact good-conditioned equality is charged through `Gamma^b`, and through `hleaf` in the seeded wrapper. | `VERIFIED` | This is the content of Theorem 4.17 and the wrapper's two-hop proof, once strip and standing hypotheses hold. | Retain with the direct-endpoint scope. |
| CE-B-083 | 235-236 | An MBO must be monotone; an event that can un-fire is not an MBO for this theorem. | `VERIFIED` | CR18's MBO definition and current `MonotoneMBO` require persistence of the bit. | Retain. |
| CE-B-084 | 236-237 | Replacing a nonmonotone event by its monotone closure makes the technique apply. | `FALSE` | Closure supplies monotonicity but can change the good-conditioned law and winning probability. CE and the probability bound must be reproved. | “The monotone closure is only a candidate monitor; reprove CE and its blind bound.” |
| CE-B-085 | 239-240 | The real system in a game-enhancement proof is the MBO-stripped game. | `VERIFIED` | CR18 Definition 4.18 and Lean `ignoreMBO_gameOf`/`seededConditionCGame_ignoreMBO` give this relationship. | Retain. |
| CE-B-086 | 240-241 | Every construction in the tree already has a library strip rewrite. | `UNVERIFIED` | Generic constructors and named CBC/seeded instances have rewrites, but no inventory proves this universal statement, and a new custom monitored construction must prove its realization identity. | “Use an existing strip lemma when present; otherwise prove the construction-specific realization equality.” |

## B. `creative-search.md`, lines 31--58

| ID | Lines | Atomic claim | Verdict | Evidence and reasoning | Safest replacement |
| --- | --- | --- | --- | --- | --- |
| CS-B-001 | 35-38 | After base real/target systems are fixed, one may choose among MBOs that actually establish strict CE, and the corresponding blind winning probability is the CR18 bound. | `VERIFIED` | Theorem 4.17 is polymorphic in the monitored game/condition and yields the bound after its hypotheses are proved. The qualification “that actually establish CE” is essential. | Retain; also mention monotonicity and strip/standing hypotheses. |
| CS-B-002 | 40-45 | Conditional equivalence itself imposes no birthday or other asymptotic rate. | `VERIFIED` | CR18 Theorem 4.17 ends at `Gamma(b Shat)`; the switching example separately applies Lemma 4.18 for its birthday rate. | Retain. |
| CS-B-003 | 41-45 | Once monitored source, target, and CE proof are fixed, numerical rates enter through estimating that source's blind winning probability. | `VERIFIED` | This exactly describes the direct Theorem-4.17 hop. Outer reductions may add other terms in a larger proof, so scope it to the CE hop. | Add “for this CE hop.” |
| CS-B-004 | 47-49 | Changing the MBO or simulator creates a new CE identity and new winning-probability problem. | `VERIFIED` | Each change alters an argument of `CondEquiv` or the monitored game whose `Gamma^b` is bounded. | Retain. |
| CS-B-005 | 47-49 | A proposed smaller bad event alone does not justify a new theorem. | `VERIFIED` | A smaller event may destroy conditional equality; even if CE survives, its blind mass still needs proof. | Retain. |
| CS-B-006 | 49-53 | Strict one-sided CE, MPR symmetric restricted games, H bad sets, coupling disagreement, and representative selection are distinct proof objects with distinct obligations. | `VERIFIED` | The cited definitions/theorems use different objects and conclusions. This separation is the strongest part of the guidance. | Retain. |
| CS-B-007 | 51-53 | The different proof objects should be compared only after each one's own equality and probability obligations are stated. | `NORMATIVE` | This is sound presentation and review guidance; the objects can still be related by explicit reductions or equivalence hops. | Retain as policy. |
| CS-B-008 | 55 | Stage 1 must be Lean-free and high-freedom. | `NORMATIVE` | Local workflow policy, not a mathematical consequence of CE. | Retain only in workflow guidance. |
| CS-B-009 | 55-57 | A ready-made predicate is not evidence of CE or of a winning-probability estimate. | `VERIFIED` | Neither property follows from the predicate's definition alone; both are separate theorem hypotheses. | Retain. |

## Primary-source receipts

The following pages were rendered and inspected visually:

- `papers/CR18_LN.pdf`, PDF pages 60--62, printed pp.107--111:
  Definition 4.18, Definition 4.19, Definition 4.20, and Theorem 4.17.
- `papers/MaPiRe07.pdf`, PDF pages 11--13, printed pp.140--142:
  Lemma 5 and the recursive common-mass construction.
- `papers/thesis (1).pdf`, PDF pages 26, 30, 34, and 36, printed pp.16,
  20, 24, and 26: Definition 2.17, Theorems 2.31--2.32, Theorem 2.37,
  and its alternative representative-based proof.

## Lean receipts

A focused scratch import of `RandomSystems.CBCMAC` and
`RandomSystems.CBCStructureGraph` compiled. Current `#check` receipts confirm
the signatures cited above. `#print axioms` found no `sorryAx` in:

- `maxAdvantage_filterQueries_seededConditionCGame_le`;
- `maxAdvantage_le_blindMaxWinProb_of_deltaFiniteQueryNormalization`;
- `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv`;
- `cbc_mac_randomness_expander`;
- `cbcGraphGame_condEquiv`.

The separate structure-graph headline remains unsound as a completed result:
`mass_cbcGraphBad_le` contains an explicit `sorry`, and downstream quantitative
theorems inherit it.

## Coverage receipt

| Target | Covered lines |
| --- | --- |
| `conditional-equivalence.md` | 15-19, 21-54, 56-107, 109-171, 173-211, 213-241 |
| `creative-search.md` | 31-58 |

## Release recommendation

Keep the source-notion separation, the exact MPR07 qualification, and the
fixed-schedule description of `hleaf`. Before release, remove automatic MBO
refinement claims, replace “adaptive blind winners” by “nonadaptive blind
winners,” print the packaged endpoint's full typeclass context, narrow its
application claims, and mark the structure-graph counting theorem admitted.
Most importantly, never use “representative” to describe simulator design or
conditional equivalence: representative replacement belongs to Definition
2.17/Theorems 2.31--2.32 and requires its own equivalence hop.
