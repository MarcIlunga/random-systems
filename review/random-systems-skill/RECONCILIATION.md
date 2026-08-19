# Reconciliation of the independent `random-systems-proofs` audits

Date: 2026-08-06

Status: **All three frozen-original audit pairs reconciled; frozen-snapshot cross-review closed.**

This is a reconciliation of frozen-snapshot audit reports, not a new audit of
the concurrently rewritten skill.  A verdict was never selected by
vote.  Wherever the reports differed substantively, the resolution below was
checked against the cited primary source or the current Lean declaration.  A
compound sentence is split into atomic claims when its factual and normative
parts warrant different verdicts.

## Audit-integrity and snapshot map

| Partition | First report | Second report | Integrity result |
| --- | --- | --- | --- |
| Conditional equivalence | `ce-audit-a.md` | `ce-audit-b.md` | Valid pair for the same frozen CE text.  B did not open A, but disclosed prior exposure to `CE_CLAIM_INDEX.md`; it is independent in verdict/evidence, not perfectly blind to claim partitioning. |
| Core and planning | `core-and-plan-audit.md` | `core-and-plan-audit-b.md` | Valid pair.  Both concern the frozen 416-line `SKILL.md` (`d2ed1ec0…`), four-line `agents/openai.yaml` (`ec74a5f3…`), and 215-line `sketch-and-plan.md` (`a94ef630…`). |
| Proof-family references | `families-audit.md` | `original-families-audit-b2.md` | Valid pair for the frozen original family text.  The first three hashes match exactly.  B2 used recovered `creative-search.md` hash `83a0aea8…`; its authorized lines 15–29 and 51–118 map to audit-target lines 15–29 and 59–126, excluding the separately audited CE insertion.  Its two exposure qualifications are recorded below. |

`families-audit-b.md` remains outside that pair: its sealed hashes show that it
audited rewritten family files.  It is useful release-audit evidence, but it
must not be represented as an independent verdict on the originals.

B2's isolation was qualified in two disclosed ways.  The governing skill-use
rule forced it to read the current installed `SKILL.md`, although it did not
read any current reference file.  An accidentally broad `rg` also exposed
three `#check` declaration-name lines from
`review/random-systems-skill/audit-probes/RewrittenSurfaceProbe.lean`; it
exposed no verdict or conclusion, and all later searches excluded `review/**`.
These are protocol-level exposures, not hidden claim-evidence dependencies.

The later post-rewrite audit B records a distinct final installed-skill
snapshot: 213-line `SKILL.md`, SHA-256 `13e8c3e3…`, with a release `PASS`.
That is a separate release audit.  The closure in this document concerns the
frozen-original cross-review and does not derive a rewrite verdict by vote.

## Direct reconciliation receipts

The decisive declaration checks were:

- `RandomSystems/SwitchingLemma.lean:1891–1913`: the seeded CE endpoint has
  `[Nonempty I]`, decidability of `bad`, `hmono`, `hCE`, probability/totality
  receipts, and `hleaf`; its body reduces the intermediate `Γᵇ` goal to
  `hleaf`.
- `RandomSystems/GameOf.lean:1343–1348`: the raw endpoint has six proposition
  side conditions followed by CE, not “seven plus CE.”
- `RandomSystems/BlindConverter.lean:51–71`: blind winners are nonadaptive
  with respect to live replies; `Γᵇ` is a supremum over blind winner
  distributions.
- `RandomSystems/HTechnique/Derivation.lean:433–447` and
  `HTechnique/SecurityDefs.lean:127–139`: `adv_le_of_fixedQuery_eq_on_good`
  concludes `Adv`, whereas `filteredDelta_le_Adv` is the missing raw-`Δ` bridge.
- `RandomSystems/HTechnique/Tactics.lean:35–58`:
  `htechnique_compress` is a finite, SoP-oriented rewrite bundle, not a generic
  repeated-query solver.
- `RandomSystems/RandomSystem.lean:72–113,445–485,8335–8376`: the current
  `statDist`/`δ`, partition, and Theorem 2.31 declarations and proofs.
- `sequence-hash/dispatch/codex-dispatch.sh:22–29`: the wrapper checks only
  that the preamble contains a literal adaptation instruction; it does not
  inspect the produced sketch.
- A focused `lake env lean RandomSystems/CBCStructureGraph.lean` failed at
  multiple current source locations (including 263, 1025–1126, 1400, and
  1440); `mass_cbcGraphBad_le` at 1423 still uses `sorry`.
- This reconciliation runtime exposes the `mcp__lean_lsp__lean_*` tool family.
  That does not contradict B's receipt that its own runtime exposed none.

Two additional Lean-LSP scratch checks compiled:

1. `statDist μ ν = δ μ ν` can hold although `ν` is not `NonNeg`: on `Bool`,
   take `μ = single false 1 + single true 1` and
   `ν = single false (-1) + single true 1`.
2. `δ_sum_of_disjoint_support` remains true without `hYnn` under its stated
   pairwise disjointness of `support (Xf i) ∪ support (Yf i)`.  The proof
   rewrites the support of the disjoint `Xf` sum as the disjoint bi-union and
   evaluates both sums in the unique active cell.  Thus the current theorem's
   `hYnn` is sufficient API baggage, not a necessary mathematical hypothesis.

## Pair 1: conditional equivalence

### Coverage receipt

| Report | Coverage and granularity |
| --- | --- |
| A | `conditional-equivalence.md` through line 241 (42 units including the title) and `creative-search.md` lines 31–58 (4 units).  It also ran focused source builds and checked the three primary-source families. |
| B | All substantive CE ranges 15–241 (86 atomic units) and the same creative-search slice.  It more aggressively split mixed sentences and checked primary PDFs plus focused Lean declarations/axioms. |

B did not separately ledger the line-1 title “Conditional equivalence (CR18
Thm. 4.17),” which A verified; this is the only small frozen-text coverage gap.
B's prior exposure to the claim index is an independence qualification, not a
defect in its direct evidence.

### Agreement themes

The reports agree on all central source boundaries:

- CR18 strict CE is one MBO-enhanced source versus one ordinary target, and
  Theorem 4.17 is an upper-bound implication, not a completeness result.
- MPR07 Lemma 5 is the symmetric two-enhanced-game, restricted-equivalence
  construction giving exact transcript distance; it is not strict CE.
- representative selection, attainment, honest coupling, and winnability are
  separate Maurer–Lanzenberger operations.
- changing an MBO requires fresh monotonicity, CE, and probability evidence;
  CE itself supplies no birthday rate.
- the packaged leaf is uniform over each blind winner's fixed
  `blindQueryList`, not an “adaptive blind winner.”
- the endpoint location/signature and several line pointers were stale;
  `[Nonempty I]` and decidability of `bad` were omitted.
- the raw endpoint has six side conditions plus CE.
- the formalized wrapper scope is narrower than NMAC/“most keyed
  constructions,” and `CBCStructureGraph` is unfinished.

### Substantive disagreements and resolutions

| Frozen claim | A | B | Evidence-based resolution |
| --- | --- | --- | --- |
| Lines 15–17: CE is for when “transcripts are not enough,” for an event the adversary triggers. | Grouped as overstated. | Split “triggered” as overstated and the transcript dichotomy as false. | **Literal dichotomy false.** `gameOf` itself accepts a transcript predicate, and CR18 examples use transcript collision conditions. “Interaction may provoke a hidden monotone bit” is only scoped intuition. |
| Lines 25–29: CE equates “response behavior while the MBO is zero.” | Verified, with a precision suggestion. | Overstated if read as pointwise response equality. | **Narrowly verified only as conditioned cumulative-law equality.** `CondEquiv` is guarded cross-multiplied mass equality, not equality of deterministic response functions. |
| Lines 64–67: loose bounds come from a loose MBO or simulator. | Normative diagnostic advice. | Factual possibility verified; “single most important” normative. | **Mixed.** Either choice can cause slack because both enter the endpoint, but causal priority/exhaustiveness is heuristic; the probability estimate and outer reductions can also lose constants. |
| Lines 104–107: choosing a predicate decides/affects the final constant. | Normative. | Overstated. | **Overstated as causation.** The predicate fixes an event to analyze, but CE may fail and different estimates/outer reductions can yield different constants. |
| Lines 109–113: exactly two doors, packaged door almost always right. | Normative; notes a history-aware third wrapper. | Normative; notes other wrappers/direct endpoints. | **Routing heuristic, not a taxonomy.** Say “two common entry points” and search specialized wrappers first. |
| Line 130: wrapper covers NMAC and “most keyed constructions.” | Composite overstated. | NMAC unverified; “most keyed” false. | **Atomic B resolution controls.** No current NMAC consumer was found; the universal breadth claim is false/unsupported because stateful, randomized-per-query, multi-interface, and non-last-query games need other models. |
| Lines 166–168: Door 1 “discharges” the raw `Γᵇ` obligation. | Verified if discharge means packaging it into `hleaf`. | Overstated because the caller still proves `hleaf`. | **Qualified:** the wrapper discharges the supremum/run machinery by reducing it to the uniform fixed-schedule `hleaf`; it does not eliminate the probability obligation. |
| Lines 228–229: seeing `Γᵇ` means the proof is necessarily on Door 2. | Overstated. | False. | **Literal necessity false.** Door 1's own implementation has an intermediate `Γᵇ` goal and reusable wrappers may expose one. Retain only as a diagnostic prompt. |
| Line 237: monotone closure makes the technique apply. | Normative candidate advice. | False as an implication. | **Literal implication false.** Closure establishes monotonicity only; CE and the new winning bound must be reproved. |
| Lines 239–241: every construction already has an `ignoreMBO` rewrite. | Overstated. | Unverified. | **Unsupported universal.** Generic and major named instances have strip lemmas, but a new/custom game may require its own realization equality. |
| Lines 206–209: keyed cascades “typically” use group-action/fiber balance. | Normative, based on CBC. | Unverified typicality. | **Only the CBC instance is verified.** Do not generalize one worked proof into a family theorem. |
| `CBCStructureGraph` build/status. | Direct single-file source check failed; count is admitted. | A scratch import compiled, while B also found the admitted count. | **Scope mismatch resolved in A's favor for source health.** Importing an existing olean is not a fresh check of the edited source. The current source fails focused elaboration and the central theorem contains `sorry`; the route is not completed regardless of import success. |

### Coverage gaps and unresolved items

- A isolated the unaudited “this is exactly what happened when first tested”
  anecdote; B grouped the surrounding reading-order advice as normative.  The
  anecdote has no primary receipt and must be deleted or linked to a durable
  test artifact.
- B separately caught the universal reuse wording for `seededHashCollision`;
  A mainly caught its stale location.  Reuse is safe only for the predicate's
  exact seed-indexed deterministic-hash collision model.
- A additionally tested the broken `GameWinnability`/`LanzenbergerChain`
  route; B concentrated on CE endpoints and primary-source semantics.
- No mathematical disagreement remains unresolved.  Empirical words such as
  “typically,” “almost always,” and “most” remain unverified and therefore
  cannot survive as factual guidance.

## Pair 2: core skill, agent metadata, and planning guide

### Coverage receipt

Both reports cover the frozen 416-line `SKILL.md`, all four lines of
`agents/openai.yaml`, and all 215 lines of `sketch-and-plan.md`.  A grouped
nearby claims; B atomized mixed sentences and repeated absolutes.  Both exclude
the internal factual claims of the other family-reference files except when
needed to verify navigation text.

### Agreement themes

The reports agree that the frozen core is unsafe unchanged because it:

- advertises “ANY theorem,” “every security statement,” and a closed
  seven-family taxonomy;
- presents a routing heuristic and finite tactic bundles as exhaustive or
  complete, including the false inference “tactic failure means model bug”;
- omits hypotheses from orientation, strict-metric, DPI, and shared-domain
  claims;
- overgeneralizes fixed-schedule CE behavior to every endpoint;
- contains a stage-4 skeleton whose outer raw-`Δ` goal does not match the
  cited `Adv` theorem;
- uses unsupported empirical superlatives, brittle counts, and absolute
  workflow/API rules;
- overstates SequenceHash enforcement and current build health; and
- treats Stage 4 as mechanical and the DAG as uniquely determining every
  generated obligation.

### Substantive disagreements and resolutions

| Frozen claim | A | B | Evidence-based resolution |
| --- | --- | --- | --- |
| Line 70: “Nothing enforces any of this.” | Verified for lack of a goal-shape/typeclass workflow hook; noted the SequenceHash preamble check. | Literal universal false. | **Literal statement false; narrow statement true.** Lean has no general workflow checker, but the dispatch script enforces preamble-marker presence and repository instructions impose process gates. It does not enforce actual adaptation. |
| Line 160: `htechnique_compress` handles repeated queries generically. | Overstated; SoP-specific. | Verified with a SoP qualification. | **Generic wording overstated.** The macro's rewrite list names SoP transcript-law declarations; it works on registered matching shapes, not arbitrary repeats. |
| Lines 177–186: stage-4 skeleton. | False: raw filtered `Δ` goal versus an `Adv` conclusion. | Verified only the inner endpoint's argument order/two legs. | **A identifies the decisive outer-goal mismatch.** Insert `filteredDelta_le_Adv` plus normalization, or change the goal to `Adv`. B's narrower signature check is compatible but incomplete. |
| Lines 241–244: `ControlledNaturalLanguage` “renders” paper-style proofs. | Overstated if this means rendering arbitrary proofs. | Verified as paper-style skeleton syntax. | **Terminology resolution:** it provides prose-shaped syntax which elaborates to theorem applications and named goals; it does not transform an arbitrary proof into prose. |
| Lines 254–262 and plan 178–182: lean-lsp availability. | Tools exposed in A's runtime. | Tools absent in B's runtime despite `.mcp.json`. | **Runtime-scoped, not mathematical.** The current reconciliation runtime exposes them. Guidance must say “when available,” with focused `lake env lean`/`#check` fallback. |
| Lines 273–275: Theorem 2.31 easy half is one DPI application. | Entire-proof wording overstated; analytic core is one DPI. | Verified after representative rewrites. | **Analytic-core claim verified; whole-proof claim overstated.** `optimal_advantage_le_class_distance` also performs `sInf`/`sSup` and representative rewrites before its one `δ_fTransform_le`. |
| Lines 292–294: `statDist = δ` “only when” the second law is `NonNeg`. | Treated `NonNeg` as the verified sufficient bridge. | Literal “only when” false. | **B is correct on necessity.** `statDist_eq_δ_of_nonneg` proves sufficiency only. The compiled signed `Bool` example above gives equality with a negative second law. |
| Lines 294–295: partition additivity is false without `NonNeg`. | False by a direct cellwise argument. | Unverified because current theorem assumes it but supplies no counterexample. | **Claim false.** The compiled generalized scratch theorem removes `hYnn` under the same pairwise union-support disjointness. Current API hypothesis is not a necessity result. |
| Line 299: `List (X × Option Y)` is infinite. | Not isolated. | Overstated: empty `X` gives only the empty list. | **B's qualification is required.** It is infinite when `X` is inhabited; generic code still lacks a `Fintype` instance. |
| Line 98: `δ = 0` beats every `δ ≤ ε`. | Treated as heuristic. | Overstated without `0 ≤ ε`. | **Requires `0 ≤ ε`.** Intended `NNReal` security budgets supply this, but the displayed untyped universal does not. |
| Lines 367–369: partition creates exactly two extra creative goals. | Overstated. | False. | **Literal count false.** Current equality and partition endpoints each expose two principal creative legs; their difficulty differs, not their count by two. |
| Line 131: a module is architected for one route. | Overstated. | False, citing a module with both CE and H styles. | **Literal invariant false.** At most, a local theorem/API may favor a route. |
| Plan 98–99: Lean cannot help clarify an unknown bound/technique. | Overstated. | False. | **Literal exclusion false.** Lean signatures, probes, and counterexamples can clarify the mathematics, though Lean cannot replace the argument. |
| Plan line 172: always stop at first search hit. | Normative but unsafe. | False as an absolute. | **Absolute false.** Inspect strength, hypotheses, status, and axioms; continue when the first hit is loose or unsuitable. |
| Plan lines 133–135: proving a creative node early necessarily causes drift. | Overstated. | False. | **Necessity false.** A node can be proved parametrically under explicit dependencies; early commitment merely risks drift. |
| Agent short description “Structure and verify …”. | Verified at high level. | Overstated as a guarantee while routes are provisional/broken. | **Interface-purpose text, not certification.** “Plan and audit selected Random Systems proofs” is safer; any “verify” promise must be conditional on current source/build receipts. |
| Declaration/notation counts. | About 10,591 declaration-like lines and 64 actual notation starts under one scan. | 9,816 tracked/11,332 including untracked and 77 actual notation lines under another scan. | **Methodology/scope mismatch.** Both refute the frozen `~6000/189` claim, but no single replacement count is justified. Remove hard counts or generate them with a documented command and scope. |

### Coverage gaps and reconciled omissions

- A alone caught the outer raw-`Δ`/`Adv` skeleton mismatch and fresh-build
  failure of `RandomSystems.HTechnique.Tactics`; these are substantive gaps in
  B's otherwise atomic ledger.
- B alone isolated the non-necessity wording for `NonNeg`, the empty-`X` list
  exception, the missing `0 ≤ ε`, and the internal “first deliverable” versus
  “not a deliverable” contradiction.
- B also split complete endpoint signatures from “creative legs only” in the
  planning DAG.  `hmono`, normalization, typeclasses, and model bridges cannot
  be erased merely because two creative leaves are highlighted.
- A's and B's lean-lsp receipts describe different runtimes.  Neither supports
  unconditional tool-availability prose.
- The metadata disagreement is editorial rather than mathematical; it is
  resolved conservatively by avoiding an unconditional verification promise.

No mathematical disagreement in this pair remains unresolved.  Unsupported
measurements, causal claims, and superlatives have a resolved operational
verdict—`UNVERIFIED`, hence delete or mark explicitly as anecdote—even though
their historical truth cannot be reconstructed from the available evidence.

## Pair 3: proof-family references

### Coverage and independence receipt

| File | A coverage | B2 coverage and mapping |
| --- | --- | --- |
| `h-technique.md` | All substantive ranges: 14–15, 17–49, 51–64, 66–101, 103–126, 128–153, 155–164. | Every substantive claim at frozen hash `dc920db8…`; headings and separators were explicitly accounted for. |
| `counting.md` | All substantive ranges: 16–32, 34–52, 54–68, 70–82, 84–99, 101–123, 125–141. | Every substantive claim at frozen hash `84b19b1f…`; headings and separators were explicitly accounted for. |
| `reshape-and-exact.md` | All substantive ranges: 16–33, 35–59, 61–114, 116–140, 142–163, 165–183. | Every substantive claim at frozen hash `2be7d137…`; headings and separators were explicitly accounted for. |
| `creative-search.md`, excluding CE | Audit-target lines 15–29 and 59–126. | Recovered-original lines 15–29 and 51–118 at hash `83a0aea8…`; these are exactly the target ranges after accounting for the target's eight-line-longer CE insertion.  Recovered lines 31–49 were deliberately excluded. |

B2 did not read A and produced an independently reasoned atomic ledger.  Its
current-`SKILL.md` exposure and the accidental exposure of three probe
declaration-name lines are the two qualifications stated in the integrity
section; neither exposed A's verdicts.  No undisclosed family range remains.

A third clean-source check in `POST_REWRITE_AUDIT_B.md` independently closes
H-010: an `rg` over `random-systems` excluding `.git`, `.lake`, and `review`
found `selectHTechnique` and `#h_grammar` only in frozen prose at
`h-technique.md:45,47`, with no local Lean definition or command syntax.  The
sibling `ccprover/CCProver/Surface/Techniques.lean` defines the selector at 209
and the command syntax at 253; the selector supports 15 explicit cases out of
the 60 combinations described by its three enums.

Fresh reconciliation receipts used below include the exact compression versus
numeric-bound declarations in `QueryCompression.lean`; the raw-law and modern
representative coupling signatures in `RandomSystemCoupling.lean`; the
normalization and common-domain premises in `StrictContextAdvantage.lean` and
`StrictContextSharedDomain.lean`; and the intended Theorem 2.37 statement in
`GameWinnability.lean:750`/`LanzenbergerChain.lean:283`.  Focused
`lake env lean` checks failed for `ReductionByConverter.lean`,
`AttainmentCounterexample.lean`, `Legacy/Amplification.lean`, and
`SoP/SoP2.lean`; their source declarations are therefore distinguished below
from current kernel receipts.  `Legacy/FundamentalTheorem.lean:172` contains
the admitted induction consumed by legacy system coupling.  The primary
Jha–Nandi article and Anthropic's official engineering article were inspected
for the two paper/process disputes rather than inferred from Lean prose.

### Agreement themes

The reports agree on the proof-family boundaries that matter for safe use:

- the H surface is sparse rather than a Cartesian product; extended endpoints
  cover selected equality/ratio variants, while selector/grammar commands and
  labelled spines are sibling-`ccprover` facilities;
- ordinary H endpoints expose recognizable equality, ratio, expectation, or
  partition obligations, but exact signatures include totality, probability,
  typeclass, projection, and model-specific plumbing that the teaching tables
  omit;
- `htechnique_compress`, `htechnique_total`, and the CR18 tactic bundle are
  finite registered automation, not completeness procedures;
- both union-bound skeletons omit `hD : D.NonNeg` and therefore do not
  elaborate, while the named blind CE wrapper really does pass its leaf the
  fixed `blindQueryList`;
- exact query compression and `compressedQuery_bound` are different facts;
  the latter only transports the cubic numerical side condition;
- the CBC structure-graph formalization is incomplete: its headline count is
  admitted and the current file does not pass a focused source check;
- raw distribution maximal coupling, representative attainment, and
  system-level advantage tightness are separate results with different
  hypotheses;
- thesis Theorem 2.37 is the equality `supWinProb = infWinnability` plus an
  attained equivalent representative, not the displayed generic
  `Delta ≤ nu(S^A)` inequality;
- the legacy fundamental/amplification routes and several signed-migration
  modules cannot presently supply clean build/axiom receipts;
- strict-metric comparison requires normalization, and equality additionally
  requires a common fixed domain; the deletion/rewind explanation is false;
- Anthropic's 90.2% result is scoped to one named internal evaluation and does
  not prove exclusive causation, a five-agent rationalization story, or the
  frozen fleet-outcome dichotomy.

### Substantive disagreements: H-technique

| Frozen claim | A | B2 | Evidence-based resolution |
| --- | --- | --- | --- |
| Line 14: “the bad thing is a bad transcript.” | Verified for ordinary H endpoints. | Overstated across the whole family. | **Scoped verification.** Ordinary good/bad endpoints use predicates or defects on transcript prefixes.  Perfect ratio has no bad event, partition uses cells, and extended variants use augmented transcripts; the literal family-wide slogan is too broad. |
| Lines 17–29: all five analyses implement/specialize partition, with the displayed arrows. | Mathematical subsumption useful, but implementation arrows false. | Atomic analysis descriptions mostly verified; unifying diagram overstated. | **Mathematical map, not dependency graph.** `hTechnique_partition` is derived from expectation; ratio-via-partition is a separate recovery and equality endpoints remain separate.  Relabel the diagram or show actual declaration dependencies. |
| Lines 31–39: the three axes form the library's endpoint grammar. | Vocabulary useful but not a uniform local grammar. | The 4/5/3 enum counts verified in sibling `ccprover`; Cartesian availability false. | **Naming taxonomy only.** The sibling enums really have 4 transcript, 5 analysis, and 3 filter values, and current names use that vocabulary.  The Random Systems surface implements only a sparse 15-of-60 subset and has no local grammar command. |
| Line 53: `OrdinaryH.lean` is “the library's own” selection rule. | Stale repository attribution/path. | Content verified when read in the sibling checkout. | **Both observations stand.** The heuristic exists in sibling `ccprover`; it is not repository-local Random Systems authority. |
| Lines 55–64: select the most specialized endpoint because it always has the fewest obligations; partition adds exactly two creative goals. | Selection rule treated as normative. | “Always fewest” overstated and exact extra-goal count false. | **Heuristic only.** Compare live signatures and elaborated goals: model-specific plumbing can dominate, and equality-on-good and partition each expose two principal creative premises, albeit of different kinds. |
| Lines 71–80: the creative-node table gives exactly the obligations for each analysis. | Overstated as exact signatures. | Principal ordinary rows verified; extended/representative row overstated. | **Use as planning labels only.** Ordinary rows capture the main mathematical premises, but complete signatures add normalization, totality, projections, weights, and instances; the representative row is not a generic family. |
| Lines 93–95: compile the skeleton; a residual mismatch means the endpoint was wrong. | Normative compilation advice. | The refine shape is verified, but the diagnosis is overstated. | **Compilation is a useful check, not a unique diagnosis.** Residual goals can come from omitted hypotheses, instances, coercions, or DAG errors without invalidating endpoint choice. |
| Lines 109–126: compression is generic and underwritten by `compressedQuery_bound`. | Exact only for function-evaluator-shaped laws; tactic SoP-specific. | Distinguished generic pushforward infrastructure from the tactic's registered shapes. | **Scope boundary:** `compressedQuery_injective` and the `fTransform_*_expand_compressedQuery` equalities are application-independent for sampled deterministic functions/function-evaluator laws.  They do not cover arbitrary stateful systems. `compressedQuery_bound` is numerical only, and `htechnique_compress` is SoP-shaped. |
| Line 137: the ratio must never be reversed and doing so “costs an hour.” | Orientation verified; time claim normative. | Absolute wording overstated. | **Keep the endpoint orientation** `(1-eps) * ideal ≤ real`; delete the time anecdote and impossibility wording.  A distinct symmetric argument may swap roles, but it is not the cited endpoint. |
| Lines 148–150: the two extended projections are routine, and difficulty proves the model wrong. | Two projection hypotheses verified. | Diagnostic conclusion overstated. | **Signature fact only.** `adv_le_of_extended_ratio_of_good` has two projections plus probability/weight premises.  Difficulty alone does not identify a modeling error. |
| Lines 152–153: never close the ideal bad bound by hand; use `probBad_iUnion_le`. | Normative advice. | False as an exclusive rule. | **Union bound is optional.** Use it for a useful finite cover; exact counting, direct mass evaluation, or other structural estimates may be sharper or necessary. |
| Lines 155–164: exemplar descriptions and superlatives. | Paths verified; grouped descriptions overstated. | Named patterns mostly verified; “heaviest” unverified. | **Cite declarations, not rankings.** The files contain the named styles, but some contain several styles and no census supports “heaviest” or similar superlatives. |

### Substantive disagreements: counting

| Frozen claim | A | B2 | Evidence-based resolution |
| --- | --- | --- | --- |
| Lines 36–52: the cover is pure logic/usually short, the leaf sum pure counting/usually long, and all real thinking starts there. | Union split verified as a useful plan; difficulty claims treated as normative. | Difficulty and “pure” classifications overstated. | **The theorem split is exact; the effort prediction is not.** Descriptor extraction can be the main combinatorial theorem, while a leaf sum may be one named lemma or may require analysis rather than “pure counting.” |
| Lines 72–74: a packaged endpoint turns every CE counting problem into a fixed list. | Verified for the displayed wrapper. | Overstated if generalized to packaged CE as a whole. | **Verified only for the named seeded blind wrapper.** Its leaf is over `blindQueryList w q`; this is not a theorem about every CE formulation. |
| Lines 84–88: normalization has no mathematical content and costs no error. | Generic “no content” wording overstated. | Exact normalization verified once its bridge applies. | **No numerical slack after a proved exact bridge.** Proving that bridge can be substantive, and arbitrary stateful repeated queries cannot simply be erased. |
| Lines 98–99: `cr18_close` is just the listed finishers and every counting proof should end with it. | Conceptually verified as an attempted finishing chain. | Operational list stale; universal use is normative. | **Description incomplete and use optional.** It also tries registered algebra and mass-expansion paths, guarantees no closure, and an explicit named calculation may be clearer. |
| Lines 112–116: the structure-graph route yields the linear-in-length CBC bound. | Paper result verified but Lean headline false/admitted. | False as a statement of current Lean completion. | **Separate mathematics from formalization.** Jha–Nandi's primary article, Theorem 6, gives `14σq/2^n + 16σqℓ^3/2^(2n) + q^2/2^(n+1)`, hence the stated linear-in-length order under its restrictions.  Current `CBCStructureGraph.lean` does not prove that headline: `mass_cbcGraphBad_le` uses `sorry` and the file fails focused elaboration. |
| Line 131: always compress before counting. | False. | Overstated. | **Delete the absolute.** Exact compression is valuable only when a matching theorem applies; direct repeated-vector or history-sensitive counting can be the correct route. |
| Lines 137–138: if a union bound is loose, the cover is the sole source of slack. | Overstated. | False. | **Not exhaustive.** Leaf estimates, correlations, weighted sums, inclusions–exclusion choices, and outer reductions can also lose sharpness, and the same cover can sometimes be analyzed more exactly. |
| Lines 140–141: the named cast/arithmetic tactics close the `NNReal → Real` tail. | Normative tooling advice. | Tool/idiom existence verified. | **Existence verified; closure not guaranteed.** Present the tactics as options and inspect the remaining goal. |

### Substantive disagreements: reshaping and exact methods

| Frozen claim | A | B2 | Evidence-based resolution |
| --- | --- | --- | --- |
| Lines 21–22: proving exact zero always beats every `delta ≤ eps` proof. | Verified as a heuristic. | Normative. | **Heuristic with a side condition.** Exact equality is strongest when `0 ≤ eps`, as intended for `NNReal` security budgets; the untyped literal implication needs that hypothesis. |
| Line 30: legacy `delta_eq_advantage` lets one move freely between distance and advantage. | Overstated scope. | Paper theorem verified, but the cited legacy route is admitted/non-reproducible. | **Unsafe operationally.** The legacy theorem depends on an admitted fundamental step.  The modern source-bounded attainment theorem is the usable analogue only with finite input, common-domain, boundedness, and nonnegativity hypotheses. |
| Line 45: parallel composition requires the user to supply nothing. | Verified only after reading this as “no new creative object,” while noting four probability proofs. | Literal “nothing” false. | **The additive theorem is current, but it has four explicit `isProbDist` premises.** Say that no separate coupling/hybrid object is needed, not that the application has no obligations. |
| Line 46: query restriction needs only two totality proofs. | Overstated. | False as a complete signature. | **Print the full theorem.** `maxAdvantage_filterQueries_le` also takes `dummy`, `q`, both systems, and the two `TotalOnNonempty` proofs. |
| Line 48: pointwise descent supplies everything after fixing a distinguisher. | The theorem description verified. | “You supply nothing” false. | **The descent theorem exists, but its premise is the work:** prove the bound for every admissible distinguisher. |
| Lines 74–75: a system coupling always exists, so existence never needs checking. | Overstated by legacy hypotheses. | False because the dependency is admitted. | **Literal claim false.** Legacy `system_coupling_exists` assumes finite fixed-query data, equal weights, and nonemptiness and depends on admitted representative attainment.  The modern theorem is explicitly conditional. |
| Lines 76–78: maximal coupling has no inherent slack for system advantage. | Overstated at system level. | Raw-law tightness verified. | **Two layers.** `optimal_probability_coupling_exists` realizes raw `δ S.val T.val` for supplied normalized laws.  Equality to system `maxAdvantage` additionally needs equivalent representatives, finite input, a common domain, and a uniform depth bound. |
| Lines 87–92: `SoP2.lean` proves the exact half-L1 and unconditional cubic online bounds. | Source formulas verified with caveats; current build stale. | Current formal result unverified because the module is blocked. | **Source statements exist but are not presently kernel-reproduced.** The exact theorem uses `m = min(q,N)` and `q ≤ card G`; the cubic corollary requires `q^3 ≤ N^2`.  Omitting that side condition is literally false. |
| Lines 108–114: a coupling proof has only a joint, two routine marginals, and a disagreement bound. | Broad obligation list verified, with a normalization caveat. | Overstated because joint nonnegativity is explicit and marginals need not be routine. | **Complete the obligation list:** joint construction, joint nonnegativity, two marginals, and disagreement analysis.  Difficulty is construction-specific; direct `coupling_bound` has no labelled local spine. |
| Lines 118–120: winnability gives `Delta ≤ nu(S^A)` and the cited workhorse is available. | Formula false; source endpoint stale. | Formula false and current module nonbuilding. | **Replace with thesis Theorem 2.37:** `supWinProb = infWinnability`, together with attainment by an equivalent representative.  `GameWinnability.lean` and its `LanzenbergerChain` wrapper currently fail focused checking, so the intended source endpoint is not presently citable. |
| Line 122: an MBO is the required creative input to winnability. | False. | Normative if read as planning advice. | **False as theorem description.** The workhorse takes a random game plus fixed-domain/boundedness hypotheses; no MBO appears.  A monitored game may be a design choice, not a signature requirement. |
| Lines 124–126: conditional equivalence is a winnability proof built by `gameOf`. | False. | Overstated relationship. | **Keep the methods distinct.** CE proves a one-sided conditional-law identity plus blind-winning bound; winnability is a random-game equality/attainment result.  `gameOf` can encode related data but does not identify their hypotheses or conclusions. |
| Line 146: `CausalApply.winProb_apply` is a proved converter equality. | Stale because its module does not build. | Source declaration/body verified. | **Source-present, current-endpoint stale.** `ReductionByConverter.lean:80` contains the intended equality, but a focused single-file check fails under current signed migration errors; no current kernel receipt is available. |
| Line 147: `ReductionByInstantiation.lean` implements the multiple-instantiation reduction. | Overstated. | Definition existence verified. | **Only partial infrastructure.** The file defines `sigmaPow q W := Dist.iidPow W q` and a reflexive support lemma; it does not package the application reduction theorem claimed. |
| Line 154: `Legacy.CC.Composition` supplies the full CC composition theorem. | Overstated scope. | Composition infrastructure verified. | **Use the exact local theorem.** The legacy file implements a simplified single-interface serial composition layer, not the full simulator-bearing, multi-interface CC framework. |
| Line 156: `threshold_combiner_bound_1_2` is proved and citable as the claimed LM20 result. | Stale/unavailable. | Source proof body verified. | **Source proof is locally complete, but citation remains blocked.** Its module cannot currently be focused-checked because the legacy import chain is missing oleans; it has no fresh axiom receipt and must be cited by its exact local statement, not as LM20 Theorem 3. |
| Line 167: `Delta` simply is advantage. | Overstated because nearby text also invokes class distance. | Verified as the local CR18 notation in that section. | **Locally true, globally unsafe.** `Δ(S,T)` in the modern CR18 namespace denotes `maxAdvantage`; Lanzenberger–Maurer class distance and raw static `δ` are different objects.  Use declaration names whenever the notions meet. |
| Line 169: `maxEDist ≤ ofReal Delta` is unconditional. | Overstated. | Normalized case verified; “unconditional” overstated. | **Normalization is required.** `maxEDist_le_maxAdvantage` assumes both laws are probability distributions.  Equality also needs a common fixed support-atom domain; the `filterDom` result is only a narrower corollary. |
| Lines 176–179: using an inequality instead of the equality necessarily introduces headline slack. | Normative anti-slack policy. | Overstated. | **Equality is the better identification receipt when its hypotheses hold, but the inequality may transfer the same upper bound without numerical loss.** Do not infer strict slack solely from theorem shape. |
| Lines 182–183: the counterexample theorem is available and establishes the one-versus-half gap, with no `maxEDist` statement. | Stale due current build failure. | Source claims verified. | **Intended source facts, not a current kernel receipt.** `AttainmentCounterexample.lean` contains the class-distance-one and advantage-one-half statements and no `maxEDist` theorem, but focused checking fails and the current source emits `sorry` warnings. |

### Substantive disagreements: creative search

| Frozen claim | A | B2 | Evidence-based resolution |
| --- | --- | --- | --- |
| Lines 25–29: the 90.2% gain comes from breadth-first independent directions, and five agents avoid solo rationalization. | Scoped result verified; causal and five-agent story unsupported. | Same, split into causal overstatement and unverified rhetoric. | **Only the scoped result survives:** Anthropic reported 90.2% for one named lead/subagent configuration on an internal research evaluation and said multi-agent systems excel especially on breadth-first work.  It did not establish exclusive causation, a five-agent ablation, or inevitable solo rationalization. |
| Lines 53–70: overlap is the main failure mode; cross-field/lower-bound scouts are where non-obvious answers come from. | The supply-chain anecdote verified; “main” and productivity ranking overstated/normative. | Anecdote verified; role ranking overstated. | **Retain the anecdote and angle menu only.** It documents one duplication failure, not the dominant one; proposed angles can overlap and have no proved productivity ordering. |
| Lines 90–99: agents are poor at effort sizing and the exact fan-out table is evidence-backed. | Universal effort claim overstated; counts normative. | Anthropic-specific sizing observation verified; counts local policy. | **Scope and label.** Anthropic reports that its agents struggled to size effort.  The frozen fan-out thresholds are tunable project policy, not an externally validated formula. |
| Line 107: parallel scouting is where wall-clock savings occur. | Overstated universally. | Verified only as a scoped possibility. | **Conditional claim:** independent complex work can benefit; Anthropic reports up to 90% reduction using 3–5 parallel subagents/tool calls.  Dependencies, contention, and coordination can eliminate the gain. |
| Lines 124–126: identical scout results prove either carrier-tightness or a shared blind spot. | Overstated. | False. | **Non-exhaustive dichotomy.** Insufficient search budget, incomplete angles, unavailable machinery, false shared assumptions, or simple discovery difficulty are additional explanations.  Agreement is evidence about the search, not a lower bound. |

### Coverage gaps, source-status distinctions, and closure

- A's grouped verdicts sometimes combined a sound atomic theorem fact with an
  unsupported superlative or workflow diagnosis.  B2's more granular ledger
  supplies the missing splits: ordinary H principal premises, exact
  normalization after a bridge, source declarations versus current build
  availability, and Anthropic-scoped observations versus local policy.
- B2 alone emphasized that the fixed-list CE statement is about the named
  blind wrapper, that “you supply nothing” hides the universal distinguisher
  premise, and that source-complete bodies such as
  `threshold_combiner_bound_1_2` still need a successful import/build and axiom
  receipt before current citation.
- A alone made several formalization-status distinctions especially explicit:
  the Jha–Nandi paper result versus the admitted Lean count, the outer theorem
  scope of legacy `delta_eq_advantage`, the partial nature of instantiation and
  composition infrastructure, and the lack of any `maxEDist` counterexample
  statement.
- Fresh reconciliation checks resolve apparent source/build conflicts:
  `ReductionByConverter.lean`, `AttainmentCounterexample.lean`, legacy
  amplification, and `SoP2.lean` do not currently pass their focused checks;
  source text alone therefore establishes intended statements, not current
  kernel certification.  Conversely, the raw coupling and strict-metric
  declarations were inspected with their exact hypotheses, so their narrower
  claims are current.
- No substantive mathematical disagreement remains unresolved.  Claims for
  which no stable measurement or primary receipt exists—popularity, line-cost,
  “routine,” “heaviest,” “main failure mode,” and similar superlatives—have the
  operational verdict `UNVERIFIED` or `NORMATIVE`; they cannot be presented as
  facts.

All three required original-snapshot pairs are now coverage-mapped and
claim-level reconciled.  The frozen-original audit is therefore **closed**.
`families-audit-b.md` remains deliberately excluded from Pair 3, and the
post-rewrite release audits remain separate evidence about later package
hashes.  This reconciliation edited no skill or frozen reference file.
