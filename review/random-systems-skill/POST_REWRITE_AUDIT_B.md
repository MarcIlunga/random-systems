# Post-rewrite release audit B — `random-systems-proofs`

Date: 2026-08-06  
Auditor: independent audit B  
Audited package: `/Users/marcilunga/.codex/skills/random-systems-proofs`  
Repository: `/Users/marcilunga/Documents/tob/research/random-systems`

## Release verdict

**PASS.** At the final hashes recorded below there are **zero open blocking
findings and zero open nonblocking findings**. The package is suitable for
release as a workflow/navigation skill.

This verdict is about the skill package, not a claim that every surface in the
current Random Systems working tree builds. The package accurately quarantines
the focused failures observed in H-technique SoP migration,
`CBCStructureGraph`, the Lanzenberger/winnability path, and legacy
amplification. It requires a current focused build and axiom receipt before any
such headline is cited as complete.

The target changed twice while this audit was running. I discarded the earlier
package verdict each time, reread every changed file from line 1, reran the
affected probes, and froze the final hashes below. Two defects found in an
intermediate target were corrected before the final freeze:

1. The H-technique application snippet originally used the wrong notation
   scope, left binder types uninferred, and split a namespace from its theorem
   name. The final lines 141–155 use
   `RandomSystems.CR18.HTechniqueDerivation`, fully type both binders, and the
   exact snippet elaborates in a focused probe.
2. The Lanzenberger status paragraph originally inferred admitted material from
   a build failure. The final lines 122–127 now state only the verified build
   block and explicitly say that it is not evidence of admission.

These are resolved delta observations, not open findings against the final
hashes.

## Independence and snapshot

- I did not open or read any file under `review/random-systems-skill`, nor any
  other auditor report. The only prior-audit exposure was a coordinator message
  saying that the release target had changed; no prior conclusions were used.
- Repository `HEAD`: `96e42831e51857aefa8d9e40e996061600061866`
  (`main`).
- Toolchain: Lake `5.0.0-src+98dc76e`; Lean `4.29.0`, commit
  `98dc76e3c0a9b856c9b98726b713fb04fab16740`.
- The repository working tree was dirty. In particular, several audited Lean
  sources were modified relative to `HEAD`, and `FOUNDATIONS.md` plus
  `papers/MaPiRe07.pdf` were untracked. Therefore the per-file hashes below,
  not the Git commit alone, identify the evidence snapshot.
- No broad `lake build` was run. All Lean checks were declaration probes,
  single-file checks, or focused module targets.

## Atomic findings

| ID | Status | Finding |
| --- | --- | --- |
| B-OPEN | none | No release-blocking defect remains at the final hashes. |
| N-OPEN | none | No nonblocking accuracy, navigation, metadata, or disclosure defect remains at the final hashes. |

## Claim-by-claim evidence

### Primary-source mathematics

The cited mathematical interpretations were checked on rendered pages, not
only extracted text.

| Package claim | Rendered primary evidence | Result |
| --- | --- | --- |
| CR18 Definition 4.19 is one enhanced source versus one ordinary target, with response law conditioned on the MBO remaining false; Theorem 4.17 gives the blind-game bound. | `papers/CR18_LN.pdf`, PDF pages 60–61 (printed pp. 108–110). | Verified. Definition 4.19 has exactly the one-sided conditional law; Theorem 4.17 concludes the blind winning-probability bound. |
| MPR07 Lemma 5 constructs enhanced versions of both systems, equates their pre-winning restrictions, and identifies each winning probability with transcript distance for every distinguisher/horizon. | `papers/MaPiRe07.pdf`, PDF pages 11–12 (printed pp. 140–141). | Verified. The symmetric construction is correctly kept separate from strict one-sided CE. |
| Lanzenberger/LanMau transcript equivalence, nonadaptive sufficiency, class-distance attainment, and honest coupling are finite/common-domain representative results. | `papers/LanMau20.pdf`, PDF pages 14–15. | Verified against Definition 10, Lemma 5, Definition 12, and Theorems 1–2. |
| Thesis Theorem 2.37 says `ν(S^A) = ω(S^A)` and an equivalent representative attains winnable mass `ω(S^A)`. | `papers/thesis (1).pdf`, PDF page 34 (printed p. 24), with the alternative proof on PDF page 36 (printed p. 26). | Verified verbatim in mathematical content. The final skill does not turn this into a generic `Delta <= nu` statement or conflate it with strict CE. |

The Maurer--Lanzenberger positive theory remains separate from the repository's
signed extension throughout the package. Unqualified “coupling” is reserved for
an honest nonnegative joint law; signed or virtual joints are explicitly not
called couplings.

### Lean declarations, namespaces, hypotheses, and axioms

A focused scratch import with `set_option autoImplicit false` checked all names
below. The probe exited 0 after using the exact fully qualified names.

| Surface claim | Exact current declaration / material hypotheses | Result |
| --- | --- | --- |
| Strict CE definition | `RandomSystems.CR18.CondEquiv.CondEquiv`; enhanced `PFunPDS X (Y × Bool)` versus ordinary `PFunPDS X Y`; both nonzero guards and the cross-multiplied normalizers are present. | Exact match to `conditional-equivalence.md` lines 31–43. |
| H equality endpoint | `RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_eq_on_good`; implicit `[FiniteTranscriptSpace X Y q]`; `ProbPDS`; both `KStepTotal`; fixed-query equality on good transcripts; bad mass for every `QQueryEnvironment`. | Exact orientation and hypotheses verified. Axiom receipt: `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`. |
| H ratio endpoint | `RandomSystems.CR18.HTechniqueDerivation.adv_le_of_fixedQuery_ratio_of_good`; `(1-eps) * tr(T) <= tr(S)` on good transcripts and conclusion `δb + eps`. | Exact orientation verified. |
| H application snippet | Final `h-technique.md` lines 141–155. | An exact standalone example with the stated import, scope, typed binders, and fully qualified call exited 0 under `lake env lean`. |
| Seeded CE endpoint | `RandomSystems.CR18.maxAdvantage_filterQueries_seededConditionCGame_le`; `[Nonempty I]`, decidable monitor, prefix monotonicity, CE, seed/target probability laws, target totality, and a leaf uniform over every blind winner. | Displayed signature is exact. Axiom receipt contains only `propext`, `Classical.choice`, `Quot.sound`. |
| Probability union bound | `RandomSystems.probBad_iUnion_le`; finite carrier/index, `D.NonNeg`, decidable pieces, and an event cover. | Exact match. No `sorryAx`. |
| Finset mass union bound | `RandomSystems.CR18.mass_biUnion_le`; finite nonempty carrier, `X.NonNeg`, `Finset` index set. | Exact match. No `sorryAx`. |
| Ratio-to-bad-mass lemma | `RandomSystems.CR18.HTechniqueDerivation.probBad_le_of_ratio`; both laws nonnegative and weight 1, comparison law zero on bad, one-sided ratio on good. | Prose summary is exact. |
| Birthday helper | `RandomSystems.CR18.pairCollisionUnionBound_le_birthday`; bounds its named expression by `(1/2) * r^2 / card X`. | Exact; the package correctly requires a construction-specific event cover. |
| Exact versus numerical compression | `RandomSystems.CR18.transcriptLaw_fixedQueryEnvironment_functionEvaluator_compress` is the evaluator-law equality; `RandomSystems.CR18.compressedQuery_bound` only transports the cubic side condition. | Exact scopes verified; both axiom-clean apart from the standard three axioms above. |
| Fixed-law maximal coupling | `RandomSystems.CR18.optimal_probability_coupling_exists`; two `PFunPDS.Prob` laws, normalized joint, two marginals, disagreement exactly `δ S.val T.val`. | Exact. No representative or causal-online conclusion is smuggled in. |
| Advantage orientation | `RandomSystems.CR18.adv_eq_maxAdvantage_swap`; hypotheses are `S.NonNeg` and `T.NonNeg`; conclusion `Adv S T = Δ(T,S)`. | Exact. |
| Strict metric inequality | `RandomSystems.CR18.StrictContextAdvantage.maxEDist_le_maxAdvantage`; both laws normalized. | Exact hypotheses and orientation. |
| Strict metric equality | `RandomSystems.CR18.StrictContextSharedDomain.maxEDist_eq_ofReal_maxAdvantage_of_sharedDomain`; both laws normalized and both have the same fixed domain `D`. | Exact hypotheses and orientation. |
| Completed CBC CE route | `RandomSystems.CR18.cbc_condEquiv` and `RandomSystems.CR18.cbc_mac_randomness_expander`. | Focused imports succeed; both print only `propext`, `Classical.choice`, `Quot.sound`. This is distinct from the incomplete optional structure-graph route. |

The named tactic claims were checked at their current definitions:
`cr18_prob` (`CR18TacticsCore.lean:35`), `cr18_routine`
(`CR18TacticsCore.lean:134`), `cr18_total`
(`TotalityTactics.lean:43`), and `htechnique_compress`,
`htechnique_adv_le`, `htechnique_total`
(`HTechnique/Tactics.lean:45,68,79`). Their implementations are finite
registered surfaces, not completeness procedures, exactly as the package says.

### Focused build and quarantine claims

The dated status paragraphs were rechecked against the current working tree.

| Command/check | Result | Package treatment |
| --- | --- | --- |
| `lake build RandomSystems.HTechnique.Tactics` | Exit 1. First failed target: `RandomSystems.HTechnique.SoP.VisibleLaw`; representative errors include `VisibleLaw.lean:85` (`Real` versus `NNReal`) and later signed-migration mismatches. | Correctly described as an imported SoP migration block, snapshot-sensitive, and not a mathematical failure. |
| `lake build RandomSystems.CBCStructureGraph` | Exit 1; source errors begin at line 263 and continue in signed mass lemmas. The central `mass_cbcGraphBad_le` is explicitly `sorry` at line 1428 and downstream `cbc_mac_beyond_birthday` uses it. | Correctly quarantined as incomplete and requiring a later clean build plus axiom receipt. |
| `lake build RandomSystems.GameWinnability` | Exit 1 with signed-distribution type/instance failures, beginning at `GameWinnability.lean:126`. | Correctly described as build-blocked. |
| `lake build RandomSystems.LanzenbergerChain` | Exit 1 through `GameWinnability` and `MultiSystemCoupling` signed-migration failures. | Correctly described as build-blocked, without inferring an admission. |
| Recursive import-closure scan from `RandomSystems.LanzenbergerChain` and `RandomSystems.GameWinnability` | 37 local modules; no source `sorry`, `admit`, or declared `axiom` in the closure. | Confirms the final wording: build failure is not evidence of admission. |
| `lake env lean RandomSystems/Legacy/Amplification.lean` | Exit 1 because `RandomSystems/Legacy/Equiv.olean` is unavailable; the source also contains an explicit `sorry` at line 119. | Final legacy-amplification warning is accurate. |

### H-010 third check — clean-source/frozen-original availability claim

This check was performed separately from the package prose and without reading
the review directory.

Command over `random-systems`:

```text
rg -n --hidden --glob '!.git/**' --glob '!.lake/**' --glob '!review/**' \
  'selectHTechnique|#h_grammar' \
  /Users/marcilunga/Documents/tob/research/random-systems
```

Exact hits:

```text
/Users/marcilunga/Documents/tob/research/random-systems/.claude/skills/random-systems-proofs/references/h-technique.md:45
/Users/marcilunga/Documents/tob/research/random-systems/.claude/skills/random-systems-proofs/references/h-technique.md:47
```

Both hits are prose in a frozen/local `.claude` skill copy. There is **no Lean
definition or command syntax** for either name in `random-systems`.

Command over the sibling `ccprover`:

```text
rg -n --hidden --glob '!.git/**' --glob '!.lake/**' \
  'selectHTechnique|#h_grammar' \
  /Users/marcilunga/Documents/tob/research/ccprover
```

Exact hits:

```text
/Users/marcilunga/Documents/tob/research/ccprover/CCProver/Surface/Techniques.lean:144
/Users/marcilunga/Documents/tob/research/ccprover/CCProver/Surface/Techniques.lean:209  def selectHTechnique
/Users/marcilunga/Documents/tob/research/ccprover/CCProver/Surface/Techniques.lean:249
/Users/marcilunga/Documents/tob/research/ccprover/CCProver/Surface/Techniques.lean:253  syntax (name := hGrammar) "#h_grammar" : command
/Users/marcilunga/Documents/tob/research/ccprover/CCProver/Surface/Techniques.lean:262
```

**Verdict:** `selectHTechnique` and `#h_grammar` are available in the sibling
`ccprover`, not in the Random Systems Lean project. Final `h-technique.md`
lines 69–71 state this correctly.

## Workflow, progressive disclosure, links, and UI

Workflow recommendations were classified as normative advice, not as theorem
or API-completeness claims. They are consistent with `AGENTS.md`, `DESIGN.md`,
`STATUS.md`, and `FOUNDATIONS.md`:

- start from the repository contract and current goal;
- use a paper sketch for genuinely new mathematics;
- search before inventing infrastructure;
- use Lean-LSP or a single-file probe while iterating;
- reserve focused Lake gates for verification;
- distinguish admissions, build failures, and mathematical failures;
- require final focused builds and `#print axioms` receipts.

The package does not present `lake env lean` alone as a release-green signal:
the final receipt immediately requires the applicable focused gates and axiom
checks. Its advice therefore remains compatible with `STATUS.md` §11.27.1 and
the package-level `autoImplicit false` setting.

Progressive disclosure passes. `SKILL.md` contains the shared workflow and a
route table, then directs the agent to read only the relevant reference. The
six references isolate sketching, H technique, CE, exact/metric/coupling,
counting, and authorized independent exploration. Snapshot-sensitive status is
confined to the relevant route and explicitly routes back to current
`STATUS.md` plus a focused check.

A validation script parsed both YAML documents, checked the frontmatter name,
verified the `$random-systems-proofs` invocation in the default prompt, ignored
links inside fenced code, and checked every local file link and TOC anchor.
Result:

```text
PASS: YAML, frontmatter, local links, and TOC anchors
```

UI metadata is consistent with the final scope:

- display name: `Random Systems Proofs`;
- short description: `Plan and audit Random Systems proofs`;
- default prompt invokes `$random-systems-proofs`, asks for current Lean
  declarations, and requires the applicable rendered primary source;
- frontmatter expressly allows RS leaves used inside `RandomSystemsCC` while
  excluding sole use for CC composition, AC/resource lifting, or complete
  multi-interface assembly.

## Full line-coverage receipt

Every line of every release file was read in the final snapshot. Blank lines,
fences, tables, and heading/TOC lines are included in the inclusive ranges.

| File | Final lines | Coverage and classification |
| --- | ---: | --- |
| `SKILL.md` | 1–213 | 1–15 metadata/reliability/scope; 17–52 repository and evidence rules; 54–124 route, links, ledger, and search; 126–162 Lean loop and automation facts; 164–196 normative proof/modeling discipline plus checked metric/orientation claims; 198–213 final receipts. |
| `references/conditional-equivalence.md` | 1–195 | 1–17 navigation; 18–74 primary-source and notion-separation claims; 76–100 normative monitor/simulator discipline; 101–143 exact endpoint and blindness facts; 145–183 obligations/library map/status routing; 185–195 review advice. |
| `references/counting.md` | 1–138 | 1–28 normative scope; 29–69 exact union/ratio declarations; 71–118 quantifier and counting advice plus birthday fact; 120–138 verification and checked CBC quarantine. |
| `references/creative-search.md` | 1–117 | Entire file classified as normative workflow advice; delegation is expressly conditional on authorization and independence. No completeness/optimality theorem is claimed. |
| `references/h-technique.md` | 1–162 | 1–50 endpoint shapes/variants; 52–71 normative selection and verified sibling boundary; 73–105 quantifier/compression facts; 107–123 tactic/status facts; 125–162 proof plan and checked Lean snippet. |
| `references/reshape-and-exact.md` | 1–192 | 1–77 exactness/DPI guidance; 79–120 coupling, representative, and primary winnability claims; 122–142 checked build boundary and signed-joint terminology; 144–179 exact orientation/metric signatures; 181–192 checked build-status discipline. |
| `references/sketch-and-plan.md` | 1–161 | Entire file read; mathematical statements are limited to route summaries already checked elsewhere, and the remaining content is explicitly normative planning/search advice. |
| `agents/openai.yaml` | 1–4 | Complete YAML/UI consistency check. |

Total audited release surface: **1,182 lines**.

## Frozen hashes

### Final package hashes

```text
13e8c3e354c53224acaf078ff3d6cfb1d49d28ef86cfb94ca0005e6548c652f4  SKILL.md
726ff1ac7c72da67162b0b5e0e2c90d8afb23c305f4a44b4c058f20fab66aea9  references/conditional-equivalence.md
32cb22ad7b078ac886105670f91202603463e0d6b1660c7a5dd4cf9e624d76db  references/counting.md
6d71c6aa3ef1797d054b2dced348630e4e3c6fd35778f6e8da0991e45eb2341e  references/creative-search.md
6cf1b96c9d42ae60d3e55ea564d52f416d1431fd1b79e771d747ae434d6bdb6d  references/h-technique.md
a334bb31f3855892f74d1a0eb4da402328b8c828c1b419d1605767a754e93f10  references/reshape-and-exact.md
c833cf687a05ae9e2b05065d6e2ce9578d8907b615fbe21530983f533a70a019  references/sketch-and-plan.md
bad0bebb58f9cbe877b09bf9689dc87d247fca2d66de6f51e2436417f2687db2  agents/openai.yaml
```

### Rendered primary PDFs

```text
b013c98a7e98de2e7def22107ccf47e2c707f6f01f6b0397afa1bc9e3090de07  papers/CR18_LN.pdf
a4bd49c246428fb96ee394b4bafda139928bb5a26a52f5de833ae1545a32c6df  papers/MaPiRe07.pdf
f414b964164a3c975b6b22fbc8178105ae53f0848cd22debbbf0c2c162007ebe  papers/LanMau20.pdf
0a566d2364adddb6894ca403dbe1b3eed3b62de04455fdddf37a5597bc324b45  papers/thesis (1).pdf
```

### Repository contracts

```text
e98c97ee04aa08463a322e344e36ce7df007e11f8b3a5053a8a1c4e1c3fa35f8  DESIGN.md
480ff0ac8ed717003751bc5946c77ecb5607250abcefd917953513a514e8d5e0  STATUS.md
b17598e84e99962c3066d8f6368d0804b337dabcbcc7ee18ec27145f1f6ecc6a  FOUNDATIONS.md
66ec89e78439dba475fc75ffbdac178a736876ca71af0f5be87eae590bc7da3e  CHEATSHEET.md
```

### Principal Lean evidence sources

```text
6b5f7c808454063953917c5cdbbf43a0a4351bb1a0062c7769b80781716fb418  RandomSystems/CondEquiv.lean
bc84fdfeb2c80ec0083025e61d859ffacb1e7ed78c64f1c7c94a07aa6dbc504e  RandomSystems/HTechnique/Derivation.lean
cb4be413c173a60f8735da52c8b78dd8c7fab71af1b1f426fddd195217211d15  RandomSystems/HTechnique/Tactics.lean
6e7f20e3de40d27f50c2c88a73bb6d531e2f00c0451d0819cdf4b2f3aa2f9d29  RandomSystems/HTechnique/SoP/VisibleLaw.lean
fba5eb5715bd5f43f01a4652c1981c014bf9682a9c7eb2f233a7e760e5147c2a  RandomSystems/SwitchingLemma.lean
34b8cacbe0038f8b5a38ec7249c914719fc6d54cbdb3b7c7a0ac4ef983212a90  RandomSystems/StatDist.lean
5e6cc085fdd042db6866646e6115b4e97f059867b0ffff2bee342289a5969bc3  RandomSystems/RandomSystemCoupling.lean
bf3351140b0c104236ab649e2813b0e5e8426a1355d0c1cfe2fccaadeebb36ee  RandomSystems/RandomSystem.lean
90bac665168a404c3587906cd6f0e22b2d358c9d1845054161813d4604da3b83  RandomSystems/StrictContextAdvantage.lean
6252cd15ea7950b20ab3342eb4144c3c0be48d9cd3095c9a74d81886d5e4266f  RandomSystems/StrictContextSharedDomain.lean
65a0c372bf61072ac1729ddabf9cd5fd5a11b1230aaa4f725c654ccc908e7e3d  RandomSystems/QueryCompression.lean
edc1b93bc1576e662f8d9ce80f7beb66f1c9c21830d3780bb805ab8179227418  RandomSystems/CBCStructureGraph.lean
e49ac4f2708d6e350b0c5f6604bb60de5f31c4247429e4b52822d0281bbfad7e  RandomSystems/CBCMAC.lean
5398f1a251ec43b16254de18da2ef76fe2077a53ead29dfe8479da456f7600b4  RandomSystems/GameWinnability.lean
287bfd45cabf022ee3dc17d4da7bfc0df889c1a7c4ab4d7463bf66eaea2d311f  RandomSystems/LanzenbergerChain.lean
1757317d1a4722de7cacdf01d3230bfcdb6254d115f4e4640f244464a01ca11b  RandomSystems/MultiSystemCoupling.lean
9c77557055ed381785097a7f67db7abc33d35928bf04d1003fdc171bd63da71a  RandomSystems/GameOf.lean
a4b16efc8bae767dce6e286cf7c0b70d7fcba1a631a6085cc0d10cfa17dbff6b  RandomSystems/BlindConverter.lean
a33efa9119205cc4719f5ab57240a12f033e8a5643ab4f2afe4ff0cb202470d8  RandomSystems/BlindAbsorption.lean
c2bea27af5e7bed49d81ed4c118833ced9c67e7caeced666e41a18f580d8f968  RandomSystems/HistoryConditionC.lean
c76af8579d4ef92c79b41397f0b38f081a9b5b59acac3e023084cdfa2c5465a1  RandomSystems/Coupling.lean
64d08399b04b515ae3b2a945397cb9627e46a7677acbfbf13425213ddc4ca4e2  RandomSystems/Distinguishing.lean
23028d450a7c4a485ae3ec3ce1ac9edc929a0223931e9a7cb04afc8df40bd466  RandomSystems/AbsorbDPI.lean
77d21fc805cec2ffcc889e115a5c9bf78cb6cd229d5913f63bca9a1b06c1d0e9  RandomSystems/CompatibleMetric.lean
```

## Final receipt

The final package keeps mathematical claims, Lean-surface claims, and workflow
advice distinct; its theorem names and hypotheses match the current
declarations; cited mathematical interpretations match rendered primary pages;
time-sensitive failures are explicitly snapshot-sensitive; all links and UI
metadata validate; and no unsupported selector, coupling, CE-completeness, or
generic-compression claim remains. **Release approved at the recorded hashes.**
