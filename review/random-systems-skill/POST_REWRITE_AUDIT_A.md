# Post-rewrite release audit A: `random-systems-proofs`

Audit date: 2026-08-06.  Package root:
`/Users/marcilunga/.codex/skills/random-systems-proofs`.

## Release verdict

**BLOCKED on two packaging corrections.**  I found no incorrect Lean theorem
signature, inequality orientation, primary-source formula, or current
quarantine direction in the seven Markdown files.  The two blockers are the
frontmatter's still-overbroad whole-`RandomSystemsCC`/indifferentiability trigger
and the provisional “being rewritten” notice, which cannot remain a release
status.  Six additional findings are nonblocking precision, reproducibility,
or progressive-disclosure improvements.

The current package is a substantial reliability improvement over the frozen
pre-rewrite version: the closed technique taxonomy, “every security theorem,”
tactic-completeness implications, fixed-schedule H claims, unconditional metric
claims, and absolute first-hit/generalize-in-place rules are gone.  The
remaining universal quantifiers are either exact endpoint quantifiers or
explicitly labelled workflow rules.

## Severity and release effect

- **HIGH / BLOCKING** — correct before release or before replacing the audit
  notice with a release status.
- **MEDIUM / NONBLOCKING** — current safety direction is sound, but the wording
  is not reproducible or can go stale.
- **LOW / NONBLOCKING** — exactness or usability improvement; no present
  mathematical unsoundness.

## Frozen release-target hashes

These hashes were re-read after the two explicitly reported late corrections
to `reshape-and-exact.md` and `agents/openai.yaml`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `SKILL.md` | 212 | `38d42930bc9eba19ee6204069c96f6c78e4159f344580de518b7f7fe9cad4d43` |
| `agents/openai.yaml` | 4 | `f39b5dddb3b8a16f090890e6823901868dd38e1c4cafa5cdc2bced3f78ae1105` |
| `references/conditional-equivalence.md` | 197 | `72b37ec61fefc80c209e856b9c1fd7c40ce4414aeb05375fe34e1c61f12fdd04` |
| `references/counting.md` | 134 | `a044e39fefce65d1c8b0efcab60194587d9cf60a3d1f85840ee1d9d4caebce12` |
| `references/creative-search.md` | 117 | `6d71c6aa3ef1797d054b2dced348630e4e3c6fd35778f6e8da0991e45eb2341e` |
| `references/h-technique.md` | 154 | `035cc360c02cae09b4d004cc0fb8bda43ab392602cdd077da119bc4cf018196a` |
| `references/reshape-and-exact.md` | 187 | `c61076d43c9a4402ea1b6b4b25a4a93b8ae4752912b413b2bbf6996153fe24f4` |
| `references/sketch-and-plan.md` | 161 | `c833cf687a05ae9e2b05065d6e2ce9578d8907b615fbe21530983f533a70a019` |

Lean evidence was checked in the current dirty repository working tree at
`HEAD` `96e42831e51857aefa8d9e40e996061600061866`; the audit does not pretend that
`HEAD` alone identifies the working-tree state.  Before this report was added,
`git status --short` already reported 149 paths.

## Atomic findings

### A-001 — frontmatter still over-promises the CC layer

- **Location:** `SKILL.md:3`; consistency consequence at
  `agents/openai.yaml:2-4`.
- **Severity / effect:** **HIGH / BLOCKING**.
- **Claim:** the skill is to be used to formalize, finish, repair, or review
  `RandomSystemsCC` security proofs, including indifferentiability theorems.
- **Evidence:** the body and six references route Random Systems distance/game
  leaves.  They do not route CC construction assembly, AC/resource lifting,
  multi-interface contextual composition, or `Indifferentiable.construct`.
  `RandomSystemsCC/Symmetric/SpongeIndifferentiability.lean` is a direct risk
  witness: its current source contains three admissions at lines 1026, 1041,
  and 1073, yet no package reference identifies that surface or its status.
  The tightened UI metadata now says only “Random Systems,” so the two public
  scope descriptions also disagree.
- **Reasoning:** using the skill for an RS leaf inside a CC theorem is valid;
  promising the whole CC/indifferentiability proof is not.  This is the only
  surviving form of the old overbroad applicability claim.
- **Exact corrective text (frontmatter):**

  ```yaml
  description: "Formalize, finish, repair, or review Random Systems advantage and distance proofs in Lean 4, including Random Systems proof leaves used inside RandomSystemsCC. Use for PRF/PRP/MAC bounds and the RS leaves of indifferentiability arguments that use H-technique, strict conditional equivalence, coupling, winnability, exact reshaping, or counting. Do not use as the sole workflow for CC composition, AC/resource lifting, or full multi-interface indifferentiability assembly. Routes the task to current declarations and requires primary-source, signature, build, and axiom checks."
  ```

  Add after the reliability paragraph:

  > This workflow routes Random Systems obligations. It may be used for an RS
  > leaf inside `RandomSystemsCC`, but it does not route CC composition,
  > AC/resource lifting, or full multi-interface indifferentiability assembly.

### A-002 — provisional audit status is not releasable metadata

- **Location:** `SKILL.md:8-14`.
- **Severity / effect:** **HIGH / BLOCKING**.
- **Claim:** the package “is being rewritten” and awaits a release receipt.
- **Evidence:** all seven Markdown files are now declared stable and this is the
  requested post-rewrite release audit.  Keeping the sentence after release
  makes the package permanently provisional and gives no stable criterion for
  removing it.
- **Reasoning:** the verification rule is valuable; the transient project-state
  assertion is not.
- **Exact corrective text:** replace lines 8-14 with:

  > **Reliability rule.** This package is a workflow and navigation aid, not a
  > mathematical source. Verify source claims on rendered primary pages and
  > library claims against current signatures, focused builds, and axiom
  > receipts.

### A-003 — volatile status paragraphs have no identifiable repository snapshot

- **Location:** `conditional-equivalence.md:182-185`;
  `counting.md:132-134`; `h-technique.md:119-121`;
  `reshape-and-exact.md:121-124,180-187`.
- **Severity / effect:** **MEDIUM / NONBLOCKING**.
- **Claim:** several routes are described as incomplete “in the audited
  snapshot,” but no date, source hash, or command receipt identifies that
  snapshot.
- **Evidence:** the claims are correct today: `CBCStructureGraph.lean` fails a
  focused check and has a `sorry`; `HTechnique/Tactics.lean` is blocked by
  failing `SoP/VisibleLaw.lean`; `GameWinnability.lean` fails and contains an
  admission; `LanzenbergerChain.lean` is blocked on its missing olean; legacy
  amplification contains a `sorry`.  They are nevertheless volatile repository
  state, not facts fixed by the package hashes above.
- **Reasoning:** “audited snapshot” without an identifier looks reproducible but
  is not.  The safety warning is conservative, so this need not block release.
- **Exact corrective text:** use this timeless form at each status boundary:

  > This route is snapshot-sensitive. Before using it, consult the current
  > `STATUS.md`, run `lake env lean <file>`, and obtain a clean
  > `#print axioms` receipt after the file elaborates.

  If retaining a dated observation, prefix it with “Rechecked 2026-08-06 in the
  working tree used by the post-rewrite audit” rather than “the audited
  snapshot.”

### A-004 — `#print axioms` is described as an existing receipt for files that do not elaborate

- **Location:** `reshape-and-exact.md:185-187`.
- **Severity / effect:** **MEDIUM / NONBLOCKING**.
- **Claim:** `#print axioms` exposes `sorryAx` for the current amplification and
  CBC structure-graph headlines.
- **Evidence:** `RandomSystems/Legacy/Amplification.lean` currently stops on a
  missing `Legacy/Equiv.olean`; `CBCStructureGraph.lean` currently has multiple
  elaboration errors.  Neither path presently yields a reproducible imported
  headline for an external `#print axioms`.  The stronger available evidence is
  direct: each source contains an admission, and the structure-graph headline
  syntactically depends on its admitted mass theorem.
- **Reasoning:** the conclusion “do not call these complete” is correct, but the
  stated receipt is not currently obtainable.
- **Exact corrective text:**

  > The legacy amplification source and CBC structure-graph source currently
  > contain admissions, and their focused paths are not clean. Do not present
  > either headline as complete; first require a successful focused build and
  > then obtain its `#print axioms` receipt.

### A-005 — winnability source paraphrase should name the two quantities

- **Location:** `reshape-and-exact.md:113-116`.
- **Severity / effect:** **LOW / NONBLOCKING**.
- **Claim:** the thesis theorem “identifies winnability with its optimal form.”
- **Evidence:** rendered thesis p. 24, Theorem 2.37, says precisely
  `ν(S^A) = ω(S^A)` and provides a representative attaining the infimum
  winnability.  The present paraphrase is directionally right but hides the
  supremum-versus-infimum distinction that the surrounding package otherwise
  insists on preserving.
- **Exact corrective text:**

  > Thesis Theorem 2.37 proves that the supremum winning probability
  > `ν(S^A)` equals the infimum winnability `ω(S^A)`, and gives an equivalent
  > representative whose probability of being winnable attains `ω(S^A)`.

### A-006 — the H application snippet omits its notation/precondition context

- **Location:** `h-technique.md:139-147`.
- **Severity / effect:** **LOW / NONBLOCKING**.
- **Claim:** the displayed application is presented as the visible top-level
  shape.
- **Evidence:** the endpoint and argument order are correct, but the notation
  comes from the `RandomSystems.CR18` scope and the endpoint also has an
  inferred `FiniteTranscriptSpace` premise.  A user pasting the fragment into a
  fresh file can fail before reaching the advertised obligations.
- **Exact corrective text:** replace the lead-in with:

  > With `open scoped RandomSystems.CR18` and the endpoint's transcript-space
  > and totality premises in scope, a schematic top-level application is:

### A-007 — UI default prompt uses an ambiguous singular “current source”

- **Location:** `agents/openai.yaml:4`.
- **Severity / effect:** **LOW / NONBLOCKING**.
- **Claim:** the default prompt asks for formalization “against the current
  source.”
- **Evidence:** package policy distinguishes current Lean declarations from a
  rendered primary source; the singular phrase does not say which authority is
  meant.  The YAML is otherwise valid and the `$random-systems-proofs` token
  matches frontmatter.
- **Exact corrective text:**

  ```yaml
  default_prompt: "Use $random-systems-proofs to plan and formalize this Random Systems security proof against the current Lean declarations and the applicable rendered primary source."
  ```

### A-008 — volatile CBC structure-graph status is repeated across three routes

- **Location:** `conditional-equivalence.md:182-185`;
  `counting.md:132-134`; `reshape-and-exact.md:185-187`.
- **Severity / effect:** **LOW / NONBLOCKING**.
- **Issue:** the same moving quarantine fact is maintained independently in a
  CE library map, the counting reference, and the general reshape reference.
- **Evidence:** compression, orientation, and axiom reminders are deliberate
  safety-critical repetition.  The CBC status is different: it is a single
  volatile implementation fact, and the three versions already use different
  evidence wording.
- **Exact corrective text:** keep the detailed warning only in `counting.md`.
  In `conditional-equivalence.md`, use:

  > For the optional CBC structure-graph counting route, see
  > [counting.md](counting.md) and recheck its current build and axiom status.

  In `reshape-and-exact.md`, use the generic snapshot-sensitive status text
  from A-003.

## Verified factual-claim ledger

Each row is a fresh check of the current rewrite, not an inherited verdict from
either blind audit.

| ID | File lines | Atomic claim | Verdict and evidence |
| --- | --- | --- | --- |
| V-001 | `SKILL.md:143-145` | The named tactics attempt registered shapes and are not complete procedures. | **VERIFIED.** `CR18TacticsCore.lean`, `CR18Tactics.lean`, `TotalityTactics.lean`, and `HTechnique/Tactics.lean` define finite `simp`/`first` portfolios. |
| V-002 | `SKILL.md:157-161` | `htechnique_compress` is a narrow SoP rewrite; `compressedQuery_bound` is numerical, not semantic compression. | **VERIFIED.** `HTechnique/Tactics.lean:42-51`; `QueryCompression.lean:116-119`; exact compression is a separate theorem at `:150`. |
| V-003 | `SKILL.md:176-181` | `transcriptDist` is a pushforward; post-hoc observation refinement can use DPI, unlike interactive leakage. | **VERIFIED.** `RandomSystem.lean:501-527` and `δ_fTransform_le` at `:164`; the interactive qualification is mathematically necessary. |
| V-004 | `SKILL.md:182-184` | `Adv S T = Delta(T,S)` under the named nonnegativity hypotheses and is orientation-sensitive at unequal weight. | **VERIFIED.** `RandomSystem.lean:1800-1824`; focused `#check` prints the two `NonNeg` premises and swapped arguments. |
| V-005 | `SKILL.md:185-189` | Strict `maxEDist ≤ ofReal maxAdvantage` requires normalized laws; equality additionally needs one common fixed domain. | **VERIFIED.** `StrictContextAdvantage.lean:403-409`; `StrictContextSharedDomain.lean:934-945`; both focused files elaborate. |
| V-006 | `SKILL.md:190-192` | A raw maximal coupling of fixed laws does not itself select equivalent interactive representatives. | **VERIFIED.** `optimal_probability_coupling_exists` has only two fixed `PFunPDS.Prob` inputs; representative attainment is a separate theorem. |
| V-007 | `conditional-equivalence.md:20-29` | CR18 Def. 4.19 is one enhanced source versus one ordinary target; Thm. 4.17 gives the blind-game bound. | **VERIFIED.** Visually checked `CR18_LN.pdf` PDF pp. 60-61 (printed pp. 107-110). |
| V-008 | `conditional-equivalence.md:31-46` | Lean `CondEquiv` is the displayed guarded, cross-multiplied equality and is exact. | **VERIFIED.** `CondEquiv.lean:118-123`; focused `#check RandomSystems.CR18.CondEquiv.CondEquiv`. |
| V-009 | `conditional-equivalence.md:54-59` | MPR07 Lemma 5 constructs two enhanced systems with equal pre-winning behavior and exact winner/transcript-distance identities. | **VERIFIED.** Visually checked `MaPiRe07.pdf` PDF pp. 11-12 (printed pp. 140-141), especially Lemma 5 (i)-(iv). |
| V-010 | `conditional-equivalence.md:63-67` | The thesis uses transcript-law classes and honest couplings in its finite/common-domain setting. | **VERIFIED.** Visually checked thesis Defs. 2.14, 2.17 and Thms. 2.31-2.32; Lean's `DistCoupling` has an explicit `nonneg` field. |
| V-011 | `conditional-equivalence.md:103-130` | The seeded CE endpoint has exactly the displayed obligations and lives in `SwitchingLemma.lean`; history and generic alternatives exist. | **VERIFIED.** `SwitchingLemma.lean:1891-1913`; `HistoryConditionC.lean:450-479`; `GameOf.lean:1100ff`; all three focused application files checked where imported. |
| V-012 | `conditional-equivalence.md:134-143` | Absorption yields a blind winner; each blind winner has its own fixed list of length at most `q`, not one universal list. | **VERIFIED.** `BlindAbsorption.lean:124-189`; `SwitchingLemma.lean:815-820`; endpoint quantifies over every `w`. |
| V-013 | `conditional-equivalence.md:169-185` | The listed CE modules exist; `CBCMAC` is a completed CE application; `CBCStructureGraph` is not clean or admission-free. | **VERIFIED.** `CBCMAC.lean` focused check succeeds and its headline axiom set is only `propext`, `Classical.choice`, `Quot.sound`; `CBCStructureGraph.lean` fails and line 1428 is `sorry`. |
| V-014 | `counting.md:31-60` | `probBad_iUnion_le` and `mass_biUnion_le` have the displayed signatures and nonnegativity/carrier premises. | **VERIFIED.** `StatDist.lean:467-479`; `SwitchingLemma.lean:55-60`; focused `#check` output matches. |
| V-015 | `counting.md:66-69` | `probBad_le_of_ratio` needs two nonnegative weight-one laws, zero ideal bad mass, and the one-sided pointwise ratio. | **VERIFIED.** `HTechnique/Derivation.lean:3849-3877`; exact `#check` receipt. |
| V-016 | `counting.md:73-84` | Seeded CE uses every blind fixed list; ordinary H uses every adaptive `QQueryEnvironment`; coupling retains its joint-law scope. | **VERIFIED.** The three current signatures expose exactly these distinct quantifiers. |
| V-017 | `counting.md:99-108` | `pairCollisionUnionBound_le_birthday` proves the stated `1/2 * r^2 / card(X)` bound only for its named expression. | **VERIFIED.** `SwitchingLemma.lean:1705-1719`; focused `#check` prints the same expression. |
| V-018 | `h-technique.md:17-50` | Equality, ratio, expectation, partition, extended, and selected filtered endpoints exist with the stated orientation/scope. | **VERIFIED.** `Derivation.lean:398-565,732-836,1957-2352`; the file focused-compiles. |
| V-019 | `h-technique.md:69-71` | The sibling `ccprover` has selector and proof-spine tooling, not declarations in this repo. | **VERIFIED.** Sibling `CCProver/Surface/Techniques.lean:206` defines the selector; `CCProver/RS/Teaching/OrdinaryH.lean` contains the spines. |
| V-020 | `h-technique.md:75-88` | Ordinary H retains a uniform adaptive-environment bad-mass premise; it does not receive a blind fixed schedule. | **VERIFIED.** Exact H signatures at `Derivation.lean:398-447`; contrast with seeded CE at `SwitchingLemma.lean:1891-1913`. |
| V-021 | `h-technique.md:96-121` | The named compression results/tactics have the stated narrow scope; the aggregate tactic module is currently blocked by an SoP migration file. | **VERIFIED.** `QueryCompression.lean`; `HTechnique/Tactics.lean`; focused `VisibleLaw.lean` check fails on the signed-`Real` migration and admissions, and `Tactics.lean` cannot import its olean. |
| V-022 | `reshape-and-exact.md:29-36` | `compressedQuery_bound` is not exact compression; the exact evaluator theorem is named correctly; thesis nonadaptive sufficiency is equivalence-only. | **VERIFIED.** `QueryCompression.lean:116,150`; visually checked thesis Lemma 2.18 on PDF p. 26 (printed p. 16). |
| V-023 | `reshape-and-exact.md:40-77` | Current triangle, DPI, filtering/parallel, and disjoint-support tools exist, with varying side conditions; transcript observation DPI needs factorization. | **VERIFIED.** Representative declarations include `maxAdvantage_triangle`, `δ_fTransform_le`, `maxAdvantage_filterQueries_le`, strict parallel inequalities, and `δ_sum_of_disjoint_support`. |
| V-024 | `reshape-and-exact.md:81-104` | `DistCoupling` is honest/nonnegative; `coupling_bound` and the fully qualified optimal normalized coupling theorem have the described conclusions and limitations. | **VERIFIED.** `Coupling.lean:45-52,149`; `RandomSystemCoupling.lean:48-67`; the corrected namespace passes focused `#check`. |
| V-025 | `reshape-and-exact.md:108-124` | Representative attainment is distinct from CE; thesis winnability gives equality plus an attaining representative; current wrappers are blocked/admitted. | **VERIFIED WITH WORDING IMPROVEMENT A-005.** Visually checked thesis Thms. 2.31-2.32 and 2.37; focused `GameWinnability.lean` and `LanzenbergerChain.lean` checks confirm quarantine. |
| V-026 | `reshape-and-exact.md:128-139` | A signed/virtual joint is not an honest coupling and cannot satisfy `DistCoupling` merely by terminology. | **VERIFIED.** Current `Dist` is signed, while `DistCoupling.nonneg` is an explicit field; the distinction matches the repository's signed-extension policy and the positive thesis model. |
| V-027 | `reshape-and-exact.md:143-176` | Orientation and both strict-metric signatures are displayed correctly, including normalization and shared-domain hypotheses. | **VERIFIED.** Focused `#check` output matches all arguments and conclusions. |
| V-028 | `reshape-and-exact.md:180-187` | Legacy amplification, winnability/representative, and CBC structure-graph surfaces are currently unsafe as completed endpoints. | **VERIFIED, subject to evidence wording A-003/A-004.** Direct focused checks and source admissions provide the receipt. |
| V-029 | `sketch-and-plan.md:83-85` and `SKILL.md:48-51` | Extraction may navigate a PDF but rendered-page verification is required. | **VERIFIED.** The scanned thesis has no useful text layer, while CR18 and MaPiRe have searchable layers; all cited pages above were visually inspected. |
| V-030 | Package links/metadata | All internal Markdown files and ToC anchors resolve; frontmatter and UI YAML parse; the UI token matches the skill name. | **VERIFIED.** Mechanical link/anchor and Ruby YAML checks pass. Scope consistency remains A-001. |

## Build and axiom receipts

Successful focused checks:

- `lake env lean RandomSystems/CBCMAC.lean`;
- `lake env lean RandomSystems/HistoryConditionC.lean`;
- `lake env lean RandomSystems/HTechnique/Derivation.lean`;
- `lake env lean RandomSystems/SwitchingLemma.lean`;
- `lake env lean RandomSystems/RandomSystemCoupling.lean`;
- `lake env lean RandomSystems/StrictContextSharedDomain.lean`;
- a temporary scratch import containing every named `#check` above and the
  headline `#print axioms` commands.

The following checked headlines depend only on `propext`,
`Classical.choice`, and `Quot.sound`:

- `maxAdvantage_filterQueries_seededConditionCGame_le`;
- `HTechniqueDerivation.adv_le_of_fixedQuery_eq_on_good`;
- `optimal_probability_coupling_exists`;
- `cbc_mac_randomness_expander`;
- `maxEDist_filterQueries_cbcReal_Vn_eq_ofReal_maxAdvantage`.

Current negative receipts:

- `HTechnique/SoP/VisibleLaw.lean` fails and contains admissions;
- `HTechnique/Tactics.lean` cannot import the missing `VisibleLaw.olean`;
- `CBCStructureGraph.lean` fails at multiple lines and warns on its admitted
  `mass_cbcGraphBad_le`;
- `GameWinnability.lean` fails throughout the signed migration and warns on an
  admission;
- `LanzenbergerChain.lean` cannot import `GameWinnability.olean`;
- `Legacy/Amplification.lean` cannot import `Legacy/Equiv.olean` and its source
  contains a `sorry`;
- `RandomSystemsCC/Symmetric/SpongeIndifferentiability.lean` elaborates with
  three `sorry` warnings.

Relevant volatile source hashes:

| Lean file | SHA-256 |
| --- | --- |
| `RandomSystems/HTechnique/SoP/VisibleLaw.lean` | `6e7f20e3de40d27f50c2c88a73bb6d531e2f00c0451d0819cdf4b2f3aa2f9d29` |
| `RandomSystems/HTechnique/Tactics.lean` | `cb4be413c173a60f8735da52c8b78dd8c7fab71af1b1f426fddd195217211d15` |
| `RandomSystems/CBCMAC.lean` | `e49ac4f2708d6e350b0c5f6604bb60de5f31c4247429e4b52822d0281bbfad7e` |
| `RandomSystems/CBCStructureGraph.lean` | `edc1b93bc1576e662f8d9ce80f7beb66f1c9c21830d3780bb805ab8179227418` |
| `RandomSystems/GameWinnability.lean` | `5398f1a251ec43b16254de18da2ef76fe2077a53ead29dfe8479da456f7600b4` |
| `RandomSystems/LanzenbergerChain.lean` | `287bfd45cabf022ee3dc17d4da7bfc0df889c1a7c4ab4d7463bf66eaea2d311f` |
| `RandomSystems/Legacy/Amplification.lean` | `43fa6ed4a92a3841963ed843e9bedf330bc25930730488bbab339e0b537fe7af` |
| `RandomSystemsCC/Symmetric/SpongeIndifferentiability.lean` | `0a766bf0bdedc2f98f038cc19375ba47a39121527656045707ccb03bd178b89b` |

## Primary-source receipts

I used extraction only for navigation and inspected the rendered pages.

- `papers/CR18_LN.pdf`: PDF p. 42 (printed p. 71), Def. 3.22; PDF
  pp. 60-62 (printed pp. 107-112), Defs. 4.18-4.20, Thm. 4.17, and
  Lemmas 4.18-4.19.
- `papers/MaPiRe07.pdf`: PDF pp. 11-12 (printed pp. 140-141), Def. 12 and
  Lemma 5 with its proof.
- `papers/thesis (1).pdf`: PDF pp. 24-31 and 34 (printed pp. 14-21 and 24),
  including Defs. 2.12, 2.14, 2.17, 2.26; Lemma 2.18; and Thms. 2.31,
  2.32, 2.37.

## Progressive disclosure, duplication, and UI review

| Check | Result |
| --- | --- |
| Main-file routing | **PASS.** `SKILL.md` gives a non-exhaustive route table and says to read only the relevant reference. |
| Reference separation | **PASS.** CE, H, counting, reshape, exploration, and planning are separated by mathematical purpose. |
| Safety-critical repetition | **PASS.** Orientation, compression, and axiom cautions are repeated where a user can otherwise make a local unsound move. |
| Volatile-status duplication | **IMPROVE.** A-008; centralize the CBC structure-graph status. |
| Internal links and anchors | **PASS.** Every Markdown target and ToC anchor resolves. |
| Referenced repo files | **PASS.** All backticked `.lean`/`.md` paths or basenames resolve. |
| Frontmatter syntax | **PASS.** Valid YAML, correct `name`, one description scalar. |
| UI YAML syntax | **PASS.** Valid `interface` map; display name and invocation token agree with frontmatter. |
| UI/package scope | **BLOCKED.** A-001; frontmatter says whole CC/indifferentiability while UI and body say RS. |
| Release-status metadata | **BLOCKED.** A-002. |
| Old absolute language | **PASS.** Remaining `every`/`only`/`must` uses are exact quantifiers, explicitly scoped advice, or cautions against completeness. |

## Full line-coverage receipt

Every line of every release-target file is covered below. “Normative” means the
text is process/style guidance rather than a falsifiable Lean/source claim;
those ranges were checked for internal consistency and surviving unsafe
absolutes.

| File | Inclusive lines | Classification and receipt |
| --- | --- | --- |
| `SKILL.md` | 1-4 | Metadata; YAML valid; scope defect A-001. |
|  | 5-7 | Heading/structure. |
|  | 8-14 | Reliability/status; release defect A-002. |
|  | 15-27 | Normative repository contract; consistent with `AGENTS.md`. |
|  | 28-52 | Evidence/terminology policy; source-model distinctions checked by V-007, V-009, V-010, V-026. |
|  | 53-67 | Explicitly non-exhaustive routing advice; no completeness claim. |
|  | 68-93 | Endpoint-selection advice and six valid internal links. |
|  | 94-124 | Normative ledger/search policy; no first-hit or unconditional-generalization rule survives. |
|  | 125-140 | Development loop and admission gate; matches `AGENTS.md`. |
|  | 141-162 | Automation/compression facts; V-001, V-002. |
|  | 163-173 | Explicit readability policy, not a soundness claim. |
|  | 174-196 | Modeling facts and quarantine discipline; V-003-V-006. |
|  | 197-212 | Normative completion receipts; transitive-axiom warning verified. |
| `references/conditional-equivalence.md` | 1-17 | Scope and valid ToC anchors. |
|  | 18-47 | CR18 and Lean strict-CE claims; V-007, V-008. |
|  | 48-75 | MPR, representative/coupling, H/winnability distinctions; V-009, V-010. |
|  | 76-100 | Monitor/simulator design consequences; logically sound scoped advice. |
|  | 101-131 | Seeded endpoint and alternative surfaces; V-011. |
|  | 132-144 | Blindness/fixed-list quantifiers; V-012. |
|  | 145-166 | Obligation-planning advice; ignore-MBO lemmas verified by source search. |
|  | 167-186 | Library map/status; V-013 and A-003/A-008. |
|  | 187-197 | Normative review checklist. |
| `references/counting.md` | 1-14 | Scope and valid ToC anchors. |
|  | 15-28 | Normative law/event inventory; listed possible goal forms exist. |
|  | 29-70 | Union and ratio theorem facts; V-014, V-015. |
|  | 71-85 | Schedule-scope facts; V-016. |
|  | 86-119 | Loss-control advice and birthday theorem; V-017. |
|  | 120-134 | Normative verification plus CBC status; V-013, A-003/A-008. |
| `references/creative-search.md` | 1-14 | Explicit advice scope and valid ToC anchors. |
|  | 15-27 | Delegation policy; correctly conditioned on authorization/independence. |
|  | 28-45 | Snapshot/evidence policy; consistent with this audit. |
|  | 46-65 | Candidate-route advice; explicitly says categories overlap. |
|  | 66-82 | Independence and probe policy; normative. |
|  | 83-104 | Proposal evaluation; normative, no completeness promise. |
|  | 105-117 | Lean handoff policy; normative. |
| `references/h-technique.md` | 1-14 | Scope and valid ToC anchors. |
|  | 15-51 | Endpoint signatures/variants; V-018. |
|  | 52-72 | Candidate selection and sibling tooling; V-019. |
|  | 73-89 | Adaptive quantifier facts; V-020. |
|  | 90-106 | Compression facts; V-002, V-021. |
|  | 107-122 | Tactic limits and current status; V-001, V-021, A-003. |
|  | 123-154 | Schematic proof plan and final gate; A-006 is the only usability issue. |
| `references/reshape-and-exact.md` | 1-17 | Scope and valid ToC anchors. |
|  | 18-37 | Exact/compression/nonadaptive claims; V-022. |
|  | 38-62 | Hybrid/additivity advice and declaration-surface claim; V-023. |
|  | 63-78 | Observation-refinement claims; V-003, V-023. |
|  | 79-105 | Honest/maximal coupling claims; V-024. |
|  | 106-125 | Representatives/winnability/status; V-025, A-003, A-005. |
|  | 126-140 | Signed-expansion distinction; V-026. |
|  | 141-177 | Orientation and strict metric signatures; V-004, V-005, V-027. |
|  | 178-187 | Build-status discipline; V-028, A-003, A-004, A-008. |
| `references/sketch-and-plan.md` | 1-14 | Explicit recommendation scope and valid ToC anchors. |
|  | 15-28 | New-result versus repair starting policy; normative and internally consistent. |
|  | 29-66 | Sketch template; normative, permits provisional asymptotics and open claims. |
|  | 67-86 | Adaptation/PDF guidance; V-029. |
|  | 87-122 | Ledger and explicitly non-complete obligation examples; current endpoint shapes checked by V-011, V-016, V-018, V-024. |
|  | 123-143 | Reuse-search policy; rejects first-hit and unconditional in-place generalization. |
|  | 144-161 | Focused endpoint probe; command tested and mismatch causes are non-exhaustive. |
| `agents/openai.yaml` | 1-4 | YAML/UI metadata; valid and token-consistent, with A-001/A-007. |

## Required release action

1. Apply A-001 and A-002.
2. Re-run the metadata/link/hash checks after those edits.
3. Keep A-003 through A-008 as nonblocking follow-up improvements, or apply
   them before sealing the final hash set.
4. Do not change the verified theorem/source statements except for the exact
   precision edits above.

## Post-correction delta receipt

Delta audit date: 2026-08-06.  This receipt supersedes the blocked release
verdict and required-release-action section above for the corrected package.

**RELEASE-CLEAR FOR AUDIT A.**  Both blockers and all six nonblocking findings
are closed.  The six changed package files were re-read in full (904 lines),
the two unchanged references remain byte-identical to the frozen target, and
the complete corrected package contains 1,182 lines.  No new unsupported
mathematical, Lean-surface, or repository-status claim was introduced.

### Correction closures

| Finding | Corrected location | Delta verdict and receipt |
| --- | --- | --- |
| A-001 | `SKILL.md:3,13-15` | **CLOSED.**  The frontmatter now promises Random Systems proofs and RS leaves inside `RandomSystemsCC`, explicitly excludes sole-workflow use for CC composition, AC/resource lifting, and full multi-interface assembly, and repeats that boundary in the body.  This matches the UI's Random Systems scope. |
| A-002 | `SKILL.md:8-11` | **CLOSED.**  The transient “being rewritten” state is gone.  The retained reliability rule describes a stable source/signature/build/axiom verification policy. |
| A-003 | `conditional-equivalence.md:182-183`; `counting.md:132-138`; `h-technique.md:119-123`; `reshape-and-exact.md:122-127,183-192` | **CLOSED.**  Moving repository observations are either centralized by reference or explicitly dated “Rechecked 2026-08-06 in the working tree used by the post-rewrite audit,” labelled snapshot-sensitive, and paired with current-status/focused-check/axiom guidance.  No unidentified “audited snapshot” phrase remains. |
| A-004 | `counting.md:132-138`; `reshape-and-exact.md:189-192` | **CLOSED.**  Where direct source admissions were found (CBC structure-graph and legacy amplification), the package reports those admissions and the unclean focused paths, then requires elaboration before an axiom receipt.  It no longer claims that a presently non-elaborating headline already yielded a `#print axioms`/`sorryAx` receipt. |
| A-005 | `reshape-and-exact.md:113-115` | **CLOSED.**  The text now states the verified Theorem 2.37 relationship exactly: supremum winning probability `ν(S^A)`, infimum winnability `ω(S^A)`, and an equivalent representative attaining `ω(S^A)`. |
| A-006 | `h-technique.md:141-155` | **CLOSED.**  The application is labelled a checked schematic; it opens the declaration namespace and the exact H-notation scope, gives the typed `Fin`/`TranscriptPrefix` and `QQueryEnvironment` binders, and uses the full endpoint identifier.  The verbatim example elaborates in the focused probe recorded below. |
| A-007 | `agents/openai.yaml:4` | **CLOSED.**  The default prompt now distinguishes current Lean declarations from the applicable rendered primary source. |
| A-008 | `conditional-equivalence.md:182-183`; `counting.md:132-138`; `reshape-and-exact.md:192` | **CLOSED.**  The detailed CBC structure-graph observation appears only in `counting.md`; the other two routes link to that single status boundary. |

### Concurrent release-B corrections

Two release-B edits landed before this receipt was sealed and are included in
the hashes and coverage below.

- **Exact H schematic:** `h-technique.md:141-155` now matches the focused
  example in
  `review/random-systems-skill/audit-probes/RewrittenSurfaceProbe.lean`.
  `lake env lean review/random-systems-skill/audit-probes/RewrittenSurfaceProbe.lean`
  succeeds; the probe SHA-256 is
  `add50260869c5b8935bccfe9410bd2d79fd2b4e737d1d4e94468f8cf7f7ad043`.
- **Lanzenberger/GameWinnability status:**
  `reshape-and-exact.md:122-127` still records the failed signed-migration
  path, but no longer infers an authored admission from that build failure.
  A source scan finds no explicit `sorry`, `admit`, or `sorryAx` in
  `GameWinnability.lean` or `LanzenbergerChain.lean`; focused checks still fail,
  so an axiom conclusion remains deferred until the path elaborates.  This
  correction supersedes the contrary admission characterization in the
  original A-003 evidence, V-025 suffix, and negative-receipt prose above.

### Claim-delta assessment

The A corrections change scope, release-state wording, provenance, and local
precision.  They do not change a theorem name, signature, hypothesis,
orientation, or numerical bound.  The release-B H edit copies the current
signature more exactly and is independently compiled above.  A-005 is a
sharper restatement of V-025,
whose exact `ν(S^A) = ω(S^A)` content and attaining representative were already
verified on the rendered thesis page.  The dated observations in A-003 and
A-004 restate V-013, V-021, and V-028; the corrected representative/winnability
paragraph makes only the verified build-failure claim and explicitly withholds
an axiom conclusion.

As a cross-check, `HEAD` is still
`96e42831e51857aefa8d9e40e996061600061866`, and every volatile Lean source hash
listed in the original audit is byte-identical.  The existing primary-source,
focused-build, and axiom receipts therefore remain the applicable evidence.
No correction required a new PDF receipt; the strengthened H snippet has the
new focused Lean receipt recorded above.

### Re-run mechanical receipts

| Check | Corrected-package result |
| --- | --- |
| Frontmatter and UI YAML | **PASS.**  Both parse; `name` is `random-systems-proofs`; the UI invocation token matches; the description is one scalar. |
| A-001--A-008 and release-B regression assertions | **PASS.**  All A closures plus the exact H and status-precision overlays were detected. |
| Focused H schematic | **PASS.**  The exact typed example and full declaration identifier elaborate in `RewrittenSurfaceProbe.lean`. |
| Representative/winnability admission precision | **PASS.**  The two named sources contain no explicit admission token; their failed paths are not presented as axiom receipts. |
| Internal Markdown links | **PASS.**  47 relative links checked, including 39 heading anchors. |
| Backticked repository references | **PASS.**  All 28 concrete `.lean`/`.md` references resolve. |
| Retired wording | **PASS.**  No “being rewritten,” unidentified “audited snapshot,” ambiguous “current source,” old winnability paraphrase, or claimed existing `sorryAx` receipt remains. |
| Full delta coverage | **PASS.**  All 904 lines in the six changed files were re-read; the remaining 278 lines are in two byte-identical references. |
| Package total | **PASS.**  Eight release-target files, 1,182 lines. |

### Final corrected-package hashes

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `SKILL.md` | 213 | `13e8c3e354c53224acaf078ff3d6cfb1d49d28ef86cfb94ca0005e6548c652f4` |
| `agents/openai.yaml` | 4 | `bad0bebb58f9cbe877b09bf9689dc87d247fca2d66de6f51e2436417f2687db2` |
| `references/conditional-equivalence.md` | 195 | `726ff1ac7c72da67162b0b5e0e2c90d8afb23c305f4a44b4c058f20fab66aea9` |
| `references/counting.md` | 138 | `32cb22ad7b078ac886105670f91202603463e0d6b1660c7a5dd4cf9e624d76db` |
| `references/creative-search.md` | 117 | `6d71c6aa3ef1797d054b2dced348630e4e3c6fd35778f6e8da0991e45eb2341e` |
| `references/h-technique.md` | 162 | `6cf1b96c9d42ae60d3e55ea564d52f416d1431fd1b79e771d747ae434d6bdb6d` |
| `references/reshape-and-exact.md` | 192 | `a334bb31f3855892f74d1a0eb4da402328b8c828c1b419d1605767a754e93f10` |
| `references/sketch-and-plan.md` | 161 | `c833cf687a05ae9e2b05065d6e2ce9578d8907b615fbe21530983f533a70a019` |

The Audit A finding set is exhausted: there is no remaining A blocker or
nonblocker.  The concurrent release-B edits are also verified, and no new
delta finding remains.
