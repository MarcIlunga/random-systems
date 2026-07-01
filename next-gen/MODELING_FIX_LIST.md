# CR18 NextGen — Modeling Fix List

Derived from `MODELING_REVIEW.md` (17 findings). Ordered by dependency: the keystone constructor
unblocks the Theorem-4.17 restatement, which unblocks the concrete instances. Fixes are **additive**:
proven free-`Shat` theorems are kept as reusable helpers, not hidden by restrictive scoping.

Cardinal rule (hook-enforced, `~/.claude/hooks/cr18_lint.py`): **base objects in; derived objects
(`Ŝ`,`T̂`,`αS`,`[q]S`) constructed in the statement; no `MonotoneMBO Ŝ`/`hCE`/`hCollision` hypotheses.**

CPA/game-example minimality guard: keep protocol files small. Do not add local aliases, helper
theorems, point-mass solver wrappers, or "rfl smoke" lemmas until a current theorem uses them. Prefer
one concrete game/adversary definition plus direct proofs through existing CR18 lemmas/tactics.

## Current status (2026-06-27 review)

- **Implemented and checked:** `gameOf`/`gameOfDDS`, `ignoreMBO_gameOf`, `monotoneMBO_gameOf`,
  `gameOf_isProbDist`, `gameOf_totalOnNonempty`, filtered Example 4.15, and the general-alphabet
  switching-lemma endpoint `urf_urp_switching`.
- **Theorem-4.17 bridge cleanup:** `GameOf.lean` now has the generic `DeltaFiniteQueryNormalization`
  and `DeltaFilteredFiniteQueryNormalization` predicates, proved supremum lifts, proved CR18 §4.10.1
  padding/normalization for filtered systems, and the assumption-explicit public theorem
  `theorem_4_17`. The previous `*_deltaBridge_obligation` placeholders have been removed. Concrete
  filtered protocol statements should call
  `theorem_4_17_filtered_of_deltaFilteredFiniteQueryNormalization_all`, which handles `q = 0` by the
  exact-zero verdict normalizer and positive budgets by the fixed-query Theorem-4.17 transcript proof.
  The raw representative-level theorem still exposes the real normalization/totality hypotheses rather
  than pretending they follow from `isProbDist` alone.
- **Thesis reconciliation:** Lanzenberger's thesis treats random systems/games as equivalence classes of
  PDS/PDG representatives. Source anchors from `papers/thesis (1).pdf` (Lanzenberger 2023, Ch. 2):
  DDS/PDS are Definitions 2.9/2.14, PDS equivalence is Definition 2.17, random systems are
  Notation 2.19, MC/DDG/PDG/random games are Definitions 2.20-2.22 and Remark 2.23, distinguishing
  advantage is Definition 2.26, the representative distance theorem is Theorem 2.31 (`A = Adv`), and
  the game analogue is the Winnability Theorem 2.37. NextGen has behavior-equivalence infrastructure,
  but `Δ`/Theorem 4.17 are still representative-level statements. Future closure should add a
  finite-query-normalized advantage layer and then lift the public endpoint toward the
  behavior/equivalence-class `Adv` view. Existing `RandomSystems/Advantage.lean` and
  `RandomSystems/AdvantageEquiv.lean` already formalize this fixed-query `Adv`/`delta` pattern;
  NextGen should adapt that design to `PFunPDS` rather than re-axiomatizing the thesis layer. This is
  why Theorem 4.17 should keep its finite-query normalization hypothesis explicit until the
  thesis-style behavior/equivalence-class layer is ported to `PFunPDS`.
- **Game/MC API review:** the operational semantics already hides the monotone condition from winners
  (`winnerView` projects away the Boolean bit), matching Thesis Remark 2.23. The remaining mismatch is
  API-level: NextGen has a subtype game API (`DDG`/`PDG`) but most theorem-facing code accepts raw
  `PFunPDS X (Y × Bool)` plus side predicates. CR18 Definition 4.18 now has one implementation:
  `ignoreMBO` is a compatibility spelling for canonical `stripMBO` / `S⁻`.
- **Transcript-law PDE repair:** `PFunPDE.transcriptLaw` now uses a probabilistic environment
  `PFunPDE.RV Ω X Y`, not a dual `PFunPDS.RV Ω Y X`.  Its environment event applies the selected DDE
  to `(some <$> y^{i-1})`, so the first-query condition is the genuine CR18 event `E() = x₁`; it is no
  longer forced through a DDS domain that excludes empty histories.  The H-technique transcript-law
  bridge has been reconciled to the same type.
- **Query filter API review:** the canonical deterministic query restriction now lives at
  `PFunDDS.filterQueries`, and the probabilistic `[q]` operation is the pushforward
  `PFunPDS.filterQueries` in `PDS.lean`, matching CR18 Def. 3.10/3.17 and the thesis'
  representative-as-distribution viewpoint. `PFunConverter.queryLimitApply` is an alias for this
  canonical DDS operation. The converter-level realization theorem is now proved:
  `PFunConverter.queryLimit_filter_apply_eq_filterQueries :
  PFunConverter.Filter.apply ([q]ᶠ) S = PFunDDS.filterQueries q S`, and `cr18_filter` uses it as the
  generic normalization hook.
- **Raw bit-system vs game boundary:** several reusable kernels (`prewinBehavior`, `massYAfalse`,
  `winProb`, `Γ`) are sensibly total on any `(X, Y × Bool)` representative, but CR18/Thesis reserve
  "game" for an MBO/MC object. Keep the generic kernels raw, and make theorem-facing statements either
  construct the MBO (`gameOf`, HCTR2's per-realization MC) or carry the minimal `MonotoneMBO`/`IsGame`
  hypothesis exactly where monotonicity is used.
- **Still open outside the switching proof:** `HCTR2.lean` is now a construction-model scaffold with
  no exported `sorry` theorem. Its public surface has been narrowed to the forward wide-block oracle,
  not the full bidirectional ±STPRP interface. Construction setup points and the XCTR counter map are
  explicit in `Params`, with `Params.Valid` carrying the static `bin0 ≠ bin1` and counter-injectivity
  assumptions for future theorem boundaries. The history-dependent MBO construction no longer uses a
  dummy empty-history output. The bad event now uses tagged logical inner-call sites and fires only on
  non-trivial collisions, so repeated setup calls and repeated identical outer queries are not counted
  as bad. The constructed standing facts `hctr2Hat_stripMBO` and `hctr2Hat_monotoneMBO` are proved
  rather than only documented.

### Current proof-shape diagnosis

The remaining Theorem-4.17 gap should be attacked at the **generic `Δ` layer**, not inside the
switching lemma.

1. **CR18 §4.10.1 finite-query WLOG/padding:** missing in NextGen for raw `maxAdvantage`. The paper
   fixes a finite upper bound `q` for a distinguisher and pads early stopping with dummy queries.
2. **Fixed-query Lemma 4.16/Theorem 4.17 chain:** implemented for per-`D` statements via
   `QueriesExactly`, `TotalUpTo`, `lemma_4_16'`, the mass variants, and the absorbed/blind helpers.
3. **Base-object construction:** implemented by `gameOf`; free-`Ŝ` helper theorems are no longer the
   paper-facing API.
4. **Supremum step:** still blocked only because raw `Δ` ranges over all probability distributions of
   `DDD`, with no normalization theorem reducing that supremum to fixed/exact finite-query
   distinguishers.

This is also where the 2023 thesis should influence the design: define the fixed-query/adaptive
advantage layer in the style of `RandomSystems.Advantage`/`AdvantageEquiv`, prove it respects the
behavior/equivalence-class presentation, then relate the CR18 notation `Δ([q]S,[q]T)` to that layer by
the generic padding theorem.

### Thesis anchors to preserve

These are the concrete commitments imported from `papers/thesis (1).pdf` into the NextGen review.

1. **PDS equivalence (Thesis Def. 2.17 / Lemma 2.18).** Two representatives are the same random system
   when all environment transcript distributions agree; non-adaptive deterministic environments suffice.
   NextGen's `PFunPDS.behavior`/`BehaviorSeqEquiv` is the right carrier for the PFun version of this.
2. **Random system (Thesis Notation 2.19).** A random system is an equivalence class `[S]`, not a chosen
   representative. Public security quantities should either be stated on behavior/equivalence classes or
   explicitly be representative lemmas that feed an invariant endpoint.
3. **MC/DDG (Thesis Def. 2.20-2.21).** For a fixed DDS `s`, an MC is a monotone input-history predicate
   `A_s : X* → {0,1}`; the DDG transcript is `(t, A_s(t_inputs))`. NextGen's `gameOf S cond` is the
   important special case where `A_s(l) = cond (ioTranscript s l)` factors through the visible
   input/output transcript. Do not force all MCs into this special case: internal-state events such as
   HCTR2's internal permutation collision may need a per-realization `A_s`.
4. **Hidden MC (Thesis Remark 2.23).** Environments/winners do not observe the MC bit. NextGen's
   `winnerView` projection is therefore not an implementation trick; it is part of the model.
5. **Random game (Thesis Def. 2.22 / Remark 2.24).** A random game is an equivalence class of PDG
   representatives. Raw `PFunPDS X (Y × Bool)` is a representative; `DDG`/`PDG` subtypes are the
   paper-shaped carrier. We can use raw representatives internally, but theorem-facing APIs must not
   silently accept non-games.
6. **Distance theorem (Thesis Def. 2.26, Def. 2.28, Thm. 2.31).** `Adv(S,T)` is the supremum transcript
   distance over environments; `A(S,T)` is the infimum statistical distance over equivalent
   representatives; the theorem says they coincide. The unresolved `GameOf.theorem_4_17` supremum bridge
   should be closed through this generic invariant/fixed-query layer, not by adding switching-specific
   hypotheses or a local transcript-counting theorem under the switching lemma.
7. **Winnability theorem (Thesis Def. 2.35-2.37).** The optimal winning probability of a random game is
   the infimum probability that an equivalent deterministic-game representative is winnable. This is the
   right abstract target for `Γ`/`Γᵇ`: switching-specific collision bounds should be concrete witnesses
   feeding a generic game-winnability layer, not ad hoc H-coefficient-style theorems baked into the
   switching statement.

---

## Phase 0 — Keystone (unblocks everything)

- [x] **F0.1 — build `gameOf` constructor** (UPSTREAM-CANDIDATE). "Enhance a base PDS `S : PFunPDS X Y`
  with a monotone transcript-predicate `cond` → game `gameOf S cond : PFunPDS X (Y × Bool)`." Prove the
  two standing facts as lemmas: `ignoreMBO (gameOf S cond) = S` and `MonotoneMBO (gameOf S cond)` (from
  `cond` monotone). `gameEnhance` only *copies* an existing MBO — this is the genuinely missing piece
  (root cause of findings #1–#6, #11). File: new `NextGen/GameOf.lean` or into `SystemMBO.lean`.
- [ ] **F0.2 — reusable collision marginal** (UPSTREAM-CANDIDATE). `iidPow_pair_collision`: two distinct
  coordinates of `X^q` coincide with prob `∑ₐ X(a)²` (independence); uniform corollary `= 1/t`. Replaces
  the bespoke `card_pair_eq` in `lemma_4_18` and feeds the Lemma-4.19 collision step. (Optional polish;
  `lemma_4_18` already proven via `card_pair_eq` — do only if it cleans up `lemma_4_19`.)

## Phase 1 — Restate the Theorem-4.17 chain on BASE objects (findings #1–#6)

- [ ] **F1.0 — finite-query normalization for `Δ`** (UPSTREAM-CANDIDATE, generic): add the missing
  CR18 §4.10.1 bridge. The target is a bounded/fixed-query advantage layer for `PFunPDS`, plus a
  padding theorem saying raw `Δ([q]S,[q]T)` is controlled by the exact-`q`/bounded layer. This should be
  independent of switching, HCTR2, or any specific MBO. Minimal assumptions: only the system-domain
  facts genuinely needed to run the filtered systems; do not add `QueriesExactly` or totality
  hypotheses to public protocol statements. Concrete shape:
  - define a normalized/fixed-query distinguisher layer for `PFunDDS.DDD`, or a theorem that collapses
    any raw `D` interacting with `⌈q⌉S`/`⌈q⌉T` to an equivalent exact-`q` distinguisher;
  - prove `advantage D (⌈q⌉S) (⌈q⌉T)` is preserved by that collapse, using only the filter semantics and
    the fact that no new information arrives after the `(q+1)`-st query;
  - derive the `sSup` bridge that lets `GameOf.theorem_4_17` apply the existing per-`D`
    `theorem_4_17_advantage` without exposing `QueriesExactly`/`TotalOnNonempty` in concrete protocol
    statements;
  - expose the query-filtered corollary that concrete proofs should call, with shape
    `theorem_4_17_filtered q S T cond : Δ(⌈q⌉S, ⌈q⌉T) ≤ Γᵇ(⌈q⌉(gameOf S cond))` (or the normalized
    commuting form `Γᵇ(gameOf (⌈q⌉S) cond)`). Its hypotheses should be only the base-system
    probability/totality facts needed before filtering, the monotone `cond`, and the filtered
    conditional equivalence. This is the paper step used by Lemma 4.19.
  - in parallel, port the old fixed-query `RandomSystems.Advantage`/`AdvantageEquiv` design to
    `PFunPDS` so this representative-level `Δ` is known to respect the thesis behavior/equivalence-class
    view (`A(S,T)=Adv(S,T)`).
  **Implemented:** `GameOf.lean` now contains the generic normalization predicates and proved supremum
  lifts (`DeltaFiniteQueryNormalization`, `DeltaFilteredFiniteQueryNormalization`,
  `maxAdvantage_le_of_deltaFiniteQueryNormalization`,
  `maxAdvantage_filterQueries_le_of_deltaFilteredFiniteQueryNormalization_exact`) plus the
  assumption-explicit Theorem-4.17 corollaries. The filtered all-budget endpoint is
  `theorem_4_17_filtered_of_deltaFilteredFiniteQueryNormalization_all`:
  `Δ(⌈q⌉S,⌈q⌉T) ≤ Γᵇ(gameOf (⌈q⌉S) cond)`. The `q = 0` indexing wrinkle is closed by exact-zero
  verdict normalization; positive budgets continue through the existing exact `(i+1)` transcript
  chain.
  **Implemented leaf:** `PFunDDS.padDDD` constructs the deterministic padded raw distinguisher,
  `PFunDDS.padDDDDist` lifts it to probabilistic distinguishers, and
  `PFunDDS.padDDDDist_queriesExactly_support` proves every support element is exact-`q`. The remaining
  mathematical leaf was `padDDDDist` advantage preservation against `⌈q⌉S,⌈q⌉T`; this is now proved by
  `advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty`.
  The first generic run-semantics step is now proved:
  `PFunDDS.verdict_padDDD_iff_tail`, characterizing a padded distinguisher's verdict as the original
  distinguisher's eventual verdict after the padded run's first `q` replies followed by `⊥` replies.
  The filter-side exact-tail API is also proved:
  `PFunDDS.transcript_length_eq_of_fire`,
  `PFunDDS.transcript_outputs_filterQueries_tail_of_total`,
  `PFunDDS.transcript_filterQueries_tail_eq_of_all_query_of_total`, and
  `PFunDDS.verdict_filterQueries_iff_tail_of_total`. These are generic `[q]`/transcript facts, not
  switching-specific facts. The remaining deterministic bridge is the comparison between the original
  and padded runs up to the filter budget: if the original distinguisher keeps querying, their
  `q`-prefixes agree; if it stops early, the DDD finality axiom transports the verdict across padded
  dummy queries.
  **Implemented next layer:** `PFunDDS.transcript_padDDD_filterQueries_eq_of_all_query_before` proves
  the pre-budget run comparison; `PFunDDS.verdict_padDDD_filterQueries_iff_of_total` proves the exact
  deterministic verdict equivalence against `[q]S`; `verdictProb_padDDDDist_filterQueries_eq_of_totalOnNonempty`
  and `advantage_padDDDDist_filterQueries_eq_of_totalOnNonempty` lift it through `winProb`/`verdictProb`;
  `deltaFilteredFiniteQueryNormalization_of_totalOnNonempty` packages the exact-`q` padded
  distinguisher distribution as the filtered normalization witness. Also added generic support-totality
  facts for `PFunPDS.ofFunDist`, `PFunPDS.ofPermDist`, `PFunPDS.URF`, and `PFunPDS.URP`.
  The per-D endpoint now has a bounded form,
  `theorem_4_17_advantage_of_totalUpTo`, and the filtered theorem uses `TotalUpTo` after filtering
  rather than requiring global totality of `⌈q⌉S`.
- [x] **F1.1 — public `theorem_4_17`** (`GameOf.lean`, #1): inputs = base `S T : PFunPDS X Y`,
  query budget, MBO `cond`; construct `Ŝ := gameOf S cond` in-statement; *prove* `ignoreMBO Ŝ = S`,
  `MonotoneMBO Ŝ`; require only `Ŝ |≡ T` (the genuine Def-4.19 hypothesis); conclude the blind
  `∆(S,T) ≤ Γ(bŜ)`. The Lean theorem is assumption-explicit: it also carries the probability,
  totality, and finite-query normalization hypotheses used by the proof rather than hiding them behind
  a bridge obligation.
- [x] **F1.2 — blind/absorbed variants** (`BlindConverter.lean:150,184`; `BlindAbsorption.lean:629,667`,
  #2,#3): keep proven bodies as reusable `*_abstract`/helper facts. The public absorbed theorem
  *derives* blindness via the absorbed winner — drop the `hblind`-on-`D` hypothesis (#2).
- [x] **F1.3 — eq-4.39 bridge** (`massYAfalse_gameEnhance_eq`, #6): re-express over `gameOf S cond`, or
  keep as a reusable lemma about the constructed `Ŝ`.
- [x] **F1.4 — rename `RelateGameDistinguishing.theorem_4_17`** (`:410`, #4): it's a Lemma-4.16
  corollary over two enhanced systems concluding adaptive `Γ(S)` — rename `lemma_4_16_adaptive_le_maxWinProb`
  and free the name `theorem_4_17` for the base-object theorem.
- [x] **F1.5 — abstract-scaffold lemmas** (`lemma_4_16`, `lemma_4_16'`, etc., #5): mark/rename as
  helper lemmas; they are not paper endpoints.

## Phase 2 — Concrete instances (findings #7, #8, #11, #12)

- [x] **F2.1 — Lemma 4.19 = the FILTERED switching lemma** (`SwitchingLemma.lean`, #7,#8): state
  `∆(filterQueries q Rₙ,ₙ, filterQueries q Pₙ) ≤ ½q²2⁻ⁿ` (the `[q]` filter Maurer writes); construct
  `R̂ₙ,ₙ := gameOf Rₙ,ₙ collisionCond`; route through the public base-object Thm 4.17; do NOT expose an
  unfiltered `Γᵇ` hypothesis. `urf_urp_switching` is implemented and `SwitchingLemma.lean` checks
  clean.
  Assumption-minimality cleanup done: the public `urf_urp_switching` endpoint now requires only
  `[Fintype X] [Nonempty X]`; decidable equality is localized with `open Classical in` and remains only
  in internal finite-counting lemmas where `Finset`/event filters require it.
  The proof now calls `theorem_4_17_filtered_of_deltaFilteredFiniteQueryNormalization_all`, deriving
  the filtered normalization witness from `deltaFilteredFiniteQueryNormalization_of_totalOnNonempty`.
  This makes the Lean proof read like the PDF line `Δ([q]R, [q]P) ≤ Γ(b[q]R̂)`, using the normalized
  commuting form `gameOf ([q]R) collisionCond`.
- [ ] **F2.2 — HCTR2** (`HCTR2.lean`, #11,#12): keep the MBO construction tight. For this internal
  collision event, forcing `gameOf hctr2Real cond` would be too restrictive unless the public transcript
  carries all internal permutation inputs. The thesis view supports the current per-realization
  history-dependent MC shape `A_σ : X* → {0,1}`. The previous exported `hctr2_condEquiv` and
  `hctr2_stprp_withinquery_bound` placeholder theorems were removed because the conditional-equivalence
  route and the leading-only RHS were not yet source-faithful. Remaining work is to formulate the
  construction/fixed-transcript density bridge for HCTR2 and then state the final advantage bound with
  all event terms it actually pays for. The current file is explicitly forward-only; the full ±STPRP
  model still needs a direction-indexed oracle/interface and the row-marked/score bad-event family from
  the HCTR2 CR18 notes.
  **Partial:** public permutation-carrier instance hypotheses have been removed; Lean infers
  `Fintype`/`Nonempty` for `Equiv.Perm F` and `Equiv.Perm (WideBody F L)` from the finite field/body
  carriers. Construction constants now live in `Params F L`, and `hctr2ForwardAdvantage` names the
  forward-only filtered distinguishing quantity. `historyEvaluator` now takes a nonempty-history proof,
  so `hctr2Hat` uses the real last query and contains no dummy/default empty-history value.
  `innerCollided` is now based on
  `HasNontrivialInnerCollision` over tagged `InnerSite`s, matching the CBC "non-trivial collision"
  discipline. The constructed facts `hctr2Hat_stripMBO : (hctr2Hat H cfg)⁻ = hctr2Real H cfg` and
  `hctr2Hat_monotoneMBO : MonotoneMBO (hctr2Hat H cfg)` are proved in the file.
- [x] **F2.3 — enumerate & discharge remaining real `sorry`s** (#12): `next-gen/NextGen` now has no
  executable `sorry` declarations; remaining textual mentions are roadmap/prose only.

## Phase 3 — Hygiene / minors (findings #9, #10, #13–#17)

- [ ] **F3.1 — one Def-4.18** (#17): merge `stripMBO`/`ignoreMBO` to a single canonical name. Prefer the
  paper-facing notation `S⁻` for theorem statements; make the other spelling an `abbrev`/deprecated
  alias with simp-lemma bridges for domains, outputs, transcript projection, and PDS pushforwards.
  Avoid two independent definitions: they are the same operation, and drift here will infect every
  Lemma-4.16/Theorem-4.17 statement. **Partial:** `RelateGameDistinguishing.lean` now imports
  `SystemMBO.lean`, and both `PFunDDS.ignoreMBO` and `PFunPDS.ignoreMBO` are compatibility abbrevs for
  canonical `stripMBO`; remaining cleanup is notation/API migration from `⁻ᴹ`/`ignoreMBO` to paper
  notation `S⁻` in public statements.
- [ ] **F3.2 — reuse `DDG` / decide the raw-game API** (#9): split the API into two explicit layers.
  The *generic bit-system layer* may keep raw `PFunPDS X (Y × Bool)` for total infrastructure such as
  `prewinBehavior`, `massYAfalse`, `winProb`, and `Γ`; these definitions are meaningful as functions
  even before monotonicity is known. The *paper-facing game layer* must use either the `DDG`/`PDG`
  subtype or raw representatives plus the minimal `MonotoneMBO`/`IsGame` side condition, and public
  theorem statements should construct/prove that condition whenever possible. The thesis pushes toward
  a mathematical pair `(s,A)`/equivalence-class view, while CR18 often writes systems with an attached
  MBO bit. NextGen's current winner semantics is sound (`winnerView` hides the bit), but public
  statements should not silently accept non-games. Concrete cleanup:
  - move/promote the support predicate `MonotoneMBO` next to `DDS.IsGame`/`DDG` in `PDS.lean`, not in
    `Theorem417.lean`; **done**
  - add coercion/bridge lemmas between a `PDG` representative and the raw `PFunPDS X (Y × Bool)` view;
    **partial:** `PFunPDS.PDG.rawLaw` forgets the deterministic `DDG` subtype into a raw law, with
    `rawLaw_isProbDist` and `rawLaw_monotoneMBO`;
  - consider renaming raw infrastructure docs to "bit-labeled system" where no monotonicity is assumed,
    reserving "game" for endpoints with a constructed/proved MBO.
- [ ] **F3.3 — bounded totality** (#10): replace global `TotalOnNonempty` with `TotalUpTo q` where the
  proof only inspects `≤ q` prefixes; keep global only where a marginal/normalizer genuinely forces it.
  **Partial:** the Lemma-4.16 core already uses `TotalUpTo`, and the bounded support lemmas now exist:
  `massDom_eq_weight_of_totalUpTo`/`massDom_eq_one_of_totalUpTo`,
  `massYAfalse_gameEnhance_eq_of_totalUpTo`, and `winProb_absorption_of_totalUpTo`. These are the exact
  fixed-query normalizers used by the eq. (4.39) and absorption proof steps. Compatibility wrappers keep
  the old global-totality API alive for existing callers. **Current blocker:** the per-winner
  Theorem-4.17 helper still rewrites by the full-PDS equality `ignoreMBO_gameEnhance`, which is stronger
  than a fixed-query proof needs. Removing the last global `TotalOnNonempty` hypotheses requires a new
  advantage/verdict-level congruence for exact-query distinguishers, not another normalizer lemma.
  Do not add global totality to `urf_urp_switching`; filtered systems intentionally fail it beyond the
  query budget.
- [ ] **F3.4 — GameEquivalence "Lemma 4.15"** (#13): keep the generic factor-through lemma as a
  neutral API fact; expose the operational `winProb` congruence as the paper-facing Lemma 4.15. The
  tautology "`≡ᵍ` is equality of pre-winning behavior, so any function of it agrees" is useful
  infrastructure, but the theorem users expect is the proved bridge from `winsDDS`/`winProb` to
  pre-winning behavior.
- [ ] **F3.5 — converter-application API** (#14): pick one paper-facing API for CR18 Def 3.9. NextGen
  currently has direct `PFunConverter.DDC.apply`, native DDS operations with converter aliases
  (`cascadeViaConverter`/`combineViaConverter`), and the function-algebra/fuel-free `CausalApply.applyG`
  line. Keep at most one as the theorem-facing operation; prove the others realize it in their intended
  fragments. In particular, prove the `rfl`-aliases realize `DDC.apply`; keep driver/fuel machinery in
  implementation namespaces.
- [ ] **F3.6 — drop avoidable instances**: localize `[DecidableEq P]` on resource attachment (#15);
  prove the transcript bridge from finite support, not `[Fintype Ω]` (#16). **Partial:** the switching
  lemma endpoint no longer exposes `[DecidableEq X]`; it is localized classically at the declaration and
  proof boundary, matching the thesis/CR18 mathematical assumption that the alphabet is finite and
  nonempty. The NextGen random-permutation constructor `PFunPDS.URP` and its standing fact
  `PFunPDS.URP_isProbDist` no longer expose `[Nonempty (Equiv.Perm X)]`; the witness is the canonical
  identity permutation and is kept local to the implementation.
- [x] **F3.7 — promote CR18 proof automation once stable** (UPSTREAM-CANDIDATE): the local
  `SwitchingLemma.lean` normal forms (`cr18_prob`, `cr18_filter`, `cr18_game`, `cr18_transcript`,
  `cr18_cond`, `cr18_simp`) are the right direction. Once they have a second consumer, move the
  underlying simp lemmas next to their definitions so proofs do not need manual
  `unfold Dist.isProbDist ...; rw [Dist.weight_fTransform]` or hand-written `[q]`/`gameOf`
  commutation. Keep the macros conservative and paper-level: probability mass bookkeeping, filter
  bookkeeping, game/MBO projection, transcript shape, and small arithmetic. **Partial:** the generic
  pushforward facts `Dist.fTransform_isProbDist` and `[simp] Dist.isProbDist_fTransform` now live next
  to `Dist.weight_fTransform`; `PDG.rawLaw_isProbDist` and the old Theorem-4.17 helper sites use the
  promoted lemma. The specific open-coded `isProbDist`/`weight_fTransform` normalization pattern is
  cleared under `NextGen`. The PDS constructor facts
  `PFunPDS.isProbDist_ofFunDist_iff`, `PFunPDS.URF_isProbDist`,
  `PFunPDS.isProbDist_ofPermDist_iff`, and `PFunPDS.URP_isProbDist` now live next to the
  random-function/permutation constructors in `PDS.lean`; `[simp] PFunPDS.isProbDist_filterQueries_iff`
  lives next to the `[q]` filter in `PDS.lean`; `PFunDDS.filterQueries_gameOfDDS` and
  `PFunPDS.filterQueries_gameOf` live next to the `gameOf` constructor in `GameOf.lean`. The generic
  tactics `cr18_prob`, `cr18_filter`, `cr18_game`, `cr18_transcript`, `cr18_arith`, `cr18_simp`, and
  `cr18_grind` now live in `CR18Tactics.lean`; protocol/event-specific unfolding, such as
  `collisionCond`, is intentionally not part of the generic tactic module. Future polish can replace
  the explicit macro lists with attributes, but the proof-local duplication has been removed.
- [x] **F3.8 — unify the `[q]` filter APIs** (UPSTREAM-CANDIDATE): NextGen should have one canonical
  Def-3.10 query restriction. The deterministic operation now lives at
  `PFunDDS.filterQueries`; the PDS operation `PFunPDS.filterQueries` / `⌈q⌉S` now lives in `PDS.lean`
  as the pushforward through deterministic representatives; and `PFunConverter.queryLimitApply q S`
  is definitionally equal to `PFunDDS.filterQueries q S`. This removes the duplicated DDS/PDS filter
  definitions from `Lemma415.lean` and lets theorem files consume `[q]` instead of owning it. The
  semantic converter-realization theorem
  `PFunConverter.Filter.apply ([q]ᶠ) S = PFunDDS.filterQueries q S` is now proved as
  `PFunConverter.queryLimit_filter_apply_eq_filterQueries` and promoted into `cr18_filter`. Protocol
  statements should use the canonical `[q]S` API; the converter object `[q]ᶠ` is connected to it by
  this realization theorem, not by a second public notion.

---

### Severity / sequencing
- **Must-fix, blocking:** F0.1, F1.0–F1.5, F2.1 (the faithfulness core).
- **Must-fix, dependent:** F2.2.
- **Should-fix:** F3.1–F3.3.
- **Minor:** F0.2, F3.4–F3.8.

### Invariants to preserve while fixing
- No proof deleted — free-`Shat` theorems become reusable helpers, proofs unchanged.
- Axiom-clean `[propext, Classical.choice, Quot.sound]` maintained; build green at each commit.
- Commit per fix; the lint hook must pass on every edited statement.
