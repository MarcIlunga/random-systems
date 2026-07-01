# H-technique migration to the NextGen random-systems surface

This folder tracks the migration of the H-technique and its applications onto
the `NextGen` CR18/PFun formalization.  It is intentionally not imported by
`next-gen/NextGen.lean` yet: the migration must prove itself before it becomes
the main surface.

The source H-technique project is:

```text
/Users/marcilunga/Documents/ToB/research/fv/h-technique
```

That project already has `require RandomSystems from ".." / "random-systems"`.
So this repository must not add `require HTechnique`: it would create a package
cycle.

The workflow is therefore external-first:

1. make the H-technique project itself build and expose the right theorem
   shapes there;
2. migrate the stabilized definitions/theorems into this repository's
   `NextGen` surface;
3. reconcile the old random-systems APIs and applications against the migrated
   surface.

This folder is the cross-repository migration ledger.  It records what must be
ported and what the `NextGen` target shape is, but the first implementation
step for H-technique-specific material is usually in `/h-technique`, not here.

## Source anchors

- CR18 §3.6.5 and Lemma 3.2: transcript-prefix laws factor into system and
  environment factors.  `NextGen.PDS` now exposes this as `transcriptLaw`,
  `transcriptSystemFactor`, `transcriptEnvironmentFactor`, and
  `transcriptLaw_eq_systemFactor_mul_environmentFactor`.  The environment side
  is now correctly a `PFunPDE.RV` (a random DDE) over optional output histories
  `List (Option Y)`, so the first-query event is `E() = x₁` rather than an
  impossible DDS evaluation at an empty input history.
- CR18 §4.10.2 and Theorem 4.17: game/distinguishing bridge.  The migrated
  H-technique route must use the `NextGen` game/MBO surface and the filtered
  or per-winner bounds, not an unfiltered `Gamma` shortcut.
- CR18 Lemma 4.19: URF/URP switching is the first concrete H-coefficient-like
  counting target to migrate.
- Lanzenberger thesis, Def. 2.17, Notation 2.19, Def. 2.26, Thm. 2.31:
  systems are transcript-law equivalence classes, `Adv` is a supremum over
  transcript distances, and the static distance `A` equals `Adv`.  This is the
  conceptual target for replacing old representative-specific statements.
- Lanzenberger-Maurer 2020 / SoP development: the SoP proof must continue to
  reduce adaptive advantage to a fixed visible transcript law and then to the
  orbit/counting bound.

## Current checked boundary

The aggregate compile target is:

```bash
lake build NextGen.Migration.HTechnique.All
```

The curated API checkpoint is:

```lean
import NextGen.Migration.HTechnique.Surface
```

`Surface` is the module to benchmark before the eventual surface flip.  It
reexports the distribution-level H-technique bounds, law-level CR18
transcript-law security wrappers, the migrated SoP application boundary, and
the migrated fixed-query HashThenPRF endpoint.
Its direct public theorem statements are over `ProbPDS`, `ProbPDE`,
deterministic CR18 environments, fixed-query transcript distributions, and
concrete application parameters.  It does not import the legacy bounded-system
compatibility bridge or the switching-heavy `LegacyBoundary` compile gate.

`All` imports this curated surface, the compatibility/build-only
legacy/switching boundary, and the migration-local tactic layer (`TacticsBase`,
`TacticsCore`, and `Tactics`) for fixed-query transcript laws,
function-evaluator laws, and repeated-query compression rewrites.

Statement-shape invariant for this migration: public CR18 transcript endpoints
take law-level systems/environments (`ProbPDS`, `ProbPDE`), deterministic CR18
environments, concrete fixed-query vectors, and named transcript-space
assumptions (`FiniteTranscriptSpace`, plus `DiscreteTranscriptSpace` only for
finite-sum H-technique lemmas).  They should not expose sample spaces,
probability distributions, raw RVs, representative wrappers, or raw
`PFunPDE.TranscriptPrefix` instance paths unless the theorem is explicitly a
construction-level adapter.
Generic constructor facts, such as function-evaluator transcript-law
normalization and repeated-query compression, should live on the shared
`RandomSystems.CR18`/`NextGen` surface and be reused from migration proofs,
not duplicated as migration-local endpoint wrappers.
The law-level CR18 transcript surface now follows that rule:
`RandomSystems.CR18.PFunPDS.Prob` / `PFunPDE.Prob` own the law-level
transcript constructors, totality predicates, deterministic-environment
embedding, weight facts, deterministic transcript distribution, ideal URF/URP laws,
the deterministic q-query environment index, and the law-level adaptive
transcript-advantage supremum.  `NextGen.BoundedEnvironment` also owns the
core bounded-chooser adaptive transcript supremum and its comparison with the
full environment supremum.  `TranscriptLawPublic` and
`AdaptiveTranscriptLawAdvantage` preserve migration-facing names as thin
aliases.  Generic supremum/order support for advantage definitions, including
the finite `NNReal` supremum transfer lemma, lives in `RandomSystems.StatDist`
rather than in the migration layer.
The first reusable CR18 raw-`Delta` to thesis transcript-`Adv` bridge facts are
shared too: event-mass gaps are bounded by statistical distance in
`RandomSystems.StatDist`, exact-query distinguishers give q-query-total
deterministic environments in `NextGen.AdaptiveLawBridge`, and the filtered
bridge
`RandomSystems.CR18.maxAdvantage_filterQueries_le_adaptiveTranscriptAdvantage`
now proves the filtered `Delta` bound from finite-query normalization,
base-law `q`-step totality, the exact-query verdict/transcript theorem, and the
base/filter transcript-law comparison.  Its right-hand side is the base thesis
`Adv(S,T)`, not the filtered-law variant.  The curated security surface exposes
this as `SecurityDefs.filteredDelta_le_Adv`, stated over law-level `ProbPDS`
objects and constructing Maurer's `[q]S`/`[q]T` inside the conclusion.

Promotion-boundary audit result: `Surface` is statement-clean and the public
SoP/HashThenPRF paths are representative-bridge-clean.  Its direct imports are
`Density`, `HashThenPRF`, `SecurityDefs`, and `SoPBoundary`; the direct public
security/application headers do not mention `PDSRepresentative`,
`PDERepresentative`, raw sample spaces,
probability carriers, or RV parameters.  The SoP proof path now uses
the shared `NextGen.AdaptiveLawBridge`, `FixedQueryLaw`, `TranscriptLawPublic` /
`TranscriptLawCore`, and law-level SoP support modules.  The old representative
modules `TranscriptLaw`, `FixedQuery`, and `AdaptiveBridge` are kept behind
legacy/compatibility gates such as `SoP.CompressionLegacy` and
`SoPLegacyBoundary`.  The surface policy is convention-based rather than
import-hidden: Lean exposes theorem proof dependencies transitively, so the
promotion audit is on direct public endpoint modules, theorem headers,
namespaces, and documentation.  Representative endpoints no longer sit on the
public SoP path.

New migrated modules should not import `RandomSystems.*` directly.  They should
receive one source item at a time after the corresponding `/h-technique` source
shape has been checked or repaired, and state it over the `NextGen`
transcript/game/PDS surface.

Current external-source status:

- `lake build HTechnique` in `/h-technique` builds in the current worktree.
- 2026-07-01 check: the SoP preservation gate
  `lake build HTechnique.Core HTechnique.OneSided
  HTechnique.Applications.SumOfPermutations` builds in `/h-technique`, and the
  migrated target `lake build NextGen.Migration.HTechnique.All` builds in
  `/random-systems`.
- 2026-07-01 check: the migrated HashThenPRF fixed-query endpoint
  `NextGen.Migration.HTechnique.HashThenPRF.hashThenPRF_fixedQueryTranscript_bound`
  builds on the CR18 law-level transcript surface.  The source-facing migrated
  name `HashThenPRF.hashThenPRF_security` is a thin wrapper around that
  endpoint.
- `/h-technique/HTechnique/CountingLemmas.lean` now owns the pure counting
  and SoP ratio-counting lemmas used by the application.
- `/h-technique/HTechnique/Core.lean` now owns the generic
  `fTransform_ratio_lower` distribution pushforward lemma, the
  distribution-level one-sided H-technique theorems, and the generic
  `oneSided_hTechnique_fTransform` post-processing theorem.  It also owns the
  source-level `uniformFunction_eval_uniform` bridge, which keeps the fixed
  injective-query URF law mathematically tight without imposing a stray
  `[Nonempty X]` hypothesis on the domain.
- SoP is therefore a source application to preserve during migration, not a
  failing source gate.
- `HTechnique.Applications.HashThenPRF` now has a migrated fixed-query
  transcript-distance theorem in
  `NextGen.Migration.HTechnique.HashThenPRF`.  The migrated statement is
  intentionally law-level: it constructs the concrete hash-then-PRF `ProbPDS`
  and the ideal URF transcript law in the theorem, while keeping the paper's
  extended `(y^q, h)` distributions as proof support.  The migrated
  `hashThenPRF_security` name preserves the source theorem name on this
  law-level statement.

Current migrated slices:

- `NextGen.Migration.HTechnique.Counting`: the concrete Jha-Nandi Proposition
  8.1 SoP ratio-counting core from
  `/h-technique/HTechnique/CountingLemmas.lean`.  Generic product,
  falling-factorial, birthday, cubic query-bound arithmetic, function-fiber,
  and permutation-fiber facts now live in `RandomSystems.CR18.Counting` and are
  used directly by the migration layer rather than re-aliased here.
- `NextGen.Migration.HTechnique.Density`: paper-facing compatibility wrappers
  for the distribution-level H-technique facts from
  `/h-technique/HTechnique/Core.lean`.  The generic API now lives in
  `RandomSystems.StatDist`: `probBad`, ratio, expectation,
  equality-on-good, one-sided, common-pushforward one-sided,
  proper-probability, and finite-mass-function wrappers.  The density wrappers
  reuse those shared facts directly, so the generic probability step no longer
  lives in the migration layer and the theorem statements carry fewer
  decidability hypotheses.  The deterministic pushforward support facts it
  needs now live in the shared `RandomSystems.Dist` API: injective-image mass
  preservation, off-image zero mass, preservation of pointwise multiplicative
  lower bounds under a common pushforward, uniform event mass as a finite
  cardinality ratio, and the uniform-pushforward theorem for maps with equal
  fiber cardinalities.
  `RandomSystems.Dist.mass_eq_sum` is also nonempty-free, so finite carrier
  event-mass rewrites do not leak irrelevant `[Nonempty A]` assumptions.  The
  generic fixed-query law for evaluating a uniform random function on an
  injective input tuple has moved out to `NextGen.FunctionEvaluator`, so this
  slice now stays purely distribution/statistical-distance-level and does not
  import the CR18/PDS surface or the old statistical-distance API.
- `NextGen.Migration.HTechnique.TranscriptLaw`: support bridge from any finite
  mass function, and in particular the current `PFunPDE.transcriptLaw` API, into
  the distribution-level H-technique.  The canonical transcript-law distribution
  adapter now lives at the CR18 surface as `PFunPDE.transcriptLawDist`, with
  apply/weight and Lemma-3.2 factorization lemmas; `TranscriptLawBridge.dist` is
  now only a compatibility alias for that shared API.  It also defines the
  migration-local `PDSRepresentative` bridge object, bundling a CR18 sample
  space, probability distribution, and system-valued RV so theorem-facing
  transcript-law endpoints take systems as high-level objects rather than
  exposing `Ω`, `pΩ`, and RV parameters separately.  It also defines the
  symmetric `PDERepresentative` object for probabilistic environments, plus
  `PDERepresentative.KQueryTotal` and the deterministic one-point constructor
  used for fixed-query and bounded-chooser environments.  Its ratio and one-sided
  bridge statements now use the named transcript carrier
  `TranscriptPrefix X Y q` and the named assumptions
  `FiniteTranscriptSpace X Y q` / `DiscreteTranscriptSpace X Y q`, so the
  public theorem headers record the mathematical transcript space rather than
  leaking the underlying `PFunPDE.TranscriptPrefix` implementation path.
  `DiscreteTranscriptSpace` is kept separate from finiteness and appears only
  where the finite H-technique summation lemmas require decidable equality.
  These theorem statements inherit the smaller density-level hypotheses: equal total
  weights, ideal mass at most one, and the concrete pointwise lower bound; they
  no longer carry an unused `eps <= 1` side condition.  The concrete experiment
  bridge is now representative-level on both systems and environments, matching
  CR18's DDE transcript semantics without exposing environment sample spaces,
  probability distributions, or RVs at the theorem boundary.  The canonical
  ideal URF constructor is `PDSRepresentative.urf`, so PRF-style endpoints build
  the ideal representative internally instead of asking callers for its sample
  space, probability distribution, or random variable.
- `NextGen.FixedQuery` / `NextGen.Migration.HTechnique.FixedQuery`: the generic
  fixed-query CR18 bridge now lives in the shared `RandomSystems.CR18`
  namespace.  It owns the `Fin q -> X` to `List.Vector X q` adapter, the exact
  fixed-query `DDE X Y`/PDE environment, the generic fixed-input
  transcript-prefix embedding and deterministic lift, and the 0/1 fixed-query
  transcript-environment factor laws.  It also proves the generic reduction of
  `PFunPDE.transcriptLaw` under that environment to the CR18 system factor on
  the fixed input tuple, the exact fixed-input lift of pointwise lower bounds,
  and the deterministic `fTransform`/fixed-input-lift commuting theorem used by
  repeated-query compression.  `FixedQueryLaw` is the clean law-level facade;
  source-name aliases such as
  `ProbPDS.fixedQueryTranscriptDist_functionEvaluator` live in the
  migration-only `FixedQueryCompatibility` module, while application proofs use
  the owner-level CR18 theorem directly.  The migration file is now only a
  compatibility re-export while downstream imports are migrated to the shared
  module.
- `NextGen.FunctionEvaluator` /
  `NextGen.Migration.HTechnique.FunctionEvaluator`: the generic sampled
  function-evaluator CR18 bridge now lives in the shared `RandomSystems.CR18`
  namespace.  It owns the `functionEvaluatorRV` embedding and proves that a
  function-evaluator transcript-system event is exactly pointwise agreement
  between the sampled function and the fixed output vector on the fixed input
  vector.  Its basic evaluation lemma factors through the existing
  `PFunDDS.functionEvaluator_output` theorem, with only a thin list-prefix
  wrapper around Mathlib's `List.take_concat_get'`.  It also owns the generic
  uniform-function fixed-query law
  `RandomSystems.CR18.uniformFunction_eval_uniform`, proved from the shared
  function-fiber count and the shared uniform-pushforward theorem, and the
  generic fixed-query transcript-law theorem identifying
  `PFunPDE.transcriptLawDist` under the exact fixed-query environment with the
  fixed-input lift of the sampled output-vector law.  The migration file now
  re-exports those generic facts and keeps only a compatibility wrapper for the
  old `TranscriptLawBridge.dist` spelling while downstream imports are migrated
  to the shared module.
- `NextGen.AdaptiveLawBridge`: shared law-level application-independent CR18
  bridge from fixed-query deterministic transcript-law ratios to arbitrary
  `ProbPDE` environments.  It uses CR18 Lemma 3.2 directly:
  `transcriptLaw = systemFactor * environmentFactor`, so a ratio proved for
  every fixed query vector is multiplied by the common environment factor.  This
  replaces the old source project's stateless `URFfunOf`-specific adaptive
  bridge with a more general transcript-law statement on the `NextGen` surface.
  Totality is exposed as the meaningful law-level predicates
  `ProbPDS.KStepTotal` and `ProbPDE.KQueryTotal`; sample spaces, probability
  distributions, RVs, and representative wrappers stay out of the theorem
  boundary.  The core statistical-distance theorem uses
  `RandomSystems.statDist_le_of_one_sub_mul_le` directly, so it needs only
  finite transcript space, not decidable transcript equality.  The migration
  `AdaptiveLawBridge` module is a compatibility wrapper, while `AdaptiveBridge`
  remains as the legacy
  representative-level compatibility bridge.
- `NextGen.BoundedEnvironment` /
  `NextGen.Migration.HTechnique.BoundedEnvironment`: the generic
  environment-side bridge from a bounded q-round total chooser
  `choose_i : Y^i -> X` to a CR18 partial-function DDE now lives in the shared
  `RandomSystems.CR18` namespace.  The embedding answers exactly concrete
  output histories of length `< q` and stops on histories containing `⊥` or
  past the budget, so it introduces no dummy/default query.  It proves the
  resulting deterministic PDE is `KQueryTotal` and packages the corresponding
  nonempty subtype witness for adaptive transcript supremums.  This shared
  module also owns
  `RandomSystems.CR18.PFunPDS.Prob.boundedAdaptiveTranscriptAdvantage`, its
  image-boundedness and nonnegativity facts, and
  `boundedAdaptiveTranscriptAdvantage_le_adaptiveTranscriptAdvantage`.  The
  migration module is now only a compatibility re-export while downstream
  proofs are migrated to the shared names.
- `NextGen.Migration.HTechnique.LegacyBoundedTranscript`: explicit legacy
  reconciliation bridge.  It maps old bounded transcripts
  `Fin q -> X × Y` to CR18 transcript prefixes `(x^q,y^q)`, embeds an old
  bounded `DDS X Y q` as a CR18 partial DDS whose domain is exactly the
  nonempty input histories of length at most `q`, packages legacy `PDS`
  probability mass as the CR18 sample distribution, proves the embedded
  old system random variable is `KStepTotal q`, proves the exact vector-prefix
  evaluation law for the embedded bounded DDS, and proves that the CR18
  environment and system rectangle events are exactly the two sides of the old
  deterministic interaction transcript.  It now also proves the tight joint
  event iff and the distribution-level equality between the old bounded
  `PDS.adaptiveTranscriptDist`, pushed through `legacyTranscriptPrefix`, and the
  CR18 `PFunPDE.transcriptLawDist` for the embedded system and
  `boundedEnvironment`.  The bridge now also proves that
  `legacyTranscriptPrefix` is injective, that old adaptive transcript
  statistical distance equals the corresponding CR18 bounded-environment
  transcript-law statistical distance, and that old bounded
  `RandomSystems.advantageAdaptive`, coerced to `ℝ`, is bounded by the named
  migrated endpoint `legacyBoundedAdaptiveTranscriptAdvantage`; that endpoint
  is a compatibility wrapper around the law-level bounded-chooser supremum in
  `RandomSystems.CR18.PFunPDS.Prob` / `NextGen.BoundedEnvironment`.  The companion
  theorem `advantageAdaptive_le_of_legacyBoundedAdaptiveTranscriptAdvantage_le`
  turns any migrated real-valued bound on that endpoint back into the old
  `NNReal` `advantageAdaptive` bound.  The old `PDS` plus its probability
  assumption is packaged once as `legacyPDSRepresentative`, so the adaptive
  transcript endpoint consumes high-level representatives rather than threading
  the legacy sample distribution and embedded RV separately.  This module
  intentionally imports the
  old `RandomSystems.PDS`/`Advantage` API because it is a compatibility bridge,
  not a generic migrated proof layer.
- `NextGen.Migration.HTechnique.AdaptiveTranscriptLawAdvantage`: compatibility
  layer for law-level transcript-law adaptive advantage names.  The full
  adaptive endpoint aliases the shared core CR18
  `RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage` over
  q-query-total deterministic CR18 environments.  The old-style bounded-chooser
  spelling `boundedAdaptiveTranscriptLawAdvantage` aliases the core
  `RandomSystems.CR18.PFunPDS.Prob.boundedAdaptiveTranscriptAdvantage` from
  `NextGen.BoundedEnvironment`, along with its image-boundedness,
  nonnegativity, and restricted-supremum comparison facts.
- `NextGen.Migration.HTechnique.AdaptiveTranscriptAdvantage`: representative
  compatibility wrapper.  The representative full adaptive endpoint and
  bounded-chooser endpoint both delegate to the law-level definitions applied
  to the induced `ProbPDS` laws.  This file no longer owns an independent
  representative supremum; representative/sample-space data are kept only for
  legacy adapters.
- Generic supremum bookkeeping is factored through the upstream-candidate order
  helpers `image_univ_eq_empty_of_not_nonempty`,
  `sSup_image_univ_le_of_forall`,
  `sSup_image_univ_nonneg_of_forall`, and
  `sSup_image_univ_le_sSup_image_univ_of_forall_exists`, so application proofs
  no longer own raw `csSup` case splits.  The generic `coe_finset_sup_le`
  helper bridges old finite `NNReal` suprema into real transcript-supremum
  bounds.  SoP and the old bounded bridge now specialize these generic bridges
  instead of owning separate `csSup` proofs.
- `NextGen.Migration.HTechnique.SoP.VisibleLaw`: the first SoP application
  slice, porting the fixed visible-output compatible-count law (`Z(y)`,
  real/ideal masses, real/ideal finite distributions, visible statistical
  distance) without importing the old `RandomSystems.Applications.SoP` stack.
  It also ports the pure count identity `sum_y Z(y) = (N)_q^2`, the pointwise
  compatible-count lower bound `prod_{k<q}(|G|-2k) <= Z(y)`, the concrete
  visible mass-ratio theorem
  `(1 - q^3/|G|^2) * idealVisibleMass y <= realVisibleMass y`, and the
  real/ideal visible-law weight facts needed by the H-technique.
- `NextGen.Migration.HTechnique.SoP.TranscriptPrefix`: fixed-input lift of the
  migrated SoP visible laws to the exact CR18 transcript-prefix carrier
  `PFunPDE.TranscriptPrefix G G q`.  The lift is the deterministic pushforward
  `y^q ↦ (x^q,y^q)`, so it is tight: no default values and no over-approximated
  mismatch event.  It also proves that a one-sided visible-law H-technique
  bound transfers to the lifted fixed-input transcript-prefix laws, reusing the
  generic fixed-query bridge instead of owning environment-specific facts.
- `NextGen.Migration.HTechnique.SoP.SystemLaw`: first system-side bridge for
  the SoP application.  It defines the difference-normalized SoP
  system over two permutations, and proves that its CR18 system event is the
  expected pointwise equation `-π₁(xᵢ)+π₂(xᵢ)=yᵢ`.  The normalization matches the
  migrated compatible-count law; the ordinary sum presentation is recovered by
  negating the first sampled permutation.  The module also proves the exact
  SoP output-fiber decomposition over compatible hidden states, the exact
  cardinality of that fiber, and the resulting sampled output-vector law
  identity with `realVisibleDist`.  The ideal side is now present as the exact
  uniform-function CR18 system law and the corresponding output-vector law
  identity with `idealVisibleDist`.  The concrete fixed-query transcript-law
  distributions are then identified with the lifted visible laws through the
  generic fixed-query/function-evaluator bridge.  It now also proves the
  fixed-query SoP one-sided H-technique theorem by applying the migrated
  one-sided H-technique bound to those lifted visible laws, and the stronger
  pointwise fixed-query transcript-law lower bound with the paper's concrete
  `q^3/|G|^2` error term.  The pointwise proof now delegates the fixed-input
  split to the shared `RandomSystems.CR18.fixedInputLiftDist_pointwise_lower_bound`
  theorem, so the SoP layer only supplies the concrete real/ideal visible-law
  identities.
- `NextGen.Migration.HTechnique.SoP.Compression`: repeated-query compression
  layer from the SoP source application.  The generic compression construction
  itself now lives in `NextGen.QueryCompression`: canonical injective distinct
  query tuples, compressed-output expansion, sampled-function common
  pushforwards, query-count/cubic-bound monotonicity, transcript-prefix
  expansion, fixed-input-lift compression, and the generic function-evaluator
  transcript-law compression theorem.  The SoP module keeps source-facing names
  as thin application wrappers, proves the corresponding concrete real/ideal
  CR18 transcript-law compression identities, and closes the repeated-query
  fixed-environment SoP one-sided H-technique theorem by data processing plus
  the injective fixed-query theorem.  It also proves the pointwise
  repeated-query transcript-law lower bound by transporting the compressed
  fixed-query pointwise bound through the common deterministic transcript
  expansion and weakening the compressed error to the original `q^3/|G|^2`
  error term.  It then proves the law-level deterministic transcript-law ratio
  using the shared CR18 PMF normalization
  `RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw_pmf`, and instantiates the generic
  law-level arbitrary-environment one-sided H-technique bridge to obtain the
  corresponding `ProbPDE` transcript statistical-distance bound under the
  meaningful q-query-total environment condition.
- `NextGen.Migration.HTechnique.SoP.CompressionLegacy`: legacy representative
  compatibility layer.  It defines `normalizedSoPRepresentative` and
  `urfRepresentative`, then reexports the representative arbitrary-environment
  and fixed-query compression endpoints by delegating to the law-level
  compression facts in `SoP.Compression` and the old representative-level
  adaptive bridge.
- `NextGen.Migration.HTechnique.SoP.LawAdvantage`: public SoP application
  endpoint on the law-level transcript-advantage surface.  It packages the SoP
  PRF bound over `ProbPDS`/`ProbPDE`, delegates fixed-query and deterministic
  wrappers through the arbitrary law-level theorem, and exports the
  paper-facing bound through `SoPBoundary.sop_advPRF_le`.  The generic
  pointwise-to-supremum proof rule is exposed as
  `SecurityDefs.fixedQueryAdv_le_of_pointwise`,
  `SecurityDefs.fixedQueryAdv_le_Adv`, and
  `SecurityDefs.Adv_le_of_pointwise`, with
  `SecurityDefs.advPRF_le_of_pointwise` and
  `SecurityDefs.advPRP_le_of_pointwise` as the PRF and PRP specializations; the
  SoP PRF bound routes through the PRF wrapper.  The same module also
  exposes `SoP.filteredDelta_le_advPRF` and `SoP.filteredDelta_bound`, which
  compose the public CR18 filtered-`Delta`/transcript-`Adv` bridge with the SoP
  PRF bound; `SoPBoundary.sop_filteredDelta_le` is the paper-facing raw
  filtered distinguishing endpoint.  Public SoP endpoints no longer expose a
  separate `[Nonempty G]`
  assumption when `[AddGroup G]` is already present; the nonemptiness needed by
  the law-level ideal URF is derived locally from `0`.
- `NextGen.Migration.HTechnique.SoP.AdaptiveAdvantage`: legacy compatibility
  names for adaptive SoP transcript advantages.  The full adaptive endpoint is
  now the law-level `SoP.advPRF` endpoint from `SoP.LawAdvantage`.  The bounded
  old-style chooser name remains a legacy representative wrapper because it is
  built from `normalizedSoPRepresentative` and `urfRepresentative`, but the
  underlying generic bounded supremum is law-level.  This module remains
  build-checked through `SoPLegacyBoundary`, not through the curated public
  `Surface`.

## Reuse and automation audit follow-ups

The migration deliberately started as a self-contained proof surface, but the
next cleanup pass should reduce duplication and make the proofs feel native in
the main library:

- Done, shared permutation-count extraction: `RandomSystems.CR18.Counting.card_perm_fiber`
  and `card_perm_fiber_finset` now live in `NextGen.Counting`; the migrated
  H-technique system-law proof calls the shared permutation-fiber theorem
  directly.
- Done, shared product/birthday extraction for the migrated surface:
  `NextGen.Counting` now also owns `prod_one_sub_ge_one_sub_sum`,
  `chain_product_lower_bound`, `sum_div_range`,
  `falling_factorial_lower_bound`, and `birthday_bound`; the migrated SoP
  ratio-counting proof calls the shared chain-product theorem directly.
- Done, shared cubic query-bound arithmetic extraction:
  `NextGen.Counting` now owns `three_sum_sq_le_cube`,
  `q_le_of_cube_le_sq`, `two_mul_pred_le_of_cube_sq`,
  `twentyfive_sq_lt_four_cube`, `five_mul_le_two_of_cube`, and
  `gap_sq_bound_of_five_mul`.  `NextGen.Migration.HTechnique.Counting` now
  keeps only the concrete `sop_ratio_counting_bound` wrapper and calls the
  shared arithmetic directly; SoP visible/system-law endpoints use the shared
  `q_le_of_cube_le_sq` rather than a migration-local alias.
- Done, shared function-fiber extraction: `NextGen.Counting` now also contains
  the finite-set theorem `card_function_fiber_finset`, the tuple-facing
  `card_function_fiber_multipoint`, and the injective-on-finite-set theorem
  `card_function_injOn_finset`; the migrated density proof calls the shared
  tuple-facing theorem directly.
- Reconcile legacy `RandomSystems.CR18.SwitchingPort` against the neutral
  `NextGen.Counting` product/falling-factorial/birthday lemmas.  A direct alias
  attempt was backed out because the file currently hits an existing timeout in
  its large switching theorem; keep this as a legacy-boundary task rather than
  blocking the migrated H-technique surface.
- Continue canonicalizing permutation/function fiber-count theorems beyond the
  migrated surface.  The migration and `NextGen.SwitchingLemma` now use the
  neutral `NextGen.Counting` family, but older application files still contain
  nearby copies (`PRPPRFSwitchingGeneral`, `CTRMode`, `CBCMAC`, and
  `URFfunEval`).
- Done for uniform event mass: the CR18-local
  `RandomSystems.CR18.uniform_mass_eq_card_filter` compatibility spelling now
  delegates directly to the shared
  `RandomSystems.Dist.uniform_mass_eq_card_filter`, and migrated SoP code uses
  the shared `Dist` theorem directly.
- Continue replacing local next-gen copies of generic `Dist` facts with aliases
  or direct uses of the shared API where older boundaries still expose
  duplicate support names.
- Reconcile the two `pcoll` stories before promoting the next-gen surface:
  the closed-form CR18 `pcoll` in the legacy indistinguishability layer and the
  next-gen event/mass definition in `SwitchingLemma` need an explicit bridge,
  including the `t = 0` convention.
- Reconcile the migrated SoP visible-law counting layer with the existing
  `XoPCombinatorics`/legacy SoP transcript analysis instead of maintaining two
  independent compatible-count developments.
  Concrete overlap from the reuse audit: migrated `SoP.VisibleLaw` duplicates
  the legacy compatible-count core around `InjectiveTuple`,
  `CompatibleHiddenState`, `CompatiblePair`, `compatiblePairEquivInjectiveProduct`,
  `compatibleCountNat`, `sum_compatibleCountNat_eq_descFactorial_sq`, and
  `compatibleCountNNReal`.  The reconciliation must also account for legacy
  utilities currently absent from the migrated layer, including
  `compatibleCountNat_add_const`, `compatibleCountNNReal_add_const`,
  `compatibleCountNat_le_descFactorial`, and the `CompatibleCount` packaging in
  `XoPCounting`.  This is the highest maintenance-risk duplication in the
  migration subtree; prefer extracting or aliasing a shared SoP visible-law core
  before adding more SoP-visible counting endpoints.
- Done: replace the SoP ideal-function distribution/system wrappers with the
  standard CR18/PDS names `RandomSystems.CR18.PFunPDS.uniformP` and
  `RandomSystems.CR18.PFunPDS.urfRV`.  The fixed-query unit distribution has
  also been moved to `RandomSystems.Dist.unitProbDist` and all migration uses
  point to that shared definition.
- Done: add a proper equivalence and simp surface for `Fin q -> X` versus
  `List.Vector X q`; the fixed-input transcript embedding now uses that
  equivalence for its injectivity proof.
- In progress: rewrite older `StatDist` support lemmas against the newer
  `Dist.fTransform` API and deprecate the local copies.  The legacy
  `RandomSystems.fTransform_injective_apply` name now delegates to the shared
  `RandomSystems.Dist.fTransform_injective_apply`, preserving downstream API
  compatibility while removing the duplicate proof body.
- Extend `CR18Tactics`/simp support for transcript-law factorization,
  function-evaluator laws, fixed-query environments, deterministic
  pushforwards, one-sided density proofs, and compression/lift rewrites so the
  SoP proof can use tactic bundles rather than repeating long rewrite blocks.
  Done for fixed-query transcript-lift lower bounds:
  `RandomSystems.CR18.fixedInputLiftDist_pointwise_lower_bound` now packages the
  split on `xv = vectorOfFunction xs`, the on-fixed-input reduction to the
  output law, and the off-fixed-input zero-mass branch.
- Done, first migration-local distribution simplifier:
  `htechnique_dist_simp` contains safe facts repeatedly used by this surface:
  `TranscriptLawBridge.dist_apply`, shared `PFunPDE.transcriptLawDist`
  `apply`/`weight` rewrites, the shared
  `PFunPDE.transcriptDist_eq_mass_jointEvent` mass normalizer,
  finite-mass-function bookkeeping,
  fixed-input/lifted visible-law weights, and deterministic pushforward
  bookkeeping.  Keep this separate from raw compression rewrites, which are
  intentionally one-shot.
- Done: pointwise fixed-query ratio normalization.  The SoP-specific
  `fixedQuerySoP_transcriptLaw_lower_bound_of_visible_bound` now rewrites the
  concrete real/ideal transcript laws to lifted visible laws and calls the
  generic fixed-input lift theorem.  The earlier SoP-local visible/off-input
  macros were removed after the generic theorem made them unused.
- Done: fixed-input lift/common-pushforward compression normalization.
  `RandomSystems.CR18.fixedInputLiftDist_fTransform` now packages the recurring
  `Dist.fTransform_comp` commuting square for exact fixed-input transcript
  lifts.  `SoP.Compression.liftVisibleDist_expandCompressed` uses this shared
  theorem directly, and the old SoP-local transcript-map equality helper was
  removed after becoming unused.
- Done: remove raw transcript-law normalization hypotheses from the public
  H-technique endpoints.  `PFunPDE.transcriptLawDist` now exists as the
  canonical CR18 transcript-law distribution adapter.  The ideal
  subdistribution side is solved generically: the upstream-candidate
  `RandomSystems.Dist.sum_mass_le_weight_of_pairwise_disjoint` proves the
  finite disjoint-event mass bound; `PFunPDE.transcriptJointEvent` names the
  exact CR18 joint system/environment transcript event;
  `PFunPDE.transcriptJointEvent_unique` proves structurally that one
  system/environment sample realizes at most one length-`k` transcript prefix;
  and `PFunPDE.transcriptLawDist_weight_le_one` packages the resulting
  transcript-law `weight <= 1` theorem.  Equality of real/ideal transcript-law
  weights is now discharged structurally from totality:
  `PFunPDS.RV.KStepTotal`, `PFunPDE.RV.KQueryTotal`,
  `PFunPDE.transcriptJointEvent_exists_of_total`, and
  `PFunPDE.transcriptLawDist_weight_eq_one_of_total`.  Function-evaluator
  systems are total by `functionEvaluatorRV_KStepTotal`, and exact fixed-query
  environments are total by `fixedQueryEnvironment_KQueryTotal`.  Consequently
  the adaptive bridge exposes system/environment totality, while the SoP
  arbitrary-environment boundary exposes only the q-query-total environment
  premise; it no longer exposes a raw `h_weight`.
- Done: expose the support-scoped law-level total-weight theorem needed by the
  public bridge.  `ProbPDS.transcriptDist_weight_eq_one_of_total` proves that
  `ProbPDS.transcriptDist S E` has mass one from exactly `S.KStepTotal q` and
  `E.KQueryTotal q`; the support-subtype conversion stays inside the proof.
- Done: promote the law-level `ProbPDS` / `ProbPDE` transcript surface to core
  CR18.  The core API now owns deterministic environment embedding,
  support-totality predicates, transcript law/distribution constructors, weight
  facts, deterministic transcript distributions, and the ideal URF/URP laws.
  `TranscriptLawPublic` is now a compatibility alias layer rather than a second
  proof stack.
- Done: promote the representative-free adaptive H-technique bridge to
  `NextGen.AdaptiveLawBridge`.  The shared
  `RandomSystems.CR18.oneSided_hTechnique_law_experiment_of_fixedQuery_ratio`
  now applies the core one-sided statistical-distance theorem directly to
  `ProbPDS.transcriptDist` and uses the public law-level weight facts, rather
  than routing through `PDSRepresentative.ofProbPDS` /
  `PDERepresentative.ofProbPDE` or the migration `TranscriptLawBridge`.
- Done: promote the uniform-function fixed-query law out of H-technique.  The
  shared theorem
  `RandomSystems.CR18.uniformFunction_eval_uniform` now lives in
  `NextGen.FunctionEvaluator`; the H-technique density layer no longer owns a
  duplicate theorem or imports the CR18/PDS surface for it.
- Done: promote the generic function-evaluator transcript-law bridge out of
  H-technique.  The theorem
  `RandomSystems.CR18.transcriptLaw_fixedQueryEnvironment_functionEvaluator_dist_eq_fixedInputLiftDist`
  now lives in `NextGen.FunctionEvaluator`; the migration theorem with the same
  short name is a compatibility wrapper over the shared CR18 statement.
- Done: promote repeated-query compression itself to generic CR18 query
  infrastructure.  `NextGen.QueryCompression` now owns the input/output
  polymorphic query-image compression API:
  `queryImageSet`, `compressedQuery`, `compressedQueryIndex`,
  `expandCompressedOutputs`, the exact sampled-function pushforward lemmas, the
  compressed-cardinality and bound-monotonicity lemmas, the transcript-prefix
  expansion map, the fixed-input-lift commuting square, and the generic
  function-evaluator transcript-law compression theorem.  `SoP.Compression`
  now keeps the source-facing names only as application wrappers over the shared
  CR18 API.
- Done: split representative SoP compression compatibility into
  `SoP.CompressionLegacy`.  Public `SoP.Compression` now imports the shared
  `NextGen.AdaptiveLawBridge`, proves the deterministic/law-level ratio directly
  using `RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw_pmf`, and no
  longer mentions `PDSRepresentative` or `PDERepresentative`.
- Add a small counting-arithmetic tactic or theorem bundle for the recurring
  factorial/descending-factorial/cast/field-simp blocks in the SoP compatible
  count and system-law proofs.
- Done for the distribution-level H-technique core: `RandomSystems.StatDist`
  now owns the bad-event mass, ratio, expectation, equality-on-good,
  one-sided, pushforward, proper-probability, and mass-function forms used by
  the migrated proof.  The migrated `Density` and `TranscriptLawCore` modules
  are paper-facing wrappers over those shared theorems.  A later XoP pass can
  reuse the same theorem family for its density-ratio error-bound pattern.
- Done: mass/event-normalization tactic.  `TacticsBase` now has
  `htechnique_mass_congr` and `htechnique_mass_event` for the recurring
  `Dist.fTransform_apply_eq_mass`, `Dist.mass_congr`, and
  `transcriptSystemEvent_*_iff` pattern in function-evaluator and SoP
  system-law proofs.  `FunctionEvaluator` and `SoP.SystemLaw` use it in the
  current output-law bridges.
- In progress: `cr18_transcript` now expands the CR18 transcript-law
  factorization
  `transcriptLaw = transcriptSystemFactor * transcriptEnvironmentFactor`, and
  the migrated fixed-query/adaptive bridges use that normalizer instead of
  hand-written Lemma-3.2 rewrites.
- Extend `htechnique_dist_simp` to include the existing `dist_simp` layer from
  `RandomSystems.DistSimp` where imports permit it, then tag theorem-shaped
  bridge rewrites for fixed-query laws, lifted visible distributions, visible
  mass applications, and compression pushforwards.
- In progress: `htechnique_fixed_query_base` now lives in the lowest
  `TacticsBase` module, which depends only on the generic fixed-query
  transcript-law bridge and can therefore be used by `FunctionEvaluator`.
  `htechnique_fixed_query_core` and `htechnique_core_simp` live in
  `TacticsCore`, adding the function-evaluator law without pulling in SoP.
  `htechnique_dist_simp` is the migration-local distribution bookkeeping simp
  set for transcript-law adapters, finite mass functions, deterministic
  fixed-input lifts, and weights; repeated-query compression now uses it for
  the transcript-law adapter normalization.  `htechnique_mass_congr` and
  `htechnique_mass_event` normalize deterministic-pushforward and event-mass
  congruence goals without hard-coding application-specific event lemmas.  The
  fixed-query pointwise ratio proof now uses the theorem-shaped shared CR18
  normalizer `fixedInputLiftDist_pointwise_lower_bound` rather than SoP-local
  branch macros: first rewrite the concrete transcript laws to lifted visible
  laws, then apply the visible mass lower bound through the exact fixed-input
  lift.
  `htechnique_fixed_query`, `htechnique_compress_once`,
  `htechnique_compress`, `htechnique_simp`, and `htechnique_grind` live in the
  full SoP-aware `Tactics` module.  The low-level compression rewrite is
  deliberately one-shot so the simplifier does not keep compressing
  already-compressed query tuples.  `FunctionEvaluator` and `SoP.SystemLaw` now
  use the tactic layer for their fixed-query transcript-law reductions.  The
  next automation pass should apply these bundles in more downstream proofs and
  add only theorem-shaped rewrites that correspond to repeated source-proof
  steps.

## Migration DAG

1. **Repair the external H-technique source.**
   Work in `/h-technique` first.  Keep `HTechnique.Core`,
   `HTechnique.OneSided`, and `HTechnique.Applications.SumOfPermutations`
   building, and factor any theorem shapes that are clearly source-level rather
   than random-systems API bridges.  This establishes the reference artifact to
   migrate.

2. **Pure probability/counting core.**
   Port from `/h-technique/HTechnique/CountingLemmas.lean`.  Rehome facts that
   do not mention DDS/PDS at all:
   `Dist.pi`, `pi_apply`, constant-family bridge, Weierstrass product bound,
   falling-factorial bound, birthday bound, factorial-ratio identity, and
   switching-ratio inequality.

3. **Transcript-law H-technique core.**
   Port/adapt from `/h-technique/HTechnique/Core.lean` and
   `/h-technique/HTechnique/OneSided.lean`.
   The distribution-level density lemmas and generic finite-transcript-law
   bridge are migrated.  The remaining application work is concrete: define the
   correct bad/good transcript predicate for each proof, prove the pointwise
   density-ratio bound on good transcripts, and route the resulting advantage
   bound through Theorem 4.17 or the absorbed/per-winner filtered form.  Minimal
   hypotheses only: probability mass, the concrete event relation, and the
   exact filtered query budget needed by the theorem.

4. **URF/URP switching port.**
   Done on the `NextGen` CR18 surface.  `NextGen.SwitchingLemma` proves the
   filtered Example 4.15 conditional equivalence
   `gameOf ([q]URF) collisionCond |≡ [q]URP`, the blind collision-game birthday
   bound, and the general-alphabet CR18 switching endpoint
   `RandomSystems.CR18.urf_urp_switching`.  The proof routes through
   `theorem_4_17_filtered_of_deltaFilteredFiniteQueryNormalization_all`, so the
   `Delta` step is the paper's filtered Theorem 4.17 route rather than a
   separate H-technique theorem.

5. **SoP fixed-transcript law.**
   Port/adapt `/h-technique/HTechnique/Applications/SumOfPermutations.lean`
   first, then reconcile it with the richer in-repo SoP/XoP orbit-counting
   development.  The fixed visible law should be expressed through
   `transcriptLaw` and source-level visible projections, not through the old
   bounded `Transcript X Y q` carrier unless a bridge theorem explicitly
   identifies the two.  The visible-law mass-function layer and exact
   fixed-input `PFunPDE.TranscriptPrefix` lift are now migrated.  The exact
   fixed-query PDE environment and the generic `PFunPDE.transcriptLaw` reduction
   for arbitrary `X/Y` systems live in `NextGen.Migration.HTechnique.FixedQuery`.
   The generic function-evaluator transcript-event bridge lives in
   `NextGen.Migration.HTechnique.FunctionEvaluator`.  The normalized SoP real
   system, its pointwise system-event shape, the compatible-hidden-state fiber
   decomposition, and the exact system-factor identity with the migrated real
   visible mass are now migrated.  The ideal fixed-query system law is also
   migrated through the generic uniform-function evaluation theorem.  The
   concrete fixed-query H-technique step now closes directly against those two
   transcript-law identities.  The repeated-query transcript-prefix compression
   bridge, concrete repeated-query real/ideal transcript-law compression
   identities, repeated-query pointwise transcript-law lower bound, and
   repeated-query fixed-environment H-technique theorem are now migrated.  The
   generic adaptive bridge and its SoP instantiation give the corresponding
   pointwise ratio for arbitrary CR18 environments.  The visible-law
   compatible-count lower bound, the concrete visible mass-ratio theorem, and
   the fixed/repeated SoP H-technique bounds with the paper's concrete
   `q^3/|G|^2` error term are now migrated.  `SoPBoundary` now exposes the
   fixed-environment and arbitrary-environment transcript statistical-distance
   bounds, plus the adaptive transcript-law supremum bound and the raw CR18
   filtered distinguishing bound `sop_filteredDelta_le`.  The old-style
   bounded-chooser sub-supremum remains build-checked through the legacy
   boundary.  The exact law equality from legacy bounded transcript
   distributions to the CR18 `boundedEnvironment` transcript laws, the
   corresponding statistical-distance equality, and the finite
   `advantageAdaptive` to named bounded transcript-supremum bridge are now in
   `LegacyBoundedTranscript`, including the `NNReal` bound-transfer theorem.
   The public SoP transcript-law endpoints and legacy bounded names now build;
   the remaining cross-surface work is the reusable CR18/thesis advantage
   comparison/alias layer and exact old/new application equivalence aliases.

6. **SoP adaptive/application theorem.**
   Reprove the existing SoP/XoP application endpoints against the migrated
   fixed-transcript law.  Acceptance requires the current key endpoints to
   remain available, especially the `xop_adaptiveAdvantage_*` and
   `visibleStatDist_*` families, with names either preserved or replaced by
   explicit deprecation aliases.

7. **Surface flip.**
   Once `NextGen.Migration.HTechnique.All` no longer imports `RandomSystems.*`
   for H-technique or SoP, rename the `NextGen` surface to the main
   random-systems surface and deprecate the old modules with thin aliases.

## Follow-up cleanup backlog

These are not blockers for the current H-technique migration boundary: the
aggregate target builds and the migration subtree has no `sorry`/`private`
hits.  They should be handled before the surface flip so the new API feels
native rather than migrated.

- Remove duplicate distribution support facts from `RandomSystems.StatDist`
  once they are covered by `RandomSystems.Dist`.  The migrated H-technique
  theorem statements now use the shared `RandomSystems.statDist` name directly;
  the remaining work is to make the surrounding distribution API native enough
  that the surface flip does not carry compatibility-only support lemmas.
- Done for the local H-technique ratio/deficit algebra: the NNReal deficit
  lemma and the one-sided density-to-statistical-distance theorem now live in
  `RandomSystems.StatDist`, and `NextGen.Migration.HTechnique.Density` calls
  them directly.  Remaining automation work is smaller: expose simplification
  support for bad-event mass sums and the proof-internal `Finsupp.sum_fintype`
  expansions still visible in the ratio/expectation variants.
- Extend the CR18/dist simplifier stack (`cr18_simp`, `cr18_grind`,
  `dist_simp`) with the H-technique pushforward/compression rewrites that are
  currently invoked manually.
- Move any remaining duplicated finite-counting facts to neutral shared modules
  as they become part of active migrated proofs.
- Replace the fixed-query vector/function adapter with a thin wrapper around
  Mathlib's vector/function equivalence (`Equiv.vectorEquivFin` and related
  `List.Vector` simp lemmas), then add domain-specific simp bridge lemmas.
- Decide whether SoP transcript-prefix wrappers should remain as source-facing
  aliases over `FixedQuery`; if they remain, register simp bridge lemmas so
  downstream proofs do not manually unfold both layers.
- Extract the SoP/XoP compatible-count combinatorics into a dependency-light
  shared module, then have both the legacy SoP/XoP stack and the migrated
  H-technique SoP proof import or alias that core.  This should reconcile the
  migrated `CompatibleHiddenState`/`compatibleCountNat` layer with the existing
  `RandomSystems.Applications.XoPCombinatorics` and XoP density-certificate
  abstractions.
- Before the surface flip, prove explicit equivalence aliases between the
  migrated SoP visible masses/statistical distance and the legacy SoP
  `Transcript`/`TV` objects, so the normalized presentation cannot drift from
  existing application semantics.
- Reconcile the migrated fixed-query uniform-function theorem with the older
  `RandomSystems.Instances.URFfunEval` infrastructure; keep the dependency-light
  theorem in the shared surface and make the legacy/migration modules reuse it.
- Reconcile `RandomSystems.CR18.Counting.card_function_fiber_multipoint` with
  `RandomSystems.Instances.URFfunEval.card_fiber_multipoint`, and reconcile the
  shared `RandomSystems.CR18.uniformFunction_eval_uniform` theorem with
  `URFfunEval.eval_nonces_uniform`.  Keep one shared theorem family and expose
  compatibility aliases only where needed.
- Done: promote the generic `FixedQuery` and `FunctionEvaluator` bridge facts
  out of the H-technique migration namespace.  They now live in
  `NextGen.FixedQuery` and `NextGen.FunctionEvaluator` under
  `RandomSystems.CR18`; the migration files are compatibility re-exports while
  downstream files are moved to the shared names.
- Done: add transcript-law total-weight lemmas for total/function-evaluator
  systems.  Arbitrary-environment endpoints now discharge the previous
  explicit `h_weight` side condition structurally from totality.  The ideal
  `weight <= 1` side condition is already discharged generically by
  `PFunPDE.transcriptLawDist_weight_le_one`.
- Done: replace the migration-local `unitProbDist : ProbDist PUnit.{1}` with
  the shared `RandomSystems.Dist.unitProbDist`.  Fixed-query environment uses
  intentionally instantiate it at universe `.{0}` (`PUnit.{1}`) so theorem
  declarations do not retain universe metavariables.
- Reuse-audit follow-up: now that the bounded-chooser adaptive endpoint has
  been promoted out of the migration namespace, reconcile it with the existing
  legacy `RandomSystems.DDE.equivChoose` equivalence instead of leaving a
  second chooser-indexing API.  The current shared statement intentionally uses
  the raw chooser family because it is exactly both the old `DDE.choose`
  projection and the input to the shared CR18 `boundedDDE` constructor.

## Acceptance gates

- `lake build NextGen.Migration.HTechnique.All`
- `/h-technique`: `lake build HTechnique.Core HTechnique.OneSided`
- `/h-technique`: `lake build HTechnique`
- `lake build NextGen`
- no new `sorry` in migrated files
- no meaningful migrated lemma marked `private`
- every theorem in the migrated path cites its source status:
  `source theorem` or `support lemma forced by formalization`
- SoP application endpoints still build after the legacy SoP import is removed

## Immediate next tasks

1. Freeze the application gate:
   SoP and fixed-query HashThenPRF are on the migrated surface, and the main
   source-facing endpoint names are preserved:
   `sop_prf_advantage`, `sop_statDist_rfDist_le`,
   `sopFixedQueryAdvantage`, `sopFixedQueryAdvantage_le`,
   `sop_advPRF_le`, and `hashThenPRF_security`.  The downstream audit in
   `DOWNSTREAM.md` found one source-name support alias that is worth keeping:
   HashThenPRF `badPred`, as the migrated bad event predicate.  Treat old
   concrete carriers such as `sopDist`, `urfDist`, and `rfDist` as support-only
   proof shapes unless a downstream caller needs a temporary deprecation alias.
2. Promote the curated H-technique surface plan:
   keep `Surface`, `SecurityDefs`, `SoPBoundary`, `Density`, and
   `HashThenPRF`, plus the concrete strong/tweakable model module `StrongPRP`,
   as the application-facing API; quarantine
   `PDSRepresentative`, `PDERepresentative`, representative transcript
   bridges, bounded legacy endpoints, and switching-heavy compatibility gates
   behind non-surface imports.
3. Use the migrated `advSPRP`, `advTPRP`, and `advTSPRP` only through
   `StrongPRP`, where the concrete ideal laws are constructed internally.
   The next task is to migrate HCTR2's real systems to the `QueryDir × X`,
   `T × X`, or `QueryDir × T × X` law-level input shapes rather than carrying
   the old free-ideal wrappers forward.
4. Start extracting the remaining shared compatible-count/fiber-count core
   before the migration namespace becomes an accidental second library.
5. Apply the migration-local H-technique tactic layer only where downstream
   bridge/application proofs still repeat source-proof rewrites.
