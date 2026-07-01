# External H-technique source inventory

Source project:

```text
/Users/marcilunga/Documents/ToB/research/fv/h-technique
```

The source project depends on this repository:

```lean
require RandomSystems from ".." / "random-systems"
```

Therefore `random-systems` cannot import `HTechnique` as a Lake dependency
without creating a cycle.

The migration order is:

1. repair and factor the external `/h-technique` project;
2. port the stabilized source declarations into `NextGen`;
3. reconcile old random-systems APIs and applications with the migrated
   surface.

This inventory names the external source declarations that need that treatment.

## Source modules to port

- `HTechnique/Core.lean`
  - `FuncCompatible`
  - `PermCompatible`
  - `Transcript`
  - `BadPredicate`
  - `probBad`
  - `uniformFunction_eval_uniform`
  - `fTransform_ratio_lower`
  - `oneSided_hTechnique_fTransform`
  - `hTechnique_ratio`
  - `hTechnique_expectation`
  - `hTechnique_eq_on_good`
  - `oneSided_hTechnique`
  - `oneSided_hTechnique_proper`
- `NextGen.PDS` transcript-law surface
  - `PFunPDE.TranscriptPrefix`
  - `PFunPDE.TranscriptLaw`
  - `PFunPDE.transcriptLaw`
  - `PFunPDE.transcriptLaw_eq_systemFactor_mul_environmentFactor`
  - environment side uses `PFunPDE.RV Ω X Y`, i.e. random DDEs
    `List (Option Y) → Option X`, so fixed/adaptive environments can emit the
    first query from the empty output history.
- `HTechnique/OneSided.lean`
  - stateless adaptive transcript compatibility lemmas
  - `oneSided_hTechnique_adaptive`
  - `oneSided_hTechnique_adaptive_proper`
  - `adaptive_ratio_of_fixed_query_ratio_URFfunOf`
- `HTechnique/CountingLemmas.lean`
  - Weierstrass product inequality
  - `sum_div_range`
  - `two_sum_sq_le_cube`
  - `chain_product_lower_bound`
  - falling-factorial and birthday bounds
  - `three_sum_sq_le_cube`
  - `q_le_of_cube_le_sq`
  - `two_mul_pred_le_of_cube_sq`
  - `five_mul_le_two_of_cube`
  - `gap_sq_bound_of_five_mul`
  - `sop_ratio_counting_bound`
- `HTechnique/SecurityDefs.lean`
  - paper-facing PRF advantage wrappers
- `HTechnique/Applications/SumOfPermutations.lean`
  - `sopDist`
  - `urfDist`
  - `rfDist`
  - `sopFunctionDist`
  - `sopPDS`
  - `sop_ratio_lower_bound`
  - `sop_prf_advantage`
  - `sop_advPRF_le`
- `HTechnique/Applications/HashThenPRF.lean`
  - `hashThenPRF_security`

## Promotion matrix

The migration preserves source theorem names only when the current CR18
law-level object is already modeled.

- **Promoted security endpoints:** `advPRF`, `advNPRF`, `advPRP`, `advNPRP`,
  `advNPRF_le_advPRF`, and `advNPRP_le_advPRP`.  Their migrated statements
  take construction laws as `ProbPDS` inputs and construct the URF/URP ideals
  and fixed-query environments inside the definitions.
- **Promoted SoP endpoints:** `sop_prf_advantage`,
  `sop_statDist_rfDist_le`, `sopFixedQueryAdvantage`,
  `sopFixedQueryAdvantage_le`, and `sop_advPRF_le`.  They are exported through
  `NextGen.Migration.HTechnique.SoPBoundary` over the migrated CR18
  transcript-law surface.  The old source carriers `sopDist`, `urfDist`, and
  `rfDist` are proof/support shapes, not new public endpoints.
- **Promoted HashThenPRF endpoint:** `hashThenPRF_security`, exported through
  `NextGen.Migration.HTechnique.HashThenPRF` as a law-level fixed-query
  transcript-distance theorem.  The downstream-used source support name
  `badPred` is also preserved there as an alias for the migrated bad event
  predicate.
- **Promoted strong/tweakable PRP model endpoints:** `QueryDir`, `strongURP`,
  `tweakableURP`, `tweakableStrongURP`, `advSPRP`, `advTPRP`, and
  `advTSPRP`, exported through `NextGen.Migration.HTechnique.StrongPRP`.  The
  migrated advantage names construct the ideal law internally instead of taking
  an `ideal` system as a free parameter.
- **Support-only internals:** counting/fiber lemmas, source visible-output
  distributions, compression adapters, fixed-query DDE construction details,
  and representative bridges.  These are preserved as proof support only when
  needed by public endpoints.
- **Still compatibility-only:** old bounded-system carriers, representative
  transcript bridges, and bad-event wrappers remain support/legacy shapes unless
  a downstream caller requires a deliberate deprecation alias.

`DOWNSTREAM.md` records the current workspace callers that still import the
external package and classifies which compatibility names are actually needed.

## Current source build status

As of this migration scaffold:

```bash
cd /Users/marcilunga/Documents/ToB/research/fv/h-technique
lake build HTechnique
```

builds in the current worktree, including
`HTechnique.Applications.SumOfPermutations` and
`HTechnique.Applications.HashThenPRF`.  The SoP application remains the main
adaptive application gate; HashThenPRF is now tracked as a fixed-query
application gate for the `NextGen` migration.

## Current migrated status

- The curated migration import is
  `NextGen.Migration.HTechnique.Surface`.  This is the API checkpoint for the
  future promotion out of `Migration`: its direct public H-technique/security
  and application statements are law-level, using `ProbPDS`, `ProbPDE`,
  deterministic CR18 environments, fixed-query transcript distributions, and
  concrete application parameters rather than raw sample spaces or
  representative wrappers.  The
  legacy bounded bridge and the switching-heavy `LegacyBoundary` remain
  compatibility/build gates imported by `NextGen.Migration.HTechnique.All`, not
  by the future-promotion surface.  The aggregate `All` builds this surface,
  those compatibility gates, and proof automation.  The current surface is
  statement-clean and the public SoP/HashThenPRF paths are
  representative-bridge-clean:
  representative modules such as `TranscriptLaw`, `FixedQuery`, and
  `AdaptiveBridge` are confined to legacy/compatibility paths, while the public
  SoP path uses the shared `NextGen.AdaptiveLawBridge`, `FixedQueryLaw`,
  `TranscriptLawPublic`/`TranscriptLawCore`, and law-level SoP support modules.
  The HashThenPRF fixed-query endpoint lives in
  `NextGen.Migration.HTechnique.HashThenPRF`; it constructs the concrete
  hash-then-PRF `ProbPDS` and ideal URF law in the theorem statement, with the
  paper's extended `(y^q, h)` distributions kept as proof support.  The migrated
  `hashThenPRF_security` theorem preserves the source theorem name on the
  law-level statement.
  Since Lean exposes theorem proof dependencies transitively, the future
  promotion surface is convention-based: direct endpoint modules and theorem
  headers are public-audited, while proof-support declarations remain in
  support namespaces.
  `TranscriptLawPublic` now aliases the core
  `RandomSystems.CR18.PFunPDS.Prob` / `PFunPDE.Prob` transcript-law API, so the
  migration no longer maintains a parallel law-level transcript implementation.
  The thesis-style q-query environment index and law-level adaptive transcript
  advantage are core CR18 declarations as well; `SecurityDefs.Adv`,
  `SecurityDefs.advPRF`, and `SecurityDefs.advPRP` wrap that core law-level
  supremum instead of rebuilding it in the migration layer.  The non-adaptive
  source names `advNPRF`/`advNPRP` wrap the generic law-level fixed-query
  supremum `SecurityDefs.fixedQueryAdv`.  The PRP wrappers use the core
  law-level ideal `RandomSystems.CR18.PFunPDS.Prob.urp`.
  The bounded old-style chooser transcript supremum is law-level too:
  `boundedAdaptiveTranscriptLawAdvantage` takes only two `ProbPDS` laws and
  embeds chooser families through `RandomSystems.CR18.boundedDDE`.  The core
  declaration lives in `NextGen.BoundedEnvironment` under
  `RandomSystems.CR18.PFunPDS.Prob`; the migration name is a compatibility
  alias.  The representative bounded endpoint and the old finite
  `advantageAdaptive` bridge are compatibility wrappers over that law-level
  object.
  The CR18 raw-advantage reconciliation has also started on shared API:
  `RandomSystems.mass_sub_mass_le_statDist` gives the generic event/statistical
  distance bound, exact-query environments are admitted through
  `RandomSystems.CR18.PFunPDE.DDEKQueryTotal_of_queriesExactly`, and
  `RandomSystems.CR18.maxAdvantage_filterQueries_le_adaptiveTranscriptAdvantage`
  supplies the filtered `Delta` to base thesis transcript-`Adv` bridge.  The
  exact-query theorem identifying a distinguisher verdict with a transcript-law
  event and its probabilistic distinguisher lift are proved in
  `NextGen.AdaptiveLawBridge`; the base-law/filtered-law transcript comparison
  is proved there too.  The curated migration security surface re-exports this
  reconciliation as `SecurityDefs.filteredDelta_le_Adv`, with only law-level
  `ProbPDS` systems as theorem inputs.
- Generic counting facts are ported in `NextGen.Counting`, including product
  and birthday arithmetic, cubic query-bound arithmetic, and
  function/permutation fiber counts for prescribed finite assignments.
  `NextGen.Migration.HTechnique.Counting` now keeps the concrete
  `sop_ratio_counting_bound` application wrapper.
- Distribution-level H-technique facts are now shared API in
  `RandomSystems.StatDist`: bad-event mass, ratio, expectation,
  equality-on-good, one-sided, common-pushforward one-sided,
  proper-probability, and finite-mass-function wrappers.  The migration
  `Density` and `TranscriptLawCore` modules are paper-facing wrappers over that
  shared API.  The deterministic-pushforward support facts and the
  finite-mass-function distribution adapter needed by this layer have been
  moved to the shared `RandomSystems.Dist` API, along with the uniform-event
  cardinality-ratio lemma and the uniform-pushforward theorem for maps with
  equal fiber cardinalities used by concrete counting bridges.  Supremum/order
  helpers used by advantage definitions now live in `RandomSystems.StatDist`
  too, including the finite `NNReal` supremum transfer lemma used by the legacy
  bounded bridge.
- Finite transcript-law mass functions, including the current
  `PFunPDE.transcriptLaw` API, are bridged to the distribution-level facts in
  `NextGen.Migration.HTechnique.TranscriptLaw` through
  `RandomSystems.Dist.ofFiniteMassFunction`.  The concrete experiment bridge is
  stated over PDE environments, not dual PDSs, and now takes bundled
  `PDSRepresentative` system inputs plus a bundled `PDERepresentative`
  environment input rather than exposing sample spaces, probability
  distributions, and RVs separately.  The CR18 transcript carrier is exposed
  through the named migration surface `TranscriptPrefix X Y q`; finite and
  decidable transcript-space requirements are written as
  `FiniteTranscriptSpace X Y q` and `DiscreteTranscriptSpace X Y q`, with
  decidable equality kept only on the statements that actually use finite-sum
  H-technique lemmas.
- The legacy bounded transcript reconciliation bridge is migrated in
  `NextGen.Migration.HTechnique.LegacyBoundedTranscript`.  It embeds old
  bounded transcripts and bounded `DDS`/`DDE` interaction into the CR18
  transcript-prefix, partial-DDS, and bounded-environment surface, and proves
  the exact distribution equality between the old
  `PDS.adaptiveTranscriptDist` pushed through `legacyTranscriptPrefix` and the
  CR18 `PFunPDE.transcriptLawDist` for the embedded system and environment.
  It also proves the injective-embedding statistical-distance equality and the
  finite old `advantageAdaptive` bound by the named migrated CR18
  bounded-chooser transcript supremum, plus the `NNReal` bound-transfer theorem
  used by legacy endpoint aliases.  The bounded-chooser supremum itself is
  law-level in `RandomSystems.CR18.PFunPDS.Prob` /
  `NextGen.BoundedEnvironment`; the old `PDS` boundary is packaged as
  `legacyPDSRepresentative` only for the compatibility wrapper.
- The fixed-query CR18 bridge is migrated in
  `NextGen.Migration.HTechnique.FixedQuery`.  It is generic over input/output
  types `X/Y`, exposes the canonical equivalence between query-indexed
  functions `Fin q -> X` and CR18 length-indexed vectors `List.Vector X q`,
  constructs the exact fixed-query DDE/PDE environment, defines the generic
  fixed-input transcript-prefix embedding/lift, and proves the environment-event,
  environment-factor, and transcript-law reduction facts needed by fixed-query
  H-technique applications.
- The function-evaluator CR18 bridge lives on the shared `NextGen.FunctionEvaluator`
  / `RandomSystems.CR18` surface.  It embeds sampled functions through
  `PFunDDS.functionEvaluator`, proves the generic pointwise transcript-system
  event characterization used by concrete applications, reuses
  `PFunDDS.functionEvaluator_output` for the basic evaluation bridge, and owns
  the generic fixed-query law identifying a function-evaluator transcript law
  with the fixed-input lift of the sampled output-vector law.  The migration
  `FunctionEvaluator` module is now only a stable export/import shim; concrete
  H-technique endpoints reuse the shared CR18 theorem instead of restating raw
  sample-space/function hypotheses locally.
- The fixed visible-output SoP law from the old `SoP.Transcript` / `SoP.TV`
  layer is migrated in `NextGen.Migration.HTechnique.SoP.VisibleLaw`, including
  the compatible-count sum identity and real/ideal visible-law weight facts.
- The exact fixed-input lift of the migrated SoP visible law to
  `PFunPDE.TranscriptPrefix G G q` is migrated in
  `NextGen.Migration.HTechnique.SoP.TranscriptPrefix`; it now reuses the
  generic fixed-query bridge rather than owning environment-specific facts.
- The first concrete SoP system bridge is migrated in
  `NextGen.Migration.HTechnique.SoP.SystemLaw`.  It instantiates the generic
  function-evaluator bridge to the difference-normalized SoP system
  `x ↦ -π₁(x)+π₂(x)`, matching the
  compatible-count coordinates used by `SoP.VisibleLaw`.  It now also proves
  the exact concrete event-fiber decomposition over compatible hidden states,
  the resulting fiber cardinality, and the sampled output-vector law identity
  with the migrated real visible-output distribution.  The ideal system law is
  migrated as well: the source-level uniform-function fixed-query theorem is
  mirrored in `Density`, then used to identify the ideal output-vector law with
  `idealVisibleDist`.  It now closes the
  fixed-query SoP one-sided H-technique step by routing the concrete CR18
  transcript-law distributions through the generic fixed-query/function-evaluator
  bridge.
- The repeated-query compression layer is migrated in
  `NextGen.Migration.HTechnique.SoP.Compression`.  It gives the canonical
  injective compressed query vector, the expansion map back to original repeated
  query positions, the sampled-function evaluation pushforward identity, the
  monotone cubic-bound bridge, the transcript-prefix pushforward identity, the
  concrete real/ideal CR18 transcript-law compression identities, and the
  repeated-query fixed-environment SoP one-sided H-technique theorem.  It also
  proves the law-level deterministic transcript-law ratio and the arbitrary
  `ProbPDE` SoP transcript statistical-distance bound using the shared
  `RandomSystems.CR18.oneSided_hTechnique_law_experiment_of_fixedQuery_ratio`
  from `NextGen.AdaptiveLawBridge`.
- Representative SoP compression compatibility now lives in
  `NextGen.Migration.HTechnique.SoP.CompressionLegacy`, including
  `normalizedSoPRepresentative`, `urfRepresentative`, the representative
  arbitrary-environment endpoint, and the representative fixed-query endpoint.
- The public adaptive/application SoP endpoint is migrated in
  `NextGen.Migration.HTechnique.SoP.LawAdvantage` and exported through
  `NextGen.Migration.HTechnique.SoPBoundary`.  It packages the SoP PRF bound on
  the law-level `ProbPDS` / `ProbPDE` transcript-law advantage surface, rather
  than exposing representatives or underlying sample spaces/RVs.  The public
  SoP boundary now assumes only `[AddGroup G] [Fintype G] [DecidableEq G]`; the
  nonemptiness needed by the law-level ideal URF is derived internally from the
  group zero instead of appearing as a separate theorem hypothesis.
  `SecurityDefs.Adv` is the thesis-style law-level transcript advantage wrapper,
  `SecurityDefs.fixedQueryAdv` is the non-adaptive fixed-query transcript
  advantage wrapper,
  `SecurityDefs.advPRF` specializes it to the PRF-vs-URF comparison,
  `SecurityDefs.advNPRF` is the corresponding fixed-query PRF comparison,
  `SecurityDefs.advPRP` specializes it to the PRP-vs-URP comparison,
  `SecurityDefs.advNPRP` is the corresponding fixed-query PRP comparison,
  `SoP.advPRF` specializes that to normalized SoP, and
  `SoPBoundary.sop_advPRF_le` is the migrated paper-facing SoP PRF endpoint.
  The old fixed-query source names are also available on the public boundary:
  `SoPBoundary.sop_statDist_rfDist_le`, `SoPBoundary.sopFixedQueryAdvantage`,
  and `SoPBoundary.sopFixedQueryAdvantage_le`, stated over migrated CR18
  transcript distributions rather than the old `sopDist`/`rfDist` carriers.
  `SoP.filteredDelta_le_advPRF`, `SoP.filteredDelta_bound`, and
  `SoPBoundary.sop_filteredDelta_le` expose the raw CR18 filtered
  distinguisher route for the concrete normalized SoP/URF pair; filtered
  finite-query normalization is proved internally from totality of those
  function-evaluator laws.
  Function-evaluator totality is now shared through
  `RandomSystems.CR18.functionEvaluatorProb_KStepTotal`,
  `RandomSystems.CR18.functionEvaluatorProb_totalOnNonempty`, and
  `RandomSystems.CR18.PFunPDS.Prob.urf_KStepTotal`, with SoP-specific
  specializations in `SoP.SystemLaw`.
  The legacy `SoP.AdaptiveAdvantage.adaptiveTranscriptAdvantage` name now
  aliases the law-level `SoP.advPRF` endpoint.  The remaining
  `SoP.AdaptiveAdvantage` bounded-chooser name is a legacy representative
  wrapper over the law-level bounded supremum, exported only through
  `SoPLegacyBoundary`.
  The pointwise-to-supremum proof rule is available under the same surface as
  `SecurityDefs.fixedQueryAdv_le_of_pointwise`,
  `SecurityDefs.fixedQueryAdv_le_Adv`, `SecurityDefs.Adv_le_of_pointwise`, and
  `SecurityDefs.advPRF_le_of_pointwise`, with
  `SecurityDefs.advPRP_le_of_pointwise` as the adaptive PRP specialization.
  The old strong/tweakable PRP source names now have concrete CR18 law-level
  ideal systems in `StrongPRP`; the remaining work is to migrate downstream
  real-system constructions such as HCTR2 onto those endpoints.
