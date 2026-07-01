# H-technique migration status

This folder is the staging area for moving the H-technique and its SoP
application onto the NextGen/CR18 transcript-law surface before promoting it to
the main random-systems API.

## Current gates

- Build gate: `lake build NextGen.Migration.HTechnique.All`
- Curated surface: `NextGen.Migration.HTechnique.Surface`
- Layer-by-layer migration audit: `COMPONENT_ROADMAP.md`
- Application/model boundaries: `NextGen.Migration.HTechnique.SoPBoundary`,
  `NextGen.Migration.HTechnique.HashThenPRF`, and
  `NextGen.Migration.HTechnique.StrongPRP`
- Last checked: 2026-07-01; `lake build NextGen.Migration.HTechnique.All`,
  `lake build NextGen.SwitchingLemma`, `lake build NextGen.Counting`,
  `lake build RandomSystems.Transcript`,
  `lake build RandomSystems.Instances.URF`,
  `lake build NextGen.Migration.HTechnique.LegacyStatelessBridge`, and the
  downstream checks `lake build HCTR2.Proofs.Concrete.Games` /
  `lake build HCTR2.Proofs.Concrete.Transcripts` /
  `lake build HCTR2.Proofs.Concrete.Switching` /
  `lake build HCTR2.Proofs.Concrete.MainLemma` /
  `lake build HCTR2.Proofs.Concrete.BirthdayEngine` /
  `lake build HCTR2.Proofs.Concrete.PaperTargetCore` /
  `lake build HCTR2.Proofs.Concrete.PaperTarget` /
  `lake build HCTR2.Proofs.Concrete.PaperTargetSection26` /
  `lake build HCTR2.Proofs.Concrete.PaperTargetSimulator` build.  In the external
  `/h-technique` project, `lake build HTechnique.Core HTechnique.OneSided
  HTechnique.Applications.SumOfPermutations
  HTechnique.Applications.HashThenPRF` builds.
- Current application scope has moved past **SoP-first**.  The migrated surface
  preserves the old SoP endpoint names on `SoPBoundary`, adds the raw CR18
  filtered distinguishing endpoint, and now includes the fixed-query
  HashThenPRF transcript-distance endpoint on the CR18 law-level surface.

## Surface audit

- Direct `Surface` imports are `Density`, `HashThenPRF`, `SecurityDefs`,
  `SoPBoundary`, and `StrongPRP`.
- Direct public security, SoP, and HashThenPRF theorem headers are law-level:
  they mention
  `ProbPDS`, `ProbPDE`, deterministic CR18 environments, fixed-query
  transcript distributions, concrete SoP parameters, and concrete hash-family
  parameters.  They do not expose raw sample spaces, raw probability carriers,
  RV parameters,
  `PDSRepresentative`, or `PDERepresentative`.
- `SoPLegacyBoundary`, `LegacyBoundary`, old bounded transcript endpoints, and
  representative adaptive advantage endpoints are build-checked through `All`,
  not through `Surface`.
- The public SoP proof path now imports the shared `NextGen.AdaptiveLawBridge`,
  `FixedQueryLaw`,
  `TranscriptLawPublic`/`TranscriptLawCore`, and law-level SoP support modules.
  It no longer imports the representative bridge modules `AdaptiveBridge`,
  `TranscriptLaw`, or `FixedQuery`; those remain behind legacy/compatibility
  gates.  Lean imports expose proof-support declarations transitively, so the
  promotion policy is convention-based: `Surface` is audited by its direct
  public theorem headers and documented endpoint modules, while support
  declarations stay in support namespaces rather than being treated as hidden.

## Done

- The migration aggregate builds.
- The migrated folder has no Lean `sorry`, `admit`, or `axiom`.
- Public transcript-law objects now live in `TranscriptLawPublic`; the
  representative wrappers and support lemmas remain in `TranscriptLaw`.
  `TranscriptLawPublic` is now a compatibility layer over the core
  `RandomSystems.CR18.PFunPDS.Prob` / `PFunPDE.Prob` transcript-law API rather
  than a parallel implementation.
- `PDSRepresentative.ofProbPDS` is now support-based, matching
  `PDERepresentative.ofProbPDE`: representative-side totality and transcript
  factors range over exactly the systems in the PDS law's support.
- Law-level system totality is exposed as `ProbPDS.KStepTotal`, with
  `ProbPDS.KStepTotal_pmf_of_rv` as the PMF constructor bridge from CR18 random
  variables.
- Public fixed-query transcript distributions now live in `FixedQueryLaw`; the
  representative fixed-query adapter remains in `FixedQuery`.
- `FixedQueryLaw` is clean support: it exposes the law-level
  `ProbPDS.fixedQueryTranscriptDist` facade only.  The source-name
  function-evaluator wrapper `ProbPDS.fixedQueryTranscriptDist_functionEvaluator`
  is isolated in the migration-only `FixedQueryCompatibility` module; public
  application proofs use the owner-level CR18 theorem directly.
- Deterministic CR18 environments can now be embedded as law-level PDEs via
  `ProbPDE.ofDDE`, with `ProbPDE.ofDDE_KQueryTotal` and
  `ProbPDS.transcriptDist_ofDDE` bridging deterministic transcript laws to the
  arbitrary `ProbPDE` theorem surface.
- Law-level CR18 transcript distributions now have public weight facts:
  `ProbPDS.transcriptDist_weight_le_one` and
  `ProbPDS.transcriptDist_weight_eq_one_of_total`.  The equality theorem has
  only the meaningful support-totality premises `ProbPDS.KStepTotal` and
  `ProbPDE.KQueryTotal`; support-subtype conversion is internal to the proof.
- PMF-induced deterministic transcript laws have the shared CR18 normalization
  fact `RandomSystems.CR18.PFunPDE.deterministicTranscriptLaw_pmf`, so
  law-level deterministic proofs can reuse sampled-RV transcript laws without
  importing representative adapters.
- Public SoP boundary theorems are stated over law-level `ProbPDS` / `ProbPDE`
  or over concrete SoP parameters, not raw sample spaces.
- `HashThenPRF` now contains the migrated fixed-query application endpoint:
  `HashThenPRF.hashThenPRF_fixedQueryTranscript_bound`.  The theorem compares
  the CR18 fixed-query transcript distribution of the concrete hash-then-PRF
  `ProbPDS` with the ideal URF `ProbPDS`, and bounds it by
  `choose2 q * eps`.  The paper's extended `(y^q, h)` distributions are proof
  support only, not public theorem inputs.  The source-facing name
  `HashThenPRF.hashThenPRF_security` is now a thin compatibility wrapper around
  the same law-level endpoint.
- Thesis-style `Adv`, fixed-query `fixedQueryAdv`, `advPRF`, `advNPRF`,
  `advPRP`, and `advNPRP` endpoints are stated over `ProbPDS`.  The PRP
  endpoints use the core law-level ideal
  `RandomSystems.CR18.PFunPDS.Prob.urp`, not a migration-local permutation
  wrapper.
- Public adaptive transcript advantage now lives on the shared CR18
  `RandomSystems.CR18.PFunPDS.Prob` surface; `AdaptiveTranscriptLawAdvantage`
  preserves migration-facing names.  Representative and old bounded adaptive
  transcript advantages remain in `AdaptiveTranscriptAdvantage` as support.
- The representative-level `adaptiveTranscriptAdvantage` is now a compatibility
  wrapper over the law-level `adaptiveTranscriptLawAdvantage` applied to the two
  induced `ProbPDS` laws.  The duplicated representative supremum was removed;
  the representative-level bounded endpoint is also a compatibility wrapper.
- The old-style bounded-chooser adaptive transcript supremum now has a
  law-level definition,
  `boundedAdaptiveTranscriptLawAdvantage : ProbPDS X Y -> ProbPDS X Y -> Real`,
  as a compatibility spelling for
  `RandomSystems.CR18.PFunPDS.Prob.boundedAdaptiveTranscriptAdvantage` from
  `NextGen.BoundedEnvironment`.  It is the tight supremum over chooser families
  embedded through `RandomSystems.CR18.boundedDDE`, with no
  representative/sample-space parameters.
- The generic comparison
  `boundedAdaptiveTranscriptLawAdvantage_le_adaptiveTranscriptLawAdvantage`
  embeds each bounded chooser as a q-query-total CR18 environment and compares
  the restricted supremum with the full thesis-style environment supremum.
- `LegacyBoundedTranscript` now proves the old finite
  `RandomSystems.advantageAdaptive` bound by this law-level bounded object via
  the representative compatibility wrapper; the representative layer is only
  the legacy adapter, not the mathematical supremum.
- `Adv` is now a direct law-level adaptive transcript supremum
  (`adaptiveTranscriptLawAdvantage`); it no longer builds canonical
  representatives in the public definition.
- Pointwise law-level security hypotheses use deterministic CR18 transcript
  distributions through `ProbPDS.deterministicTranscriptDist`.
- The generic law-level adaptive H-technique bridge now lives on the shared
  `NextGen.AdaptiveLawBridge` / `RandomSystems.CR18` surface as
  `RandomSystems.CR18.oneSided_hTechnique_law_experiment_of_fixedQuery_ratio`:
  fixed-query deterministic transcript-law ratios imply an arbitrary law-level
  `ProbPDE` transcript-distance bound under the meaningful q-totality premises,
  without converting through `PDSRepresentative`/`PDERepresentative` in the
  theorem proof.  The core statement no longer needs a decidable transcript-space
  hypothesis; the migration `AdaptiveLawBridge` module is now compatibility only.
- The SoP adaptive PRF bound now uses a named law-level pointwise bridge
  (`SoP.repeatedQuerySoP_law_experiment_bound`) instead of inlining
  representative rewrites in the public theorem proof.
- The legacy name `SoP.adaptiveTranscriptAdvantage` is now a compatibility
  alias for the law-level SoP PRF endpoint `SoP.advPRF`; it no longer builds
  the full adaptive supremum from `normalizedSoPRepresentative` /
  `urfRepresentative`.
- `SoP.Compression` now contains the law-level arbitrary-environment theorem
  `SoP.repeatedQuerySoP_probPDE_bound`, which applies the generic law-level
  H-technique bridge directly to `ProbPDS` / `ProbPDE`.
- `SoP.Compression` is now law-level: representative constructors and
  representative SoP compression endpoints moved to `SoP.CompressionLegacy`.
- The public SoP application boundary now delegates fixed-query and arbitrary
  PDE transcript bounds to named law-level bridges
  (`SoP.repeatedQuerySoP_fixedQuery_law_bound` and
  `SoP.repeatedQuerySoP_probPDE_law_bound`), so `SoPBoundary` no longer exposes
  representative adapters in theorem proofs.
- `SoP.repeatedQuerySoP_probPDE_law_bound` now delegates to the law-level
  `SoP.repeatedQuerySoP_probPDE_bound`.
- The deterministic and fixed-query SoP wrappers in `SoP.LawAdvantage` now
  delegate through `ProbPDE.ofDDE` to the arbitrary law-level theorem, instead
  of rewriting through representative fixed-query transcript distributions.
- Public SoP PRF endpoints now live in `SoP.LawAdvantage` and `SoPBoundary`.
  Source-name compatibility wrappers for the old fixed-query layer are now on
  `SoPBoundary`: `sop_statDist_rfDist_le`, `sopFixedQueryAdvantage`, and
  `sopFixedQueryAdvantage_le`, all stated over the migrated CR18 transcript-law
  surface.  The old source `0 < |G|` premise is no longer exposed because it is
  discharged from `[AddGroup G]`.
  `SoP.filteredDelta_le_advPRF` and `SoP.filteredDelta_bound` also expose the
  raw CR18 filtered distinguishing route for the concrete normalized SoP/URF
  pair.  The public wrapper `sop_filteredDelta_le` bounds the filtered
  `Delta(⌈q⌉SoP,⌈q⌉URF)` by the same `q^3 / |G|^2` term; the finite-query
  normalization premise is discharged internally from totality of the concrete
  function-evaluator laws.
- Function-evaluator laws are now factored through the owner-level constructor
  `RandomSystems.CR18.PFunPDS.Prob.functionEvaluator`; sampled-function systems
  no longer need to expose `Dist.PMF p (functionEvaluatorRV F)` at public model
  sites.  Strong/tweakable PRP ideals, HashThenPRF, SoP
  `normalizedSoPProbPDS`, and HCTR2's migrated `hctr2RealProbPDS` use this
  constructor.  Totality is factored through reusable shared lemmas:
  `RandomSystems.CR18.functionEvaluatorProb_KStepTotal`,
  `RandomSystems.CR18.functionEvaluatorProb_totalOnNonempty`, and
  `RandomSystems.CR18.PFunPDS.Prob.urf_KStepTotal`.  The SoP law-level proofs
  use the specializations `SoP.normalizedSoPProbPDS_KStepTotal` and
  `SoP.normalizedSoPProbPDS_totalOnNonempty`, so endpoint proofs no longer
  repeat support/fiber bookkeeping for function-evaluator laws.
  Representative-level and old bounded SoP adaptive endpoints moved behind
  `SoPLegacyBoundary`, which is imported by `All` but not by `Surface`.
- `SecurityDefs` now contains only law-level `fixedQueryAdv`,
  `fixedQueryAdv_le_of_pointwise`, `fixedQueryAdv_le_Adv`, `Adv`,
  `Adv_le_of_pointwise`, `filteredDelta_le_Adv`, `advPRF`,
  `advPRF_le_of_pointwise`, `advNPRF`, `advNPRF_le_advPRF`, `advPRP`,
  `advPRP_le_of_pointwise`, `advNPRP`, and `advNPRP_le_advPRP`; the unused
  representative-level `representativeAdv` alias was removed rather than moved
  as a floating helper.
- The adaptive environment index is a deterministic CR18 `DDE` plus the tight
  query-totality predicate `DDEKQueryTotal`, not a representative wrapper.
- `Dist.supportProbDist` has been promoted to the core `RandomSystems.Dist`
  API; the migration folder now reuses it instead of defining it locally.
- `Dist.supportProbDist_mass_preimage` records the generic event-mass fact for
  support-subtype representatives, and the migration uses it to bridge
  law-level PDE transcript distributions to representative transcript
  distributions without exposing sample-space parameters.
- Deterministic environment query-totality has been promoted to the core
  `RandomSystems.CR18.PFunPDE.DDEKQueryTotal` predicate; the migration-level
  name is now only a compatibility alias.
- Law-level probability aliases `PFunPDS.Prob` / `PFunPDE.Prob`, deterministic
  environment embedding, support-totality predicates, transcript law/distribution
  constructors, weight facts, deterministic transcript distributions, and the
  ideal URF law have been promoted to the core CR18 API under
  `RandomSystems.CR18.PFunPDS.Prob` / `PFunPDE.Prob`; migration-level names now
  reuse those core definitions and theorems.
- The thesis-style deterministic q-query environment index and law-level
  adaptive transcript advantage now live in the core CR18 API as
  `RandomSystems.CR18.PFunPDE.QQueryEnvironment`,
  `RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage`, and
  `RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage_le_of_pointwise`;
  `AdaptiveTranscriptLawAdvantage` is now a compatibility layer over those core
  declarations.
- The law-level bounded-chooser adaptive transcript advantage and its
  image-boundedness, nonnegativity, and sub-supremum comparison facts now live
  in `NextGen.BoundedEnvironment` under
  `RandomSystems.CR18.PFunPDS.Prob`; the migration layer only wraps those names.
- The CR18 filtered URF/URP switching path is now closed in
  `NextGen.SwitchingLemma`: the filtered Example 4.15 conditional-equivalence
  theorem, the blind collision birthday bound, and
  `RandomSystems.CR18.urf_urp_switching` all build without local sorries.
- Lightweight switching-ratio arithmetic now lives in shared counting
  infrastructure as
  `RandomSystems.CR18.Counting.factorial_ratio_eq_descFactorial_inv` and
  `RandomSystems.CR18.Counting.switching_ratio_le`.  HCTR2's concrete switching
  proof uses this shared theorem instead of importing old
  `HTechnique.CountingLemmas` or the heavy `RandomSystems.CR18.SwitchingPort`
  module.
- The generic old bounded stateless adaptive-transcript bridge facts used by
  HCTR2 now live in their natural `RandomSystems` owners.
  `RandomSystems.Transcript` owns `RandomSystems.transcriptInputsMatch`,
  `RandomSystems.transcriptOutputs`, `Transcript.compatibleWithEnv`,
  `Transcript.inputs`, `Transcript.outputs`, `Transcript.outputPrefix`,
  `DDE.FollowsTranscript`, `DDE.transcriptOfOutputs`,
  `DDS.interact_eq_transcript_iff_of_follows`,
  `RandomSystems.interact_ofFunq_eq_iff`, and the generic `DDS.ofFunq`
  adaptive/fixed-query replay facts.  The deterministic adaptive transcript
  replay bridge was removed from HCTR2's `BirthdayEngine` copy and from
  `RandomSystems.Equiv`'s local prefix.  `RandomSystems.Instances.URF` owns
  `RandomSystems.transcriptDist_URFfunOf_match`,
  `RandomSystems.transcriptDist_URFfunOf_mismatch`,
  `RandomSystems.transcriptDist_URFfun_uniform`,
  `RandomSystems.ofStatelessOracleDist_eq_URFfunOf`,
  `RandomSystems.adaptiveTranscriptDist_URFfunOf_eq_of_compatible`, and
  `RandomSystems.adaptiveTranscriptDist_URFfunOf_eq_zero_of_incompatible`.
  `NextGen.Migration.HTechnique.LegacyStatelessBridge` remains only a
  compatibility re-export.  HCTR2's concrete transcript layer imports the
  owning `RandomSystems` module directly and no longer defines local copies of
  the fixed-query `URFfunOf` transcript lemmas.  The switching proof no longer
  imports `HTechnique.OneSided`; its pointwise distance step uses
  `RandomSystems.oneSided_hTechnique`.
- HCTR2's legacy bounded `hctr2AdvSPRP` endpoint no longer imports
  `HTechnique.SecurityDefs` or calls the old free-ideal wrapper
  `SecurityDefs.advSPRP`; it is stated directly as
  `RandomSystems.advantageAdaptive` between the concrete real and ideal PDSs.
- HCTR2's concrete H-coefficient bad-event discharge now uses the shared
  `RandomSystems.StatDist` interface directly.  `MainLemma`, `BirthdayEngine`,
  `PaperTargetCore`, `PaperTarget`, `PaperTargetSection26`, and
  `PaperTargetSimulator` use plain predicates for bad events plus
  `RandomSystems.probBad`, `RandomSystems.hTechnique_ratio`,
  `RandomSystems.hTechnique_eq_on_good`, and `RandomSystems.oneSided_hTechnique`.
  The old external `HTechnique.Core` import, `BadPredicate` wrapper, `.isBad`
  projections, and `HTechnique.probBad` calls have been removed from
  `HCTR2/Proofs/Concrete`.
- The generic probability and `URFfun` birthday support used by HCTR2's
  `BirthdayEngine` now lives in the owning `RandomSystems` modules rather than
  in the HCTR2 proof tree.  `RandomSystems.Dist` owns
  `Dist.evalPred_iUnion_le`, `Dist.evalPred_uniform`,
  `Dist.evalPred_uniform_le`, and `Dist.evalPred_fTransform_uniform_le`;
  `RandomSystems.StatDist` owns `RandomSystems.probBad_eq_evalPred` and
  `RandomSystems.probBad_iUnion_le`; and `RandomSystems.Instances.URF` owns
  `RandomSystems.urffun_aTD_eq_fTransform_uniform`,
  `RandomSystems.urffun_evalPred_le`, and
  `RandomSystems.probBad_urffun_birthday_le`.  `BirthdayEngine` now keeps only
  HCTR2-specific counting content and consumes these shared facts.
- HCTR2's concrete strong-permutation direction model has moved off
  `HTechnique.Models`: `Games`, `Switching`, `MainLemma`, `PaperTargetCore`,
  `PaperTarget`, `PaperTargetSection26`, and `PaperTargetSimulator` now use the
  migrated `NextGen.Migration.HTechnique.StrongPRP.QueryDir` /
  `forwardOnly` surface.  The bridge function `queryDirToLegacy` was removed,
  and a search of `HCTR2/Proofs/Concrete` finds no `HTechnique.Models` import or
  use.
- Generic supremum/order helpers used by advantage definitions now live in
  `RandomSystems.StatDist`, including `RandomSystems.coe_finset_sup_le`; the
  migration layer no longer owns a duplicate finite-`NNReal` supremum helper.
- Generic distribution-level H-technique facts now live in
  `RandomSystems.StatDist`: bad-event mass, ratio, expectation,
  equality-on-good, one-sided, common-pushforward one-sided, proper-probability,
  and finite-mass-function wrappers.  `Density` and `TranscriptLawCore` are now
  paper-facing compatibility layers over those shared facts and carry fewer
  decidability hypotheses.
- `RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage_image_bddAbove`
  owns the reusable law-level boundedness fact for the adaptive
  transcript-advantage image.  This is the side condition used to compare
  restricted environment suprema with the full thesis-style supremum.
- The first generic CR18/thesis raw-advantage bridge facts now live in shared
  API rather than the migration layer:
  `RandomSystems.mass_tsub_mass_le_statDist` and
  `RandomSystems.mass_sub_mass_le_statDist` bound event probability gaps by
  statistical distance; `RandomSystems.CR18.PFunPDE.DDEKQueryTotal_of_queriesExactly`
  turns exact-query distinguishers/environments into admissible thesis
  transcript environments; and
  `RandomSystems.CR18.PFunPDS.Prob.adaptiveTranscriptAdvantage_nonneg` supplies
  the nonnegativity side condition for supremum shells.
- `NextGen.AdaptiveLawBridge` now proves the exact-query CR18/thesis bridge:
  `verdictProb_single_eq_deterministicTranscriptDist_mass_of_queriesExactly`
  identifies point-distinguisher verdict probability with a length-`q`
  transcript event; `advantage_single_le_adaptiveTranscriptAdvantage_of_queriesExactly`
  proves the point bound; `verdictProb_eq_sum_single` and
  `advantage_eq_sum_single` record linearity in the distinguisher distribution;
  and `advantage_le_adaptiveTranscriptAdvantage_of_queriesExactly` lifts the
  bound to arbitrary probability distributions over exact-query distinguishers.
- `RandomSystems.CR18.maxAdvantage_filterQueries_le_adaptiveTranscriptAdvantage`
  now combines finite-query normalization, the exact-query bridge, and the
  base/filter transcript-law comparison, proving `Delta(⌈q⌉S,⌈q⌉T)` bounded by
  the thesis-style base-law transcript `Adv(S,T)` under the meaningful base-law
  `q`-step totality premises.
- `NextGen.Migration.HTechnique.SecurityDefs.filteredDelta_le_Adv` exposes that
  bridge on the curated H-technique security surface: callers provide law-level
  `ProbPDS` objects, their q-step totality premises, and the existing filtered
  finite-query normalization fact; the theorem constructs Maurer's `[q]S` and
  `[q]T` in the conclusion and bounds the raw CR18 filtered `Delta` by
  thesis-style `Adv(S,T)`.
- The base/filter comparison is proved generically in `NextGen.AdaptiveLawBridge`:
  `PFunDDS.filterQueries_apply_eq_some_iff` records that `[q]s` preserves
  concrete evaluations at histories of length at most `q`;
  `PFunPDS.Prob.deterministicTranscriptDist_filterQueries_eq` proves length-`q`
  deterministic transcript laws are unchanged by `[q]`; and
  `PFunPDS.Prob.adaptiveTranscriptAdvantage_filterQueries_le` lifts this to the
  thesis-style adaptive transcript supremum.
- `StrongPRP` now provides concrete CR18 law-level strong/tweakable PRP model
  objects: `QueryDir`, `strongURP`, `tweakableURP`, `tweakableStrongURP`, and
  source-facing `advSPRP`, `advTPRP`, and `advTSPRP`.  These definitions
  construct the ideal laws internally from uniform permutation families rather
  than accepting a free ideal parameter.

## Compatibility/deprecation map

- **Promotion surface:** `Surface`, `SecurityDefs`, `SoPBoundary`, `Density`,
  `HashThenPRF`, `StrongPRP`, law-level transcript objects from
  `TranscriptLawPublic`, and the shared application-independent CR18 bridge facts in
  `NextGen.AdaptiveLawBridge`.
- **Promoted source-facing endpoint names:**
  `advPRF`, `advNPRF`, `advPRP`, `advNPRP`, `advSPRP`, `advTPRP`, `advTSPRP`,
  `advNPRF_le_advPRF`, `advNPRP_le_advPRP`,
  `sop_prf_advantage`, `sop_statDist_rfDist_le`,
  `sopFixedQueryAdvantage`, `sopFixedQueryAdvantage_le`,
  `sop_advPRF_le`, and `hashThenPRF_security`.  These names now sit on the
  CR18 transcript-law surface: the theorem inputs are law-level systems,
  deterministic CR18 environments, fixed-query vectors, or concrete
  application parameters, while fixed-query environments, URF/URP ideals,
  filtered systems, strong/tweakable permutation ideals, and sampled
  representatives are constructed internally.
- **Downstream audit:** `DOWNSTREAM.md` records actual workspace callers of the
  old package.  It currently identifies SequenceHash as an old bounded-system
  scaffold, ChaChaPoly as a pure interop re-export layer, and HCTR2 as the real
  strong/tweakable PRP consumer.  The only concrete source-name support alias
  added from this audit is HashThenPRF `badPred`, which names the migrated bad
  event predicate without reintroducing the old `BadPredicate` wrapper.
- **Support modules, not endpoint APIs:** `FixedQueryLaw`,
  `TranscriptLawCore`, `FunctionEvaluator`, `QueryCompression`,
  `SoP.VisibleLaw`, `SoP.TranscriptPrefix`, `SoP.SystemLaw`, and
  `SoP.Compression`. These contain proof objects and source-proof bridges used
  by the public theorems, but their declarations are not the advertised
  application boundary.
- **Compatibility-only representative layer:** `PDSRepresentative`,
  `PDERepresentative`, `TranscriptLaw`, `FixedQuery`, `AdaptiveBridge`,
  `AdaptiveTranscriptAdvantage`, and `SoP.CompressionLegacy`. These remain
  implementation bridges for old representative-shaped endpoints and should not
  be promoted as the new API.
- **Legacy build gates:** `LegacyBoundary`, `LegacyBoundedTranscript`,
  `LegacyStatelessBridge`, and `SoPLegacyBoundary` keep old bounded-system and
  old SoP names build-checked while downstream callers migrate. They are
  imported by `All`, not by `Surface`.
- The representative-level adaptive transcript wrappers remain as support
  bridges for legacy/adaptive representative endpoints, but both the full
  adaptive supremum and the bounded-chooser sub-supremum are delegated to the
  induced law-level PDSs.
- The representative-level fixed-query theorem `SoP.repeatedQuerySoP_bound`
  remains in `SoP.CompressionLegacy` as compatibility support for legacy
  representative endpoints.  The public deterministic, fixed-query, and
  arbitrary `ProbPDE` SoP endpoints now delegate through the law-level
  arbitrary-PDE theorem.
- `PDERepresentative.ofDDE` remains support-level: it is used to feed
  deterministic CR18 environments into existing representative transcript-law
  proofs, but it is no longer part of the public `Adv` endpoint.
- Old source security names are split by whether the current CR18 law-level
  object exists.  Adaptive `advPRF`/`advPRP` are direct specializations of
  thesis-style `Adv`; non-adaptive `advNPRF`/`advNPRP` are direct
  specializations of the generic fixed-query supremum `fixedQueryAdv`.
- **Remaining strong/tweakable work:** the concrete ideal side is now modeled
  in `StrongPRP`.  HCTR2 has a first law-level `advSPRP` cut and its concrete
  switching proof no longer depends on old counting or one-sided transcript
  bridge modules, its legacy bounded advantage endpoint no longer depends on
  the old `SecurityDefs` wrapper, and the concrete files no longer depend on
  `HTechnique.Models.QueryDir` / `forwardOnly`, `HTechnique.Core` bad-event
  wrappers, or `NextGen.Migration.HTechnique.LegacyStatelessBridge`.  The next
  blocker is deeper law-level adoption: replacing the remaining old bounded
  `PDS` / `DDE` compatibility layer with the migrated CR18 law-level endpoints
  where that is mathematically faithful.

## Promotion blockers

- Keep the promotion surface convention-based rather than import-hidden:
  `Surface` directly imports the public endpoint modules, and support/proof
  declarations remain reachable transitively as normal Lean declarations.  The
  promotion audit is therefore on theorem headers, endpoint modules, namespace
  organization, and docs, not on impossible selective import hiding.
- The generic CR18 raw-`Delta` to thesis transcript-`Adv` bridge is now in the
  right base-law shape for filtered systems, is threaded through
  `SecurityDefs`, and has a concrete SoP raw-`Delta` endpoint on
  `SoPBoundary`.  The remaining promotion blocker is to retire or explicitly
  quarantine compatibility wrappers that are no longer part of the curated
  surface.
- After H-technique and SoP are accepted on this surface, deprecate the old
  H-technique path and then plan the broader NextGen-to-main namespace
  migration.
- Decide the application gate precisely.  SoP and the fixed-query HashThenPRF
  endpoint are now on the migrated surface, including the main old source-facing
  theorem names.  The remaining blocker for wholesale application-folder
  deprecation is whether any less central old helper names need compatibility
  wrappers, or whether the migrated law-level theorem names are the intended
  public replacement.
