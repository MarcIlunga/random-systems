# Downstream H-technique migration audit

This note records the current workspace users of the external `/h-technique`
package.  It is the compatibility checklist before the migrated
`NextGen.Migration.HTechnique.Surface` can become the main random-systems
surface and the old package can be deprecated.

Audit command, run from `/Users/marcilunga/Documents/ToB/research/fv`:

```bash
rg -n '\b(advPRF|advNPRF|advPRP|advNPRP|advSPRP|advTPRP|advTSPRP|sop_prf_advantage|sop_statDist_rfDist_le|sopFixedQueryAdvantage|sopFixedQueryAdvantage_le|sop_advPRF_le|hashThenPRF_security)\b' \
  --glob '*.lean' --glob '!**/.lake/**' --glob '!**/lake-packages/**' --glob '!**/.git/**'
```

## Actual downstream callers

- `/sequencehash-fv/SequenceHash/HTechniqueScaffold.lean`
  imports `HTechnique.Core`, `HTechnique.OneSided`, and
  `HTechnique.SecurityDefs`.  It uses the old bounded-system API:
  `HTechnique.SecurityDefs.advPRF`, `HTechnique.hTechnique_ratio`,
  `BadPredicate`, old `PDS`, old `DDE`, and old finite `Transcript`.
  Migration is not a name-only import swap.  The theorem should be restated on
  the CR18 law-level surface (`ProbPDS`, deterministic CR18 environments, and
  transcript laws) or kept behind an explicit legacy adapter until the
  construction is ported.

- `/chachapoly-verification/ChaChaPoly/Proofs/Interop/HTechnique.lean`
  is a pure re-export layer for H-technique symbols.  Most exported
  HashThenPRF names are now present in
  `NextGen.Migration.HTechnique.HashThenPRF`; the migrated module also provides
  the source-name alias `badPred` for the old support predicate.  The security
  exports `advNPRF`, `advPRF`, `advNPRP`, and `advPRP` can map to
  `NextGen.Migration.HTechnique.SecurityDefs`.  The export `advSPRP` can now
  map to `NextGen.Migration.HTechnique.StrongPRP.advSPRP`, provided callers use
  the concrete `QueryDir × X` law-level input shape rather than the old
  free-ideal scaffold.

- `/hctr2-verification` is the real strong/tweakable PRP consumer.  The first
  law-level cut now exists in `HCTR2.Proofs.Concrete.Games`:
  `hctr2RealProbPDS` states the real HCTR2 world as a concrete `ProbPDS`, and
  `hctr2AdvSPRP_law` calls the migrated `StrongPRP.advSPRP`, whose ideal is
  constructed internally.  The real sampled-function law now uses the shared
  owner-level constructor `RandomSystems.CR18.PFunPDS.Prob.functionEvaluator`
  rather than spelling the raw `Dist.PMF`/`functionEvaluatorRV` composition.
  The old bounded endpoint `hctr2AdvSPRP` no longer imports the legacy
  `HTechnique.SecurityDefs` wrapper; it is the canonical bounded
  `RandomSystems.advantageAdaptive real ideal` expression.

- HCTR2's concrete switching proof no longer depends on
  `HTechnique.CountingLemmas` or `HTechnique.OneSided`.  The shared numeric
  step is now `RandomSystems.CR18.Counting.switching_ratio_le` from
  `NextGen.Counting`, and the generic old bounded stateless
  adaptive-transcript facts now live in their natural `RandomSystems` owners:
  `RandomSystems.Transcript` for environment/transcript compatibility and
  deterministic replay (`DDE.FollowsTranscript`, `DDE.transcriptOfOutputs`, and
  `DDS.interact_eq_transcript_iff_of_follows`), and
  `RandomSystems.Instances.URF` for fixed-query and adaptive `URFfunOf`
  transcript masses, uniform fixed-query URF transcript masses, and the generic
  `PDS.ofStatelessOracleDist = URFfunOf` bridge.
  `NextGen.Migration.HTechnique.LegacyStatelessBridge` is now only a
  compatibility re-export, and HCTR2's concrete transcript layer imports the
  owning `RandomSystems` module directly.  `BirthdayEngine.lean` no longer
  carries a verbatim copy of the deterministic transcript prefix from
  `RandomSystems.Equiv`.  `Switching.lean` also calls the shared
  distribution-level `RandomSystems.oneSided_hTechnique` instead of the old
  H-technique theorem.
  The concrete HCTR2 proof no longer imports `HTechnique.Models` and no longer
  uses the legacy `QueryDir` / `forwardOnly` objects; those now come from
  `NextGen.Migration.HTechnique.StrongPRP`.  The concrete HCTR2 bad-event
  discharge has also moved off the external `HTechnique.Core` interface:
  bad events are plain predicates, and `BirthdayEngine`, `MainLemma`,
  `PaperTargetCore`, and the `PaperTarget` wrappers use shared
  `RandomSystems.probBad`, `RandomSystems.hTechnique_ratio`, and
  `RandomSystems.hTechnique_eq_on_good`.
  The generic probability and `URFfun` birthday lemmas that `BirthdayEngine`
  uses have been promoted into their owners: `RandomSystems.Dist` owns the
  `evalPred` union/uniform/pushforward bounds, `RandomSystems.StatDist` owns
  the `probBad`/`evalPred` bridge and bad-event union bound, and
  `RandomSystems.Instances.URF` owns the adaptive `URFfun` uniform-pushforward
  and birthday capstone facts.  `BirthdayEngine.lean` now keeps only
  HCTR2-specific counting lemmas.
  A targeted search of `HCTR2/Proofs/Concrete` finds no external
  `HTechnique.*` imports, no `BadPredicate`, no `.isBad`, and no
  `HTechnique.probBad`.  The scratchpad file
  `HCTR2/RandomSystemsScratchpad.lean` still imports `HTechnique.OneSided`, but
  it is not part of the concrete proof build gate tracked here.

## Non-blocking name collision

- `/vcvio-crypto-core/Core/Probability/SumOfPermutations.lean` has a theorem
  named `sop_prf_advantage`, but it is an independent VCVio probability
  development, not a caller of the external H-technique package.

## Compatibility rule

Add compatibility names only for actual downstream use and only when they
preserve the migrated modeling.  The current example is HashThenPRF `badPred`,
which is the old name for the same bad event; it is exposed as a predicate
because the migrated density API uses predicates directly.

Compatibility aliases for `advSPRP`, `advTPRP`, and `advTSPRP` must point to
the concrete law-level definitions in `StrongPRP`.  A theorem that takes both
`F` and `ideal` as free inputs would preserve the old name while losing the
mathematical content we are migrating toward.
