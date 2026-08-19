Implemented the generic facade fix, but packaging is blocked by a missing step-3b theorem in the checkout.

- Added `adv_le_of_extFixedQueryRep_eq_on_good_filtered_of_filter` in [IdealCompression.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/IdealCompression.lean:378).
- Its equality premise requires `Filt tz.1`, and out-of-filter mass is eliminated using `EnvRespects`.
- Reused `filteredAdaptiveTranscriptAdvantage_le_of_pointwise`, `hTechnique_eq_on_good`, `statDist_le_of_extension`, representative projection, and fixed-query self-mass lemmas.
- Existing facade endpoint remains unchanged and the repository builds without breaking users.

The blocker: [SequenceMACGenericFiberMass.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:1) contains the reveal maps and per-call reductions, but no real/ideal extended fixed-query mass-equality theorem. It ends at line 288. Therefore the required SequenceFunction packaging lemma cannot be proved merely by specialization; the missing fiber theorem still needs to establish:

```lean
SequenceFunctionTaggedBudgetRespects … tz.1 →
¬ Bad_SEQ tz →
extFixedQueryTranscriptDistRep realP realF realReveal xs tz =
  extFixedQueryTranscriptDistRep idealP idealF idealReveal xs tz
```

Verification:

- `lake build` — green, 8441 jobs.
- `lake build SequenceHash.RandomSystems.SequenceMACGenericFiberMass` — green.
- `lake run htechniqueSurfaceAudit` — passed.
- New endpoint axioms: `[propext, Classical.choice, Quot.sound]`.
- No new `sorry`, `axiom`, `private`, `B_SEQ`, `h_badmass`, or final theorem.

Consequently, step 4 is not yet the only remaining R4-spine work: the step-3b fiber mass equality and its packaging remain.