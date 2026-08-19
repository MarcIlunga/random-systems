Implemented and verified. R4’s `h_norm` is closed.

- Replay invariant: [`padRespecting_replay_of_transcript`](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/FilterDomNormalization.lean:852) proves the padded transcript reproduces the suppressed run and aligns its certified admitted-history state.
- Stop-by-`q`: [`queriesAtMostN_suppressViolating`](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/FilterDomNormalization.lean:515) derives the contradiction with `QBounded` from a hypothetical `(q+1)`st admitted query.
- Verdict equivalence: deterministic, distribution-level, and advantage equality are proved using totality, `StopFinal`, `winProb_fTransform_left`, and `winProb_congr_support`.
- Domination: [`advantage_suppressViolating_le_padRespecting`](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/FilterDomNormalization.lean:1060), strengthened internally to equality.
- Generic normalization: [`deltaFilterDomFiniteQueryNormalization_of_extensible`](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/Derivation.lean:1780).
- Discharged headline: [`sequenceMAC_generic_prf_tight_norm`](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGeneric.lean:330), with the required `0 < users`; `h_norm` is gone and only `h_badmass` remains as the R4-deep premise.

Reused by name: `advantage_suppressViolating_eq_filterDom`, `queriesExactly_ddToDDE_padRespecting`, `distinguisherRespects_padRespecting`, `Cache.QueriesAtMostN`, `Cache.verdict_iff_at_stall`, transcript prefix/length lemmas, `winProb_fTransform_left`, `winProb_congr_support`, all four `budgetHist_*` facts, and both SequenceFunction totality theorems. Generic facts were added publicly; no local SequenceHash duplicate was introduced.

Verification:

- `lake build RandomSystems RandomSystemsCC SequenceHash` — green.
- `lake run htechniqueSurfaceAudit` — passed.
- Existing count-filter normalization remains green and unchanged.
- Changed files contain no `sorry`, `admit`, `axiom`, or `private`.
- Axioms for replay, stop-by-`q`, domination, generic normalization, and `_norm`: `{propext, Classical.choice, Quot.sound}`.