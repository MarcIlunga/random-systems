Valve taken after Step 1; suppression is landed and green in [FilterDomNormalization.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/FilterDomNormalization.lean:1).

Implemented publicly:

- `keepAdmitted` and `keptPrefix_filterDom_eq_keepAdmitted_of_total`
- `suppressViolating`
- `verdict_suppressViolating_iff_filterDom`
- `verdictProb_suppressViolating_eq_filterDom`
- `advantage_suppressViolating_eq_filterDom`

The suppression correctly answers rejected queries internally with `none` and continues simulating later queries.

Two soundness corrections are required for Step 2:

- The requested generic theorem needs `P l → l.length ≤ q`. `QExtensible P q` alone is insufficient: `P := True`, `q := 0` satisfies it but cannot normalize an arbitrary querying distinguisher to zero queries.
- Prefix closure does not make rejection permanent. `fullyDefined` deletes a rejected query from `keptPrefix`, so a later query may be admitted. The implemented replay handles this correctly.

Remaining obligations:

1. Add a public `q`-bounded predicate and prove it for `budgetHist`.
2. Implement history-dependent respecting padding using `QExtensible`.
3. Prove exact-`q`, `DistinguisherRespects`, mass preservation, and verdict/advantage preservation.
4. Prove the corrected normalization lemma with both extensibility and boundedness.
5. Add `sequenceMAC_generic_prf_tight_norm` with `0 < users`; only `h_badmass` will remain.

Reuse map: `keptPrefix`, `fullyDefined`, `filterDom`, `Transcript`, `transcript_mem_iff`, `ddToDDE_eq_some_iff`, `output_fullyDefined_append_of_mem`, the `absorbGo` replay discipline, and `winProb_fTransform_left/right` with `winProb_congr_support`.

Verification:

- `lake build RandomSystems RandomSystemsCC SequenceHash` — green, 8502 jobs.
- Existing count-filter normalization remained unchanged and built green.
- New file contains no `sorry`, `admit`, `axiom`, or `private`.
- Axioms for all four suppression endpoints: `{propext, Classical.choice, Quot.sound}`.
- `sequenceMAC_generic_prf_tight_norm` was not added because the valve was triggered.