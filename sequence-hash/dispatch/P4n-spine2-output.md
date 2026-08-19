Implemented the filter-first R4 structural headline in [SequenceMACGeneric.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGeneric.lean:1).

- Added `budgetHist` using the existing `primCount`, `evalCount`, and `sequenceFunctionEvalCost`, with `budgetHist_prefixClosed` proved via Mathlib’s prefix/filter APIs.
- Proved [liftHist_budgetHist_eq](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGeneric.lean:117):
  `liftHist budgetHist = SequenceFunctionTaggedBudgetRespects`.
- Defined [B_cascade, B_key, deriveCostGeneric, and B_SEQ](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGeneric.lean:149) exactly as A4 §5. Also proved `deriveCostGeneric … 0 0 … = 0`.
- Preserved the §8 guardrail assumptions: `users ≤ q`, key point-mass, trace bound, cross-role separation, and output-compression backing.

The two named deep hypotheses are exactly:

```lean
h_norm :
  DeltaFilterDomFiniteQueryNormalization
    (budgetHist model b S p q lambda)
    (budgetHist_prefixClosed model b S p q lambda) (p + q)
    (sequenceFunctionICReal model b S users keysP).val
    (sequenceFunctionICIdeal users keysP).val

h_badmass :
  ∀ E : QQueryEnvironment
      (SequenceFunctionICQuery Block L users)
      (SequenceFunctionICReply L) (p + q),
    EnvRespects
      (SequenceFunctionTaggedBudgetRespects model b S p q lambda users) E →
    probBad
      (extendedTranscriptDistRep
        (sequenceFunctionICIdealP users keysP)
        sequenceFunctionICIdealF
        (sequenceFunctionICIdealReveal model b S) E.1)
      (Bad_SEQ (p := p) (q := q) (lambda := lambda)) ≤
    B_SEQ p q users lambda rK rS c kappaStar
```

The frozen [sequenceMAC_generic_prf_tight](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGeneric.lean:192) proves the requested `Δ(filterDom budget real, filterDom budget ideal) ≤ B_SEQ` chain using:

1. `maxAdvantage_filterDom_le_filteredAdaptiveTranscriptAdvantage`
2. `sequenceFunctionICReal_KStepTotal` and `sequenceFunctionICIdeal_KStepTotal`
3. `liftHist_budgetHist_eq`
4. `sequenceFunctionIC_r4_equality_on_good`

There is no triangle or NMAC hop.

Verification:

- `lake build RandomSystems RandomSystemsCC SequenceHash` — green, 8501 jobs.
- New file contains no `sorry`, `admit`, `axiom`, or `private`.
- `#print axioms sequenceMAC_generic_prf_tight`:
  `{propext, Classical.choice, Quot.sound}`.
- Only the requested new file was added.