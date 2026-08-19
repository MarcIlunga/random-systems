Part A landed and builds green. Part B was valve-stopped; consequently `sequenceMAC_generic_prf_tight_norm` was not added.

Implemented:

- Public `QExtensible` beside `PrefixClosed` in [PFunDDS.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/PFunDDS.lean:28).
- Public generic tag-count facts in [IdealCompression.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/IdealCompression.lean:77):
  `taggedCounts_toList`, `primCount_add_evalCount`, and prefix monotonicity for both counters.
- `SequenceFunctionOutputCompressionBacked.nonemptyBlock` in [SequenceMACGenericTrace.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericTrace.lean:337).
- `sequenceFunctionICReal_totalOnNonempty` and `sequenceFunctionICIdeal_totalOnNonempty` in [IdealCompression.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/IdealCompression.lean:172).
- `budgetHist_append_prim`, `budgetHist_append_eval`, and the corrected `budgetHist_qExtensible` in [SequenceMACGeneric.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGeneric.lean:61).

The requested unconditional extensibility statement is false. The corrected theorem requires:

- `SequenceFunctionTraceBound`, supplying `evalCost ≤ lambda`;
- `SequenceFunctionOutputCompressionBacked`, supplying a primitive block;
- `0 < users`, supplying an evaluation request.

For example, with `users = 0`, `p = 0`, and `q = 1`, the budget admits the empty history but no one-query extension. Thus a future discharged headline must either assume `0 < users` or restrict parameters equivalently.

Part B’s remaining construction obligations are:

1. Define a public suppression transform that follows `d` while proposed histories satisfy `P`, then, at the first violation, computes the eventual verdict along the deterministic `none` tail.
2. Prove its verdict probability equals that of `d` against `filterDom P S`; prefix closure ensures no later query can restore `P`.
3. Define history-dependent padding using `QExtensible`, rather than the fixed-dummy `padDDD`.
4. Prove the padded distinguisher makes exactly `q` queries and satisfies `DistinguisherRespects P`.
5. Lift both transforms through `Dist.fTransform`, preserve probability mass, and prove the two base-system verdict equalities using `TotalOnNonempty`.
6. Combine those equalities into the required advantage domination and then instantiate it with the Part A facts.

Existing `padDDD` provides useful exact-query and verdict-tail structure, but cannot select a history-dependent respecting query or suppress a rejected query without issuing it. The existing `SelfAnswerFilter` and `PFunDDS.Cache` machinery is specialized to other settings and does not discharge these obligations directly.

Reuse map:

- Reused `SequenceFunctionTraceBound.evalCost_apply_le`.
- Reused `functionEvaluatorProb_totalOnNonempty`.
- Generalized the former SequenceHash-specific tagged-count calculation into public scheme-independent framework facts.
- Reused those count facts in `budgetHist_prefixClosed` and extensibility instead of reproving accounting.

Verification:

- `lake build RandomSystems RandomSystemsCC SequenceHash` — passed, 8501 jobs.
- All added declarations are free of `sorry`, `admit`, and `private`.
- Axiom audit: `QExtensible` has no axioms; every added theorem uses only `{propext, Classical.choice, Quot.sound}`.
- The aggregate build still reports pre-existing `sorry` declarations in unrelated legacy/current files; none were introduced or modified here.