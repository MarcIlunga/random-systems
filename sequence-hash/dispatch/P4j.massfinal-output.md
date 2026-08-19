Invoked the explicit valve after the fiber-card layer. Changes are in [SequenceMACGenericFiberMass.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:381).

Completed, sorry-free:

- Terminal inputs are a sublist of global construction inputs, and hence `Nodup` off `Bad_SEQ` ([line 405](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:405)).
- Generic MD and full SequenceFunction trace stability: derive, inner, and nonterminal outer calls are preserved; only the terminal outer output changes ([line 639](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:639), [line 833](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:833)).
- `sequenceFunction_fiber_card`, using `Counting.card_filter_shift_univ` ([line 865](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:865)).
- Off-`Bad_SEQ` specialization supplying terminal freshness from 3a ([line 919](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:919)).

Reuse map:

- `sequenceFunctionTerminalShift`, `_state`, `_compose`, `_zero`
- `not_Bad_SEQ_iff_compressionFresh`
- `sequenceFunctionCompressionTrace_final_output`
- `Counting.card_filter_shift_univ`
- Existing programmed-trace and honest-prefix reductions

Verification:

- `lake build SequenceHash.RandomSystems.SequenceMACGenericFiberMass`: passed
- Whole-repository `lake build`: passed
- No `sorry`, `private`, `condEquiv`, games, or `|≡` added
- Axioms: `{propext, Classical.choice, Quot.sound}`

Still remaining:

1. Define the terminal-free representative skeleton and derive its prefix/terminal disjointness directly from global construction `Nodup`.
2. Apply the fiber factorization to `extFixedQueryTranscriptDistRep`.
3. Prove direct real/ideal representative-mass equality.
4. Package it through `adv_le_of_extFixedQueryRep_eq_on_good_filtered_of_filter`.

Therefore the packaged equality-on-good is not yet proved, and step 4 is not yet the only remaining R4-spine work.