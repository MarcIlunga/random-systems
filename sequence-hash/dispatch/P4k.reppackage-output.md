Invoked the explicit valve: the representative-mass normalization proved substantially larger than a direct fiber-card application, so I stopped after item 1 and removed all unfinished work.

Implemented in [SequenceMACGenericFiberMass.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:951):

- Public grouped construction-input rows.
- Public generic `Nodup` lemma separating `dropLast` entries from all row terminals.
- Padding/trace-length support lemmas.
- `SequenceFunctionTerminalFreeSkeleton`.
- `sequenceFunctionTerminalFreeSkeleton_prefix_terminal_disjoint`, derived directly from global construction-input `Nodup` via `not_Bad_SEQ_iff_compressionFresh`; no new domain-separation theorem.

Not implemented under the valve:

- Fiber-card application to `extFixedQueryTranscriptDistRep`.
- Direct real/ideal representative-mass equality.
- Packaged R4 equality-on-good lemma.

Therefore, final R4 step 4 is not yet the only remaining spine work. The remaining sequence is skeleton shift-invariance, representative mass normalization using `sequenceFunction_fiber_card_of_not_Bad_SEQ`, direct mass equality, then endpoint packaging.

Reuse/generalization:

- Reused `not_Bad_SEQ_iff_compressionFresh`, `sequenceFunctionCompressionTrace_length_le_evalCost`, `programFinalCompressionOutput_inputs`, `sequenceFunctionICIdealReveal`, and `SequenceFunctionTaggedBudgetRespects`.
- Added public generic list/trace facts rather than local scheme-specific helpers.

Verification:

- `lake build SequenceHash.RandomSystems.SequenceMACGenericFiberMass`: green.
- Whole-repository `lake build`: green, 8441 jobs.
- Edited file contains no `sorry`, `private`, games, `condEquiv`, `B_SEQ`, or `h_badmass`.
- Axiom audit: `{propext, Classical.choice, Quot.sound}` only.