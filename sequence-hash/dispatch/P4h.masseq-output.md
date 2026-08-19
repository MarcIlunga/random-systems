Stopped at the mandated valve after item 1; no `sorry` was introduced.

Implemented in [SequenceMACGenericFiberMass.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:102):

- `programFinalCompressionOutput_dropLast`
- `padCompressionTrace_programFinalCompressionOutput_of_lt_dropLast`
- `sequenceFunctionICReveal_honestPrefix_agreement`

These prove that real and programmed-ideal reveals have identical keys and identical non-terminal compression entries. Only the terminal programmed coordinate remains.

The terminal mass step requires a protocol-specific simultaneous re-randomization/fiber-cardinality theorem: swap each fresh terminal compression-table coordinate with its corresponding independent ideal-function coordinate, then prove all traces remain stable. `condEquiv_of_transcript_mass_reductions` cannot supply this directly—its `hprod` premise already requires the protocol-specific mass factorization. CBC discharges that premise using its separate `cbc_fiber_card`; no SequenceFunction analogue currently exists.

Consequently, these remain:

1. Terminal uniform/programmed fiber equality.
2. Per-transcript extended-mass equality.
3. Packaging through `adv_le_of_extFixedQueryRep_eq_on_good_filtered_of_filter`.

Verification:

- Focused build: green.
- Whole `lake build`: green, 8,441 jobs.
- H-technique surface audit: passed.
- No new `sorry`, `admit`, `axiom`, `private`, `B_SEQ`, or `h_badmass`.
- Principal axiom line: `{propext, Classical.choice, Quot.sound}`.

Step 4 is therefore not yet the only remaining R4-spine work; the terminal portion of step 3 remains.