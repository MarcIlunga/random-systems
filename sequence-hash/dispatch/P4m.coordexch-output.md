Implemented and verified.

- Framework lemma: [`Dist.mass_prod_uniform_coordinate_exchange`](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/Dist.lean:1315)
- Direct representative equality: [`sequenceFunctionIC_extFixedQueryTranscriptDistRep_eq_on_good`](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:1927)
- Packaged R4 equality-on-good: [`sequenceFunctionIC_r4_equality_on_good`](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:2201)

Reuse map:

- `uniform_mass_eq_mass_mul_mass_of_card_mul_eq`
- `sequenceFunction_fiber_card_of_not_Bad_SEQ`
- `sequenceFunctionTerminalFreeSkeleton_terminalShift`
- `sequenceFunctionRevealedTerminalInputs_nodup_of_not_Bad_SEQ`
- `adv_le_of_extFixedQueryRep_eq_on_good_filtered_of_filter`
- Existing real/ideal `KStepTotal` lemmas

Generic additions required by the proof:

- Curried multipoint function-fiber counts in [`Counting.lean`](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/Counting.lean:422)
- Uniform-law independence from `Fintype` instance selection in [`Dist.lean`](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/Dist.lean:414)
- Finite tagged query/reply instances in [`IdealCompression.lean`](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/IdealCompression.lean:53)

Verification:

- `lake build`: green, 8441 jobs
- H-technique surface audit: passed
- Legacy checks: green
- No `sorry`, `private`, `B_SEQ`, `h_badmass`, games, or `condEquiv` added
- Axioms for both final lemmas: `{propext, Classical.choice, Quot.sound}`

Step 4—the bad-mass bound and final R4 theorem—is now the only remaining R4-spine work.