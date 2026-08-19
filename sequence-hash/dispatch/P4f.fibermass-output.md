Stopped at the mandated valve after the reveal maps and per-call reduction. The exact mass equality is not soundly derivable under the frozen facade.

Implemented [SequenceMACGenericFiberMass.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean):

- `sequenceFunctionICRealReveal`: dummy-key reveal plus honest canonical compression traces.
- `sequenceFunctionICIdealReveal`: same dummy keys, with each final outer output programmed to the independent ideal-function reply.
- `sequenceFunctionProgrammedTrace_call_reduction`: every preceding entry is an honest compression evaluation; only the terminal entry is programmed.
- `sequenceFunctionProgrammedTrace_final_output`: the programmed terminal entry remains an outer call and outputs the ideal reply.
- Supporting input/length preservation and honest-trace lemmas.

The blocker is that `adv_le_of_extFixedQueryRep_eq_on_good_filtered` requires equality for every fixed transcript, without a `Filt` premise. Yet the reveal carrier contains only `q` evaluation slots while a length-`p+q` transcript may contain more than `q` `Eval` calls unless `TaggedBudgetRespects` is assumed. Such omitted calls are also invisible to the frozen `Bad_SEQ`. Therefore the requested unconditional equality-on-good hypothesis is too strong.

The sound continuation requires either:

- an additive filtered representative endpoint whose equality premise includes `Filt t`, analogous to `adv_le_of_fixedQuery_ratio_of_good_filtered`; or
- changing the reveal carrier/`Bad_SEQ` to cover out-of-budget transcripts.

Both violate the “facade and step 2 unchanged” constraint.

Reuse map:

- Freshness: `not_Bad_SEQ_iff_compressionFresh`, `sequenceFunctionFreshCompressionValues_uniform`.
- Trace reconstruction: `sequenceFunctionCompressionTrace_final_output`.
- Intended mass template: CBC’s `condEquiv_of_transcript_mass_reductions`.
- Facade carriers: `RevealMap`, `SequenceFunctionICRealRevealMap`, `SequenceFunctionICIdealRevealMap`.

Verification:

- `lake build SequenceHash.RandomSystems.SequenceMACGenericFiberMass` passed.
- Whole-repository `lake build` passed: 8,441 jobs.
- No `sorry`, `admit`, `axiom`, or `private`.
- Axioms: `[propext, Classical.choice, Quot.sound]`.
- No `B_SEQ`, `h_badmass`, or final theorem added.