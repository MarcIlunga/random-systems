Implemented P4c.traces in one additive module: [SequenceMACGenericTrace.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericTrace.lean).

- Generic MD machinery:
  - `MDCompressionCall`, `mdCompressionTrace`
  - exact `blockify` length theorem
  - `mdCompressionTrace_reconstruct`
  - `mdCompressionTrace_final_output`

- Canonical SequenceFunction machinery:
  - derive-key / derive-customization / inner / outer role tags
  - `sequenceFunctionCompressionTrace`
  - exact trace length
  - four-call schedule witness for `sequenceFunctionCompressionCost`
  - length bound from `SequenceFunctionTraceBound`
  - fixed-size `EvalTrace` padding and preservation theorems
  - final outer entry outputs exactly `sequenceFunctionICEval`

- Output backing:
  - `SequenceFunctionOutputCompressionBacked`
  - precise codec premise:
    `MDCodecBlockifyNonemptyInput codec := ∀ input, input ≠ [] → codec.blockify input ≠ []`
  - proved via `SequenceFunctionOutputCompressionBacked.of_blockifyNonemptyInput`
  - The current List API has no `List.Nonempty`, so the propositions use the equivalent `≠ []` spelling.

Reuse map: `mdHash`, `mdIterate`, `MDCodec.blockify`, canonical `sequenceFunction`, `sequenceFunction{Inner,Outer}Input`, `derive`, `sequenceFunctionICEval`, `sequenceFunctionCompressionCost`, `sequenceFunctionEvalCost`, `SequenceFunctionTraceBound.evalCost_apply_le`, `TraceEntry`, and `EvalTrace`.

Verification:

- Targeted build: 8319 jobs, green.
- Whole `lake build`: 8441 jobs, green.
- No `sorry`, `admit`, `axiom`, or `private` in the new module.
- Every new theorem’s axiom line is contained in `{propext, Classical.choice, Quot.sound}`.
- Existing source files and mtimes were untouched.
- No `Bad_SEQ`, equality-on-good, `B_SEQ`, theorem endpoint, or `h_badmass`; steps 2–4 remain untouched.