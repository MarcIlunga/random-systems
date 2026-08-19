Implemented P4a.facade additively and without touching existing proofs.

New modules:

- [Generic ideal-compression facade](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/IdealCompression.lean)
  - `TaggedBudgetRespects` at [line 85](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/IdealCompression.lean:85)
  - Shared-`Prim` real/ideal resources and typed coins
  - Finite trace/reveal carriers and extended-representative facade
  - Real/ideal totality lemmas
  - `adv_le_of_extFixedQueryRep_eq_on_good_filtered` at [line 335](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/IdealCompression.lean:335)

- [SequenceHash specialization](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/IdealCompression.lean)
  - Frozen compression model at [line 35](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/IdealCompression.lean:35)
  - Frozen `SequenceFunctionTraceBound` at [line 67](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/IdealCompression.lean:67)
  - Canonical `sequenceFunction` evaluator at [line 101](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/IdealCompression.lean:101)

Frozen model:

```lean
structure SequenceFunctionCompressionModel (Block : Type u) (L : U128) where
  codec : MDCodec Block
  iv : HashOutput L
```

Digest and chaining state are both `HashOutput L`. The trace bound is parameterized by:

```lean
SequenceFunctionTraceBound model b S lambda rK rS
```

It bounds canonical `sequenceFunctionCompressionCost` for evaluation plus the key and customization derivation costs.

Reuse map:

- `adv_le_of_extFixedQueryRep_ratio_of_good_filtered`, specialized at ε = 0
- `extendedTranscriptDistRep`
- `fTransform_fst_extendedTranscriptDistRep`
- `functionEvaluatorRV`
- `functionEvaluatorProb_KStepTotal`
- `Dist.prodProbDist` and `Dist.uniform`
- Canonical `sequenceFunction`, `mdHash`, and `sequenceFunctionCompressionCost`

`EnvRespects` was not changed and none of its users were rewritten. `TaggedBudgetRespects` is a parallel public transcript predicate suitable for use inside it. The only existing-file edit from this task was an appended import in `HTechnique/All.lean`; pre-existing dirty changes were left untouched.

Validation passed:

- `lake build RandomSystems`
- `lake build SequenceHash`
- `lake build RandomSystems.HTechnique.All`
- `lake build RandomSystems.HTechnique.LegacyChecks`
- `lake run htechniqueSurfaceAudit`
- Forbidden-token scan: no `sorry`, `admit`, `axiom`, or `private` in either new module
- Axiom audit for new representative, trace-bound, and totality theorems: `{propext, Classical.choice, Quot.sound}` only

No dispatch-2 structural or bad-event obligation was discharged here.