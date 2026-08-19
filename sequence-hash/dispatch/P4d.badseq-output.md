Implemented in new additive module [SequenceMACGenericBad.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericBad.lean).

### Exact statements

`Bad_SEQ` ([line 67](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericBad.lean:67)) has type:

```lean
TranscriptPrefix (SequenceFunctionICQuery Block L users)
    (SequenceFunctionICReply L) (p + q) ×
  SequenceFunctionICReveal SequenceFunctionCompressionRole Block L
    users q lambda → Prop
```

It holds iff:

```lean
(∃ input,
  input ∈ constructionInputs ∧ input ∈ visiblePrimInputs) ∨
¬ constructionInputs.Nodup
```

Construction calls are flattened in `Fin q` evaluation-slot order and then `Fin lambda` call-slot order, omitting padding. Thus every `Prim` input is conventionally prior, while `Nodup` covers earlier same-role and cross-role construction collisions.

`KeyPointMassBound` ([line 89](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericBad.lean:89)) is the ratio-free conditional-min-entropy predicate:

```lean
∀ i key otherKeys,
  DK.val.mass (fun keys =>
      keys i = key ∧
      ∀ j : {j // j ≠ i}, keys j.1 = otherKeys j) ≤
    ((2 : NNReal) ^ kappaStar)⁻¹ *
      DK.val.mass (fun keys =>
        ∀ j : {j // j ≠ i}, keys j.1 = otherKeys j)
```

It conditions on a complete assignment of every other user’s key, including zero-mass conditioning events.

`SequenceFunctionCrossRoleSeparated b S` ([line 110](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericBad.lean:110)) contains exactly:

- unconditional inner/outer input separation;
- long-key derivation versus inner/outer separation outside `DerivePrefixHit_SEQ`;
- long-customization derivation versus inner/outer separation under `DeriveSafeS_SEQ` and key support;
- long key/customization raw-input separation outside `DerivePrefixHit_SEQ`.

The discharge theorem is [sequenceFunctionCrossRoleSeparated](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericBad.lean:145).

### Reuse map

Reused directly:

- `SequenceFunctionICQuery`, `SequenceFunctionICReply`, `SequenceFunctionICReveal`
- `SequenceFunctionCompressionRole`, `TraceEntry`, and the trace/reveal carrier established around `sequenceFunctionCompressionTrace`
- canonical `sequenceFunctionInnerInput` and `sequenceFunctionOuterInput`
- `sequenceMACInnerInput_ne_outerInput`
- `sequenceMAC_keyDerive_separated_of_not_prefixHit`
- `sequenceMAC_customizationDerive_separated_of_safe`
- `DerivePrefixHit_SEQ` and `DeriveSafeS_SEQ`

No framework facts were generalized or duplicated.

### Verification

- `lake build SequenceHash.RandomSystems.SequenceMACGenericBad`: green
- Whole-repository `lake build`: green, 8441 jobs
- New module contains no `sorry`, `admit`, `axiom`, or `private`
- Axiom line:

```text
'SequenceHash.RandomSystemsModel.sequenceFunctionCrossRoleSeparated'
depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the new file was added; step-1 definitions and the requested existing modules were unchanged. No fiber equality, equality-on-good, `B_SEQ`, endpoint theorem, or `h_badmass` was introduced, so steps 3–4 remain untouched.