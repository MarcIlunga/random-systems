Implemented in [DomainSeparation.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/DomainSeparation.lean:1), purely additively: one new file, 171 lines, no existing proof or statement changed.

New public results:

- Header preservation and separation:
  - `take_eight_headerI`
  - `take_eight_headerO`
  - `take_eight_headerI_append`
  - `take_eight_headerO_append`
  - `headerI_ne_headerO`

- Unconditional framed-role separation:
  - `sequenceMACInnerInput_ne_outerInput` ([line 67](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/DomainSeparation.lean:67))
  - `sequenceHashInnerInput_ne_outerInput` ([line 83](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/DomainSeparation.lean:83))

- Within-role injectivity:
  - Existing `RandomSystemsModel.sequenceMACInnerInput_injective` reused unchanged.
  - `sequenceHashInnerInput_injective` ([line 98](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/DomainSeparation.lean:98))
  - `sequenceMACSeparatedOuterCall_injective_of_innerTag_injective`
  - Raw-list form `sequenceMACSeparatedOuterInput_injective_of_innerTag_injective` ([line 125](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/DomainSeparation.lean:125)).

The outer-input statement necessarily assumes `Function.Injective a.2.2.2`: outer framing contains only the item count and inner digest, so unconditional injectivity in `M` would be false.

DERIVE verdict: **(b), conditional**. The exact conditions are:

```lean
¬ List.IsPrefix (headerI b fSeqMac K.1) deriveInput
```

for separation from inner inputs, and

```lean
¬ List.IsPrefix (headerO b fSeqMac S K.1) deriveInput
```

for separation from outer inputs. The resulting lemmas are at [lines 144–169](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/DomainSeparation.lean:144). Instantiate `deriveInput` with either `K.1.val` or `S.val`. Separation is not unconditional because `derive` hashes those raw strings without a role header.

Reuse map:

- `encodeItems_injective`: direct proof of SequenceHash inner injectivity.
- `sequenceMACSeparatedOuterCall_collision`: direct basis of both outer-injectivity lemmas.
- `sequenceMACInnerInput_injective` and `encodeMSBF_injective`: reused through that existing collision theorem; its framing core was not duplicated.
- Canonical `sequenceHash*Input` and `sequenceMAC*Input` definitions used directly.

Verification:

- `lake build SequenceHash`: green, 8318 jobs.
- `lake build`: green, 8440 jobs.
- Every new theorem has axioms exactly `{propext, Classical.choice, Quot.sound}`.
- No `private`, `sorry`, `admit`, or `axiom`.
- Scoped diff: `1 file changed, 171 insertions`.