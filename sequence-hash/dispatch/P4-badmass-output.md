Implemented the accepted valve skeleton, sorry-free. The full leaf counting and `_final` headline remain deliberately deferred.

The implementation is in [SequenceMACGenericCount.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericCount.lean:28). No existing headline or bridge file was modified.

### SequenceHash adaptation

| Paper/CBC contribution | SequenceHash effect | Status |
|---|---|---|
| Input ambiguity and prefix aliasing | Killed by field framing and prefix-freeness | Excluded from events |
| Inner/outer related-key events | Killed by distinct role headers | Excluded |
| Cross-role input aliasing | Killed at encoded-input level | Excluded |
| Compression-call internal collision | Domain separation does not prevent equal `(state, block)` calls | Remains |
| Primitive input hit | Secret-bearing inputs limit steering, but fresh-state counting is still needed | Remains: `pqλ/2^c` |
| Single construction collision | Cascade-inherent | Remains: `C(q,2)(λ+2)/2^c` |
| Double collision/equal-top merge | Cascade-inherent corrected-BPR05 corner | Named: `sequenceGraphBad_equalTop` |
| Raw-key repeats | Reduced to birthday mass | Remains in `B_key` |
| Secret-bearing primitive guessing | Reduced to key guessing, but generic `MDCodec` does not yet expose the relevant call-site injection | Named key leaf |
| Long-key/customization derivation | Small accountable contribution | Named derive leaf; target is zero for `rK=rS=0` |

### Proven structure

- Exact `Bad_SEQ = PrimHit ∨ ConstructionCollision`.
- Cover:
  `Bad_SEQ ⊆ CascadeBad_SEQ ∪ KeyBad_SEQ ∪ DeriveBad_SEQ`.
- Construction collisions split into unique single-collision or double-collision graph cases.
- Cascade cover:
  `CascadeBad_SEQ ⊆ CascadePrimHit_SEQ ∪ CascadeSingleColl_SEQ ∪ CascadeGraphBad_SEQ`.
- Additive cascade assembly into `B_cascade`.
- Additive complete assembly into `B_SEQ`.
- Final skeleton theorem `sequenceFunction_badmass_of_named_leaves`, producing the required `h_badmass` from the named leaves.

The covers are at [line 136](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericCount.lean:136), the named leaves at [line 281](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericCount.lean:281), and probability assembly at [line 385](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericCount.lean:385).

### Sub-bound status

| Sub-bound | Status |
|---|---|
| `h_primHit` | Named, not yet discharged |
| `h_singleColl` | Named, not yet discharged |
| `sequenceGraphBad_equalTop` | Named honest residual |
| `h_key` | Named, not yet discharged |
| `h_derive` | Named, not yet discharged |
| `h_cascade` assembly | Proven |
| Complete `h_badmass` assembly | Proven modulo named leaves |
| `sequenceMAC_generic_prf_tight_final` | Not added under the valve |

Adding `_final` now would incorrectly suggest equal-top is already the only residual. The next work is to expose codec-level secret-bearing sites, relate digest cardinality to `2^c`, discharge the uniform/counting leaves, and instantiate `KeyPointMassBound` and `SequenceFunctionTraceBound`; then `_final` can honestly carry only `sequenceGraphBad_equalTop`.

Reused framework facts include `Bad_SEQ`, revealed construction/primitive input definitions, `extendedTranscriptDistRep`, `mass_mono`, `mass_or_le`, `List.nodup_iff_injective_get`, and the existing `B_cascade`, `B_key`, `deriveCostGeneric`, and `B_SEQ`. No generic theorem was specialized or duplicated.

Validation:

- `lake build SequenceHash.RandomSystems.SequenceMACGenericCount` — passed.
- `lake build RandomSystems RandomSystemsCC SequenceHash` — passed.
- `lake run htechniqueSurfaceAudit` — passed.
- Axiom audit for all new assembly theorems: `{propext, Classical.choice, Quot.sound}`.
- No `private`, `sorry`, `admit`, or new axioms.