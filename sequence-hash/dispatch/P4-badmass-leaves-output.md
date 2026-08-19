Valve applied. The four leaves cannot be discharged honestly from the current statements, so `_final` was not added.

I added the public cardinality theorem [Finite.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/Finite.lean:59):

```lean
card_hashOutput_eq_two_pow (L) :
  Fintype.card (HashOutput L) = 2 ^ (8 * L.val)
```

It reuses `card_hashOutput` and `pow_mul`.

### Precise blockers

| Leaf | Status | Blocker |
|---|---|---|
| `h_primHit` | Valved | The state space has width `8·L.val`, but the leaf takes an unrelated free `c`. The model supplies no proof that `c = 8·L.val`. |
| `h_singleColl` | Valved | Besides the free-`c` issue, the statement is undercounted: at `q = 1`, its RHS is zero, while `SingleColl_SEQ` still admits collisions between calls within that one evaluation. |
| `h_key` | Valved | `KeyBad_SEQ` currently contains only `KeyRepeat_SEQ`; the advertised secret-bearing primitive-guess event is absent. `MDCodec` exposes no designated secret-bearing call-site injection/recovery theorem. |
| `h_derive` | Not attempted after valve | The zero-cost route needs public lemmas transporting `rK = rS = 0` from `SequenceFunctionTraceBound` to absence of derive-role entries in both concrete traces and flattened revealed traces. |
| `sequenceGraphBad_equalTop` | Unchanged | Remains the named residual. |

Required repairs:

1. Fix `c := 8 * L.val` throughout the bound, or add a model-level cardinality invariant relating `c` to the chaining-state type.
2. Give construction calls evaluation/call-slot provenance and restrict the stated `choose q 2` leaf to cross-evaluation collisions; account for same-evaluation collisions separately.
3. Extend `KeyBad_SEQ` with the secret-guess event and expose a public codec/trace call-site injection sufficient to reduce it to `KeyPointMassBound`.
4. Add the trace-to-reveal no-derive lemmas for the zero-cost derivation case.

SequenceHash-specific adaptation remains:

| Effect | Classification |
|---|---|
| Framing ambiguity/prefix aliasing | Killed |
| Inner/outer related-key terms | Killed |
| Encoded cross-role aliasing | Killed |
| Internal compression-call collisions | Remaining |
| Same-evaluation cascade collisions | Remaining and currently unbudgeted |
| Key repetition/secret guessing | Remaining; secret event not yet modeled |
| Derivation cost at `rK=rS=0` | Should vanish after trace exposure |
| Equal-top graph corner | Remaining named residual |

Validation:

- `lake build RandomSystems RandomSystemsCC SequenceHash` — green, 8503 jobs.
- New theorem axioms: `[propext, Classical.choice, Quot.sound]`.
- No new `sorry`, `admit`, `private`, or axioms.
- `sequenceMAC_generic_prf_tight_final` was correctly not added.