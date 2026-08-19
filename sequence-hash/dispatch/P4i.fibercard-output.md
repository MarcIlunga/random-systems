Implemented the valve-safe portion in [SequenceMACGenericFiberMass.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGenericFiberMass.lean:365):

- `sequenceFunctionTerminalShift`
- `sequenceFunctionTerminalShift_state`
- `sequenceFunctionTerminalShift_compose`
- `sequenceFunctionTerminalShift_zero`
- `sequenceFunction_fiber_card`

The fiber theorem reuses `Counting.card_filter_shift_univ`; no counting engine was duplicated. It supports any freshness predicate preserved by the terminal shift, matching `cbc_fiber_card`’s abstraction.

I stopped before mass packaging because two required premises in the dispatch do not exist in the stated form:

- `DomainSeparation.lean` has inner/outer inequality and conditional outer injectivity, but no framed-outer `PrefixFree` theorem. Thus trace-event preservation under the shift still needs a new SequenceFunction trace-stability proof from `Bad_SEQ`’s global `Nodup`.
- `condEquiv_of_transcript_mass_reductions` assumes `hprod` and concludes `Shat |≡ T` for a Bool-output game. It cannot itself produce representative extended-mass equality, and introducing such a game would violate the R4/no-games discipline.

Remaining step 3 work is therefore:

1. Prove the shifted table reproduces every honest non-terminal trace entry and only translates terminal outputs.
2. Instantiate `sequenceFunction_fiber_card` for the `extSysFactorRep` event.
3. Prove the real/ideal extended fixed-query mass equality directly.
4. Package through `adv_le_of_extFixedQueryRep_eq_on_good_filtered_of_filter`.

Verification:

- Targeted build: green.
- Whole `lake build`: green, 8,441 jobs.
- No new `sorry`, `admit`, `axiom`, or `private`.
- Axioms for all four shift/fiber theorems: `{propext, Classical.choice, Quot.sound}`.

Step 4 is not yet the only remaining R4 work; the trace-stability and mass-packaging portion of step 3 remains.