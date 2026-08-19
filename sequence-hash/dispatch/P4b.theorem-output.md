I stopped under the mandatory split clause. No files or source mtimes changed; `SequenceMACGeneric.lean` remains absent.

The frozen equality-on-good claim is not derivable from the named separation results:

- [`sequenceMACInnerInput_ne_outerInput`](</Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/DomainSeparation.lean:67>) separates complete byte strings.
- The R5 bridges at [`SequenceMACIndiffMD.lean:202`](</Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACIndiffMD.lean:202>) and [`:223`](</Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACIndiffMD.lean:223>) also prove byte-string separation, conditionally on key/support facts.
- None proves pairwise disjointness of individual MD compression inputs `(chainingState, block)`.

Distinct framed messages can still have internal cross-role compression collisions. Such a collision is excluded by neither `SameRoleCollision` nor the other four proposed events. On that transcript, a final outer call may reuse an existing compression-table point, so the real extended mass and the ideal independent-function mass need not agree.

The accepted sketch itself labels compression-level cross-role separation as “not-yet-formal” at [`A4-tight-generic-prf.md:116`](</Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/sketches/A4-tight-generic-prf.md:116>). The task’s request to discharge it using existing lemmas therefore overstates the current API.

Recommended finer split:

1. Resolve the statement: either make compression-level cross-role separation a genuine explicit hypothesis, or extend `Bad_SEQ` to cover cross-role compression collisions. The latter may require revisiting the claimed §5 bound.
2. Prove canonical MD compression traces, real/hybrid ideal reveal maps, trace reconstruction, and length bounds.
3. Prove the uniform-function partial-assignment fiber equality, then define `B_SEQ`, state the precise `h_badmass`, and close with `adv_le_of_extFixedQueryRep_eq_on_good_filtered`.

One additional deep-bound requirement should be frozen: because `keysP` is an arbitrary joint law on `Fin u → SequenceMACKey`, `KeyPointMassBound` must express conditional per-user min-entropy or require an independent product law. Marginal point-mass bounds alone do not imply the `KeyRepeat` term.