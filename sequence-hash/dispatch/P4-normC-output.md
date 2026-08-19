Valve taken after Steps 1–2. The additions are sorry-free and all build gates are green, but `h_norm` is not yet discharged.

Completed:

- Public `QBounded` in [PFunDDS.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/PFunDDS.lean:35).
- `budgetHist_qBounded`, reusing `primCount_add_evalCount`, plus `budgetHist_nil` in [SequenceMACGeneric.lean](/Users/marcilunga/Documents/tob/research/random-systems/sequence-hash/SequenceHash/RandomSystems/SequenceMACGeneric.lean:61).
- History-dependent `padRespecting`, whose subtype-valued state maintains `P` after every query, in [FilterDomNormalization.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/FilterDomNormalization.lean:577).
- Exact-query theorem `queriesExactly_ddToDDE_padRespecting` at [FilterDomNormalization.lean:740](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/FilterDomNormalization.lean:740).
- `distinguisherRespects_padRespecting` at [Derivation.lean:1707](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/Derivation.lean:1707).

A further soundness correction emerged: the requested generic lemma is false without `P []`. For example, `P := False` satisfies `PrefixClosed`, `QExtensible P q`, and `QBounded P q` vacuously, but no exact-query distinguisher can satisfy `DistinguisherRespects P`. Accordingly, `padRespecting` explicitly requires `h0 : P []`; `budgetHist_nil` supplies this for SequenceHash.

Remaining precise proof plan:

1. Prove a replay invariant aligning the admitted-query state of `suppressViolating` with `padRespectingState`, showing padding never replaces a suppressed query.
2. Use `QBounded` to prove the suppressed distinguisher must stop by query `q`; another admitted query would create a `P`-history of length `q+1`.
3. Prove the deterministic verdict equivalence against total systems, then lift it using `winProb_fTransform_left/right` and `winProb_congr_support`.
4. Derive advantage domination and the generic normalization theorem with either `P []` added explicitly or `QExtensible` strengthened to include it.
5. Instantiate it with `budgetHist_nil`, `budgetHist_qExtensible`, `budgetHist_qBounded`, and the real/ideal totality lemmas to obtain `_norm`.

Verification:

- `lake build RandomSystems RandomSystemsCC SequenceHash` — passed.
- `lake run htechniqueSurfaceAudit` — passed.
- Added theorem axioms: `{propext, Classical.choice, Quot.sound}`.
- No new `sorry`, `admit`, or `private`.
- Existing count-filter normalization and suppression lemmas remain unchanged.