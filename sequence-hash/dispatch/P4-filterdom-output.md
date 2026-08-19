Implemented the accepted step-1 checkpoint and valve-stopped the bridge.

Changes:

- Added public `PrefixClosed` and `prefixClosed_length_le`, using `<+:` and `List.IsPrefix.length_le`: [PFunDDS.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/PFunDDS.lean:23).
- Added DDS `filterDom`, with domain, subset, and output lemmas: [PFunDDS.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/PFunDDS.lean:283).
- Redefined DDS `filterQueries` directly as the length-bounded `filterDom` instance: [PFunDDS.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/PFunDDS.lean:311).
- Added PDS `filterDom` and `[simp] isProbDist_filterDom_iff`: [PDS.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/PDS.lean:96).
- PDS `filterQueries` retains its established pushforward spelling to preserve every downstream unfold unchanged. `filterQueries_eq_filterDom` is proved by `rfl`, certifying definitional equality with the length-bounded `filterDom` instance: [PDS.lean](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/PDS.lean:113).
- No downstream, R1–R6, CBC, sequence, or R4 proof body was changed.

Bridge valve

The general bridge cannot soundly reuse the current exact-`q` `Adv[q]` carrier. A distinguisher may issue a `P`-violating query, receive `none` from the domain filter, and continue. An exact-`q`, `P`-respecting environment cannot represent this without suppressing the violating query and internally self-answering `none`.

The precise intended replacement is:

```lean
DomEnvRespects P E :=
  ∀ {n} (t : TranscriptPrefix X Y n),
    EnvConsistent E t → P t.1.toList

StopsBy E q :=
  ∀ h, q ≤ h.length → E h = none
```

Define `domAdaptiveTranscriptAdvantage P S T` as the supremum over `q, E` satisfying `StopsBy E q ∧ DomEnvRespects P E`, using the statistical distance between the operational transcript laws
`Dist.fTransform (fun s => PFunDDS.transcript s E q) S.val` and its `T` analogue.

The normalization shell should state:

```lean
∀ D, D.isProbDist →
  ∃ q D', D'.isProbDist ∧
    (∀ d ∈ D'.support,
      StopsBy (ddToDDE d) q ∧ DomEnvRespects P (ddToDDE d)) ∧
    advantage D (filterDom P hP S) (filterDom P hP T) ≤
      advantage D' S T
```

Then the honest endpoint is:

```lean
Δ(filterDom P hP S.val, filterDom P hP T.val)
  ≤ domAdaptiveTranscriptAdvantage P S T
```

Support generalizations needed:

- `filterDom_apply_eq_some_iff` under `P xs`.
- `deterministicTranscriptDist_filterDom_eq` for respecting environments.
- Predicate versions of the `CondEquiv` mass reductions.
- A run-restricted replacement for `KStepTotal_filterQueries_of_KStepTotal`; ordinary `KStepTotal filterDom` is false unless every bounded history satisfies `P`.
- The suppress/self-answer normalization above. This is the resisting, load-bearing piece; ordinary exact-query padding is unsound because arbitrary prefix-closed predicates need not be extensible.

Verification:

- `lake build RandomSystems`: green, 8,441 jobs.
- `lake run htechniqueSurfaceAudit`: passed.
- Added declarations contain no `sorry`, `private`, `admit`, or `axiom`.
- Axiom line: DDS declarations require none; PDS probability lemmas use exactly `[propext, Classical.choice, Quot.sound]`.