Implemented the sound general filter→restricted-advantage bridge.

The headline at [Derivation.lean:1909](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/Derivation.lean:1909) is:

```lean
(Δ(PFunPDS.filterDom P hP S.val,
   PFunPDS.filterDom P hP T.val) : ℝ)
  ≤ filteredAdaptiveTranscriptAdvantage
      (liftHist P) S T
```

with `KStepTotal S q`, `KStepTotal T q`, `PrefixClosed P`, and `DeltaFilterDomFiniteQueryNormalization`.

Key results:

- `liftHist P t := P t.1.toList` — [Derivation.lean:1693](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/Derivation.lean:1693).
- Respecting-environment filter invisibility:
  `deterministicTranscriptDist_filterDom_eq` — [Derivation.lean:1759](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/Derivation.lean:1759).
- Exact respecting randomized-distinguisher bridge — [Derivation.lean:1884](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/Derivation.lean:1884).
- General DDS filter evaluation and count-filter specialization — [AdaptiveLawBridge.lean:405](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/AdaptiveLawBridge.lean:405).
- Generic `filterDom` conditional-equivalence mass reductions; existing count-filter reductions are now one-line instances — [CondEquiv.lean:152](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/CondEquiv.lean:152).
- The length-`≤q` restricted advantage equals ordinary `adaptiveTranscriptAdvantage`, preserving the count-filter route — [Derivation.lean:1859](/Users/marcilunga/Documents/tob/research/random-systems/RandomSystems/HTechnique/Derivation.lean:1859).
- Extracted reusable singleton transcript-distance and probability-mixture lemmas instead of duplicating the old bridge proof.

Valve status: the bridge and base-transcript agreement are closed. The normalization explicitly includes the necessary respecting-completion obligation. An unconditional `padDDDDist` constructor was not claimed: prefix closure alone does not guarantee length-`q` respecting continuations—for example, `P l := l.length ≤ 1` at `q = 2`. A concrete budget predicate must establish `DeltaFilterDomFiniteQueryNormalization`; this is the precise remaining input for the SequenceHash thin chain.

Verification:

- `lake build RandomSystems RandomSystemsCC SequenceHash` — green, 8500 jobs.
- `lake run htechniqueSurfaceAudit` — passed.
- No new `sorry`, `admit`, `axiom`, `private`, `B_SEQ`, or `h_badmass`.
- New headline axioms: `[propext, Classical.choice, Quot.sound]`.
- No sequence, CBC, or R1–R6 proof body was modified.