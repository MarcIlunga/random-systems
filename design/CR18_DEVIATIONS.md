# CR18 — Deviations from the Lecture Notes

Items where Maurer's CR18 text is **technically wrong or incomplete**, so the Lean
formalization deliberately differs from the notes. Each deviation is also marked in code
with a `-- DEVIATION FROM CR18 (<Def id>): …` comment and carries the `[!]` status marker
in `CR18_FORMALIZATION_CHECKLIST.md`.

A deviation is recorded **only** when the lecture note itself is unsound (e.g. asserts a
non-well-formed object, an "easy to see" that is false, or a definition that violates a
standing requirement). A mere implementation bug against a *correct* note is fixed, not
recorded here.

Format per entry:

```
## <item id> — <one-line title>
- **Maurer says:** <the exact claim / equation>
- **Why it's wrong:** <counterexample or argument>
- **What we do instead:** <the sound design>
- **Marked in:** RandomSystems/CR18/<file>.lean (<symbol>), checklist row <id> = [!]
- **Found by:** contrarian review, <date>
```

---

<!-- entries appended below by the contrarian-review stage -->

## 4.8 — Bit-guessing performance is mis-calibrated (`−1/2` should be `−1`)
- **Maurer says:** Definition 4.8 (and the referenced Definition 2.9, and the
  IND-CPA discussion in §2.3.1) literally prints the bit-guessing advantage as
  `[S;B](D) := Λ_D(S,B) = 2 · Pr_{D·(S,B)}[κ(D,S) = B] − 1/2`.
- **Why it's wrong:** the printed constant `−1/2` is a typo. Concrete
  counterexamples:
  1. A guesser that is always correct has `Pr[κ(D,S)=B] = 1`, giving
     `Λ = 2·1 − 1/2 = 3/2 > 1`. This violates Maurer's own assertion in the
     very same definition that "the performance is between −1 and 1" and that
     "performance 1 means D's guess is correct with probability 1" (which forces
     the subtracted constant to be `1`, since `2·1 − 1 = 1`). Likewise a
     never-correct guesser (`Pr = 0`) gives `−1/2`, not the stated `−1`.
  2. The Lemma 2.3 proof chain
     `Λ_D(S_U,U) = 2·(½·Pr_{S0}(Z=0) + ½·Pr_{S1}(Z=1)) − c
                 = Pr_{S1}(Z=1) − Pr_{S0}(Z=1) = Δ_D(S₀,S₁)`
     only closes for `c = 1` (with `c = 1/2` it evaluates to `½ + Δ ≠ Δ`).
     Numeric witness: perfect distinguisher with `Pr_{S1}(Z=1)=1`,
     `Pr_{S0}(Z=1)=0` gives `Δ = 1`; the `−1/2` formula yields `3/2 ≠ 1`,
     the `−1` formula yields `1 = Δ`.
- **What we do instead:** implement the standard, correctly-calibrated advantage
  `Λ_d(S,B) := 2·(Pr[κ(d,S)=B] − 1/2) = 2·Pr[κ(d,S)=B] − 1`, which matches
  Maurer's prose anchors (range `[−1,1]`, `1 ⇔ Pr=1`, `−1 ⇔ Pr=0`) and the
  Lemma 2.3 identity `Λ_D(S_U,U) = Δ_D(S₀,S₁)`.
- **Marked in:** RandomSystems/CR18/Game.lean (`Def48.BitGuessingStructure.advantageDet`,
  also `performance`), checklist row 4.8 = [!]
- **Found by:** contrarian review, 2026-06-09
