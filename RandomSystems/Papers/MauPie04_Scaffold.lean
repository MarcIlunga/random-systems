/-
Paper scaffold (offline): Maurer–Pietrzak (2004)
"Composition of Random Systems: When Two Weak Make One Strong"

This file is intentionally a *scaffold*:
- It records (names + Lean-shaped statements) of the paper objects we expect to
  formalize next.
- It is NOT imported by `RandomSystems.lean` yet, so it does not affect builds.
- Fill these in when we start the full MauPie04 maximum-condition development.
-/
import RandomSystems.ConditionBased

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Papers.MauPie04

/-!
## What we want from MauPie04

`random-systems/papers/MauPie04.md` introduces a "maximum condition" technique
that turns non-adaptive indistinguishability statements about *components* into
adaptive indistinguishability of a *composition*.

The eventual goal is to support cascade-style constructions (and later NMAC/HMAC).

For now we only record the key items:
- Definition 8: maximum condition `A := F ↓ G`
- Lemmas 3/5/6: bounds relating `Adv_k(F,G)` to failure probabilities of `A`
- Definition 10: composition operators `⋆` and `∘`
- Theorem 1/2: applications to `⋆` (random functions) and `∘` (random permutations)

This repo already has a Maurer-2002-style condition framework in
`RandomSystems/ConditionBased.lean`. MauPie04 adds an extra layer: the maximum
condition and a submartingale inequality.
!-/

namespace Placeholders

variable {X Y : Type*} {q : ℕ}
  [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)]

/-!
### Definition 10 (composition operators)

We eventually want a generic way to combine random systems; for the RS model
here, that is easiest to phrase as an operation on DDS, then lifted to PDS.

We leave the details open for now (independence/product distribution of PDS).
!-/

-- TODO: a general product distribution `Dist.prod` to sample independent DDSs.
-- TODO: a lifted operator `PDS.star`/`PDS.circle` that samples two systems independently.

/-!
### Maximum condition (Definition 8)

The maximum condition depends on a pair of systems `F,G` and produces a
monotone condition `A` (in our setting: a `TranscriptCondition`).

This is *not* just "no collision"; it is defined via a likelihood ratio / max
condition over transcript probabilities.
!-/

-- TODO: define maximum condition for finite PDS transcript distributions.
-- def maximumCondition (F G : PDS X Y q) : TranscriptCondition X Y q := by
--   ...

/-!
### Key paper lemmas (statements only, to be refined)
!-/

-- TODO: Lemma 3/5/6: relate advantage to failure of the maximum condition.
-- The final forms in this repo may differ slightly because `advantage` is
-- defined via non-adaptive input sequences.
--
-- theorem advantage_le_maximumCondition_failure
--     (F G : PDS X Y q) :
--     advantage F G ≤ _ := by
--   sorry

end Placeholders

end RandomSystems.Papers.MauPie04

