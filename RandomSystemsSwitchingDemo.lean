/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystemsCC.ControlledNaturalLanguage

/-!
# Five presentations of the switching lemma

This talk-facing file only presents results that already exist in
`RandomSystems.SwitchingLemma` and `RandomSystems.HTechnique.Derivation`.
It introduces no replacement switching theorem or proof-search layer; the
controlled sentences live in `RandomSystemsCC.ControlledNaturalLanguage`.

* **Version 1** — CR18 Lemma 4.19 in ordinary Lean, with the repository's
  paper notation `𝖱`, `𝖯`, `⌈q⌉`, `Δ`: the condition-C reduction to the
  blind collision game, then the birthday bound.
* **Version 2** — the same two-edge calculation, each citation written as a
  controlled sentence (Maurer's own transitions on CR18 PDF page 62:
  Theorem 4.17, then Lemma 4.18).
* **Version 3** — the H-technique's law-level `ProbPDS` objects, URF real
  and URP ideal.  The **perfect** H-coefficient skeleton with its structure
  visible: no bad event, because collision transcripts have zero URP mass,
  so the fixed-query ratio holds on *every* transcript.
* **Version 4** — the reverse orientation, URP real and URF ideal, where
  the asymmetry bites: collision transcripts have positive ideal mass, so a
  **bad event is genuinely needed**.  The Patarin good/bad skeleton with
  `Bad := Collision`, defect `0`, and the adaptive birthday bound.
* **Version 5** — the summary granularity: one sentence citing a finished
  endpoint, for when the argument's structure is not the point.

`set_option trace.CryptoControlledNaturalLanguage.sentence true in` before
any theorem shows each sentence's stable label as it elaborates.
-/

noncomputable section

open RandomSystems
open RandomSystems.CR18
open PFunPDS.Prob (urf urp)
open HTechniqueDerivation (bday Collision urp_urf_fixedQuery_ratio
  urf_le_urp_fixedQuery_of_good probBad_urf_collision_le)
open scoped RandomSystems.CR18
  RandomSystems.CR18.HTechniqueDerivation
  CryptoControlledNaturalLanguage

namespace RandomSystemsSwitchingDemo

/-- Presentation notation for Maurer's filtered collision game `[q]R̂`. -/
local notation:max "⌈" q "⌉𝖱̂ " X:max =>
  gameOf (⌈q⌉ 𝖱 X) (collisionCond (X := X) (Y := X))

/-! ## Version 1: ordinary Lean, condition C

The two displayed edges are the established condition-C reduction and blind
collision-game bound from `RandomSystems.SwitchingLemma`. -/

/-- CR18 Lemma 4.19, using the existing ordinary-Lean endpoint. -/
theorem switching_via_condition_c_in_lean
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : Nat) :
    Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X) ≤
      (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ) := by
  calc Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X)
      ≤ (Γᵇ (⌈q⌉𝖱̂ X) : ℝ) :=
        filtered_urf_urp_advantage_le_blind_collision_game X q
    _ ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ) :=
        blindMaxWinProb_filterURF_collisionCond_le_birthday X q

/-! ## Version 2: condition C in controlled language -/

/-- The same two-edge calculation, with each citation written as a
controlled sentence. -/
theorem switching_via_readable_condition_c
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : Nat) :
    Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X) ≤
      (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ) := by
  calc
    Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X)
        ≤ (Γᵇ (⌈q⌉𝖱̂ X) : ℝ) := by
          According to the condition C theorem, we obtain the blind game bound using
            (filtered_urf_urp_advantage_le_blind_collision_game X q)
    _ ≤ (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ) := by
          It remains to analyze the blind game; the birthday lemma gives the bound using
            (blindMaxWinProb_filterURF_collisionCond_le_birthday X q)

/-! ## Version 3: perfect H coefficients, URP ideal

The full skeleton with the structure visible.  With the URP as the ideal
world, collision transcripts have zero ideal mass, so the fixed-query ratio
holds on every transcript and **no bad event is needed** — the whole
birthday defect is carried by ε.  The sentences hide only the degenerate
`defect > 1` branch, the totality side conditions, and the casts. -/

/-- Adaptive switching, URF real to URP ideal, via the perfect/no-bad
H-coefficient skeleton. -/
theorem switching_via_perfect_h_coefficients
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : Nat) :
    Adv[q](urf (X := X) (Y := X), urp (X := X)) ≤
      (bday q (Fintype.card X) : ℝ) := by
  We may assume the stated bound is at most one, since otherwise it holds
    trivially; call this assumption h_defect
  We apply the perfect H coefficient technique, with no bad transcripts
  The ratio of real to ideal probabilities is at least one minus the defect
    on every transcript, by (urp_urf_fixedQuery_ratio h_defect)
      ("collision transcripts have zero URP mass; permutation counting elsewhere")

/-! ## Version 4: H coefficients with a genuine bad event, URF ideal

The reverse orientation, where the asymmetry bites: collision transcripts
have **positive** ideal (URF) mass, so the good/bad split is genuinely
needed.  The two bullets are exactly Patarin's two legs. -/

/-- Adaptive switching, URP real to URF ideal, via the good/bad
H-coefficient skeleton at `Bad := Collision`. -/
theorem switching_via_bad_transcripts
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : Nat) :
    Adv[q](urp (X := X), urf (X := X) (Y := X)) ≤
      (bday q (Fintype.card X) : ℝ) := by
  We may assume the stated bound is at most one, since otherwise it holds
    trivially; call this assumption h_defect
  We apply the H coefficient technique: the bad event is Collision,
    the ratio defect is 0, and the bad probability is at most
    (bday q (Fintype.card X))
  · On good transcripts, the ratio of real to ideal probabilities is at least
      one minus the defect, by urf_le_urp_fixedQuery_of_good
        ("collision-free URP mass 1/(N)_q′ dominates URF mass 1/N^q′")
  · The probability of a bad transcript in the ideal world is at most the
      birthday bound, by (probBad_urf_collision_le h_defect)

/-! ## Version 5: one-sentence summaries

The summary granularity of the same language: when the argument's structure
is not the point, one sentence cites the finished endpoint. -/

/-- CR18 Lemma 4.19, citing the finished condition-C endpoint. -/
theorem switching_summary_condition_c
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : Nat) :
    Δ(⌈q⌉ 𝖱 X, ⌈q⌉ 𝖯 X) ≤
      (1 / 2 : ℝ) * (q : ℝ) ^ 2 / (Fintype.card X : ℝ) := by
  The condition C argument gives the switching bound using
    (urf_urp_switching X q)

/-- Adaptive switching, citing the finished perfect H-coefficient
endpoint. -/
theorem switching_summary_h_coefficients
    (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (q : Nat) :
    Adv[q](urf (X := X) (Y := X), urp (X := X)) ≤
      (bday q (Fintype.card X) : ℝ) := by
  The perfect H coefficient argument gives the switching bound using
    HTechniqueDerivation.urf_urp_switching

end RandomSystemsSwitchingDemo

end
