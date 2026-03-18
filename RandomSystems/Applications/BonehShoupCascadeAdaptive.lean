/-
Boneh–Shoup §6.4 (prefix-free PRFs for long messages): Cascade construction (adaptive variant).

This file extends `Applications/BonehShoupCascade.lean` with the *adaptive* (environment-based)
advantage notion, i.e. supremum over deterministic environments `DDE`, rather than just fixed
input sequences.

This module is currently **not** imported by `RandomSystems.lean`, so it can serve as a staging
ground while we adapt the proof.
-/
import RandomSystems.Applications.BonehShoupCascade

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems.Applications

namespace BonehShoup6_4

/-! ### Prefix-free restriction for adaptive environments -/

variable {K X : Type*} {ℓ q : ℕ}

-- Helper: take the first `i` outputs out of a full `q`-vector of outputs.
private def prevOutputs (ys : Fin q → K) (i : Fin q) : Fin i.val → K :=
  fun j => ys ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩

-- Inputs chosen by an adaptive environment when fed a hypothetical output sequence `ys`.
private def inputsOfEnv (e : DDE (Msg X ℓ) K q) (ys : Fin q → K) : Fin q → Msg X ℓ :=
  fun i => e.choose i (prevOutputs (K := K) ys i)

/-- Prefix-free deterministic environments: for every possible output history, the induced
input sequence is prefix-free (Boneh–Shoup Definition 4.5 / §6.4). -/
def PrefixFreeEnv (K X : Type*)
    [Fintype K] [DecidableEq K]
    [Fintype X] [DecidableEq X]
    (ℓ q : ℕ) [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)] :
    DDE (Msg X ℓ) K q → Prop :=
  fun e => ∀ ys : Fin q → K, PrefixFree X ℓ q (inputsOfEnv (K := K) (X := X) (ℓ := ℓ) (q := q) e ys)

instance {K X : Type*} [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
    (ℓ q : ℕ) [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)] :
    DecidablePred (PrefixFreeEnv (K := K) (X := X) ℓ q) := by
  classical
  infer_instance

/-! ### Target theorem (adaptive version) -/

/--
Adaptive prefix-free security for the ideal cascade:

`Adv_adapt` ranges over *adaptive* deterministic environments (DDE), restricted to those that are
prefix-free regardless of the output history.

This is the natural RS analogue of Boneh–Shoup’s Attack Game 4.2 with the prefix-free restriction.

TODO: Adapt the proof of
`advantageOn_URFfunCascadeIdeal_URFfun_prefixFree_le_birthday`
to the adaptive setting, using environment-lifting for trace instruments + the adaptive
condition-based lemma `ConditionBased.advantageAdaptive_le_condition_failure`.
-/
theorem advantageAdaptiveOn_URFfunCascadeIdeal_URFfun_prefixFreeEnv_le_birthday
    {K X : Type*}
    [Fintype K] [DecidableEq K] [Nonempty K]
    [Fintype X] [DecidableEq X]
    {ℓ q : ℕ} [Fintype (Msg X ℓ)] [DecidableEq (Msg X ℓ)]
    [Fintype (Transcript (Msg X ℓ) K q)] [DecidableEq (Transcript (Msg X ℓ) K q)] :
    advantageAdaptiveOn (URFfunCascadeIdeal (K := K) (X := X) ℓ q)
      (Instances.URFfun (X := Msg X ℓ) (Y := K) (q := q))
      (PrefixFreeEnv (K := K) (X := X) ℓ q) ≤ birthdayBound (q * (ℓ + 1)) (Fintype.card K) := by
  classical
  -- The adaptive proof is not in place yet. We keep the statement (and a proof plan) here so
  -- downstream developments can depend on it once the proof is completed.
  --
  -- Key missing components:
  -- 1) A lemma relating tag-only interaction under `e` to trace-interaction under a lifted
  --    environment that only feeds the tag projection to `e`.
  -- 2) An adaptive variant of the trace-level “equal on good transcripts” lemma.
  -- 3) A bound on the adaptive failure probability (birthday term), ideally tightened to match
  --    the `O(q^2 * ℓ / |K|)` discussion in Boneh–Shoup (eq. (6.15)).
  --
  -- For now, we leave this as a placeholder.
  sorry

end BonehShoup6_4

end RandomSystems.Applications

