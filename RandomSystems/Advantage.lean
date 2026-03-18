/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Equiv
import RandomSystems.StatDist

/-!
# Advantage and Delta

Lean 4 formalization of Definitions 11-12 from Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `advantage S T` — the distinguishing advantage (Definition 11)
* `delta S T` — the infimum statistical distance (Definition 12)

## Main Results

* `advantage_self` — Adv(S, S) = 0 (proved)
* `advantage_respects_equiv` — Adv is well-defined on equivalence classes (proved)
* `advantage_triangle` — triangle inequality (proved)
* `delta_le_statDist` — Δ(S, T) ≤ δ(S.dist, T.dist) (proved)

## Design Notes

The advantage is the supremum over non-adaptive input sequences
of the statistical distance between transcript distributions.

Delta is the infimum over equivalent PDS pairs of the statistical
distance between the underlying DDS distributions. Theorem 1 shows
these are equal.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- The distinguishing advantage between two PDS.

Paper Definition 11:
  Adv(S, T) := sup_e δ(tr(S, e), tr(T, e))

Using Lemma 5, we optimize over non-adaptive environments only.
For finite X, the set of input sequences is finite, so the sup
is a finite max (using `Finset.sup` with ⊥ = 0 for NNReal). -/
def advantage [Fintype X] (S T : PDS X Y q) : NNReal :=
  Finset.sup Finset.univ
    (fun inputs => statDist (S.transcriptDist inputs) (T.transcriptDist inputs))

/-- Restricted distinguishing advantage: supremum over a subset of input sequences.

This is the same as `advantage`, but the supremum ranges only over those `inputs`
that satisfy `Good`. -/
def advantageOn [Fintype X] (S T : PDS X Y q) (Good : (Fin q → X) → Prop)
    [DecidablePred Good] : NNReal :=
  Finset.sup (Finset.univ.filter Good)
    (fun inputs => statDist (S.transcriptDist inputs) (T.transcriptDist inputs))

/-! ### Adaptive advantage (paper Definition 11)

The paper defines the optimal distinguishing advantage as the supremum over all compatible
deterministic environments (DDE). Our earlier `advantage` optimizes only over non-adaptive
input sequences; this is convenient for many proofs, but it is *not* the paper definition.

The definitions below follow the paper. -/

/-- The adaptive distinguishing advantage between two PDS: supremum over DDE environments. -/
def advantageAdaptive [Fintype X] [Fintype Y] [DecidableEq Y] (S T : PDS X Y q) : NNReal :=
  Finset.sup Finset.univ
    (fun e => statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e))

/-- Restricted adaptive distinguishing advantage: supremum over environments satisfying `Good`. -/
def advantageAdaptiveOn [Fintype X] [Fintype Y] [DecidableEq Y]
    (S T : PDS X Y q) (Good : DDE X Y q → Prop)
    [DecidablePred Good] : NNReal :=
  Finset.sup (Finset.univ.filter Good)
    (fun e => statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e))

/-- `Adv(S, S) = 0`. A system is perfectly indistinguishable from itself. -/
theorem advantage_self [Fintype X] (S : PDS X Y q) :
    advantage S S = 0 := by
  simp only [advantage]
  apply le_antisymm
  · apply Finset.sup_le
    intro inputs _
    exact le_of_eq (statDist_self (S.transcriptDist inputs))
  · exact zero_le _

/-- The advantage respects PDS equivalence: if S ≡ S' and T ≡ T',
then Adv(S, T) = Adv(S', T').

This is why advantage is well-defined on random systems. -/
theorem advantage_respects_equiv [Fintype X]
    {S S' T T' : PDS X Y q}
    (hS : S ≡ₚ S') (hT : T ≡ₚ T') :
    advantage S T = advantage S' T' := by
  simp only [advantage]
  congr 1
  ext inputs
  rw [hS inputs, hT inputs]

/-- Triangle inequality for advantage.

  Adv(S, U) ≤ Adv(S, T) + Adv(T, U) -/
theorem advantage_triangle [Fintype X]
    (S T U : PDS X Y q) :
    advantage S U ≤ advantage S T + advantage T U := by
  simp only [advantage]
  apply Finset.sup_le
  intro inputs _
  let fST := fun i => statDist (S.transcriptDist i) (T.transcriptDist i)
  let fTU := fun i => statDist (T.transcriptDist i) (U.transcriptDist i)
  have h_st : fST inputs ≤ Finset.sup Finset.univ fST :=
    Finset.le_sup (Finset.mem_univ inputs)
  have h_tu : fTU inputs ≤ Finset.sup Finset.univ fTU :=
    Finset.le_sup (Finset.mem_univ inputs)
  calc statDist (S.transcriptDist inputs) (U.transcriptDist inputs)
      ≤ statDist (S.transcriptDist inputs) (T.transcriptDist inputs) +
        statDist (T.transcriptDist inputs) (U.transcriptDist inputs) :=
        statDist_triangle _ _ _
    _ ≤ _ := add_le_add h_st h_tu

/-- If statDist is bounded pointwise by ε, so is advantage.

This bridges direct statDist computations into the advantage framework. -/
theorem advantage_le_of_pointwise [Fintype X]
    (S T : PDS X Y q) (ε : NNReal)
    (h : ∀ inputs, statDist (S.transcriptDist inputs) (T.transcriptDist inputs) ≤ ε) :
    advantage S T ≤ ε := by
  simp only [advantage]
  exact Finset.sup_le (fun inputs _ => h inputs)

/-- If statDist is bounded pointwise on an admissible set of inputs, then the
restricted advantage is bounded by the same value. -/
theorem advantageOn_le_of_pointwise [Fintype X]
    (S T : PDS X Y q) (Good : (Fin q → X) → Prop) [DecidablePred Good] (ε : NNReal)
    (h : ∀ inputs, Good inputs →
      statDist (S.transcriptDist inputs) (T.transcriptDist inputs) ≤ ε) :
    advantageOn S T Good ≤ ε := by
  simp only [advantageOn]
  refine Finset.sup_le ?_
  intro inputs hmem
  have hGood : Good inputs := (Finset.mem_filter.mp hmem).2
  exact h inputs hGood

/-- `Adv_adapt(S, S) = 0`. -/
theorem advantageAdaptive_self [Fintype X] [Fintype Y] [DecidableEq Y] (S : PDS X Y q) :
    advantageAdaptive S S = 0 := by
  simp only [advantageAdaptive]
  apply le_antisymm
  · apply Finset.sup_le
    intro e _
    exact le_of_eq (statDist_self (S.adaptiveTranscriptDist e))
  · exact zero_le _

/-- Triangle inequality for adaptive advantage. -/
theorem advantageAdaptive_triangle [Fintype X] [Fintype Y] [DecidableEq Y]
    (S T U : PDS X Y q) :
    advantageAdaptive S U ≤ advantageAdaptive S T + advantageAdaptive T U := by
  simp only [advantageAdaptive]
  apply Finset.sup_le
  intro e _
  let fST := fun e => statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e)
  let fTU := fun e => statDist (T.adaptiveTranscriptDist e) (U.adaptiveTranscriptDist e)
  have h_st : fST e ≤ Finset.sup Finset.univ fST :=
    Finset.le_sup (Finset.mem_univ e)
  have h_tu : fTU e ≤ Finset.sup Finset.univ fTU :=
    Finset.le_sup (Finset.mem_univ e)
  calc statDist (S.adaptiveTranscriptDist e) (U.adaptiveTranscriptDist e)
      ≤ statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) +
        statDist (T.adaptiveTranscriptDist e) (U.adaptiveTranscriptDist e) :=
        statDist_triangle _ _ _
    _ ≤ _ := add_le_add h_st h_tu

/-- Pointwise bound implies an adaptive advantage bound. -/
theorem advantageAdaptive_le_of_pointwise [Fintype X] [Fintype Y] [DecidableEq Y]
    (S T : PDS X Y q) (ε : NNReal)
    (h : ∀ e, statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) ≤ ε) :
    advantageAdaptive S T ≤ ε := by
  simp only [advantageAdaptive]
  exact Finset.sup_le (fun e _ => h e)

/-- Pointwise bound on an admissible set of environments implies a restricted adaptive advantage
bound. -/
theorem advantageAdaptiveOn_le_of_pointwise [Fintype X] [Fintype Y] [DecidableEq Y]
    (S T : PDS X Y q) (Good : DDE X Y q → Prop) [DecidablePred Good] (ε : NNReal)
    (h : ∀ e, Good e →
      statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) ≤ ε) :
    advantageAdaptiveOn S T Good ≤ ε := by
  simp only [advantageAdaptiveOn]
  refine Finset.sup_le ?_
  intro e hmem
  have hGood : Good e := (Finset.mem_filter.mp hmem).2
  exact h e hGood

/-- Non-adaptive advantage is bounded by adaptive advantage (since non-adaptive environments are a
special case). -/
theorem advantage_le_advantageAdaptive [Fintype X] [Fintype Y] [DecidableEq Y]
    (S T : PDS X Y q) :
    advantage S T ≤ advantageAdaptive S T := by
  classical
  simp only [advantage, advantageAdaptive]
  apply Finset.sup_le
  intro inputs _
  have h_inputs :
      statDist (S.transcriptDist inputs) (T.transcriptDist inputs) =
        statDist (S.adaptiveTranscriptDist (DDE.nonadaptive inputs))
          (T.adaptiveTranscriptDist (DDE.nonadaptive inputs)) := by
    simp [PDS.adaptiveTranscriptDist_nonadaptive]
  -- `DDE.nonadaptive inputs` is one of the environments in the supremum defining `advantageAdaptive`.
  calc statDist (S.transcriptDist inputs) (T.transcriptDist inputs)
      = statDist (S.adaptiveTranscriptDist (DDE.nonadaptive inputs))
          (T.adaptiveTranscriptDist (DDE.nonadaptive inputs)) := h_inputs
    _ ≤ Finset.sup Finset.univ
          (fun e => statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e)) :=
        Finset.le_sup (f := fun e =>
          statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e))
          (Finset.mem_univ (DDE.nonadaptive inputs))

/-- The infimum statistical distance (Delta) between two PDS.

Paper Definition 12:
  Δ(S, T) := inf_{S'≡S, T'≡T} δ(S'.dist, T'.dist)

We use `sInf` over the set of values, avoiding the need for
`Fintype (PDS X Y q)` or decidability of equivalence. -/
def delta (S T : PDS X Y q) : NNReal :=
  sInf { d : NNReal | ∃ (S' : PDS X Y q) (T' : PDS X Y q),
    (S ≡ₚ S') ∧ (T ≡ₚ T') ∧ statDist S'.dist T'.dist = d }

/-- Δ(S, T) ≤ δ(S.dist, T.dist) — the trivial representative.

Taking S' = S and T' = T gives this bound. -/
theorem delta_le_statDist (S T : PDS X Y q) :
    delta S T ≤ statDist S.dist T.dist := by
  apply csInf_le
  · exact ⟨0, fun _ ⟨_, _, _, _, hd⟩ => hd ▸ zero_le _⟩
  · exact ⟨S, T, PDS.equiv_refl S, PDS.equiv_refl T, rfl⟩

/-- Δ(S, S) = 0 — a system has zero delta with itself. -/
theorem delta_self (S : PDS X Y q) : delta S S = 0 := by
  apply le_antisymm
  · calc delta S S ≤ statDist S.dist S.dist := delta_le_statDist S S
    _ = 0 := statDist_self S.dist
  · exact zero_le _

/-- Transport a security bound across equivalence.

If `Adv(S, T) ≤ ε` and `S ≡ S'`, `T ≡ T'`, then `Adv(S', T') ≤ ε`. -/
theorem transport_security_bound [Fintype X]
    {S S' T T' : PDS X Y q}
    (hS : S ≡ₚ S') (hT : T ≡ₚ T')
    {ε : NNReal} (h : advantage S T ≤ ε) :
    advantage S' T' ≤ ε := by
  rw [← advantage_respects_equiv hS hT]
  exact h

end RandomSystems
