/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.PDS
import RandomSystems.Coupling

/-!
# PDS Equivalence

Lean 4 formalization of the non-adaptive equivalence relation used by the
current random-system development.

## Main Definitions

* `PDS.equivNonadaptive` — equality of transcript distributions for all fixed
  input sequences.
* `PDS.equivAdaptive` — equality of transcript distributions for all DDEs,
  matching Lanzenberger-Maurer Definition 10.
* `PDS.equiv` — current project default, an alias for `PDS.equivNonadaptive`.

## Main Results

* `PDS.equiv_refl` — equivalence is reflexive (proved)
* `PDS.equiv_symm` — equivalence is symmetric (proved)
* `PDS.equiv_trans` — equivalence is transitive (proved)
* `PDS.equivAdaptive_iff_nonadaptive` — the real Lemma 5 statement

## Design Notes

Paper Definition 10: S ≡ T iff tr(S, e) = tr(T, e) for all compatible
environments e.

Paper Lemma 5: It suffices to check non-adaptive environments.  The actual
adaptive-to-non-adaptive bridge is `PDS.equivAdaptive_iff_nonadaptive`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

variable {X Y : Type*} {q : ℕ}
  [Fintype (DDS X Y q)]
  [Fintype (Transcript X Y q)]
  [DecidableEq (Transcript X Y q)]

/-- Non-adaptive equivalence: two PDS produce the same transcript distributions
for all fixed input sequences.

This is the non-adaptive equivalence relation used by the existing random-system
development.  It is not, by itself, the full adaptive equivalence relation from
Lanzenberger-Maurer Definition 10. -/
def PDS.equivNonadaptive (S T : PDS X Y q) : Prop :=
  ∀ (inputs : Fin q → X), S.transcriptDist inputs = T.transcriptDist inputs

/-- Adaptive equivalence, matching Lanzenberger-Maurer Definition 10: two PDS
produce the same transcript distributions for all deterministic discrete
environments. -/
def PDS.equivAdaptive (S T : PDS X Y q) : Prop :=
  ∀ (e : DDE X Y q), S.adaptiveTranscriptDist e = T.adaptiveTranscriptDist e

/-- Current project default equivalence.

This remains non-adaptive to avoid disrupting the existing development.  The
real bridge to adaptive equivalence is `PDS.equivAdaptive_iff_nonadaptive`. -/
def PDS.equiv (S T : PDS X Y q) : Prop :=
  PDS.equivNonadaptive S T

/-- PDS equivalence notation. -/
scoped notation:50 S " ≡ₚ " T => PDS.equiv S T

/-- PDS equivalence is reflexive. -/
theorem PDS.equiv_refl (S : PDS X Y q) : S ≡ₚ S :=
  fun _ => rfl

/-- PDS equivalence is symmetric. -/
theorem PDS.equiv_symm {S T : PDS X Y q} (h : S ≡ₚ T) : T ≡ₚ S :=
  fun inputs => (h inputs).symm

/-- PDS equivalence is transitive. -/
theorem PDS.equiv_trans {S T U : PDS X Y q}
    (h₁ : S ≡ₚ T) (h₂ : T ≡ₚ U) : S ≡ₚ U :=
  fun inputs => (h₁ inputs).trans (h₂ inputs)

/-- PDS equivalence is an equivalence relation. -/
theorem PDS.equiv_equivalence : Equivalence (PDS.equiv (X := X) (Y := Y) (q := q)) where
  refl := PDS.equiv_refl
  symm := PDS.equiv_symm
  trans := PDS.equiv_trans

/-- Two PDS with the same distribution are equivalent. -/
theorem PDS.equiv_of_eq {S T : PDS X Y q} (h : S = T) : S ≡ₚ T := by
  subst h; exact PDS.equiv_refl S

/-! ## Adaptive/non-adaptive bridge helpers

The deterministic replay primitives used below now live in
`RandomSystems.Transcript`: `Transcript.inputs`, `Transcript.outputs`,
`Transcript.outputPrefix`, `DDE.FollowsTranscript`,
`DDE.transcriptOfOutputs`, and
`DDS.interact_eq_transcript_iff_of_follows`.
-/

/-- If an environment does not follow transcript `t`, then no deterministic
system can produce `t` when interacting with that environment. -/
theorem PDS.adaptiveTranscriptDist_apply_eq_zero_of_not_follows
    (S : PDS X Y q) (e : DDE X Y q) (t : Transcript X Y q)
    (hnot : ¬ DDE.FollowsTranscript e t) :
    S.adaptiveTranscriptDist e t = 0 := by
  classical
  rw [PDS.adaptiveTranscriptDist_apply_eq_sum]
  exact Finset.sum_eq_zero fun s hs => by
    have hs_interact : interact s e = t := (Finset.mem_filter.mp hs).2
    exact False.elim (hnot (DDE.followsTranscript_of_interact_eq s e t hs_interact))

/-- The output-history distribution induced by an adaptive environment. -/
def PDS.adaptiveOutputDist [DecidableEq (Fin q → Y)]
    (S : PDS X Y q) (e : DDE X Y q) : Dist (Fin q → Y) :=
  Dist.fTransform Transcript.outputs (S.adaptiveTranscriptDist e)

/-- Adaptive transcripts are the deterministic replay of their output-history
distribution through the environment. -/
theorem PDS.adaptiveTranscriptDist_eq_output_pushforward
    [DecidableEq (Fin q → Y)]
    (S : PDS X Y q) (e : DDE X Y q) :
    S.adaptiveTranscriptDist e =
      Dist.fTransform (DDE.transcriptOfOutputs e) (PDS.adaptiveOutputDist S e) := by
  classical
  unfold PDS.adaptiveOutputDist
  rw [Dist.fTransform_comp]
  ext t
  rw [Dist.fTransform_apply_eq_sum]
  by_cases hfollow : DDE.FollowsTranscript e t
  · symm
    rw [Finset.sum_eq_single t]
    · intro u hu hne
      by_cases hufollow : DDE.FollowsTranscript e u
      · have hu_eq : DDE.transcriptOfOutputs e (Transcript.outputs u) = u :=
          DDE.transcriptOfOutputs_outputs_eq_of_follows e u hufollow
        have hut : u = t := by
          rw [← hu_eq]
          exact (Finset.mem_filter.mp hu).2
        exact False.elim (hne hut)
      · exact PDS.adaptiveTranscriptDist_apply_eq_zero_of_not_follows S e u hufollow
    · intro hnotmem
      exact False.elim (hnotmem (by
        simp [DDE.transcriptOfOutputs_outputs_eq_of_follows e t hfollow]))
  · rw [PDS.adaptiveTranscriptDist_apply_eq_zero_of_not_follows S e t hfollow]
    symm
    have hsum :
        (∑ a ∈ (Finset.univ : Finset (Transcript X Y q)).filter
            (fun a => (DDE.transcriptOfOutputs e ∘ Transcript.outputs) a = t),
          (S.adaptiveTranscriptDist e) a) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      by_cases hufollow : DDE.FollowsTranscript e u
      · have hu_eq : DDE.transcriptOfOutputs e (Transcript.outputs u) = u :=
          DDE.transcriptOfOutputs_outputs_eq_of_follows e u hufollow
        have hut : u = t := by
          rw [← hu_eq]
          exact (Finset.mem_filter.mp hu).2
        exact False.elim (hfollow (hut ▸ hufollow))
      · exact PDS.adaptiveTranscriptDist_apply_eq_zero_of_not_follows S e u hufollow
    rw [hsum]

/-- For a fixed environment, adaptive transcript distance is exactly adaptive
output-history distance. -/
theorem statDist_adaptiveTranscriptDist_eq_adaptiveOutputDist
    [Fintype (Fin q → Y)] [DecidableEq (Fin q → Y)]
    (S T : PDS X Y q) (e : DDE X Y q) :
    statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) =
      statDist (PDS.adaptiveOutputDist S e) (PDS.adaptiveOutputDist T e) := by
  rw [PDS.adaptiveTranscriptDist_eq_output_pushforward (S := S) (e := e)]
  rw [PDS.adaptiveTranscriptDist_eq_output_pushforward (S := T) (e := e)]
  exact statDist_fTransform_injective
    (PDS.adaptiveOutputDist S e) (PDS.adaptiveOutputDist T e)
    (DDE.transcriptOfOutputs e) (DDE.transcriptOfOutputs_injective e)

/-- Point masses of adaptive output histories are point masses of their replayed
adaptive transcripts. -/
theorem PDS.adaptiveOutputDist_apply_eq_adaptiveTranscriptDist_replay
    [Fintype (Fin q → Y)] [DecidableEq (Fin q → Y)]
    (S : PDS X Y q) (e : DDE X Y q) (ys : Fin q → Y) :
    PDS.adaptiveOutputDist S e ys =
      S.adaptiveTranscriptDist e (DDE.transcriptOfOutputs e ys) := by
  rw [PDS.adaptiveTranscriptDist_eq_output_pushforward (S := S) (e := e)]
  rw [fTransform_injective_apply
    (PDS.adaptiveOutputDist S e) (DDE.transcriptOfOutputs e)
    (DDE.transcriptOfOutputs_injective e) ys]

/-- The output history generated by a stateless oracle in an adaptive
environment. -/
def DDE.outputHistoryOfOracle (e : DDE X Y q) (f : X → Y) : Fin q → Y :=
  Transcript.outputs (interact (DDS.ofFunq (q := q) f) e)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- First occurrence of the current input in a query prefix.

For query `i`, the `inputs` argument has length `i + 1`; this returns the
least position in that prefix whose input equals the current input. -/
noncomputable def DDS.firstInputIndex [DecidableEq X]
    (i : Fin q) (inputs : Fin (i.val + 1) → X) : Fin (i.val + 1) :=
  ((Finset.univ : Finset (Fin (i.val + 1))).filter
    (fun j => inputs j = inputs ⟨i.val, Nat.lt_succ_self i.val⟩)).min'
      (by
        refine ⟨⟨i.val, Nat.lt_succ_self i.val⟩, ?_⟩
        simp)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- The first occurrence selected from a query prefix has the current input
value. -/
theorem DDS.firstInputIndex_spec [DecidableEq X]
    (i : Fin q) (inputs : Fin (i.val + 1) → X) :
    inputs (DDS.firstInputIndex (q := q) i inputs) =
      inputs ⟨i.val, Nat.lt_succ_self i.val⟩ := by
  unfold DDS.firstInputIndex
  have hmem := Finset.min'_mem
    ((Finset.univ : Finset (Fin (i.val + 1))).filter
      (fun j => inputs j = inputs ⟨i.val, Nat.lt_succ_self i.val⟩))
    (by
      refine ⟨⟨i.val, Nat.lt_succ_self i.val⟩, ?_⟩
      simp)
  simpa using (Finset.mem_filter.mp hmem).2

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- The first occurrence is no later than any prefix position with the current
input value. -/
theorem DDS.firstInputIndex_le_of_eq [DecidableEq X]
    (i : Fin q) (inputs : Fin (i.val + 1) → X) (j : Fin (i.val + 1))
    (hj : inputs j = inputs ⟨i.val, Nat.lt_succ_self i.val⟩) :
    (DDS.firstInputIndex (q := q) i inputs).val ≤ j.val := by
  unfold DDS.firstInputIndex
  exact Finset.min'_le _ j (by simp [hj])

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- No position earlier than the selected first occurrence has the current input
value. -/
theorem DDS.ne_of_lt_firstInputIndex [DecidableEq X]
    (i : Fin q) (inputs : Fin (i.val + 1) → X) (j : Fin (i.val + 1))
    (hjlt : j.val < (DDS.firstInputIndex (q := q) i inputs).val) :
    inputs j ≠ inputs ⟨i.val, Nat.lt_succ_self i.val⟩ := by
  intro hj
  exact (Nat.not_lt_of_ge (DDS.firstInputIndex_le_of_eq (q := q) i inputs j hj)) hjlt

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- First occurrence of `u i` in the global prefix of `u` ending at `i`,
repackaged as an index of the full `Fin q` domain. -/
noncomputable def DDS.firstInputIndexGlobal [DecidableEq X]
    (u : Fin q → X) (i : Fin q) : Fin q :=
  ⟨(DDS.firstInputIndex (q := q) i
      (fun j : Fin (i.val + 1) =>
        u ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)).val,
    Nat.lt_of_le_of_lt
      (Nat.le_of_lt_succ
        (DDS.firstInputIndex (q := q) i
          (fun j : Fin (i.val + 1) =>
            u ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)).isLt)
      i.isLt⟩

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- The global first occurrence has the same input value as its target. -/
theorem DDS.firstInputIndexGlobal_spec [DecidableEq X]
    (u : Fin q → X) (i : Fin q) :
    u (DDS.firstInputIndexGlobal (q := q) u i) = u i := by
  unfold DDS.firstInputIndexGlobal
  simpa using DDS.firstInputIndex_spec (q := q) i
    (fun j : Fin (i.val + 1) =>
      u ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- The global first occurrence of `u i` is no later than `i`. -/
theorem DDS.firstInputIndexGlobal_le [DecidableEq X]
    (u : Fin q → X) (i : Fin q) :
    (DDS.firstInputIndexGlobal (q := q) u i).val ≤ i.val := by
  unfold DDS.firstInputIndexGlobal
  exact Nat.le_of_lt_succ
    (DDS.firstInputIndex (q := q) i
      (fun j : Fin (i.val + 1) =>
        u ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)).isLt

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Equal input values have the same global first occurrence. -/
theorem DDS.firstInputIndexGlobal_eq_of_eq [DecidableEq X]
    (u : Fin q → X) (i j : Fin q) (hij : u i = u j) :
    DDS.firstInputIndexGlobal (q := q) u i =
      DDS.firstInputIndexGlobal (q := q) u j := by
  apply Fin.ext
  let fi := DDS.firstInputIndexGlobal (q := q) u i
  let fj := DDS.firstInputIndexGlobal (q := q) u j
  change fi.val = fj.val
  rcases lt_trichotomy fi.val fj.val with hlt | heq | hgt
  · exfalso
    let inputsJ : Fin (j.val + 1) → X := fun k =>
      u ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt j.isLt)⟩
    have hfj_le : fj.val ≤ j.val := by
      simpa [fj] using DDS.firstInputIndexGlobal_le (q := q) u j
    have hfi_in_j : fi.val < j.val + 1 := Nat.lt_succ_of_le (le_trans hlt.le hfj_le)
    have hneq := DDS.ne_of_lt_firstInputIndex (q := q) j inputsJ ⟨fi.val, hfi_in_j⟩ ?_
    · apply hneq
      have hfi_spec : u fi = u i := by
        simpa [fi] using DDS.firstInputIndexGlobal_spec (q := q) u i
      exact hfi_spec.trans hij
    · simpa [fj, DDS.firstInputIndexGlobal] using hlt
  · exact heq
  · exfalso
    let inputsI : Fin (i.val + 1) → X := fun k =>
      u ⟨k.val, Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt i.isLt)⟩
    have hfi_le : fi.val ≤ i.val := by
      simpa [fi] using DDS.firstInputIndexGlobal_le (q := q) u i
    have hfj_in_i : fj.val < i.val + 1 := Nat.lt_succ_of_le (le_trans hgt.le hfi_le)
    have hneq := DDS.ne_of_lt_firstInputIndex (q := q) i inputsI ⟨fj.val, hfj_in_i⟩ ?_
    · apply hneq
      have hfj_spec : u fj = u j := by
        simpa [fj] using DDS.firstInputIndexGlobal_spec (q := q) u j
      exact hfj_spec.trans hij.symm
    · simpa [fi, DDS.firstInputIndexGlobal] using hgt

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- The global first occurrence selected from a transcript's input history is a
fresh position in that transcript. -/
theorem Transcript.freshAt_firstInputIndexGlobal [DecidableEq X]
    (t : Transcript X Y q) (i : Fin q) :
    Transcript.FreshAt t
      (DDS.firstInputIndexGlobal (q := q) (Transcript.inputs t) i) := by
  intro k hk
  let u : Fin q → X := Transcript.inputs t
  let j := DDS.firstInputIndexGlobal (q := q) u i
  have hj_le : j.val ≤ i.val := by
    simpa [j, u] using DDS.firstInputIndexGlobal_le (q := q) u i
  let inputs : Fin (i.val + 1) → X := fun l =>
    u ⟨l.val, Nat.lt_of_lt_of_le l.isLt (Nat.succ_le_of_lt i.isLt)⟩
  have hk_in_i : k.val < i.val + 1 := Nat.lt_succ_of_le (le_trans hk.le hj_le)
  have hneq := DDS.ne_of_lt_firstInputIndex (q := q) i inputs ⟨k.val, hk_in_i⟩ ?_
  · intro hkj
    apply hneq
    have hji : u j = u i := DDS.firstInputIndexGlobal_spec (q := q) u i
    exact hkj.trans hji
  · simpa [j, u, DDS.firstInputIndexGlobal, inputs] using hk

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- If the current input is fresh in the prefix, the first occurrence is the
current position itself. -/
theorem DDS.firstInputIndex_eq_last_of_fresh [DecidableEq X]
    (i : Fin q) (inputs : Fin (i.val + 1) → X)
    (hfresh : ∀ j : Fin (i.val + 1), j.val < i.val →
      inputs j ≠ inputs ⟨i.val, Nat.lt_succ_self i.val⟩) :
    DDS.firstInputIndex (q := q) i inputs = ⟨i.val, Nat.lt_succ_self i.val⟩ := by
  apply Fin.ext
  have hle : (DDS.firstInputIndex (q := q) i inputs).val ≤ i.val :=
    Nat.le_of_lt_succ (DDS.firstInputIndex (q := q) i inputs).isLt
  have hnlt : ¬ (DDS.firstInputIndex (q := q) i inputs).val < i.val := by
    intro hlt
    exact (hfresh (DDS.firstInputIndex (q := q) i inputs) hlt)
      (DDS.firstInputIndex_spec (q := q) i inputs)
  exact le_antisymm hle (Nat.le_of_not_gt hnlt)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Deterministic DDS that replays a position-indexed output tape.

At query `i`, it returns the tape value at the first occurrence of the current
input in the input prefix.  Therefore fresh inputs consume their own position's
tape value, while repeated inputs replay the value assigned to their first
occurrence. -/
noncomputable def DDS.ofPositionTape [DecidableEq X] (ys : Fin q → Y) : DDS X Y q where
  respond := fun i inputs =>
    ys ⟨(DDS.firstInputIndex (q := q) i inputs).val,
      Nat.lt_of_le_of_lt
        (Nat.le_of_lt_succ (DDS.firstInputIndex (q := q) i inputs).isLt) i.isLt⟩

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- The output history obtained by replaying a position-indexed tape through an
adaptive environment. -/
noncomputable def DDE.outputHistoryOfPositionTape [DecidableEq X]
    (e : DDE X Y q) (ys : Fin q → Y) : Fin q → Y :=
  Transcript.outputs (interact (DDS.ofPositionTape (q := q) ys) e)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- On fixed inputs, a position tape returns the tape value at the global first
occurrence of the current input name. -/
theorem DDS.transcript_ofPositionTape_output_eq_firstInputIndexGlobal [DecidableEq X]
    (ys : Fin q → Y) (inputs : Fin q → X) (i : Fin q) :
    (DDS.transcript (DDS.ofPositionTape (q := q) ys) inputs i).2 =
      ys (DDS.firstInputIndexGlobal (q := q) inputs i) := by
  unfold DDS.transcript DDS.ofPositionTape DDS.firstInputIndexGlobal
  rfl

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- On an injective input sequence, the first global occurrence of a position is
that position itself. -/
theorem DDS.firstInputIndexGlobal_eq_self_of_injective [DecidableEq X]
    (inputs : Fin q → X) (hinj : Function.Injective inputs) (i : Fin q) :
    DDS.firstInputIndexGlobal (q := q) inputs i = i := by
  exact hinj (DDS.firstInputIndexGlobal_spec (q := q) inputs i)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- On injective fixed inputs, a position tape embeds its output vector as the
transcript with those fixed inputs. -/
theorem DDS.transcript_ofPositionTape_eq_of_injective_inputs [DecidableEq X]
    (ys : Fin q → Y) (inputs : Fin q → X) (hinj : Function.Injective inputs) :
    DDS.transcript (DDS.ofPositionTape (q := q) ys) inputs =
      Transcript.ofOutputs inputs ys := by
  funext i
  apply Prod.ext
  · rfl
  · rw [DDS.transcript_ofPositionTape_output_eq_firstInputIndexGlobal]
    exact congrArg ys
      (DDS.firstInputIndexGlobal_eq_self_of_injective (q := q) inputs hinj i)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- A position tape that agrees with a repeat-consistent transcript on fresh
positions reproduces that transcript on the transcript's fixed input sequence. -/
theorem DDS.ofPositionTape_transcript_eq_of_fresh_values [DecidableEq X]
    (t : Transcript X Y q) (ys : Fin q → Y)
    (hrep : Transcript.RepeatConsistent t)
    (hyfresh : ∀ i : Fin q, Transcript.FreshAt t i → ys i = (t i).2) :
    DDS.transcript (DDS.ofPositionTape (q := q) ys) (Transcript.inputs t) = t := by
  funext i
  apply Prod.ext
  · rfl
  · rw [DDS.transcript_ofPositionTape_output_eq_firstInputIndexGlobal]
    let j := DDS.firstInputIndexGlobal (q := q) (Transcript.inputs t) i
    have hjfresh : Transcript.FreshAt t j :=
      Transcript.freshAt_firstInputIndexGlobal (q := q) t i
    have hinput : (t j).1 = (t i).1 := by
      simpa [j, Transcript.inputs] using
        DDS.firstInputIndexGlobal_spec (q := q) (Transcript.inputs t) i
    rw [hyfresh j hjfresh]
    exact hrep j i hinput

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- A position tape that agrees with a repeat-consistent followed transcript on
fresh positions reproduces that transcript adaptively. -/
theorem interact_ofPositionTape_eq_of_fresh_values [DecidableEq X]
    (e : DDE X Y q) (t : Transcript X Y q) (ys : Fin q → Y)
    (hfollow : DDE.FollowsTranscript e t)
    (hrep : Transcript.RepeatConsistent t)
    (hyfresh : ∀ i : Fin q, Transcript.FreshAt t i → ys i = (t i).2) :
    interact (DDS.ofPositionTape (q := q) ys) e = t := by
  exact (DDS.interact_eq_transcript_iff_of_follows
    (DDS.ofPositionTape (q := q) ys) e t hfollow).2
    (DDS.ofPositionTape_transcript_eq_of_fresh_values (q := q) t ys hrep hyfresh)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- At every position, position-tape replay returns the tape value at the first
global occurrence of the current adaptive input name. -/
theorem interact_ofPositionTape_output_eq_firstInputIndexGlobal [DecidableEq X]
    (e : DDE X Y q) (ys : Fin q → Y) (i : Fin q) :
    (interact (DDS.ofPositionTape (q := q) ys) e i).2 =
      ys (DDS.firstInputIndexGlobal (q := q)
        (fun k => (interact (DDS.ofPositionTape (q := q) ys) e k).1) i) := by
  unfold interact DDS.ofPositionTape DDS.firstInputIndexGlobal
  rfl

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- At a fresh position, replaying a position tape consumes the tape entry at
that same position. -/
theorem interact_ofPositionTape_output_eq_of_fresh [DecidableEq X]
    (e : DDE X Y q) (ys : Fin q → Y) (i : Fin q)
    (hfresh : Transcript.FreshAt (interact (DDS.ofPositionTape (q := q) ys) e) i) :
    (interact (DDS.ofPositionTape (q := q) ys) e i).2 = ys i := by
  let inputs : Fin (i.val + 1) → X := fun j =>
    interactInput (DDS.ofPositionTape (q := q) ys) e
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩
  have hfresh_inputs : ∀ j : Fin (i.val + 1), j.val < i.val →
      inputs j ≠ inputs ⟨i.val, Nat.lt_succ_self i.val⟩ := by
    intro j hlt
    exact hfresh ⟨j.val, Nat.lt_trans hlt i.isLt⟩ hlt
  have hfirst := DDS.firstInputIndex_eq_last_of_fresh (q := q) i inputs hfresh_inputs
  simp only [interact, DDS.ofPositionTape]
  change ys ⟨(DDS.firstInputIndex (q := q) i inputs).val, _⟩ = ys i
  apply congrArg ys
  apply Fin.ext
  simpa using congrArg Fin.val hfirst

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Position-tape replay is repeat-consistent: repeated adaptive input names
receive the same replayed output. -/
theorem interact_ofPositionTape_repeatConsistent [DecidableEq X]
    (e : DDE X Y q) (ys : Fin q → Y) :
    Transcript.RepeatConsistent (interact (DDS.ofPositionTape (q := q) ys) e) := by
  intro i j hij
  rw [interact_ofPositionTape_output_eq_firstInputIndexGlobal (q := q) e ys i]
  rw [interact_ofPositionTape_output_eq_firstInputIndexGlobal (q := q) e ys j]
  exact congrArg ys (DDS.firstInputIndexGlobal_eq_of_eq (X := X) (q := q)
    (u := fun k => (interact (DDS.ofPositionTape (q := q) ys) e k).1) i j hij)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Replaying the visible output history of a position-tape interaction through
the same environment recovers the original interaction transcript. -/
theorem DDE.transcriptOfOutputs_outputHistoryOfPositionTape [DecidableEq X]
    (e : DDE X Y q) (ys : Fin q → Y) :
    DDE.transcriptOfOutputs e (DDE.outputHistoryOfPositionTape e ys) =
      interact (DDS.ofPositionTape (q := q) ys) e := by
  unfold DDE.outputHistoryOfPositionTape
  exact DDE.transcriptOfOutputs_outputs_eq_of_follows e
    (interact (DDS.ofPositionTape (q := q) ys) e)
    (DDE.followsTranscript_of_interact_eq (DDS.ofPositionTape (q := q) ys) e
      (interact (DDS.ofPositionTape (q := q) ys) e) rfl)

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Output histories produced by position-tape replay are repeat-consistent
when replayed through the same environment. -/
theorem DDE.repeatConsistent_transcriptOfOutputs_outputHistoryOfPositionTape
    [DecidableEq X] (e : DDE X Y q) (ys : Fin q → Y) :
    Transcript.RepeatConsistent
      (DDE.transcriptOfOutputs e (DDE.outputHistoryOfPositionTape e ys)) := by
  rw [DDE.transcriptOfOutputs_outputHistoryOfPositionTape (q := q) e ys]
  exact interact_ofPositionTape_repeatConsistent (q := q) e ys

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- If a tape agrees with a replayed output history on fresh positions of that
history's adaptive transcript, then replaying the tape produces that output
history. -/
theorem DDE.outputHistoryOfPositionTape_eq_of_fresh_values [DecidableEq X]
    (e : DDE X Y q) (zs ys : Fin q → Y)
    (hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e zs))
    (hyfresh : ∀ i : Fin q, Transcript.FreshAt (DDE.transcriptOfOutputs e zs) i →
      ys i = zs i) :
    DDE.outputHistoryOfPositionTape e ys = zs := by
  have hinteract := interact_ofPositionTape_eq_of_fresh_values (q := q) e
    (DDE.transcriptOfOutputs e zs) ys
    (DDE.followsTranscript_transcriptOfOutputs e zs) hrep ?_
  · unfold DDE.outputHistoryOfPositionTape
    rw [hinteract]
    exact DDE.outputs_transcriptOfOutputs e zs
  · intro i hi
    simpa [DDE.transcriptOfOutputs] using hyfresh i hi

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Any tape producing a target output history must agree with that history on
fresh positions of the target's adaptive transcript. -/
theorem DDE.fresh_values_of_outputHistoryOfPositionTape_eq [DecidableEq X]
    (e : DDE X Y q) (ys zs : Fin q → Y)
    (h : DDE.outputHistoryOfPositionTape e ys = zs) :
    ∀ i : Fin q, Transcript.FreshAt (DDE.transcriptOfOutputs e zs) i → ys i = zs i := by
  intro i hi
  have ht : interact (DDS.ofPositionTape (q := q) ys) e =
      DDE.transcriptOfOutputs e zs := by
    rw [← DDE.transcriptOfOutputs_outputHistoryOfPositionTape (q := q) e ys]
    rw [h]
  have hfresh : Transcript.FreshAt (interact (DDS.ofPositionTape (q := q) ys) e) i := by
    simpa [ht] using hi
  have hout := interact_ofPositionTape_output_eq_of_fresh (q := q) e ys i hfresh
  have hz : (interact (DDS.ofPositionTape (q := q) ys) e i).2 = zs i := by
    rw [ht]
    rfl
  exact hout.symm.trans hz

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- For a repeat-consistent target history, the position-tape fiber is exactly
the set of tapes agreeing with the target on fresh positions. -/
theorem DDE.outputHistoryOfPositionTape_eq_iff_fresh_values [DecidableEq X]
    (e : DDE X Y q) (zs ys : Fin q → Y)
    (hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e zs)) :
    DDE.outputHistoryOfPositionTape e ys = zs ↔
      ∀ i : Fin q, Transcript.FreshAt (DDE.transcriptOfOutputs e zs) i → ys i = zs i := by
  constructor
  · exact DDE.fresh_values_of_outputHistoryOfPositionTape_eq (q := q) e ys zs
  · intro hyfresh
    exact DDE.outputHistoryOfPositionTape_eq_of_fresh_values (q := q) e zs ys hrep hyfresh

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Tapes agreeing with a transcript on fresh positions are equivalent to
arbitrary assignments on the non-fresh positions. -/
def Transcript.tapeFreshFiberEquiv [DecidableEq X]
    (t : Transcript X Y q) (z : Fin q → Y) :
    {ys : Fin q → Y // ∀ i : Fin q, Transcript.FreshAt t i → ys i = z i} ≃
      ({i : Fin q // ¬ Transcript.FreshAt t i} → Y) where
  toFun ys := fun i => ys.1 i.1
  invFun g := ⟨fun i => if h : Transcript.FreshAt t i then z i else g ⟨i, h⟩, by
    intro i hi
    simp [hi]⟩
  left_inv ys := by
    apply Subtype.ext
    funext i
    by_cases hi : Transcript.FreshAt t i
    · simp [hi, ys.2 i hi]
    · simp [hi]
  right_inv g := by
    funext i
    simp [i.2]

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- The number of tapes agreeing with a transcript on fresh positions is
`|Y|` to the number of non-fresh positions. -/
theorem Transcript.card_tapeFreshFiber [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (t : Transcript X Y q) (z : Fin q → Y) :
    Fintype.card {ys : Fin q → Y // ∀ i : Fin q, Transcript.FreshAt t i → ys i = z i} =
      (Fintype.card Y) ^ (q - Fintype.card (Transcript.FreshPos t)) := by
  rw [Fintype.card_congr (Transcript.tapeFreshFiberEquiv (q := q) t z)]
  rw [Fintype.card_fun]
  rw [Fintype.card_subtype_compl (p := fun i : Fin q => Transcript.FreshAt t i)]
  rw [Fintype.card_fin]
  rfl

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Agreement with a transcript on fresh positions is equivalent to equality of
the reindexed fresh-position projection with the transcript's fresh outputs. -/
theorem Transcript.fresh_values_iff_project_eq [DecidableEq X]
    (t : Transcript X Y q) (y : Fin q → Y) :
    (∀ i : Fin q, Transcript.FreshAt t i → y i = (t i).2) ↔
      (fun k : Fin (Fintype.card (Transcript.FreshPos t)) =>
        y (((Fintype.equivFin (Transcript.FreshPos t)).symm k).1)) =
        Transcript.freshOutputsFin t := by
  constructor
  · intro h
    funext k
    exact h (((Fintype.equivFin (Transcript.FreshPos t)).symm k).1)
      (((Fintype.equivFin (Transcript.FreshPos t)).symm k).2)
  · intro h i hi
    let k := (Fintype.equivFin (Transcript.FreshPos t)) ⟨i, hi⟩
    have hk := congrFun h k
    simpa [k, Transcript.freshOutputsFin, Transcript.freshOutputs] using hk

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- For a repeat-consistent target history, the position-tape fiber has one
free tape coordinate for each non-fresh target-transcript position. -/
theorem DDE.outputHistoryOfPositionTape_fiber_card [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : DDE X Y q) (zs : Fin q → Y)
    (hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e zs)) :
    Fintype.card {ys : Fin q → Y // DDE.outputHistoryOfPositionTape e ys = zs} =
      (Fintype.card Y) ^
        (q - Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e zs))) := by
  rw [Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl (Fin q → Y))
    (p := fun ys => DDE.outputHistoryOfPositionTape e ys = zs)
    (q := fun ys => ∀ i : Fin q,
      Transcript.FreshAt (DDE.transcriptOfOutputs e zs) i → ys i = zs i)
    (by
      intro ys
      exact DDE.outputHistoryOfPositionTape_eq_iff_fresh_values (q := q) e zs ys hrep))]
  exact Transcript.card_tapeFreshFiber (q := q) (DDE.transcriptOfOutputs e zs) zs

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Uniform position tapes assign a repeat-consistent target history mass equal
to its replay-fiber cardinality divided by the full tape-space cardinality. -/
theorem DDE.positionTape_uniform_apply_of_repeatConsistent
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (e : DDE X Y q) (zs : Fin q → Y)
    (hrep : Transcript.RepeatConsistent (DDE.transcriptOfOutputs e zs)) :
    (Dist.fTransform (DDE.outputHistoryOfPositionTape e) (Dist.uniform (Fin q → Y))) zs =
      (((Fintype.card Y) ^
          (q - Fintype.card (Transcript.FreshPos (DDE.transcriptOfOutputs e zs))) : Nat) :
        ℝ) /
        (Fintype.card (Fin q → Y) : ℝ) := by
  rw [Dist.fTransform_uniform_apply]
  rw [show (Finset.univ.filter
      (fun ys : Fin q → Y => DDE.outputHistoryOfPositionTape e ys = zs)).card =
        Fintype.card {ys : Fin q → Y // DDE.outputHistoryOfPositionTape e ys = zs} from by
    rw [← Fintype.card_subtype
      (p := fun ys : Fin q → Y => DDE.outputHistoryOfPositionTape e ys = zs)]]
  rw [DDE.outputHistoryOfPositionTape_fiber_card (q := q) e zs hrep]

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Uniform position tapes assign no mass to histories whose replayed adaptive
transcript is repeat-inconsistent. -/
theorem DDE.positionTape_uniform_apply_eq_zero_of_not_repeatConsistent
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (e : DDE X Y q) (zs : Fin q → Y)
    (hnot : ¬ Transcript.RepeatConsistent (DDE.transcriptOfOutputs e zs)) :
    (Dist.fTransform (DDE.outputHistoryOfPositionTape e) (Dist.uniform (Fin q → Y))) zs = 0 := by
  rw [Dist.fTransform_uniform_apply]
  have hcard : (Finset.univ.filter
      (fun ys : Fin q → Y => DDE.outputHistoryOfPositionTape e ys = zs)).card = 0 := by
    rw [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    intro ys _ hys
    apply hnot
    rw [← hys]
    exact DDE.repeatConsistent_transcriptOfOutputs_outputHistoryOfPositionTape (q := q) e ys
  rw [hcard]
  simp

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- Any position-tape pushforward assigns no mass to histories whose replayed
adaptive transcript is repeat-inconsistent. -/
theorem DDE.positionTape_pushforward_apply_eq_zero_of_not_repeatConsistent
    [DecidableEq X] [Fintype (Fin q → Y)] [DecidableEq (Fin q → Y)]
    (D : Dist (Fin q → Y)) (e : DDE X Y q) (zs : Fin q → Y)
    (hnot : ¬ Transcript.RepeatConsistent (DDE.transcriptOfOutputs e zs)) :
    (Dist.fTransform (DDE.outputHistoryOfPositionTape e) D) zs = 0 := by
  rw [Dist.fTransform_apply_eq_sum]
  have hfilter : (Finset.univ.filter
      (fun ys : Fin q → Y => DDE.outputHistoryOfPositionTape e ys = zs)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro ys _ hys
    apply hnot
    rw [← hys]
    exact DDE.repeatConsistent_transcriptOfOutputs_outputHistoryOfPositionTape (q := q) e ys
  rw [hfilter]
  simp

/-- For a distribution over stateless oracles, adaptive output histories are the
pushforward of the sampled oracle distribution. -/
theorem PDS.stateless_adaptiveOutputDist_eq_oracle_pushforward
    {A : Type*} [Fintype A] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [DecidableEq (Fin q → Y)]
    (D : Dist A) (oracle : A → X → Y) (e : DDE X Y q) :
    (PDS.ofStatelessOracleDist (q := q) D oracle).adaptiveOutputDist e =
      Dist.fTransform (fun a : A => DDE.outputHistoryOfOracle e (oracle a)) D := by
  unfold PDS.adaptiveOutputDist PDS.ofStatelessOracleDist PDS.adaptiveTranscriptDist
    DDE.outputHistoryOfOracle
  rw [Dist.fTransform_comp]
  rw [Dist.fTransform_comp]
  rfl

/-- If an environment follows transcript `t`, then adaptive transcript mass at
`t` equals the non-adaptive transcript mass for the fixed input sequence
extracted from `t`. -/
theorem PDS.adaptiveTranscriptDist_apply_eq_transcriptDist_of_follows
    (S : PDS X Y q) (e : DDE X Y q) (t : Transcript X Y q)
    (hfollow : DDE.FollowsTranscript e t) :
    S.adaptiveTranscriptDist e t = S.transcriptDist (Transcript.inputs t) t := by
  classical
  rw [PDS.adaptiveTranscriptDist_apply_eq_sum]
  rw [PDS.transcriptDist_apply_eq_sum]
  have hfilter :
      (Finset.univ.filter (fun s : DDS X Y q => interact s e = t)) =
        (Finset.univ.filter
          (fun s : DDS X Y q => DDS.transcript s (Transcript.inputs t) = t)) := by
    ext s
    simp [DDS.interact_eq_transcript_iff_of_follows s e t hfollow]
  rw [hfilter]

/-- Adaptive statistical distance decomposes over the transcripts followed by
the adaptive environment.

For a followed transcript `t`, adaptive mass at `t` is just the non-adaptive
mass of `t` at the input sequence recorded by `t`.  For an unfollowed
transcript, both adaptive masses are zero.  This is the exact generic
decomposition that an input-symmetric XoP proof must bound. -/
theorem statDist_adaptiveTranscriptDist_eq_sum_following_transcriptDist
    (S T : PDS X Y q) (e : DDE X Y q) [DecidablePred (DDE.FollowsTranscript e)] :
    statDist (S.adaptiveTranscriptDist e) (T.adaptiveTranscriptDist e) =
      ∑ t ∈ (Finset.univ : Finset (Transcript X Y q)).filter (DDE.FollowsTranscript e),
        max (S.transcriptDist (Transcript.inputs t) t -
          T.transcriptDist (Transcript.inputs t) t) 0 := by
  classical
  -- the signed carrier indexes `statDist` by `(X - Y).support`, not `univ`;
  -- `statDist_eq_sum_univ` is the migrated unfolding lemma for `Fintype` carriers
  rw [statDist_eq_sum_univ]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hfollow : DDE.FollowsTranscript e t
  · rw [if_pos hfollow]
    rw [PDS.adaptiveTranscriptDist_apply_eq_transcriptDist_of_follows
      (S := S) (e := e) (t := t) hfollow]
    rw [PDS.adaptiveTranscriptDist_apply_eq_transcriptDist_of_follows
      (S := T) (e := e) (t := t) hfollow]
  · rw [if_neg hfollow]
    rw [PDS.adaptiveTranscriptDist_apply_eq_zero_of_not_follows
      (S := S) (e := e) (t := t) hfollow]
    rw [PDS.adaptiveTranscriptDist_apply_eq_zero_of_not_follows
      (S := T) (e := e) (t := t) hfollow]
    simp

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- For a stateless DDS, producing a repeat-consistent adaptive transcript is
equivalent to producing the transcript's fresh subtranscript nonadaptively. -/
theorem DDS.ofFunq_fresh_transcript_iff_interact
    [DecidableEq X]
    (f : X → Y) (e : DDE X Y q) (t : Transcript X Y q)
    (hfollow : DDE.FollowsTranscript e t) (hrep : Transcript.RepeatConsistent t) :
    interact (DDS.ofFunq (q := q) f) e = t ↔
      DDS.transcript (DDS.ofFunq (q := Fintype.card (Transcript.FreshPos t)) f)
        (Transcript.freshInputsFin t) =
        fun k => (Transcript.freshInputsFin t k, Transcript.freshOutputsFin t k) := by
  constructor
  · intro hint
    funext k
    have hk := congrFun hint (((Fintype.equivFin (Transcript.FreshPos t)).symm k).1)
    have hy : f ((t (((Fintype.equivFin (Transcript.FreshPos t)).symm k).1)).1) =
        (t (((Fintype.equivFin (Transcript.FreshPos t)).symm k).1)).2 := by
      rw [← hk]
      exact interact_ofFunq_output_eq (q := q) f e
        (((Fintype.equivFin (Transcript.FreshPos t)).symm k).1)
    simp [DDS.transcript, DDS.ofFunq, Transcript.freshInputsFin, Transcript.freshOutputsFin,
      Transcript.freshInputs, Transcript.freshOutputs, hy]
  · intro hfresh
    have hfull : DDS.transcript (DDS.ofFunq (q := q) f) (Transcript.inputs t) = t := by
      funext i
      rcases Transcript.exists_freshFin_same_pair_of_repeatConsistent t hrep i with
        ⟨k, hinput, houtput⟩
      have hk := congrFun hfresh k
      have hy : f (Transcript.freshInputsFin t k) = Transcript.freshOutputsFin t k := by
        simpa [DDS.transcript, DDS.ofFunq] using congrArg Prod.snd hk
      apply Prod.ext
      · rfl
      · simp [DDS.transcript, DDS.ofFunq, Transcript.inputs]
        rw [← hinput, hy, houtput]
    exact (DDS.interact_eq_transcript_iff_of_follows
      (DDS.ofFunq (q := q) f) e t hfollow).2 hfull

/-- A distribution over stateless oracles has the same mass on a followed,
repeat-consistent adaptive transcript as on that transcript's fresh
subtranscript under nonadaptive evaluation. -/
theorem PDS.stateless_adaptiveTranscriptDist_eq_fresh_transcriptDist
    {A : Type*} [Fintype A] [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (D : Dist A) (oracle : A → X → Y)
    (e : DDE X Y q) (t : Transcript X Y q)
    (hfollow : DDE.FollowsTranscript e t) (hrep : Transcript.RepeatConsistent t) :
    (PDS.ofStatelessOracleDist (q := q) D oracle).adaptiveTranscriptDist e t =
      (PDS.ofStatelessOracleDist (q := Fintype.card (Transcript.FreshPos t)) D oracle).transcriptDist
        (Transcript.freshInputsFin t)
        (fun k => (Transcript.freshInputsFin t k, Transcript.freshOutputsFin t k)) := by
  classical
  unfold PDS.adaptiveTranscriptDist PDS.transcriptDist PDS.ofStatelessOracleDist
  rw [Dist.fTransform_comp]
  rw [Dist.fTransform_comp]
  rw [Dist.fTransform_apply_eq_sum]
  rw [Dist.fTransform_apply_eq_sum]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact DDS.ofFunq_fresh_transcript_iff_interact (f := oracle a) (e := e) (t := t)
    hfollow hrep

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- A stateless adaptive output history is determined by the oracle values on
the fresh input names that occur along the interaction.

This is the deterministic core of fresh-tape replay: if `g` agrees with the
fresh input-output pairs generated by `f`, then replaying the same environment
against `g` gives the same visible output history. -/
theorem DDE.outputHistoryOfOracle_eq_of_fresh_values [DecidableEq X]
    (e : DDE X Y q) (f g : X → Y)
    (hfresh :
      ∀ k : Fin (Fintype.card (Transcript.FreshPos
          (interact (DDS.ofFunq (q := q) f) e))),
        g (Transcript.freshInputsFin (interact (DDS.ofFunq (q := q) f) e) k) =
          Transcript.freshOutputsFin (interact (DDS.ofFunq (q := q) f) e) k) :
    DDE.outputHistoryOfOracle e g = DDE.outputHistoryOfOracle e f := by
  let t : Transcript X Y q := interact (DDS.ofFunq (q := q) f) e
  have hfollow : DDE.FollowsTranscript e t := DDE.followsTranscript_of_interact_eq _ _ _ rfl
  have hrep : Transcript.RepeatConsistent t := by
    dsimp [t]
    exact interact_ofFunq_repeatConsistent (q := q) f e
  have hfreshTranscript :
      DDS.transcript (DDS.ofFunq (q := Fintype.card (Transcript.FreshPos t)) g)
          (Transcript.freshInputsFin t) =
        fun k => (Transcript.freshInputsFin t k, Transcript.freshOutputsFin t k) := by
    funext k
    apply Prod.ext
    · rfl
    · exact hfresh k
  have hinteract : interact (DDS.ofFunq (q := q) g) e = t := by
    exact (DDS.ofFunq_fresh_transcript_iff_interact
      (q := q) (f := g) (e := e) (t := t) hfollow hrep).2 hfreshTranscript
  simp [DDE.outputHistoryOfOracle, hinteract, t]

/-- Lanzenberger-Maurer Lemma 5: adaptive equivalence is equivalent to
non-adaptive equivalence.

The forward direction is immediate because fixed input sequences embed as
`DDE.nonadaptive` environments.  The reverse direction is the real content of
Lemma 5: if an adaptive environment changes some transcript probability, then
the fixed input sequence appearing in that transcript also changes that
transcript probability. -/
theorem PDS.equivAdaptive_iff_nonadaptive (S T : PDS X Y q) :
    PDS.equivAdaptive S T ↔ PDS.equivNonadaptive S T := by
  constructor
  · intro h inputs
    simpa [PDS.equivNonadaptive, PDS.adaptiveTranscriptDist_nonadaptive] using
      h (DDE.nonadaptive inputs)
  · intro h e
    ext t
    by_cases hfollow : DDE.FollowsTranscript e t
    · rw [PDS.adaptiveTranscriptDist_apply_eq_transcriptDist_of_follows
        (S := S) (e := e) (t := t) hfollow]
      rw [PDS.adaptiveTranscriptDist_apply_eq_transcriptDist_of_follows
        (S := T) (e := e) (t := t) hfollow]
      simpa using
        (congrArg (fun D : Dist (Transcript X Y q) => D t) (h (Transcript.inputs t)))
    · rw [PDS.adaptiveTranscriptDist_apply_eq_zero_of_not_follows
        (S := S) (e := e) (t := t) hfollow]
      rw [PDS.adaptiveTranscriptDist_apply_eq_zero_of_not_follows
        (S := T) (e := e) (t := t) hfollow]

/-- LM20 representative-lift helper.

To prove that two PDS representatives are adaptively equivalent, it suffices to
show equality of their non-adaptive transcript distributions on every fixed
input sequence.  This is the named bridge used by transcript-level
representative constructions. -/
theorem PDS.equivAdaptive_of_transcriptDist_eq (S T : PDS X Y q)
    (h : ∀ inputs : Fin q → X, S.transcriptDist inputs = T.transcriptDist inputs) :
    PDS.equivAdaptive S T :=
  (PDS.equivAdaptive_iff_nonadaptive S T).2 h

/-- PDS obtained by first sampling a position-indexed output tape, then replaying
that tape as a deterministic discrete system. -/
noncomputable def PDS.ofPositionTapeDist [DecidableEq X] [DecidableEq (DDS X Y q)]
    (D : Dist (Fin q → Y)) : PDS X Y q where
  dist := Dist.fTransform (fun ys => DDS.ofPositionTape (q := q) (X := X) ys) D

/-- On injective fixed inputs, sampling a position-tape DDS realizes exactly the
pushforward of the sampled output vector into a fixed-input transcript. -/
theorem PDS.transcriptDist_ofPositionTapeDist_eq
    [DecidableEq X] [DecidableEq (DDS X Y q)]
    (D : Dist (Fin q → Y)) (inputs : Fin q → X) (hinj : Function.Injective inputs) :
    (PDS.ofPositionTapeDist (q := q) (X := X) D).transcriptDist inputs =
      Dist.fTransform (Transcript.ofOutputs inputs) D := by
  unfold PDS.ofPositionTapeDist PDS.transcriptDist
  rw [Dist.fTransform_comp]
  congr 1
  funext ys
  exact DDS.transcript_ofPositionTape_eq_of_injective_inputs (q := q) ys inputs hinj

omit [Fintype (DDS X Y q)] [Fintype (Transcript X Y q)]
    [DecidableEq (Transcript X Y q)] in
/-- If the input alphabet admits a fixed injective `q`-query sequence, then the
position-tape embedding into DDS is injective: every tape value can be observed
by replaying that fixed fresh-input sequence. -/
theorem DDS.ofPositionTape_injective_of_injective_inputs
    [DecidableEq X] (inputs : Fin q → X) (hinj : Function.Injective inputs) :
    Function.Injective (fun ys : Fin q → Y =>
      DDS.ofPositionTape (q := q) (X := X) ys) := by
  intro ys zs h
  funext i
  have ht := congrArg (fun s : DDS X Y q => DDS.transcript s inputs) h
  change DDS.transcript (DDS.ofPositionTape (q := q) (X := X) ys) inputs =
    DDS.transcript (DDS.ofPositionTape (q := q) (X := X) zs) inputs at ht
  rw [DDS.transcript_ofPositionTape_eq_of_injective_inputs
    (q := q) ys inputs hinj] at ht
  rw [DDS.transcript_ofPositionTape_eq_of_injective_inputs
    (q := q) zs inputs hinj] at ht
  have hi := congrFun ht i
  exact congrArg Prod.snd hi

/-- Lift a coupling of position-indexed output tapes to a coupling of the
corresponding position-tape PDS distributions over deterministic systems. -/
def PDS.positionTapeDistCoupling
    [Fintype Y] [DecidableEq Y] [DecidableEq X] [DecidableEq (DDS X Y q)]
    [Nonempty (DDS X Y q)]
    {D E : Dist (Fin q → Y)} (C : DistCoupling D E) :
    DistCoupling
      (PDS.ofPositionTapeDist (q := q) (X := X) D).dist
      (PDS.ofPositionTapeDist (q := q) (X := X) E).dist :=
  C.fTransform (fun ys : Fin q → Y => DDS.ofPositionTape (q := q) (X := X) ys)

omit [Fintype (Transcript X Y q)] [DecidableEq (Transcript X Y q)] in
/-- Under an injective fixed input sequence, the position-tape PDS coupling has
exactly the same failure probability as the original output-tape coupling. -/
theorem PDS.positionTapeDistCoupling_prDisagree_of_injective_inputs
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [DecidableEq X] [DecidableEq (DDS X Y q)]
    [Nonempty (DDS X Y q)]
    {D E : Dist (Fin q → Y)} (C : DistCoupling D E)
    (inputs : Fin q → X) (hinj : Function.Injective inputs) :
    (PDS.positionTapeDistCoupling (q := q) (X := X) C).prDisagree =
      C.prDisagree := by
  exact DistCoupling.prDisagree_fTransform_of_injective C
    (fun ys : Fin q → Y => DDS.ofPositionTape (q := q) (X := X) ys)
    (DDS.ofPositionTape_injective_of_injective_inputs (q := q) inputs hinj)

/-- The adaptive output-history law of a position-tape PDS is the pushforward of
the sampled tape law through the environment's position-tape replay map. -/
theorem PDS.adaptiveOutputDist_ofPositionTapeDist_eq
    [DecidableEq X] [DecidableEq (DDS X Y q)] [DecidableEq (Fin q → Y)]
    (D : Dist (Fin q → Y)) (e : DDE X Y q) :
    (PDS.ofPositionTapeDist (q := q) (X := X) D).adaptiveOutputDist e =
      Dist.fTransform (DDE.outputHistoryOfPositionTape e) D := by
  unfold PDS.adaptiveOutputDist PDS.ofPositionTapeDist PDS.adaptiveTranscriptDist
  rw [Dist.fTransform_comp]
  rw [Dist.fTransform_comp]
  congr 1

end RandomSystems
