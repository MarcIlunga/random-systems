/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.DDS
import RandomSystems.Legacy.DDE

/-!
# Transcripts

Lean 4 formalization of Definition 7 from Lanzenberger-Maurer (TCC 2020).

Moved into the `Legacy` tree on 2026-07-28: the bounded `Fin q`-transcript
model is consumed only by `Legacy.PDS` and the legacy bridges; the live tree
uses `DependentTranscript`/`ExtendedTranscript`.  Declaration namespace
unchanged (`RandomSystems`).

## Main Definitions

* `Transcript` — type alias for `Fin q → X × Y`
* `interact` — the adaptive transcript of a DDS interacting with a DDE

## Design Notes

The transcript records `(xᵢ, yᵢ)` for each query `i`. In the adaptive
case, the environment chooses `xᵢ₊₁` based on previous outputs, and
the system responds based on all previous inputs.

For non-adaptive environments, `interact s (DDE.nonadaptive inputs)`
coincides with `DDS.transcript s inputs`.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

/-- A transcript of `q` queries: a sequence of input-output pairs. -/
abbrev Transcript (X Y : Type*) (q : ℕ) := Fin q → X × Y

/-- A transcript records the fixed query vector `xs` if its input components are
exactly `xs`. -/
def transcriptInputsMatch {X Y : Type*} {q : ℕ}
    (xs : Fin q → X) (t : Transcript X Y q) : Prop :=
  ∀ i, (t i).1 = xs i

/-- The output components recorded by a transcript. -/
def transcriptOutputs {X Y : Type*} {q : ℕ}
    (t : Transcript X Y q) : Fin q → Y :=
  fun i => (t i).2

namespace Transcript

/-- The fixed input sequence appearing in a transcript. -/
def inputs {X Y : Type*} {q : ℕ} (t : Transcript X Y q) : Fin q → X :=
  fun i => (t i).1

/-- The output sequence appearing in a transcript. -/
def outputs {X Y : Type*} {q : ℕ} (t : Transcript X Y q) : Fin q → Y :=
  fun i => (t i).2

/-- Embed an output vector into a transcript with fixed input components. -/
def ofOutputs {X Y : Type*} {q : ℕ}
    (inputs : Fin q → X) (ys : Fin q → Y) : Transcript X Y q :=
  fun i => (inputs i, ys i)

/-- The output prefix of a transcript visible just before query `i`. -/
def outputPrefix {X Y : Type*} {q : ℕ} (t : Transcript X Y q) (i : Fin q) : Fin i.val → Y :=
  fun j => (t ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).2

/-- A transcript is repeat-consistent if repeated input names always carry the
same output.  Stateless random-function systems can only produce
repeat-consistent transcripts. -/
def RepeatConsistent {X Y : Type*} {q : ℕ} (t : Transcript X Y q) : Prop :=
  ∀ i j : Fin q, (t i).1 = (t j).1 → (t i).2 = (t j).2

/-- A position is fresh if its input name has not appeared at an earlier
position in the transcript. -/
def FreshAt {X Y : Type*} {q : ℕ} (t : Transcript X Y q) (i : Fin q) : Prop :=
  ∀ j : Fin q, j.val < i.val → (t j).1 ≠ (t i).1

/-- The subtype of fresh positions in a transcript. -/
def FreshPos {X Y : Type*} {q : ℕ} (t : Transcript X Y q) :=
  { i : Fin q // FreshAt t i }

instance freshAtDecidable {X Y : Type*} {q : ℕ} [DecidableEq X]
    (t : Transcript X Y q) (i : Fin q) : Decidable (FreshAt t i) := by
  unfold FreshAt
  infer_instance

instance freshPosFintype {X Y : Type*} {q : ℕ} [DecidableEq X]
    (t : Transcript X Y q) : Fintype (FreshPos t) := by
  unfold FreshPos
  infer_instance

/-- The input tuple formed by restricting a transcript to its fresh positions. -/
def freshInputs {X Y : Type*} {q : ℕ} (t : Transcript X Y q) : FreshPos t → X :=
  fun i => (t i.1).1

/-- The output tuple formed by restricting a transcript to its fresh positions. -/
def freshOutputs {X Y : Type*} {q : ℕ} (t : Transcript X Y q) : FreshPos t → Y :=
  fun i => (t i.1).2

/-- The fresh input tuple reindexed by `Fin |Fresh(t)|`. -/
noncomputable def freshInputsFin {X Y : Type*} {q : ℕ} [DecidableEq X]
    (t : Transcript X Y q) : Fin (Fintype.card (FreshPos t)) → X :=
  fun i => freshInputs t ((Fintype.equivFin (FreshPos t)).symm i)

/-- The fresh output tuple reindexed by `Fin |Fresh(t)|`. -/
noncomputable def freshOutputsFin {X Y : Type*} {q : ℕ} [DecidableEq X]
    (t : Transcript X Y q) : Fin (Fintype.card (FreshPos t)) → Y :=
  fun i => freshOutputs t ((Fintype.equivFin (FreshPos t)).symm i)

/-- Fresh positions have distinct input names. -/
theorem freshInputs_injective {X Y : Type*} {q : ℕ} (t : Transcript X Y q) :
    Function.Injective (freshInputs t) := by
  intro i j h
  apply Subtype.ext
  rcases lt_trichotomy i.1.val j.1.val with hlt | heq | hgt
  · have hne := j.2 i.1 hlt
    exact False.elim (hne h)
  · exact Fin.ext heq
  · have hne := i.2 j.1 hgt
    exact False.elim (hne h.symm)

/-- The `Fin |Fresh(t)|` fresh input tuple is injective. -/
theorem freshInputsFin_injective {X Y : Type*} {q : ℕ} [DecidableEq X]
    (t : Transcript X Y q) :
    Function.Injective (freshInputsFin t) := by
  intro i j h
  apply (Fintype.equivFin (FreshPos t)).symm.injective
  exact freshInputs_injective t h

/-- Every transcript position has an earlier-or-equal fresh representative with
the same input name. -/
theorem exists_freshPos_same_input {X Y : Type*} {q : ℕ}
    (t : Transcript X Y q) (i : Fin q) :
    ∃ j : FreshPos t, (t j.1).1 = (t i).1 ∧ j.1.val ≤ i.val := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ i : Fin q, i.val = n → ∃ j : FreshPos t, (t j.1).1 = (t i).1 ∧ j.1.val ≤ i.val
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn n (motive := P) (fun n ih => by
      intro i hi
      by_cases hfresh : FreshAt t i
      · exact ⟨⟨i, hfresh⟩, rfl, le_rfl⟩
      · unfold FreshAt at hfresh
        push Not at hfresh
        rcases hfresh with ⟨j, hlt, heq⟩
        rcases ih j.val (by simpa [hi] using hlt) j rfl with ⟨k, hkinput, hkle⟩
        refine ⟨k, ?_, ?_⟩
        · exact hkinput.trans heq
        · exact le_trans hkle (Nat.le_of_lt hlt))
  exact hP i.val i rfl

/-- In a repeat-consistent transcript, every position has an earlier-or-equal
fresh representative with the same input-output pair. -/
theorem exists_freshPos_same_pair_of_repeatConsistent {X Y : Type*} {q : ℕ}
    (t : Transcript X Y q) (hrep : RepeatConsistent t) (i : Fin q) :
    ∃ j : FreshPos t, (t j.1).1 = (t i).1 ∧ (t j.1).2 = (t i).2 ∧ j.1.val ≤ i.val := by
  rcases exists_freshPos_same_input t i with ⟨j, hinput, hle⟩
  exact ⟨j, hinput, hrep j.1 i hinput, hle⟩

/-- In a repeat-consistent transcript, every position is represented in the
`Fin |Fresh(t)|` fresh tuple by the same input-output pair. -/
theorem exists_freshFin_same_pair_of_repeatConsistent {X Y : Type*} {q : ℕ}
    [DecidableEq X] (t : Transcript X Y q) (hrep : RepeatConsistent t) (i : Fin q) :
    ∃ k : Fin (Fintype.card (FreshPos t)),
      freshInputsFin t k = (t i).1 ∧ freshOutputsFin t k = (t i).2 := by
  rcases exists_freshPos_same_pair_of_repeatConsistent t hrep i with
    ⟨j, hinput, houtput, _⟩
  refine ⟨(Fintype.equivFin (FreshPos t)) j, ?_, ?_⟩
  · simp [freshInputsFin, freshInputs, hinput]
  · simp [freshOutputsFin, freshOutputs, houtput]

/-- A transcript has at most `q` fresh positions. -/
theorem freshPos_card_le_query {X Y : Type*} {q : ℕ} [DecidableEq X]
    (t : Transcript X Y q) :
    Fintype.card (FreshPos t) ≤ q := by
  simpa [Fintype.card_fin] using
    Fintype.card_le_of_injective (fun i : FreshPos t => i.1)
      (fun _ _ h => Subtype.ext h)

/-- The fresh input tuple has length at most the input-domain cardinality. -/
theorem freshPos_card_le_input {X Y : Type*} {q : ℕ} [Fintype X] [DecidableEq X]
    (t : Transcript X Y q) :
    Fintype.card (FreshPos t) ≤ Fintype.card X :=
  Fintype.card_le_of_injective (freshInputs t) (freshInputs_injective t)

/-- A transcript is compatible with an adaptive environment if its recorded
query at each step is exactly the query the environment chooses after seeing
the previous recorded outputs. -/
def compatibleWithEnv {X Y : Type*} {q : ℕ}
    (e : DDE X Y q) (t : Transcript X Y q) : Prop :=
  ∀ i : Fin q,
    (t i).1 = e.choose i (fun j => (t ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩).2)

end Transcript

/-- Recursively build the input sequence from a DDS-DDE interaction.

  input(i) = e.choose i (y₀, ..., y_{i-1})

where each y_j = s.respond j (input(0), ..., input(j)). This uses
well-founded recursion on the query index. -/
def interactInput {X Y : Type*} {q : ℕ}
    (s : DDS X Y q) (e : DDE X Y q) (i : Fin q) : X :=
  e.choose i (fun j =>
    have hj : j.val < q := Nat.lt_trans j.isLt i.isLt
    s.respond ⟨j.val, hj⟩ (fun k =>
      have hk : k.val < q := by omega
      interactInput s e ⟨k.val, hk⟩))
termination_by i.val
decreasing_by
  show k.val < i.val
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le k.isLt (Nat.le_of_eq rfl)) j.isLt

/-- Compute the adaptive transcript of a DDS interacting with a DDE.

Paper Definition 7: The transcript `tr(s, e)` is defined by:
  x₁ := e(ε),  y₁ := s(x₁)
  xᵢ := e(y₁,...,yᵢ₋₁),  yᵢ := s(x₁,...,xᵢ) -/
def interact {X Y : Type*} {q : ℕ} (s : DDS X Y q) (e : DDE X Y q) :
    Transcript X Y q :=
  fun i =>
    let x := interactInput s e i
    let y := s.respond i (fun j =>
      interactInput s e ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩)
    (x, y)

/-- `interactInput` with a non-adaptive environment just returns the fixed input. -/
theorem interactInput_nonadaptive {X Y : Type*} {q : ℕ}
    (s : DDS X Y q) (inputs : Fin q → X) (i : Fin q) :
    interactInput s (DDE.nonadaptive inputs) i = inputs i := by
  unfold interactInput; simp [DDE.nonadaptive]

/-- For non-adaptive environments, the adaptive transcript equals the
simple (non-adaptive) transcript. -/
theorem interact_nonadaptive {X Y : Type*} {q : ℕ}
    (s : DDS X Y q) (inputs : Fin q → X) :
    interact s (DDE.nonadaptive inputs) = DDS.transcript s inputs := by
  funext i
  simp only [interact, DDS.transcript]
  ext
  · exact interactInput_nonadaptive s inputs i
  · simp only
    congr 1
    funext j
    exact interactInput_nonadaptive s inputs ⟨j.val, _⟩

/-! ### Deterministic adaptive transcript replay bridge

UPSTREAM-CANDIDATE: these are generic deterministic transcript facts used by
the H-technique birthday engine and the old `RandomSystems.Equiv` adaptive /
non-adaptive bridge. They belong with `Transcript`/`interact`, not in an
application proof file.
-/

/-- An adaptive environment follows a concrete transcript when, along the
transcript's output path, it asks exactly the transcript's next input. -/
def DDE.FollowsTranscript {X Y : Type*} {q : ℕ} (e : DDE X Y q)
    (t : Transcript X Y q) : Prop :=
  ∀ i : Fin q, e.choose i (Transcript.outputPrefix t i) = (t i).1

/-- The transcript obtained by feeding a fixed output history to an adaptive
environment.  This is the deterministic postprocessing map from output
histories to followed transcripts. -/
def DDE.transcriptOfOutputs {X Y : Type*} {q : ℕ}
    (e : DDE X Y q) (ys : Fin q → Y) : Transcript X Y q :=
  fun i => (e.choose i (fun j => ys ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩), ys i)

/-- The canonical transcript for an output history is followed by the
environment that generated it. -/
theorem DDE.followsTranscript_transcriptOfOutputs
    {X Y : Type*} {q : ℕ} (e : DDE X Y q) (ys : Fin q → Y) :
    DDE.FollowsTranscript e (DDE.transcriptOfOutputs e ys) := by
  intro i
  have hprefix :
      Transcript.outputPrefix (DDE.transcriptOfOutputs e ys) i =
        fun j => ys ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩ := by
    funext j
    rfl
  simp [DDE.transcriptOfOutputs, hprefix]

/-- The canonical transcript has the output history it was built from. -/
theorem DDE.outputs_transcriptOfOutputs {X Y : Type*} {q : ℕ}
    (e : DDE X Y q) (ys : Fin q → Y) :
    Transcript.outputs (DDE.transcriptOfOutputs e ys) = ys := by
  funext i
  rfl

/-- Replaying output histories through a fixed environment is injective. -/
theorem DDE.transcriptOfOutputs_injective {X Y : Type*} {q : ℕ}
    (e : DDE X Y q) :
    Function.Injective (DDE.transcriptOfOutputs e) := by
  intro ys zs h
  have hout := congrArg Transcript.outputs h
  simpa [DDE.outputs_transcriptOfOutputs] using hout

/-- Every followed transcript is recovered by replaying its output history
through the same environment. -/
theorem DDE.transcriptOfOutputs_outputs_eq_of_follows
    {X Y : Type*} {q : ℕ} (e : DDE X Y q) (t : Transcript X Y q)
    (hfollow : DDE.FollowsTranscript e t) :
    DDE.transcriptOfOutputs e (Transcript.outputs t) = t := by
  funext i
  apply Prod.ext
  · have hprefix :
        (fun j => Transcript.outputs t ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩) =
          Transcript.outputPrefix t i := by
      funext j
      rfl
    simp [DDE.transcriptOfOutputs, hprefix, hfollow i]
  · rfl

/-- For a fixed adaptive environment, the output sequence determines any
followed transcript. -/
theorem DDE.followsTranscript_eq_of_outputs_eq
    {X Y : Type*} {q : ℕ} (e : DDE X Y q) (t u : Transcript X Y q)
    (ht : DDE.FollowsTranscript e t) (hu : DDE.FollowsTranscript e u)
    (hout : Transcript.outputs t = Transcript.outputs u) :
    t = u := by
  funext i
  apply Prod.ext
  · have hprefix : Transcript.outputPrefix t i = Transcript.outputPrefix u i := by
      funext j
      exact congrFun hout ⟨j.val, Nat.lt_trans j.isLt i.isLt⟩
    rw [← ht i, ← hu i, hprefix]
  · exact congrFun hout i

/-- On the subtype of transcripts followed by a fixed environment, the output
sequence map is injective. -/
theorem DDE.followsTranscript_outputs_injective {X Y : Type*} {q : ℕ}
    (e : DDE X Y q) :
    Function.Injective
      (fun t : {t : Transcript X Y q // DDE.FollowsTranscript e t} =>
        Transcript.outputs t.1) := by
  intro t u h
  apply Subtype.ext
  exact DDE.followsTranscript_eq_of_outputs_eq e t.1 u.1 t.2 u.2 h

/-- If an interaction produces transcript `t`, then the environment necessarily
follows the input path recorded by `t`. -/
theorem DDE.followsTranscript_of_interact_eq
    {X Y : Type*} {q : ℕ} (s : DDS X Y q) (e : DDE X Y q)
    (t : Transcript X Y q) (h : interact s e = t) :
    DDE.FollowsTranscript e t := by
  intro i
  unfold Transcript.outputPrefix
  have hi : interact s e i = t i := congrFun h i
  have hx : interactInput s e i = (t i).1 := by
    simpa [interact] using congrArg Prod.fst hi
  rw [← hx]
  unfold interactInput
  congr 1
  funext j
  have hjq : j.val < q := Nat.lt_trans j.isLt i.isLt
  have hj : interact s e ⟨j.val, hjq⟩ = t ⟨j.val, hjq⟩ :=
    congrFun h ⟨j.val, hjq⟩
  simpa [interact] using (congrArg Prod.snd hj).symm

/-- If the non-adaptive transcript with the input sequence extracted from `t`
equals `t`, and the adaptive environment follows `t`, then the recursive
adaptive input at every query is exactly the input recorded by `t`. -/
theorem interactInput_eq_of_transcript_eq_of_follows
    {X Y : Type*} {q : ℕ} (s : DDS X Y q) (e : DDE X Y q)
    (t : Transcript X Y q)
    (hfollow : DDE.FollowsTranscript e t)
    (htrans : DDS.transcript s (Transcript.inputs t) = t)
    (i : Fin q) :
    interactInput s e i = (t i).1 := by
  let P : Nat → Prop := fun n =>
    ∀ i : Fin q, i.val = n → interactInput s e i = (t i).1
  have hP : ∀ n, P n := by
    intro n
    exact Nat.strongRecOn n (motive := P) (fun n ih => by
        intro i hi
        rw [← hfollow i]
        unfold interactInput
        congr 1
        funext j
        have hjq : j.val < q := Nat.lt_trans j.isLt i.isLt
        have hprev := congrFun htrans ⟨j.val, hjq⟩
        have hsecond :
            (DDS.transcript s (Transcript.inputs t) ⟨j.val, hjq⟩).2 =
              (t ⟨j.val, hjq⟩).2 :=
          congrArg Prod.snd hprev
        have hinputs :
            (fun k : Fin (j.val + 1) =>
                interactInput s e
                  ⟨k.val,
                    Nat.lt_trans
                      (Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt j.isLt))
                      i.isLt⟩) =
              fun k : Fin (j.val + 1) =>
                (t ⟨k.val,
                    Nat.lt_trans
                      (Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt j.isLt))
                      i.isLt⟩).1 := by
          funext k
          have hk_lt_i : k.val < i.val :=
            Nat.lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt j.isLt)
          have hkq : k.val < q := Nat.lt_trans hk_lt_i i.isLt
          exact ih k.val (by simpa [hi] using hk_lt_i) ⟨k.val, hkq⟩ rfl
        simpa [DDS.transcript, Transcript.inputs, hinputs] using hsecond)
  exact hP i.val i rfl

/-- If an adaptive environment follows transcript `t`, then the fiber of DDSs
that produce `t` adaptively is the same as the fiber of DDSs that produce `t`
against the fixed input sequence extracted from `t`. -/
theorem DDS.interact_eq_transcript_iff_of_follows
    {X Y : Type*} {q : ℕ} (s : DDS X Y q) (e : DDE X Y q)
    (t : Transcript X Y q) (hfollow : DDE.FollowsTranscript e t) :
    interact s e = t ↔ DDS.transcript s (Transcript.inputs t) = t := by
  constructor
  · intro h
    ext i <;> simp [DDS.transcript, Transcript.inputs]
    have hi : interact s e i = t i := congrFun h i
    have hsecond :
        (interact s e i).2 = (t i).2 := congrArg Prod.snd hi
    have hinputs :
        (fun j : Fin (i.val + 1) =>
            interactInput s e
              ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩) =
          fun j : Fin (i.val + 1) =>
            (t ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩).1 := by
      funext j
      have hj :
          interact s e
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩ =
          t ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩ :=
        congrFun h ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩
      simpa [interact] using congrArg Prod.fst hj
    simpa [interact, hinputs] using hsecond
  · intro htrans
    ext i <;> simp [interact]
    · exact interactInput_eq_of_transcript_eq_of_follows s e t hfollow htrans i
    · have hinputs :
          (fun j : Fin (i.val + 1) =>
              interactInput s e
                ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩) =
            fun j : Fin (i.val + 1) =>
              (t ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩).1 := by
        funext j
        exact interactInput_eq_of_transcript_eq_of_follows
          s e t hfollow htrans
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩
      have hi : DDS.transcript s (Transcript.inputs t) i = t i :=
        congrFun htrans i
      have hsecond :
          (DDS.transcript s (Transcript.inputs t) i).2 = (t i).2 :=
        congrArg Prod.snd hi
      simpa [DDS.transcript, Transcript.inputs, hinputs] using hsecond

/-! ### Stateless DDS (`DDS.ofFunq`) and transcript compatibility -/

/-- If a stateless function oracle has the fixed-query transcript recorded by
`t`, and `t` is compatible with the adaptive environment, then the adaptive
interaction follows exactly the query path recorded in `t`. -/
theorem interactInput_ofFunq_eq_of_transcript
    {X Y : Type*} {q : ℕ} (f : X → Y) (e : DDE X Y q)
    (t : Transcript X Y q)
    (hcompat : Transcript.compatibleWithEnv e t)
    (hfixed : DDS.transcript (DDS.ofFunq (q := q) f) (fun i => (t i).1) = t) :
    ∀ i : Fin q, interactInput (DDS.ofFunq (q := q) f) e i = (t i).1 := by
  classical
  intro i
  let P : ℕ → Prop := fun n =>
    ∀ i : Fin q, i.val = n →
      interactInput (DDS.ofFunq (q := q) f) e i = (t i).1
  have hstep : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n ih i hi
    cases hi
    unfold interactInput
    rw [hcompat i]
    congr 1
    funext j
    have hjq : j.val < q := Nat.lt_trans j.isLt i.isLt
    have hx :
        interactInput (DDS.ofFunq (q := q) f) e ⟨j.val, hjq⟩ =
          (t ⟨j.val, hjq⟩).1 :=
      (ih j.val j.isLt) ⟨j.val, hjq⟩ rfl
    have hout : f ((t ⟨j.val, hjq⟩).1) = (t ⟨j.val, hjq⟩).2 := by
      have hpoint := congr_fun hfixed ⟨j.val, hjq⟩
      simpa [DDS.transcript, DDS.ofFunq] using congrArg Prod.snd hpoint
    simpa [DDS.ofFunq] using (congrArg f hx).trans hout
  have hP : P i.val := Nat.strongRecOn i.val hstep
  exact hP i rfl

/-- For a stateless function oracle, compatibility plus equality of the
fixed-query transcript implies equality of the adaptive transcript. -/
theorem interact_ofFunq_eq_of_compatible
    {X Y : Type*} {q : ℕ} (f : X → Y) (e : DDE X Y q)
    (t : Transcript X Y q)
    (hcompat : Transcript.compatibleWithEnv e t)
    (hfixed : DDS.transcript (DDS.ofFunq (q := q) f) (fun i => (t i).1) = t) :
    interact (DDS.ofFunq (q := q) f) e = t := by
  have hx := interactInput_ofFunq_eq_of_transcript f e t hcompat hfixed
  funext i
  apply Prod.ext
  · simpa [interact] using hx i
  · have hpoint := congr_fun hfixed i
    have hout : f ((t i).1) = (t i).2 := by
      simpa [DDS.transcript, DDS.ofFunq] using congrArg Prod.snd hpoint
    simpa [interact, DDS.ofFunq] using (congrArg f (hx i)).trans hout

/-- Any actual interaction transcript is compatible with the environment that
produced it. -/
theorem compatibleWithEnv_of_interact_eq
    {X Y : Type*} {q : ℕ} (s : DDS X Y q) (e : DDE X Y q)
    (t : Transcript X Y q) (h : interact s e = t) :
    Transcript.compatibleWithEnv e t := by
  intro i
  have hpoint := congr_fun h i
  have hx : (t i).1 = interactInput s e i := by
    rw [← hpoint]
    rfl
  rw [hx]
  unfold interactInput
  congr 1
  funext j
  have hjq : j.val < q := Nat.lt_trans j.isLt i.isLt
  have hprev := congr_fun h ⟨j.val, hjq⟩
  simpa [interact] using congrArg Prod.snd hprev

/-- If a stateless function oracle adaptively produces transcript `t`, then
running the same function non-adaptively on the queries recorded in `t` also
produces `t`. -/
theorem transcript_ofFunq_inputs_of_interact_eq
    {X Y : Type*} {q : ℕ} (f : X → Y) (e : DDE X Y q)
    (t : Transcript X Y q) (h : interact (DDS.ofFunq (q := q) f) e = t) :
    DDS.transcript (DDS.ofFunq (q := q) f) (fun i => (t i).1) = t := by
  funext i
  have hpoint := congr_fun h i
  apply Prod.ext
  · rfl
  · have hx : (t i).1 = interactInput (DDS.ofFunq (q := q) f) e i := by
      rw [← hpoint]
      rfl
    have hy : f (interactInput (DDS.ofFunq (q := q) f) e i) = (t i).2 := by
      simpa [interact, DDS.ofFunq] using congrArg Prod.snd hpoint
    simpa [DDS.transcript, DDS.ofFunq] using (congrArg f hx).trans hy

/-- Characterization of adaptive transcripts for stateless function oracles:
they are exactly environment-compatible transcripts whose fixed-query replay on
the recorded inputs matches. -/
theorem interact_ofFunq_eq_iff
    {X Y : Type*} {q : ℕ} (f : X → Y) (e : DDE X Y q)
    (t : Transcript X Y q) :
    interact (DDS.ofFunq (q := q) f) e = t ↔
      Transcript.compatibleWithEnv e t ∧
        DDS.transcript (DDS.ofFunq (q := q) f) (fun i => (t i).1) = t := by
  constructor
  · intro h
    exact ⟨compatibleWithEnv_of_interact_eq _ _ _ h,
      transcript_ofFunq_inputs_of_interact_eq f e t h⟩
  · intro h
    exact interact_ofFunq_eq_of_compatible f e t h.1 h.2

/-! ### Stateless DDS (`DDS.ofFunq`) and output-precomposed environments -/

section OfFunq

variable {X Y Y' : Type*} {q : ℕ}

-- This helper lemma lets us reduce `DDS.ofFunq` responses inside `interactInput`.
private lemma ofFunq_respond (f : X → Y') (j : Fin q) (inputs : Fin (j.val + 1) → X) :
    (DDS.ofFunq (q := q) f).respond j inputs =
      f (inputs ⟨j.val, Nat.lt_succ_iff.mpr le_rfl⟩) := by
  rfl

/-- `interactInput` is stable under output precomposition for stateless DDS.

If `s` is stateless (`DDS.ofFunq f`) and the environment only depends on outputs through a map
`g`, then composing `f` with `g` and feeding `e` directly yields the same input sequence. -/
theorem interactInput_ofFunq_mapOutput (f : X → Y') (g : Y' → Y) (e : DDE X Y q) :
    ∀ i : Fin q,
      interactInput (DDS.ofFunq (q := q) f) (DDE.mapOutput g e) i =
        interactInput (DDS.ofFunq (q := q) (g ∘ f)) e i := by
  classical
  intro i
  -- Strong induction on the index value, since `interactInput` recurses on earlier indices.
  let P : ℕ → Prop := fun n =>
    ∀ i : Fin q, i.val = n →
      interactInput (DDS.ofFunq (q := q) f) (DDE.mapOutput g e) i =
        interactInput (DDS.ofFunq (q := q) (g ∘ f)) e i
  have hstep : ∀ n, (∀ m, m < n → P m) → P n := by
    intro n ih i hi
    cases hi
    unfold interactInput
    simp [DDE.mapOutput]
    congr 1
    funext j
    have hjq : j.val < q := Nat.lt_trans j.isLt i.isLt
    have hrec :
        interactInput (DDS.ofFunq (q := q) f) (DDE.mapOutput g e) ⟨j.val, hjq⟩ =
          interactInput (DDS.ofFunq (q := q) (g ∘ f)) e ⟨j.val, hjq⟩ := by
      exact (ih j.val j.isLt) ⟨j.val, hjq⟩ rfl
    -- `DDS.ofFunq` only depends on the current input, so the previous-output functions match.
    simpa [ofFunq_respond, DDS.ofFunq, Function.comp] using congrArg (fun x => g (f x)) hrec
  have hP : P i.val := Nat.strongRecOn i.val hstep
  exact hP i rfl

/-- Projecting the transcript of a stateless DDS interacting with a precomposed environment
is the same as interacting with the composed function. -/
theorem interact_ofFunq_mapOutput (f : X → Y') (g : Y' → Y) (e : DDE X Y q) :
    (fun i =>
      let p := interact (DDS.ofFunq (q := q) f) (DDE.mapOutput g e) i
      (p.1, g p.2)) =
    interact (DDS.ofFunq (q := q) (g ∘ f)) e := by
  funext i
  have hx :=
    interactInput_ofFunq_mapOutput (q := q) (f := f) (g := g) (e := e) i
  -- Unfold the transcript; `DDS.ofFunq` makes the output depend only on the current input.
  simp [interact, ofFunq_respond, Function.comp, hx]

end OfFunq

/-- At every adaptive query, a stateless DDS returns its underlying function
applied to the current input. -/
theorem interact_ofFunq_output_eq {X Y : Type*} {q : ℕ}
    (f : X → Y) (e : DDE X Y q) (i : Fin q) :
    (interact (DDS.ofFunq (q := q) f) e i).2 =
      f ((interact (DDS.ofFunq (q := q) f) e i).1) := by
  simp [interact, DDS.ofFunq]

/-- Adaptive transcripts produced by stateless DDSs are repeat-consistent. -/
theorem interact_ofFunq_repeatConsistent {X Y : Type*} {q : ℕ}
    (f : X → Y) (e : DDE X Y q) :
    Transcript.RepeatConsistent (interact (DDS.ofFunq (q := q) f) e) := by
  intro i j hij
  rw [interact_ofFunq_output_eq (q := q) f e i]
  rw [interact_ofFunq_output_eq (q := q) f e j]
  rw [hij]

end RandomSystems
