/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.DDE
import RandomSystems.CR18.DDS

/-!
# CR18 Definition 3.6 — Deterministic Discrete Environment (DDE)

Faithful formalization of Maurer's CR18 Definition 3.6. A deterministic
discrete environment for an `(X, Y)`-DDS (a `(Y, X)`-DDE) is a function
`e : (Y ∪ {⊥})* → X ∪ {⊣}` where `⊣` means the environment stops.

We model `Y ∪ {⊥}` as `Option Y` (`none = ⊥`, matching the CR18
`DDS.fullyDefined` convention), and `X ∪ {⊣}` as `Option X`
(`none = ⊣ = stop`). The history is the finite sequence of outputs the
environment has received so far; `e []` is the first input `x₁ = e(ε)`.
-/

namespace RandomSystems.CR18

/-- CR18 Def 3.6: a deterministic discrete environment `e : (Y∪{⊥})* → X∪{⊣}`.
`none` inside the input list is `⊥` (the system did not reply); a `none`
result is `⊣` (the environment stops). -/
def DDE (X Y : Type*) := List (Option Y) → Option X

namespace DDE

variable {X Y : Type*}

/-- The environment stops (outputs `⊣`) after seeing history `l`. -/
def Stops (e : DDE X Y) (l : List (Option Y)) : Prop := e l = none

/-- The first input `x₁ = e(ε)`: the environment's output on the empty history. -/
def firstInput (e : DDE X Y) : Option X := e []

/-- Interpret the existing total fixed-`q` adaptive environment
`RandomSystems.DDE` (Lanzenberger–Maurer) as a CR18 Def 3.6 DDE.

On a history `l`, if `l.length < q` and every received output is `some y`
(no `⊥`), produce the next input `e.choose ⟨l.length, _⟩ (fun i ↦ yᵢ)`;
otherwise stop (`⊣ = none`). The legacy environment makes exactly `q`
queries and never sees `⊥`, so once `q` outputs have been received — or a
`⊥` appears — the CR18 environment correctly emits `⊣`. -/
def ofTotal {q : ℕ} (e : RandomSystems.DDE X Y q) : DDE X Y := fun l =>
  if h : l.length < q ∧ ∀ i : Fin l.length, (l.get i).isSome then
    some (e.choose ⟨l.length, h.1⟩ (fun i => (l.get i).get (h.2 i)))
  else none

/-- `ofTotal` faithfully transports the legacy environment: on the empty
history it emits the legacy environment's first input `e.choose 0 _` (defined
on `ε`, as required by CR18), provided the legacy environment makes at least
one query. This makes the "relates the existing `RandomSystems.DDE`" claim a
checked theorem rather than an unverified assertion. -/
theorem ofTotal_firstInput {q : ℕ} (e : RandomSystems.DDE X Y q) (hq : 0 < q) :
    (ofTotal e).firstInput = some (e.choose ⟨0, hq⟩ (fun i => i.elim0)) := by
  simp only [firstInput, ofTotal]
  rw [dif_pos ⟨hq, fun i => i.elim0⟩]
  congr 1
  congr 1
  funext i
  exact i.elim0

/-- `ofTotal` correctly emits `⊣` (stops) once the legacy environment has
exhausted its `q` queries: any history of length `≥ q` maps to `none`. This
shows `ofTotal e` is not the trivial constant-stop environment. -/
theorem ofTotal_stop_of_le {q : ℕ} (e : RandomSystems.DDE X Y q)
    (l : List (Option Y)) (h : q ≤ l.length) : ofTotal e l = none := by
  simp only [ofTotal]
  rw [dif_neg]
  rintro ⟨h1, _⟩
  omega

end DDE

end RandomSystems.CR18

namespace RandomSystems.CR18

namespace DDE

variable {X Y : Type*}

/-- CR18 Definition 3.7: a finite prefix of the transcript `tr(s,e)`.

The prefix records separately the input history `(x₁, ..., xₙ)` sent by the
environment and the output history `(y₁, ..., yₙ)` produced by `s⊥`. This is the
faithful stop-aware representation of Maurer's possibly infinite transcript:
the environment consumes only the output history, while `s⊥` consumes only the
input history. -/
structure TranscriptPrefix (X Y : Type*) where
  inputs : List X
  outputs : List (Option Y)

namespace TranscriptPrefix

/-- CR18 Definition 3.7: the empty transcript prefix before any interaction
between a deterministic discrete system and environment. -/
def empty : TranscriptPrefix X Y where
  inputs := []
  outputs := []

/-- CR18 Definition 3.7: pair view of a transcript prefix, listing the
available `(xᵢ, yᵢ)` pairs. -/
def pairs (t : TranscriptPrefix X Y) : List (X × Option Y) :=
  t.inputs.zip t.outputs

/-- CR18 Definition 3.7: the zero-based `i`-th input of a transcript prefix,
corresponding to Maurer's `(i+1)`-st input. -/
def inputAt (t : TranscriptPrefix X Y) (i : Nat) (h : i < t.inputs.length) : X :=
  t.inputs.get ⟨i, h⟩

/-- CR18 Definition 3.7: the optional zero-based `i`-th input of a transcript
prefix, corresponding to Maurer's `(i+1)`-st input. -/
def inputAt? (t : TranscriptPrefix X Y) (i : Nat) : Option X :=
  t.inputs[i]?

/-- CR18 Definition 3.7: the zero-based `i`-th output of a transcript prefix,
corresponding to Maurer's `(i+1)`-st output. -/
def outputAt (t : TranscriptPrefix X Y) (i : Nat) (h : i < t.outputs.length) :
    Option Y :=
  t.outputs.get ⟨i, h⟩

/-- CR18 Definition 3.7: the optional zero-based `i`-th output of a transcript
prefix, corresponding to Maurer's `(i+1)`-st output. -/
def outputAt? (t : TranscriptPrefix X Y) (i : Nat) : Option (Option Y) :=
  t.outputs[i]?

end TranscriptPrefix

/-- CR18 Definition 3.7: extend a transcript prefix by one environment input.

Given the current output history `(y₁, ..., yᵢ₋₁)` and a new input `xᵢ`, this
appends `xᵢ` to the input history and appends
`yᵢ = s⊥(x₁, ..., xᵢ)` to the output history. -/
def extendWithInput (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (t : TranscriptPrefix X Y) (x : X) : TranscriptPrefix X Y :=
  let inputs' := t.inputs ++ [x]
  let y := (DDS.fullyDefined s).output inputs' (by
    have hne : inputs' ≠ [] := by
      dsimp [inputs']
      simp
    simpa [DDS.fullyDefined] using hne)
  { inputs := inputs', outputs := t.outputs ++ [y] }

/-- CR18 Definition 3.7: one stop-aware transcript step.

The step computes `xᵢ := e(y₁, ..., yᵢ₋₁)`. If the result is `none`
(`⊣`, stop), the accumulated transcript is returned unchanged; otherwise the
input is appended and `yᵢ := s⊥(x₁, ..., xᵢ)` is appended. -/
def transcriptStep (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (e : DDE X Y) (t : TranscriptPrefix X Y) : TranscriptPrefix X Y :=
  match e t.outputs with
  | none => t
  | some x => extendWithInput s t x

/-- CR18 Definition 3.7: fuel-bounded driver for the possibly infinite
transcript `tr(s,e)`.

The driver starts from an accumulated prefix. Each unit of fuel performs one
CR18 transcript step unless the environment returns `⊣`, in which case the
driver halts immediately and returns the accumulated prefix ending with the
last output already produced. -/
def runTranscript (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (e : DDE X Y) : Nat → TranscriptPrefix X Y → TranscriptPrefix X Y
  | 0, t => t
  | n + 1, t =>
      match e t.outputs with
      | none => t
      | some x => runTranscript s e n (extendWithInput s t x)

/-- CR18 Definition 3.7: the fuel-bounded transcript prefix `tr(s,e)`.

This partial-function, stop-symbol-aware transcript is the CR18 analogue of the
legacy fixed-query `RandomSystems.interact` transcript: the legacy model returns
a total `Fin q → X × Y`, while this CR18 driver stops when the environment
returns `none` (`⊣`) and records `Option Y` outputs from `s⊥`. -/
def transcript (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (e : DDE X Y) (fuel : Nat) : TranscriptPrefix X Y :=
  runTranscript s e fuel TranscriptPrefix.empty

/-- CR18 Definition 3.7: notation-style alias for the fuel-bounded transcript
`tr(s,e)`. -/
abbrev tr (s : DDS X Y) [DecidablePred (fun l : List X => l ∈ s.dom)]
    (e : DDE X Y) (fuel : Nat) : TranscriptPrefix X Y :=
  transcript s e fuel

/-- CR18 Definition 3.7: if the environment stops at the current output
history, one transcript step returns the accumulated prefix unchanged. -/
@[simp]
theorem transcriptStep_of_stop (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (t : TranscriptPrefix X Y) (hstop : e t.outputs = none) :
    transcriptStep s e t = t := by
  simp [transcriptStep, hstop]

/-- CR18 Definition 3.7: if the environment returns `some x`, one transcript
step appends `x` and then appends the corresponding `s⊥` output. -/
@[simp]
theorem transcriptStep_of_input (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (t : TranscriptPrefix X Y) {x : X} (hinput : e t.outputs = some x) :
    transcriptStep s e t = extendWithInput s t x := by
  simp [transcriptStep, hinput]

/-- CR18 Definition 3.7: if the environment stops at the current output
history, the fuel-bounded driver halts with the prefix ending in the last
already produced output. -/
theorem runTranscript_halting_clause (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (t : TranscriptPrefix X Y) (fuel : Nat) (hstop : e t.outputs = none) :
    runTranscript s e (fuel + 1) t = t := by
  cases fuel <;> simp [runTranscript, hstop]

/-- CR18 Definition 3.7: the fuel-bounded driver preserves equality of input
and output history lengths from any accumulated transcript prefix. -/
theorem runTranscript_lengths_eq_of_eq (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (fuel : Nat) (t : TranscriptPrefix X Y)
    (h : t.inputs.length = t.outputs.length) :
    (runTranscript s e fuel t).inputs.length =
      (runTranscript s e fuel t).outputs.length := by
  induction fuel generalizing t with
  | zero =>
      simpa [runTranscript] using h
  | succ n ih =>
      simp [runTranscript]
      split
      · simpa using h
      · apply ih
        simp [extendWithInput, h]

/-- CR18 Definition 3.7: the input and output histories in a fuel-bounded
transcript prefix have the same length. -/
theorem transcript_lengths_eq (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (fuel : Nat) :
    (transcript s e fuel).inputs.length = (transcript s e fuel).outputs.length := by
  simpa [transcript, TranscriptPrefix.empty] using
    runTranscript_lengths_eq_of_eq s e fuel TranscriptPrefix.empty rfl

/-- CR18 Definition 3.7: every recorded output position has a nonempty input
prefix, so `s⊥` is defined on the first `i+1` inputs. -/
theorem transcript_input_prefix_mem_fullyDefined_dom (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (fuel i : Nat) (h : i < (transcript s e fuel).outputs.length) :
    (transcript s e fuel).inputs.take (i + 1) ∈ (DDS.fullyDefined s).dom := by
  have hi : i < (transcript s e fuel).inputs.length := by
    simpa [transcript_lengths_eq s e fuel] using h
  have hpos : 0 < ((transcript s e fuel).inputs.take (i + 1)).length := by
    rw [List.length_take]
    omega
  have hne : (transcript s e fuel).inputs.take (i + 1) ≠ [] :=
    List.length_pos_iff.mp hpos
  simpa [DDS.fullyDefined] using hne

private def PrefixInputsFromEnvironment (e : DDE X Y) (t : TranscriptPrefix X Y) :
    Prop :=
  ∀ (i : Nat) (h : i < t.inputs.length),
    some (t.inputs.get ⟨i, h⟩) = e (t.outputs.take i)

private def PrefixOutputsFromSystem (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (t : TranscriptPrefix X Y) :
    Prop :=
  ∀ (i : Nat) (h : i < t.outputs.length)
    (hdom : t.inputs.take (i + 1) ∈ (DDS.fullyDefined s).dom),
    t.outputs.get ⟨i, h⟩ =
      (DDS.fullyDefined s).output (t.inputs.take (i + 1)) hdom

private theorem extendWithInput_lengths_eq_of_eq (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)]
    (t : TranscriptPrefix X Y) (x : X)
    (hlen : t.inputs.length = t.outputs.length) :
    (extendWithInput s t x).inputs.length =
      (extendWithInput s t x).outputs.length := by
  simp [extendWithInput, hlen]

private theorem extendWithInput_inputsFromEnvironment (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (t : TranscriptPrefix X Y) (x : X)
    (hlen : t.inputs.length = t.outputs.length)
    (hinv : PrefixInputsFromEnvironment e t)
    (hx : e t.outputs = some x) :
    PrefixInputsFromEnvironment e (extendWithInput s t x) := by
  intro i h
  dsimp [PrefixInputsFromEnvironment, extendWithInput] at *
  by_cases hi : i < t.inputs.length
  · have htake_le : i ≤ t.outputs.length := by omega
    rw [List.getElem_append_left hi]
    rw [List.take_append_of_le_length htake_le]
    exact hinv i hi
  · have hi_eq : i = t.inputs.length := by
      have hlen_i : i < t.inputs.length + 1 := by
        simpa [extendWithInput, List.length_append] using h
      omega
    subst i
    simp [hlen, hx]

private theorem extendWithInput_outputsFromSystem (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)]
    (t : TranscriptPrefix X Y) (x : X)
    (hlen : t.inputs.length = t.outputs.length)
    (hout : PrefixOutputsFromSystem s t) :
    PrefixOutputsFromSystem s (extendWithInput s t x) := by
  intro i h hdom
  dsimp [PrefixOutputsFromSystem, extendWithInput] at *
  by_cases hi : i < t.outputs.length
  · have htake_le : i + 1 ≤ t.inputs.length := by omega
    have htake : (t.inputs ++ [x]).take (i + 1) =
        t.inputs.take (i + 1) := by
      exact List.take_append_of_le_length htake_le
    have hdom' : t.inputs.take (i + 1) ∈ (DDS.fullyDefined s).dom := by
      simpa [extendWithInput, htake] using hdom
    rw [List.getElem_append_left hi]
    trans (DDS.fullyDefined s).output (t.inputs.take (i + 1)) hdom'
    · exact hout i hi hdom'
    · simp [DDS.output, DDS.fullyDefined, htake]
  · have hi_eq : i = t.outputs.length := by
      have hlen_i : i < t.outputs.length + 1 := by
        simpa [extendWithInput, List.length_append] using h
      omega
    subst i
    have htake : (t.inputs ++ [x]).take (t.outputs.length + 1) =
        t.inputs ++ [x] := by
      rw [← hlen]
      simp
    simp [DDS.output, DDS.fullyDefined, htake]

private theorem runTranscript_inputsFromEnvironment (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (fuel : Nat) (t : TranscriptPrefix X Y)
    (hlen : t.inputs.length = t.outputs.length)
    (hinv : PrefixInputsFromEnvironment e t) :
    PrefixInputsFromEnvironment e (runTranscript s e fuel t) := by
  induction fuel generalizing t with
  | zero =>
      simpa [runTranscript] using hinv
  | succ n ih =>
      cases hx : e t.outputs with
      | none =>
          simpa [runTranscript, hx] using hinv
      | some x =>
          simpa [runTranscript, hx] using
            ih (extendWithInput s t x)
              (extendWithInput_lengths_eq_of_eq s t x hlen)
              (extendWithInput_inputsFromEnvironment s e t x hlen hinv hx)

private theorem runTranscript_outputsFromSystem (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (fuel : Nat) (t : TranscriptPrefix X Y)
    (hlen : t.inputs.length = t.outputs.length)
    (hout : PrefixOutputsFromSystem s t) :
    PrefixOutputsFromSystem s (runTranscript s e fuel t) := by
  induction fuel generalizing t with
  | zero =>
      simpa [runTranscript] using hout
  | succ n ih =>
      cases hx : e t.outputs with
      | none =>
          simpa [runTranscript, hx] using hout
      | some x =>
          simpa [runTranscript, hx] using
            ih (extendWithInput s t x)
              (extendWithInput_lengths_eq_of_eq s t x hlen)
              (extendWithInput_outputsFromSystem s t x hlen hout)

/-- CR18 Definition 3.7: first defining equation for `tr(s,e)`.

For a recorded zero-based position `i`, corresponding to Maurer's index `i+1`,
the input is exactly
`xᵢ₊₁ = e(y₁, ..., yᵢ)`, represented by applying `e` to the first `i`
recorded outputs. -/
theorem transcript_input_eq_environment (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (fuel i : Nat) (h : i < (transcript s e fuel).inputs.length) :
    some (TranscriptPrefix.inputAt (transcript s e fuel) i h) =
      e ((transcript s e fuel).outputs.take i) := by
  have hinv :
      PrefixInputsFromEnvironment e
        (runTranscript s e fuel TranscriptPrefix.empty) :=
    runTranscript_inputsFromEnvironment s e fuel TranscriptPrefix.empty rfl (by
      intro i h
      simp [TranscriptPrefix.empty] at h)
  simpa [transcript, PrefixInputsFromEnvironment, TranscriptPrefix.inputAt]
    using hinv i h

/-- CR18 Definition 3.7: second defining equation for `tr(s,e)`.

For a recorded zero-based position `i`, corresponding to Maurer's index `i+1`,
the output is exactly
`yᵢ₊₁ = s⊥(x₁, ..., xᵢ₊₁)`, represented by applying `DDS.fullyDefined s` to
the first `i+1` recorded inputs. -/
theorem transcript_output_eq_fullyDefined (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (fuel i : Nat) (h : i < (transcript s e fuel).outputs.length) :
    TranscriptPrefix.outputAt (transcript s e fuel) i h =
      (DDS.fullyDefined s).output
        ((transcript s e fuel).inputs.take (i + 1))
        (transcript_input_prefix_mem_fullyDefined_dom (s := s) (e := e)
          (fuel := fuel) (i := i) h) := by
  have hout :
      PrefixOutputsFromSystem s
        (runTranscript s e fuel TranscriptPrefix.empty) :=
    runTranscript_outputsFromSystem s e fuel TranscriptPrefix.empty rfl (by
      intro i h _hdom
      simp [TranscriptPrefix.empty] at h)
  simpa [transcript, PrefixOutputsFromSystem, TranscriptPrefix.outputAt]
    using hout i h
      (transcript_input_prefix_mem_fullyDefined_dom (s := s) (e := e)
        (fuel := fuel) (i := i) h)

/-- CR18 Definition 3.7: halting clause for a finished transcript prefix.

If the environment returns `⊣` on the current output history
`(y₁, ..., yᵢ₋₁)`, then any positive amount of additional fuel leaves the
accumulated transcript unchanged, i.e. the transcript ends with `yᵢ₋₁`. -/
theorem transcript_halts_from_stopped_prefix (s : DDS X Y)
    [DecidablePred (fun l : List X => l ∈ s.dom)] (e : DDE X Y)
    (fuel extraFuel : Nat) (hstop : e (transcript s e fuel).outputs = none) :
    runTranscript s e (extraFuel + 1) (transcript s e fuel) = transcript s e fuel :=
  runTranscript_halting_clause s e (transcript s e fuel) extraFuel hstop

end DDE

end RandomSystems.CR18
