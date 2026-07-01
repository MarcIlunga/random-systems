/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import RandomSystems.CR18.DDS
import RandomSystems.CR18.HistMap

/-!
# CR18 Deterministic Converters (Definition 3.8)

This module formalizes CR18 Definition 3.8: a deterministic discrete converter
for converting an `(X, Y)`-DDS into a `(U, V)`-DDS.

The source presents such a converter as a DDS over a converter input alphabet
`U union (Y union {bot})` and a converter output alphabet
`({out} x V) union ({in} x X)`. We model the input alphabet as
`Sum U (Option Y)`, where `Sum.inl u` is an outside input and `Sum.inr none`
is the distinguished `bot` response from the inner side. We model the output
alphabet by the inductive type `ConverterOutput`, using constructor name `inn`
for source label `in` because `in` is reserved in Lean.

The structure `DDC` is a DDS over those alphabets together with the three
alphabet-discipline constraints from CR18 Definition 3.8 and a finite bound on
consecutive inner calls.
-/

namespace RandomSystems.CR18

universe u v w z

/-- CR18 Definition 3.8: converter inputs are either outside inputs `u : U`
or inside-side responses in `Y union {bot}`. The Lean encoding is
`Sum U (Option Y)`: `Sum.inl u` is an input from the outside interface,
`Sum.inr (some y)` is a response `y : Y` from the inner DDS, and
`Sum.inr none` is the distinguished `bot`. -/
abbrev ConverterInput (U : Type u) (Y : Type v) : Type (max u v) :=
  Sum U (Option Y)

/-- CR18 Definition 3.8: converter outputs are either outside outputs
`out v`, with `v : V`, or inner calls `inn x`, with `x : X`. The constructor
name `inn` represents the source label `in`, which is reserved in Lean. -/
inductive ConverterOutput (V : Type w) (X : Type z) : Type (max w z) where
  /-- CR18 Definition 3.8: `out v` means output `v : V` at the outside
  interface. -/
  | out : V → ConverterOutput V X
  /-- CR18 Definition 3.8: `inn x` means feed `x : X` as input to the inner
  DDS. -/
  | inn : X → ConverterOutput V X

/-- CR18 Definition 3.8: a converter history has an inner-call output when the
underlying DDS responds to that history with an output of the form `inn x`. -/
def IsInnerCallOutput {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (s : DDS (ConverterInput U Y) (ConverterOutput V X))
    (l : List (ConverterInput U Y)) : Prop :=
  ∃ h : l ∈ s.dom, ∃ x : X, s.respond l h = ConverterOutput.inn x

/-- CR18 Definition 3.8: a run of consecutive inner calls is a list of
successive in-domain histories whose outputs are all of the form `inn x`, where
each next history extends the previous one by exactly one converter input. -/
inductive InnerCallRun {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (s : DDS (ConverterInput U Y) (ConverterOutput V X)) :
    List (List (ConverterInput U Y)) → Prop where
  /-- CR18 Definition 3.8: the empty run of inner-call outputs. -/
  | nil : InnerCallRun s []
  /-- CR18 Definition 3.8: a one-history run whose current output is an inner
  call. -/
  | singleton {l : List (ConverterInput U Y)} :
      IsInnerCallOutput s l → InnerCallRun s [l]
  /-- CR18 Definition 3.8: extend a consecutive inner-call run backward by one
  history, requiring the next history to be a one-input extension. -/
  | cons {l₁ l₂ : List (ConverterInput U Y)}
      {rest : List (List (ConverterInput U Y))} :
      IsInnerCallOutput s l₁ →
      (∃ i : ConverterInput U Y, l₂ = l₁ ++ [i]) →
      InnerCallRun s (l₂ :: rest) →
      InnerCallRun s (l₁ :: l₂ :: rest)

/-- CR18 Definition 3.8: a deterministic discrete converter, a
`((U, V), (X, Y))`-DDC.

The field `system` is the DDS over converter inputs and outputs. The remaining
fields record the alphabet discipline stated in CR18 Definition 3.8:
histories start with a `U` input, a converter output `inn x` is followed only
by an accepted `Y union {bot}` input, and a converter output `out v` is
followed only by an accepted `U` input. The fields `innerCallBound` and
`bounded_inner_calls` record the finite upper bound on consecutive outputs of
the form `inn x`. -/
structure DDC (U : Type u) (V : Type w) (X : Type z) (Y : Type v) where
  /-- CR18 Definition 3.8: the converter is a DDS over converter input and
  output alphabets. -/
  system : DDS (ConverterInput U Y) (ConverterOutput V X)
  /-- CR18 Definition 3.8: every accepted nonempty converter history begins
  with an outside input from `U`. -/
  starts_with_U :
    ∀ {i : ConverterInput U Y} {rest : List (ConverterInput U Y)},
      i :: rest ∈ system.dom → ∃ u : U, i = (@Sum.inl U (Option Y) u)
  /-- CR18 Definition 3.8: after an output of the form `inn x`, the next
  accepted input, if any, is from `Y union {bot}`. -/
  input_after_inn :
    ∀ {l : List (ConverterInput U Y)} (h : l ∈ system.dom) {x : X}
      {i : ConverterInput U Y},
      system.respond l h = ConverterOutput.inn x →
      l ++ [i] ∈ system.dom → ∃ y : Option Y, i = (@Sum.inr U (Option Y) y)
  /-- CR18 Definition 3.8: after an output of the form `out v`, the next
  accepted input, if any, is from `U`. -/
  input_after_out :
    ∀ {l : List (ConverterInput U Y)} (h : l ∈ system.dom) {v' : V}
      {i : ConverterInput U Y},
      system.respond l h = ConverterOutput.out v' →
      l ++ [i] ∈ system.dom → ∃ u : U, i = (@Sum.inl U (Option Y) u)
  /-- CR18 Definition 3.8: the finite upper bound on consecutive inner calls. -/
  innerCallBound : Nat
  /-- CR18 Definition 3.8: every run of consecutive outputs of the form
  `inn x` has length at most `innerCallBound`. -/
  bounded_inner_calls :
    ∀ {run : List (List (ConverterInput U Y))},
      InnerCallRun system run → run.length ≤ innerCallBound

namespace DDC

/-- CR18 Definition 3.8: smoke-test converter that immediately outputs a fixed
outside value `v0` and never calls the inner DDS. Its accepted histories are
exactly the nonempty histories consisting only of outside `U` inputs. -/
def trivial {U : Type u} {V : Type w} {X : Type z} {Y : Type v} (v0 : V) :
    DDC U V X Y where
  system := {
    dom := {l | l ≠ [] ∧ ∀ i ∈ l, ∃ u : U, i = (@Sum.inl U (Option Y) u)}
    nonempty_input := by
      intro h
      exact h.1 rfl
    prefix_closed := by
      intro l₁ l₂ hprefix h_nonempty hdom
      constructor
      · exact h_nonempty
      · intro i hi
        obtain ⟨tail, htail⟩ := hprefix
        rw [← htail] at hdom
        exact hdom.2 i (by simp [hi])
    respond := fun _ _ => ConverterOutput.out v0
  }
  starts_with_U := by
    intro i rest h
    exact h.2 i (by simp)
  input_after_inn := by
    intro _l _h _x _i hout _hnext
    cases hout
  input_after_out := by
    intro _l _h _v' i _hout hnext
    exact hnext.2 i (by simp)
  innerCallBound := 0
  bounded_inner_calls := by
    intro _run hrun
    induction hrun with
    | nil =>
        simp
    | singleton hinner =>
        obtain ⟨_, _, houtput⟩ := hinner
        cases houtput
    | cons hinner _ _ =>
        obtain ⟨_, _, houtput⟩ := hinner
        cases houtput

/-!
## CR18 Definition 3.9

Maurer explicitly leaves the application of a converter to a system only
semi-formal. This section fixes that gap by giving an operational
fixpoint-over-the-trace semantics for the notation `alpha-s`.

For an outside input history, we maintain two histories: the converter-input
trace and the inner-system input trace. On a new outside input `u`, the driver
appends `Sum.inl u` to the converter trace and asks the converter DDS for its
next output. If the converter outputs `inn x`, the driver queries the fully
defined completion `s_bot = DDS.fullyDefined s` on the extended inner trace,
appends the resulting `Option Y` response as `Sum.inr y` to the converter
trace, and continues. If the converter outputs `out v`, that `v` is the output
for the most recent outside input.

The recursion is fuel-bounded by `alpha.innerCallBound`, the finite bound from
CR18 Definition 3.8 on consecutive inner calls. Operational undefinedness is
represented by `none`: the converter trace is outside `alpha.system.dom`, the
fuel is exhausted before an outside output appears, or a previous outside input
failed. The induced DDS domain consists exactly of nonempty outside-input
histories for which this driver returns `some v`.
-/

/-- CR18 Definition 3.9: state returned by one successful run of the converter
driver. It records the updated converter trace, the updated inner-system trace,
and the outside output for the most recent outside input. -/
abbrev ApplyRunState (U : Type u) (V : Type w) (X : Type z) (Y : Type v) :=
  List (ConverterInput U Y) × List X × V

/-- CR18 Definition 3.9: query the fully-defined completion `s_bot` of the
inner DDS after appending one inner input to the current inner trace. -/
def completedInnerResponse {X : Type z} {Y : Type v} (s : DDS X Y)
    [DecidablePred (fun l => l ∈ s.dom)] (innerTrace : List X) (x : X) :
    Option Y :=
  (DDS.fullyDefined s).respond (innerTrace ++ [x]) (by
    simp [DDS.fullyDefined])

/-- CR18 Definition 3.9: fuel-bounded driver for the converter trace.

`runConverter alpha s fuel converterTrace innerTrace` starts from the current
converter-input trace and inner-system trace. It returns `some state` after the
converter produces an outside output, and returns `none` if the converter is
undefined at the current trace or if the fuel is exhausted while the converter
keeps making inner calls. -/
def runConverter {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] :
    Nat → List (ConverterInput U Y) → List X → Option (ApplyRunState U V X Y)
  | 0, converterTrace, innerTrace =>
      if hconv : converterTrace ∈ alpha.system.dom then
        match alpha.system.respond converterTrace hconv with
        | ConverterOutput.out v => some (converterTrace, innerTrace, v)
        | ConverterOutput.inn _ => none
      else
        none
  | fuel + 1, converterTrace, innerTrace =>
      if hconv : converterTrace ∈ alpha.system.dom then
        match alpha.system.respond converterTrace hconv with
        | ConverterOutput.out v => some (converterTrace, innerTrace, v)
        | ConverterOutput.inn x =>
            let y := completedInnerResponse s innerTrace x
            runConverter alpha s fuel (converterTrace ++ [Sum.inr y]) (innerTrace ++ [x])
      else
        none

/-- CR18 Definition 3.9: process an outside-input history while threading the
converter trace and inner-system trace. The final `V` is the output for the
last outside input in the history. -/
def applyTraceAux {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] (fuel : Nat) :
    List U → List (ConverterInput U Y) → List X → Option (ApplyRunState U V X Y)
  | [], _, _ => none
  | u :: us, converterTrace, innerTrace =>
      match runConverter alpha s fuel (converterTrace ++ [Sum.inl u]) innerTrace with
      | none => none
      | some (converterTrace', innerTrace', v) =>
          match us with
          | [] => some (converterTrace', innerTrace', v)
          | _ => applyTraceAux alpha s fuel us converterTrace' innerTrace'

/-- CR18 Definition 3.9: run `alpha` attached to `s` on an outside-input
history, returning the outside output for the most recent input if the
operational driver is defined. -/
def applyTrace {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] (inputs : List U) : Option V :=
  Option.map (fun state : ApplyRunState U V X Y => state.2.2)
    (applyTraceAux alpha s alpha.innerCallBound inputs [] [])

/-- CR18 Definition 3.9: processing a nonempty outside-input prefix is a
sub-run of processing the whole history; success propagates to prefixes. -/
theorem applyTraceAux_prefix {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)]
    (fuel : Nat) :
    ∀ (us₁ us₂ : List U) (ct : List (ConverterInput U Y)) (it : List X)
      (r : ApplyRunState U V X Y),
      us₁ ≠ [] →
      applyTraceAux alpha s fuel (us₁ ++ us₂) ct it = some r →
      ∃ r', applyTraceAux alpha s fuel us₁ ct it = some r' := by
  intro us₁
  induction us₁ with
  | nil => intro us₂ ct it r hne _; exact absurd rfl hne
  | cons u us ih =>
    intro us₂ ct it r _ hsucc
    cases us with
    | nil =>
        simp only [List.nil_append, List.cons_append] at hsucc ⊢
        unfold applyTraceAux at hsucc ⊢
        cases hrc : runConverter alpha s fuel (ct ++ [Sum.inl u]) it with
        | none => rw [hrc] at hsucc; simp at hsucc
        | some r0 =>
            rw [hrc] at hsucc
            obtain ⟨ct', it', v⟩ := r0
            simp
    | cons u2 us' =>
        simp only [List.cons_append] at hsucc ⊢
        unfold applyTraceAux at hsucc ⊢
        cases hrc : runConverter alpha s fuel (ct ++ [Sum.inl u]) it with
        | none => rw [hrc] at hsucc; simp at hsucc
        | some r0 =>
            rw [hrc] at hsucc
            obtain ⟨ct', it', v⟩ := r0
            simp only at hsucc
            exact ih us₂ ct' it' r (by simp) hsucc

/-- CR18 Definition 3.9: application of a converter to a DDS, written
`alpha-s` in the source text. The domain contains exactly the nonempty outside
histories for which the operational driver returns an outside output. -/
noncomputable def apply {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] : DDS U V where
  dom := {inputs | inputs ≠ [] ∧ ∃ v, applyTrace alpha s inputs = some v}
  nonempty_input := by
    intro h
    exact h.1 rfl
  prefix_closed := by
    intro l₁ l₂ hprefix h_nonempty hdom
    obtain ⟨us₂, rfl⟩ := hprefix
    obtain ⟨_, v, hv⟩ := hdom
    refine ⟨h_nonempty, ?_⟩
    unfold applyTrace at hv ⊢
    rw [Option.map_eq_some_iff] at hv
    obtain ⟨r, hr, _⟩ := hv
    obtain ⟨r', hr'⟩ :=
      applyTraceAux_prefix alpha s alpha.innerCallBound l₁ us₂ [] [] r h_nonempty hr
    exact ⟨r'.2.2, by rw [Option.map_eq_some_iff]; exact ⟨r', hr', rfl⟩⟩
  respond := fun _ h => Classical.choose h.2

/-- CR18 Definition 3.9: if the converter immediately produces an outside
output at the current converter trace, the fuel-bounded driver returns that
output without touching the inner DDS. -/
theorem runConverter_out {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)]
    (fuel : Nat) (converterTrace : List (ConverterInput U Y)) (innerTrace : List X)
    {v : V} (hconv : converterTrace ∈ alpha.system.dom)
    (hout : alpha.system.respond converterTrace hconv = ConverterOutput.out v) :
    runConverter alpha s fuel converterTrace innerTrace =
      some (converterTrace, innerTrace, v) := by
  cases fuel <;> simp [runConverter, hconv, hout]

/-- CR18 Definition 3.9: if the converter makes an inner call at the current
converter trace, the fuel-bounded driver appends the completed inner response
to the converter trace and the inner input to the inner trace, then continues
with one unit of fuel less. This is the defining-equation form of one driver
step. -/
theorem runConverter_inn {U : Type u} {V : Type w} {X : Type z} {Y : Type v}
    (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)]
    (fuel : Nat) (converterTrace : List (ConverterInput U Y)) (innerTrace : List X)
    {x : X} (hconv : converterTrace ∈ alpha.system.dom)
    (hout : alpha.system.respond converterTrace hconv = ConverterOutput.inn x) :
    runConverter alpha s (fuel + 1) converterTrace innerTrace =
      runConverter alpha s fuel
        (converterTrace ++ [Sum.inr (completedInnerResponse s innerTrace x)])
        (innerTrace ++ [x]) := by
  simp [runConverter, hconv, hout]

/-- CR18 Definition 3.9: outputs of the induced DDS agree with successful
runs of the operational driver when the domain proof is built from that run. -/
theorem apply_output_eq_of_applyTrace {U : Type u} {V : Type w} {X : Type z}
    {Y : Type v} (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)]
    (inputs : List U) {v : V} (h_nonempty : inputs ≠ [])
    (hrun : applyTrace alpha s inputs = some v) :
    (apply alpha s).output inputs ⟨h_nonempty, ⟨v, hrun⟩⟩ = v := by
  unfold DDS.output apply
  simp
  have hchoose := Classical.choose_spec
    (show ∃ v', applyTrace alpha s inputs = some v' from ⟨v, hrun⟩)
  exact Option.some.inj (hchoose.symm.trans hrun)

/-- CR18 Definition 3.9: one-input characterization for the no-inner-call
case. If `alpha` responds to the trace `[Sum.inl u]` with `out v`, then the
attached DDS `alpha-s` outputs `v` on the outside history `[u]`. -/
theorem apply_output_single_of_out {U : Type u} {V : Type w} {X : Type z}
    {Y : Type v} (alpha : DDC U V X Y) (s : DDS X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)]
    (u : U) {v : V} (hconv : [Sum.inl u] ∈ alpha.system.dom)
    (hout : alpha.system.respond [Sum.inl u] hconv = ConverterOutput.out v) :
    ∃ h : [u] ∈ (apply alpha s).dom, (apply alpha s).output [u] h = v := by
  have hrun : applyTrace alpha s [u] = some v := by
    simp [applyTrace, applyTraceAux,
      runConverter_out alpha s alpha.innerCallBound [Sum.inl u] [] hconv hout]
  refine ⟨⟨by simp, ⟨v, hrun⟩⟩, ?_⟩
  exact apply_output_eq_of_applyTrace alpha s [u] (by simp) hrun

end DDC

namespace DDS

variable {X Y Z : Type*}

/-!
## CR18 Definition 3.11: Cascade of DDSs

The cascade `s ⊲ t` feeds each output history of an `(X, Y)`-DDS `s` as the
input history of a `(Y, Z)`-DDS `t`. Undefinedness propagates: a history is in
the domain of the cascade exactly when it is in the domain of `s` and the
induced `Y`-history is in the domain of `t`.
-/

/-- CR18 Definition 3.11: intermediate output history induced by an
`(X, Y)`-DDS `s` on an accepted input history `l`.

For the `j`-th position, represented by `j : Fin l.length`, this list contains
`s.respond (l.take (j + 1)) _`, i.e. the response of `s` on the nonempty prefix
`(x₁, ..., xⱼ₊₁)`. Prefix-closedness of `s.dom` supplies the domain proof for
each such nonempty prefix. -/
def yHistory (s : DDS X Y) (l : List X) (h : l ∈ s.dom) : List Y :=
  (List.finRange l.length).map fun j =>
    s.respond (l.take (j.val + 1)) (by
      have hprefix : l.take (j.val + 1) <+: l := List.take_prefix (j.val + 1) l
      have hle : j.val + 1 ≤ l.length := Nat.succ_le_of_lt j.isLt
      have hlen : (l.take (j.val + 1)).length = j.val + 1 := by
        rw [List.length_take, Nat.min_eq_left hle]
      have hne : l.take (j.val + 1) ≠ [] := by
        intro hnil
        have hzero : (l.take (j.val + 1)).length = 0 := by
          simp [hnil]
        omega
      exact s.prefix_closed hprefix hne h)

/-- CR18 Definition 3.11: the intermediate `Y`-history has one response for
each input in the original `X`-history. -/
@[simp]
theorem yHistory_length (s : DDS X Y) (l : List X) (h : l ∈ s.dom) :
    (yHistory s l h).length = l.length := by
  simp [yHistory]

/-- CR18 Definition 3.11: the `j`-th entry of the intermediate `Y`-history is
`s`'s response on the length-`(j+1)` prefix of the input history. -/
theorem yHistory_getElem (s : DDS X Y) (l : List X) (h : l ∈ s.dom)
    (j : ℕ) (hj : j < (yHistory s l h).length) :
    (yHistory s l h)[j] =
      s.respond (l.take (j + 1))
        (s.prefix_closed (List.take_prefix (j + 1) l)
          (by
            have hjl : j < l.length := by simpa [yHistory] using hj
            have hlen : (l.take (j + 1)).length = j + 1 := by
              rw [List.length_take, Nat.min_eq_left (by omega)]
            intro hnil
            simp [hnil] at hlen) h) := by
  simp only [yHistory, List.getElem_map, List.getElem_finRange, Fin.cast_mk]

/-- CR18 Definition 3.11 (scan law 1): the intermediate `Y`-history is prefix
monotone — a prefix of the input history induces a prefix of the `Y`-history.
This is one of the two scan laws that make `yHistory s` a `HistMap`. -/
theorem yHistory_prefix (s : DDS X Y) {l₁ l₂ : List X}
    (h₁ : l₁ ∈ s.dom) (h₂ : l₂ ∈ s.dom) (hp : l₁ <+: l₂) :
    yHistory s l₁ h₁ <+: yHistory s l₂ h₂ := by
  -- The `Y`-history of `l₁` equals the length-`|l₁|` prefix of the `Y`-history
  -- of `l₂`, because the first `|l₁|` prefixes of `l₁` and `l₂` coincide.
  have hlen : l₁.length ≤ l₂.length := hp.length_le
  refine List.prefix_iff_eq_take.2 ?_
  apply List.ext_getElem
  · rw [yHistory_length, List.length_take, yHistory_length, Nat.min_eq_left hlen]
  · intro j hj1 hj2
    have hj1' : j < l₁.length := by
      have : j < (yHistory s l₁ h₁).length := hj1
      rwa [yHistory_length] at this
    have hj2' : j < l₂.length := by omega
    rw [yHistory_getElem s l₁ h₁ j hj1]
    rw [List.getElem_take]
    rw [yHistory_getElem s l₂ h₂ j (by rw [yHistory_length]; exact hj2')]
    -- The length-`(j+1)` prefixes of `l₁` and `l₂` agree since `l₁ <+: l₂`.
    have htake : l₁.take (j + 1) = l₂.take (j + 1) := by
      -- Both prefixes have length `j+1` (since `j+1 ≤ l₁.length ≤ l₂.length`),
      -- and `l₁.take (j+1) <+: l₂.take (j+1)`, so a same-length prefix is equality.
      have hpt : l₁.take (j + 1) <+: l₂.take (j + 1) := hp.take (j + 1)
      have hlen1 : (l₁.take (j + 1)).length = j + 1 := by
        rw [List.length_take]; omega
      have hlen2 : (l₂.take (j + 1)).length = j + 1 := by
        rw [List.length_take]; omega
      exact List.IsPrefix.eq_of_length_le hpt (by rw [hlen1, hlen2])
    -- Responses on definitionally-equal prefixes coincide.
    exact DDS.respond_congr s htake _ _

/-- CR18 Definition 3.11 (scan law 2): the intermediate `Y`-history of a defined
(hence nonempty) input history is nonempty. -/
theorem yHistory_ne_nil (s : DDS X Y) (l : List X) (h : l ∈ s.dom) :
    yHistory s l h ≠ [] := by
  intro hnil
  have : (yHistory s l h).length = 0 := by rw [hnil]; rfl
  rw [yHistory_length] at this
  exact s.nonempty_input (by rwa [List.length_eq_zero_iff.1 this] at h)

/-- CR18 Definition 3.11: the intermediate-`Y`-history morphism induced by an
`(X, Y)`-DDS `s`, as a `HistMap X Y`.

This is the canonical SCAN-shaped history morphism (built via `HistMap.ofScan`):
its `defined` set is `s.dom` (inheriting the `DDS`-domain discipline) and its
action on `l` is `yHistory s l = (s(x₁), s(x₁,x₂), …, s(x₁…xₖ))`. The two scan
laws are the already-proven `yHistory_prefix` (prefix monotonicity) and
`yHistory_ne_nil` (nonempty preservation). Cascade is then `comap` of this
morphism — the WF obligations are discharged once in `DDS.comap`. -/
def yHistoryMap (s : DDS X Y) : HistMap X Y :=
  HistMap.ofScan s.dom s.nonempty_input
    (fun hp hne hd => s.prefix_closed hp hne hd)
    (fun l h => yHistory s l h)
    (fun h₁ h₂ hp => yHistory_prefix s h₁ h₂ hp)
    (fun h => yHistory_ne_nil s _ h)

@[simp]
theorem yHistoryMap_defined (s : DDS X Y) (l : List X) :
    l ∈ (yHistoryMap s).defined ↔ l ∈ s.dom := Iff.rfl

@[simp]
theorem yHistoryMap_map (s : DDS X Y) (l : List X) (h : l ∈ (yHistoryMap s).defined) :
    (yHistoryMap s).map l h = yHistory s l h := rfl

/-- CR18 Definition 3.11: the cascade of an `(X, Y)`-DDS `s` and a `(Y, Z)`-DDS
`t`, written `s ⊲ t` in the source, **defined equationally** as the precomposition
(`DDS.comap`) of `t` with the intermediate-history morphism `yHistoryMap s`.

The cascade is defined on an `X`-history `l` exactly when `s` is defined on
`l` and the induced intermediate history
`yHistory s l h = (s(x₁), s(x₁,x₂), ..., s(x₁,...,xₖ))` is defined for `t`.
Its response is then `t`'s response to that intermediate history, capturing
`(s ⊲ t)(x₁,...,xₖ) = t(y₁,...,yₖ)`. Because cascade is now a `comap`, its
`prefix_closed`/`nonempty_input` obligations are inherited from `DDS.comap` and
no longer re-proved here (the previous `prefix_closed` `sorry` is eliminated). -/
def cascade (s : DDS X Y) (t : DDS Y Z) : DDS X Z :=
  DDS.comap (yHistoryMap s) t

/-- CR18 Definition 3.11: notation for DDS cascade, written `s ⊲ t` in the
source text. -/
scoped infixl:70 " ⊲ " => DDS.cascade

/-- CR18 Definition 3.11: domain characterization for cascade. A history is in the
cascade domain exactly when `s` is defined on it and the induced `Y`-history is in
`t.dom`. -/
@[simp]
theorem cascade_dom (s : DDS X Y) (t : DDS Y Z) (l : List X) :
    l ∈ (cascade s t).dom ↔ ∃ (h : l ∈ s.dom), yHistory s l h ∈ t.dom := by
  simp only [cascade, comap_dom, yHistoryMap_defined, yHistoryMap_map]

/-- CR18 Definition 3.11: output characterization for cascade. On every
history in the cascade domain, `(s ⊲ t)` returns exactly `t`'s output on the
intermediate history
`(s(x₁), s(x₁,x₂), ..., s(x₁,...,xₖ))`. This is a direct consequence of the
`comap` defining output equation. -/
theorem cascade_output (s : DDS X Y) (t : DDS Y Z) (l : List X)
    (h : l ∈ (cascade s t).dom) (hs : l ∈ s.dom) (ht : yHistory s l hs ∈ t.dom) :
    (cascade s t).output l h = t.output (yHistory s l hs) ht := by
  exact comap_output (yHistoryMap s) t l h hs ht

/-!
## CR18 Definition 3.12: Output-combine of DDSs

For two `(X, Y)`-DDSs `s` and `t` and an operation `op : Y → Y → Y`, the
combined DDS gives the same input history to both systems and combines their
outputs with `op`. Undefinedness propagates: a history is in the combined
domain exactly when it is in both component domains.
-/

/-- CR18 Definition 3.12: output-combine of two `(X, Y)`-DDSs.

The combined system is defined exactly on histories where both component
systems are defined. On such a history `l`, its response is
`op (s(l)) (t(l))`, formalizing
`(s star t)(x₁,...,xₖ) = s(x₁,...,xₖ) star t(x₁,...,xₖ)`. -/
def outputCombine (op : Y → Y → Y) (s t : DDS X Y) : DDS X Y where
  dom := {l | l ∈ s.dom ∧ l ∈ t.dom}
  nonempty_input := by
    intro hdom
    exact s.nonempty_input hdom.1
  prefix_closed := by
    intro l₁ l₂ hprefix hnonempty hdom
    exact ⟨s.prefix_closed hprefix hnonempty hdom.1,
      t.prefix_closed hprefix hnonempty hdom.2⟩
  respond := fun l h => op (s.respond l h.1) (t.respond l h.2)

/-- CR18 Definition 3.12: output characterization for output-combine. -/
@[simp]
theorem outputCombine_output (op : Y → Y → Y) (s t : DDS X Y) (l : List X)
    (h : l ∈ (outputCombine op s t).dom) :
    (outputCombine op s t).output l h = op (s.output l h.1) (t.output l h.2) := by
  rfl

/-- CR18 Definition 3.12: domain characterization for output-combine. -/
theorem outputCombine_dom (op : Y → Y → Y) (s t : DDS X Y) (l : List X) :
    l ∈ (outputCombine op s t).dom ↔ l ∈ s.dom ∧ l ∈ t.dom := by
  rfl

/-- CR18 Definition 3.11 / casc converter (item P2): left projection of the
single parallel-access history used by `casc`.

This is the `s`-side history in the source prose immediately after Definition
3.11, where the converter `casc` has parallel access to `s` and `t` and is
specified by the equation `casc[s,t] = s ⊲ t`. -/
def cascLeftHistory (l : List (Sum X Y)) : List X :=
  l.filterMap fun q =>
    match q with
    | Sum.inl x => some x
    | Sum.inr _ => none

/-- CR18 Definition 3.11 / casc converter (item P2): right projection of the
single parallel-access history used by `casc`.

This is the `t`-side history in the source prose immediately after Definition
3.11, where the converter `casc` has parallel access to `s` and `t` and is
specified by the equation `casc[s,t] = s ⊲ t`. -/
def cascRightHistory (l : List (Sum X Y)) : List Y :=
  l.filterMap fun q =>
    match q with
    | Sum.inl _ => none
    | Sum.inr y => some y

/-- CR18 Definition 3.11 / casc converter (item P2): the local domain
condition imposed by the most recent query in one parallel-access history. -/
def cascParallelStep (s : DDS X Y) (t : DDS Y Z) (p : List (Sum X Y)) : Prop :=
  match p.getLast? with
  | some (Sum.inl _) => cascLeftHistory p ∈ s.dom
  | some (Sum.inr _) => cascRightHistory p ∈ t.dom
  | none => False

/-- CR18 Definition 3.11 / casc converter (item P2): the single inner DDS that
models parallel access to `s` and `t` for the converter `casc`.

The left summand queries `s`; the right summand queries `t`. This packages the
source's prose-only "parallel access to `s` and `t`" into one inner system for
the converter equation `casc[s,t] = s ⊲ t`. -/
noncomputable def cascParallel (s : DDS X Y) (t : DDS Y Z) :
    DDS (Sum X Y) (Sum Y Z) where
  dom := {l | l ≠ [] ∧ ∀ p, p ≠ [] → p <+: l → cascParallelStep s t p}
  nonempty_input := by
    intro h
    exact h.1 rfl
  prefix_closed := by
    intro l₁ l₂ hprefix hnonempty hdom
    refine ⟨hnonempty, ?_⟩
    intro p hpne hpprefix
    exact hdom.2 p hpne (List.IsPrefix.trans hpprefix hprefix)
  respond := fun l h =>
    match hlast : l.getLast? with
    | none => absurd (List.getLast?_eq_none_iff.mp hlast) h.1
    | some (Sum.inl _) =>
        Sum.inl (s.respond (cascLeftHistory l) (by
          simpa [cascParallelStep, hlast] using h.2 l h.1 (List.prefix_refl l)))
    | some (Sum.inr _) =>
        Sum.inr (t.respond (cascRightHistory l) (by
          simpa [cascParallelStep, hlast] using h.2 l h.1 (List.prefix_refl l)))

/-- CR18 Definition 3.11 / casc converter (item P2): the operational output of
the generic converter `casc` on its converter-side history.

One outside input `x` first produces an inner call to the `s` component. A
response `y` from that component produces an inner call to the `t` component.
A response `z` from that component produces the outside output `z`. Complete
rounds may then be followed by the next outside input. This records the
source equation `casc[s,t] = s ⊲ t` at the converter-orchestration layer. -/
def cascConverterOutput? :
    List (ConverterInput X (Sum Y Z)) →
      Option (ConverterOutput Z (Sum X Y))
  | [] => none
  | Sum.inl x :: rest =>
      match rest with
      | [] => some (ConverterOutput.inn (Sum.inl x))
      | Sum.inr (some (Sum.inl y)) :: rest' =>
          match rest' with
          | [] => some (ConverterOutput.inn (Sum.inr y))
          | Sum.inr (some (Sum.inr z)) :: rest'' =>
              match rest'' with
              | [] => some (ConverterOutput.out z)
              | Sum.inl _ :: _ => cascConverterOutput? rest''
              | _ => none
          | _ => none
      | _ => none
  | _ => none

/-- CR18 Definition 3.11 / casc converter (item P2): the accepted converter
histories of `casc` are closed under nonempty prefixes.

Every accepted history is a sequence of complete `x, y, z` rounds followed by a
partial round, and truncating such a history yields a history of the same
shape. Proved by the functional induction of the defining equation
`cascConverterOutput?`. -/
theorem cascConverterOutput?_isSome_of_prefix :
    ∀ {l₂ l₁ : List (ConverterInput X (Sum Y Z))}, l₁ <+: l₂ → l₁ ≠ [] →
      (cascConverterOutput? l₂).isSome → (cascConverterOutput? l₁).isSome := by
  intro l₂
  induction l₂ using cascConverterOutput?.induct with
  | case1 =>
      intro l₁ hpre hne _
      exact absurd (List.prefix_nil.mp hpre) hne
  | case2 x =>
      intro l₁ hpre hne _
      rcases List.prefix_cons_iff.mp hpre with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · obtain rfl := List.prefix_nil.mp ht
        simp [cascConverterOutput?]
  | case3 x y =>
      intro l₁ hpre hne _
      rcases List.prefix_cons_iff.mp hpre with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [cascConverterOutput?]
        · obtain rfl := List.prefix_nil.mp ht'
          simp [cascConverterOutput?]
  | case4 x y z =>
      intro l₁ hpre hne _
      rcases List.prefix_cons_iff.mp hpre with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [cascConverterOutput?]
        · rcases List.prefix_cons_iff.mp ht' with rfl | ⟨t'', rfl, ht''⟩
          · simp [cascConverterOutput?]
          · obtain rfl := List.prefix_nil.mp ht''
            simp [cascConverterOutput?]
  | case5 x y z val tail ih =>
      intro l₁ hpre hne h₂
      simp only [cascConverterOutput?] at h₂
      rcases List.prefix_cons_iff.mp hpre with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [cascConverterOutput?]
        · rcases List.prefix_cons_iff.mp ht' with rfl | ⟨t'', rfl, ht''⟩
          · simp [cascConverterOutput?]
          · rcases List.prefix_cons_iff.mp ht'' with rfl | ⟨t''', rfl, ht'''⟩
            · simp [cascConverterOutput?]
            · have := ih (l₁ := Sum.inl val :: t''')
                (List.cons_prefix_cons.mpr ⟨rfl, ht'''⟩) (List.cons_ne_nil _ _) h₂
              simpa [cascConverterOutput?] using this
  | case6 x y z rest'' hnil hinl =>
      intro l₁ hpre hne h₂
      rcases rest'' with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [cascConverterOutput?] at h₂
  | case7 x y rest' hnil hrz =>
      intro l₁ hpre hne h₂
      rcases rest' with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [cascConverterOutput?] at h₂
      · simp [cascConverterOutput?] at h₂
      · simp [cascConverterOutput?] at h₂
      · exact (hrz z' tail rfl).elim
  | case8 x rest hnil hry =>
      intro l₁ hpre hne h₂
      rcases rest with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [cascConverterOutput?] at h₂
      · simp [cascConverterOutput?] at h₂
      · exact (hry y' tail rfl).elim
      · simp [cascConverterOutput?] at h₂
  | case9 t hnil hinl =>
      intro l₁ hpre hne h₂
      rcases t with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [cascConverterOutput?] at h₂

/-- CR18 Definition 3.11 / casc converter (item P2): an inner-call (`inn`)
output of `casc` occurs exactly at converter-history lengths that are not
multiples of three.

Within each `x, y, z` round of `casc[s,t] = s ⊲ t`, positions `1` and `2`
(mod `3`) are the inner calls to `s` and `t`, and position `0` (mod `3`) is the
outside output. Only the direction needed for the inner-call bound is
recorded. -/
theorem cascConverterOutput?_inn_length {x : Sum X Y} :
    ∀ {l : List (ConverterInput X (Sum Y Z))},
      cascConverterOutput? l = some (ConverterOutput.inn x) →
      l.length % 3 ≠ 0 := by
  intro l
  induction l using cascConverterOutput?.induct with
  | case1 => intro h; simp [cascConverterOutput?] at h
  | case2 x' => intro _; simp
  | case3 x' y => intro _; simp
  | case4 x' y z => intro h; simp [cascConverterOutput?] at h
  | case5 x' y z val tail ih =>
      intro h
      simp only [cascConverterOutput?] at h
      have := ih h
      simp only [List.length_cons] at this ⊢
      omega
  | case6 x' y z rest'' hnil hinl =>
      intro h
      rcases rest'' with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [cascConverterOutput?] at h
  | case7 x' y rest' hnil hrz =>
      intro h
      rcases rest' with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · exact (hrz z' tail rfl).elim
  | case8 x' rest hnil hry =>
      intro h
      rcases rest with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · exact (hry y' tail rfl).elim
      · simp [cascConverterOutput?] at h
  | case9 t hnil hinl =>
      intro h
      rcases t with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [cascConverterOutput?] at h

/-- CR18 Definition 3.11 / casc converter (item P2): after an `inn` output of
`casc`, the next accepted converter input is an inner-side response
`Sum.inr _`. This is the `input_after_inn` alphabet discipline of CR18
Definition 3.8 for the `casc` converter. -/
theorem cascConverterOutput?_append_inn {x : Sum X Y}
    {i : ConverterInput X (Sum Y Z)} :
    ∀ {l : List (ConverterInput X (Sum Y Z))},
      cascConverterOutput? l = some (ConverterOutput.inn x) →
      (cascConverterOutput? (l ++ [i])).isSome →
      ∃ y : Option (Sum Y Z), i = Sum.inr y := by
  intro l
  induction l using cascConverterOutput?.induct with
  | case1 => intro h _; simp [cascConverterOutput?] at h
  | case2 x' =>
      intro _ hnext
      rcases i with u | y
      · simp [cascConverterOutput?] at hnext
      · exact ⟨y, rfl⟩
  | case3 x' y =>
      intro _ hnext
      rcases i with u | y'
      · simp [cascConverterOutput?] at hnext
      · exact ⟨y', rfl⟩
  | case4 x' y z => intro h _; simp [cascConverterOutput?] at h
  | case5 x' y z val tail ih =>
      intro h hnext
      simp only [cascConverterOutput?] at h
      simp only [List.cons_append, cascConverterOutput?] at hnext
      exact ih h hnext
  | case6 x' y z rest'' hnil hinl =>
      intro h _
      rcases rest'' with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [cascConverterOutput?] at h
  | case7 x' y rest' hnil hrz =>
      intro h _
      rcases rest' with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · exact (hrz z' tail rfl).elim
  | case8 x' rest hnil hry =>
      intro h _
      rcases rest with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · exact (hry y' tail rfl).elim
      · simp [cascConverterOutput?] at h
  | case9 t hnil hinl =>
      intro h _
      rcases t with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [cascConverterOutput?] at h

/-- CR18 Definition 3.11 / casc converter (item P2): after an `out` output of
`casc`, the next accepted converter input is an outside input `Sum.inl _`.
This is the `input_after_out` alphabet discipline of CR18 Definition 3.8 for
the `casc` converter. -/
theorem cascConverterOutput?_append_out {z₀ : Z}
    {i : ConverterInput X (Sum Y Z)} :
    ∀ {l : List (ConverterInput X (Sum Y Z))},
      cascConverterOutput? l = some (ConverterOutput.out z₀) →
      (cascConverterOutput? (l ++ [i])).isSome →
      ∃ u : X, i = Sum.inl u := by
  intro l
  induction l using cascConverterOutput?.induct with
  | case1 => intro h _; simp [cascConverterOutput?] at h
  | case2 x' => intro h _; simp [cascConverterOutput?] at h
  | case3 x' y => intro h _; simp [cascConverterOutput?] at h
  | case4 x' y z =>
      intro _ hnext
      rcases i with u | y'
      · exact ⟨u, rfl⟩
      · simp [cascConverterOutput?] at hnext
  | case5 x' y z val tail ih =>
      intro h hnext
      simp only [cascConverterOutput?] at h
      simp only [List.cons_append, cascConverterOutput?] at hnext
      exact ih h hnext
  | case6 x' y z rest'' hnil hinl =>
      intro h _
      rcases rest'' with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [cascConverterOutput?] at h
  | case7 x' y rest' hnil hrz =>
      intro h _
      rcases rest' with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · exact (hrz z' tail rfl).elim
  | case8 x' rest hnil hry =>
      intro h _
      rcases rest with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [cascConverterOutput?] at h
      · simp [cascConverterOutput?] at h
      · exact (hry y' tail rfl).elim
      · simp [cascConverterOutput?] at h
  | case9 t hnil hinl =>
      intro h _
      rcases t with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [cascConverterOutput?] at h

/-- CR18 Definition 3.8: the head history of a nonempty run of consecutive
inner calls has an inner-call output. Inversion helper for
`bounded_inner_calls` obligations. -/
theorem isInnerCallOutput_of_innerCallRun_cons {U V X' Y' : Type*}
    {s : DDS (ConverterInput U Y') (ConverterOutput V X')}
    {l : List (ConverterInput U Y')} {rest : List (List (ConverterInput U Y'))}
    (h : InnerCallRun s (l :: rest)) : IsInnerCallOutput s l := by
  cases h with
  | singleton h => exact h
  | cons h _ _ => exact h

/-- CR18 Definition 3.11 / casc converter (item P2): the converter `casc`.

The converter has outside alphabet `X`, outside output alphabet `Z`, and inner
access to a single parallel DDS with input alphabet `X + Y` and output alphabet
`Y + Z`. It implements the prose equation `casc[s,t] = s ⊲ t` by querying the
left component on `x`, querying the right component on the resulting `y`, and
then outputting the resulting `z`.

All Definition 3.8 obligations are read off the defining equation
`cascConverterOutput?`: the response is the equationally determined
`(cascConverterOutput? l).get _`, prefix closure and the alphabet discipline
are the `cascConverterOutput?_*` lemmas above, and the inner-call bound `2`
holds because inner calls occur only at history lengths `1` and `2` modulo
`3`, so no three consecutive histories can all be inner calls. -/
noncomputable def cascConverter : DDC X Z (Sum X Y) (Sum Y Z) where
  system := {
    dom := {l | (cascConverterOutput? l).isSome}
    nonempty_input := by
      simp [cascConverterOutput?]
    prefix_closed := fun hpre hne h₂ =>
      cascConverterOutput?_isSome_of_prefix hpre hne h₂
    respond := fun l h => (cascConverterOutput? l).get h
  }
  starts_with_U := by
    intro i rest h
    rcases i with u | y
    · exact ⟨u, rfl⟩
    · simp [cascConverterOutput?] at h
  input_after_inn := by
    intro l h x i hresp hnext
    have hsome : (cascConverterOutput? l).isSome := h
    have hf : cascConverterOutput? l = some (ConverterOutput.inn x) :=
      (Option.some_get hsome).symm.trans (congrArg some hresp)
    exact cascConverterOutput?_append_inn hf hnext
  input_after_out := by
    intro l h v' i hresp hnext
    have hsome : (cascConverterOutput? l).isSome := h
    have hf : cascConverterOutput? l = some (ConverterOutput.out v') :=
      (Option.some_get hsome).symm.trans (congrArg some hresp)
    exact cascConverterOutput?_append_out hf hnext
  innerCallBound := 2
  bounded_inner_calls := by
    intro run hrun
    cases hrun with
    | nil => simp
    | singleton _ => simp
    | cons h₁ hext hrest =>
      cases hrest with
      | singleton _ => simp
      | cons h₂ hext₂ hrest₂ =>
        exfalso
        have key : ∀ {l : List (ConverterInput X (Sum Y Z))}
            (h : (cascConverterOutput? l).isSome)
            {o : ConverterOutput Z (Sum X Y)},
            (cascConverterOutput? l).get h = o →
              cascConverterOutput? l = some o := by
          intro l h o hget
          rw [← hget, Option.some_get]
        obtain ⟨hdom₁, x₁, hx₁⟩ := h₁
        have hn₁ := cascConverterOutput?_inn_length (key hdom₁ hx₁)
        obtain ⟨i₁, rfl⟩ := hext
        obtain ⟨hdom₂, x₂, hx₂⟩ := h₂
        have hn₂ := cascConverterOutput?_inn_length (key hdom₂ hx₂)
        obtain ⟨i₂, rfl⟩ := hext₂
        obtain ⟨hdom₃, x₃, hx₃⟩ :=
          isInnerCallOutput_of_innerCallRun_cons hrest₂
        have hn₃ := cascConverterOutput?_inn_length (key hdom₃ hx₃)
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hn₁ hn₂ hn₃
        omega

/-- CR18 Definition 3.11 / casc converter (item P2): decidable converter
domain for the generic `casc` converter.

This instance lets `DDC.apply` attach `casc` to the single parallel-access DDS
used to state the source equation `casc[s,t] = s ⊲ t`. -/
instance cascConverterSystemDomDecidable :
    DecidablePred (fun l => l ∈ (cascConverter : DDC X Z (Sum X Y) (Sum Y Z)).system.dom) := by
  intro l
  dsimp [cascConverter]
  infer_instance

/-- CR18 Definition 3.11 / casc converter (item P2): decidable domain for the
single parallel-access DDS used by `casc`.

Assuming decidable domains for `s` and `t`, this instance lets `DDC.apply`
form the left side of the source equation `casc[s,t] = s ⊲ t`. -/
instance cascParallelDomDecidable (s : DDS X Y) (t : DDS Y Z)
    [DecidablePred (fun l => l ∈ s.dom)]
    [DecidablePred (fun l => l ∈ t.dom)] :
    DecidablePred (fun l => l ∈ (cascParallel s t).dom) := by
  intro l
  letI : DecidablePred (cascParallelStep s t) := by
    intro p
    dsimp [cascParallelStep]
    cases p.getLast? with
    | none =>
        infer_instance
    | some q =>
        cases q <;> infer_instance
  dsimp [cascParallel]
  refine decidable_of_iff
    (l ≠ [] ∧ ∀ p ∈ l.inits, p ≠ [] → cascParallelStep s t p) ?_
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro p hpne hp
    exact h.2 p ((List.mem_inits p l).mpr hp) hpne
  · intro h
    refine ⟨h.1, ?_⟩
    intro p hp hpne
    exact h.2 p hpne ((List.mem_inits p l).mp hp)

/-- CR18 Definition 3.3 / 3.9 helper: the deletion pass of `DDS.fullyDefined`
keeps an in-domain (or empty) history unchanged, because every nonempty prefix
of an in-domain history is again in the domain. -/
theorem keptPrefix_eq_self {X' Y' : Type*} (s' : DDS X' Y')
    [DecidablePred (fun l => l ∈ s'.dom)] {l : List X'}
    (hl : l = [] ∨ l ∈ s'.dom) : keptPrefix s' l = l := by
  rcases hl with rfl | hl
  · rfl
  · suffices haux : ∀ (suf acc : List X'), acc ++ suf = l →
        List.foldl (fun acc x => if acc ++ [x] ∈ s'.dom then acc ++ [x] else acc)
          acc suf = l by
      simpa [keptPrefix] using haux l [] rfl
    intro suf
    induction suf with
    | nil => intro acc hacc; simpa using hacc
    | cons x xs ihx =>
        intro acc hacc
        have hpre : acc ++ [x] ∈ s'.dom := by
          refine s'.prefix_closed ⟨xs, ?_⟩ (by simp) hl
          simpa using hacc
        simp only [List.foldl_cons, if_pos hpre]
        exact ihx (acc ++ [x]) (by simpa using hacc)

/-- CR18 Definition 3.9 helper: querying the fully defined completion of an
inner DDS on an in-domain one-step extension returns the original response. -/
theorem completedInnerResponse_of_dom {X' Y' : Type*} (s' : DDS X' Y')
    [DecidablePred (fun l => l ∈ s'.dom)] (it : List X') (x : X')
    (hit : it = [] ∨ it ∈ s'.dom) (hcand : it ++ [x] ∈ s'.dom) :
    DDC.completedInnerResponse s' it x = some (s'.respond (it ++ [x]) hcand) := by
  unfold DDC.completedInnerResponse
  show (fullyDefined s').respond (it ++ [x]) (by simp [fullyDefined]) = _
  simp only [fullyDefined, List.dropLast_concat, keptPrefix_eq_self s' hit,
    List.getLast_concat]
  rw [dif_pos hcand]

/-- CR18 Definition 3.11 / casc converter (item P2): one-step domain extension
for the parallel-access DDS, in equational snoc form. The whole extended
history is accepted as soon as the previous history was (or was empty) and the
local step condition holds for the new last query. -/
theorem cascParallel_dom_snoc (s : DDS X Y) (t : DDS Y Z)
    {p : List (Sum X Y)} {a : Sum X Y}
    (hp : p = [] ∨ p ∈ (cascParallel s t).dom)
    (hstep : cascParallelStep s t (p ++ [a])) :
    p ++ [a] ∈ (cascParallel s t).dom := by
  refine ⟨by simp, ?_⟩
  intro q hqne hqpre
  rcases List.prefix_concat_iff.mp hqpre with hq | hq
  · subst hq; exact hstep
  · rcases hp with rfl | hp
    · exact absurd (List.prefix_nil.mp hq) hqne
    · exact hp.2 q hqne hq

/-- CR18 Definition 3.11 / casc converter (item P2): defining-equation form of
the parallel-access response when the most recent query is on the `s` side. -/
theorem cascParallel_respond_inl (s : DDS X Y) (t : DDS Y Z)
    {p : List (Sum X Y)} (h : p ∈ (cascParallel s t).dom) {x : X}
    (hlast : p.getLast? = some (Sum.inl x))
    (hL : cascLeftHistory p ∈ s.dom) :
    (cascParallel s t).respond p h = Sum.inl (s.respond (cascLeftHistory p) hL) := by
  dsimp only [cascParallel]
  split <;> rename_i heq
  · rw [hlast] at heq; cases heq
  · rfl
  · rw [hlast] at heq; cases heq

/-- CR18 Definition 3.11 / casc converter (item P2): defining-equation form of
the parallel-access response when the most recent query is on the `t` side. -/
theorem cascParallel_respond_inr (s : DDS X Y) (t : DDS Y Z)
    {p : List (Sum X Y)} (h : p ∈ (cascParallel s t).dom) {y : Y}
    (hlast : p.getLast? = some (Sum.inr y))
    (hR : cascRightHistory p ∈ t.dom) :
    (cascParallel s t).respond p h = Sum.inr (t.respond (cascRightHistory p) hR) := by
  dsimp only [cascParallel]
  split <;> rename_i heq
  · rw [hlast] at heq; cases heq
  · rw [hlast] at heq; cases heq
  · rfl

/-- CR18 Definition 3.11 / casc converter (item P2): the converter-side trace
of a list of complete `x, y, z` rounds of `casc[s,t]`, in defining-equation
form. Each round contributes the outside input `x`, the `s`-side response `y`,
and the `t`-side response `z`. -/
def cascRoundsTrace : List (X × Y × Z) → List (ConverterInput X (Sum Y Z))
  | [] => []
  | (x, y, z) :: r =>
      Sum.inl x :: Sum.inr (some (Sum.inl y)) :: Sum.inr (some (Sum.inr z)) ::
        cascRoundsTrace r

/-- CR18 Definition 3.11 / casc converter (item P2): the inner-side
(parallel-access) trace of a list of complete `x, y, z` rounds of
`casc[s,t]`. Each round contributes the `s`-side query `x` and the `t`-side
query `y`. -/
def cascRoundsInner : List (X × Y × Z) → List (Sum X Y)
  | [] => []
  | (x, y, _) :: r => Sum.inl x :: Sum.inr y :: cascRoundsInner r

/-- item P2 helper: the rounds converter trace is a list homomorphism. -/
theorem cascRoundsTrace_append (r r' : List (X × Y × Z)) :
    cascRoundsTrace (X := X) (Y := Y) (Z := Z) (r ++ r') =
      cascRoundsTrace r ++ cascRoundsTrace r' := by
  induction r with
  | nil => simp [cascRoundsTrace]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      simp [cascRoundsTrace, ih]

/-- item P2 helper: the rounds inner trace is a list homomorphism. -/
theorem cascRoundsInner_append (r r' : List (X × Y × Z)) :
    cascRoundsInner (X := X) (Y := Y) (Z := Z) (r ++ r') =
      cascRoundsInner r ++ cascRoundsInner r' := by
  induction r with
  | nil => simp [cascRoundsInner]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      simp [cascRoundsInner, ih]

/-- item P2 helper: the left projection is a list homomorphism. -/
theorem cascLeftHistory_append (l₁ l₂ : List (Sum X Y)) :
    cascLeftHistory (l₁ ++ l₂) = cascLeftHistory l₁ ++ cascLeftHistory l₂ :=
  List.filterMap_append

/-- item P2 helper: the right projection is a list homomorphism. -/
theorem cascRightHistory_append (l₁ l₂ : List (Sum X Y)) :
    cascRightHistory (l₁ ++ l₂) = cascRightHistory l₁ ++ cascRightHistory l₂ :=
  List.filterMap_append

/-- item P2 helper: the left projection of the rounds inner trace recovers the
outside inputs of the rounds. -/
theorem cascLeftHistory_roundsInner (r : List (X × Y × Z)) :
    cascLeftHistory (cascRoundsInner r) = r.map (fun p => p.1) := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      show cascLeftHistory ([Sum.inl a, Sum.inr b] ++ cascRoundsInner r) = _
      rw [cascLeftHistory_append, ih]
      rfl

/-- item P2 helper: the right projection of the rounds inner trace recovers
the `s`-side responses of the rounds. -/
theorem cascRightHistory_roundsInner (r : List (X × Y × Z)) :
    cascRightHistory (cascRoundsInner r) = r.map (fun p => p.2.1) := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      show cascRightHistory ([Sum.inl a, Sum.inr b] ++ cascRoundsInner r) = _
      rw [cascRightHistory_append, ih]
      rfl

/-- item P2 helper: the defining equation `cascConverterOutput?` consumes any
number of complete `x, y, z` rounds before a trace whose first entry is an
outside input. -/
theorem cascConverterOutput?_roundsTrace_append (r : List (X × Y × Z))
    {x : X} {tail : List (ConverterInput X (Sum Y Z))}
    (htail : tail.head? = some (Sum.inl x)) :
    cascConverterOutput? (cascRoundsTrace r ++ tail) = cascConverterOutput? tail := by
  induction r with
  | nil => simp [cascRoundsTrace]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      obtain ⟨x', rest', heq⟩ : ∃ (x' : X) (rest' : List (ConverterInput X (Sum Y Z))),
          cascRoundsTrace r ++ tail = Sum.inl x' :: rest' := by
        cases r with
        | nil =>
            cases tail with
            | nil => simp at htail
            | cons i tl =>
                have hi : i = Sum.inl x := by simpa using htail
                exact ⟨x, tl, by simp [cascRoundsTrace, hi]⟩
        | cons q r' =>
            obtain ⟨a', b', c'⟩ := q
            exact ⟨a', Sum.inr (some (Sum.inl b')) :: Sum.inr (some (Sum.inr c')) ::
              (cascRoundsTrace r' ++ tail), by simp [cascRoundsTrace]⟩
      rw [show cascRoundsTrace ((a, b, c) :: r) ++ tail
          = Sum.inl a :: Sum.inr (some (Sum.inl b)) :: Sum.inr (some (Sum.inr c)) ::
            (cascRoundsTrace r ++ tail) from by simp [cascRoundsTrace], heq]
      rw [show cascConverterOutput? (Sum.inl a :: Sum.inr (some (Sum.inl b)) ::
            Sum.inr (some (Sum.inr c)) :: Sum.inl x' :: rest')
          = cascConverterOutput? (Sum.inl x' :: rest') from by
        simp [cascConverterOutput?]]
      rw [← heq]
      exact ih

/-- item P2 helper: one complete `x, y, z` round of the operational driver for
`casc[s,t]`, in defining-equation form. Starting from any number of complete
rounds, an outside input `x` triggers the inner call to `s` (answered by `y`),
then the inner call to `t` (answered by `z`), and the driver returns `z` with
the round completed on both traces. -/
theorem runConverter_cascRound (s : DDS X Y) (t : DDS Y Z)
    [DecidablePred (fun l => l ∈ s.dom)] [DecidablePred (fun l => l ∈ t.dom)]
    (r : List (X × Y × Z)) (x : X) (y : Y) (z : Z)
    (hit : cascRoundsInner r = [] ∨ cascRoundsInner r ∈ (cascParallel s t).dom)
    (hL : r.map (fun p => p.1) ++ [x] ∈ s.dom)
    (hLy : s.respond (r.map (fun p => p.1) ++ [x]) hL = y)
    (hR : r.map (fun p => p.2.1) ++ [y] ∈ t.dom)
    (hRz : t.respond (r.map (fun p => p.2.1) ++ [y]) hR = z) :
    cascRoundsInner (r ++ [(x, y, z)]) ∈ (cascParallel s t).dom ∧
      DDC.runConverter (cascConverter : DDC X Z (Sum X Y) (Sum Y Z))
          (cascParallel s t) 2 (cascRoundsTrace r ++ [Sum.inl x]) (cascRoundsInner r) =
        some (cascRoundsTrace (r ++ [(x, y, z)]), cascRoundsInner (r ++ [(x, y, z)]), z) := by
  -- the `s`-side extension of the inner trace
  have hLproj : cascLeftHistory (cascRoundsInner r ++ [Sum.inl x])
      = r.map (fun p => p.1) ++ [x] := by
    rw [cascLeftHistory_append, cascLeftHistory_roundsInner]
    rfl
  have hLmem : cascLeftHistory (cascRoundsInner r ++ [Sum.inl x]) ∈ s.dom := by
    rw [hLproj]; exact hL
  have hstep1 : cascParallelStep s t (cascRoundsInner r ++ [Sum.inl x]) := by
    have hgl : (cascRoundsInner r ++ [Sum.inl x]).getLast? = some (Sum.inl x) :=
      List.getLast?_concat
    simp only [cascParallelStep, hgl]
    exact hLmem
  have hit1 : cascRoundsInner r ++ [Sum.inl x] ∈ (cascParallel s t).dom :=
    cascParallel_dom_snoc s t hit hstep1
  have hresp1 : (cascParallel s t).respond (cascRoundsInner r ++ [Sum.inl x]) hit1
      = Sum.inl y := by
    rw [cascParallel_respond_inl s t hit1 List.getLast?_concat hLmem]
    exact congrArg Sum.inl ((s.respond_congr hLproj hLmem hL).trans hLy)
  -- the `t`-side extension of the inner trace
  have hRproj : cascRightHistory ((cascRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr y])
      = r.map (fun p => p.2.1) ++ [y] := by
    rw [cascRightHistory_append, cascRightHistory_append, cascRightHistory_roundsInner]
    simp [cascRightHistory]
  have hRmem : cascRightHistory ((cascRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr y]) ∈ t.dom := by
    rw [hRproj]; exact hR
  have hstep2 : cascParallelStep s t ((cascRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr y]) := by
    have hgl : ((cascRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr (y : Y)]).getLast?
        = some (Sum.inr y) := List.getLast?_concat
    simp only [cascParallelStep, hgl]
    exact hRmem
  have hit2 : (cascRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr y] ∈ (cascParallel s t).dom :=
    cascParallel_dom_snoc s t (Or.inr hit1) hstep2
  have hresp2 : (cascParallel s t).respond
      ((cascRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr y]) hit2 = Sum.inr z := by
    rw [cascParallel_respond_inr s t hit2 List.getLast?_concat hRmem]
    exact congrArg Sum.inr ((t.respond_congr hRproj hRmem hR).trans hRz)
  -- the completed inner responses queried by the driver
  have hcir1 : DDC.completedInnerResponse (cascParallel s t) (cascRoundsInner r) (Sum.inl x)
      = some (Sum.inl y) := by
    rw [completedInnerResponse_of_dom (cascParallel s t) _ _ hit hit1, hresp1]
  have hcir2 : DDC.completedInnerResponse (cascParallel s t)
      (cascRoundsInner r ++ [Sum.inl x]) (Sum.inr y) = some (Sum.inr z) := by
    rw [completedInnerResponse_of_dom (cascParallel s t) _ _ (Or.inr hit1) hit2, hresp2]
  -- the three converter-trace defining equations of the round
  have hct1 : cascConverterOutput? (cascRoundsTrace r ++ [Sum.inl x])
      = some (ConverterOutput.inn (Sum.inl x)) := by
    rw [cascConverterOutput?_roundsTrace_append r rfl]
    simp [cascConverterOutput?]
  have hct2 : cascConverterOutput?
      (cascRoundsTrace r ++ [Sum.inl x, Sum.inr (some (Sum.inl y))])
      = some (ConverterOutput.inn (Sum.inr y)) := by
    rw [cascConverterOutput?_roundsTrace_append r rfl]
    simp [cascConverterOutput?]
  have hct3 : cascConverterOutput? (cascRoundsTrace r ++
        [Sum.inl x, Sum.inr (some (Sum.inl y)), Sum.inr (some (Sum.inr z))])
      = some (ConverterOutput.out z) := by
    rw [cascConverterOutput?_roundsTrace_append r rfl]
    simp [cascConverterOutput?]
  have hdom1 : cascRoundsTrace r ++ [Sum.inl x]
      ∈ (cascConverter : DDC X Z (Sum X Y) (Sum Y Z)).system.dom := by
    show (cascConverterOutput? _).isSome
    simp [hct1]
  have hrespC1 : (cascConverter : DDC X Z (Sum X Y) (Sum Y Z)).system.respond
      (cascRoundsTrace r ++ [Sum.inl x]) hdom1 = ConverterOutput.inn (Sum.inl x) := by
    show (cascConverterOutput? _).get _ = _
    simp [hct1]
  have hdom2 : cascRoundsTrace r ++ [Sum.inl x, Sum.inr (some (Sum.inl y))]
      ∈ (cascConverter : DDC X Z (Sum X Y) (Sum Y Z)).system.dom := by
    show (cascConverterOutput? _).isSome
    simp [hct2]
  have hrespC2 : (cascConverter : DDC X Z (Sum X Y) (Sum Y Z)).system.respond
      (cascRoundsTrace r ++ [Sum.inl x, Sum.inr (some (Sum.inl y))]) hdom2
      = ConverterOutput.inn (Sum.inr y) := by
    show (cascConverterOutput? _).get _ = _
    simp [hct2]
  have hdom3 : cascRoundsTrace r ++
        [Sum.inl x, Sum.inr (some (Sum.inl y)), Sum.inr (some (Sum.inr z))]
      ∈ (cascConverter : DDC X Z (Sum X Y) (Sum Y Z)).system.dom := by
    show (cascConverterOutput? _).isSome
    simp [hct3]
  have hrespC3 : (cascConverter : DDC X Z (Sum X Y) (Sum Y Z)).system.respond
      (cascRoundsTrace r ++
        [Sum.inl x, Sum.inr (some (Sum.inl y)), Sum.inr (some (Sum.inr z))]) hdom3
      = ConverterOutput.out z := by
    show (cascConverterOutput? _).get _ = _
    simp [hct3]
  refine ⟨?_, ?_⟩
  · simpa [cascRoundsInner_append, cascRoundsInner] using hit2
  · rw [DDC.runConverter_inn _ _ 1 _ _ hdom1 hrespC1, hcir1]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [DDC.runConverter_inn _ _ 0 _ _ hdom2 hrespC2, hcir2]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [DDC.runConverter_out _ _ 0 _ _ hdom3 hrespC3]
    simp [cascRoundsTrace_append, cascRoundsInner_append, cascRoundsTrace,
      cascRoundsInner]

/-- item P2 helper: the full driver invariant for `casc[s,t]`. After any number
of complete rounds consistent with `s` and `t`, processing the remaining
outside inputs succeeds and returns the last entry of the intermediate
`Z`-history of the cascade. -/
theorem applyTraceAux_cascRounds (s : DDS X Y) (t : DDS Y Z)
    [DecidablePred (fun l => l ∈ s.dom)] [DecidablePred (fun l => l ∈ t.dom)]
    (l : List X) (hs : l ∈ s.dom) (ht : yHistory s l hs ∈ t.dom) :
    ∀ (rest : List X) (k : ℕ) (r : List (X × Y × Z)),
      l.drop k = rest → rest ≠ [] →
      r.map (fun p => p.1) = l.take k →
      r.map (fun p => p.2.1) = (yHistory s l hs).take k →
      (cascRoundsInner r = [] ∨ cascRoundsInner r ∈ (cascParallel s t).dom) →
      ∃ ct' it',
        DDC.applyTraceAux (cascConverter : DDC X Z (Sum X Y) (Sum Y Z))
            (cascParallel s t) 2 rest (cascRoundsTrace r) (cascRoundsInner r) =
          some (ct', it',
            (yHistory t (yHistory s l hs) ht).getLast (yHistory_ne_nil t _ ht)) := by
  have hlne : l ≠ [] := fun hnil => s.nonempty_input (hnil ▸ hs)
  have hYne : yHistory s l hs ≠ [] := yHistory_ne_nil s l hs
  have hZne : yHistory t (yHistory s l hs) ht ≠ [] := yHistory_ne_nil t _ ht
  intro rest
  induction rest with
  | nil => intro k r _ hne _ _ _; exact absurd rfl hne
  | cons x rest' ih =>
      intro k r hdrop hne hm1 hm2 hit
      -- the position of the current outside input
      have hk : k < l.length := by
        by_contra hk'
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hk')] at hdrop
        cases hdrop
      have hxr : l[k] :: l.drop (k + 1) = x :: rest' := by
        rw [← List.drop_eq_getElem_cons hk, hdrop]
      have hx : l[k] = x := by injection hxr
      have hrest' : l.drop (k + 1) = rest' := by injection hxr
      have hkY : k < (yHistory s l hs).length := by
        rw [yHistory_length]; exact hk
      have hkZ : k < (yHistory t (yHistory s l hs) ht).length := by
        rw [yHistory_length]; exact hkY
      -- the canonical responses of `s` and `t` at this round
      have htakeL : l.take k ++ [l[k]] = l.take (k + 1) :=
        (List.take_succ_eq_append_getElem hk).symm
      have htakeY : (yHistory s l hs).take k ++ [(yHistory s l hs)[k]'hkY]
          = (yHistory s l hs).take (k + 1) :=
        (List.take_succ_eq_append_getElem hkY).symm
      have hLmem : l.take (k + 1) ∈ s.dom :=
        s.prefix_closed (List.take_prefix _ l)
          (by simp [List.take_eq_nil_iff, hlne]) hs
      have hYmem : (yHistory s l hs).take (k + 1) ∈ t.dom :=
        t.prefix_closed (List.take_prefix _ _)
          (by simp [List.take_eq_nil_iff, hYne]) ht
      have hmem1 : r.map (fun p => p.1) ++ [x] ∈ s.dom := by
        rw [hm1, ← hx, htakeL]; exact hLmem
      have hresp1 : s.respond (r.map (fun p => p.1) ++ [x]) hmem1
          = (yHistory s l hs)[k]'hkY := by
        rw [yHistory_getElem s l hs k hkY]
        exact s.respond_congr (by rw [hm1, ← hx, htakeL]) hmem1 _
      have hmem2 : r.map (fun p => p.2.1) ++ [(yHistory s l hs)[k]'hkY] ∈ t.dom := by
        rw [hm2, htakeY]; exact hYmem
      have hresp2 : t.respond (r.map (fun p => p.2.1) ++ [(yHistory s l hs)[k]'hkY]) hmem2
          = (yHistory t (yHistory s l hs) ht)[k]'hkZ := by
        rw [yHistory_getElem t (yHistory s l hs) ht k hkZ]
        exact t.respond_congr (by rw [hm2, htakeY]) hmem2 _
      have hround := runConverter_cascRound s t r x
        ((yHistory s l hs)[k]'hkY) ((yHistory t (yHistory s l hs) ht)[k]'hkZ)
        hit hmem1 hresp1 hmem2 hresp2
      cases rest' with
      | nil =>
          -- last round: the driver returns the last `Z`-history entry
          have hkn : k + 1 = l.length := by
            have hlen := congrArg List.length hrest'
            simp only [List.length_drop, List.length_nil] at hlen
            omega
          have hidx : k = (yHistory t (yHistory s l hs) ht).length - 1 := by
            rw [yHistory_length, yHistory_length]
            omega
          have hgl : (yHistory t (yHistory s l hs) ht)[k]'hkZ
              = (yHistory t (yHistory s l hs) ht).getLast hZne := by
            rw [List.getLast_eq_getElem]
            congr 1
          refine ⟨cascRoundsTrace (r ++ [(x, (yHistory s l hs)[k]'hkY,
              (yHistory t (yHistory s l hs) ht)[k]'hkZ)]),
            cascRoundsInner (r ++ [(x, (yHistory s l hs)[k]'hkY,
              (yHistory t (yHistory s l hs) ht)[k]'hkZ)]), ?_⟩
          unfold DDC.applyTraceAux
          rw [hround.2, ← hgl]
      | cons x2 rest'' =>
          -- recurse with one more completed round
          have hm1' : (r ++ [(x, (yHistory s l hs)[k]'hkY,
              (yHistory t (yHistory s l hs) ht)[k]'hkZ)]).map (fun p => p.1)
              = l.take (k + 1) := by
            rw [List.map_append, hm1]
            simp [← hx]
          have hm2' : (r ++ [(x, (yHistory s l hs)[k]'hkY,
              (yHistory t (yHistory s l hs) ht)[k]'hkZ)]).map (fun p => p.2.1)
              = (yHistory s l hs).take (k + 1) := by
            rw [List.map_append, hm2]
            simp
          obtain ⟨ct', it', hrun'⟩ := ih (k + 1)
            (r ++ [(x, (yHistory s l hs)[k]'hkY,
              (yHistory t (yHistory s l hs) ht)[k]'hkZ)])
            hrest' (by simp) hm1' hm2' (Or.inr hround.1)
          refine ⟨ct', it', ?_⟩
          unfold DDC.applyTraceAux
          rw [hround.2]
          exact hrun'

/-- CR18 Definition 3.11 / casc converter (item P2): output agreement
recording the prose-only defining equation `casc[s,t] = s ⊲ t`.

For every cascade history `l`, applying the generic `casc` converter to the
single parallel-access DDS for `s` and `t` has an output that agrees with the
already formalized cascade `(s ⊲ t)` on `l`. -/
theorem cascConverter_output_eq_cascade (s : DDS X Y) (t : DDS Y Z)
    [DecidablePred (fun l => l ∈ s.dom)]
    [DecidablePred (fun l => l ∈ t.dom)]
    (l : List X) (h : l ∈ (s ⊲ t).dom) :
    ∃ hcasc : l ∈ (DDC.apply (cascConverter : DDC X Z (Sum X Y) (Sum Y Z))
      (cascParallel s t)).dom,
      (DDC.apply (cascConverter : DDC X Z (Sum X Y) (Sum Y Z))
        (cascParallel s t)).output l hcasc = (s ⊲ t).output l h := by
  obtain ⟨hs, ht⟩ := (cascade_dom s t l).mp h
  have hlne : l ≠ [] := fun hnil => s.nonempty_input (hnil ▸ hs)
  have hYne : yHistory s l hs ≠ [] := yHistory_ne_nil s l hs
  have hZne : yHistory t (yHistory s l hs) ht ≠ [] := yHistory_ne_nil t _ ht
  -- run the driver invariant from the empty trace
  obtain ⟨ct', it', hrun⟩ :=
    applyTraceAux_cascRounds s t l hs ht l 0 [] (by simp) hlne (by simp) (by simp)
      (Or.inl rfl)
  have happly : DDC.applyTrace (cascConverter : DDC X Z (Sum X Y) (Sum Y Z))
      (cascParallel s t) l
      = some ((yHistory t (yHistory s l hs) ht).getLast hZne) := by
    unfold DDC.applyTrace
    have hbound : (cascConverter : DDC X Z (Sum X Y) (Sum Y Z)).innerCallBound = 2 := rfl
    rw [hbound]
    simp only [cascRoundsTrace, cascRoundsInner] at hrun
    rw [hrun]
    rfl
  refine ⟨⟨hlne, (yHistory t (yHistory s l hs) ht).getLast hZne, happly⟩, ?_⟩
  rw [DDC.apply_output_eq_of_applyTrace (cascConverter : DDC X Z (Sum X Y) (Sum Y Z))
    (cascParallel s t) l hlne happly]
  rw [cascade_output s t l h hs ht]
  -- the last `Z`-history entry is `t`'s response on the full intermediate history
  have hZpos : 0 < (yHistory t (yHistory s l hs) ht).length :=
    List.length_pos_iff.mpr hZne
  have hidx : (yHistory t (yHistory s l hs) ht).length - 1
      < (yHistory t (yHistory s l hs) ht).length := by omega
  rw [List.getLast_eq_getElem,
    yHistory_getElem t (yHistory s l hs) ht _ hidx]
  have htake : (yHistory s l hs).take
      ((yHistory t (yHistory s l hs) ht).length - 1 + 1) = yHistory s l hs := by
    have hlen : (yHistory t (yHistory s l hs) ht).length - 1 + 1
        = (yHistory s l hs).length := by
      have h1 : (yHistory t (yHistory s l hs) ht).length
          = (yHistory s l hs).length := yHistory_length t (yHistory s l hs) ht
      omega
    rw [hlen, List.take_length]
  exact t.respond_congr htake _ ht

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): left projection of the
single parallel-access history used by `comb⋆`.

This is the `s`-side history in the source prose immediately after Definition
3.12, where the converter `comb⋆` has parallel access to `s` and `t` and is
specified by the equation `comb⋆[s,t] = s ⋆ t`. -/
def combLeftHistory (l : List (Sum X X)) : List X :=
  l.filterMap fun q =>
    match q with
    | Sum.inl x => some x
    | Sum.inr _ => none

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): right projection of the
single parallel-access history used by `comb⋆`.

This is the `t`-side history in the source prose immediately after Definition
3.12, where the converter `comb⋆` has parallel access to `s` and `t` and is
specified by the equation `comb⋆[s,t] = s ⋆ t`. -/
def combRightHistory (l : List (Sum X X)) : List X :=
  l.filterMap fun q =>
    match q with
    | Sum.inl _ => none
    | Sum.inr x => some x

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): the local domain
condition imposed by the most recent query in one parallel-access history. -/
def combParallelStep (s t : DDS X Y) (p : List (Sum X X)) : Prop :=
  match p.getLast? with
  | some (Sum.inl _) => combLeftHistory p ∈ s.dom
  | some (Sum.inr _) => combRightHistory p ∈ t.dom
  | none => False

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): the single inner DDS that
models parallel access to `s` and `t` for the converter `comb⋆`.

The left summand queries `s`; the right summand queries `t`. This packages the
source's prose-only "parallel access to `s` and `t`" into one inner system for
the converter equation `comb⋆[s,t] = s ⋆ t`. -/
noncomputable def combParallel (s t : DDS X Y) :
    DDS (Sum X X) (Sum Y Y) where
  dom := {l | l ≠ [] ∧ ∀ p, p ≠ [] → p <+: l → combParallelStep s t p}
  nonempty_input := by
    intro h
    exact h.1 rfl
  prefix_closed := by
    intro l₁ l₂ hprefix hnonempty hdom
    refine ⟨hnonempty, ?_⟩
    intro p hpne hpprefix
    exact hdom.2 p hpne (List.IsPrefix.trans hpprefix hprefix)
  respond := fun l h =>
    match hlast : l.getLast? with
    | none => absurd (List.getLast?_eq_none_iff.mp hlast) h.1
    | some (Sum.inl _) =>
        Sum.inl (s.respond (combLeftHistory l) (by
          simpa [combParallelStep, hlast] using h.2 l h.1 (List.prefix_refl l)))
    | some (Sum.inr _) =>
        Sum.inr (t.respond (combRightHistory l) (by
          simpa [combParallelStep, hlast] using h.2 l h.1 (List.prefix_refl l)))

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): the operational output of
the generic converter `comb⋆` on its converter-side history.

One outside input `x` first produces an inner call to the `s` component. A
response `y₁` from that component produces an inner call to the `t` component
on the same outside input `x`. A response `y₂` from that component produces the
outside output `op y₁ y₂`. Complete rounds may then be followed by the next
outside input. This records the source equation `comb⋆[s,t] = s ⋆ t` at the
converter-orchestration layer. -/
def combConverterOutput? (op : Y → Y → Y) :
    List (ConverterInput X (Sum Y Y)) →
      Option (ConverterOutput Y (Sum X X))
  | [] => none
  | Sum.inl x :: rest =>
      match rest with
      | [] => some (ConverterOutput.inn (Sum.inl x))
      | Sum.inr (some (Sum.inl y₁)) :: rest' =>
          match rest' with
          | [] => some (ConverterOutput.inn (Sum.inr x))
          | Sum.inr (some (Sum.inr y₂)) :: rest'' =>
              match rest'' with
              | [] => some (ConverterOutput.out (op y₁ y₂))
              | Sum.inl _ :: _ => combConverterOutput? op rest''
              | _ => none
          | _ => none
      | _ => none
  | _ => none

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): the accepted converter
histories of `comb⋆` are closed under nonempty prefixes.

Every accepted history is a sequence of complete `x, y₁, y₂` rounds followed
by a partial round, and truncating such a history yields a history of the same
shape. Proved by the functional induction of the defining equation
`combConverterOutput?`. -/
theorem combConverterOutput?_isSome_of_prefix (op : Y → Y → Y) :
    ∀ {l₂ l₁ : List (ConverterInput X (Sum Y Y))}, l₁ <+: l₂ → l₁ ≠ [] →
      (combConverterOutput? op l₂).isSome →
      (combConverterOutput? op l₁).isSome := by
  intro l₂
  induction l₂ using combConverterOutput?.induct with
  | case1 =>
      intro l₁ hpre hne _
      exact absurd (List.prefix_nil.mp hpre) hne
  | case2 x =>
      intro l₁ hpre hne _
      rcases List.prefix_cons_iff.mp hpre with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · obtain rfl := List.prefix_nil.mp ht
        simp [combConverterOutput?]
  | case3 x y₁ =>
      intro l₁ hpre hne _
      rcases List.prefix_cons_iff.mp hpre with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [combConverterOutput?]
        · obtain rfl := List.prefix_nil.mp ht'
          simp [combConverterOutput?]
  | case4 x y₁ y₂ =>
      intro l₁ hpre hne _
      rcases List.prefix_cons_iff.mp hpre with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [combConverterOutput?]
        · rcases List.prefix_cons_iff.mp ht' with rfl | ⟨t'', rfl, ht''⟩
          · simp [combConverterOutput?]
          · obtain rfl := List.prefix_nil.mp ht''
            simp [combConverterOutput?]
  | case5 x y₁ y₂ val tail ih =>
      intro l₁ hpre hne h₂
      simp only [combConverterOutput?] at h₂
      rcases List.prefix_cons_iff.mp hpre with rfl | ⟨t, rfl, ht⟩
      · exact absurd rfl hne
      · rcases List.prefix_cons_iff.mp ht with rfl | ⟨t', rfl, ht'⟩
        · simp [combConverterOutput?]
        · rcases List.prefix_cons_iff.mp ht' with rfl | ⟨t'', rfl, ht''⟩
          · simp [combConverterOutput?]
          · rcases List.prefix_cons_iff.mp ht'' with rfl | ⟨t''', rfl, ht'''⟩
            · simp [combConverterOutput?]
            · have := ih (l₁ := Sum.inl val :: t''')
                (List.cons_prefix_cons.mpr ⟨rfl, ht'''⟩) (List.cons_ne_nil _ _) h₂
              simpa [combConverterOutput?] using this
  | case6 x y₁ y₂ rest'' hnil hinl =>
      intro l₁ hpre hne h₂
      rcases rest'' with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [combConverterOutput?] at h₂
  | case7 x y₁ rest' hnil hry₂ =>
      intro l₁ hpre hne h₂
      rcases rest' with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [combConverterOutput?] at h₂
      · simp [combConverterOutput?] at h₂
      · simp [combConverterOutput?] at h₂
      · exact (hry₂ z' tail rfl).elim
  | case8 x rest hnil hry₁ =>
      intro l₁ hpre hne h₂
      rcases rest with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [combConverterOutput?] at h₂
      · simp [combConverterOutput?] at h₂
      · exact (hry₁ y' tail rfl).elim
      · simp [combConverterOutput?] at h₂
  | case9 t hnil hinl =>
      intro l₁ hpre hne h₂
      rcases t with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [combConverterOutput?] at h₂

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): an inner-call (`inn`)
output of `comb⋆` occurs exactly at converter-history lengths that are not
multiples of three.

Within each `x, y₁, y₂` round of `comb⋆[s,t] = s ⋆ t`, positions `1` and `2`
(mod `3`) are the inner calls to `s` and `t`, and position `0` (mod `3`) is the
outside output. Only the direction needed for the inner-call bound is
recorded. -/
theorem combConverterOutput?_inn_length (op : Y → Y → Y) {x : Sum X X} :
    ∀ {l : List (ConverterInput X (Sum Y Y))},
      combConverterOutput? op l = some (ConverterOutput.inn x) →
      l.length % 3 ≠ 0 := by
  intro l
  induction l using combConverterOutput?.induct with
  | case1 => intro h; simp [combConverterOutput?] at h
  | case2 x' => intro _; simp
  | case3 x' y₁ => intro _; simp
  | case4 x' y₁ y₂ => intro h; simp [combConverterOutput?] at h
  | case5 x' y₁ y₂ val tail ih =>
      intro h
      simp only [combConverterOutput?] at h
      have := ih h
      simp only [List.length_cons] at this ⊢
      omega
  | case6 x' y₁ y₂ rest'' hnil hinl =>
      intro h
      rcases rest'' with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [combConverterOutput?] at h
  | case7 x' y₁ rest' hnil hry₂ =>
      intro h
      rcases rest' with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · exact (hry₂ z' tail rfl).elim
  | case8 x' rest hnil hry₁ =>
      intro h
      rcases rest with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · exact (hry₁ y' tail rfl).elim
      · simp [combConverterOutput?] at h
  | case9 t hnil hinl =>
      intro h
      rcases t with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [combConverterOutput?] at h

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): after an `inn` output of
`comb⋆`, the next accepted converter input is an inner-side response
`Sum.inr _`. This is the `input_after_inn` alphabet discipline of CR18
Definition 3.8 for the `comb⋆` converter. -/
theorem combConverterOutput?_append_inn (op : Y → Y → Y) {x : Sum X X}
    {i : ConverterInput X (Sum Y Y)} :
    ∀ {l : List (ConverterInput X (Sum Y Y))},
      combConverterOutput? op l = some (ConverterOutput.inn x) →
      (combConverterOutput? op (l ++ [i])).isSome →
      ∃ y : Option (Sum Y Y), i = Sum.inr y := by
  intro l
  induction l using combConverterOutput?.induct with
  | case1 => intro h _; simp [combConverterOutput?] at h
  | case2 x' =>
      intro _ hnext
      rcases i with u | y
      · simp [combConverterOutput?] at hnext
      · exact ⟨y, rfl⟩
  | case3 x' y₁ =>
      intro _ hnext
      rcases i with u | y'
      · simp [combConverterOutput?] at hnext
      · exact ⟨y', rfl⟩
  | case4 x' y₁ y₂ => intro h _; simp [combConverterOutput?] at h
  | case5 x' y₁ y₂ val tail ih =>
      intro h hnext
      simp only [combConverterOutput?] at h
      simp only [List.cons_append, combConverterOutput?] at hnext
      exact ih h hnext
  | case6 x' y₁ y₂ rest'' hnil hinl =>
      intro h _
      rcases rest'' with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [combConverterOutput?] at h
  | case7 x' y₁ rest' hnil hry₂ =>
      intro h _
      rcases rest' with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · exact (hry₂ z' tail rfl).elim
  | case8 x' rest hnil hry₁ =>
      intro h _
      rcases rest with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · exact (hry₁ y' tail rfl).elim
      · simp [combConverterOutput?] at h
  | case9 t hnil hinl =>
      intro h _
      rcases t with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [combConverterOutput?] at h

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): after an `out` output of
`comb⋆`, the next accepted converter input is an outside input `Sum.inl _`.
This is the `input_after_out` alphabet discipline of CR18 Definition 3.8 for
the `comb⋆` converter. -/
theorem combConverterOutput?_append_out (op : Y → Y → Y) {y₀ : Y}
    {i : ConverterInput X (Sum Y Y)} :
    ∀ {l : List (ConverterInput X (Sum Y Y))},
      combConverterOutput? op l = some (ConverterOutput.out y₀) →
      (combConverterOutput? op (l ++ [i])).isSome →
      ∃ u : X, i = Sum.inl u := by
  intro l
  induction l using combConverterOutput?.induct with
  | case1 => intro h _; simp [combConverterOutput?] at h
  | case2 x' => intro h _; simp [combConverterOutput?] at h
  | case3 x' y₁ => intro h _; simp [combConverterOutput?] at h
  | case4 x' y₁ y₂ =>
      intro _ hnext
      rcases i with u | y'
      · exact ⟨u, rfl⟩
      · simp [combConverterOutput?] at hnext
  | case5 x' y₁ y₂ val tail ih =>
      intro h hnext
      simp only [combConverterOutput?] at h
      simp only [List.cons_append, combConverterOutput?] at hnext
      exact ih h hnext
  | case6 x' y₁ y₂ rest'' hnil hinl =>
      intro h _
      rcases rest'' with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [combConverterOutput?] at h
  | case7 x' y₁ rest' hnil hry₂ =>
      intro h _
      rcases rest' with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · exact (hry₂ z' tail rfl).elim
  | case8 x' rest hnil hry₁ =>
      intro h _
      rcases rest with _ | ⟨(a | (_ | (y' | z'))), tail⟩
      · exact (hnil rfl).elim
      · simp [combConverterOutput?] at h
      · simp [combConverterOutput?] at h
      · exact (hry₁ y' tail rfl).elim
      · simp [combConverterOutput?] at h
  | case9 t hnil hinl =>
      intro h _
      rcases t with _ | ⟨a | b, tail⟩
      · exact (hnil rfl).elim
      · exact (hinl a tail rfl).elim
      · simp [combConverterOutput?] at h

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): the converter `comb⋆`.

The converter has outside alphabet `X`, outside output alphabet `Y`, and inner
access to a single parallel DDS with input alphabet `X + X` and output alphabet
`Y + Y`. It implements the prose equation `comb⋆[s,t] = s ⋆ t` by querying the
left component on `x`, querying the right component on the same `x`, and then
outputting `op` applied to the two component responses.

All Definition 3.8 obligations are read off the defining equation
`combConverterOutput?`: the response is the equationally determined
`(combConverterOutput? op l).get _`, prefix closure and the alphabet
discipline are the `combConverterOutput?_*` lemmas above, and the inner-call
bound `2` holds because inner calls occur only at history lengths `1` and `2`
modulo `3`, so no three consecutive histories can all be inner calls. -/
noncomputable def combConverter (op : Y → Y → Y) :
    DDC X Y (Sum X X) (Sum Y Y) where
  system := {
    dom := {l | (combConverterOutput? op l).isSome}
    nonempty_input := by
      simp [combConverterOutput?]
    prefix_closed := fun hpre hne h₂ =>
      combConverterOutput?_isSome_of_prefix op hpre hne h₂
    respond := fun l h => (combConverterOutput? op l).get h
  }
  starts_with_U := by
    intro i rest h
    rcases i with u | y
    · exact ⟨u, rfl⟩
    · simp [combConverterOutput?] at h
  input_after_inn := by
    intro l h x i hresp hnext
    have hsome : (combConverterOutput? op l).isSome := h
    have hf : combConverterOutput? op l = some (ConverterOutput.inn x) :=
      (Option.some_get hsome).symm.trans (congrArg some hresp)
    exact combConverterOutput?_append_inn op hf hnext
  input_after_out := by
    intro l h v' i hresp hnext
    have hsome : (combConverterOutput? op l).isSome := h
    have hf : combConverterOutput? op l = some (ConverterOutput.out v') :=
      (Option.some_get hsome).symm.trans (congrArg some hresp)
    exact combConverterOutput?_append_out op hf hnext
  innerCallBound := 2
  bounded_inner_calls := by
    intro run hrun
    cases hrun with
    | nil => simp
    | singleton _ => simp
    | cons h₁ hext hrest =>
      cases hrest with
      | singleton _ => simp
      | cons h₂ hext₂ hrest₂ =>
        exfalso
        have key : ∀ {l : List (ConverterInput X (Sum Y Y))}
            (h : (combConverterOutput? op l).isSome)
            {o : ConverterOutput Y (Sum X X)},
            (combConverterOutput? op l).get h = o →
              combConverterOutput? op l = some o := by
          intro l h o hget
          rw [← hget, Option.some_get]
        obtain ⟨hdom₁, x₁, hx₁⟩ := h₁
        have hn₁ := combConverterOutput?_inn_length op (key hdom₁ hx₁)
        obtain ⟨i₁, rfl⟩ := hext
        obtain ⟨hdom₂, x₂, hx₂⟩ := h₂
        have hn₂ := combConverterOutput?_inn_length op (key hdom₂ hx₂)
        obtain ⟨i₂, rfl⟩ := hext₂
        obtain ⟨hdom₃, x₃, hx₃⟩ :=
          isInnerCallOutput_of_innerCallRun_cons hrest₂
        have hn₃ := combConverterOutput?_inn_length op (key hdom₃ hx₃)
        simp only [List.length_append, List.length_cons, List.length_nil]
          at hn₁ hn₂ hn₃
        omega

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): decidable converter
domain for the generic `comb⋆` converter.

This instance lets `DDC.apply` attach `comb⋆` to the single parallel-access DDS
used to state the source equation `comb⋆[s,t] = s ⋆ t`. -/
instance combConverterSystemDomDecidable (op : Y → Y → Y) :
    DecidablePred
      (fun l => l ∈ (combConverter op : DDC X Y (Sum X X) (Sum Y Y)).system.dom) := by
  intro l
  dsimp [combConverter]
  infer_instance

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): decidable domain for the
single parallel-access DDS used by `comb⋆`.

Assuming decidable domains for `s` and `t`, this instance lets `DDC.apply`
form the left side of the source equation `comb⋆[s,t] = s ⋆ t`. -/
instance combParallelDomDecidable (s t : DDS X Y)
    [DecidablePred (fun l => l ∈ s.dom)]
    [DecidablePred (fun l => l ∈ t.dom)] :
    DecidablePred (fun l => l ∈ (combParallel s t).dom) := by
  intro l
  letI : DecidablePred (combParallelStep s t) := by
    intro p
    dsimp [combParallelStep]
    cases p.getLast? with
    | none =>
        infer_instance
    | some q =>
        cases q <;> infer_instance
  dsimp [combParallel]
  refine decidable_of_iff
    (l ≠ [] ∧ ∀ p ∈ l.inits, p ≠ [] → combParallelStep s t p) ?_
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro p hpne hp
    exact h.2 p ((List.mem_inits p l).mpr hp) hpne
  · intro h
    refine ⟨h.1, ?_⟩
    intro p hp hpne
    exact h.2 p hpne ((List.mem_inits p l).mp hp)

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): one-step domain
extension for the parallel-access DDS, in equational snoc form. The whole
extended history is accepted as soon as the previous history was (or was
empty) and the local step condition holds for the new last query. -/
theorem combParallel_dom_snoc (s t : DDS X Y)
    {p : List (Sum X X)} {a : Sum X X}
    (hp : p = [] ∨ p ∈ (combParallel s t).dom)
    (hstep : combParallelStep s t (p ++ [a])) :
    p ++ [a] ∈ (combParallel s t).dom := by
  refine ⟨by simp, ?_⟩
  intro q hqne hqpre
  rcases List.prefix_concat_iff.mp hqpre with hq | hq
  · subst hq; exact hstep
  · rcases hp with rfl | hp
    · exact absurd (List.prefix_nil.mp hq) hqne
    · exact hp.2 q hqne hq

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): defining-equation form
of the parallel-access response when the most recent query is on the `s`
side. -/
theorem combParallel_respond_inl (s t : DDS X Y)
    {p : List (Sum X X)} (h : p ∈ (combParallel s t).dom) {x : X}
    (hlast : p.getLast? = some (Sum.inl x))
    (hL : combLeftHistory p ∈ s.dom) :
    (combParallel s t).respond p h = Sum.inl (s.respond (combLeftHistory p) hL) := by
  dsimp only [combParallel]
  split <;> rename_i heq
  · rw [hlast] at heq; cases heq
  · rfl
  · rw [hlast] at heq; cases heq

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): defining-equation form
of the parallel-access response when the most recent query is on the `t`
side. -/
theorem combParallel_respond_inr (s t : DDS X Y)
    {p : List (Sum X X)} (h : p ∈ (combParallel s t).dom) {x : X}
    (hlast : p.getLast? = some (Sum.inr x))
    (hR : combRightHistory p ∈ t.dom) :
    (combParallel s t).respond p h = Sum.inr (t.respond (combRightHistory p) hR) := by
  dsimp only [combParallel]
  split <;> rename_i heq
  · rw [hlast] at heq; cases heq
  · rw [hlast] at heq; cases heq
  · rfl

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): the converter-side trace
of a list of complete `x, y₁, y₂` rounds of `comb⋆[s,t]`, in defining-equation
form. Each round contributes the outside input `x`, the `s`-side response
`y₁`, and the `t`-side response `y₂`. -/
def combRoundsTrace : List (X × Y × Y) → List (ConverterInput X (Sum Y Y))
  | [] => []
  | (x, y₁, y₂) :: r =>
      Sum.inl x :: Sum.inr (some (Sum.inl y₁)) :: Sum.inr (some (Sum.inr y₂)) ::
        combRoundsTrace r

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): the inner-side
(parallel-access) trace of a list of complete `x, y₁, y₂` rounds of
`comb⋆[s,t]`. Each round contributes the `s`-side query `x` and the `t`-side
query on the same `x`. -/
def combRoundsInner : List (X × Y × Y) → List (Sum X X)
  | [] => []
  | (x, _, _) :: r => Sum.inl x :: Sum.inr x :: combRoundsInner r

/-- item P3 helper: the rounds converter trace is a list homomorphism. -/
theorem combRoundsTrace_append (r r' : List (X × Y × Y)) :
    combRoundsTrace (X := X) (Y := Y) (r ++ r') =
      combRoundsTrace r ++ combRoundsTrace r' := by
  induction r with
  | nil => simp [combRoundsTrace]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      simp [combRoundsTrace, ih]

/-- item P3 helper: the rounds inner trace is a list homomorphism. -/
theorem combRoundsInner_append (r r' : List (X × Y × Y)) :
    combRoundsInner (X := X) (Y := Y) (r ++ r') =
      combRoundsInner r ++ combRoundsInner r' := by
  induction r with
  | nil => simp [combRoundsInner]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      simp [combRoundsInner, ih]

/-- item P3 helper: the left projection is a list homomorphism. -/
theorem combLeftHistory_append (l₁ l₂ : List (Sum X X)) :
    combLeftHistory (l₁ ++ l₂) = combLeftHistory l₁ ++ combLeftHistory l₂ :=
  List.filterMap_append

/-- item P3 helper: the right projection is a list homomorphism. -/
theorem combRightHistory_append (l₁ l₂ : List (Sum X X)) :
    combRightHistory (l₁ ++ l₂) = combRightHistory l₁ ++ combRightHistory l₂ :=
  List.filterMap_append

/-- item P3 helper: the left projection of the rounds inner trace recovers the
outside inputs of the rounds. -/
theorem combLeftHistory_roundsInner (r : List (X × Y × Y)) :
    combLeftHistory (combRoundsInner r) = r.map (fun p => p.1) := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      show combLeftHistory ([Sum.inl a, Sum.inr a] ++ combRoundsInner r) = _
      rw [combLeftHistory_append, ih]
      rfl

/-- item P3 helper: the right projection of the rounds inner trace also
recovers the outside inputs of the rounds, because each round queries both
components on the same outside input. -/
theorem combRightHistory_roundsInner (r : List (X × Y × Y)) :
    combRightHistory (combRoundsInner r) = r.map (fun p => p.1) := by
  induction r with
  | nil => rfl
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      show combRightHistory ([Sum.inl a, Sum.inr a] ++ combRoundsInner r) = _
      rw [combRightHistory_append, ih]
      rfl

/-- item P3 helper: the defining equation `combConverterOutput?` consumes any
number of complete `x, y₁, y₂` rounds before a trace whose first entry is an
outside input. -/
theorem combConverterOutput?_roundsTrace_append (op : Y → Y → Y)
    (r : List (X × Y × Y))
    {x : X} {tail : List (ConverterInput X (Sum Y Y))}
    (htail : tail.head? = some (Sum.inl x)) :
    combConverterOutput? op (combRoundsTrace r ++ tail)
      = combConverterOutput? op tail := by
  induction r with
  | nil => simp [combRoundsTrace]
  | cons p r ih =>
      obtain ⟨a, b, c⟩ := p
      obtain ⟨x', rest', heq⟩ : ∃ (x' : X) (rest' : List (ConverterInput X (Sum Y Y))),
          combRoundsTrace r ++ tail = Sum.inl x' :: rest' := by
        cases r with
        | nil =>
            cases tail with
            | nil => simp at htail
            | cons i tl =>
                have hi : i = Sum.inl x := by simpa using htail
                exact ⟨x, tl, by simp [combRoundsTrace, hi]⟩
        | cons q r' =>
            obtain ⟨a', b', c'⟩ := q
            exact ⟨a', Sum.inr (some (Sum.inl b')) :: Sum.inr (some (Sum.inr c')) ::
              (combRoundsTrace r' ++ tail), by simp [combRoundsTrace]⟩
      rw [show combRoundsTrace ((a, b, c) :: r) ++ tail
          = Sum.inl a :: Sum.inr (some (Sum.inl b)) :: Sum.inr (some (Sum.inr c)) ::
            (combRoundsTrace r ++ tail) from by simp [combRoundsTrace], heq]
      rw [show combConverterOutput? op (Sum.inl a :: Sum.inr (some (Sum.inl b)) ::
            Sum.inr (some (Sum.inr c)) :: Sum.inl x' :: rest')
          = combConverterOutput? op (Sum.inl x' :: rest') from by
        simp [combConverterOutput?]]
      rw [← heq]
      exact ih

/-- item P3 helper: one complete `x, y₁, y₂` round of the operational driver
for `comb⋆[s,t]`, in defining-equation form. Starting from any number of
complete rounds, an outside input `x` triggers the inner call to `s` (answered
by `y₁`), then the inner call to `t` on the same `x` (answered by `y₂`), and
the driver returns `op y₁ y₂` with the round completed on both traces. -/
theorem runConverter_combRound (op : Y → Y → Y) (s t : DDS X Y)
    [DecidablePred (fun l => l ∈ s.dom)] [DecidablePred (fun l => l ∈ t.dom)]
    (r : List (X × Y × Y)) (x : X) (y₁ y₂ : Y)
    (hit : combRoundsInner r = [] ∨ combRoundsInner r ∈ (combParallel s t).dom)
    (hL : r.map (fun p => p.1) ++ [x] ∈ s.dom)
    (hLy : s.respond (r.map (fun p => p.1) ++ [x]) hL = y₁)
    (hR : r.map (fun p => p.1) ++ [x] ∈ t.dom)
    (hRy : t.respond (r.map (fun p => p.1) ++ [x]) hR = y₂) :
    combRoundsInner (r ++ [(x, y₁, y₂)]) ∈ (combParallel s t).dom ∧
      DDC.runConverter (combConverter op : DDC X Y (Sum X X) (Sum Y Y))
          (combParallel s t) 2 (combRoundsTrace r ++ [Sum.inl x]) (combRoundsInner r) =
        some (combRoundsTrace (r ++ [(x, y₁, y₂)]), combRoundsInner (r ++ [(x, y₁, y₂)]),
          op y₁ y₂) := by
  -- the `s`-side extension of the inner trace
  have hLproj : combLeftHistory (combRoundsInner r ++ [Sum.inl x])
      = r.map (fun p => p.1) ++ [x] := by
    rw [combLeftHistory_append, combLeftHistory_roundsInner]
    rfl
  have hLmem : combLeftHistory (combRoundsInner r ++ [Sum.inl x]) ∈ s.dom := by
    rw [hLproj]; exact hL
  have hstep1 : combParallelStep s t (combRoundsInner r ++ [Sum.inl x]) := by
    have hgl : (combRoundsInner r ++ [Sum.inl x]).getLast? = some (Sum.inl x) :=
      List.getLast?_concat
    simp only [combParallelStep, hgl]
    exact hLmem
  have hit1 : combRoundsInner r ++ [Sum.inl x] ∈ (combParallel s t).dom :=
    combParallel_dom_snoc s t hit hstep1
  have hresp1 : (combParallel s t).respond (combRoundsInner r ++ [Sum.inl x]) hit1
      = Sum.inl y₁ := by
    rw [combParallel_respond_inl s t hit1 List.getLast?_concat hLmem]
    exact congrArg Sum.inl ((s.respond_congr hLproj hLmem hL).trans hLy)
  -- the `t`-side extension of the inner trace
  have hRproj : combRightHistory ((combRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr x])
      = r.map (fun p => p.1) ++ [x] := by
    rw [combRightHistory_append, combRightHistory_append, combRightHistory_roundsInner]
    simp [combRightHistory]
  have hRmem : combRightHistory ((combRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr x])
      ∈ t.dom := by
    rw [hRproj]; exact hR
  have hstep2 : combParallelStep s t ((combRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr x]) := by
    have hgl : ((combRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr (x : X)]).getLast?
        = some (Sum.inr x) := List.getLast?_concat
    simp only [combParallelStep, hgl]
    exact hRmem
  have hit2 : (combRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr x] ∈ (combParallel s t).dom :=
    combParallel_dom_snoc s t (Or.inr hit1) hstep2
  have hresp2 : (combParallel s t).respond
      ((combRoundsInner r ++ [Sum.inl x]) ++ [Sum.inr x]) hit2 = Sum.inr y₂ := by
    rw [combParallel_respond_inr s t hit2 List.getLast?_concat hRmem]
    exact congrArg Sum.inr ((t.respond_congr hRproj hRmem hR).trans hRy)
  -- the completed inner responses queried by the driver
  have hcir1 : DDC.completedInnerResponse (combParallel s t) (combRoundsInner r) (Sum.inl x)
      = some (Sum.inl y₁) := by
    rw [completedInnerResponse_of_dom (combParallel s t) _ _ hit hit1, hresp1]
  have hcir2 : DDC.completedInnerResponse (combParallel s t)
      (combRoundsInner r ++ [Sum.inl x]) (Sum.inr x) = some (Sum.inr y₂) := by
    rw [completedInnerResponse_of_dom (combParallel s t) _ _ (Or.inr hit1) hit2, hresp2]
  -- the three converter-trace defining equations of the round
  have hct1 : combConverterOutput? op (combRoundsTrace r ++ [Sum.inl x])
      = some (ConverterOutput.inn (Sum.inl x)) := by
    rw [combConverterOutput?_roundsTrace_append op r rfl]
    simp [combConverterOutput?]
  have hct2 : combConverterOutput? op
      (combRoundsTrace r ++ [Sum.inl x, Sum.inr (some (Sum.inl y₁))])
      = some (ConverterOutput.inn (Sum.inr x)) := by
    rw [combConverterOutput?_roundsTrace_append op r rfl]
    simp [combConverterOutput?]
  have hct3 : combConverterOutput? op (combRoundsTrace r ++
        [Sum.inl x, Sum.inr (some (Sum.inl y₁)), Sum.inr (some (Sum.inr y₂))])
      = some (ConverterOutput.out (op y₁ y₂)) := by
    rw [combConverterOutput?_roundsTrace_append op r rfl]
    simp [combConverterOutput?]
  have hdom1 : combRoundsTrace r ++ [Sum.inl x]
      ∈ (combConverter op : DDC X Y (Sum X X) (Sum Y Y)).system.dom := by
    show (combConverterOutput? op _).isSome
    simp [hct1]
  have hrespC1 : (combConverter op : DDC X Y (Sum X X) (Sum Y Y)).system.respond
      (combRoundsTrace r ++ [Sum.inl x]) hdom1 = ConverterOutput.inn (Sum.inl x) := by
    show (combConverterOutput? op _).get _ = _
    simp [hct1]
  have hdom2 : combRoundsTrace r ++ [Sum.inl x, Sum.inr (some (Sum.inl y₁))]
      ∈ (combConverter op : DDC X Y (Sum X X) (Sum Y Y)).system.dom := by
    show (combConverterOutput? op _).isSome
    simp [hct2]
  have hrespC2 : (combConverter op : DDC X Y (Sum X X) (Sum Y Y)).system.respond
      (combRoundsTrace r ++ [Sum.inl x, Sum.inr (some (Sum.inl y₁))]) hdom2
      = ConverterOutput.inn (Sum.inr x) := by
    show (combConverterOutput? op _).get _ = _
    simp [hct2]
  have hdom3 : combRoundsTrace r ++
        [Sum.inl x, Sum.inr (some (Sum.inl y₁)), Sum.inr (some (Sum.inr y₂))]
      ∈ (combConverter op : DDC X Y (Sum X X) (Sum Y Y)).system.dom := by
    show (combConverterOutput? op _).isSome
    simp [hct3]
  have hrespC3 : (combConverter op : DDC X Y (Sum X X) (Sum Y Y)).system.respond
      (combRoundsTrace r ++
        [Sum.inl x, Sum.inr (some (Sum.inl y₁)), Sum.inr (some (Sum.inr y₂))]) hdom3
      = ConverterOutput.out (op y₁ y₂) := by
    show (combConverterOutput? op _).get _ = _
    simp [hct3]
  refine ⟨?_, ?_⟩
  · simpa [combRoundsInner_append, combRoundsInner] using hit2
  · rw [DDC.runConverter_inn _ _ 1 _ _ hdom1 hrespC1, hcir1]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [DDC.runConverter_inn _ _ 0 _ _ hdom2 hrespC2, hcir2]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [DDC.runConverter_out _ _ 0 _ _ hdom3 hrespC3]
    simp [combRoundsTrace_append, combRoundsInner_append, combRoundsTrace,
      combRoundsInner]

/-- item P3 helper: the full driver invariant for `comb⋆[s,t]`. After any
number of complete rounds consistent with `s` and `t`, processing the
remaining outside inputs succeeds and returns `op` applied to the last entries
of the intermediate `Y`-histories of `s` and `t`. -/
theorem applyTraceAux_combRounds (op : Y → Y → Y) (s t : DDS X Y)
    [DecidablePred (fun l => l ∈ s.dom)] [DecidablePred (fun l => l ∈ t.dom)]
    (l : List X) (hs : l ∈ s.dom) (ht : l ∈ t.dom) :
    ∀ (rest : List X) (k : ℕ) (r : List (X × Y × Y)),
      l.drop k = rest → rest ≠ [] →
      r.map (fun p => p.1) = l.take k →
      (combRoundsInner r = [] ∨ combRoundsInner r ∈ (combParallel s t).dom) →
      ∃ ct' it',
        DDC.applyTraceAux (combConverter op : DDC X Y (Sum X X) (Sum Y Y))
            (combParallel s t) 2 rest (combRoundsTrace r) (combRoundsInner r) =
          some (ct', it',
            op ((yHistory s l hs).getLast (yHistory_ne_nil s l hs))
              ((yHistory t l ht).getLast (yHistory_ne_nil t l ht))) := by
  have hlne : l ≠ [] := fun hnil => s.nonempty_input (hnil ▸ hs)
  have hYsne : yHistory s l hs ≠ [] := yHistory_ne_nil s l hs
  have hYtne : yHistory t l ht ≠ [] := yHistory_ne_nil t l ht
  intro rest
  induction rest with
  | nil => intro k r _ hne _ _; exact absurd rfl hne
  | cons x rest' ih =>
      intro k r hdrop hne hm1 hit
      -- the position of the current outside input
      have hk : k < l.length := by
        by_contra hk'
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hk')] at hdrop
        cases hdrop
      have hxr : l[k] :: l.drop (k + 1) = x :: rest' := by
        rw [← List.drop_eq_getElem_cons hk, hdrop]
      have hx : l[k] = x := by injection hxr
      have hrest' : l.drop (k + 1) = rest' := by injection hxr
      have hkYs : k < (yHistory s l hs).length := by
        rw [yHistory_length]; exact hk
      have hkYt : k < (yHistory t l ht).length := by
        rw [yHistory_length]; exact hk
      -- the canonical responses of `s` and `t` at this round
      have htakeL : l.take k ++ [l[k]] = l.take (k + 1) :=
        (List.take_succ_eq_append_getElem hk).symm
      have hLmem : l.take (k + 1) ∈ s.dom :=
        s.prefix_closed (List.take_prefix _ l)
          (by simp [List.take_eq_nil_iff, hlne]) hs
      have hRmem : l.take (k + 1) ∈ t.dom :=
        t.prefix_closed (List.take_prefix _ l)
          (by simp [List.take_eq_nil_iff, hlne]) ht
      have hmem1 : r.map (fun p => p.1) ++ [x] ∈ s.dom := by
        rw [hm1, ← hx, htakeL]; exact hLmem
      have hresp1 : s.respond (r.map (fun p => p.1) ++ [x]) hmem1
          = (yHistory s l hs)[k]'hkYs := by
        rw [yHistory_getElem s l hs k hkYs]
        exact s.respond_congr (by rw [hm1, ← hx, htakeL]) hmem1 _
      have hmem2 : r.map (fun p => p.1) ++ [x] ∈ t.dom := by
        rw [hm1, ← hx, htakeL]; exact hRmem
      have hresp2 : t.respond (r.map (fun p => p.1) ++ [x]) hmem2
          = (yHistory t l ht)[k]'hkYt := by
        rw [yHistory_getElem t l ht k hkYt]
        exact t.respond_congr (by rw [hm1, ← hx, htakeL]) hmem2 _
      have hround := runConverter_combRound op s t r x
        ((yHistory s l hs)[k]'hkYs) ((yHistory t l ht)[k]'hkYt)
        hit hmem1 hresp1 hmem2 hresp2
      cases rest' with
      | nil =>
          -- last round: the driver returns `op` of the last `Y`-history entries
          have hkn : k + 1 = l.length := by
            have hlen := congrArg List.length hrest'
            simp only [List.length_drop, List.length_nil] at hlen
            omega
          have hidxs : k = (yHistory s l hs).length - 1 := by
            rw [yHistory_length]
            omega
          have hidxt : k = (yHistory t l ht).length - 1 := by
            rw [yHistory_length]
            omega
          have hgls : (yHistory s l hs)[k]'hkYs
              = (yHistory s l hs).getLast hYsne := by
            rw [List.getLast_eq_getElem]
            congr 1
          have hglt : (yHistory t l ht)[k]'hkYt
              = (yHistory t l ht).getLast hYtne := by
            rw [List.getLast_eq_getElem]
            congr 1
          refine ⟨combRoundsTrace (r ++ [(x, (yHistory s l hs)[k]'hkYs,
              (yHistory t l ht)[k]'hkYt)]),
            combRoundsInner (r ++ [(x, (yHistory s l hs)[k]'hkYs,
              (yHistory t l ht)[k]'hkYt)]), ?_⟩
          unfold DDC.applyTraceAux
          rw [hround.2, ← hgls, ← hglt]
      | cons x2 rest'' =>
          -- recurse with one more completed round
          have hm1' : (r ++ [(x, (yHistory s l hs)[k]'hkYs,
              (yHistory t l ht)[k]'hkYt)]).map (fun p => p.1)
              = l.take (k + 1) := by
            rw [List.map_append, hm1]
            simp [← hx]
          obtain ⟨ct', it', hrun'⟩ := ih (k + 1)
            (r ++ [(x, (yHistory s l hs)[k]'hkYs,
              (yHistory t l ht)[k]'hkYt)])
            hrest' (by simp) hm1' (Or.inr hround.1)
          refine ⟨ct', it', ?_⟩
          unfold DDC.applyTraceAux
          rw [hround.2]
          exact hrun'

/-- CR18 Definition 3.12 / comb⋆ converter (item P3): output agreement
recording the prose-only defining equation `comb⋆[s,t] = s ⋆ t`.

For every output-combine history `l`, applying the generic `comb⋆` converter to
the single parallel-access DDS for `s` and `t` has an output that agrees with
the already formalized output-combine `s ⋆ t` on `l`. -/
theorem combConverter_output_eq_outputCombine (op : Y → Y → Y) (s t : DDS X Y)
    [DecidablePred (fun l => l ∈ s.dom)]
    [DecidablePred (fun l => l ∈ t.dom)]
    (l : List X) (h : l ∈ (DDS.outputCombine op s t).dom) :
    ∃ hcomb : l ∈ (DDC.apply (combConverter op : DDC X Y (Sum X X) (Sum Y Y))
      (combParallel s t)).dom,
      (DDC.apply (combConverter op : DDC X Y (Sum X X) (Sum Y Y))
        (combParallel s t)).output l hcomb = (DDS.outputCombine op s t).output l h := by
  have hs : l ∈ s.dom := h.1
  have ht : l ∈ t.dom := h.2
  have hlne : l ≠ [] := fun hnil => s.nonempty_input (hnil ▸ hs)
  have hYsne : yHistory s l hs ≠ [] := yHistory_ne_nil s l hs
  have hYtne : yHistory t l ht ≠ [] := yHistory_ne_nil t l ht
  -- run the driver invariant from the empty trace
  obtain ⟨ct', it', hrun⟩ :=
    applyTraceAux_combRounds op s t l hs ht l 0 [] (by simp) hlne (by simp)
      (Or.inl rfl)
  have happly : DDC.applyTrace (combConverter op : DDC X Y (Sum X X) (Sum Y Y))
      (combParallel s t) l
      = some (op ((yHistory s l hs).getLast hYsne)
          ((yHistory t l ht).getLast hYtne)) := by
    unfold DDC.applyTrace
    have hbound : (combConverter op : DDC X Y (Sum X X) (Sum Y Y)).innerCallBound
        = 2 := rfl
    rw [hbound]
    simp only [combRoundsTrace, combRoundsInner] at hrun
    rw [hrun]
    rfl
  refine ⟨⟨hlne, op ((yHistory s l hs).getLast hYsne)
      ((yHistory t l ht).getLast hYtne), happly⟩, ?_⟩
  rw [DDC.apply_output_eq_of_applyTrace (combConverter op : DDC X Y (Sum X X) (Sum Y Y))
    (combParallel s t) l hlne happly]
  rw [outputCombine_output op s t l h]
  -- the last `Y`-history entries are the component responses on the full history
  have hglS : (yHistory s l hs).getLast hYsne = s.output l h.1 := by
    have hpos : 0 < (yHistory s l hs).length := List.length_pos_iff.mpr hYsne
    have hidx : (yHistory s l hs).length - 1 < (yHistory s l hs).length := by omega
    rw [List.getLast_eq_getElem, yHistory_getElem s l hs _ hidx]
    have htake : l.take ((yHistory s l hs).length - 1 + 1) = l := by
      have hlen : (yHistory s l hs).length - 1 + 1 = l.length := by
        rw [yHistory_length]
        have : 0 < l.length := List.length_pos_iff.mpr hlne
        omega
      rw [hlen, List.take_length]
    exact s.respond_congr htake _ h.1
  have hglT : (yHistory t l ht).getLast hYtne = t.output l h.2 := by
    have hpos : 0 < (yHistory t l ht).length := List.length_pos_iff.mpr hYtne
    have hidx : (yHistory t l ht).length - 1 < (yHistory t l ht).length := by omega
    rw [List.getLast_eq_getElem, yHistory_getElem t l ht _ hidx]
    have htake : l.take ((yHistory t l ht).length - 1 + 1) = l := by
      have hlen : (yHistory t l ht).length - 1 + 1 = l.length := by
        rw [yHistory_length]
        have : 0 < l.length := List.length_pos_iff.mpr hlne
        omega
      rw [hlen, List.take_length]
    exact t.respond_congr htake _ h.2
  rw [hglS, hglT]

end DDS

/-!
## CR18 Section 3.4.3: Filters

This section formalizes CR18 Section 3.4.3 and Definition 3.10. A filter is a
special converter-like restriction of a DDS domain to a prefix-closed subset,
while preserving the original DDS responses on the retained histories. The
fixed query filter `[q]` keeps exactly the histories of the original DDS whose
length is at most `q`.
-/

/-- CR18 Section 3.4.3: a filter restricts each `(X, Y)`-DDS domain to a
prefix-closed subset of the original domain. Applying such a filter to `s`
keeps only `keep s`, which must be a subset of `s.dom` and closed under
nonempty prefixes in the same shape as `DDS.prefix_closed`. -/
structure Filter (X Y : Type*) where
  /-- CR18 Section 3.4.3: the retained histories of the DDS after applying the
  filter. -/
  keep : DDS X Y → Set (List X)
  /-- CR18 Section 3.4.3: a filter only restricts the original DDS domain. -/
  keep_subset : ∀ s, keep s ⊆ s.dom
  /-- CR18 Section 3.4.3: the retained histories are closed under nonempty
  prefixes. -/
  keep_prefix_closed :
    ∀ s {l1 l2 : List X}, l1 <+: l2 → l1 ≠ [] → l2 ∈ keep s → l1 ∈ keep s

namespace Filter

variable {X Y : Type*}

/-- CR18 Section 3.4.3: apply a filter `phi` to a DDS `s`. The resulting DDS
has domain `phi.keep s`, a subset of `s.dom`, and responds with the original
system response on every retained history. -/
def apply (phi : Filter X Y) (s : DDS X Y) : DDS X Y where
  dom := phi.keep s
  nonempty_input := by
    intro h
    exact s.nonempty_input (phi.keep_subset s h)
  prefix_closed := by
    intro l1 l2 hprefix hnonempty hdom
    exact phi.keep_prefix_closed s hprefix hnonempty hdom
  respond := fun l h => s.respond l (phi.keep_subset s h)

/-- CR18 Section 3.4.3: applying a filter preserves the original DDS output
on every history retained by the filtered domain. This formalizes
`(phi s)(x1, ..., xk) = s(x1, ..., xk)` for histories in `dom(phi s)`. -/
@[simp]
theorem apply_output (phi : Filter X Y) (s : DDS X Y) (l : List X)
    (h : l ∈ (phi.apply s).dom) :
    (phi.apply s).output l h = s.output l (phi.keep_subset s h) := by
  rfl

/-- CR18 Section 3.4.3: the domain of a filtered DDS is a subset of the
original DDS domain. -/
theorem apply_dom_subset (phi : Filter X Y) (s : DDS X Y) :
    (phi.apply s).dom ⊆ s.dom := by
  intro l h
  exact phi.keep_subset s h

end Filter

variable {X Y : Type*}

/-- CR18 Definition 3.10: the filter `[q]` restricts access to at most `q`
queries. It keeps exactly those histories already in the original DDS domain
whose length is at most `q`, so the filtered DDS is undefined starting at the
`(q + 1)`-st query. -/
def queryFilter (X Y : Type*) (q : Nat) : Filter X Y where
  keep := fun s => {l | l ∈ s.dom ∧ l.length ≤ q}
  keep_subset := by
    intro s l h
    exact h.1
  keep_prefix_closed := by
    intro s l1 l2 hprefix hne hkeep
    exact ⟨s.prefix_closed hprefix hne hkeep.1,
      le_trans (List.IsPrefix.length_le hprefix) hkeep.2⟩

/-- CR18 Definition 3.10: apply the query filter `[q]` to a DDS `s`. This is
the Lean spelling of the source notation `[q]s`. -/
def filterQueries (q : Nat) (s : DDS X Y) : DDS X Y :=
  (queryFilter X Y q).apply s

/-- CR18 Definition 3.10: membership in `[q]s` is exactly membership in the
original DDS domain together with the query bound `length <= q`. -/
@[simp]
theorem filterQueries_dom (q : Nat) (s : DDS X Y) (l : List X) :
    l ∈ (filterQueries q s).dom ↔ l ∈ s.dom ∧ l.length ≤ q := by
  rfl

/-- CR18 Definition 3.10: `[q]s` is undefined on histories whose length is
greater than `q`, in particular as of the `(q + 1)`-st query. -/
theorem filterQueries_not_mem_of_length_gt (q : Nat) (s : DDS X Y)
    {l : List X} (hlen : q < l.length) :
    l ∉ (filterQueries q s).dom := by
  intro h
  exact (not_le_of_gt hlen) ((filterQueries_dom q s l).mp h).2

/-- CR18 Definition 3.10: `[q]s` preserves the response of `s` on every
history retained by the query filter. -/
@[simp]
theorem filterQueries_output (q : Nat) (s : DDS X Y) (l : List X)
    (h : l ∈ (filterQueries q s).dom) :
    (filterQueries q s).output l h =
      s.output l ((queryFilter X Y q).keep_subset s h) := by
  exact Filter.apply_output (queryFilter X Y q) s l h

namespace DDS

/-!
## CR18 Definition 3.13: Converter Attachment at an Interface

CR18 writes `alpha^i s` for the result of attaching a
`((X, Y), (X, Y))` converter `alpha` at one distinguished interface `i` of a
resource `s : Resource P X Y`, i.e. a `(P × X, Y)` DDS. Inputs at interfaces
other than `i` are handled by `s` exactly as before. Inputs at interface `i`
are handled by the converter: outside input `x` is given to `alpha`, inner
converter outputs `inn x'` are forwarded to the `i`-interface view of `s`, and
the first converter output `out y` becomes the resource output.

The interface-local converter execution is deliberately reduced to the
existing CR18 Definition 3.9 operation `DDC.apply` on the DDS obtained by
feeding `s` only queries tagged with `i`.
-/

variable {P X Y : Type*}
variable [DecidableEq P]

/-- CR18 Definition 3.13: the subsequence of a resource history consisting of
the payloads sent to interface `i`. This is the outside history seen by the
converter attached at `i`. -/
def interfaceHistory (i : P) (l : List (P × X)) : List X :=
  l.filterMap fun input =>
    if input.1 = i then
      some input.2
    else
      none

/-- CR18 Definition 3.13: the `(X, Y)` DDS obtained by restricting a resource
`s : Resource P X Y` to queries at the distinguished interface `i`. A pure
`X`-history is accepted exactly when the corresponding resource history with
every input tagged by `i` is accepted by `s`. -/
def interfaceRestriction (i : P) (s : Resource P X Y) : DDS X Y where
  dom := {l | List.map (fun x : X => (i, x)) l ∈ s.dom}
  nonempty_input := by
    intro h
    exact s.nonempty_input (by simpa using h)
  prefix_closed := by
    intro l₁ l₂ hprefix hnonempty hdom
    exact s.prefix_closed (by simpa using hprefix.map (fun x : X => (i, x)))
      (by simpa using hnonempty) hdom
  respond := fun l h => s.respond (List.map (fun x : X => (i, x)) l) h

/-- CR18 Definition 3.13: decidability of the interface restriction domain is
inherited from decidability of the resource domain. This supplies the
typeclass required by `DDC.apply`. -/
instance interfaceRestriction_dom_decidable (i : P) (s : Resource P X Y)
    [DecidablePred (fun l => l ∈ s.dom)] :
    DecidablePred (fun l => l ∈ (interfaceRestriction i s).dom) := by
  intro l
  change Decidable (List.map (fun x : X => (i, x)) l ∈ s.dom)
  infer_instance

/-- CR18 Definition 3.13: the `(X, Y)` DDS obtained by restricting a resource
`s : Resource P X Y` to interface `i`, but *anchored at the live resource
prefix* `pre`. A pure `X`-history `m` is accepted exactly when the resource
history `pre ++ map (i, ·) m` is accepted by `s`, and the response is that of
`s` on the full anchored history.

This is the faithful inner system the converter at interface `i` talks to while
handling an input that arrives after the resource has already processed the
history `pre`: an inner call `inn x'` is routed to `s⊥` as `(i, x')` *appended
to the live history `pre`*, so `s` still sees every input it received at the
other interfaces (and at `i`) before the current activation. The empty inner
history is excluded so that this is a genuine DDS even when `pre ∈ s.dom`. -/
def interfaceRestrictionFrom (i : P) (pre : List (P × X)) (s : Resource P X Y) :
    DDS X Y where
  dom := {l | l ≠ [] ∧ pre ++ List.map (fun x : X => (i, x)) l ∈ s.dom}
  nonempty_input := by
    rintro ⟨hne, _⟩; exact hne rfl
  prefix_closed := by
    rintro l₁ l₂ hprefix hnonempty ⟨_, hdom⟩
    refine ⟨hnonempty, s.prefix_closed ?_ ?_ hdom⟩
    · obtain ⟨t, ht⟩ := hprefix.map (fun x : X => (i, x))
      exact ⟨t, by rw [List.append_assoc, ht]⟩
    · intro hnil
      have := (List.append_eq_nil_iff).1 hnil
      exact hnonempty (List.map_eq_nil_iff.1 this.2)
  respond := fun l h => s.respond (pre ++ List.map (fun x : X => (i, x)) l) h.2

/-- CR18 Definition 3.13: decidability of the anchored interface restriction
domain, inherited from decidability of the resource domain. -/
instance interfaceRestrictionFrom_dom_decidable (i : P) (pre : List (P × X))
    (s : Resource P X Y) [DecidablePred (fun l => l ∈ s.dom)] :
    DecidablePred (fun l => l ∈ (interfaceRestrictionFrom i pre s).dom) := by
  intro l
  change Decidable (l ≠ [] ∧ pre ++ List.map (fun x : X => (i, x)) l ∈ s.dom)
  infer_instance

/-- CR18 Definition 3.13: the interface-local DDS produced by applying `alpha`
to the interface-`i` restriction of `s` *anchored at the live resource prefix*
`pre`. This is the formal model of the source text's handling of an input
`(i, x)` that arrives after `s` has already processed the history `pre`: the
converter's `inn x'` outputs are routed to `s⊥` as `(i, x')` appended to the
live history `pre`, and the converter's first `out y` is the resource output.

Anchoring at `pre` (rather than at the empty history) is essential for
faithfulness to a *stateful* resource: `s`'s response at interface `i` may
depend on inputs it received at the other interfaces, and those inputs are part
of `pre`. The earlier context-free model `DDC.apply alpha (interfaceRestriction
i s)` silently discarded that cross-interface context. -/
noncomputable def attachedInterface (i : P) (pre : List (P × X))
    (alpha : DDC X Y X Y) (s : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] : DDS X Y :=
  DDC.apply alpha (interfaceRestrictionFrom i pre s)

/-!
### Equational (Maurer-style) attachment via `DDS.comap`

The attachment `αⁱs` is now defined **equationally** as a `DDS.comap` over a
purely-functional history morphism `translate α i`, postcomposed with α's output
transformation at interface `i`. This replaces the previous operational driver
encoding, whose `attachAtDom` recorded only the *final* activation's success and
therefore had a PROVEN-FALSE `prefix_closed` obligation.

**Formalization choice (single inner call per query).** Under Def 3.9's "we do not
give a completely formal definition", we model the converter `α` at interface `i`
by its **single inner-call-per-query** behaviour, in the *memoryless* form used by
the `casc`/`comb⋆` converters: on an outside input `x`, `α` issues exactly one
inner call `inn (αInnerInput α x)` to `s` (routed at the same interface `i`,
appended to the live resource history so all cross-interface state is preserved by
the `comap` derived history), and on receiving the inner response `y'` emits the
outside output `αOuterOutput α x y'`. An `i`-query for which `α` does not make a
well-defined inner call (it outputs immediately, or `α` is undefined on `[x]`)
makes the translation — hence the attachment — undefined there. For `α` undefined
on `[x]` this matches the operational driver (Def 3.9 `DDC.apply`); an
immediate-`out` (zero-inner-call) converter such as `DDC.trivial` is instead
DEFINED by the driver (`apply_output_single_of_out`), so zero-call converters are
OUTSIDE the modeled class — as are multi-call converters (e.g. the ℓ-invocation
example before Def 3.8), converters whose behaviour depends on their own earlier
activations, and converters that recover from a `⊥` inner response. This scope
restriction is the deliberate price of the equational `comap` form (a derived
history cannot depend on `s`'s responses); the faithful operational
interface-local execution remains available above via `attachedInterface`
(Def 3.9 `DDC.apply` on `interfaceRestrictionFrom`).

Because `translate α i` is **coordinate-wise** (it touches only interface-`i`
entries, leaving every `p ≠ i` entry fixed), prefix monotonicity and nonempty
preservation are immediate, the `comap` WF obligations close once, and the
distinct-interface commutation (Lemma 3.1) reduces to the fact that
`translate α i` and `translate β j` act on disjoint coordinates.
-/

/-- CR18 Definition 3.13 (single-call model): the converter's inner-call input on
outside input `x`. We run `α`'s system on the one-element converter trace
`[inl x]`; if it issues an inner call `inn x'`, the inner-call input is `x'`,
otherwise there is no inner call (`none`). -/
def αInnerInput (alpha : DDC X Y X Y) [DecidablePred (fun l => l ∈ alpha.system.dom)]
    (x : X) : Option X :=
  if h : [Sum.inl x] ∈ alpha.system.dom then
    match alpha.system.respond [Sum.inl x] h with
    | ConverterOutput.inn x' => some x'
    | ConverterOutput.out _ => none
  else
    none

/-- CR18 Definition 3.13 (single-call model): the converter's outside output after
its single inner call on outside input `x` returns the inner response `y'`. We run
`α`'s system on the converter trace `[inl x, inr (some y')]`; if it emits an
outside output `out y`, that `y` is the result, otherwise `none`. -/
def αOuterOutput (alpha : DDC X Y X Y) [DecidablePred (fun l => l ∈ alpha.system.dom)]
    (x : X) (y' : Y) : Option Y :=
  if h : [Sum.inl x, Sum.inr (some y')] ∈ alpha.system.dom then
    match alpha.system.respond [Sum.inl x, Sum.inr (some y')] h with
    | ConverterOutput.out y => some y
    | ConverterOutput.inn _ => none
  else
    none

/-- CR18 Definition 3.13 (single-call model): translate one resource input entry.
An entry at an interface `p ≠ i` is passed through unchanged; an entry `(i, x)` at
the distinguished interface is rerouted to the converter's inner call
`(i, αInnerInput α x)`. The reroute is `Option`-valued because `α` may make no
inner call. -/
def translateEntry (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)] (e : P × X) :
    Option (P × X) :=
  if e.1 = i then
    (αInnerInput alpha e.2).map (fun x' => (i, x'))
  else
    some e

/-- CR18 Definition 3.13 (single-call model): the set of resource histories on
which the coordinate-wise translation is *defined* — nonempty histories all of
whose entries translate (every interface-`i` entry yields a well-defined inner
call). -/
def translateDefined (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)] : Set (List (P × X)) :=
  {l | l ≠ [] ∧ ∀ e ∈ l, (translateEntry i alpha e).isSome}

/-- CR18 Definition 3.13 (single-call model): the translated (derived) resource
history that `s` is actually evaluated on, defined on `translateDefined`. Each
entry is replaced by its `translateEntry` image; the membership proof guarantees
every entry translates, so `Option.get` is total here. -/
def translateMap (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    (l : List (P × X)) (h : l ∈ translateDefined i alpha) : List (P × X) :=
  l.attach.map (fun e => (translateEntry i alpha e.1).get (h.2 e.1 e.2))

@[simp]
theorem translateMap_length (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    (l : List (P × X)) (h : l ∈ translateDefined i alpha) :
    (translateMap i alpha l h).length = l.length := by
  simp [translateMap]

/-- Non-dependent characterization of `translateMap`: on a defined history every
entry translates, so the dependent `Option.get` coincides with the total
`Option.getD e`. This frees the structural reasoning from the membership proofs. -/
theorem translateMap_eq_map_getD (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    (l : List (P × X)) (h : l ∈ translateDefined i alpha) :
    translateMap i alpha l h =
      l.map (fun e => (translateEntry i alpha e).getD e) := by
  simp only [translateMap]
  rw [show (fun e : {x // x ∈ l} => (translateEntry i alpha e.1).get (h.2 e.1 e.2))
        = (fun e : {x // x ∈ l} => (translateEntry i alpha (e : P × X)).getD (e : P × X))
        from by funext e; exact Option.get_eq_getD _]
  exact List.attach_map_val (l := l)
    (f := fun e => (translateEntry i alpha e).getD e)

/-- The set `translateDefined` is downward closed under (the `subset` of) sublists
of a defined history: every entry of a sublist is an entry of the whole. Used for
the prefix-closure and monotonicity laws of `translate`. -/
theorem translateDefined_of_subset (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    {l₁ l₂ : List (P × X)} (hsub : ∀ e ∈ l₁, e ∈ l₂) (hne : l₁ ≠ [])
    (h₂ : l₂ ∈ translateDefined i alpha) : l₁ ∈ translateDefined i alpha :=
  ⟨hne, fun e he => h₂.2 e (hsub e he)⟩

/-- CR18 Definition 3.13: the coordinate-wise translation `translateMap`
distributes over `append`. This is the single structural fact behind the two scan
laws of `translate`. -/
theorem translateMap_append (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    (l₁ l₂ : List (P × X)) (h : l₁ ++ l₂ ∈ translateDefined i alpha)
    (h₁ : l₁ ∈ translateDefined i alpha) (h₂ : l₂ ∈ translateDefined i alpha) :
    translateMap i alpha (l₁ ++ l₂) h =
      translateMap i alpha l₁ h₁ ++ translateMap i alpha l₂ h₂ := by
  rw [translateMap_eq_map_getD i alpha (l₁ ++ l₂) h,
      translateMap_eq_map_getD i alpha l₁ h₁,
      translateMap_eq_map_getD i alpha l₂ h₂, List.map_append]

/-- CR18 Definition 3.13: the coordinate-wise translation morphism
`translate α i : HistMap (P×X) (P×X)`. Because it acts entry-by-entry, the two
scan laws (prefix monotonicity, nonempty preservation) are immediate from
`translateMap_append`. -/
def translate (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)] : HistMap (P × X) (P × X) :=
  HistMap.ofScan (translateDefined i alpha)
    (by rintro ⟨hne, _⟩; exact hne rfl)
    (by
      rintro l₁ l₂ hprefix hne h₂
      exact translateDefined_of_subset i alpha (fun e he => hprefix.subset he) hne h₂)
    (translateMap i alpha)
    (by
      -- prefix monotonicity from `translateMap_append`
      intro l₁ l₂ h₁ h₂ hprefix
      obtain ⟨t, rfl⟩ := hprefix
      by_cases ht : t = []
      · subst ht; simp
      · have htdef : t ∈ translateDefined i alpha :=
          translateDefined_of_subset i alpha (fun e he => by simp [he]) ht h₂
        rw [translateMap_append i alpha l₁ t h₂ h₁ htdef]
        exact ⟨_, rfl⟩)
    (by
      rintro l h hnil
      have hlen : (translateMap i alpha l h).length = 0 := by rw [hnil]; rfl
      rw [translateMap_length] at hlen
      exact h.1 (List.length_eq_zero_iff.1 hlen))

@[simp]
theorem translate_defined (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)] (l : List (P × X)) :
    l ∈ (translate i alpha).defined ↔ l ∈ translateDefined i alpha := Iff.rfl

@[simp]
theorem translate_map (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    (l : List (P × X)) (h : l ∈ (translate i alpha).defined) :
    (translate i alpha).map l h = translateMap i alpha l h := rfl

/-- CR18 Definition 3.13: the post-α output transformation applied at the last
query of a history. If the last query is at the distinguished interface `i`, the
resource output is `α`'s outside output `αOuterOutput α x y'` (defaulting to the
raw `y'` when `α` does not emit one); otherwise it is the raw `s` output `y'`. -/
def attachOutput (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    (l : List (P × X)) (y' : Y) : Y :=
  match l.getLast? with
  | some (p, x) => if p = i then (αOuterOutput alpha x y').getD y' else y'
  | none => y'

/-- CR18 Definition 3.13: attach a `((X, Y), (X, Y))` converter `alpha` at
interface `i` of a resource `s : Resource P X Y`, **defined equationally**.

The system is `DDS.comap (translate α i) s` — `s` evaluated on the α-translated
resource history — with the post-α output transformation `attachOutput` applied to
its response. Inputs at interfaces `p ≠ i` pass through unchanged (`translateEntry`
is the identity there, `attachOutput` leaves the output alone); an input `(i, x)`
is rerouted to `α`'s single inner call and its output transformed by `α`. The
well-formedness obligations are inherited from `DDS.comap` — no `sorry`. -/
def attachAt (i : P) (alpha : DDC X Y X Y)
    (s : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] : Resource P X Y :=
  { DDS.comap (translate i alpha) s with
    respond := fun l h =>
      attachOutput i alpha l ((DDS.comap (translate i alpha) s).respond l h) }

@[simp]
theorem attachAt_dom (i : P) (alpha : DDC X Y X Y) (s : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] :
    (attachAt i alpha s).dom = (DDS.comap (translate i alpha) s).dom := rfl

/-- CR18 Definition 3.13: defining output equation for `αⁱs`. The output on a
history `l` is `α`'s post-output transformation of `s`'s response on the derived
(α-translated) history. -/
theorem attachAt_output_spec (i : P) (alpha : DDC X Y X Y) (s : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)]
    (l : List (P × X)) (h : l ∈ (attachAt i alpha s).dom) :
    (attachAt i alpha s).output l h =
      attachOutput i alpha l ((DDS.comap (translate i alpha) s).output l h) := rfl

/-- CR18 Definition 3.13: passthrough characterization. If the most recent input
is at an interface `p ≠ i`, then `αⁱs` agrees with the original resource `s` on
that history (the translation is the identity on the whole history, and the output
transformation is trivial). -/
theorem attachAt_passthrough (i : P) (alpha : DDC X Y X Y) (s : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] (pre : List (P × X)) (p : P)
    (x : X) (hp : p ≠ i)
    (htr : pre ++ [(p, x)] ∈ translateDefined i alpha)
    (hs : translateMap i alpha (pre ++ [(p, x)]) htr ∈ s.dom) :
    ∃ h : pre ++ [(p, x)] ∈ (attachAt i alpha s).dom,
      (attachAt i alpha s).output (pre ++ [(p, x)]) h =
        s.output (translateMap i alpha (pre ++ [(p, x)]) htr) hs := by
  have hdom : pre ++ [(p, x)] ∈ (attachAt i alpha s).dom := ⟨htr, hs⟩
  refine ⟨hdom, ?_⟩
  rw [attachAt_output_spec, comap_output (translate i alpha) s _ hdom htr hs]
  -- the last entry has interface `p ≠ i`, so `attachOutput` is the identity
  simp only [attachOutput, List.getLast?_concat, if_neg hp, translate_map]

/-- CR18 Definition 3.13: interface characterization. If the most recent input is
at the distinguished interface `i`, then `αⁱs` outputs `α`'s post-transform of
`s`'s response on the derived history. -/
theorem attachAt_interface (i : P) (alpha : DDC X Y X Y) (s : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)] (pre : List (P × X)) (x : X)
    (htr : pre ++ [(i, x)] ∈ translateDefined i alpha)
    (hs : translateMap i alpha (pre ++ [(i, x)]) htr ∈ s.dom) :
    ∃ h : pre ++ [(i, x)] ∈ (attachAt i alpha s).dom,
      (attachAt i alpha s).output (pre ++ [(i, x)]) h =
        (αOuterOutput alpha x
          (s.output (translateMap i alpha (pre ++ [(i, x)]) htr) hs)).getD
          (s.output (translateMap i alpha (pre ++ [(i, x)]) htr) hs) := by
  have hdom : pre ++ [(i, x)] ∈ (attachAt i alpha s).dom := ⟨htr, hs⟩
  refine ⟨hdom, ?_⟩
  rw [attachAt_output_spec, comap_output (translate i alpha) s _ hdom htr hs]
  -- the last entry has interface `i`, so `attachOutput` applies `α`'s output map
  simp only [attachOutput, List.getLast?_concat, if_true, translate_map]

/-!
### CR18 Lemma 3.1: distinct-interface attachments commute

With the equational coordinate-wise model, the converter translation
`translate i α` touches only interface-`i` entries and `translate j β` only
interface-`j` entries, so for `i ≠ j` they act on **disjoint coordinates** and
commute as list maps. Lemma 3.1 then follows by `DDS.ext`: the derived histories
on both sides coincide (`translateMap_comm`), the domain membership is invariant
under the other translation (tags are preserved), and the two output
transformations `attachOutput i α` / `attachOutput j β` are non-trivial on disjoint
last-interface tags.
-/

/-- The total (`getD`) form of one-entry translation. On a defined history this
agrees with `translateMap`'s entrywise action (see `translateMap_eq_map_getD`). -/
def translateEntryD (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)] (e : P × X) : P × X :=
  (translateEntry i alpha e).getD e

/-- Translation never changes an entry's interface tag. -/
theorem translateEntryD_fst (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)] (e : P × X) :
    (translateEntryD i alpha e).1 = e.1 := by
  unfold translateEntryD translateEntry
  by_cases hei : e.1 = i
  · simp only [hei, if_pos]
    cases αInnerInput alpha e.2 <;> simp [hei]
  · simp [hei]

/-- Translation at interface `i` fixes any entry whose tag is not `i`. -/
theorem translateEntryD_of_ne (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)] {e : P × X} (he : e.1 ≠ i) :
    translateEntryD i alpha e = e := by
  unfold translateEntryD translateEntry
  simp [he]

/-- **List-level commutation of the entry translations** for distinct interfaces:
`translate i α` and `translate j β` act on disjoint coordinates, so the
single-entry maps commute. -/
theorem translateEntryD_comm (i j : P) (hij : i ≠ j)
    (alpha beta : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ beta.system.dom)] (e : P × X) :
    translateEntryD i alpha (translateEntryD j beta e) =
      translateEntryD j beta (translateEntryD i alpha e) := by
  by_cases hei : e.1 = i
  · -- `e` is an `i`-entry: `translate j β` fixes it (tag `i ≠ j`).
    have hej : e.1 ≠ j := by rw [hei]; exact hij
    rw [translateEntryD_of_ne j beta hej]
    have : (translateEntryD i alpha e).1 ≠ j := by
      rw [translateEntryD_fst]; exact hej
    rw [translateEntryD_of_ne j beta this]
  · by_cases hej : e.1 = j
    · -- `e` is a `j`-entry: `translate i α` fixes it (tag `j ≠ i`).
      rw [translateEntryD_of_ne i alpha hei]
      have : (translateEntryD j beta e).1 ≠ i := by
        rw [translateEntryD_fst]; exact hei
      rw [translateEntryD_of_ne i alpha this]
    · -- `e` is at neither interface: both translations fix it.
      simp only [translateEntryD_of_ne i alpha hei, translateEntryD_of_ne j beta hej]

/-- An entry whose tag is not `i` always translates under `translate i α`
(passthrough). -/
theorem translateEntry_isSome_of_ne (i : P) (alpha : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)] {e : P × X} (he : e.1 ≠ i) :
    (translateEntry i alpha e).isSome := by
  simp [translateEntry, he]

/-- Whether an entry translates under `translate i α` is unaffected by first
translating it through the other interface `j` (`i ≠ j`): the two share the tag,
and only `i`-tagged entries can fail to translate. -/
theorem translateEntry_isSome_translateEntryD (i j : P) (hij : i ≠ j)
    (alpha beta : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ beta.system.dom)] (e : P × X) :
    (translateEntry i alpha (translateEntryD j beta e)).isSome =
      (translateEntry i alpha e).isSome := by
  by_cases hei : e.1 = i
  · -- `i`-entry: `translate j β` fixes it (tag `i ≠ j`).
    have hej : e.1 ≠ j := by rw [hei]; exact hij
    rw [translateEntryD_of_ne j beta hej]
  · -- non-`i`-entry: both passthrough, both `some`.
    have htag : (translateEntryD j beta e).1 = e.1 := translateEntryD_fst j beta e
    rw [translateEntry_isSome_of_ne i alpha (by rw [htag]; exact hei),
        translateEntry_isSome_of_ne i alpha hei]

/-- `translateDefined` membership is invariant under the other-interface
translation: applying `translate j β` to a history does not change whether every
entry translates under `translate i α` (tags are preserved and a `j`-entry always
passes through `translate i α`). -/
theorem translateDefined_map_iff (i j : P) (hij : i ≠ j)
    (alpha beta : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ beta.system.dom)]
    (l : List (P × X)) (hj : l ∈ translateDefined j beta) :
    translateMap j beta l hj ∈ translateDefined i alpha ↔
      l ∈ translateDefined i alpha := by
  rw [translateMap_eq_map_getD]
  simp only [translateDefined, Set.mem_setOf_eq, ne_eq, List.forall_mem_map]
  -- after `forall_mem_map`, the hypothesis quantifies over `e ∈ l` with the
  -- `translateEntryD j β`-image; each `isSome` matches via the lemma above.
  have hmapne : List.map (fun e => (translateEntry j beta e).getD e) l ≠ [] := by
    simpa using hj.1
  constructor
  · rintro ⟨_, hall⟩
    refine ⟨hj.1, fun e he => ?_⟩
    have := hall e he
    rwa [← translateEntryD, translateEntry_isSome_translateEntryD i j hij alpha beta e]
      at this
  · rintro ⟨_, hall⟩
    refine ⟨hmapne, fun e he => ?_⟩
    rw [← translateEntryD, translateEntry_isSome_translateEntryD i j hij alpha beta e]
    exact hall e he

/-- **The derived histories coincide**: for `i ≠ j`, translating by `j` then `i`
gives the same resource history as translating by `i` then `j`. This is the
list-level heart of Lemma 3.1. -/
theorem translateMap_comm (i j : P) (hij : i ≠ j)
    (alpha beta : DDC X Y X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ beta.system.dom)]
    (l : List (P × X))
    (hj : l ∈ translateDefined j beta) (hi : l ∈ translateDefined i alpha)
    (hij' : translateMap j beta l hj ∈ translateDefined i alpha)
    (hji' : translateMap i alpha l hi ∈ translateDefined j beta) :
    translateMap i alpha (translateMap j beta l hj) hij' =
      translateMap j beta (translateMap i alpha l hi) hji' := by
  rw [translateMap_eq_map_getD, translateMap_eq_map_getD,
      translateMap_eq_map_getD, translateMap_eq_map_getD,
      List.map_map, List.map_map]
  apply List.map_congr_left
  intro e _
  exact translateEntryD_comm i j hij alpha beta e

/-- Membership characterization of an attachment's domain: a history is accepted
by `αⁱS` exactly when it translates under `translate i α` and its translated image
is accepted by the inner system `S`. -/
theorem mem_attachAt_dom_iff (i : P) (alpha : DDC X Y X Y) (S : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ S.dom)] (l : List (P × X)) :
    l ∈ (attachAt i alpha S).dom ↔
      ∃ h : l ∈ translateDefined i alpha, translateMap i alpha l h ∈ S.dom := by
  rw [attachAt_dom, comap_dom]; rfl

/-- The translated image used by `attachAt`, made independent of the membership
proof (proof irrelevance). -/
theorem attachAt_respond_eq (i : P) (alpha : DDC X Y X Y) (S : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ S.dom)] (l : List (P × X))
    (h : l ∈ (attachAt i alpha S).dom)
    (htr : l ∈ translateDefined i alpha) (hin : translateMap i alpha l htr ∈ S.dom) :
    (attachAt i alpha S).output l h =
      attachOutput i alpha l (S.output (translateMap i alpha l htr) hin) := by
  rw [attachAt_output_spec, comap_output (translate i alpha) S l h htr hin]
  rfl

/-- CR18 Lemma 3.1: appending converters at **distinct** interfaces commutes,
`αⁱβʲs = βʲαⁱs`. CR18 states this lemma without proof.

The equational model makes it a list-level fact: `translate i α` and
`translate j β` act on disjoint coordinates (`i ≠ j`), so the derived histories
coincide (`translateMap_comm`), domain membership is invariant under the other
translation (`translateDefined_map_iff`), and the output transformations are
non-trivial only on disjoint last-interface tags. -/
theorem attachAt_comm (i j : P) (hij : i ≠ j)
    (alpha beta : DDC X Y X Y) (s : Resource P X Y)
    [DecidablePred (fun l => l ∈ alpha.system.dom)]
    [DecidablePred (fun l => l ∈ beta.system.dom)]
    [DecidablePred (fun l => l ∈ s.dom)]
    [DecidablePred (fun l => l ∈ (attachAt j beta s).dom)]
    [DecidablePred (fun l => l ∈ (attachAt i alpha s).dom)] :
    attachAt i alpha (attachAt j beta s) =
      attachAt j beta (attachAt i alpha s) := by
  -- The last-interface tag of the input history `l` determines which output
  -- transform fires; `translate` preserves tags, so `attachOutput k _ (T_ l)` sees
  -- the same last tag as `attachOutput k _ l`. Combined with `translateMap_comm`,
  -- the two compositions agree pointwise.
  apply DDS.ext
  · -- domain equality
    ext l
    simp only [mem_attachAt_dom_iff]
    constructor
    · -- LHS: `l ∈ Di`, `Ti l ∈ Dj`, `Tj (Ti l) ∈ s.dom`
      rintro ⟨hi, hjT, hs⟩
      have hj : l ∈ translateDefined j beta :=
        (translateDefined_map_iff j i hij.symm beta alpha l hi).1 hjT
      have hiT : translateMap j beta l hj ∈ translateDefined i alpha :=
        (translateDefined_map_iff i j hij alpha beta l hj).2 hi
      refine ⟨hj, hiT, ?_⟩
      rwa [translateMap_comm i j hij alpha beta l hj hi hiT hjT]
    · -- RHS: `l ∈ Dj`, `Tj l ∈ Di`, `Ti (Tj l) ∈ s.dom`
      rintro ⟨hj, hiT, hs⟩
      have hi : l ∈ translateDefined i alpha :=
        (translateDefined_map_iff i j hij alpha beta l hj).1 hiT
      have hjT : translateMap i alpha l hi ∈ translateDefined j beta :=
        (translateDefined_map_iff j i hij.symm beta alpha l hi).2 hj
      refine ⟨hi, hjT, ?_⟩
      rwa [← translateMap_comm i j hij alpha beta l hj hi hiT hjT]
  · -- output equality
    intro l hL hR
    -- unpack each side: outer-translate proof, inner-translate proof, `s`-membership
    obtain ⟨hi, hin⟩ := (mem_attachAt_dom_iff i alpha (attachAt j beta s) l).1 hL
    obtain ⟨hjT, hsL⟩ := (mem_attachAt_dom_iff j beta s (translateMap i alpha l hi)).1 hin
    obtain ⟨hj, hin'⟩ := (mem_attachAt_dom_iff j beta (attachAt i alpha s) l).1 hR
    obtain ⟨hiT, hsR⟩ := (mem_attachAt_dom_iff i alpha s (translateMap j beta l hj)).1 hin'
    -- expand both outputs: outer transform of inner transform of `s`'s response.
    rw [attachAt_respond_eq i alpha (attachAt j beta s) l hL hi hin,
        attachAt_respond_eq j beta s (translateMap i alpha l hi) hin hjT hsL,
        attachAt_respond_eq j beta (attachAt i alpha s) l hR hj hin',
        attachAt_respond_eq i alpha s (translateMap j beta l hj) hin' hiT hsR]
    -- the doubly-translated histories coincide, so `s`'s responses coincide.
    have hcomm : translateMap j beta (translateMap i alpha l hi) hjT =
        translateMap i alpha (translateMap j beta l hj) hiT :=
      (translateMap_comm i j hij alpha beta l hj hi hiT hjT).symm
    have hv : s.output (translateMap j beta (translateMap i alpha l hi) hjT) hsL =
        s.output (translateMap i alpha (translateMap j beta l hj) hiT) hsR :=
      DDS.respond_congr s hcomm hsL hsR
    rw [hv]
    -- it remains to commute the two `attachOutput` transforms; their fired branch
    -- is selected by `l`'s last interface tag, and `translate` preserves tags.
    set v := s.output (translateMap i alpha (translateMap j beta l hj) hiT) hsR with hvdef
    -- last entry of `translateMap _ l _` shares `l`'s last interface tag
    have htagI : (translateMap i alpha l hi).getLast? =
        (l.getLast?).map (translateEntryD i alpha) := by
      rw [translateMap_eq_map_getD]; rw [List.getLast?_map]; rfl
    have htagJ : (translateMap j beta l hj).getLast? =
        (l.getLast?).map (translateEntryD j beta) := by
      rw [translateMap_eq_map_getD]; rw [List.getLast?_map]; rfl
    -- `attachOutput k _ (T l) = attachOutput k _ l` when the relevant tag is unchanged
    cases hlast : l.getLast? with
    | none =>
        simp [attachOutput, htagI, htagJ, hlast]
    | some e =>
        rcases e with ⟨p, x⟩
        simp only [attachOutput, htagI, htagJ, hlast, Option.map_some,
          translateEntryD_fst]
        by_cases hpi : p = i
        · -- last is at `i`: `αⁱ` fires; `βʲ` is the identity here (`i ≠ j`)
          subst hpi
          have hji : p ≠ j := hij
          -- `translateEntryD j β (p,x) = (p,x)` since `p ≠ j`, so its payload is `x`
          have hpx : translateEntryD j beta (p, x) = (p, x) :=
            translateEntryD_of_ne j beta (by simpa using hji)
          simp only [if_neg hji, hpx]
        · by_cases hpj : p = j
          · -- last is at `j`: `βʲ` fires; `αⁱ` is the identity here (`i ≠ j`)
            subst hpj
            have hij' : p ≠ i := fun h => hij (h ▸ rfl)
            have hpx : translateEntryD i alpha (p, x) = (p, x) :=
              translateEntryD_of_ne i alpha (by simpa using hij')
            simp only [if_neg hij', hpx]
          · -- last is at neither: both transforms are the identity
            simp [hpi, hpj]

end DDS

end RandomSystems.CR18
