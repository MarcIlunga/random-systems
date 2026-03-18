/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DDS
import RandomSystems.DDE

/-!
# Transcripts

Lean 4 formalization of Definition 7 from Lanzenberger-Maurer (TCC 2020).

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

end RandomSystems
