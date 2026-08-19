/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Legacy.Equiv

/-!
# Heterogeneous Constructions

The `RandomSystems.Construction` API models *homogeneous* constructions:

`(Fin n → PDS X Y q) → PDS X' Y' q'`.

For software verification and CC-style modular reasoning, dependencies are often **heterogeneous**
(different APIs). This file provides a lightweight generalization:

`(∀ i : I, PDS (X i) (Y i) (q i)) → PDS X' Y' q'`.

Intended interpretation:
- a *library/module implementation* is a construction that wires calls to its dependencies,
  injects constants, and sequences function calls;
- a *constant* is a construction with no dependencies (index type `Empty`);
- chaining libraries corresponds to **substituting** one construction into another.
-/

noncomputable section

namespace RandomSystems

universe uI uJ u

/-- A heterogeneous construction: a map from a family of PDS (indexed by `I`, each with its own
input/output alphabets and query bound) to a single output PDS, respecting PDS equivalence in each
component. -/
structure HConstruction
    {I : Type uI}
    (X Y : I → Type u) (q : I → ℕ)
    (X' Y' : Type u) (q' : ℕ)
    [∀ i, Fintype (DDS (X i) (Y i) (q i))]
    [∀ i, Fintype (Transcript (X i) (Y i) (q i))]
    [∀ i, DecidableEq (Transcript (X i) (Y i) (q i))]
    [Fintype (DDS X' Y' q')]
    [Fintype (Transcript X' Y' q')]
    [DecidableEq (Transcript X' Y' q')] where
  /-- The construction map. -/
  apply : (∀ i : I, PDS (X i) (Y i) (q i)) → PDS X' Y' q'
  /-- The construction respects equivalence. -/
  respects_equiv :
    ∀ (Ss Ts : ∀ i : I, PDS (X i) (Y i) (q i)),
      (∀ i, Ss i ≡ₚ Ts i) →
      apply Ss ≡ₚ apply Ts

namespace HConstruction

variable {I : Type uI} {J : Type uJ}

variable {X₁ Y₁ : I → Type u} {q₁ : I → ℕ}
variable {X₂ Y₂ : J → Type u} {q₂ : J → ℕ}

variable {Xm Ym : Type u} {qm : ℕ}
variable {Xo Yo : Type u} {qo : ℕ}

variable
  [∀ i, Fintype (DDS (X₁ i) (Y₁ i) (q₁ i))]
  [∀ i, Fintype (Transcript (X₁ i) (Y₁ i) (q₁ i))]
  [∀ i, DecidableEq (Transcript (X₁ i) (Y₁ i) (q₁ i))]

variable
  [∀ j, Fintype (DDS (X₂ j) (Y₂ j) (q₂ j))]
  [∀ j, Fintype (Transcript (X₂ j) (Y₂ j) (q₂ j))]
  [∀ j, DecidableEq (Transcript (X₂ j) (Y₂ j) (q₂ j))]

variable
  [Fintype (DDS Xm Ym qm)]
  [Fintype (Transcript Xm Ym qm)]
  [DecidableEq (Transcript Xm Ym qm)]

variable
  [Fintype (DDS Xo Yo qo)]
  [Fintype (Transcript Xo Yo qo)]
  [DecidableEq (Transcript Xo Yo qo)]

/-- Instance helper: build per-index typeclass instances for `Sum Unit J` by cases. -/
instance instDDS_sumUnit :
    ∀ s : Sum Unit J,
      Fintype
        (DDS
          (match s with | .inl _ => Xm | .inr j => X₂ j)
          (match s with | .inl _ => Ym | .inr j => Y₂ j)
          (match s with | .inl _ => qm | .inr j => q₂ j)) := by
  intro s; cases s with
  | inl _ => infer_instance
  | inr _ => infer_instance

instance instTranscript_sumUnit :
    ∀ s : Sum Unit J,
      Fintype
        (Transcript
          (match s with | .inl _ => Xm | .inr j => X₂ j)
          (match s with | .inl _ => Ym | .inr j => Y₂ j)
          (match s with | .inl _ => qm | .inr j => q₂ j)) := by
  intro s; cases s with
  | inl _ => infer_instance
  | inr _ => infer_instance

instance instDecEqTranscript_sumUnit :
    ∀ s : Sum Unit J,
      DecidableEq
        (Transcript
          (match s with | .inl _ => Xm | .inr j => X₂ j)
          (match s with | .inl _ => Ym | .inr j => Y₂ j)
          (match s with | .inl _ => qm | .inr j => q₂ j)) := by
  intro s; cases s with
  | inl _ => infer_instance
  | inr _ => infer_instance

/-- Instance helper: build per-index typeclass instances for `Sum I J` by cases. -/
instance instDDS_sum :
    ∀ s : Sum I J,
      Fintype
        (DDS
          (match s with | .inl i => X₁ i | .inr j => X₂ j)
          (match s with | .inl i => Y₁ i | .inr j => Y₂ j)
          (match s with | .inl i => q₁ i | .inr j => q₂ j)) := by
  intro s; cases s with
  | inl _ => infer_instance
  | inr _ => infer_instance

instance instTranscript_sum :
    ∀ s : Sum I J,
      Fintype
        (Transcript
          (match s with | .inl i => X₁ i | .inr j => X₂ j)
          (match s with | .inl i => Y₁ i | .inr j => Y₂ j)
          (match s with | .inl i => q₁ i | .inr j => q₂ j)) := by
  intro s; cases s with
  | inl _ => infer_instance
  | inr _ => infer_instance

instance instDecEqTranscript_sum :
    ∀ s : Sum I J,
      DecidableEq
        (Transcript
          (match s with | .inl i => X₁ i | .inr j => X₂ j)
          (match s with | .inl i => Y₁ i | .inr j => Y₂ j)
          (match s with | .inl i => q₁ i | .inr j => q₂ j)) := by
  intro s; cases s with
  | inl _ => infer_instance
  | inr _ => infer_instance

/-- Substitute a construction into the distinguished dependency of another construction.

This captures “software wiring” / converter composition:

- `C₁` builds an intermediate component from dependencies indexed by `I`.
- `C₂` builds the final system from the intermediate component (as the `Unit`-indexed dependency)
  plus extra dependencies indexed by `J`.

The result is a construction from the combined dependencies `Sum I J`. -/
def subst
    (C₁ : HConstruction X₁ Y₁ q₁ Xm Ym qm)
    (C₂ :
      HConstruction
        (X := fun s : Sum Unit J => match s with | .inl _ => Xm | .inr j => X₂ j)
        (Y := fun s : Sum Unit J => match s with | .inl _ => Ym | .inr j => Y₂ j)
        (q := fun s : Sum Unit J => match s with | .inl _ => qm | .inr j => q₂ j)
        Xo Yo qo) :
    HConstruction
      (X := fun s : Sum I J => match s with | .inl i => X₁ i | .inr j => X₂ j)
      (Y := fun s : Sum I J => match s with | .inl i => Y₁ i | .inr j => Y₂ j)
      (q := fun s : Sum I J => match s with | .inl i => q₁ i | .inr j => q₂ j)
      Xo Yo qo where
  apply := fun Ss =>
    let SsI : ∀ i : I, PDS (X₁ i) (Y₁ i) (q₁ i) := fun i => Ss (.inl i)
    let SsJ : ∀ j : J, PDS (X₂ j) (Y₂ j) (q₂ j) := fun j => Ss (.inr j)
    let mid : PDS Xm Ym qm := C₁.apply SsI
    let deps₂ : ∀ s : Sum Unit J, PDS (match s with | .inl _ => Xm | .inr j => X₂ j)
        (match s with | .inl _ => Ym | .inr j => Y₂ j)
        (match s with | .inl _ => qm | .inr j => q₂ j) :=
      fun s =>
        match s with
        | .inl _ => mid
        | .inr j => SsJ j
    C₂.apply deps₂
  respects_equiv := by
    intro Ss Ts hST
    have hI : ∀ i : I, (Ss (.inl i)) ≡ₚ (Ts (.inl i)) := fun i => hST (.inl i)
    have hJ : ∀ j : J, (Ss (.inr j)) ≡ₚ (Ts (.inr j)) := fun j => hST (.inr j)

    let SsI : ∀ i : I, PDS (X₁ i) (Y₁ i) (q₁ i) := fun i => Ss (.inl i)
    let TsI : ∀ i : I, PDS (X₁ i) (Y₁ i) (q₁ i) := fun i => Ts (.inl i)
    have h_mid : C₁.apply SsI ≡ₚ C₁.apply TsI := C₁.respects_equiv SsI TsI hI

    let SsJ : ∀ j : J, PDS (X₂ j) (Y₂ j) (q₂ j) := fun j => Ss (.inr j)
    let TsJ : ∀ j : J, PDS (X₂ j) (Y₂ j) (q₂ j) := fun j => Ts (.inr j)

    let deps₂S : ∀ s : Sum Unit J, PDS (match s with | .inl _ => Xm | .inr j => X₂ j)
        (match s with | .inl _ => Ym | .inr j => Y₂ j)
        (match s with | .inl _ => qm | .inr j => q₂ j) :=
      fun s =>
        match s with
        | .inl _ => C₁.apply SsI
        | .inr j => SsJ j

    let deps₂T : ∀ s : Sum Unit J, PDS (match s with | .inl _ => Xm | .inr j => X₂ j)
        (match s with | .inl _ => Ym | .inr j => Y₂ j)
        (match s with | .inl _ => qm | .inr j => q₂ j) :=
      fun s =>
        match s with
        | .inl _ => C₁.apply TsI
        | .inr j => TsJ j

    have h_deps₂ : ∀ s, deps₂S s ≡ₚ deps₂T s := by
      intro s
      cases s with
      | inl u =>
          -- distinguished dependency: the intermediate construction
          cases u
          simpa using h_mid
      | inr j =>
          -- extra dependencies: forwarded unchanged
          simpa [deps₂S, deps₂T] using hJ j

    exact C₂.respects_equiv deps₂S deps₂T h_deps₂

end HConstruction

end RandomSystems
