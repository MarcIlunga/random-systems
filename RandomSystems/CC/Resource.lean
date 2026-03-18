/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Equiv

/-!
# Constructive Cryptography: Resources and Converters

Lean 4 formalization of the core objects from Maurer's Constructive
Cryptography paradigm (Maurer 2011, Maurer-Renner 2011).

## Main Definitions

* `CCResource` — a multi-interface resource: indexed family of PDS
* `Converter` — a map on PDS that respects equivalence
* `applyConverter` — attach a converter at a single interface
* `CCResource.equiv` — equivalence of CC resources (pointwise PDS equivalence)

## Main Results

* `converter_commutativity` — converters at distinct interfaces commute (FREE)
* `applyConverter_preserves_equiv` — converter application preserves equivalence

## Design Notes

A CC resource has `n` interfaces, each with its own input/output types and
query count. A converter transforms one interface's PDS to another PDS
(possibly with different types). Application at interface `i` uses
`Function.update`, giving commutativity for free via `Function.update_comm`.

References:
- Maurer, "Constructive Cryptography — A New Paradigm" (2011), Definition 1
- Maurer-Renner, "Abstract Cryptography" (2011), Definition 14
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

namespace CC

variable {n : ℕ}

/-! ### Resources -/

/-- A Constructive Cryptography resource: an indexed family of PDS, one per interface.

Maurer's abstract algebra ⟨Φ, Σ, ≈⟩ — this is the carrier Φ.
Each interface `i : Fin n` has its own input type `X i`, output type `Y i`,
and query bound `q i`. -/
def CCResource
    (X Y : Fin n → Type*) (q : Fin n → ℕ)
    [inst : ∀ i, Fintype (DDS (X i) (Y i) (q i))] :=
  (i : Fin n) → PDS (X i) (Y i) (q i)

variable {X Y : Fin n → Type*} {q : Fin n → ℕ}
  [inst : ∀ i, Fintype (DDS (X i) (Y i) (q i))]
  [instT : ∀ i, Fintype (Transcript (X i) (Y i) (q i))]
  [instD : ∀ i, DecidableEq (Transcript (X i) (Y i) (q i))]

/-! ### Resource Equivalence -/

/-- Two CC resources are equivalent if they are pointwise PDS-equivalent.

This lifts PDS equivalence (Definition 10) to the multi-interface setting. -/
def CCResource.equiv
    (R S : CCResource X Y q) : Prop :=
  ∀ i, R i ≡ₚ S i

scoped notation:50 R " ≡ᵣ " S => CCResource.equiv R S

/-- Resource equivalence is reflexive. -/
theorem CCResource.equiv_refl (R : CCResource X Y q) : R ≡ᵣ R :=
  fun i => PDS.equiv_refl (R i)

/-- Resource equivalence is symmetric. -/
theorem CCResource.equiv_symm {R S : CCResource X Y q}
    (h : R ≡ᵣ S) : S ≡ᵣ R :=
  fun i => PDS.equiv_symm (h i)

/-- Resource equivalence is transitive. -/
theorem CCResource.equiv_trans {R S T : CCResource X Y q}
    (h₁ : R ≡ᵣ S) (h₂ : S ≡ᵣ T) : R ≡ᵣ T :=
  fun i => PDS.equiv_trans (h₁ i) (h₂ i)

/-! ### Converters -/

/-- A converter: a map on PDS at a single interface that respects equivalence.

Maurer's converter algebra Σ. A converter transforms the PDS at one
interface, e.g., an encryption protocol transforms a plaintext channel
into a ciphertext channel. -/
structure Converter
    (Xi Yi : Type*) (qi : ℕ)
    [Fintype (DDS Xi Yi qi)]
    [Fintype (Transcript Xi Yi qi)]
    [DecidableEq (Transcript Xi Yi qi)] where
  /-- The underlying transformation on PDS. -/
  apply : PDS Xi Yi qi → PDS Xi Yi qi
  /-- The transformation respects PDS equivalence. -/
  respects_equiv :
    ∀ (S T : PDS Xi Yi qi),
      (∀ inputs, S.transcriptDist inputs = T.transcriptDist inputs) →
      ∀ inputs, (apply S).transcriptDist inputs = (apply T).transcriptDist inputs

/-! ### Converter Application -/

/-- Apply a converter at interface `i` of a resource.

This replaces the PDS at interface `i` with `conv.apply (R i)`,
leaving all other interfaces unchanged. Uses `Function.update`. -/
def applyConverter
    (i : Fin n)
    (conv : Converter (X i) (Y i) (q i))
    (R : CCResource X Y q) : CCResource X Y q :=
  Function.update R i (conv.apply (R i))

/-! ### Core Theorems -/

/-- Converters at distinct interfaces commute.

This is the key structural property of CC: protocol steps at different
interfaces can be applied in any order. The proof is trivial via
`Function.update_comm`, which is the payoff of our `Fin n` + `Function.update`
design.

Maurer 2011, Section 2.3: "The converter application αⁱ and βʲ commute
for i ≠ j." -/
theorem converter_commutativity
    {i j : Fin n} (hij : i ≠ j)
    (ci : Converter (X i) (Y i) (q i))
    (cj : Converter (X j) (Y j) (q j))
    (R : CCResource X Y q) :
    applyConverter i ci (applyConverter j cj R) =
    applyConverter j cj (applyConverter i ci R) := by
  unfold applyConverter
  have h1 : Function.update R j (cj.apply (R j)) i = R i := by
    rw [Function.update_of_ne hij]
  have h2 : Function.update R i (ci.apply (R i)) j = R j := by
    rw [Function.update_of_ne (Ne.symm hij)]
  rw [h1, h2, Function.update_comm hij]

/-- Applying a converter preserves resource equivalence.

If R ≡ᵣ S and conv respects PDS equivalence, then
  applyConverter i conv R ≡ᵣ applyConverter i conv S.

Maurer 2011: "d(αⁱR, αⁱS) ≤ d(R, S)" — the metric compatibility axiom
for converter application. -/
theorem applyConverter_preserves_equiv
    (i : Fin n)
    (conv : Converter (X i) (Y i) (q i))
    {R S : CCResource X Y q}
    (h : R ≡ᵣ S) :
    applyConverter i conv R ≡ᵣ applyConverter i conv S := by
  intro k
  simp only [applyConverter]
  by_cases hik : k = i
  · subst hik
    rw [Function.update_self, Function.update_self]
    exact conv.respects_equiv _ _ (h _)
  · rw [Function.update_of_ne hik, Function.update_of_ne hik]
    exact h k

/-- The identity converter: does nothing. -/
def Converter.id
    (Xi Yi : Type*) (qi : ℕ)
    [Fintype (DDS Xi Yi qi)]
    [Fintype (Transcript Xi Yi qi)]
    [DecidableEq (Transcript Xi Yi qi)] : Converter Xi Yi qi where
  apply := fun S => S
  respects_equiv := fun _ _ h => h

/-- Composing two converters yields a converter. -/
def Converter.comp
    {Xi Yi : Type*} {qi : ℕ}
    [Fintype (DDS Xi Yi qi)]
    [Fintype (Transcript Xi Yi qi)]
    [DecidableEq (Transcript Xi Yi qi)]
    (c₁ c₂ : Converter Xi Yi qi) : Converter Xi Yi qi where
  apply := c₁.apply ∘ c₂.apply
  respects_equiv := fun _ _ h => c₁.respects_equiv _ _ (c₂.respects_equiv _ _ h)

/-- Applying the identity converter is a no-op. -/
theorem applyConverter_id
    (i : Fin n)
    (R : CCResource X Y q) :
    applyConverter i (Converter.id (X i) (Y i) (q i)) R = R := by
  simp [applyConverter, Converter.id, Function.update_eq_self]

end CC

end RandomSystems
