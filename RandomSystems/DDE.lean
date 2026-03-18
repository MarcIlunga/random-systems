/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.DDS

/-!
# Deterministic Discrete Environments (DDE)

Lean 4 formalization of Definition 6 from Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `DDE X Y q` — a deterministic environment making `q` queries
* `DDE.nonadaptive` — a non-adaptive environment (fixed input sequence)

## Design Notes

A DDE is the "dual" of a DDS: it chooses the next input based on all
previous outputs. The pair (DDS, DDE) determines a transcript.

For proving equivalence (Lemma 5), non-adaptive environments suffice,
so `DDE.nonadaptive` is the primary constructor in practice.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

/-- A Deterministic Discrete Environment making `q` queries.

Paper Definition 6: An environment `e : Y* → X` chooses the next
input based on all previous outputs.

For the i-th query, the environment sees the previous `i` outputs
`(y₁, ..., yᵢ)` and produces the next input `xᵢ₊₁`. -/
structure DDE (X : Type*) (Y : Type*) (q : ℕ) where
  /-- Given query index `i` and previous outputs `(y₁, ..., yᵢ)`,
      choose the next input `xᵢ₊₁`. -/
  choose : (i : Fin q) → (Fin i.val → Y) → X

namespace DDE

variable {X Y : Type*} {q : ℕ}

/-- The canonical equivalence between DDE and its underlying choice function type. -/
def equivChoose (X Y : Type*) (q : ℕ) :
    DDE X Y q ≃ ((i : Fin q) → (Fin i.val → Y) → X) where
  toFun e := e.choose
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- DDE is `Fintype` when X and Y are `Fintype` (and Y has decidable equality).

We need `DecidableEq Y` because environments take as input a function `Fin i → Y`,
and `Fintype` for function spaces in Mathlib is defined via `Fintype.piFinset`,
which requires decidable equality on the index type. -/
instance instFintype [Fintype X] [Fintype Y] [DecidableEq Y] :
    Fintype (DDE X Y q) :=
  Fintype.ofEquiv _ (equivChoose X Y q).symm

/-- Two DDE are equal iff they agree on all choices. -/
@[ext]
theorem ext {e₁ e₂ : DDE X Y q} (h : e₁.choose = e₂.choose) : e₁ = e₂ := by
  cases e₁; cases e₂; simp_all

/-- Precompose an environment with an output map.

If `e` expects outputs of type `Y`, then `mapOutput g e` expects outputs of type `Y'`
and feeds `g (·)` into `e`. This is the environment-side analogue of "dropping trace
information" in instrumented systems. -/
def mapOutput {Y' : Type*} (g : Y' → Y) (e : DDE X Y q) : DDE X Y' q where
  choose := fun i prevOutputs => e.choose i (fun j => g (prevOutputs j))

/-- A non-adaptive environment: the input sequence is fixed in advance,
independent of the system's outputs.

Paper Lemma 5 shows that non-adaptive environments suffice for
checking PDS equivalence. -/
def nonadaptive (inputs : Fin q → X) : DDE X Y q where
  choose := fun i _ => inputs i

/-- The successor environment: after the first query, shift indices.
Dual to `DDS.successor`. -/
def successor (e : DDE X Y (q + 1)) (y₁ : Y) : DDE X Y q where
  choose := fun i prevOutputs =>
    e.choose ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      (Fin.cons y₁ prevOutputs ∘ Fin.cast (by simp))

end DDE

end RandomSystems
