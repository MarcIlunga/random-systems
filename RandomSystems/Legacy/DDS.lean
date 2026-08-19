/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Dist

/-!
# Deterministic Discrete Systems (DDS)

Lean 4 formalization of Definition 5 and Notation 2 from
Lanzenberger-Maurer (TCC 2020).

## Main Definitions

* `DDS X Y q` — an (X,Y)-DDS answering at most `q` queries
* `DDS.ofFun` — single-query DDS from `X → Y`
* `DDS.firstQuery` — extract the first-query function
* `DDS.successor` — the successor operation `s^{↑x↓y}` (Notation 2)
* `DDS.transcript` — non-adaptive transcript (Definition 7, simplified)

## Design Notes

The i-th response of a DDS depends on inputs `(x₁, ..., x_{i+1})`.
This makes prefix-closure automatic from the type.

The successor operation `s^{↑x}` (paper Notation 2) prepends `x` to the
input sequence: `s^{↑x}(x̂ⁱ) := s(x | x̂ⁱ)`. This is the key proof
technique for the inductive proof of Theorem 1.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems

/-- An (X, Y)-DDS answering at most `q` queries.

Paper Definition 5: A DDS is a partial function `s : X⁺ → Y` with
prefix-closed domain. We model this for a fixed query bound `q`:
given the first `i+1` inputs `(x₁,...,x_{i+1})`, produce the
`(i+1)`-th output `yᵢ₊₁`.

The type ensures prefix-closure: the `i`-th response can depend on
all inputs up to position `i`. -/
structure DDS (X : Type*) (Y : Type*) (q : ℕ) where
  /-- Given query index `i` and input history `(x₁,...,x_{i+1})`,
      produce the `(i+1)`-th output. -/
  respond : (i : Fin q) → (Fin (i.val + 1) → X) → Y

namespace DDS

variable {X Y : Type*} {q : ℕ}

/-- `DDS X Y q` is inhabited whenever the response alphabet `Y` is (use the
constant responder).  Declared globally so the `Dist`-over-`DDS` API — which now
requires `[Nonempty]` carriers — resolves `Nonempty (DDS X Y q)` automatically. -/
instance instNonempty [Nonempty Y] : Nonempty (DDS X Y q) :=
  ⟨⟨fun _ _ => ‹Nonempty Y›.some⟩⟩

/-- The canonical equivalence between DDS and its underlying function type. -/
def equivRespond (X Y : Type*) (q : ℕ) :
    DDS X Y q ≃ ((i : Fin q) → (Fin (i.val + 1) → X) → Y) where
  toFun s := s.respond
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- DDS is Fintype when X and Y are Fintype (and X has DecidableEq). -/
instance instFintype [Fintype X] [DecidableEq X] [Fintype Y] :
    Fintype (DDS X Y q) :=
  Fintype.ofEquiv _ (equivRespond X Y q).symm

/-- DDS has decidable equality when X and Y do (and both are Fintype). -/
instance instDecidableEq [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    DecidableEq (DDS X Y q) :=
  Equiv.decidableEq (equivRespond X Y q)

/-- Two DDS are equal iff they agree on all queries. -/
@[ext]
theorem ext {s t : DDS X Y q} (h : s.respond = t.respond) : s = t := by
  cases s; cases t; simp_all

/-- Single-query DDS from a function `f : X → Y`.
The unique query receives exactly one input. -/
def ofFun (f : X → Y) : DDS X Y 1 where
  respond := fun ⟨0, _⟩ inputs => f (inputs ⟨0, Nat.zero_lt_one⟩)

/-- Stateless q-query DDS from a function `f : X → Y`.

At each query, the system returns `f` applied to the *current* input and ignores
the history. This is the natural embedding of (random) functions into DDS. -/
def ofFunq (f : X → Y) : DDS X Y q where
  respond := fun i inputs => f (inputs ⟨i, Nat.lt_succ_iff.mpr le_rfl⟩)

/-- Extract the first-query function from any DDS.
`firstQuery s x = s.respond 0 (fun _ => x)`. -/
def firstQuery (s : DDS X Y q) (hq : 0 < q) : X → Y :=
  fun x => s.respond ⟨0, hq⟩ (fun _ => x)

/-- The non-adaptive transcript of a DDS `s` with fixed input sequence.

For each query `i`, the transcript records the input-output pair
`(inputs i, s.respond i (inputs₀, ..., inputsᵢ))`.

Paper Definition 7 (simplified for non-adaptive case). -/
def transcript (s : DDS X Y q) (inputs : Fin q → X) : Fin q → X × Y :=
  fun i => (inputs i,
    s.respond i (fun j => inputs ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩))

/-- The successor operation: given a DDS `s` and a first input-output pair
`(x, y)`, produce the DDS `s^{↑x↓y}` that answers `q-1` queries.

Paper Notation 2: `s^{↑x}(x̂ⁱ) := s(x | x̂ⁱ)`, where `x | x̂ⁱ`
is the concatenation of `x` with `x̂ⁱ`.

We require `y = s.respond 0 (fun _ => x)` externally; here we just
shift the indices.

The successor of a q-query DDS is a (q-1)-query DDS. -/
def successor (s : DDS X Y (q + 1)) (x : X) : DDS X Y q where
  respond := fun i inputs =>
    s.respond ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      (Fin.cons x inputs ∘ Fin.cast (by simp))

/-- Reconstruct a (q+1)-query DDS from a first-query function and successor family.

This is the inverse of the successor decomposition: given `f : X → Y` for the
first query and `g : X → DDS X Y q` for the successor at each first input,
build the full (q+1)-query system. -/
def reconstruct (f : X → Y) (g : X → DDS X Y q) : DDS X Y (q + 1) where
  respond := fun i inputs =>
    if h : i.val = 0 then
      f (inputs ⟨0, by omega⟩)
    else
      have hi' : i.val - 1 < q := by omega
      (g (inputs ⟨0, by omega⟩)).respond ⟨i.val - 1, hi'⟩
        (fun (j : Fin (i.val - 1 + 1)) => inputs ⟨j.val + 1, by
          have := j.isLt; have := i.isLt; omega⟩)

/-- Helper: respond depends only on the Nat values, not the proofs. -/
theorem respond_congr_val (s : DDS X Y q)
    (i j : ℕ) (hi : i < q) (hj : j < q) (hij : i = j)
    (f : Fin (i + 1) → X) (g : Fin (j + 1) → X)
    (hfg : ∀ (k : ℕ) (hki : k < i + 1) (hkj : k < j + 1), f ⟨k, hki⟩ = g ⟨k, hkj⟩) :
    s.respond ⟨i, hi⟩ f = s.respond ⟨j, hj⟩ g := by
  subst hij; congr 1; funext ⟨k, hk⟩; exact hfg k hk hk

set_option maxHeartbeats 1600000 in
/-- The successor of a reconstructed DDS recovers the original successor. -/
theorem reconstruct_successor (f : X → Y) (g : X → DDS X Y q) (x : X) :
    (reconstruct f g).successor x = g x := by
  apply ext; funext ⟨i, hi⟩ inputs
  simp only [successor, reconstruct, Fin.val_mk,
    show ¬((⟨i, hi⟩ : Fin q).val + 1 = 0) from by omega, dite_false, Function.comp]
  rfl

/-- The first query of a reconstructed DDS recovers the original function. -/
theorem reconstruct_firstQuery (f : X → Y) (g : X → DDS X Y q) (x : X) :
    (reconstruct f g).firstQuery (Nat.zero_lt_succ q) x = f x := by
  simp [reconstruct, firstQuery]

set_option maxHeartbeats 1600000 in
/-- Every (q+1)-query DDS equals the reconstruction of its first query and successor. -/
theorem eq_reconstruct (s : DDS X Y (q + 1)) :
    s = reconstruct (s.firstQuery (Nat.zero_lt_succ q)) (fun x => s.successor x) := by
  apply ext; funext ⟨i, hi⟩ inputs
  simp only [reconstruct]
  by_cases h : i = 0
  · subst h; simp only [Fin.val_mk, dite_true, firstQuery]
    congr 1; ext ⟨j, hj⟩
    have : j = 0 := Nat.lt_one_iff.mp hj; subst this; rfl
  · rw [dif_neg h]; simp only [successor, Fin.val_mk]
    symm
    apply respond_congr_val
    · exact Nat.succ_pred_eq_of_ne_zero h
    · intro k hki hkj
      rcases k with _ | k
      · simp [Fin.cons_zero]
      · change Fin.cons _ _ (Fin.succ ⟨k, by omega⟩) = _; rw [Fin.cons_succ]

/-- `ofFun` and `firstQuery` are inverses for single-query systems. -/
theorem ofFun_firstQuery (f : X → Y) :
    (ofFun f).firstQuery Nat.zero_lt_one = f := by
  ext x
  simp [ofFun, firstQuery]

/-- Helper for Prod equality with respond_congr_val on second component. -/
private theorem transcript_eq_of_input_respond
    (s : DDS X Y q) (i j : ℕ) (hi : i < q) (hj : j < q) (hij : i = j)
    (x₁ x₂ : X) (hx : x₁ = x₂)
    (f : Fin (i + 1) → X) (g : Fin (j + 1) → X)
    (hfg : ∀ (k : ℕ) (hki : k < i + 1) (hkj : k < j + 1), f ⟨k, hki⟩ = g ⟨k, hkj⟩) :
    ((x₁, s.respond ⟨i, hi⟩ f) : X × Y) = (x₂, s.respond ⟨j, hj⟩ g) :=
  Prod.ext hx (respond_congr_val s i j hi hj hij f g hfg)

/-- The transcript at position 0 with `Fin.cons x inputs'` relates to `firstQuery`. -/
theorem transcript_zero_cons (s : DDS X Y (q + 1)) (x : X) (inputs' : Fin q → X) :
    s.transcript (Fin.cons x inputs') ⟨0, Nat.zero_lt_succ q⟩ =
    (x, s.firstQuery (Nat.zero_lt_succ q) x) := by
  simp only [transcript, firstQuery]
  exact transcript_eq_of_input_respond s 0 0 _ _ rfl _ _ (by simp [Fin.cons])
    _ _ (fun k hki hkj => by
      obtain rfl : k = 0 := by omega
      simp [Fin.cons])

/-- The transcript at position i+1 of a (q+1)-query DDS with `Fin.cons x inputs'` equals
    the transcript of its successor at position i. -/
theorem transcript_succ_cons (s : DDS X Y (q + 1)) (x : X)
    (inputs' : Fin q → X) (i : Fin q) :
    s.transcript (Fin.cons x inputs') ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
    (s.successor x).transcript inputs' i := by
  simp only [transcript, successor, Fin.val_mk]
  exact transcript_eq_of_input_respond s _ _ _ _ rfl _ _ (by simp [Fin.cons])
    _ _ (fun k hki hkj => by
      simp only [Function.comp, Fin.cast]
      rcases k with _ | k
      · simp [Fin.cons]
      · simp [Fin.cons])

/-- For q = 1, the transcript depends only on the single input and
the first-query response. -/
theorem transcript_q1 {X Y : Type*} (s : DDS X Y 1) (inputs : Fin 1 → X) :
    DDS.transcript s inputs =
    fun _ => (inputs 0, s.firstQuery Nat.zero_lt_one (inputs 0)) := by
  funext ⟨i, hi⟩
  have : i = 0 := by omega
  subst this
  simp only [DDS.transcript, DDS.firstQuery]
  apply Prod.ext
  · rfl
  · apply DDS.respond_congr_val s 0 0 hi Nat.zero_lt_one rfl _ _ (fun k hki hkj => by
      obtain rfl : k = 0 := by omega
      rfl)

end DDS

/-- A single-query DDS is essentially a function `X → Y`. -/
abbrev DDS₁ (X Y : Type*) := DDS X Y 1

/-- The equivalence between single-query DDS and functions.

Paper: For `q = 1`, a DDS is just a function `X → Y`.
This is the simplest case and appears frequently. -/
def dds1Equiv (X Y : Type*) : DDS X Y 1 ≃ (X → Y) where
  toFun := fun s => s.firstQuery Nat.zero_lt_one
  invFun := DDS.ofFun
  left_inv := by
    intro s
    apply DDS.ext
    funext ⟨i, hi⟩
    have : i = 0 := by omega
    subst this
    funext inputs
    simp [DDS.ofFun, DDS.firstQuery]
    congr 1
    funext ⟨j, hj⟩
    have : j = 0 := by omega
    subst this
    rfl
  right_inv := by
    intro f
    funext x
    simp [DDS.ofFun, DDS.firstQuery]

set_option maxHeartbeats 1600000 in
/-- The decomposition equivalence: a (q+1)-query DDS is equivalent to
a first-query function and a family of successor q-query DDS.

This is the formal bijection underlying the inductive proof of Theorem 1.
  DDS X Y (q+1) ≃ (X → Y) × (X → DDS X Y q) -/
def DDS.decompose (X Y : Type*) (q : ℕ) :
    DDS X Y (q + 1) ≃ (X → Y) × (X → DDS X Y q) where
  toFun s := (s.firstQuery (Nat.zero_lt_succ q), fun x => s.successor x)
  invFun p := DDS.reconstruct p.1 p.2
  left_inv s := (DDS.eq_reconstruct s).symm
  right_inv := by
    intro ⟨f, g⟩
    simp only [Prod.mk.injEq]
    exact ⟨funext (DDS.reconstruct_firstQuery f g),
           funext (DDS.reconstruct_successor f g)⟩

end RandomSystems
