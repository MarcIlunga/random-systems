/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Applications.XoPCounting
import Mathlib.Data.Fintype.CardEmbedding

/-!
# XoP Combinatorics

This file isolates the elementary hidden-state count used by the concrete XoP
counting scaffold.  For a visible output tuple `y`, a hidden tuple `a` is
compatible when both `a` and `a + y` are injective.
-/

noncomputable section

open scoped BigOperators NNReal

namespace RandomSystems
namespace Applications
namespace XoP
namespace Combinatorics

variable {G : Type*} {q : Nat}

/-- A query-indexed tuple with no repeated entries. -/
def InjectiveTuple (a : Fin q → G) : Prop :=
  Function.Injective a

local instance injectiveTupleDecidable : DecidablePred (fun a : Fin q → G => InjectiveTuple a) :=
  fun _ => Classical.propDecidable _

/-- Number of injective hidden tuples.  This is Mathlib's falling factorial. -/
def injectiveTupleCount [Fintype G] : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter (fun a => InjectiveTuple a)).card

/--
The injective tuple count is `(N)_q`.  The proof is only the XoP-shaped adapter:
Mathlib supplies `Fintype.card_embedding_eq` for the cardinality of embeddings.
-/
@[simp]
theorem injectiveTupleCount_descFactorial [Fintype G] :
    injectiveTupleCount (G := G) (q := q) = (Fintype.card G).descFactorial q := by
  unfold injectiveTupleCount InjectiveTuple
  letI : Fintype { f : Fin q → G // Function.Injective f } :=
    Fintype.ofEquiv (Fin q ↪ G) (Equiv.subtypeInjectiveEquivEmbedding (Fin q) G).symm
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin q) G)]
  rw [Fintype.card_embedding_eq, Fintype.card_fin]

/-- The subtype of injective hidden tuples. -/
def InjectiveTupleSubtype (G : Type*) (q : Nat) : Type _ :=
  { a : Fin q → G // InjectiveTuple a }

instance injectiveTupleSubtypeFintype [Fintype G] : Fintype (InjectiveTupleSubtype G q) :=
  Fintype.ofEquiv (Fin q ↪ G) (Equiv.subtypeInjectiveEquivEmbedding (Fin q) G).symm

/-- The subtype cardinality agrees with the filtered finite-set count. -/
@[simp]
theorem injectiveTupleSubtype_card [Fintype G] :
    Fintype.card (InjectiveTupleSubtype G q) = @injectiveTupleCount G q _ := by
  letI : Fintype { f : Fin q → G // Function.Injective f } :=
    Fintype.ofEquiv (Fin q ↪ G) (Equiv.subtypeInjectiveEquivEmbedding (Fin q) G).symm
  unfold InjectiveTupleSubtype injectiveTupleCount InjectiveTuple
  rw [← Fintype.card_subtype]
  rfl

/-- Shift a hidden tuple by a visible output tuple. -/
def shifted [AddGroup G] (y a : Fin q → G) : Fin q → G :=
  fun i => a i + y i

/-- XoP hidden-state compatibility for one visible output tuple. -/
def CompatibleHiddenState [AddGroup G] (y a : Fin q → G) : Prop :=
  Function.Injective a ∧ Function.Injective (shifted y a)

/-- Visible-output/hidden-state compatible pairs. -/
def CompatiblePair (G : Type*) [AddGroup G] (q : Nat) : Type _ :=
  { p : (Fin q → G) × (Fin q → G) // CompatibleHiddenState p.1 p.2 }

/--
Compatible `(y, a)` pairs are equivalent to pairs of injective tuples `(a, b)`,
where `b = a + y`.  This is the combinatorial core of the normalizer
`E_I[Z] = (N)_q^2 / N^q`.
-/
def compatiblePairEquivInjectiveProduct [AddGroup G] :
    CompatiblePair G q ≃ InjectiveTupleSubtype G q × InjectiveTupleSubtype G q where
  toFun p :=
    (⟨p.1.2, p.2.1⟩, ⟨shifted p.1.1 p.1.2, p.2.2⟩)
  invFun p :=
    ⟨(fun i => -p.1.1 i + p.2.1 i, p.1.1), by
      constructor
      · exact p.1.2
      · have hshift : shifted (fun i => -p.1.1 i + p.2.1 i) p.1.1 = p.2.1 := by
          funext i
          simp [shifted]
        simpa [hshift] using p.2.2⟩
  left_inv p := by
    cases p with
    | mk val h =>
      cases val with
      | mk y a =>
        simp [shifted]
  right_inv p := by
    cases p with
    | mk a b =>
      cases a with
      | mk a ha =>
        cases b with
        | mk b hb =>
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            funext i
            simp [shifted]

/-- Compatible pairs as a dependent sum over visible outputs and compatible hidden states. -/
def compatiblePairEquivSigma [AddGroup G] :
    CompatiblePair G q ≃ Sigma (fun y : Fin q → G =>
      { a : Fin q → G // CompatibleHiddenState y a }) where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv p := by
    cases p with
    | mk val h =>
      cases val
      rfl
  right_inv p := by
    cases p with
    | mk y a =>
      cases a
      rfl

instance compatiblePairFintype [AddGroup G] [Fintype G] : Fintype (CompatiblePair G q) :=
  Fintype.ofEquiv (InjectiveTupleSubtype G q × InjectiveTupleSubtype G q)
    (compatiblePairEquivInjectiveProduct :
      CompatiblePair G q ≃ InjectiveTupleSubtype G q × InjectiveTupleSubtype G q).symm

/-- The number of compatible `(y, a)` pairs is the square of the injective-tuple count. -/
@[simp]
theorem compatiblePair_card [AddGroup G] [Fintype G] :
    Fintype.card (CompatiblePair G q) =
      @injectiveTupleCount G q _ * @injectiveTupleCount G q _ := by
  rw [Fintype.card_congr
    (compatiblePairEquivInjectiveProduct :
      CompatiblePair G q ≃ InjectiveTupleSubtype G q × InjectiveTupleSubtype G q)]
  simp [Fintype.card_prod]

local instance compatibleHiddenStateDecidable [AddGroup G] (y : Fin q → G) :
    DecidablePred (fun a => CompatibleHiddenState y a) :=
  fun _ => Classical.propDecidable _

local instance compatibleFiberFintype [AddGroup G] [Fintype G] (y : Fin q → G) :
    Fintype { a : Fin q → G // CompatibleHiddenState y a } :=
  Fintype.subtype
    ((Finset.univ : Finset (Fin q → G)).filter (fun a => CompatibleHiddenState y a))
    (by intro a; simp)

/-- Natural-number count of hidden tuples compatible with a visible output tuple. -/
def compatibleCountNat [AddGroup G] [Fintype G] (y : Fin q → G) : Nat :=
  ((Finset.univ : Finset (Fin q → G)).filter
    (fun a => CompatibleHiddenState y a)).card

/-- `compatibleCountNat` is definitionally the card of the compatible filter. -/
@[simp]
theorem compatibleCountNat_eq_card_filter [AddGroup G] [Fintype G] (y : Fin q → G) :
    compatibleCountNat y =
      ((Finset.univ : Finset (Fin q → G)).filter
        (fun a => CompatibleHiddenState y a)).card := by
  rfl

/-- The compatible fiber subtype has cardinality `compatibleCountNat`. -/
@[simp]
theorem compatibleFiber_card [AddGroup G] [Fintype G] (y : Fin q → G) :
    Fintype.card { a : Fin q → G // CompatibleHiddenState y a } = compatibleCountNat y := by
  unfold compatibleCountNat
  rw [← Fintype.card_subtype]

/-- Compatibility is invariant under translating every visible output by the same group element. -/
theorem compatibleHiddenState_add_const [AddGroup G] (y a : Fin q → G) (t : G)
    (h : CompatibleHiddenState y a) :
    CompatibleHiddenState (fun i => y i + t) a := by
  constructor
  · exact h.1
  · intro i j hij
    apply h.2
    exact add_right_cancel (by simpa [shifted, add_assoc] using hij)

/-- Identity equivalence between compatible fibers before and after global visible translation. -/
def compatibleFiberAddConstEquiv [AddGroup G] (y : Fin q → G) (t : G) :
    { a : Fin q → G // CompatibleHiddenState y a } ≃
      { a : Fin q → G // CompatibleHiddenState (fun i => y i + t) a } where
  toFun a := ⟨a.1, compatibleHiddenState_add_const y a.1 t a.2⟩
  invFun a := by
    refine ⟨a.1, ?_⟩
    simpa [add_assoc] using compatibleHiddenState_add_const (fun i => y i + t) a.1 (-t) a.2
  left_inv a := by
    exact Subtype.ext rfl
  right_inv a := by
    exact Subtype.ext rfl

/-- Compatible hidden-state counts are invariant under global visible translation. -/
theorem compatibleCountNat_add_const [AddGroup G] [Fintype G] (y : Fin q → G) (t : G) :
    compatibleCountNat (fun i => y i + t) = compatibleCountNat y := by
  simpa [compatibleFiber_card] using
    Fintype.card_congr (compatibleFiberAddConstEquiv (G := G) (q := q) y t).symm

/-- Summing compatible hidden-state counts over visible tuples counts compatible pairs. -/
theorem sum_compatibleCountNat_eq_compatiblePair_card [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNat y) = Fintype.card (CompatiblePair G q) := by
  rw [Fintype.card_congr
    (compatiblePairEquivSigma :
      CompatiblePair G q ≃ Sigma (fun y : Fin q → G =>
        { a : Fin q → G // CompatibleHiddenState y a }))]
  rw [Fintype.card_sigma]
  simp [compatibleFiber_card]

/-- The raw total compatible count is the square of the injective-tuple count. -/
theorem sum_compatibleCountNat_eq_injectiveTupleCount_sq [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNat y) =
      @injectiveTupleCount G q _ * @injectiveTupleCount G q _ := by
  rw [sum_compatibleCountNat_eq_compatiblePair_card, compatiblePair_card]

/-- The raw total compatible count is `(N)_q^2`. -/
theorem sum_compatibleCountNat_eq_descFactorial_sq [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNat y) =
      (Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q := by
  rw [sum_compatibleCountNat_eq_injectiveTupleCount_sq, injectiveTupleCount_descFactorial]

/-- NNReal version of the compatible hidden-state count. -/
def compatibleCountNNReal [AddGroup G] [Fintype G] (y : Fin q → G) : NNReal :=
  (compatibleCountNat y : NNReal)

/-- `compatibleCountNNReal` is definitionally the `NNReal` cast of the natural count. -/
@[simp]
theorem compatibleCountNNReal_eq_coe_nat [AddGroup G] [Fintype G] (y : Fin q → G) :
    compatibleCountNNReal y = (compatibleCountNat y : NNReal) := by
  rfl

/-- `NNReal` compatible hidden-state counts are invariant under global visible translation. -/
theorem compatibleCountNNReal_add_const [AddGroup G] [Fintype G] (y : Fin q → G) (t : G) :
    compatibleCountNNReal (fun i => y i + t) = compatibleCountNNReal y := by
  simpa [compatibleCountNNReal] using
    congrArg (fun n : Nat => (n : NNReal)) (compatibleCountNat_add_const (G := G) (q := q) y t)

/-- `NNReal` version of the raw total compatible-count identity. -/
theorem sum_compatibleCountNNReal_eq_descFactorial_sq [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNNReal y) =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
        NNReal) := by
  change (∑ y : Fin q → G, (compatibleCountNat y : NNReal)) =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
        NNReal)
  rw [← Nat.cast_sum]
  rw [sum_compatibleCountNat_eq_descFactorial_sq]

/-- The visible output tuple space has size `N^q`. -/
@[simp]
theorem visibleTupleCount_eq_pow [Fintype G] :
    Fintype.card (Fin q → G) = Fintype.card G ^ q := by
  simp

/--
The ideal-uniform average of the compatible hidden-state count is
`(N)_q^2 / N^q`.
-/
theorem idealCompatibleExpectation_eq_descFactorial_sq_div_pow [AddGroup G] [Fintype G] :
    (∑ y : Fin q → G, compatibleCountNNReal y) /
        (Fintype.card (Fin q → G) : NNReal) =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          NNReal) /
        ((Fintype.card G ^ q : Nat) : NNReal) := by
  rw [sum_compatibleCountNNReal_eq_descFactorial_sq]
  rw [visibleTupleCount_eq_pow]

/--
Correct theorem-facing normalizer for the visible-output compatible count:
`(N)_q^2 / N^q`.  The explicit `q ≤ N` assumption is the reusable condition
that makes `(N)_q` nonzero.
-/
def compatibleExpectationNormalizer [AddGroup G] [Fintype G] (hq : q ≤ Fintype.card G) :
    Counting.FallingFactorialNormalizer G q where
  value := (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
      NNReal) / ((Fintype.card G ^ q : Nat) : NNReal)
  value_ne_zero := by
    have hdesc_pos : 0 < (Fintype.card G).descFactorial q := Nat.descFactorial_pos.mpr hq
    have hnum_pos :
        0 < (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
          NNReal) :=
      Nat.cast_pos.mpr (Nat.mul_pos hdesc_pos hdesc_pos)
    have hcard_pos : 0 < Fintype.card G := Fintype.card_pos
    have hden_pos : 0 < ((Fintype.card G ^ q : Nat) : NNReal) :=
      Nat.cast_pos.mpr (pow_pos hcard_pos q)
    exact ne_of_gt (div_pos hnum_pos hden_pos)

/-- Compatible hidden states are a subset of injective hidden tuples. -/
theorem compatibleCountNat_le_injectiveTupleCount [AddGroup G] [Fintype G] (y : Fin q → G) :
    compatibleCountNat y ≤ injectiveTupleCount (G := G) (q := q) := by
  unfold compatibleCountNat injectiveTupleCount CompatibleHiddenState InjectiveTuple
  exact Finset.card_le_card (by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ha.1)

/-- Compatible hidden-state counts are bounded by the falling factorial `(N)_q`. -/
theorem compatibleCountNat_le_descFactorial [AddGroup G] [Fintype G] (y : Fin q → G) :
    compatibleCountNat y ≤ (Fintype.card G).descFactorial q := by
  simpa using compatibleCountNat_le_injectiveTupleCount (G := G) (q := q) y

/-- The output component of a transcript, viewed as the visible XoP tuple. -/
def transcriptOutputs (t : Transcript G G q) : Fin q → G :=
  fun i => (t i).2

/-- Transcript-level natural count, depending only on the output component. -/
def compatibleTranscriptCountNat [AddGroup G] [Fintype G] (t : Transcript G G q) : Nat :=
  compatibleCountNat (transcriptOutputs t)

/-- Transcript-level NNReal count, depending only on the output component. -/
def compatibleTranscriptCountNNReal [AddGroup G] [Fintype G] (t : Transcript G G q) : NNReal :=
  compatibleCountNNReal (transcriptOutputs t)

/-- The transcript-level natural count reads the output component of the transcript. -/
@[simp]
theorem compatibleTranscriptCountNat_eq_outputs [AddGroup G] [Fintype G] (t : Transcript G G q) :
    compatibleTranscriptCountNat t =
      compatibleCountNat (transcriptOutputs t) := by
  rfl

/-- The transcript-level NNReal count reads the output component of the transcript. -/
@[simp]
theorem compatibleTranscriptCountNNReal_eq_outputs [AddGroup G] [Fintype G] (t : Transcript G G q) :
    compatibleTranscriptCountNNReal t =
      compatibleCountNNReal (transcriptOutputs t) := by
  rfl

/-- With no queries, every hidden tuple is compatible. -/
@[simp]
theorem compatibleHiddenState_zero [AddGroup G] (y a : Fin 0 → G) :
    CompatibleHiddenState y a := by
  constructor
  · intro i j _
    exact Subsingleton.elim i j
  · intro i j _
    exact Subsingleton.elim i j

/-- With one query, every hidden tuple is compatible. -/
@[simp]
theorem compatibleHiddenState_one [AddGroup G] (y a : Fin 1 → G) :
    CompatibleHiddenState y a := by
  constructor
  · intro i j _
    exact Subsingleton.elim i j
  · intro i j _
    exact Subsingleton.elim i j

/-- The trivial normalizer used to package the raw compatible-count function. -/
def compatibleCountNormalizer [Fintype G] : Counting.FallingFactorialNormalizer G q where
  value := 1
  value_ne_zero := one_ne_zero

/--
The concrete `CompatibleCount` object whose `Z` reads the output component of a
transcript and returns the compatible hidden-state count for that output tuple.
-/
def compatibleCount [AddGroup G] [Fintype G] : Counting.CompatibleCount G G q where
  Z := compatibleTranscriptCountNNReal
  normalizer := compatibleCountNormalizer

/--
The theorem-facing compatible count using the corrected normalizer
`(N)_q^2 / N^q` under the explicit nonzero-domain assumption `q ≤ N`.
-/
def compatibleCountWithExpectationNormalizer [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) : Counting.CompatibleCount G G q where
  Z := compatibleTranscriptCountNNReal
  normalizer := compatibleExpectationNormalizer hq

/-- The packaged compatible count is exactly the output-tuple hidden-state count. -/
@[simp]
theorem compatibleCount_Z [AddGroup G] [Fintype G] (t : Transcript G G q) :
    compatibleCount.Z t = compatibleCountNNReal (transcriptOutputs t) := by
  rfl

/-- The corrected packaged compatible count has the same `Z` function. -/
@[simp]
theorem compatibleCountWithExpectationNormalizer_Z [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) (t : Transcript G G q) :
    (compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).Z t =
      compatibleCountNNReal (transcriptOutputs t) := by
  rfl

/-- The corrected packaged compatible count exposes the expected normalizer. -/
@[simp]
theorem compatibleCountWithExpectationNormalizer_normalizer [AddGroup G] [Fintype G]
    (hq : q ≤ Fintype.card G) :
    (compatibleCountWithExpectationNormalizer (G := G) (q := q) hq).normalizer.value =
      (((Fintype.card G).descFactorial q * (Fintype.card G).descFactorial q : Nat) :
        NNReal) / ((Fintype.card G ^ q : Nat) : NNReal) := by
  rfl

end Combinatorics
end XoP
end Applications
end RandomSystems
